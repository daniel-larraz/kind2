(* This file is part of the Kind 2 model checker.

   Copyright (c) 2017-2018, 2021 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open Lib
open Realizability

module ISys = InputSystem
module TSys = TransSys

module SVM = StateVar.StateVarMap
module VS = Var.VarSet


type t =
{
  (* Initial predicate *)
  init: Term.t ;

  (* Transition relation predicate *)
  trans: Term.t;
}

let empty = { init = Term.t_true; trans = Term.t_true }

let is_empty { init; trans } = init == Term.t_true && trans == Term.t_true

let print_init_debug init =
  Debug.assump "  @[<hov 2>Initial predicate:@ %a@]@."
    (LustreExpr.pp_print_term_as_expr true) init

let print_trans_debug trans =
  let trans' = Term.bump_state (Numeral.of_int (-1)) trans in

  Debug.assump "  @[<hov 2>Transition predicate:@ %a@]@."
    (LustreExpr.pp_print_term_as_expr true) trans'

let print_assump_debug {init; trans} =
  print_init_debug init ; print_trans_debug trans

let print_predicate_debug pred =
  Debug.assump "  @[<hov 2>Candidate:@ %a@]@."
    (LustreExpr.pp_print_term_as_expr true) pred

let state_vars_of_init { init } = Term.state_vars_of_term init

let state_vars_of_trans { trans } = Term.state_vars_of_term trans

let map_vars f { init; trans } =
  { init = Term.map_state_vars f init;
    trans = Term.map_state_vars f trans }

let lustre_assumption { init; trans } =
  let mk_expr_of_term t =
    LustreExpr.mk_of_expr (LustreExpr.unsafe_expr_of_term t)
  in
  let bump_minus_one term =
    Term.bump_state (Numeral.of_int (- 1)) term
  in
  let init_expr = mk_expr_of_term init in
  let trans_expr = trans |> bump_minus_one |> mk_expr_of_term in
  LustreExpr.mk_arrow init_expr trans_expr


type 'a variable_filter_func = 'a InputSystem.t -> Scope.t -> Var.t list -> Var.t list

type 'a pair_of_filters = ('a variable_filter_func * 'a variable_filter_func)


type response =
  | Success of t
  | Failure
  | Unknown


let filter_non_input _ _ =
  List.filter
    (fun v -> Var.state_var_of_state_var_instance v |> StateVar.is_input |> not)

let get_output_svars in_sys scope =
  match ISys.get_lustre_node in_sys scope with
  | Some { LustreNode.outputs } ->
    List.map snd (LustreIndex.bindings outputs)
  | None -> []

let filter_non_output in_sys scope =
  let output_svars = get_output_svars in_sys scope in
  List.filter
    (fun v ->
     let sv = Var.state_var_of_state_var_instance v in
     List.exists (fun o -> StateVar.equal_state_vars o sv) output_svars
     |> not
    )

let create_assumpion_init fmt_assump sys solver vars fp prop =

  let init = TSys.init_of_bound None sys Numeral.zero in

  let conclusion = Term.mk_and [prop.Property.prop_term; fp] in

  let assump_init =
    Abduction.abduce solver vars init conclusion
    |> SMTSolver.simplify_term solver
  in

  (*Format.printf "Assump Init: %a@." Term.pp_print_term assump_init;*)

  KEvent.log_uncond "  @[<hov 2>Initial predicate:@ %a@]" fmt_assump assump_init;

  assump_init


let create_assumpion_trans fmt_assump sys solver vars fp prop =

  let trans =
    let invars =
      (TransSys.invars_of_bound sys ~one_state_only:true Numeral.zero) @
      TransSys.invars_of_bound sys Numeral.one
    in  
    Term.mk_and
      (TSys.trans_of_bound None sys Numeral.one :: invars)
  in

  let premises = Term.mk_and [fp ; trans] in

  let fp_at_1 = Term.bump_state Numeral.one fp in

  let prop_at_1 = Term.bump_state Numeral.one prop.Property.prop_term  in

  let conclusion = Term.mk_and [prop_at_1; fp_at_1] in

  let assump_trans = Abduction.abduce solver vars premises conclusion in

  (*Format.printf "Assump Trans: %a@." Term.pp_print_term assump_trans;*)

  let assump_trans' = Term.bump_state (Numeral.of_int (-1)) assump_trans in

  KEvent.log_uncond "  @[<hov 2>Transition predicate:@ %a@]" fmt_assump assump_trans';

  assump_trans


type 'a analyze_func =
  bool -> bool -> 
  Lib.kind_module list ->
  'a InputSystem.t ->
  Analysis.param ->
  TransSys.t ->
  unit


let create_solver_and_context sys k =
  let solver =
    SMTSolver.create_instance
      (TermLib.add_quantifiers (TSys.get_logic sys))
      (Flags.Smt.solver ())
  in

  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero (Numeral.of_int k);

  solver


let get_uf_symbol sv_to_ufs sv o =
  match SVM.find_opt sv sv_to_ufs with
  | Some lst -> (
    match List.nth_opt lst o with
    | Some uf -> uf
    | None -> assert false
  )
  | None -> assert false


let mk_equality sv_to_ufs f sv i j =
  let v = Var.mk_state_var_instance sv (Numeral.of_int i) in
  let uf = get_uf_symbol sv_to_ufs sv j in
  Term.mk_eq [Term.mk_var v; f (Term.mk_uf uf [])]


let mk_equalities input_svars sv_to_ufs f i j =
  input_svars
  |> List.map (fun sv -> mk_equality sv_to_ufs f sv i j)
  |> Term.mk_and


let mk_forall_vars input_svars k =
  List.fold_left
    (fun acc sv ->
      let vars =
        List.init
          (k+1)
          (fun i -> Var.mk_state_var_instance sv (Numeral.of_int i))
      in
      List.rev_append vars acc
    )
    []
    input_svars
  |> List.rev


let mk_forall_term input_svars sv_to_ufs k abduct =
  let mk_equalities =
    mk_equalities input_svars sv_to_ufs identity
  in
  let forall_vars = mk_forall_vars input_svars k in
  let cterms =
    List.init (k+1) (fun i ->
      List.init (k+1) (fun j -> mk_equalities i j)
      |> Term.mk_or
    )
  in
  Term.mk_forall forall_vars
    (Term.mk_implies [Term.mk_and cterms; abduct])


let init_soln solver input_svars sv_to_ufs k system_unrolling abduct =

  let full_term =
    let qterm =
      mk_forall_term input_svars sv_to_ufs k abduct
    in
    let sigma =
      SVM.fold
        (fun sv ufs acc ->
          let sv_sigma =
            ufs |> List.mapi (fun i uf ->
              (Var.mk_state_var_instance sv (Numeral.of_int i),
               Term.mk_uf uf [])
            )
          in
          List.rev_append sv_sigma acc
        )
        sv_to_ufs
        []
    in
    Term.mk_and [Term.apply_subst sigma system_unrolling; qterm]
  in

  SMTSolver.push solver;

  SMTSolver.assert_term solver full_term;

  let assump_pred =
    let all_ufs =
      SVM.fold
        (fun _ ufs acc -> List.rev_append ufs acc)
        sv_to_ufs
        []
      |> List.map (fun uf -> Term.mk_uf uf [])
    in
    SMTSolver.check_sat_and_get_term_values
      solver
      (fun _ term_values -> (* If sat. *)
        let f t =
          match List.assoc_opt t term_values with
          | Some v -> v
          | None -> assert false
        in
        let mk_equalities =
          mk_equalities input_svars sv_to_ufs f
        in
        List.init (k+1) (fun j -> mk_equalities 0 j)
        |> Term.mk_or
      )
      (fun _ -> assert false) (* If unsat. *)
      all_ufs
  in

  SMTSolver.pop solver;
 
  assump_pred


let iso_decomp abd_solver uf_solver input_svars sv_to_ufs assump_pred k abduct =

  let rec loop assump_pred' iter =
    let term =
      List.init (k+1) (fun i ->
        let sigma =
          SVM.fold
            (fun sv ufs acc ->
              let v = Var.mk_state_var_instance sv Numeral.zero in
              let uf =
                match List.nth_opt ufs i with
                | Some uf -> uf
                | None -> assert false
              in
              (v, Term.mk_uf uf []) :: acc
            )
            sv_to_ufs
            []
        in
        Term.apply_subst sigma assump_pred' |> Term.negate
      )
      |> Term.mk_and
    in

    SMTSolver.push uf_solver;

    SMTSolver.assert_term uf_solver term;

    let res =
      let all_ufs_from_0 =
        SVM.fold
          (fun _ ufs acc -> List.rev_append ufs acc)
          sv_to_ufs
          []
        |> List.map (fun uf -> Term.mk_uf uf [])
      in
      SMTSolver.check_sat_and_get_term_values
        uf_solver
        (fun _ term_values -> (* If sat. *)
          let f t =
            match List.assoc_opt t term_values with
            | Some v -> v
            | None -> assert false
          in
          let mk_equalities =
            mk_equalities input_svars sv_to_ufs f
          in
          Some (
            List.init (k+1) (fun j -> mk_equalities 0 j)
            |> Term.mk_or
          )
        )
        (fun _ -> (* If unsat. *)
          None
        )
        all_ufs_from_0
    in

    SMTSolver.pop uf_solver;

    match res with
    | None -> assump_pred'
    | Some sol -> (
      let assump_pred'' =
        let pred_unrolling =
          let pred' = Term.mk_or [assump_pred'; sol] in
          List.init
            (k+1)
            (fun i -> Term.bump_state (Numeral.of_int i) pred')
        in
        let all_forall_vars =
          mk_forall_vars input_svars k
        in
        List.fold_left
          (fun pred_unrolling' i ->
            let forall_vars =
              all_forall_vars |> List.filter (fun v -> 
                Numeral.equal (Var.offset_of_state_var_instance v) (Numeral.of_int i)
                |> not
              )
            in
            let pred_unrolling' = Lib.list_remove_nth i pred_unrolling' in
            let premises = Term.mk_and pred_unrolling' in
            let pred_at_i =
              SMTSolver.trace_comment abd_solver (Format.sprintf "Iter: %d" i);
              Abduction.abduce abd_solver forall_vars premises abduct
              |> SMTSolver.simplify_term abd_solver
            in
            Lib.list_insert_at pred_at_i i pred_unrolling'
          )
          pred_unrolling
          (List.init (k+1) identity) 
        |> List.mapi (fun i t ->
          Term.bump_state (Numeral.of_int (- i)) t
        )
        |> Term.mk_and
        |> SMTSolver.simplify_term abd_solver
      in

      if (assump_pred' == assump_pred'') then (
        assump_pred''
      )
      else (
        Debug.assump "Generalized candidate@." ;

        print_predicate_debug assump_pred'';

        if (iter >= Flags.Contracts.assumption_gen_iter ()) then
          assump_pred''
        else
          loop assump_pred'' (iter+1)
      ) 
    )
  in

  let qterm =
    mk_forall_term input_svars sv_to_ufs k abduct
  in

  SMTSolver.push uf_solver;

  SMTSolver.assert_term uf_solver qterm;

  let assump_pred' = loop assump_pred 1 in

  SMTSolver.pop uf_solver;

  assump_pred'


let cart_decomp abd_solver sys k system_unrolling abduct =

  let uf_solver = create_solver_and_context sys k in

  let input_svars =
    TSys.vars_of_bounds ~with_init_flag:false sys Numeral.zero Numeral.zero
    |> List.filter_map (fun v ->
      let sv = Var.state_var_of_state_var_instance v in
      if StateVar.is_input sv then Some sv else None
    )
  in

  let sv_to_ufs, _ =
    let mk_uf_symbol sv id o =
      let name = Printf.sprintf "__assump_v%i_%i" id o in
      let typ = StateVar.type_of_state_var sv in
      let ufs = UfSymbol.mk_uf_symbol name [] typ in
      SMTSolver.declare_fun uf_solver ufs;
      ufs
    in
    List.fold_left
      (fun (map, id) sv ->
        let lst =
          List.init (k+1) (fun o -> mk_uf_symbol sv id o)
        in
        (SVM.add sv lst map, id+1)
      )
      (SVM.empty, 0)
      input_svars
  in

  let init =
    init_soln uf_solver input_svars sv_to_ufs k system_unrolling abduct
  in

  Debug.assump "Generated initial solution@." ;

  print_predicate_debug init ;

  let init =
    iso_decomp
      abd_solver uf_solver input_svars sv_to_ufs init k abduct
  in

  SMTSolver.delete_instance uf_solver ;
  
  Success { init; trans=Term.bump_state Numeral.one init }


let generate_assumption_for_k_and_below sys props k =

  Debug.assump "Generating assumption for k=%d...@." k ;

  let abd_solver = create_solver_and_context sys k in

  let num_k = Numeral.of_int k in

  let system_unrolling =
    let init = TSys.init_of_bound None sys Numeral.zero in
    if k=0 then
      init
    else
      Term.mk_and (init :: List.init k
        (fun n ->
          TSys.trans_of_bound None sys (Numeral.of_int (n+1))
        ))
      (*|> SMTSolver.simplify_term abd_solver*)
  in

  let props_from_0_to_k =
    let props_conj =
      props
      |> List.map (fun { Property.prop_term } -> prop_term)
      |> Term.mk_and
    in
    List.init (k+1) (fun n ->
      Term.bump_state (Numeral.of_int n) props_conj)
    |> Term.mk_and
  in

  let abduct =
    let forall_vars =
      let all_vars =
        TSys.vars_of_bounds ~with_init_flag:true sys Numeral.zero num_k
      in
      (* Remove duplicates: all_vars contains one ocurrence of each constant per instant *)
      VS.of_list all_vars
      |> VS.elements
      |> List.filter (fun v ->
        Var.state_var_of_state_var_instance v |> StateVar.is_input |> not
      )
    in
    Abduction.abduce abd_solver forall_vars system_unrolling props_from_0_to_k
    |> SMTSolver.simplify_term abd_solver
  in

  Debug.assump "@[<hv>Initial abduct:@ @[<hv>%a@]@]@." Term.pp_print_term abduct ;

  let res =
    if abduct = Term.t_false then
      Failure
    else (
      if k=0 then
        Success { init=abduct; trans=Term.t_true }
      else
        cart_decomp abd_solver sys k system_unrolling abduct
    )
  in

  SMTSolver.delete_instance abd_solver ;

  res


let generate_assumption analyze in_sys param sys =

  let modules = Flags.enabled () in
  let old_log_level = Lib.get_log_level () in

  let get_min_k props =
    let k_list =
      props |> List.map (fun p ->
        match Property.get_prop_status p with
        | Property.PropFalse cex -> (Property.length_of_cex cex) - 1
        | _ -> assert false
      )
    in
    List.fold_left min (List.hd k_list) (List.tl k_list)
  in

  let rec loop props k =
    let res = generate_assumption_for_k_and_below sys props k in
    match res with
    | Success ({init; trans} as assump) -> (

      Debug.assump "Generated new assumption candidate@." ;

      print_assump_debug assump ; 
      
      props |> List.iter (fun { Property.prop_name = n } ->
        TSys.set_prop_unknown sys n) ;

      let sys' =
        let scope = TSys.scope_of_trans_sys sys in
        let (_, init_eq, trans_eq) = TSys.init_trans_open sys in
        let init_eq = Term.mk_and [init_eq; init] in
        let trans_eq = Term.mk_and [trans_eq; trans] in
        TSys.set_subsystem_equations sys scope init_eq trans_eq
      in

      Lib.set_log_level L_off ;

      analyze false false modules in_sys param sys' ;

      Lib.set_log_level old_log_level;

      match TSys.get_split_properties sys' with
      | _, [], [] -> Success { init; trans }
      | _, [], _ -> Unknown
      | _, invalid, _ -> loop props (get_min_k invalid)

    )
    | r -> r
  in

  match TSys.get_split_properties sys with
  | _, [], [] -> Success { init = Term.t_true; trans = Term.t_true }
  | _, [], _ -> Unknown
  | _, invalid, _ -> loop invalid (get_min_k invalid)


let generate_assumption_vg in_sys sys var_filters prop =

  let vars_at_0 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.zero Numeral.zero
    |> List.filter (fun v -> not (Var.is_const_state_var v))
  in

  let vars_at_1 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.one Numeral.one
    |> List.filter (fun v -> not (Var.is_const_state_var v))
  in

  let controllable_vars_at_0 = vars_at_0 in
  
  let controllable_vars_at_1 = vars_at_1 in

  let scope = TSys.scope_of_trans_sys sys in

  let sys' =
    let (_, init_eq, trans_eq) = TSys.init_trans_open sys in
    let init_eq =
      Term.mk_and [init_eq; prop.Property.prop_term]
    in
    let trans_eq =
      let prop_at_1 = Term.bump_state Numeral.one prop.Property.prop_term in
      Term.mk_and [trans_eq; prop_at_1]
    in
    TSys.set_subsystem_equations sys scope init_eq trans_eq
  in

  let result =
    realizability_check
      sys' controllable_vars_at_0 vars_at_1 controllable_vars_at_1
  in

  match result with
  | Realizable fp -> (

    KEvent.log L_note
      "Generating assumption's initial and transition predicates..." ;

    let vf_pre, vf_curr = var_filters in

    let fmt_assump = ISys.pp_print_term_as_expr in_sys sys in

    let solver =
      SMTSolver.create_instance 
        (TermLib.add_quantifiers (TSys.get_logic sys))
        (Flags.Smt.solver ())
    in
  
    TransSys.define_and_declare_of_bounds
      sys
      (SMTSolver.define_fun solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero Numeral.one;
  
    let init_vars = vf_curr in_sys scope vars_at_0 in

    let init = create_assumpion_init fmt_assump sys solver init_vars fp prop in

    if Term.equal init Term.t_false then Unknown

    else (

      let trans_vars =
        List.rev_append (vf_pre in_sys scope vars_at_0) (vf_curr in_sys scope vars_at_1)
      in

      let trans = create_assumpion_trans fmt_assump sys solver trans_vars fp prop in

      if Term.equal trans Term.t_false then Unknown

      else Success { init; trans }

    )
  )
  | Unrealizable _ -> Failure
  | Unknown -> Unknown


let open_file_and_dump_header node path contract_name =

  let out_channel = open_out path in
  let fmt = Format.formatter_of_out_channel out_channel in

  let fmt_sig fmt =
    Format.fprintf fmt "@[<hov>%a@]" LustreNode.pp_print_node_signature
  in

  Format.fprintf fmt
    "(* Automatically generated assumption *)@.contract %s %a@.let@[<v -1>@ "
    contract_name fmt_sig node ;

  (out_channel, fmt)


let dump_footer fmt =
  Format.fprintf fmt "@]@.tel@.@."


let dump_assumption fmt { init ; trans } =

  let pp_print_lustre_expr = LustreExpr.pp_print_term_as_expr false in

  let trans' = Term.bump_state (Numeral.of_int (-1)) trans in

  if (init == trans') then (
    Format.fprintf fmt "@[<hov 2>assume@ %a;@]"
      pp_print_lustre_expr init
  )
  else (
    Format.fprintf fmt "@[<hov 2>assume@ (%a)@ ->@ (%a);@]"
      pp_print_lustre_expr init pp_print_lustre_expr trans'
  )


let dump_contract_for_assumption in_sys scope assumption path contract_name =

  match ISys.get_lustre_node in_sys scope with
  | Some node -> (

    let out_channel, fmt =
      open_file_and_dump_header node path contract_name
    in
    dump_assumption fmt assumption;
    dump_footer fmt;
    close_out out_channel

  )
  | None ->
    KEvent.log L_error "Assumption dump is only supported for Lustre models"

