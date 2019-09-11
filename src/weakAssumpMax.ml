(* This file is part of the Kind 2 model checker.

   Copyright (c) 2019 by the Board of Trustees of the University of Iowa

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

module I = LustreIdent

module ISys = InputSystem
module TSys = TransSys

type 'a analyze_func =
  Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> unit

let create_smt_solver logic =
  let solver = Flags.Smt.solver () in
  match solver with
  | `Z3_SMTLIB -> (
    SMTSolver.create_instance 
      (TermLib.add_quantifiers logic)
      solver
  )
  | _ -> (
    failwith "Max-SMT is not supported by SMT solver or \
              implementation is not available"
  )

let get_cex_length p =
  match Property.get_prop_status p with
  | Property.PropFalse cex -> Property.length_of_cex cex
  | _ -> assert false

let get_prop_with_shortest_cex props =
  List.map (fun p -> p, get_cex_length p) props
  |> List.fast_sort (fun (_,l1) (_,l2) -> compare l1 l2)
  |> List.hd


let disprove_maximizing_globally analyze in_sys param sys props weak_assumes =

  let mdl = KEvent.get_module () in

  KEvent.set_module `WeakAssumpMaximizer;

  let num_weak_assumes = List.length weak_assumes in

  let get_cex prop =
    match prop.Property.prop_status with
    | Property.PropFalse cex -> cex
    | _ -> failwith "property is not false"
  in

  let print_result param' prop sys' cex =

    let wa_model =
      weak_assumes
      |> List.map (fun ({LustreContract.svar} as wa) ->
        let value_list = try
          List.find (fun (sv, _) -> StateVar.equal_state_vars svar sv) cex |> snd
          with Not_found -> failwith "weak assumption value not found"
        in
        LustreContract.prop_name_of_svar wa "weakly_assume" "",
        List.fold_left (* eval conjunction *)
          (fun acc v -> acc &&
             match v with
             | Model.Term t when Term.is_bool t -> Term.bool_of_term t
             | _ -> failwith "weak assumption valuation failed"
          )
          true value_list
      )
    in

    (* It sets property status to falsifiable.
       It requires property status to be Unknown. *)
    KEvent.cex_wam
      cex wa_model in_sys param' sys' prop.Property.prop_name
  in

  let scope = TSys.scope_of_trans_sys sys in

  let mk_klocal_svar scope name =
    let svar_scope = scope @ I.reserved_scope in
    StateVar.mk_state_var
      ~is_input:false ~is_const:true ~for_inv_gen:true
      name svar_scope Type.t_bool
  in

  let act_svars =
    Lib.list_init
      ( fun i -> mk_klocal_svar scope (Format.sprintf "act_%d" i) )
      num_weak_assumes
  in

  let act_vars =
    List.map Var.mk_const_state_var act_svars
  in

  (* Techniques assume all properties are unknown initially;
     so we remove all properties except the one we want to check
     (here we remove all properties, we add the property to check later)
  *)
  let base_sys = TSys.remove_properties sys in

  let sys =
    List.fold_left
      (fun sys' svar -> TSys.add_global_constant sys' svar)
      base_sys act_svars
  in

  let act_preds =
    List.combine
      act_vars
      (List.map
        (fun {LustreContract.svar} -> Var.mk_state_var_instance svar Numeral.zero)
        weak_assumes
      )
    |> List.map (fun (a,v) -> Term.mk_implies [Term.mk_var a; Term.mk_var v])
  in

  let sys =
    List.fold_left
      (fun sys' p ->
        TSys.add_to_trans (TSys.add_to_init sys' p) (Term.bump_state Numeral.one p)
      )
      sys act_preds
  in

  let sum_act_vars =
    List.map
      (fun v ->
        Term.mk_ite (Term.mk_var v) (Term.mk_num_of_int 1)  (Term.mk_num_of_int 0)
      )
      act_vars
    |> Term.mk_plus
  in

  let mk_num_act_vars_bounded k =
    Term.mk_geq [sum_act_vars; Term.mk_num_of_int k]
  in

  (* Format.printf "%a" (TSys.pp_print_subsystems true) sys; *)

  let modules = Flags.enabled () in

  let old_log_level = Lib.get_log_level () in


  let run_analysis param' prop lower_bound upper_bound =

    Property.set_prop_status prop Property.PropUnknown;

    TSys.remove_invariants sys ;

    let sys' =
      (*if (lower_bound = num_weak_assumes) then
        List.fold_left
          (fun sys' wa ->
            TSys.add_to_trans (TSys.add_to_init sys' wa) (Term.bump_state Numeral.one wa)
          )
          base_sys
          (List.map
            (fun {LustreContract.svar} ->
               Var.mk_state_var_instance svar Numeral.zero |> Term.mk_var
            )
            weak_assumes
          )
      else*)
        TSys.add_to_init sys (mk_num_act_vars_bounded lower_bound)
    in

    let sys' =
      TSys.add_properties sys' [prop]
    in

    Format.printf "Looking for optimal value... LB=%d; UB=%d@." lower_bound upper_bound;

    let param' = Analysis.param_clone param' in

    Lib.set_log_level L_off ;

    analyze modules in_sys param' sys' ;

    Lib.set_log_level old_log_level;

    Format.printf "Analysis finished!@.";

    sys', param'
  in


  let rec disprove_property_linear param' prop last_cex max =
    if max > num_weak_assumes then

      print_result param' prop (TSys.add_properties sys [prop]) last_cex

    else (

      let sys', param' = run_analysis param' prop max num_weak_assumes in

      match Property.get_prop_status prop with
      | Property.PropUnknown
      | Property.PropKTrue _ -> (
        Format.printf "WARNING: no optimal solution@.";
        Property.set_prop_status prop Property.PropUnknown;
        print_result param' prop sys' last_cex
      )
      | Property.PropInvariant _ -> (
        Property.set_prop_status prop Property.PropUnknown;
        print_result param' prop sys' last_cex
      )
      | Property.PropFalse cex ->
        disprove_property_linear param' prop cex (max + 1)
    )
  in

  let rec disprove_property_binary param' prop last_cex lo hi =
    if lo > hi then (

      Property.set_prop_status prop Property.PropUnknown;
      print_result param' prop (TSys.add_properties sys [prop]) last_cex

    )
    else (

      let mid = lo + (hi-lo)/2 in

      let sys', param' = run_analysis param' prop mid hi in

      match Property.get_prop_status prop with
      | Property.PropUnknown
      | Property.PropKTrue _ -> (
        Format.printf "WARNING: no optimal solution@.";
        Property.set_prop_status prop Property.PropUnknown;
        print_result param' prop sys' last_cex
      )
      | Property.PropInvariant _ -> (
        disprove_property_binary param' prop last_cex lo (mid - 1)
      )
      | Property.PropFalse cex ->
        disprove_property_binary param' prop cex (mid + 1) hi
     
    )
  in

  match Flags.max_global_search () with
  | `Linear ->
    List.iter (fun p ->
      disprove_property_linear param p (get_cex p) 1
    ) props;
  | `Binary ->
    List.iter (fun p -> 
      disprove_property_binary param p (get_cex p) 1 num_weak_assumes
    ) props;

  KEvent.set_module mdl


let disprove_maximizing_locally in_sys param sys props weak_assumes =

  let disprove_property prop k =
    Property.set_prop_status prop Property.PropUnknown;

    let num_k = Numeral.of_int k in
    let solver = create_smt_solver (TSys.get_logic sys) in
    TSys.define_and_declare_of_bounds
      sys
      (SMTSolver.define_fun solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero num_k;

    TSys.init_of_bound None sys Numeral.zero
    |> SMTSolver.assert_term solver;
    for i = 0 to (k - 1) do
      TSys.trans_of_bound None sys (Numeral.of_int (i+1))
      |> SMTSolver.assert_term solver
    done;
    (*List.iter (fun {LustreContract.svar} ->
      Format.printf "%a@." StateVar.pp_print_state_var svar) weak_assumes;*)

    let soft_terms =
      List.map (fun ({LustreContract.svar} as wa) ->
        Lib.list_init
          (fun i ->
            Term.mk_var (Var.mk_state_var_instance svar (Numeral.of_int i))
          )
          k
        |> Term.mk_and, wa
      )
      weak_assumes
    in

    List.iter
      (fun (conj, _) -> SMTSolver.assert_soft_term solver conj 1)
      soft_terms;

    let prop_at_last_step =
      Term.bump_state num_k prop.Property.prop_term
    in
    SMTSolver.assert_term solver (Term.negate prop_at_last_step);

    try (
      let sat = SMTSolver.check_sat solver in
      assert (sat);

      let model =
        (* SMTSolver.get_model solver *)
        SMTSolver.get_var_values
          solver
          (TransSys.get_state_var_bounds sys)
          (TransSys.vars_of_bounds sys Numeral.zero num_k)
      in

      let eval term =
        Eval.eval_term (TSys.uf_defs sys) model term
        |> Eval.bool_of_value
      in

      let wa_model =
        List.map (fun (conj, wa) ->
          (LustreContract.prop_name_of_svar wa "weakly_assume" "", eval conj))
          soft_terms
      in

      (* Extract counterexample from solver *)
      let cex =
        Model.path_from_model
          (TransSys.state_vars sys) model num_k
      in

      KEvent.cex_wam
        (Model.path_to_list cex)
        wa_model in_sys param sys prop.Property.prop_name

    )
    with e -> raise e

  in

  let mdl = KEvent.get_module () in

  KEvent.set_module `WeakAssumpMaximizer;

  List.iter (fun p -> disprove_property p (get_cex_length p)) props;

  (*let prop, k = get_prop_with_shortest_cex props in

  disprove_property prop k;*)
  
  KEvent.set_module mdl
