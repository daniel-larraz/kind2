(* This file is part of the Kind 2 model checker.

   Copyright (c) 2024 by the Board of Trustees of the University of Iowa

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

module ME = ModelElement
module SVS = StateVar.StateVarSet

type cex = (StateVar.t * Model.value list) list

let create_solver_and_context sys k =
  let solver =
    SMTSolver.create_instance
      ~produce_unsat_assumptions:true
      ~minimize_cores:true
      (TransSys.get_logic sys)
      (Flags.Smt.solver ())
  in

  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero k;

  solver

let assert_init_and_trans solver sys k =
  TransSys.init_of_bound
    (Some (SMTSolver.declare_fun solver)) sys Numeral.zero
  |> SMTSolver.assert_term solver ;

  for i = 1 to (Numeral.to_int k) do
    TransSys.trans_of_bound
      (Some (SMTSolver.declare_fun solver)) sys (Numeral.of_int i)
    |> SMTSolver.assert_term solver ;
  done

let compute_unrolling solver sys k =
  let init =
    TransSys.init_of_bound
      (Some (SMTSolver.declare_fun solver)) sys Numeral.zero
  in
  let trans =
    List.init k (fun i ->
      TransSys.trans_of_bound
      (Some (SMTSolver.declare_fun solver)) sys (Numeral.of_int (i+1))
    )
  in
  Term.mk_and (init :: trans)

let actlits_of_core core =
  let aux acc scope =
    (ME.get_actlits_of_scope core scope)@acc
  in
  List.fold_left aux [] (ME.scopes_of_core core)

let actsvs_of_core core =
  actlits_of_core core
  |> List.map (ME.get_sv_of_actlit core)

let actlit_of_term t =
  match Term.destruct t with
  | Const s -> Symbol.uf_of_symbol s
  | _ -> assert false


let get_assignments svars cex =
  List.fold_left (fun acc (sv, values) ->
    if SVS.mem sv svars then (
      let _, assignments =
        List.fold_left (fun (i, acc') vl ->
          let var = Var.mk_state_var_instance sv (Numeral.of_int i) in
          match vl with
          | Model.Term e ->
            let assign = Term.mk_eq [Term.mk_var var; e] in
            i+1, assign :: acc'
          | _ -> assert false
        )
        (0, [])
        values
      in
      (sv, assignments) :: acc
    )
    else acc
  )
  []
  cex

let minimize_cex sys prop cex =
  let k =
    (Property.length_of_cex cex) - 1
  in
  let solver = create_solver_and_context sys (Numeral.of_int k) in
  let unrolling =
    Term.mk_and [compute_unrolling solver sys k; Term.mk_not (Term.bump_state (Numeral.of_int k) prop)] 
  in
  let svars =
    TransSys.state_vars sys
    |> SVS.of_list
  in
  let assignments = get_assignments svars cex in
  let svar_actl =
    assignments |> List.map (fun (sv, assign) ->
      let acl = Actlit.fresh_actlit () in
      let aclt = Term.mk_uf acl [] in
      SMTSolver.declare_fun solver acl;
      SMTSolver.assert_term solver (Term.mk_implies [aclt; Term.mk_and assign]) ;
      sv, aclt
    )
  in
  SMTSolver.assert_term solver (Term.mk_not unrolling) ;
  let act_terms = List.map snd svar_actl in
  let sat, unsat_core =
    SMTSolver.check_sat_assuming solver
      (fun _ -> true, [])
      (fun _ -> false, SMTSolver.get_unsat_core_lits solver)
      act_terms
  in
  assert (not sat);
  let cex' =
    cex |> List.filter (fun (sv, _) ->
      let act =
        match List.assoc_opt sv svar_actl with
        | None -> (Format.printf "SVAR: %a@." StateVar.pp_print_state_var sv; assert false)
        | Some x -> x
      in
      List.exists (fun e -> Term.equal e act) unsat_core
    )
  in
  (*List.iter (fun (sv,_) -> Format.printf "SV: %a@." StateVar.pp_print_state_var sv) cex ;
  List.iter (fun (sv,_) -> Format.printf "SV': %a@." StateVar.pp_print_state_var sv) cex' ;*)
  cex'


let is_any_cex_blocked sys core prop_cex_lst =
  let svars =
    TransSys.state_vars sys
    |> SVS.of_list
  in
  let actlits = actlits_of_core core in
  let actsvs = actsvs_of_core core in
  let actsv_terms =
    List.map
      (fun sv -> Term.mk_var (Var.mk_const_state_var sv) |> Term.mk_not)
      actsvs
  in
  let act_terms = List.map Actlit.term_of_actlit actlits in
  let is_cex_blocked (name, cex) =
    let k =
      (Property.length_of_cex cex) - 1
      |> Numeral.of_int
    in
    let solver = create_solver_and_context sys k in
    assert_init_and_trans solver sys k ;
    List.iter (SMTSolver.declare_fun solver) actlits ;
    cex |> List.iter (fun (sv, values) ->
      values |> List.iteri (fun i vl ->
        if SVS.mem sv svars then (
          let var = Var.mk_state_var_instance sv (Numeral.of_int i) in
          match vl with
          | Model.Term e ->
            let assign = Term.mk_eq [Term.mk_var var; e] in
            SMTSolver.assert_term solver assign
          | _ -> assert false
        )
      )
    ) ;
    List.iter
      (fun (at, svt) -> SMTSolver.assert_term solver (Term.mk_implies [at; svt]))
      (List.combine act_terms actsv_terms);
    let sat, unsat_core =
      SMTSolver.check_sat_assuming solver
        (fun _ -> true, [])
        (fun _ -> false, SMTSolver.get_unsat_core_lits solver)
        act_terms
    in
    if sat then (
      let model =
        SMTSolver.get_var_values
          solver
          (TransSys.get_state_var_bounds sys)
          (TransSys.vars_of_bounds sys Numeral.zero k)
      in
      
      (* Extract new counterexample from model *)
      let new_cex =
        Model.path_from_model (TransSys.state_vars sys) model k
        |> Model.path_to_list
        |> List.filter (fun (sv,_) ->
          not (List.exists (fun sv' -> StateVar.equal_state_vars sv sv') actsvs)
        )
      in

      TransSys.set_prop_false sys name new_cex ;
    ) ;
    let refinement =
      if List.length unsat_core = List.length act_terms then None
      else
        let symbols = List.map actlit_of_term unsat_core in
        Some (ME.filter_core symbols core)
    in
    not sat, refinement
  in
  let rec loop = function
  | [] -> false, None
  | prop_cex :: lst -> (
    let is_blocked, refinement =
      is_cex_blocked prop_cex
    in
    if is_blocked then is_blocked, refinement
    else loop lst
  )
  in
  loop prop_cex_lst

let mk_refinement sys scope core actlits =
  let eq_of_actlit = ME.eq_of_actlit_sv core in
  let eqs =
    List.map (fun t -> eq_of_actlit ~with_act:false t) actlits
  in
  let init_eq = List.map (fun eq -> eq.ME.init_opened) eqs
  |> Term.mk_and in
  let trans_eq = List.map (fun eq -> eq.ME.trans_opened) eqs
  |> Term.mk_and in
  let sys' =
    TransSys.set_subsystem_equations sys scope init_eq trans_eq
  in
  sys'


let compute_core_of_sys in_sys sys scope =
  (*Format.printf "SCOPE: %a@." Scope.pp_print_scope scope;
  Format.printf "SYS: %a@." (TransSys.pp_print_subsystems true) sys;*)
  let refined_sys =
    TransSys.find_subsystem_of_scope sys scope
  in
  let loc_core =
    ME.treat_subnode in_sys ME.empty_loc_core refined_sys
  in
  ME.loc_core_to_new_core loc_core


let instrument_refined_sys in_sys sys scopes refinement_map =
  List.fold_left
    (fun (core', test_core', sys) scope ->
      let keep =
        match Scope.Map.find_opt scope refinement_map with
        | None -> []
        | Some actlits -> actlits
      in
      ME.reset_actlit_count ();
      let core = compute_core_of_sys in_sys sys scope in
      let eq_of_actlit = ME.eq_of_actlit_sv core in
      let keep_core = ME.filter_core keep core in
      let test_core = ME.core_diff core keep_core in
      let test = ME.get_actlits_of_scope test_core scope in
      let eqs =
        List.map (fun k -> eq_of_actlit ~with_act:false k) keep @
        List.map (fun t -> eq_of_actlit ~with_act:true t) test
      in
      let init_eq = List.map (fun eq -> eq.ME.init_opened) eqs
      |> Term.mk_and in
      let trans_eq = List.map (fun eq -> eq.ME.trans_opened) eqs
      |> Term.mk_and in
      let sys' =
        TransSys.set_subsystem_equations sys scope init_eq trans_eq
      in
      let actsvs = actsvs_of_core test_core in
      let sys' =
        List.fold_left (fun acc sv ->
          TransSys.add_global_constant acc (Var.mk_const_state_var sv)
        ) sys' actsvs
      in
      ME.core_union core' core, ME.core_union test_core' test_core, sys'
    )
    (ME.empty_core, ME.empty_core, sys)
    scopes
