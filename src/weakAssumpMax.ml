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

module TSys = TransSys

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

let disprove_maximizing in_sys param sys props weak_assumes =

  let mdl = KEvent.get_module () in

  KEvent.set_module `WeakAssumpMaximizer;

  let prop, k = get_prop_with_shortest_cex props in

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

  assert (SMTSolver.check_sat solver);

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

  Format.printf "Satisfied weak assumptions:@.";
  List.iter (fun (conj, wa) ->
    if eval conj then
      Format.printf "%s@." (LustreContract.prop_name_of_svar wa "weakly_assume" "")
  )
  soft_terms;
  Format.printf "@.";

  Format.printf "Unsatisfied weak assumptions:@.";
  List.iter (fun (conj, wa) ->
    if eval conj |> not then
      Format.printf "%s@." (LustreContract.prop_name_of_svar wa "weakly_assume" "")
  )
  soft_terms;
  Format.printf "@.";

  (* Extract counterexample from solver *)
  let cex =
    Model.path_from_model
      (TransSys.state_vars sys) model num_k 
  in

  KEvent.prop_status
    (Property.PropFalse (Model.path_to_list cex))
    in_sys param sys prop.Property.prop_name;
  
  KEvent.set_module mdl;
