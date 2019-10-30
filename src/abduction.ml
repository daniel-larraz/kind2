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

let generalize trans_sys vars premise concl =

  let solver = SMTSolver.create_instance
    ~produce_abducts:true
    (TransSys.get_logic trans_sys)
    `CVC4_SMTLIB
  in

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero Numeral.one;

  SMTSolver.assert_term solver premise;

  Format.printf "A: Computing abduct...@.";

  let abduct =
    SMTSolver.get_conjunctive_abduct solver vars concl
  in

  Format.printf "A: %a@." Term.pp_print_term abduct;

  SMTSolver.delete_instance solver; 

  [abduct]
