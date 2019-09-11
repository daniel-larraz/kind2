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

(** Weak Assumption Maximizer

    @author Daniel Larraz
*)

type 'a analyze_func =
  Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> unit

val disprove_maximizing_locally: 'a InputSystem.t -> Analysis.param -> TransSys.t ->
  Property.t list -> LustreContract.svar list -> unit

val disprove_maximizing_globally:
  'a analyze_func -> 'a InputSystem.t -> Analysis.param -> TransSys.t ->
  Property.t list -> LustreContract.svar list -> unit

