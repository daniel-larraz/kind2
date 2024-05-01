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

(** @author Daniel Larraz
*)

type cex = (StateVar.t * Model.value list) list

val compute_core_of_sys :
  'a InputSystem.t ->
  TransSys.t ->
  Scope.t ->
  ModelElement.core

val instrument_refined_sys :
  'a InputSystem.t ->
  TransSys.t ->
  Scope.t list ->
  UfSymbol.t list Scope.Map.t ->
  ModelElement.core * ModelElement.core * TransSys.t

val minimize_cex :
  TransSys.t ->
  Term.t ->
  cex ->
  cex

val is_any_cex_blocked :
  TransSys.t ->
  ModelElement.core ->
  (string * cex) list ->
  bool * ModelElement.core option

val mk_refinement :
  TransSys.t ->
  Scope.t ->
   ModelElement.core ->
  UfSymbol.t list ->
  TransSys.t
