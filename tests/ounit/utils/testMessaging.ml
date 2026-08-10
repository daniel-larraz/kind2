(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

open OUnit2

module M = Messaging.Make (struct
  type t = unit

  let pp_print_message ppf () = Format.fprintf ppf "()"
end)

(* Longest we give a wait to come back, in seconds. Far above the
   period the messaging system wakes waiting domains at, so that a slow
   machine does not fail the test. *)
let patience = 10.

(* Run [f] in a domain of its own and report whether it returned within
   [patience]. The domain is left alone when it did not: it is blocked
   for good, and joining it would hang the test run instead of failing
   it. *)
let returns_in_time f =
  let returned = Atomic.make false in
  let _ = Domain.spawn (fun () -> f () ; Atomic.set returned true) in
  let deadline = Unix.gettimeofday () +. patience in
  while (not (Atomic.get returned)) && Unix.gettimeofday () < deadline do
    Thread.delay 0.01
  done ;
  Atomic.get returned

(* An engine blocks on its mailbox when it has nothing to do until
   another engine sends it something. It may be wrong about that: the
   engine it waits for may have exited, or the state it waits on may
   have been reached without a message left to announce it. Waiting
   must be bounded, so that an engine that mispredicted rechecks and
   moves on rather than blocking the whole analysis forever. *)
let test_wait_returns_without_any_message _ =
  let ctx = M.init_im () in
  M.run_im ctx ;
  let worker = M.init_worker `BMC 1 ctx in
  let waited =
    returns_in_time (fun () ->
        ignore (M.run_worker worker) ;
        (* Nothing is ever sent to this mailbox *)
        M.wait_for_message ())
  in
  assert_bool
    "wait_for_message did not return although no message was sent"
    waited

let tests = "Messaging" >::: [
  "wait_for_message returns without any message"
  >:: test_wait_returns_without_any_message ;
]

let () = run_test_tt_main tests
