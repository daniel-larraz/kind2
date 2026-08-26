(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

let handle_events input_sys aparam trans_sys = 

  (* Receive queued events *)
  let events = KEvent.recv () in

  (* Output events *)
  List.iter 
    (function (m, e) -> 
      KEvent.log
        L_debug
        "Message received from %a: %a"
        pp_print_kind_module m
        KEvent.pp_print_event e)
    events;

  (* Update transition system from events *)
  let _ =
    KEvent.update_trans_sys input_sys aparam trans_sys events
  in

  ()

let print_stats trans_sys =
  
  KEvent.log
    L_debug
    "@[<v>%a@,\
     Final statistics:@]"
    Pretty.print_line ();
  
  List.iter 
    (fun (mdl, stat) -> KEvent.log_stat mdl L_debug stat)
    (KEvent.all_stats ());
  
  match trans_sys with
  | None -> ()
  | Some trans_sys ->
    let status_kinds = TransSys.get_prop_status_and_kind_all_nocands trans_sys in
    KEvent.log_prop_status L_fatal trans_sys status_kinds


let on_exit trans_sys =

  print_stats trans_sys ;
    
  try 
    (* Send termination message to all worker processes *)
    KEvent.terminate () ;

    (* if trans_sys <> None then handle_events (get trans_sys); *)
      
  (* Skip if analysisning as a single process *)
  with Messaging.NotInitialized -> ()


(* List of modules to monitor, and do actions in case they crashes *) 
let monitor_modules = [`BMC; `IND]

(* modules for which other modules needs them to be active to function
   properly *)
let needed_by = function
  | `BMC -> [`IND; `IND2];
  | `IND -> [`BMC]
  | _ -> []

(* Set of core modules. The analysis goes on if at least one of them is
   active *)
let core_module = function
  | `IND | `BMC | `IC3QE | `IC3IA -> true
  | _ -> false


let pids_depend_on m child_pids =
  let deps = needed_by m in
  List.filter (fun (_, md) -> List.mem md deps) child_pids

(* Terminate an engine, and kill the solvers of its domain to unblock
   it if it did not exit. *)
let term_kill (id, dep) =
  KEvent.log L_warn "Terminating useless %a (%d)"
    pp_print_kind_module dep id;
  KEvent.terminate_worker id;
  minisleep 0.1;
  (match EngineDomains.find id with
   | Some c ->
     EngineDomains.kill_solvers c;
     KEvent.log L_warn "Killed solvers of not responding useless %a (%d)"
       pp_print_kind_module dep id
   | None -> ())

(* Kill engines that are not needed anymore because some of their dependencies
   have crashed. This function returns a boolean that is true when it is no
   longer necessary to continue the analysis because core components have
   crahsed.  *)
let kill_useless_engines child_pids =
  List.iter (fun m ->
      if not (List.exists (fun (_,x) -> x = m) child_pids) then
        List.iter term_kill (pids_depend_on m child_pids)
    ) monitor_modules;
  not (List.exists (fun (_,m) -> core_module m) child_pids)

let check_pending_processes run_process pending_processes sys child_pids =
  pending_processes := !pending_processes |> List.filter (function
    | ProcessCall.IC3IA_Call (_, _, prop, _) -> (
      match TransSys.get_prop_status sys prop.prop_name with
      | PropUnknown | PropKTrue _ -> true
      | _ -> false
    )
    | _ -> assert false
  ) ;
  match !pending_processes with
  | [] -> ()
  | _ -> (
    let num_of_ic3ia_modules =
      !child_pids |> List.filter (function
        | (_, `IC3IA) -> true
        | _ -> false
      )
      |> List.length
    in
    let diff = Flags.IC3IA.max_processes () - num_of_ic3ia_modules in
    if diff > 0 then
      let to_run, pending =
        list_split diff !pending_processes
      in
      pending_processes := pending ;
      List.iter (fun m -> run_process m) to_run ;
  )


(* Remove terminated engines from the list of running engines

   Return [true] if the last engine has terminated or some engine
   terminated with a runtime error. *)
let wait_for_children run_process pending_processes sys child_pids =

  match EngineDomains.take_finished () with

    (* No engine terminated *)
    | [] ->

      (* Terminate if the last engine has terminated *)
      !child_pids = []

    | finished -> (

      (* Process every engine that terminated *)
      let crashed =
        finished |> List.fold_left (fun crashed child ->

          let child_id = EngineDomains.id child in

          let crashed_too =
            match EngineDomains.outcome child with
            | EngineDomains.Done None ->
              KEvent.log L_info
                "Child process %d (%a) terminated normally"
                child_id
                pp_print_kind_module (EngineDomains.mdl child) ;
              false
            | EngineDomains.Done (Some e) ->
              KEvent.log L_warn
                "Child process %d (%a) terminated on exception: %s"
                child_id
                pp_print_kind_module (EngineDomains.mdl child)
                (Printexc.to_string e) ;
              true
            | EngineDomains.Running -> assert false
          in

          (* Remove engine from list *)
          child_pids := List.remove_assoc child_id !child_pids ;

          check_pending_processes run_process pending_processes sys child_pids ;

          crashed || crashed_too

        ) false
      in

      (* If some engine crashed, terminate the engines that depend on
         it, and stop the analysis if no core engine is left *)
      (crashed && kill_useless_engines !child_pids) ||
      !child_pids = []

    )

(* Giving up an engine when the analysis stops progressing.

   Engines are domains, and a stop-the-world collection needs every one
   of them to arrive at it. Where more of them are busy at once than the
   machine has cores, the ones that cannot be scheduled hold the
   rendezvous open while the ones that can spin waiting, taking the
   cores the missing ones need. The supervisor then does not run either,
   and an analysis can spend nine tenths of its wall clock making no
   progress at all. Measured on a four core Windows runner: a run took
   227s against a `--timeout` of 20s and never reached a counterexample
   that two engines find in one second. Linux and macOS share the
   machine proportionally and do not do this.

   It is a bad trade to prevent by starting fewer engines, because
   whether it happens depends on how many of them are busy together,
   which depends on the model: most runs never come near it, and would
   pay for the ones that do. So notice it instead. The supervisor knows
   when it is not being scheduled -- its own loop should come round
   every ten milliseconds -- and an engine given up while that is
   happening costs nothing, since nothing is progressing anyway.

   Which one goes is the mirror of what an engine is worth: invariant
   generation before the engines it feeds, and an engine that decides
   properties by itself last of all. *)
let shed_rank = function
  | `BMC -> 0
  | `IND -> 1
  | `IC3 | `IC3QE -> 2
  | `BMCSKIP -> 3
  | `IC3IA -> 4
  | `IND2 -> 5
  | _ -> 6   (* invariant generation, and anything else, go first *)

(* An iteration slower than this is the supervisor not being scheduled,
   not the supervisor working: everything it does in one takes
   milliseconds. *)
let stalled_iteration =
  (* PROBE ONLY, not for the PR: lets the verification job run an arm
     with shedding disabled, so both arms share a machine and a moment. *)
  match Sys.getenv_opt "KIND2_PROBE_NO_SHEDDING" with
  | Some _ -> infinity
  | None -> 2.0

(* How many in a row before giving an engine up. One can be a hiccup. *)
let stalls_before_shedding = 2

let last_iteration = ref 0.0
let consecutive_stalls = ref 0

let reset_shedding () =
  last_iteration := 0.0 ;
  consecutive_stalls := 0

(* Give up the least valuable engine still running, if there is one that
   is not the last. Returns whether one was given up. *)
let shed_one_engine child_pids =
  match
    !child_pids
    |> List.sort (fun (_, a) (_, b) -> compare (shed_rank b) (shed_rank a))
  with
  | [] | [ _ ] -> false            (* never leave the analysis with none *)
  | (id, mdl) :: _ ->
    KEvent.log L_warn
      "@[<hov>The analysis is not progressing: %a is being given up so \
       that the others can run.@ More engines are busy at once than this \
       machine can schedule.@]"
      pp_print_kind_module mdl ;
    KEvent.terminate_worker id ;
    ( match EngineDomains.find id with
      | Some c -> EngineDomains.kill_solvers c
      | None -> () ) ;
    child_pids := List.remove_assoc id !child_pids ;
    true

(* Watch how long an iteration of the polling loop takes, and give up an
   engine when several in a row say the supervisor is not running. *)
let watch_progress child_pids =
  let now = Unix.gettimeofday () in
  ( if !last_iteration > 0.0 then (
      if now -. !last_iteration > stalled_iteration then (
        incr consecutive_stalls ;
        if !consecutive_stalls >= stalls_before_shedding then
          if shed_one_engine child_pids then consecutive_stalls := 0
      ) else consecutive_stalls := 0
    ) ) ;
  last_iteration := Unix.gettimeofday ()

(* Polling loop *)
let rec loop
  run_process pending_processes
  ignore_props stop_if_falsified done_at timeout_analysis_reached
  child_pids input_sys aparam trans_sys
=

  watch_progress child_pids ;

  handle_events input_sys aparam trans_sys ;

  (* On Windows there is no SIGALRM-based wall clock timeout: enforce
     it here. [handle_events] has just refreshed the total time. *)
  ( if Sys.win32 then
      let timeout = Flags.timeout_wall () in
      if timeout > 0. && Stat.get_float Stat.total_time > timeout then
        raise TimeoutWall ) ;

  let done_at' =

    (* All properties proved? *)
    if (TransSys.all_props_proved trans_sys && not ignore_props)
    || (TransSys.at_least_one_prop_falsified trans_sys && stop_if_falsified)
    then (

      (* Has is_done been true in the last iteration? *)
      match done_at with

      | None ->
          (* Message after is_done becomes true first time *)
          KEvent.log L_info
            "<Done> @[<v>\
              All properties proved or disproved in %.3fs.@ \
              Waiting for children to terminate.\
            @]"
            (Stat.get_float Stat.total_time) ;

          (* Solvers of terminating engines are killed outright instead
             of shut down gracefully, as the engine processes and their
             solvers used to be killed. Solvers of the running engines
             are killed right away to unblock engines that are inside a
             solver call and would not see the termination message. *)
          EngineDomains.set_terminating true ;
          KEvent.terminate () ;
          EngineDomains.live () |> List.iter EngineDomains.kill_solvers ;
          Some (Unix.gettimeofday ())

      | Some t -> Some t

    ) else if timeout_analysis_reached () then (

      match done_at with

      | None ->

        let timeout_analysis = Flags.timeout_analysis () in

        KEvent.log L_info
          "<Done> @[<v>\
            Reached analysis timeout (%1.0f)@ \
            Waiting for children to terminate.
          @]" timeout_analysis ;

        EngineDomains.set_terminating true ;
        KEvent.terminate () ;
        EngineDomains.live () |> List.iter EngineDomains.kill_solvers ;
        Some (Unix.gettimeofday ())

      | Some t -> Some t

    ) else None

  in

  (* Check if child processes have died and exit if necessary *)
  if wait_for_children run_process pending_processes trans_sys child_pids || (
    match done_at with 
    | None -> false
    | Some t -> (Unix.gettimeofday () -. t) > 0.3
  ) then (

    (* Get messages after termination of all processes *)
    handle_events input_sys aparam trans_sys ;

    (* All properties proved? *)
    if TransSys.all_props_proved trans_sys then KEvent.terminate ()

    (* Have we reached the run timeout? *)
  ) else (

    (* Sleep *)
    minisleep 0.01 ;

    (* Continue polling loop *)
    loop
      run_process pending_processes
      ignore_props stop_if_falsified done_at' timeout_analysis_reached
      child_pids input_sys aparam trans_sys

  )
  

(* Entry point *)
let main run_process pending_processes ignore_props stop_if_falsified child_pids input_sys aparam trans_sys =
  (* Building the function checking whether we reached the analysis timeout. *)
  let timeout_analysis = Flags.timeout_analysis () in
  let timeout_analysis_reached =
    if timeout_analysis > 0.0 then (
      fun () ->
        Stat.get_float Stat.analysis_time > timeout_analysis
    ) else (
      fun () -> false
    )
  in

  let pending_processes = ref pending_processes in

  reset_shedding () ;

  (* Run main loop *)
  loop
    run_process pending_processes
    ignore_props stop_if_falsified None timeout_analysis_reached
    child_pids input_sys aparam trans_sys

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
