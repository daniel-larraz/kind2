(* Does a busy thread starve the other threads of its domain on
   Windows?

   `st_thread_yield` in the runtime's `st_win32.h` is a line by line
   port of the pthreads one, and it carries the comment that came with
   it:

     Note: the POSIX spec prevents the above signal from pairing with
     this wait, which is good: we'll reliably continue waiting until
     the next yield() ...

   The guarantee named there is POSIX's, about `pthread_cond_signal`.
   The Windows file calls `WakeConditionVariable`, which promises no
   such thing. If that wake does pair with the yielding thread's own
   sleep, the thread returns, reads the `busy` flag it cleared itself,
   leaves the loop, retakes the master lock and carries on -- and the
   thread that was waiting for it never runs. The yield becomes a no
   operation, and it is what the tick thread uses every 50ms to
   preempt.

   So: one domain, one thread that works, one thread that measures. No
   oversubscription and no second domain, since the claim is about
   threads sharing one master lock. If the handoff works, the measuring
   thread is late by about the tick interval. If it does not, it is
   late for as long as the other thread cares to run.

   Kind 2's shape is about ten domains and about thirty threads between
   them, so several of its domains have more than one thread, and its
   supervisor polls its clock from one of them.

   Usage: yield_repro <busy|yield|alloc> <workers> <seconds>

     busy    workers compute and allocate; only the tick thread's
             preemption can move the master lock along
     yield   workers call Thread.yield in the loop as well, which is
             the same path taken directly
     alloc   workers allocate hard, so that anything wanting a poll
             point gets one often *)

let stop = Atomic.make false

let busy_work () =
  let x = ref 0 in
  while not (Atomic.get stop) do
    for i = 1 to 1_000_000 do x := (!x + i) land 0xffff done ;
    ignore (Sys.opaque_identity !x)
  done

let yield_work () =
  let x = ref 0 in
  while not (Atomic.get stop) do
    for i = 1 to 1_000_000 do x := (!x + i) land 0xffff done ;
    ignore (Sys.opaque_identity !x) ;
    Thread.yield ()
  done

let alloc_work () =
  let keep = ref (Obj.repr 0) in
  while not (Atomic.get stop) do
    for _ = 1 to 100_000 do
      keep := Obj.repr (Sys.opaque_identity (ref 0))
    done ;
    ignore (Sys.opaque_identity !keep)
  done

let () =
  let mode = Sys.argv.(1) in
  let workers = int_of_string Sys.argv.(2) in
  let seconds = float_of_string Sys.argv.(3) in
  let work = match mode with
    | "busy" -> busy_work
    | "yield" -> yield_work
    | "alloc" -> alloc_work
    | m -> failwith ("unknown mode " ^ m)
  in
  (* Said before anything is spawned, so that a run which prints
     nothing at all is known to have started. *)
  Printf.printf "  start %s workers=%d\n%!" mode workers ;
  let started = Unix.gettimeofday () in

  (* Every thread here, the measuring one included, belongs to the one
     domain the program starts with. A run with no workers is the
     control for Thread.delay itself. *)
  let threads = List.init workers (fun _ -> Thread.create work ()) in

  let worst = ref 0.0 and stalled = ref 0.0 and count = ref 0 in
  let previous = ref (Unix.gettimeofday ()) in
  while Unix.gettimeofday () -. started < seconds do
    Thread.delay 0.01 ;
    let now = Unix.gettimeofday () in
    let late = now -. !previous -. 0.01 in
    if late > 0.5 then ( incr count ; stalled := !stalled +. late ) ;
    if late > !worst then worst := late ;
    previous := now
  done ;
  Atomic.set stop true ;
  List.iter Thread.join threads ;
  let wall = Unix.gettimeofday () -. started in
  Printf.printf
    "%-6s workers=%-2d in 1 domain  cores=%-3d wall=%5.1fs  \
     worst wait %6.2fs  waits over 0.5s: %-4d  waiting %5.1fs of wall (%.0f%%)\n%!"
    mode workers (Domain.recommended_domain_count ()) wall !worst !count
    !stalled (100. *. !stalled /. wall)
