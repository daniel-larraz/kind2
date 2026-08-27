(* Does OCaml stop running when busy domains outnumber the cores?

   Kind 2 stalls on Windows CI in a way it never does on Linux or macOS:
   for seconds at a stretch no OCaml code executes anywhere in the
   process, while the process itself holds every core spinning inside
   the runtime. This asks the same question with nothing of Kind 2 in
   it -- no solvers, no subprocesses, no libraries.

   The measurement is a thread that means to wake every 10ms. When it
   wakes 5 seconds late, OCaml was not running: the thread needs the
   runtime lock, and no amount of scheduling pressure alone keeps a
   thread off a machine for that long when the runtime is willing to
   hand the lock over.

   Two arms, and the difference between them is the whole point:

     alloc    each domain allocates, so minor collections are frequent,
              and a minor collection in OCaml 5 is a stop-the-world
              rendezvous that every domain must reach.
     compute  each domain does integer arithmetic and allocates
              nothing, so there is no rendezvous to reach.

     threads  as alloc, and each domain also runs two systhreads that
              allocate, since that is the shape Kind 2 has: about ten
              domains and about thirty threads between them, every one
              of which has to be at a safe point for the rendezvous to
              complete.

   The first two oversubscribe the machine identically. If only the
   allocating arm stalls, the cause is the rendezvous and not the
   oversubscription.

     io       half the domains block in `Unix.read` on a pipe while
              the other half allocate. This is the shape Kind 2 has and
              the one none of the arms above test: its engine domains
              sit in a read waiting for a solver, and a rendezvous has
              to wait for a domain that is inside a blocking call. On
              POSIX the runtime can interrupt one with a signal; that
              machinery is not the same on Windows.

   The first two oversubscribe the machine identically. If only the
   allocating arm stalls, the cause is the rendezvous and not the
   oversubscription.

   The ticker runs until the last domain has been joined, not until the
   clock runs out: an earlier version stopped measuring first, and the
   one place Windows looked pathological -- domains taking seconds to
   notice a flag -- fell outside the window.

   Usage: stw_repro <alloc|compute|threads|io> <domains> <seconds> *)

let stop = Atomic.make false

let alloc_work () =
  let keep = ref (Obj.repr 0) in
  while not (Atomic.get stop) do
    for _ = 1 to 100_000 do
      keep := Obj.repr (Sys.opaque_identity (ref 0))
    done ;
    ignore (Sys.opaque_identity !keep)
  done

(* Integer arithmetic in a mutable cell: unboxed, so not one word is
   allocated and no minor collection is ever needed. *)
let compute_work () =
  let x = ref 0 in
  while not (Atomic.get stop) do
    for i = 1 to 10_000_000 do
      x := (!x + i) land 0xffff
    done ;
    ignore (Sys.opaque_identity !x)
  done

(* Kind 2's domains each run threads of their own, and a rendezvous
   waits for threads as well as for domains. *)
let threads_work () =
  let mine = List.init 2 (fun _ -> Thread.create alloc_work ()) in
  alloc_work () ;
  List.iter Thread.join mine

(* Blocked in a read almost all of the time, as an engine waiting on
   its solver is. Woken now and then so that it is a blocking call and
   not a dead one. *)
let io_work fd () =
  let buf = Bytes.create 1 in
  while not (Atomic.get stop) do
    match Unix.read fd buf 0 1 with _ -> () | exception _ -> ()
  done

let () =
  let mode = Sys.argv.(1) in
  let domains = int_of_string Sys.argv.(2) in
  let seconds = float_of_string Sys.argv.(3) in
  let started = Unix.gettimeofday () in

  (* The measurement, on a thread of its own so that it keeps running
     while the domains are joined. *)
  let worst = ref 0.0 and stalled = ref 0.0 and count = ref 0 in
  let finished = Atomic.make false in
  let ticker =
    Thread.create
      (fun () ->
        let previous = ref (Unix.gettimeofday ()) in
        while not (Atomic.get finished) do
          Thread.delay 0.01 ;
          let now = Unix.gettimeofday () in
          let late = now -. !previous -. 0.01 in
          if late > 0.5 then ( incr count ; stalled := !stalled +. late ) ;
          if late > !worst then worst := late ;
          previous := now
        done)
      ()
  in

  let pipes = ref [] in
  let work_for i =
    match mode with
    | "alloc" -> alloc_work
    | "compute" -> compute_work
    | "threads" -> threads_work
    | "io" ->
      if i mod 2 = 1 then (
        let r, w = Unix.pipe () in
        pipes := (r, w) :: !pipes ;
        io_work r )
      else alloc_work
    | m -> failwith ("unknown mode " ^ m)
  in
  let spawned = List.init domains (fun i -> Domain.spawn (work_for i)) in

  (* Traffic for the blocked domains, so that they are waiting on a
     pipe that does deliver rather than on one that never will. *)
  let feeder =
    Thread.create
      (fun () ->
        while not (Atomic.get stop) do
          Thread.delay 0.5 ;
          List.iter
            (fun (_, w) -> try ignore (Unix.write w (Bytes.make 1 'x') 0 1) with _ -> ())
            !pipes
        done)
      ()
  in

  while Unix.gettimeofday () -. started < seconds do Thread.delay 0.05 done ;
  Atomic.set stop true ;
  Thread.join feeder ;
  (* Let go of anyone still inside a read. *)
  List.iter (fun (_, w) -> try ignore (Unix.write w (Bytes.make 1 'x') 0 1) with _ -> ()) !pipes ;

  let joining = Unix.gettimeofday () in
  List.iter Domain.join spawned ;
  let joined = Unix.gettimeofday () -. joining in
  Atomic.set finished true ;
  Thread.join ticker ;
  List.iter (fun (r, w) -> (try Unix.close r with _ -> ()) ; try Unix.close w with _ -> ()) !pipes ;

  let wall = Unix.gettimeofday () -. started in
  Printf.printf
    "%-7s domains=%-3d cores=%-3d wall=%5.1fs  join%6.2fs  worst stall %6.2fs  \
     stalls over 0.5s: %-4d  stalled %5.1fs of wall (%.0f%%)\n%!"
    mode domains (Domain.recommended_domain_count ()) wall joined !worst
    !count !stalled (100. *. !stalled /. wall)
