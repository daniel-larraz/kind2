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

   Both oversubscribe the machine identically. If only the allocating
   arm stalls, the cause is the rendezvous and not the oversubscription.

   Usage: stw_repro <alloc|compute> <domains> <seconds> *)

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

let () =
  let mode = Sys.argv.(1) in
  let domains = int_of_string Sys.argv.(2) in
  let seconds = float_of_string Sys.argv.(3) in
  let work = match mode with
    | "alloc" -> alloc_work
    | "compute" -> compute_work
    | m -> failwith ("unknown mode " ^ m)
  in
  let started = Unix.gettimeofday () in
  let spawned = List.init domains (fun _ -> Domain.spawn work) in

  (* The ticker: how late it is, is the measurement. *)
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
  List.iter Domain.join spawned ;
  let wall = Unix.gettimeofday () -. started in
  Printf.printf
    "%-7s domains=%-3d cores=%-3d wall=%5.1fs  worst stall %6.2fs  \
     stalls over 0.5s: %-4d  stalled %5.1fs of wall (%.0f%%)\n%!"
    mode domains (Domain.recommended_domain_count ()) wall !worst !count
    !stalled (100. *. !stalled /. wall)
