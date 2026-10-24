(* tools/bh.ml: the batch harness -- many proof attempts in one
   load of the session.
   Each attempt is tried under a processor-time budget; a failure
   prints its exception (and the goals it leaves) and the next
   attempt goes on, so one round of the REPL gives the feedback of
   a whole batch.  Everything also goes to a log file, which has no
   scrollback limit. *)
let b_log = ref stdout;;
let b_open f = b_log := open_out f;;
let say s =
  print_string s;
  (if !b_log != stdout then output_string !b_log s);
  flush !b_log;;
let b_secs = ref 120;;
let b_ok = ref 0;;
let b_bad = ref ([]:string list);;
let b_asm = ref false;;
let b_goals () = let (_,gls,_) = hd (!current_goalstack) in gls;;
let b_show () =
  let gls = b_goals () in
  say ("  " ^ string_of_int (length gls) ^ " goal(s) left\n");
  do_list (fun (asl,w) ->
    (if !b_asm then
       do_list (fun (_,th) ->
         say ("    . " ^ string_of_term (concl th) ^ "\n")) asl);
    say ("  GOAL " ^ string_of_term w ^ "\n"))
    (if length gls > 4 then fst(chop_list 4 gls) else gls);;
let bt nm th f =
  let old = !cake_timeout in
  cake_timeout := !b_secs;
  (try let _ = with_timeout (fun () -> prove(concl th, f ())) () in
       (b_ok := !b_ok + 1; say ("OK   " ^ nm ^ "\n"))
   with ex ->
     (b_bad := nm :: !b_bad;
      say ("FAIL " ^ nm ^ " " ^ Printexc.to_string ex ^ "\n");
      if Printexc.to_string ex =
         "Failure(\"TAC_PROOF: Unsolved goals\")"
      then
        (try let _ = g (concl th) in
             let _ = with_timeout (fun () -> e (f ())) () in
             b_show ()
         with _ -> say "  (no goal state)\n")));
  cake_timeout := old;;
(* a proof applied one step at a time: which step fails, and what
   the goal state is when it does.  One round of the REPL then
   gives what a dozen interactive steps used to. *)
let bsteps nm th tacs =
  let _ = g (concl th) in
  let k = ref 0 in
  (try do_list (fun t ->
       k := !k + 1;
       let _ = with_timeout (fun () -> e t) () in ()) tacs;
     say (nm ^ ": all " ^ string_of_int !k ^ " steps ok\n")
   with ex ->
     say (nm ^ ": step " ^ string_of_int !k ^ " failed " ^
          Printexc.to_string ex ^ "\n"));
  (try b_show () with _ -> say "  (no goal state)\n");;
(* the same, but each step is tried as the chain of the steps so
   far (t1 THEN ... THEN tk) against the whole goal, as the finished
   proof will have it: `bsteps` applies a step to the first goal
   only, as the interactive `e` does, so a step list that passes it
   can still break when the steps are chained. *)
let bchain nm th tacs =
  let n = length tacs in
  let chain k = end_itlist (fun a b -> a THEN b)
                  (fst(chop_list k tacs)) in
  let rec go k =
    if k > n then
      (say (nm ^ ": the chain of all " ^ string_of_int n ^ " ok\n");
       let gls = (try length (b_goals ()) with Failure _ -> -1) in
       if gls = 0 then say "  and the goal is proved\n"
       else (say ("  but " ^ string_of_int gls ^
                  " goal(s) are left\n"); b_show ()))
    else
      try let _ = g (concl th) in
          let _ = with_timeout (fun () -> e (chain k)) () in
          go (k + 1)
      with ex ->
        (say (nm ^ ": the chain breaks at step " ^
              string_of_int k ^ " " ^ Printexc.to_string ex ^ "\n");
         if k <= 1 then () else
         try let _ = g (concl th) in
             let _ = with_timeout (fun () -> e (chain (k-1))) () in
             b_show ()
         with _ -> say "  (no goal state)\n") in
  go 1;;
let b_end () =
  say ("BATCH ok=" ^ string_of_int !b_ok ^ " bad=" ^
       string_of_int (length !b_bad) ^ ":" ^
       itlist (fun s t -> " " ^ s ^ t) (rev !b_bad) "\n");
  (if !b_log != stdout then close_out !b_log);
  b_log := stdout; b_ok := 0; b_bad := [];;
print_string "BH loaded\n";;
