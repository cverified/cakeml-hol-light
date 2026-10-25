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
(* ------------------------------------------------------------------ *)
(* Where a proof attempt broke.  `prove` only ever says which        *)
(* exception came out of a tactic, so finding the step that failed   *)
(* used to mean splitting the proof into a `bsteps` list by hand.    *)
(* Instead THEN and THENL are shadowed by versions that remember the *)
(* goal each step is applied to: a failure then reports the goal the *)
(* failing step saw, and how many steps had succeeded before it.     *)
(* The kernel's own combinators are untouched, so this is what the   *)
(* tactics written after this file is loaded use, and it costs one   *)
(* ref write per step.                                               *)
(* ------------------------------------------------------------------ *)

let b_orig_then = (THEN);;
let b_orig_thenl = (THENL);;

(* the step count is progress: of two states the one that got
   further is the interesting one, because the failures of a
   backtracking combinator (ORELSE, FIRST, REPEAT, TRY) are
   expected and shallow *)

let b_steps = ref 0;;
let b_best = ref ((-1),(([],`T`):goal),"");;
let b_last = ref ((-1),(([],`T`):goal),"");;

let b_reset () =
  b_steps := 0;
  b_best := ((-1),(([],`T`):goal),"");
  b_last := ((-1),(([],`T`):goal),"");;

let b_note lab (g:goal) =
  (let (d,_,_) = !b_best in
   if !b_steps >= d then b_best := (!b_steps,g,lab));
  b_last := (!b_steps,g,lab);;

let b_watch lab (t:tactic) : tactic =
  fun g ->
    b_note lab g;
    let r = t g in
    b_steps := !b_steps + 1;
    r;;

let ((THEN):tactic->tactic->tactic) =
  fun t1 t2 -> b_orig_then (b_watch "" t1) (b_watch "" t2);;

let ((THENL):tactic->tactic list->tactic) =
  fun t1 tl ->
    let n = length tl in
    b_orig_thenl (b_watch "" t1)
      (map (fun (i,t) ->
              b_watch ("branch " ^ string_of_int i ^ " of " ^
                       string_of_int n) t)
           (zip (1--n) tl));;

let b_state lab d (asl,w) =
  say ("  " ^ lab ^ " after " ^ string_of_int d ^ " step(s)\n");
  (if !b_asm then
     do_list (fun (_,th) ->
       say ("    . " ^ string_of_term (concl th) ^ "\n"))
       (if length asl > 16 then fst(chop_list 16 asl) else asl));
  say ("  GOAL " ^ string_of_term w ^ "\n");;

let b_where () =
  let (d,g,lab) = !b_best in
  if d < 0 then say "  (no step recorded)\n" else
  (b_state ("the step that got furthest broke" ^
            (if lab = "" then "" else " (" ^ lab ^ ")")) d g;
   let (d2,g2,lab2) = !b_last in
   if d2 = d && snd g2 = snd g then () else
   b_state ("the last step tried broke" ^
            (if lab2 = "" then "" else " (" ^ lab2 ^ ")")) d2 g2);;

(* an attempt at a term: what the statement of the source says
   (`bt`, below) or a lemma that a proof wants on the way (`bp`,
   which hands the theorem back, so the attempts of one round can
   build on one another) *)

let bp nm tm f =
  let old = !cake_timeout in
  cake_timeout := !b_secs;
  b_reset ();
  let r =
    (try let th = with_timeout (fun () -> prove(tm, f ())) () in
         (b_ok := !b_ok + 1; say ("OK   " ^ nm ^ "\n"); Some th)
     with ex ->
       (b_bad := nm :: !b_bad;
        say ("FAIL " ^ nm ^ " " ^ Printexc.to_string ex ^ "\n");
        (if Printexc.to_string ex <>
            "Failure(\"TAC_PROOF: Unsolved goals\")"
         then b_where () else
           (try let _ = g tm in
                let _ = with_timeout (fun () -> e (f ())) () in
                b_show ()
            with _ -> say "  (no goal state)\n"));
        None)) in
  cake_timeout := old; r;;

let bt nm th f = let _ = bp nm (concl th) f in ();;

(* the theorem of an attempt that went well, for the next attempt
   of the round to use *)

let b_the = function
    Some th -> th
  | None -> failwith "b_the: the attempt failed";;
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
