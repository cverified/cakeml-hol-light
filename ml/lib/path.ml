(* ================================================================== *)
(*  Paths, HOL4's pathTheory (src/coalgebras/pathScript.sml), of      *)
(*  which the port has what the statements of CakeML need.  A path is *)
(*  a state and a lazy list of label and state pairs, which is the    *)
(*  type that HOL4 makes the type of a path of; HOL Light has no      *)
(*  greatest fixed point, so the one that okpath is of HOL4's         *)
(*  okpath_f is written out.  HOL4's first is path_first here,        *)
(*  because the port has one namespace and first is a variable of     *)
(*  statements of its own.                                            *)
(* ================================================================== *)

let path_tybij =
  let th = prove
   (`?x:A#(B#A)llist. (\x. T) x`,
    BETA_TAC THEN REWRITE_TAC[]) in
  new_type_definition "path" ("toPath","fromPath") th;;

let path_first = new_definition
  `path_first (p:(A,B)path) = FST (fromPath p)`;;

let stopped_at = new_definition
  `stopped_at (x:A) = (toPath (x,LNIL):(A,B)path)`;;

let pcons = new_definition
  `pcons (x:A) (r:B) p =
   (toPath (x,LCONS (r,path_first p) (SND (fromPath p))):(A,B)path)`;;

(* a path is OK when every step of it is a step of the relation,
   which HOL4 says as the greatest fixed point of okpath_f *)

let okpath_f = new_definition
  `okpath_f (R:A->B->A->bool) (X:((A,B)path)->bool) =
   {p | ?x. p = stopped_at x} UNION
   {p | ?x r q. p = pcons x r q /\ R x r (path_first q) /\ q IN X}`;;

let okpath = new_definition
  `okpath (R:A->B->A->bool) =
   {p | ?X. X SUBSET okpath_f R X /\ p IN X}`;;
