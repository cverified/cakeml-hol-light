(* ================================================================== *)
(*  The value of a term, where a statement of a source is one.        *)
(*                                                                    *)
(*  A CakeML source may state a theorem as the value of an ML         *)
(*  expression of the derived rules of the logic, and one of those    *)
(*  rules computes the value of a term: HOL4 does that with the       *)
(*  compset of its whole development, which HOL Light has no          *)
(*  counterpart of.  So the port says which definitions the term      *)
(*  reaches (tools/derive.py reads them off the bodies), and this     *)
(*  unfolds them and reduces the arithmetic that is left.             *)
(* ================================================================== *)

let CAKE_EVAL defs tm =
  (TRY_CONV (REWRITE_CONV defs) THENC
   TRY_CONV NUM_REDUCE_CONV THENC
   TRY_CONV (REWRITE_CONV [])) tm;;

(* HOL4's Q.SPEC reads its quotation in the context of the         *)
(* theorem, so a variable of it has the type the theorem gives it; *)
(* HOL Light's SPEC takes a term that is typed already, and a      *)
(* quotation of a bare variable is of a type of its own.  These    *)
(* give the term the type of the variable it stands for, and are   *)
(* HOL Light's rules in every other respect.                       *)

let CAKE_SPEC tm th =
  let v = fst (dest_forall (concl th)) in
  let tm = try inst (type_match (type_of tm) (type_of v) []) tm
           with Failure _ -> tm in
  SPEC tm th;;

let CAKE_SPECL tms th = rev_itlist CAKE_SPEC tms th;;

let CAKE_GEN tm th =
  let n = fst (dest_var tm) in
  let v = try find (fun w -> fst (dest_var w) = n) (frees (concl th))
          with Failure _ -> tm in
  GEN v th;;

let CAKE_GENL tms th = itlist CAKE_GEN tms th;;

let CAKE_INST l th =
  let fv = frees (concl th) in
  let fix (t,v) =
    let n = fst (dest_var v) in
    try let w = find (fun w -> fst (dest_var w) = n) fv in
        (try inst (type_match (type_of t) (type_of w) []) t
         with Failure _ -> t), w
    with Failure _ -> (t,v) in
  INST (map fix l) th;;
