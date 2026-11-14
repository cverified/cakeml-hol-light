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
