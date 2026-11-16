(* ======================================================== *)
(*  HashtableProg: ported from HOL4's
    basis/HashtableProgScript.sml
    A definition theory, with 1 definition and no theorems.  Needed
    by CommandLineProg.ml.  *)
(* ======================================================== *)

(*
  A module about hash tables for the CakeML standard basis library.
*)

needs "basis/SetProg.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "HashtableProg"
  ["SetProg"; "ml_prog"; "ml_translator"];;

(* HOL4 HashtableProgScript.sml:10: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:12: ML code, not ported *)

(*Local structure:
  local
    hashtable                     -- Hidden
  in
    delete
    lookup
    toAscList
    size
    local
      initBuckets                 -- Hidden
    in
      empty
      clear
      local
        staticInsert              -- Hidden
      in
        local
          doubleCapacity          -- Hidden
        in
          local
            load_treshold_den     -- Hidden
          in
            local
              load_treshold_num   -- Hidden
            in
              insert
*)


(* HOL4 HashtableProgScript.sml:43: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:45-52: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:54-56: the ML values that the definitions
   below antiquote *)

let hashtable_con_stamp_def,hashtable_con_stamp_ind = define_guess
  `hashtable_con_stamp = OPTION_MAP SND hashtable_con_stamp`;;

(* HOL4 HashtableProgScript.sml:62: ML code, not ported *)

(* provides the Hashtable.hashtable name for the hashtable type *)
(* HOL4 HashtableProgScript.sml:65-66: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:68-84: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:86-95: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:97-101: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:103-107: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:109: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:111-113: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:115: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:117-125: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:127-132: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:134: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:136-150: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:152-153: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:155-157: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:159-171: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:173: ML code, not ported *)

(*Load treshold values for insert function, default 3/4*)
(* HOL4 HashtableProgScript.sml:176-182: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:184: ML code, not ported *)

(* HOL4 HashtableProgScript.sml:186: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
