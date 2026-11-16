(* ======================================================== *)
(*  patternMatches: ported from HOL4's
    src/pattern_matches/patternMatchesScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 5 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: option list *)
let PMATCH_ROW_COND_def = new_definition
  `PMATCH_ROW_COND pat guard inp v = (
     (pat v = inp) /\ (guard v))`;;
let PMATCH_ROW_def = new_definition
  `PMATCH_ROW pat guard rhs i =
     (OPTION_MAP rhs (some (\v. PMATCH_ROW_COND pat guard i v)))`;;
let PMATCH_INCOMPLETE_def = new_definition
  `PMATCH_INCOMPLETE = ARB`;;
let PMATCH_def,PMATCH_ind = define_guess
  `(PMATCH v [] = PMATCH_INCOMPLETE) /\
   (PMATCH v (CONS r rs) = option_CASE (r v) (PMATCH v rs) I)`;;
