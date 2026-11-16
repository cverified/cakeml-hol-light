(* ======================================================== *)
(*  holKernelPmatch: ported from HOL4's
    candle/standard/monadic/holKernelPmatchScript.sml
    A definition theory, with no definitions and 26 theorems.
    Needed by ml_hol_kernel_funsProg.ml.  *)
(* ======================================================== *)

(*
  This file proves alternative definitions of those HOL kernel
  functions that have complex pattern matching. The new definitions
  use PMATCH-based pmatch expressions instead of HOL's standard
  per-datatype case constants.
*)

needs "candle/standard/monadic/holKernel.ml";;
needs "lib/patternMatches.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holKernelPmatch"
  ["holKernel"; "ml_monadBase"];;

let _ = do_list hide_constant ["failwith"; "free"; "not"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["return","errorLogMonad_return";
   "return","errorMonad_return"];;

(* HOL4 holKernelPmatchScript.sml:17: the overload failwith, which the port
   expands *)
(* HOL4 holKernelPmatchScript.sml:18: the overload raise_clash, which the
   port expands *)
(* HOL4 holKernelPmatchScript.sml:19: the overload handle_clash, which the
   port expands *)

(* HOL4 holKernelPmatchScript.sml:23: the type abbreviation M, which the
   port expands *)

(* TODO: stolen from deepMatchesLib.sml; should be exported? *)
(* [local] *)
let PAIR_EQ_COLLAPSE = prove
 (`(((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a,b)))`,
  CHEAT_TAC);;

(* HOL4 holKernelPmatchScript.sml:32-37: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:39-44: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:46-62: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:64: ML code, not ported *)
(* -- *)

(* HOL4 holKernelPmatchScript.sml:67-69: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:71-72: a proof *)

(* HOL4 holKernelPmatchScript.sml:74-77: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:81-86: a theorem whose statement the port
   cannot state yet: codomain_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:87: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:89-96: a theorem whose statement the port
   cannot state yet: rev_assocd_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:97: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:99-115: a theorem whose statement the port
   cannot state yet: type_of_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:116: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:118-133: a theorem whose statement the
   port cannot state yet: raconv_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:134: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:136-141: a theorem whose statement the
   port cannot state yet: is_var_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:142: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:144-149: a theorem whose statement the
   port cannot state yet: is_const_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:150: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:152-157: a theorem whose statement the
   port cannot state yet: is_abs_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:158: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:160-165: a theorem whose statement the
   port cannot state yet: is_comb_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:166: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:168-174: a theorem whose statement the
   port cannot state yet: mk_abs_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:175: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:177-188: a theorem whose statement the
   port cannot state yet: mk_comb_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:189: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:191-197: a theorem whose statement the
   port cannot state yet: dest_var_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:198: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:200-206: a theorem whose statement the
   port cannot state yet: dest_const_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:207: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:209-215: a theorem whose statement the
   port cannot state yet: dest_comb_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:216: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:218-224: a theorem whose statement the
   port cannot state yet: dest_abs_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:225: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:227-235: a theorem whose statement the
   port cannot state yet: vfree_in_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:236: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:238-245: a theorem whose statement the
   port cannot state yet: rator_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:246: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:248-255: a theorem whose statement the
   port cannot state yet: rand_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:256: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:258-265: a theorem whose statement the
   port cannot state yet: dest_eq_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:266: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:268-275: a theorem whose statement the
   port cannot state yet: is_eq_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:276: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:278-290: a theorem whose statement the
   port cannot state yet: TRANS_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:291: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:293-314: a theorem whose statement the
   port cannot state yet: MK_COMB_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:315: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:317-328: a theorem whose statement the
   port cannot state yet: ABS_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:329: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:331-340: a theorem whose statement the
   port cannot state yet: BETA_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:341: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:343-352: a theorem whose statement the
   port cannot state yet: EQ_MP_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:353: ML code, not ported *)

(* HOL4 holKernelPmatchScript.sml:355-363: a theorem whose statement the
   port cannot state yet: SYM_PMATCH *)
(* HOL4 holKernelPmatchScript.sml:364: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["failwith";
   "free";
   "not"];;

(* and the interface *)
let _ = unhide_overloads ();;
