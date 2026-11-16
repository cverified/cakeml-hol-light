(* ======================================================== *)
(*  cfHeaps: ported from HOL4's
    characteristic/cfHeapsScript.sml
    A definition theory, with 2 definitions and 15 theorems.  Needed
    by cf.ml, cfApp.ml, cfDiv.ml, cfMain.ml, cfNormalise.ml,
    cfStore.ml, cfTactics.ml, panStatic.ml and pan_passes.ml.  *)
(* ======================================================== *)

(*
  Defines what is means for a CF separation logic assertion to be "local".
*)

needs "characteristic/cfHeapsBase.ml";;
needs "lib/set_sep.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfHeaps"
  ["cfHeapsBase"];;

let _ = do_list hide_constant ["cf"];;

(* HOL4 cfHeapsScript.sml:10: ML code, not ported *)

(*------------------------------------------------------------------*)
(* hchange: using a [H1 ==>> H2] theorem modulo frame rule *)

let hchange_lemma' = prove
 (`!H1 H1' H H' H2. SEP_IMP H1 H1' ==> SEP_IMP H (H1 * H2) /\ SEP_IMP (
    H1' * H2) H' ==> SEP_IMP H H'`,
  CHEAT_TAC);;

let hchange_lemma = prove
 (`!H1 H1' H H' H2. SEP_IMP H1 H1' /\ SEP_IMP H (H1 * H2) /\ SEP_IMP (
    H1' * H2) H' ==> SEP_IMP H H'`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(** Locality *)

(* local = frame rule + consequence rule + garbage collection *)

let local_def = new_definition
  `local cf (H:(heap_part->bool)->bool) (Q:res->(heap_part->bool)->bool) =
     (!(h:heap_part->bool). H h ==> (?H1 H2 Q1.
       (H1 * H2) h /\
       cf H1 Q1 /\
       (SEP_IMPPOST (STARPOST Q1 H2) (STARPOST Q GC))))`;;

let is_local_def = new_definition
  `is_local cf = (cf = local cf)`;;

(* Properties of [local] *)

let local_elim = prove
 (`!cf H Q. cf H Q ==> local cf H Q`,
  CHEAT_TAC);;

let local_local = prove
 (`!cf. local (local cf) = local cf`,
  CHEAT_TAC);;

let local_is_local = prove
 (`!F'. is_local (local F') = T`,
  CHEAT_TAC);;

let is_local_prove = prove
 (`!F'. (!H Q. F' H Q <=> local F' H Q) ==> is_local F'`,
  CHEAT_TAC);;

let local_frame_gc = prove
 (`!F' H H1 H2 Q1 Q.
      is_local F' ==>
      F' H1 Q1 ==> SEP_IMP H (H1 * H2) ==> SEP_IMPPOST (STARPOST Q1 H2)
        (STARPOST Q GC) ==>
      F' H Q`,
  CHEAT_TAC);;

let local_frame = prove
 (`!H1 H2 Q1 F' H Q.
      is_local F' ==>
      F' H1 Q1 ==> SEP_IMP H (H1 * H2) ==> SEP_IMPPOST (STARPOST Q1 H2) Q
        ==>
      F' H Q`,
  CHEAT_TAC);;

let local_gc_pre_on = prove
 (`!HG H' F' H Q.
     is_local F' ==> SEP_IMP H (HG * H') ==>
     F' H' Q ==>
     F' H Q`,
  CHEAT_TAC);;

let local_gc_post = prove
 (`!Q' F' H Q.
     is_local F' ==>
     F' H Q' ==> SEP_IMPPOST Q' (STARPOST Q GC) ==>
     F' H Q`,
  CHEAT_TAC);;

(* Extraction of premisses from [local] *)

let local_intro_prop = prove
 (`!F' H P Q.
      is_local F' ==>
      (P ==> F' H Q) ==>
      F' (H * cond P) Q`,
  CHEAT_TAC);;

(** Extraction of existentials from [local] *)

let local_extract_exists = prove
 (`!F' A J Q.
      is_local F' ==>
      (!x. F' (J x) Q) ==>
      F' (SEP_EXISTS J) Q`,
  CHEAT_TAC);;

(** Auxiliary lemmas for [hclean]. Mostly repackaging of previous lemmas *)

let hclean_prop = prove
 (`!F' H P Q.
       is_local F' /\
       (P ==> F' H Q) ==>
       F' (H * cond P) Q`,
  CHEAT_TAC);;

let hclean_prop_single = prove
 (`!F' P Q.
      is_local F' /\
      (P ==> F' emp Q) ==>
      F' (cond P) Q`,
  CHEAT_TAC);;

let hclean_exists_single = prove
 (`!F' A J Q.
      is_local F' /\
      (!x. F' (J x) Q) ==>
      F' (SEP_EXISTS J) Q`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["cf"];;

(* and the interface *)
let _ = unhide_overloads ();;
