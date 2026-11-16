(* ======================================================== *)
(*  from_pancake64Prog: ported from HOL4's
    compiler/bootstrap/translation/from_pancake64ProgScript.sml
    A definition theory, with no definitions and 14 theorems.
    Needed by x64Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the pan_to_target part of the 64-bit compiler.
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/bootstrap/translation/to_target64Prog.ml";;
needs "lib/integer_word.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/crep_arith.ml";;
needs "pancake/crep_inline.ml";;
needs "pancake/crep_to_loop.ml";;
needs "pancake/loopLang.ml";;
needs "pancake/loop_call.ml";;
needs "pancake/loop_live.ml";;
needs "pancake/loop_to_word.ml";;
needs "pancake/panLang.ml";;
needs "pancake/pan_globals.ml";;
needs "pancake/pan_simp.ml";;
needs "pancake/pan_structs.ml";;
needs "pancake/pan_to_crep.ml";;
needs "pancake/pan_to_target.ml";;
needs "pancake/pan_to_word.ml";;
needs "pancake/parser/panPtreeConversion.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "from_pancake64Prog"
  ["backend"; "crepLang"; "crep_arith"; "crep_inline"; "crep_to_loop";
   "loopLang"; "loop_call"; "loop_live"; "loop_to_word"; "ml_translator";
   "panLang"; "panPtreeConversion"; "pan_globals"; "pan_simp"; "pan_structs";
   "pan_to_crep"; "pan_to_target"; "pan_to_word"; "std_prelude";
   "to_target64Prog"; "word_to_word"];;

(* HOL4 from_pancake64ProgScript.sml:14-16: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:18: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:20-21: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:23: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:25: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let from_pancake64Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* option_map_thm[local] *)
let from_pancake64Prog_option_map_thm = prove
 (`OPTION_MAP f x = match x with NONE -> NONE | SOME y -> SOME (f y)`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:39: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:41-45: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:47: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:49-60: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:62-64: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:66-68: ML code, not ported *)
              (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 from_pancake64ProgScript.sml:72-73: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:75: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:77: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:79: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:81: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:83: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:85: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:87: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:89-91: the ML values that the
   definitions below antiquote *)

(* HOL4 from_pancake64ProgScript.sml:93: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:95: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:97: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:99: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:101: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:103: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:105: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:107: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:109: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:111: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:113: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:115: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:117: ML code, not ported *)

(* lem[local] *)
let from_pancake64Prog_lem = prove
 (`dimindex (:64) = 64`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:125: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:127: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:129: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:131: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:133: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:135: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:137: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:139: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:141: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:143: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:145: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:147: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:149: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:151: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:153: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:155: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:157: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:159: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:161: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:163: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:165: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:167: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:169: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:171: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:173: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:175: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:177: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:179: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:181: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:183: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:185: ML code, not ported *)

(* pan_globals_compile_decs_ind[local] *)
let from_pancake64Prog_pan_globals_compile_decs_ind = prove
 (`pan_globals_compile_decs_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:200: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:202: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:204: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:206: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:208: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:210: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:212: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:214: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:216: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:218: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:220: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:222: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:224: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:226: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:228: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:230: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:232: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:234: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:236: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:238: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:240: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:242: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:244: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:246: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:248: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:250: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:252: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:254: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:256: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:258: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:260: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:262: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:264: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:266: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:268: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:270: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:272: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:274: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:276: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:278: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:280: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:282: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:284: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:286: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:288: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:290: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:292: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:294: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:296-299: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:301: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:303-314: a theorem that HOL4 states as
   the value of an ML expression: ind_lemma *)

(* HOL4 from_pancake64ProgScript.sml:316: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:318: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:320: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:322-323: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:325: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:327: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:329: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:331: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:333: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:335: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:337: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:339: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:341: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:343: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:345: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:347: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:349: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:351: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:353: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:355: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:357: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:359: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:361: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:363: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:365: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:367: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:369: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:371: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:373: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:375: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:377: ML code, not ported *)

(* TODO: duplicate *)
(* HOL4 from_pancake64ProgScript.sml:380: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:382: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:384: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:386: ML code, not ported *)

(* TODO: duplicated from compiler64ProgScript. *)
(* HOL4 from_pancake64ProgScript.sml:389-392: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:394-395: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:397-400: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:402: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:404: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:406: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:408: ML code, not ported *)

(* ptree conversion *)

(* HOL4 from_pancake64ProgScript.sml:412: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:414: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:416: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:418: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:420: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:422: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:424: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:426: ML code, not ported *)

(* conv_const_thm *)
let from_pancake64Prog_conv_const_thm = prove
 (`conv_const t =
   match conv_int t with NONE -> (NONE:('a pan_exp) option)
                   | SOME x -> SOME (pan_Const (i2w x))`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:436: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:438: ML code, not ported *)

(* conv_nat_side[local] *)
let from_pancake64Prog_conv_nat_side = prove
 (`!x. panptreeconversion_conv_nat_side x`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:447: ML code, not ported *)


(* HOL4 from_pancake64ProgScript.sml:450: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:452: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:454: the overload ptree_size, which the
   port expands *)

(* HOL4 from_pancake64ProgScript.sml:456: ML code, not ported *)

(* OPT_MMAP_eq_MAP[local] *)
let from_pancake64Prog_OPT_MMAP_eq_MAP = prove
 (`OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:464: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:466-469: ML code, not ported *)

(* panptreeconversion_conv_shape_side[local] *)
let from_pancake64Prog_panptreeconversion_conv_shape_side = prove
 (`!sh. panptreeconversion_conv_shape_side sh`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:481: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:483: ML code, not ported *)

(* OPTION_MAP2_thm[local] *)
let from_pancake64Prog_OPTION_MAP2_thm = prove
 (`OPTION_MAP2 f x y =
   match x with
     NONE -> NONE
   | SOME x ->
       (match y with
          NONE -> NONE
        | SOME y -> SOME (f x y))`,
  CHEAT_TAC);;

(* FOLDR_eta[local] *)
let from_pancake64Prog_FOLDR_eta = prove
 (`FOLDR (\t. f t) = FOLDR (\t e. f t e)`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:503: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:505: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:507: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:509: ML code, not ported *)


(* HOL4 from_pancake64ProgScript.sml:512-516: ML code, not ported *)

(* panptreeconversion_conv_arglist_ind[local] *)
let from_pancake64Prog_panptreeconversion_conv_arglist_ind = prove
 (`panptreeconversion_conv_arglist_ind (:'b)`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:535: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:537: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:539: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:541: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:543: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:545: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:547: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:549: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:551: ML code, not ported *)

(* conv_Prog_ind *)
let from_pancake64Prog_conv_Prog_ind = prove
 (`panptreeconversion_conv_prog_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:566: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:568: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:570: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:572: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:574: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:576: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:578: ML code, not ported *)

(* panptreeconversion_conv_topdeclist_ind[local] *)
let from_pancake64Prog_panptreeconversion_conv_topdeclist_ind = prove
 (`panptreeconversion_conv_topdeclist_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:593: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:595: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:597: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:599: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:601: ML code, not ported *)

(* panptreeconversion_localise_prog_ind[local] *)
let from_pancake64Prog_panptreeconversion_localise_prog_ind = prove
 (`panptreeconversion_localise_prog_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake64ProgScript.sml:616: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:618: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:620: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:622: ML code, not ported *)

(* HOL4 from_pancake64ProgScript.sml:624: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
