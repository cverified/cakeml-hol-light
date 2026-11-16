(* ======================================================== *)
(*  from_pancake32Prog: ported from HOL4's
    compiler/bootstrap/translation/from_pancake32ProgScript.sml
    A definition theory, with no definitions and 14 theorems.
    Needed by arm7Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the pan_to_target part of the 32-bit compiler.
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/bootstrap/translation/to_target32Prog.ml";;
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
let _ = cake_theory "from_pancake32Prog"
  ["backend"; "crepLang"; "crep_arith"; "crep_inline"; "crep_to_loop";
   "loopLang"; "loop_call"; "loop_live"; "loop_to_word"; "ml_translator";
   "panLang"; "panPtreeConversion"; "pan_globals"; "pan_simp"; "pan_structs";
   "pan_to_crep"; "pan_to_target"; "pan_to_word"; "std_prelude";
   "to_target32Prog"; "word_to_word"];;

(* HOL4 from_pancake32ProgScript.sml:14-16: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:18: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:20-21: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:23: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:25: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let from_pancake32Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* [local] *)
let option_map_thm = prove
 (`OPTION_MAP f x = match x with NONE -> NONE | SOME y -> SOME (f y)`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:39: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:41-45: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:47: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:49-60: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:62: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:64-66: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 from_pancake32ProgScript.sml:70-71: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:73: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:75: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:77: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:79: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:81: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:83: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:85: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:87: the ML values that the definitions
   below antiquote *)

(* HOL4 from_pancake32ProgScript.sml:89: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:91: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:93: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:95: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:97: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:99: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:101: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:103: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:105: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:107: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:109: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:111: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:113: ML code, not ported *)

(* lem[local] *)
let from_pancake32Prog_lem = prove
 (`dimindex (:32) = 32`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:121: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:123: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:125: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:127: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:129: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:131: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:133: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:135: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:137: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:139: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:141: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:143: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:145: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:147: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:149: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:151: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:153: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:155: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:157: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:159: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:161: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:163: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:165: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:167: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:169: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:171: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:173: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:175: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:177: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:179: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:181: ML code, not ported *)

(* [local] *)
let pan_globals_compile_decs_ind = prove
 (`pan_globals_compile_decs_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:196: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:198: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:200: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:202: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:204: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:206: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:208: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:210: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:212: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:214: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:216: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:218: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:220: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:222: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:224: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:226: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:228: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:230: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:232: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:234: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:236: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:238: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:240: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:242: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:244: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:246: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:248: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:250: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:252: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:254: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:256: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:258: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:260: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:262: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:264: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:266: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:268: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:270: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:272: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:274: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:276: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:278: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:280: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:282: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:284: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:286: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:288: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:290: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:292-294: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:296: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:298-310: a theorem that HOL4 states as
   the value of an ML expression: ind_lemma *)

(* HOL4 from_pancake32ProgScript.sml:312: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:314: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:316: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:318-319: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:321: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:323: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:325: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:327: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:329: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:331: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:333: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:335: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:337: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:339: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:341: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:343: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:345: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:347: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:349: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:351: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:353: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:355: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:357: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:359: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:361: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:363: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:365: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:367: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:369: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:371: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:373: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:375: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:377: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:379: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:381: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:383-386: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:388-389: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:391-394: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:396: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:398: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:400: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:402: ML code, not ported *)

(* ptree conversion *)

(* HOL4 from_pancake32ProgScript.sml:406: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:408: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:410: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:412: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:414: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:416: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:418: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:420: ML code, not ported *)

let conv_const_thm = prove
 (`conv_const t =
   match conv_int t with NONE -> (NONE:('a pan_exp) option)
          | SOME x -> SOME (asm_Const (i2w x))`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:430: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:432: ML code, not ported *)

(* [local] *)
let conv_nat_side = prove
 (`!x. panptreeconversion_conv_nat_side x`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:441: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:443: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:445: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:447: the overload ptree_size, which the
   port expands *)

(* HOL4 from_pancake32ProgScript.sml:449: ML code, not ported *)

(* [local] *)
let OPT_MMAP_eq_MAP = prove
 (`OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:457: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:459-462: ML code, not ported *)

(* [local] *)
let panptreeconversion_conv_shape_side = prove
 (`!sh. panptreeconversion_conv_shape_side sh`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:474: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:476: ML code, not ported *)

let OPTION_MAP2_thm = prove
 (`OPTION_MAP2 f x y =
   match x with
     NONE -> NONE
   | SOME x ->
       (match y with
          NONE -> NONE
        | SOME y -> SOME (f x y))`,
  CHEAT_TAC);;

(* [local] *)
let FOLDR_eta = prove
 (`FOLDR (\t. f t) = FOLDR (\t e. f t e)`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:496: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:498: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:500: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:502: ML code, not ported *)


(* HOL4 from_pancake32ProgScript.sml:505-509: ML code, not ported *)

(* if the above is attempted without the "spec32" line, the translator seems to
   break, and *loses* the ability to translate the expression datatype:

   time hol2deep ``(Panop i [(BaseAddr :32 panLang$exp); i'])``
*)

(* [local] *)
let panptreeconversion_conv_arglist_ind = prove
 (`panptreeconversion_conv_arglist_ind (:'b)`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:534: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:536: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:538: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:540: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:542: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:544: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:546: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:548: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:550: ML code, not ported *)

let conv_Prog_ind = prove
 (`panptreeconversion_conv_prog_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:565: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:567: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:569: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:571: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:573: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:575: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:577: ML code, not ported *)

(* [local] *)
let panptreeconversion_conv_topdeclist_ind = prove
 (`panptreeconversion_conv_topdeclist_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:592: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:594: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:596: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:598: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:600: ML code, not ported *)

(* [local] *)
let panptreeconversion_localise_prog_ind = prove
 (`panptreeconversion_localise_prog_ind`,
  CHEAT_TAC);;

(* HOL4 from_pancake32ProgScript.sml:615: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:617: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:619: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:621: ML code, not ported *)

(* HOL4 from_pancake32ProgScript.sml:623: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
