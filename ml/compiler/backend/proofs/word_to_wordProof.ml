(* ======================================================== *)
(*  word_to_wordProof: ported from HOL4's
    compiler/backend/proofs/word_to_wordProofScript.sml
    A proof theory about word_to_word.ml, with 2 definitions and 27
    theorems.  Needed by data_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_to_word
*)

needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_allocProof.ml";;
needs "compiler/backend/proofs/word_copyProof.ml";;
needs "compiler/backend/proofs/word_cseProof.ml";;
needs "compiler/backend/proofs/word_elimProof.ml";;
needs "compiler/backend/proofs/word_instProof.ml";;
needs "compiler/backend/proofs/word_removeProof.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;
needs "compiler/backend/proofs/word_unreachProof.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "lib/sptree.ml";;

(* HOL4 word_to_wordProofScript.sml:19-23: a proof *)

(*Chains up compile_single theorems*)

(* HOL4 word_to_wordProofScript.sml:165: ML code, not ported *)

(* The t k a c parameters don't need to be existentially quantified *)
let code_rel_def = cake_define
  `word_to_wordProof_code_rel stc ttc <=>
   (!n v. lookup n stc = SOME v ==>
          (?col t k a c.
          lookup n ttc = SOME (SND (word_to_word_compile_single t
            k a c ((n,v),col)))))`;;
hol4_overload "code_rel" "word_to_wordProof_code_rel";;

(* HOL4 word_to_wordProofScript.sml:294-296: a proof *)

(* HOL4 word_to_wordProofScript.sml:298-301: a proof *)

(* HOL4 word_to_wordProofScript.sml:303-306: a proof *)

(* HOL4 word_to_wordProofScript.sml:308-311: a proof *)

(* HOL4 word_to_wordProofScript.sml:313-316: a proof *)

(* HOL4 word_to_wordProofScript.sml:318-321: a proof *)

(* HOL4 word_to_wordProofScript.sml:323-326: a proof *)

(* HOL4 word_to_wordProofScript.sml:328-341: a proof *)

(* HOL4 word_to_wordProofScript.sml:343-346: code that the source has
   in a comment *)
(* HOL4 word_to_wordProofScript.sml:347-438: a proof *)
    (*Manual simulation for Result*)
(* HOL4 word_to_wordProofScript.sml:440-507: a proof *)
    (*Manual simulation for Exceptions*)
(* HOL4 word_to_wordProofScript.sml:509-589: a proof *)


(* HOL4 word_to_wordProofScript.sml:592-605: a proof *)
    (* NONE case (first w/o reverse) *)
(* HOL4 word_to_wordProofScript.sml:607-639: a proof *)
  (* SOME case *)
(* HOL4 word_to_wordProofScript.sml:641-642: a proof *)

(* HOL4 word_to_wordProofScript.sml:644-653: a proof *)

(* HOL4 word_to_wordProofScript.sml:655-659: a proof *)
    (* SOME case: cut_state succeeds *)
(* HOL4 word_to_wordProofScript.sml:661-745: a proof *)
  (* NONE case *)
(* HOL4 word_to_wordProofScript.sml:747-748: a proof *)

(* HOL4 word_to_wordProofScript.sml:750-765: a proof *)

(* HOL4 word_to_wordProofScript.sml:767-769: a proof *)

(* HOL4 word_to_wordProofScript.sml:771-773: a proof *)

(* HOL4 word_to_wordProofScript.sml:775-777: a proof *)

(* HOL4 word_to_wordProofScript.sml:779-782: a proof *)

(* HOL4 word_to_wordProofScript.sml:784-787: a proof *)

(* HOL4 word_to_wordProofScript.sml:789-791: a proof *)

(* HOL4 word_to_wordProofScript.sml:793-795: a proof *)

(* HOL4 word_to_wordProofScript.sml:797-799: a proof *)

(* HOL4 word_to_wordProofScript.sml:801-822: a proof *)

(* HOL4 word_to_wordProofScript.sml:824-826: a proof *)

(* HOL4 word_to_wordProofScript.sml:828-830: a proof *)

(* HOL4 word_to_wordProofScript.sml:832-834: a proof *)

(* HOL4 word_to_wordProofScript.sml:836-847: a proof *)

(* HOL4 word_to_wordProofScript.sml:849: a proof *)

(* HOL4 word_to_wordProofScript.sml:902: ML code, not ported *)

(* HOL4 word_to_wordProofScript.sml:904: ML code, not ported *)

(* HOL4 word_to_wordProofScript.sml:917: ML code, not ported *)

(* syntax going into stackLang *)

(**** more on syntactic form restrictions ****)


(***** compile_single correctness for no_alloc & no_install ******)

(* HOL4 word_to_wordProofScript.sml:1145-1147: a proof *)

(* HOL4 word_to_wordProofScript.sml:1149-1152: a proof *)

(* HOL4 word_to_wordProofScript.sml:1154-1157: a proof *)

(* HOL4 word_to_wordProofScript.sml:1159-1162: a proof *)

(* HOL4 word_to_wordProofScript.sml:1164-1167: a proof *)

(* HOL4 word_to_wordProofScript.sml:1169-1172: a proof *)

(* HOL4 word_to_wordProofScript.sml:1174-1177: a proof *)

(* HOL4 word_to_wordProofScript.sml:1179-1189: a proof *)

(* HOL4 word_to_wordProofScript.sml:1191-1193: a proof *)

(* HOL4 word_to_wordProofScript.sml:1195-1197: a proof *)

(* HOL4 word_to_wordProofScript.sml:1199-1203: a proof *)

(* HOL4 word_to_wordProofScript.sml:1205-1209: a proof *)

(* HOL4 word_to_wordProofScript.sml:1211-1215: a proof *)

(* HOL4 word_to_wordProofScript.sml:1217-1221: a proof *)

(* HOL4 word_to_wordProofScript.sml:1223-1227: a proof *)

(* HOL4 word_to_wordProofScript.sml:1229-1233: a proof *)

(* HOL4 word_to_wordProofScript.sml:1235-1239: a proof *)

(* HOL4 word_to_wordProofScript.sml:1241-1243: a proof *)

(* HOL4 word_to_wordProofScript.sml:1245-1249: a proof *)

(* HOL4 word_to_wordProofScript.sml:1251-1255: a proof *)

(* HOL4 word_to_wordProofScript.sml:1257-1261: a proof *)

(* HOL4 word_to_wordProofScript.sml:1263-1274: a proof *)

(* HOL4 word_to_wordProofScript.sml:1276-1286: a proof *)

(* HOL4 word_to_wordProofScript.sml:1288-1345: a proof *)

(* HOL4 word_to_wordProofScript.sml:1347-1441: a proof *)

(* HOL4 word_to_wordProofScript.sml:1443-1562: a proof *)
   (* Manual simulation for Result *)
(* HOL4 word_to_wordProofScript.sml:1564-1615: a proof *)
   (* Manual simulation for Exceptions *)
(* HOL4 word_to_wordProofScript.sml:1617-1690: a proof *)

(* HOL4 word_to_wordProofScript.sml:1692: a proof *)

(* HOL4 word_to_wordProofScript.sml:1694-2098: code that the source
   has in a comment *)

(******** more on no_mt **********)

(*** code_rel_ext ***)

let code_rel_ext_def = cake_define
  `code_rel_ext code l <=>
   (!n p_1 p_2.
      SOME (p_1,p_2) = lookup n code ==>
      (?t' k' a' c' col.
        SOME
        (SND (full_compile_single t' k' a' c' ((n,p_1,p_2),col))) =
        lookup n l))`;;

(* HOL4 word_to_wordProofScript.sml:2154: ML code, not ported *)

(**** more on no_share_inst ****)

(***** word_to_word semantics correctness for Pancake *****)
