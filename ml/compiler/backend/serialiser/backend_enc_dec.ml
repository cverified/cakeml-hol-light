(* ======================================================== *)
(*  backend_enc_dec: ported from HOL4's
    compiler/backend/serialiser/backend_enc_decScript.sml
    A definition theory, with 14 definitions and 11 theorems.
    Needed by backend_asm.ml, decodeProg.ml and replProof.ml.  *)
(* ======================================================== *)

(*
  Encoders and decoders to/from configuration types in backend.
*)

needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/serialiser/num_list_enc_dec.ml";;
needs "compiler/backend/serialiser/num_tree_enc_dec.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_enc_dec"
  ["ast"; "backend"; "backend_common"; "evaluateProps"; "fpSem"; "misc";
   "ml_prog"; "ml_translator"; "mlstring"; "mlvector"; "num_list_enc_dec";
   "num_tree_enc_dec"; "semanticPrimitives"; "semanticPrimitivesProps"];;
(* HOL4 ancestors outside the port: integer *)

(* HOL4 backend_enc_decScript.sml:12: ML code, not ported *)

(* automation *)

(* Creates fully-qualified types, with some (basic) exceptions. *)
(* Shadows Hol_pp.type_to_string, whose string output depends on the grammar *)
(* HOL4 backend_enc_decScript.sml:18-23: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:25-31: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:33-34: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:36-52: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:54-69: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:71-109: the ML values that the definitions
   below antiquote *)

(* HOL4 backend_enc_decScript.sml:111-123: a proof *)

(* backend_common_tra *)

(* HOL4 backend_enc_decScript.sml:127: ML code, not ported *)

cake_declare "backend_common_tra_enc'" `:tra->num_tree`;;

(* HOL4 backend_enc_decScript.sml:129-131: the definition *)

cake_declare "backend_common_tra_dec'" `:num_tree->tra`;;

(* HOL4 backend_enc_decScript.sml:133-147: the definition *)

let backend_common_tra_enc'_thm = prove
 (`backend_common_tra_dec' (backend_common_tra_enc' x) = x`,
  CHEAT_TAC);;
add_simp backend_common_tra_enc'_thm;;

(* HOL4 backend_enc_decScript.sml:156: ML code, not ported *)

(* some simple ones *)

(* HOL4 backend_enc_decScript.sml:160-167: ML code, not ported *)

(* closLang_const *)

(* HOL4 backend_enc_decScript.sml:171: ML code, not ported *)

cake_declare "closLang_const_enc'" `:const->num_tree`;;

(* HOL4 backend_enc_decScript.sml:173-177: the definition *)

cake_declare "closLang_const_dec'" `:num_tree->const`;;

(* HOL4 backend_enc_decScript.sml:179-191: the definition *)

let closLang_const_enc'_thm = prove
 (`closLang_const_dec' (closLang_const_enc' x) = x`,
  CHEAT_TAC);;
add_simp closLang_const_enc'_thm;;

(* HOL4 backend_enc_decScript.sml:204: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:206-222: ML code, not ported *)

(* closLang's exp *)

(* HOL4 backend_enc_decScript.sml:226: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:228-235: a theorem whose statement the
   port cannot state yet: MEM_exp_size *)

cake_declare "closLang_exp_enc'" `:clos_exp->num_tree`;;

(* HOL4 backend_enc_decScript.sml:237-242: the definition *)

cake_declare "closLang_exp_dec'" `:num_tree->clos_exp`;;

(* HOL4 backend_enc_decScript.sml:244-258: the definition *)

(* HOL4 backend_enc_decScript.sml:260-265: a theorem whose statement the
   port cannot state yet: bvl_MEM_exp_size *)

let closLang_exp_enc'_thm = prove
 (`!x. closLang_exp_dec' (closLang_exp_enc' x) = x`,
  CHEAT_TAC);;
add_simp closLang_exp_enc'_thm;;

(* HOL4 backend_enc_decScript.sml:279: ML code, not ported *)

(* BVL's exp *)

(* HOL4 backend_enc_decScript.sml:283: ML code, not ported *)

cake_declare "bvl_exp_enc'" `:bvl_exp->num_tree`;;

(* HOL4 backend_enc_decScript.sml:285-290: the definition *)

cake_declare "bvl_exp_dec'" `:num_tree->bvl_exp`;;

(* HOL4 backend_enc_decScript.sml:292-304: the definition *)

let bvl_exp_enc'_thm = prove
 (`!x. bvl_exp_dec' (bvl_exp_enc' x) = x`,
  CHEAT_TAC);;
add_simp bvl_exp_enc'_thm;;

(* HOL4 backend_enc_decScript.sml:316: ML code, not ported *)

(* BVI's exp *)

(* HOL4 backend_enc_decScript.sml:320-325: a theorem whose statement the
   port cannot state yet: bvi_MEM_exp_size *)

(* HOL4 backend_enc_decScript.sml:327: ML code, not ported *)

cake_declare "bvi_exp_enc'" `:bvi_exp->num_tree`;;

(* HOL4 backend_enc_decScript.sml:329-334: the definition *)

cake_declare "bvi_exp_dec'" `:num_tree->bvi_exp`;;

(* HOL4 backend_enc_decScript.sml:336-352: the definition *)

let bvi_exp_enc'_thm = prove
 (`!x. bvi_exp_dec' (bvi_exp_enc' x) = x`,
  CHEAT_TAC);;
add_simp bvi_exp_enc'_thm;;

(* HOL4 backend_enc_decScript.sml:367: ML code, not ported *)

(* val_approx *)

(* HOL4 backend_enc_decScript.sml:371: ML code, not ported *)

cake_declare "clos_known_val_approx_enc'" `:val_approx->num_tree`;;

(* HOL4 backend_enc_decScript.sml:373-375: the definition *)

cake_declare "clos_known_val_approx_dec'" `:num_tree->val_approx`;;

(* HOL4 backend_enc_decScript.sml:377-390: the definition *)

let clos_known_val_approx_enc'_thm = prove
 (`!x. clos_known_val_approx_dec' (clos_known_val_approx_enc' x) = x`,
  CHEAT_TAC);;
add_simp clos_known_val_approx_enc'_thm;;

(* HOL4 backend_enc_decScript.sml:402: ML code, not ported *)

(* automation for producing enc/dec for record types *)

(* HOL4 backend_enc_decScript.sml:406-415: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:417-421: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:423-426: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:428: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:430: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:432-443: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:445: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:447-458: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:460-462: ML code, not ported *)
(*
  val (name,ty) = first (not o can get_enc_dec_ok'_thm) xs
*)
(* HOL4 backend_enc_decScript.sml:466-499: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:501-515: ML code, not ported *)

(* HOL4 backend_enc_decScript.sml:517-520: a theorem that HOL4 states as the
   value of an ML expression: config_dec_thm *)

(* top level *)

let encode_backend_config_def = new_definition
  `encode_backend_config c =
     (rev_nums_to_chars (append_rev (backend_config_enc c) []) "":char
       list)`;;

let decode_backend_config_def = new_definition
  `decode_backend_config s = FST (backend_config_dec (chars_to_nums s))`;;

let encode_backend_config_thm = prove
 (`decode_backend_config (encode_backend_config c) = c`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
