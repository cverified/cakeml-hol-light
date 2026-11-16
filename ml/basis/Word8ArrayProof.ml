(* ======================================================== *)
(*  Word8ArrayProof: ported from HOL4's
    basis/Word8ArrayProofScript.sml
    A proof theory, with 1 definition and 13 theorems.  Needed by
    CommandLineProof.ml, MarshallingProg.ml and TextIOProof.ml.  *)
(* ======================================================== *)

(*
  Proof about the code in the byte-array module Word8Array.
*)

needs "basis/Word8ArrayProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "lib/set_sep.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "Word8ArrayProof"
  ["Word8ArrayProg"; "cf"; "ml_prog"; "ml_translator"];;

let _ = do_list hide_constant ["fv"];;

(* HOL4 Word8ArrayProofScript.sml:10: ML code, not ported *)

(* HOL4 Word8ArrayProofScript.sml:12: ML code, not ported *)

(* HOL4 Word8ArrayProofScript.sml:14-29: a proof *)

(* HOL4 Word8ArrayProofScript.sml:31-38: a theorem whose statement the port
   cannot state yet: w8array_alloc_spec *)

(* HOL4 Word8ArrayProofScript.sml:40-47: a theorem whose statement the port
   cannot state yet: w8array_sub_spec *)

(* HOL4 Word8ArrayProofScript.sml:49-55: a theorem whose statement the port
   cannot state yet: w8array_length_spec *)

(* HOL4 Word8ArrayProofScript.sml:57-66: a theorem whose statement the port
   cannot state yet: w8array_update_spec *)

(* HOL4 Word8ArrayProofScript.sml:68-82: a theorem whose statement the port
   cannot state yet: w8array_copy_spec *)

(* HOL4 Word8ArrayProofScript.sml:84-98: a theorem whose statement the port
   cannot state yet: w8array_copyVec_spec *)

(* HOL4 Word8ArrayProofScript.sml:100-111: a theorem whose statement the
   port cannot state yet: w8array_substring_spec *)

let Word8ArrayProof_findi_def,Word8ArrayProof_findi_ind = define_guess
  `(Word8ArrayProof_findi f [] = NONE) /\
   (Word8ArrayProof_findi f (CONS x xs) =
      if (f x) then SOME ((0:num),x) else match Word8ArrayProof_findi f xs
          with NONE -> NONE
        | SOME (n,x) -> SOME (n + 1,x))`;;

let findi_spec_SOME = prove
 (`!f arr i.
   Word8ArrayProof_findi f arr = SOME (i,x) ==>
     EL i arr = x /\
     f (EL i arr) /\ (!m. m < i ==> ~(f (EL m arr))) /\ i < LENGTH (arr)`,
  CHEAT_TAC);;

let findi_spec_SOME_rev = prove
 (`!i arr f.
     EL i arr = x /\
     i < LENGTH (arr) /\ f (EL i arr) /\ (!m. m < i ==> ~(f (EL m arr))) ==>
     Word8ArrayProof_findi f arr = SOME (i,x)`,
  CHEAT_TAC);;

let findi_spec_NONE = prove
 (`!f arr i.
   Word8ArrayProof_findi f arr = NONE ==>
     (!i. i < LENGTH arr ==> ~(f (EL i arr)))`,
  CHEAT_TAC);;

let findi_spec_NONE_rev = prove
 (`!f arr i.
     (!i. i < LENGTH arr ==> ~(f (EL i arr))) ==>
     Word8ArrayProof_findi f arr = NONE`,
  CHEAT_TAC);;

let w8array_find_aux_spec = prove
 (`!arr arrv f fv' av n nv old p.
     Word8ArrayProof_findi f old = NONE /\
     (Arrow (WORD:word8->semanticPrimitives_v->bool) BOOL) f fv' /\ NUM
       (LENGTH arr + LENGTH old) av /\ NUM (LENGTH old) nv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       Word8Array_findi_aux_v
       [fv'; arrv; av; nv]
       (W8ARRAY arrv (APPEND old arr))
       (POSTv (\v. W8ARRAY arrv (APPEND old arr) *
           cond (OPTION_TYPE (PAIR_TYPE NUM
             (WORD:word8->semanticPrimitives_v->bool)) (Word8ArrayProof_findi
             f (APPEND old arr)) v)))`,
  CHEAT_TAC);;

let w8array_find_spec = prove
 (`!f fv' arr arrv.
     (Arrow (WORD:word8->semanticPrimitives_v->bool) BOOL) f fv' ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       Word8Array_findi_v [fv'; arrv]
       (W8ARRAY arrv arr)
       (POSTv (\v. W8ARRAY arrv arr *
           cond (OPTION_TYPE (PAIR_TYPE NUM
             (WORD:word8->semanticPrimitives_v->bool)) (Word8ArrayProof_findi
             f arr) v)))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
