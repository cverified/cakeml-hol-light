(* ======================================================== *)
(*  semanticPrimitivesProps: ported from HOL4's
    semantics/proofs/semanticPrimitivesPropsScript.sml  *)
(* ======================================================== *)

(*
  Various basic properties of the semantic primitives.
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let shift_lookup_def = cake_define
  `(shift_lookup Lsl = word_lsl) /\
   (shift_lookup Lsr = word_lsr) /\
   (shift_lookup Asr = word_asr) /\
   (shift_lookup Ror = word_ror)`;;

let do_shift_def = cake_define
  `do_shift sh n x3 x4 =
        match (x3,x4) with
          (W8,Word8 w) -> SOME (Word8 (shift_lookup sh w n))
        | (W64,(Word64 w)) -> SOME (Word64 (shift_lookup sh w n))
        | (_1,_2) -> NONE`;;

(*
Definition do_word_op_def[simp]:
  (do_word_op op W8 (Word8 w1) (Word8 w2) = SOME (Word8 (opw_lookup op
    w1 w2))) ∧
  (do_word_op op W64 (Word64 w1) (Word64 w2) = SOME (Word64 (opw_lookup
    op w1 w2))) ∧
  (do_word_op op _ _ _ = NONE)
End

Definition do_word_to_int_def[simp]:
  (do_word_to_int W8 (Word8 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int W64 (Word64 w) = SOME(int_of_num(w2n w))) ∧
  (do_word_to_int _ _ = NONE)
End

Definition do_word_from_int_def[simp]:
  (do_word_from_int W8 i = Word8 (i2w i)) ∧
  (do_word_from_int W64 i = Word64 (i2w i))
End
*)

(* HOL4 ML code, not ported:
val eqs = LIST_CONJ (map TypeBase.case_eq_of
  [``:op``, ``:'a list``, ``:'a option``, ``:v``, ``:'a store_v``,
    ``:lit``,
   ``:eq_result``, ``:word_size``])
*)

(* Alternate definition for build_rec_env *)

let map_error_result_def = cake_define
  `(map_error_result f (Rraise e) = Rraise (f e)) /\
   (map_error_result f (Rabort a) = Rabort a)`;;

let map_result_def = cake_define
  `(map_result f1 f2 (Rval v) = Rval (f1 v)) /\
   (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))`;;

let exc_rel_def = cake_define
  `exc_rel R x2 x3 =
        match (x2,x3) with
          (Rraise v1,Rraise v2) -> R v1 v2
        | ((Rabort a1),(Rabort a2)) -> a1 = a2
        | (_3,_4) -> F`;;

let result_rel_def = cake_define
  `result_rel R1 R2 x3 x4 =
        match (x3,x4) with
          (Rval v1,Rval v2) -> R1 v1 v2
        | ((Rerr e1),(Rerr e2)) -> exc_rel R2 e1 e2
        | (_5,_6) -> F`;;

let every_error_result_def = cake_define
  `(every_error_result P (Rraise e) = P e) /\
   (every_error_result P (Rabort a) = T)`;;

let every_result_def = cake_define
  `(every_result P1 P2 (Rval v) = (P1 v)) /\
   (every_result P1 P2 (Rerr e) = (every_error_result P2 e))`;;

let map_sv_def = cake_define
  `map_sv f (Refv v) = Refv (f v) /\
   map_sv _7 (W8array w) = (W8array w) /\
   map_sv f (Varray vs) = (Varray (MAP f vs)) /\
   map_sv f (Thunk m v) = (Thunk m (f v))`;;

let dest_Refv_def = cake_define
  `dest_Refv (Refv v) = v`;;
let is_Refv_def = cake_define
  `is_Refv x1 =
      match x1 with
        Refv _8 -> T
      | _9 -> F`;;

let sv_every_def = cake_define
  `sv_every P x2 =
      match x2 with
        Refv v -> P v
      | (Varray vs) -> EVERY P vs
      | (Thunk m v) -> P v
      | _10 -> T`;;

let sv_rel_def = cake_define
  `sv_rel R x2 x3 =
      match (x2,x3) with
        (Refv v1,Refv v2) -> R v1 v2
      | ((W8array w1),(W8array w2)) -> (w1 = w2)
      | ((Varray vs1),(Varray vs2)) -> LIST_REL R vs1 vs2
      | ((Thunk m1 v1),(Thunk m2 v2)) -> (m1 = m2 /\ R v1 v2)
      | (_11,_12) -> F`;;

let store_v_vs_def = cake_define
  `semanticPrimitivesProps_store_v_vs (Refv v) = [v] /\
   semanticPrimitivesProps_store_v_vs (Varray vs) = vs /\
   semanticPrimitivesProps_store_v_vs (W8array _13) = [] /\
   semanticPrimitivesProps_store_v_vs (Thunk _14 v) = [v]`;;
hol4_overload "store_v_vs" "semanticPrimitivesProps_store_v_vs";;

let store_vs_def = cake_define
  `store_vs s = FLAT (MAP store_v_vs s)`;;

let map_match_def = cake_define
  `map_match f x =
        match x with
          Match env -> Match (f env)
        | x -> x`;;

let ctors_of_tdef_def = cake_define
  `ctors_of_tdef (_15,_16,condefs) = MAP FST condefs`;;

let ctors_of_dec_def = cake_define
  `ctors_of_dec x1 =
      match x1 with
        Dtype locs tds -> FLAT (MAP ctors_of_tdef tds)
      | (Dexn locs s _17) -> [s]
      | _18 -> []`;;

(* free vars *)

let FV_def = cake_define
  `(FV (Raise e) = FV e) /\
   (FV (Handle e pes) = FV e UNION FV_pes pes) /\
   (FV (Lit _19) = {}) /\
   (FV (Con _20 ls) = FV_list ls) /\
   (FV (Var id') = {id'}) /\
   (FV (Fun x e) = FV e DIFF {Short x}) /\
   (FV (App _21 es) = FV_list es) /\
   (FV (Log _22 e1 e2) = FV e1 UNION FV e2) /\
   (FV (If e1 e2 e3) = FV e1 UNION FV e2 UNION FV e3) /\
   (FV (Mat e pes) = FV e UNION FV_pes pes) /\
   (FV (Let xo e b) = FV e UNION (FV b DIFF (match xo with NONE -> {}
     | SOME x -> {Short x}))) /\
   (FV (Letrec defs b) = (FV_defs defs UNION FV b) DIFF set_of_list
     (MAP (Short o FST) defs)) /\
   (FV (Tannot e t) = FV e) /\
   (FV (Lannot e l) = FV e) /\
   (FV_list [] = {}) /\
   (FV_list (e :: es) = FV e UNION FV_list es) /\
   (FV_pes [] = {}) /\
   (FV_pes ((p,e) :: pes) =
      (FV e DIFF (IMAGE Short (set_of_list (pat_bindings p)))) UNION
        FV_pes pes) /\
   (FV_defs [] = {}) /\
   (FV_defs ((_23,x,e) :: defs) =
      (FV e DIFF {Short x}) UNION FV_defs defs)`;;

(* HOL4 overload (expanded in the port):
     SFV = λe. {x | Short x ∈ FV e} *)

let FV_dec_def = cake_define
  `(FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) /\
   (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB))) /\
   (FV_dec (Dtype _24 _25) = {}) /\
   (FV_dec (Dtabbrev _26 _27 _28 _29) = {}) /\
   (FV_dec (Dexn _30 _31 _32) = {})`;;
