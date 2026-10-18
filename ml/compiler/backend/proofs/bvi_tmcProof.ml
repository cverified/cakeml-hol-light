(* ======================================================== *)
(*  bvi_tmcProof: ported from HOL4's
    compiler/backend/proofs/bvi_tmcProofScript.sml
    A proof theory about bvi_tmc.ml, with 25 definitions and 169
    theorems.  Needed by bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_tailrec
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tmc.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 bvi_tmcProofScript.sml:10: the ML values that the definitions
   below antiquote *)

(* HOL4 bvi_tmcProofScript.sml:12: the overload in_ns_3, which the
   port expands *)

let v_rel = cake_inductive
  `(!f i. bvi_tmcProof_v_rel f (bvlSem_Number i) (bvlSem_Number i)) /\
   (!f w. bvi_tmcProof_v_rel f (bvlSem_Word64 w) (bvlSem_Word64 w))
     /\
   (!f n xs ys.
       LIST_REL (bvi_tmcProof_v_rel f) xs ys ==>
       bvi_tmcProof_v_rel f (bvlSem_Block n xs) (bvlSem_Block n ys))
         /\
   (!f n. bvi_tmcProof_v_rel f (bvlSem_CodePtr n) (bvlSem_CodePtr n))
     /\
   (!f n m b.
       FLOOKUP f n = SOME m ==>
       bvi_tmcProof_v_rel f (bvlSem_RefPtr b n) (bvlSem_RefPtr b
         m))`;;
hol4_overload "v_rel" "bvi_tmcProof_v_rel";;

let ref_rel = cake_inductive
  `(bvi_tmcProof_ref_rel f (bvlSem_ByteArray b bs) (bvlSem_ByteArray b
  bs)) /\
   (LIST_REL (bvi_tmcProof_v_rel f) xs ys ==>
     bvi_tmcProof_ref_rel f (bvlSem_ValueArray xs) (bvlSem_ValueArray
       ys)) /\
   (bvi_tmcProof_v_rel f x y ==>
     bvi_tmcProof_ref_rel f (bvlSem_Thunk tm x) (bvlSem_Thunk tm
       y))`;;
hol4_overload "ref_rel" "bvi_tmcProof_ref_rel";;

let env_rel_def = cake_define
  `bvi_tmcProof_env_rel opt f env1 env2 <=>
   (?xs ys.
     env2 = xs ++ ys /\
     LIST_REL (bvi_tmcProof_v_rel f) env1 xs /\
     (opt ==>
       LENGTH ys = 2 /\
       (?hole_ptr hole_idx.
         EL 0 ys = RefPtr F hole_ptr /\
         EL 1 ys = Number hole_idx /\
         small_enough_int hole_idx)))`;;
hol4_overload "env_rel" "bvi_tmcProof_env_rel";;

let no_mutcons_op_def = cake_define
  `no_mutcons_op op <=> (!tag i. ~(op = closLang_MemOp
  (closLang_MutCons tag i)))`;;

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let no_mutcons_def = cake_define_list_try (fun () ->
  `MEASURE flatLang_exp_size`)
  [`no_mutcons (Var n:bvi_exp) <=> T`;
   `no_mutcons (If x1 x2 x3:bvi_exp) <=> no_mutcons x1 /\ no_mutcons
  x2 /\ no_mutcons x3`;
   `no_mutcons (Let xs x:bvi_exp) <=> EVERY no_mutcons xs /\
  no_mutcons x`;
   `no_mutcons (Raise x:bvi_exp) <=> no_mutcons x`;
   `no_mutcons (Tick x:bvi_exp) <=> no_mutcons x`;
   `no_mutcons (Call ticks dest xs handler:bvi_exp) <=>
         EVERY no_mutcons xs /\ (match handler with NONE -> T |
           SOME x -> no_mutcons x)`;
   `no_mutcons (Force loc n:bvi_exp) <=> T`;
   `no_mutcons (bvi_LetCall rets ticks dest xs y) <=> EVERY
  no_mutcons xs /\ no_mutcons y`;
   `no_mutcons (bvi_Return xs:bvi_exp) <=> EVERY no_mutcons xs`;
   `no_mutcons (Op op xs:bvi_exp) <=> no_mutcons_op op /\ EVERY
  no_mutcons xs`];;

let code_rel_def = cake_define
  `bvi_tmcProof_code_rel c1 c2 <=>
     (!loc arity exp.
       sptree_lookup loc c1 = SOME (arity,exp) ==>
       no_mutcons exp /\
       (?n.
         (compile_exp loc n arity exp = NONE ==>
          sptree_lookup loc c2 = SOME (arity,exp)) /\
         (!wrap work.
           compile_exp loc n arity exp = SOME (wrap,work) ==>
           sptree_lookup loc c2 = SOME (arity,wrap) /\
           sptree_lookup n c2 = SOME (arity + 2,work))))`;;
hol4_overload "code_rel" "bvi_tmcProof_code_rel";;

let free_names_def = cake_define
  `bvi_tmcProof_free_names n (name:num) <=> (!k. ~(n +
  bvl_to_bvi_namespaces * k = name))`;;
hol4_overload "free_names" "bvi_tmcProof_free_names";;

let namespace_rel_def = cake_define
  `bvi_tmcProof_namespace_rel (c1:'a spt) (c2:'a spt) <=>
     (!n. n IN domain c2 /\ bvl_num_stubs <= n ==> (if (\n. n MOD
       bvl_to_bvi_namespaces = 3) n then ~(n IN domain c1) else n IN
       domain c1)) /\
     (!n. n IN domain c1 /\ bvl_num_stubs <= n ==> ~((\n. n MOD
       bvl_to_bvi_namespaces = 3) n)) /\
     (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;
hol4_overload "namespace_rel" "bvi_tmcProof_namespace_rel";;

(* This should say: expression in prog satisfies no-mutblock property *)
let input_condition_def = cake_define
  `bvi_tmcProof_input_condition next' prog <=>
     EVERY (bvi_tmcProof_free_names next' o FST) prog /\
     EVERY (no_mutcons o SND o SND) prog /\
     ALL_DISTINCT (MAP FST prog) /\
     EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 3) o FST)
       (FILTER ((<=) bvl_num_stubs o FST) prog) /\
     bvl_num_stubs <= next' /\ (\n. n MOD bvl_to_bvi_namespaces =
       3) next'`;;
hol4_overload "input_condition" "bvi_tmcProof_input_condition";;

let state_ref_rel_def = cake_define
  `state_ref_rel f (s_refs:(num,bvlSem_v bvlSem_ref)fmap)
  (t_refs:(num,bvlSem_v bvlSem_ref)fmap) <=>
     FDOM f = FDOM s_refs /\
     (!i v.
       FLOOKUP s_refs i = SOME v ==>
        (?j w. FLOOKUP f i = SOME j /\
              bvi_tmcProof_ref_rel f v w /\
              FLOOKUP t_refs j = SOME w))`;;

let fmap_inj_def = cake_define
  `fmap_inj (f:(num,num)fmap) <=>
     (!p1 p2 q. FLOOKUP f p1 = SOME q /\ FLOOKUP f p2 = SOME q ==>
       p1 = p2)`;;

let state_rel_def = cake_define
  `bvi_tmcProof_state_rel f s (t:('a,'ffi)bviSem_state) <=>
     state_ref_rel f (state_refs s) (state_refs t) /\ state_clock
     t = state_clock s /\
     OPTREL (\p p'. FLOOKUP f p = SOME p') (bviSem_state_global s)
       (bviSem_state_global t) /\ state_ffi
     t = state_ffi s /\ compile_oracle
     t = state_co bvi_tmc_compile_each (compile_oracle s) /\ compile
     s = state_cc bvi_tmc_compile_each (compile t) /\
     bvi_tmcProof_code_rel (state_code s) (state_code t) /\
     bvi_tmcProof_namespace_rel (state_code s) (state_code t) /\
     (!n. let ((next',cfg),prog) = compile_oracle s n in
             bvi_tmcProof_input_condition next' prog) /\
     (!n. n IN domain (state_code t) /\ (\n. n MOD
       bvl_to_bvi_namespaces = 3) n ==> n < FST (FST (compile_oracle s
       0))) /\
     fmap_inj f`;;
hol4_overload "state_rel" "bvi_tmcProof_state_rel";;

(* Structural facts about compile_each and the namespace allocation.
   These follow bvi_tailrecProof; they only depend on the recursion shape of
   compile_each (NONE keeps an entry, SOME emits wrapper + worker). *)

let eor_rel_def = cake_define
  `eor_rel f x2 x3 =
        match (x2,x3) with
          (Exn v1,Exn v2) -> bvi_tmcProof_v_rel f v1 v2
        | ((Ret vs1),(Ret vs2)) -> LIST_REL (bvi_tmcProof_v_rel f)
          vs1 vs2
        | (_1,_2) -> F`;;

let opt_res_rel_def = cake_define
  `opt_res_rel f (r1:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result) (r2:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result) =
   (match (r1,r2) with (Rval v1,Rval [Block 0 []]) -> T | (Rerr
     e1,Rerr e2) -> exc_rel (eor_rel f) e1 e2 | _3 -> F)`;;

(* not a strict equality anymore! *)

let hole_has_val_def = cake_define
  `hole_has_val (f:(num,num)fmap) (env1:bvlSem_v list) (env2:bvlSem_v
  list) (refs:(num,bvlSem_v bvlSem_ref)fmap) c <=>
   LENGTH env2 = LENGTH env1 + 2 /\
   (?hole_ptr tag finalised left right. EL (LENGTH env1)
     env2 = RefPtr F hole_ptr /\ EL (LENGTH env1 + 1)
     env2 = Number (&(LENGTH left)) /\
     small_enough_int (&(LENGTH left)) /\ ~(
     hole_ptr IN FRANGE f) /\
     FLOOKUP refs hole_ptr = SOME (bvlSem_MutBlock tag finalised
       left c right))`;;

let holes_unchanged_except_def = cake_define
  `holes_unchanged_except f refs refs' changed <=>
     (!ptr tag finalised left child right. ~(
        ptr IN FRANGE f) /\
        FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag finalised left
          child right) ==>
        (?finalised' child'.
          FLOOKUP refs' ptr = SOME (bvlSem_MutBlock tag finalised'
            left child' right) /\
          (~(ptr IN changed) ==> child = child')))`;;

let hole_not_finalised_def = cake_define
  `hole_not_finalised refs ptr <=>
     (?tag left child right.
       FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag F left child
         right))`;;

let holes_still_not_finalised_def = cake_define
  `holes_still_not_finalised f (refs:('b,'c bvlSem_ref)fmap)
  (refs':('b,'c bvlSem_ref)fmap) <=>
     (!ptr. ~(
       ptr IN FRANGE f) /\
       hole_not_finalised refs ptr ==>
       hole_not_finalised refs' ptr)`;;

let only_fresh_def = cake_define
  `only_fresh (f:(num,num)fmap) (f':(num,num)fmap)
  (refs_old:(num,bvlSem_v bvlSem_ref)fmap) =
   (!n. n IN FRANGE f' /\ ~(n IN FRANGE f) ==> ~(n IN FDOM
     refs_old))`;;

(* HOL4 bvi_tmcProofScript.sml:1095-1103: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let mb_rel_def = cake_define_try_tac (fun () ->
  `MEASURE (CARD o FDOM o FST o SND o SND)`)
  CHEAT_TAC
  `mb_rel f x2 refs v1 v2 =
        match (x2,v1,v2) with
          ((refs_old:(num,bvlSem_v bvlSem_ref)fmap),(Block tag
            xs:bvlSem_v),(RefPtr b ptr:bvlSem_v)) ->
      (if b \/ ptr IN FRANGE f \/ ptr IN FDOM refs_old then F else
        match FLOOKUP refs ptr with SOME (bvlSem_MutBlock tag' fin'
          left' child' right') ->
            (tag = tag' /\
             fin' = F /\
             (?left child right.
               xs = left ++ [child] ++ right /\
               LIST_REL (bvi_tmcProof_v_rel f) left left' /\
               mb_rel f refs_old (refs \\ ptr) child child' /\
               LIST_REL (bvi_tmcProof_v_rel f) right right')) | _4 ->
                 F)
        | (_5,v1,v2) -> bvi_tmcProof_v_rel f v1 v2`;;

(* Install reads byte/word vectors out of values; these are lists of Numbers
   resp. Word64s, which v_rel relates exactly. *)

(* HOL4 bvi_tmcProofScript.sml:1520-1541: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1543-1549: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1551-1563: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1565-1593: a proof *)
  (* SetGlobal *)
(* HOL4 bvi_tmcProofScript.sml:1595-1616: a proof *)

(* Allocating a fresh reference (Ref, RefByte, RefArray). *)
(* HOL4 bvi_tmcProofScript.sml:1619-1640: a proof *)

(* Reading a reference without changing the state, returning a fresh value
   (Length, LengthByte, DerefByte, BoundsCheckArray, BoundsCheckByte). *)
(* HOL4 bvi_tmcProofScript.sml:1644-1650: a proof *)

(* Reading an element out of a ValueArray reference (El on a RefPtr). *)
(* HOL4 bvi_tmcProofScript.sml:1653-1662: a proof *)

(* Reading an element out of a Block (El on a Block). *)
(* HOL4 bvi_tmcProofScript.sml:1665-1670: a proof *)

(* Updating a ValueArray reference in place (Update). *)
(* HOL4 bvi_tmcProofScript.sml:1673-1689: a proof *)

(* Updating a ByteArray reference in place (UpdateByte, CopyByte, XorByte).
   The byte arrays are equal on both sides, so the operations agree. *)
(* HOL4 bvi_tmcProofScript.sml:1693-1703: a proof *)

(* Turning a stack of mutable conses into a Block (FinaliseCons). *)
(* HOL4 bvi_tmcProofScript.sml:1706-1713: a proof *)

(* Mutating the hole of a MutBlock (UpdateCons) cannot happen: state_ref_rel
   never relates a MutBlock. *)
(* HOL4 bvi_tmcProofScript.sml:1717-1719: a proof *)

(* ConfigGC returns Unit and leaves the state unchanged. *)
(* HOL4 bvi_tmcProofScript.sml:1722-1725: a proof *)

(* Comparing two ByteArray references without changing the state (StringCmp).
   Both byte arrays are equal on the two sides, so the comparison agrees. *)
(* HOL4 bvi_tmcProofScript.sml:1729-1734: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1768-1774: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1776-1784: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1786-1796: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1814-1817: a proof *)
   (* UpdateThunk *)
(* HOL4 bvi_tmcProofScript.sml:1819-1840: a proof *)
  (* AllocThunk *)
(* HOL4 bvi_tmcProofScript.sml:1842-1861: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1863-1884: a proof *)

(* Structural block operations with a fresh, state-preserving result
   (Cons, TagLenEq, LenEq, TagEq, LengthBlock, BoolTest, BoundsCheckBlock,
   EqualConst on a Number/Word64). *)
(* HOL4 bvi_tmcProofScript.sml:1889-1895: a proof *)

(* ElemAt reading an element out of a Block value. *)
(* HOL4 bvi_tmcProofScript.sml:1898-1905: a proof *)

(* ElemAt reading an element out of a ValueArray reference. *)
(* HOL4 bvi_tmcProofScript.sml:1908-1917: a proof *)

(* ConsExtend: result is an append of (a prefix of) two related blocks. *)
(* HOL4 bvi_tmcProofScript.sml:1920-1929: a proof *)

(* FromList: convert a list value to a packed Block. *)
(* HOL4 bvi_tmcProofScript.sml:1932-1938: a proof *)

(* ListAppend: append two lists. *)
(* HOL4 bvi_tmcProofScript.sml:1941-1945: a proof *)

(* Equal: structural equality preserved by the renaming (uses do_eq_v_rel). *)
(* HOL4 bvi_tmcProofScript.sml:1948-1956: a proof *)

(* EqualConst on a string constant (a compare-by-contents byte array). *)
(* HOL4 bvi_tmcProofScript.sml:1959-1966: a proof *)

(* Build: evaluate a constant, possibly allocating byte arrays for strings. *)
(* HOL4 bvi_tmcProofScript.sml:1969-1977: a proof *)

(* BoolNot: negates a boolean; the argument value is a Boolv, equal on both
   sides, so the negation agrees. *)
(* HOL4 bvi_tmcProofScript.sml:1981-1987: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1989-1998: a proof *)

(* HOL4 bvi_tmcProofScript.sml:2000-2123: a proof *)

(* HOL4 bvi_tmcProofScript.sml:2125: a proof *)

let is_block_op_cons_def = cake_define
  `is_block_op_cons op <=>
     (?block_tag.
       op = closLang_BlockOp (closLang_Cons block_tag))`;;

let optimised_code_def = cake_define
  `optimised_code loc loc_opt c1 c2 <=>
     (?arity body body_wrap body_work.
       sptree_lookup loc c1 = SOME (arity,body) /\
       sptree_lookup loc c2 = SOME (arity,body_wrap) /\
       sptree_lookup loc_opt c2 = SOME (arity + 2,body_work) /\
       rewrite_wrapper loc loc_opt arity body = SOME body_wrap /\
       rewrite_worker loc loc_opt arity (arity + 1) arity body =
         body_work)`;;

(* HOL4 bvi_tmcProofScript.sml:3031-3106: a proof *)

let hypothesis_def = cake_define
  `hypothesis xs' (s'':(num#'c,'ffi)bviSem_state) clock <=> state_clock
   s'' < clock ==>
   (!env1' r' t' opt' f' s'3' env2' loc'.
             evaluate (xs',env1',s'') = (r',t') /\
             bvi_tmcProof_env_rel opt' f' env1' env2' /\ EVERY (\x.
               no_mutcons x) xs' /\
             bvi_tmcProof_state_rel f' s'' s'3' /\
             (opt' ==> LENGTH xs' = 1) /\ ~(
             r' = Rerr (Rabort Rtype_error)) ==>
             (?t'' f'' r''.
               evaluate (xs',env2',s'3') = (r'',t'') /\
               semanticPrimitivesProps_result_rel (LIST_REL
                 (bvi_tmcProof_v_rel f'')) (eor_rel f'') r' r'' /\
               bvi_tmcProof_state_rel f'' t' t'' /\ f' SUBMAP f'' /\
                 only_fresh f' f'' (state_refs s'3') /\
               holes_unchanged_except f' (state_refs s'3')
                 (state_refs t'') {} /\
               holes_still_not_finalised f' (state_refs s'3')
                 (state_refs t'') /\
               (!loc_opt.
                 optimised_code loc' loc_opt (state_code s'')
                   (state_code s'3') ==>
                 (!wrap.
                    LENGTH xs' = 1 /\
                    rewrite_wrapper loc' loc_opt (LENGTH env1') (HD
                      xs') = SOME wrap ==>
                    (?t_wrap f_wrap r_wrap.
                      evaluate ([wrap],env2',s'3') = (r_wrap,t_wrap)
                        /\
                      semanticPrimitivesProps_result_rel (LIST_REL
                        (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r'
                        r_wrap /\ bvi_tmcProof_state_rel f_wrap t'
                          t_wrap /\ f' SUBMAP f_wrap /\
                      only_fresh f' f_wrap (state_refs s'3') /\
                      holes_unchanged_except f' (state_refs s'3')
                        (state_refs t_wrap) {} /\
                      holes_still_not_finalised f' (state_refs s'3')
                        (state_refs t_wrap))) /\
                 (opt' ==>
                  (!hole_ptr.
                    (?c. hole_has_val f' env1' env2' (state_refs
                      s'3') c) /\
                    hole_not_finalised (state_refs s'3') hole_ptr /\
                      EL (LENGTH env1')
                    env2' = RefPtr F hole_ptr ==>
                    (?r_work f_work t_work.
                      evaluate
                        ([rewrite_worker loc' loc_opt (LENGTH env1')
                            (LENGTH env1' + 1) (LENGTH env1') (HD
                              xs')],env2',s'3') =
                      (r_work,t_work) /\ opt_res_rel f_work r' r_work
                        /\
                      bvi_tmcProof_state_rel f_work t' t_work /\ f'
                        SUBMAP f_work /\
                      only_fresh f' f_work (state_refs s'3') /\
                      holes_unchanged_except f' (state_refs s'3')
                        (state_refs t_work) {hole_ptr} /\
                      holes_still_not_finalised f' (state_refs s'3')
                        (state_refs t_work) /\
                      (!res_v.
                        r' = Rval [res_v] ==>
                        (?res_v'.
                          mb_rel f_work (state_refs s'3') (state_refs
                            t_work \\ hole_ptr) res_v res_v' /\
                          hole_has_val f' env1' env2' (state_refs
                            t_work) res_v'))))))))`;;

let alloc_hole_has_val_def = cake_define
  `alloc_hole_has_val f refs extras i_ptr c_idx c <=>
     (?hole_ptr tag left right.
       i_ptr < LENGTH extras /\ EL i_ptr
       extras = RefPtr F hole_ptr /\
       c_idx = LENGTH left /\
       small_enough_int (&(LENGTH left)) /\ ~(
       hole_ptr IN FRANGE f) /\
       FLOOKUP refs hole_ptr = SOME (bvlSem_MutBlock tag F left c
         right))`;;

(* HOL4 bvi_tmcProofScript.sml:4209: a proof *)
  (* Phase 1 theorem in s *)
(* HOL4 bvi_tmcProofScript.sml:4211-4216: a proof *)
  (* Hypothesis on bs *)
(* HOL4 bvi_tmcProofScript.sml:4218-4231: a proof *)
  (* Phase 1 theorem in s' *)
(* HOL4 bvi_tmcProofScript.sml:4233-4263: a proof *)
  (* Phase 2 theorem *)
(* HOL4 bvi_tmcProofScript.sml:4265-4418: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4420-4421: a proof *)
  (* First inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4423-4439: a proof *)
  (* Second inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4441-4488: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4490-4513: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4515-4518: a proof *)
  (* First inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4520-4652: a proof *)
    (* Else inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4654-4768: a proof *)
  (* Error case *)
(* HOL4 bvi_tmcProofScript.sml:4770-4792: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4794-4797: a proof *)
  (* First inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4799-4829: a proof *)
  (* Second inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4831-4936: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4938-4975: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4977-5026: a proof *)

(* HOL4 bvi_tmcProofScript.sml:5091-5095: a proof *)
  (* xs inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:5097-5111: a proof *)
  (* Error case *)
(* HOL4 bvi_tmcProofScript.sml:5113-5445: a proof *)

let dest_thunk_ret_rel_def = cake_define
  `dest_thunk_ret_rel f t1 t2 <=>
     ((t1 = BadRef /\ t2 = BadRef) \/
      (t1 = NotThunk /\ t2 = NotThunk) \/
      (?tm1 tm2 v1 v2.
        t1 = IsThunk tm1 v1 /\ t2 = IsThunk tm2 v2 /\
        tm1 = tm2 /\
        bvi_tmcProof_v_rel f v1 v2))`;;

(* HOL4 bvi_tmcProofScript.sml:5496-5594: a proof *)

(* HOL4 bvi_tmcProofScript.sml:5596-5599: a proof *)
  (* args inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:5601-5645: a proof *)
      (* callee inductive hypothesis (smaller clock) *)
(* HOL4 bvi_tmcProofScript.sml:5647-5744: a proof *)
          (* the wrapper-IH gives the target callee result for body'; rename to
             controlled names and discard the spurious direct-IH result for exp *)
(* HOL4 bvi_tmcProofScript.sml:5747-5831: a proof *)

(* HOL4 bvi_tmcProofScript.sml:5833-5869: a proof *)

(* HOL4 bvi_tmcProofScript.sml:5871: a proof *)

(* -------------------------------------------------------------------------
   Code labels: the pass only introduces calls to the fresh worker names it
   allocates, so every label of the output is a label of the input or one of
   the names strictly below the final next-name.
   ------------------------------------------------------------------------- *)
