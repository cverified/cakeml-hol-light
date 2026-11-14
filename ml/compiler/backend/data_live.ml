(* ======================================================== *)
(*  data_live: ported from HOL4's
    compiler/backend/data_liveScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by bvi_to_data.ml, dataSem.ml, data_liveProof.ml and
    wordProps.ml.  *)
(* ======================================================== *)

(*
  This compiler phase minimises the live-var annotations that are
  attached to MakeSpace, Assign and Call in dataLang programs. This
  phase also locally deletes code that has no observable effect.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "data_live"
  ["dataLang"];;

let _ = do_list hide_constant ["pmatch"];;

let is_pure_def = new_definition
  `data_live_is_pure x1 =
     match x1 with
       closLang_FFI _ -> F
     | closLang_IntOp closLang_Add -> F
     // TODO: these would be pure if space usage were not tracked
     | closLang_IntOp closLang_Sub -> F
     // which could be a switch in the semantics
     | closLang_IntOp closLang_Mult -> F
     | closLang_IntOp closLang_Div -> F
     | closLang_IntOp closLang_Mod -> F
     | closLang_IntOp closLang_Less -> F
     // TODO: are these really impure?
     | closLang_IntOp closLang_LessEq -> F
     | closLang_WordOp (WordOpw ast_W64 _) -> F
     | closLang_WordOp (WordShift ast_W64 _ _) -> F
     | closLang_WordOp WordFromInt -> F
     | closLang_WordOp WordToInt -> F
     | closLang_WordOp (WordFromWord b) -> F
     | closLang_WordOp (FP_uop _) -> F
     | closLang_WordOp (FP_bop _) -> F
     | closLang_WordOp (FP_top _) -> F
     | closLang_BlockOp (closLang_Build _) -> F
     | closLang_BlockOp (closLang_Cons _) -> F
     | closLang_BlockOp (closLang_ConsExtend _) -> F
     | closLang_BlockOp (closLang_FromList _) -> F
     | closLang_BlockOp closLang_ListAppend -> F
     | closLang_BlockOp closLang_Equal -> F
     | closLang_GlobOp (closLang_SetGlobal _) -> F
     | closLang_GlobOp closLang_SetGlobalsPtr -> F
     | closLang_MemOp closLang_Ref -> F
     | closLang_MemOp (closLang_RefByte _) -> F
     | closLang_MemOp closLang_RefArray -> F
     | closLang_MemOp closLang_Update -> F
     | closLang_MemOp (closLang_MutCons _ _) -> F
     | closLang_MemOp closLang_UpdateCons -> F
     | closLang_MemOp closLang_FinaliseCons -> F
     | closLang_MemOp closLang_UpdateByte -> F
     | closLang_MemOp closLang_FromListByte -> F
     | closLang_MemOp (closLang_CopyByte _) -> F
     | closLang_MemOp closLang_XorByte -> F
     | closLang_MemOp closLang_ConfigGC -> F
     | closLang_Install -> F
     | closLang_ThunkOp _ -> F
     | _ -> T`;;

let is_pure_pmatch = prove
 (`!op.
   data_live_is_pure op =
     match op with closLang_FFI _ -> F
     | closLang_GlobOp (closLang_SetGlobal _) -> F
     | closLang_GlobOp closLang_SetGlobalsPtr -> F
     | closLang_WordOp (WordOpw ast_W64 _) -> F
     | closLang_WordOp (WordShift ast_W64 _ _) -> F
     | closLang_WordOp WordFromInt -> F
     | closLang_WordOp WordToInt -> F
     | closLang_WordOp (WordFromWord b) -> F
     | closLang_WordOp (FP_uop _) -> F
     | closLang_WordOp (FP_bop _) -> F
     | closLang_WordOp (FP_top _) -> F
     | closLang_BlockOp (closLang_Build _) -> F
     | closLang_BlockOp (closLang_Cons _) -> F
     | closLang_BlockOp (closLang_ConsExtend _) -> F
     | closLang_BlockOp (closLang_FromList _) -> F
     | closLang_BlockOp closLang_ListAppend -> F
     | closLang_BlockOp closLang_Equal -> F
     | closLang_MemOp closLang_Ref -> F
     | closLang_MemOp (closLang_RefByte _) -> F
     | closLang_MemOp closLang_RefArray -> F
     | closLang_MemOp closLang_Update -> F
     | closLang_MemOp (closLang_MutCons _ _) -> F
     | closLang_MemOp closLang_UpdateCons -> F
     | closLang_MemOp closLang_FinaliseCons -> F
     | closLang_MemOp closLang_UpdateByte -> F
     | closLang_MemOp closLang_FromListByte -> F
     | closLang_MemOp (closLang_CopyByte _) -> F
     | closLang_MemOp closLang_XorByte -> F
     | closLang_IntOp closLang_Add -> F
     | closLang_IntOp closLang_Sub -> F
     | closLang_IntOp closLang_Mult -> F
     | closLang_IntOp closLang_Div -> F
     | closLang_IntOp closLang_Mod -> F
     | closLang_IntOp closLang_Less -> F
     | closLang_IntOp closLang_LessEq -> F
     | closLang_Install -> F
     | closLang_MemOp closLang_ConfigGC -> F
     | closLang_ThunkOp _ -> F
     | _ -> T`,
  CHEAT_TAC);;

let compile_def,compile_ind = define_shaped_rec
  "cases"
  `(data_live_compile dataLang_Skip live =
    ((dataLang_Skip:dataLang_prog),live)) /\
   (data_live_compile (dataLang_Return ns) live = ((dataLang_Return
    ns:dataLang_prog),list_insert ns LN)) /\
   (data_live_compile (dataLang_Raise n) live = ((dataLang_Raise
    n:dataLang_prog),sptree_insert n one LN)) /\
   (data_live_compile (dataLang_Move n1 n2) live =
        ((dataLang_Move n1 n2:dataLang_prog),sptree_insert n2 one
            (sptree_delete n1 live))) /\
   (data_live_compile (dataLang_Seq c1 c2) live =
         let (d2,l2) = data_live_compile c2 live in
         let (d1,l1) = data_live_compile c1 l2 in
           (dataLang_Seq d1 d2,l1)) /\
   (data_live_compile dataLang_Tick live =
    ((dataLang_Tick:dataLang_prog),live)) /\
   (data_live_compile (dataLang_MakeSpace k names) live =
         let l1 = inter names live in (dataLang_MakeSpace k l1,l1)) /\
   (data_live_compile (dataLang_Assign v op vs NONE) live =
         if IS_NONE (sptree_lookup v live) /\ data_live_is_pure op then
             (dataLang_Skip,live) else let l1 = list_insert vs (sptree_delete v
             live) in
             ((dataLang_Assign v op vs NONE:dataLang_prog),l1)) /\
   (data_live_compile (dataLang_Assign v op vs (SOME names)) live =
         let l1 = inter names (sptree_delete v live) in
           (dataLang_Assign v op vs (SOME l1),list_insert vs l1)) /\
   (data_live_compile (dataLang_If n c2 c3) live =
         let (d3,l3) = data_live_compile c3 live in
         let (d2,l2) = data_live_compile c2 live in
           (dataLang_If n d2 d3,sptree_insert n one (sptree_union l2
               l3))) /\
   (data_live_compile (dataLang_Force NONE loc src) live =
         ((dataLang_Force NONE loc src:dataLang_prog),sptree_insert src
             one LN)) /\
   (data_live_compile (dataLang_Force (SOME (n,names)) loc src) live =
         let l1 = inter names (sptree_delete n live) in
         let l2 = sptree_insert src one l1 in
           (dataLang_Force (SOME (n,l1)) loc src,l2)) /\
   (data_live_compile (dataLang_Call NONE dest vs handler) live =
         ((dataLang_Call NONE dest vs
             handler:dataLang_prog),list_to_num_set vs)) /\
   (data_live_compile (dataLang_Call (SOME (ns,names)) dest vs NONE) live =
         let l1 = inter names (list_delete ns live) in
         let l2 = list_insert vs l1 in
           (dataLang_Call (SOME (ns,l1)) dest vs NONE,l2)) /\
   (data_live_compile (dataLang_Call (SOME (ns,names)) dest vs (SOME (v,c)))
    live =
         let (d,l3) = data_live_compile c live in
         let l0 = sptree_union (list_delete ns live) (sptree_delete v l3)
             in
         let l1 = inter names l0 in
         let l2 = list_insert vs l1 in
           (dataLang_Call (SOME (ns,l1)) dest vs (SOME (v,d)),l2))`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
