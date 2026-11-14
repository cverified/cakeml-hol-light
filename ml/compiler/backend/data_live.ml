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
       clos_FFI _ -> F
     | clos_IntOp clos_Add -> F
     // TODO: these would be pure if space usage were not tracked
     | clos_IntOp clos_Sub -> F
     // which could be a switch in the semantics
     | clos_IntOp clos_Mult -> F
     | clos_IntOp clos_Div -> F
     | clos_IntOp clos_Mod -> F
     | clos_IntOp clos_Less -> F
     // TODO: are these really impure?
     | clos_IntOp clos_LessEq -> F
     | clos_WordOp (WordOpw ast_W64 _) -> F
     | clos_WordOp (WordShift ast_W64 _ _) -> F
     | clos_WordOp WordFromInt -> F
     | clos_WordOp WordToInt -> F
     | clos_WordOp (WordFromWord b) -> F
     | clos_WordOp (FP_uop _) -> F
     | clos_WordOp (FP_bop _) -> F
     | clos_WordOp (FP_top _) -> F
     | clos_BlockOp (clos_Build _) -> F
     | clos_BlockOp (clos_Cons _) -> F
     | clos_BlockOp (clos_ConsExtend _) -> F
     | clos_BlockOp (clos_FromList _) -> F
     | clos_BlockOp clos_ListAppend -> F
     | clos_BlockOp clos_Equal -> F
     | clos_GlobOp (clos_SetGlobal _) -> F
     | clos_GlobOp clos_SetGlobalsPtr -> F
     | clos_MemOp clos_Ref -> F
     | clos_MemOp (clos_RefByte _) -> F
     | clos_MemOp clos_RefArray -> F
     | clos_MemOp clos_Update -> F
     | clos_MemOp (clos_MutCons _ _) -> F
     | clos_MemOp clos_UpdateCons -> F
     | clos_MemOp clos_FinaliseCons -> F
     | clos_MemOp clos_UpdateByte -> F
     | clos_MemOp clos_FromListByte -> F
     | clos_MemOp (clos_CopyByte _) -> F
     | clos_MemOp clos_XorByte -> F
     | clos_MemOp clos_ConfigGC -> F
     | clos_Install -> F
     | clos_ThunkOp _ -> F
     | _ -> T`;;

let is_pure_pmatch = prove
 (`!op.
   data_live_is_pure op =
     match op with clos_FFI _ -> F
     | clos_GlobOp (clos_SetGlobal _) -> F
     | clos_GlobOp clos_SetGlobalsPtr -> F
     | clos_WordOp (WordOpw ast_W64 _) -> F
     | clos_WordOp (WordShift ast_W64 _ _) -> F
     | clos_WordOp WordFromInt -> F
     | clos_WordOp WordToInt -> F
     | clos_WordOp (WordFromWord b) -> F
     | clos_WordOp (FP_uop _) -> F
     | clos_WordOp (FP_bop _) -> F
     | clos_WordOp (FP_top _) -> F
     | clos_BlockOp (clos_Build _) -> F
     | clos_BlockOp (clos_Cons _) -> F
     | clos_BlockOp (clos_ConsExtend _) -> F
     | clos_BlockOp (clos_FromList _) -> F
     | clos_BlockOp clos_ListAppend -> F
     | clos_BlockOp clos_Equal -> F
     | clos_MemOp clos_Ref -> F
     | clos_MemOp (clos_RefByte _) -> F
     | clos_MemOp clos_RefArray -> F
     | clos_MemOp clos_Update -> F
     | clos_MemOp (clos_MutCons _ _) -> F
     | clos_MemOp clos_UpdateCons -> F
     | clos_MemOp clos_FinaliseCons -> F
     | clos_MemOp clos_UpdateByte -> F
     | clos_MemOp clos_FromListByte -> F
     | clos_MemOp (clos_CopyByte _) -> F
     | clos_MemOp clos_XorByte -> F
     | clos_IntOp clos_Add -> F
     | clos_IntOp clos_Sub -> F
     | clos_IntOp clos_Mult -> F
     | clos_IntOp clos_Div -> F
     | clos_IntOp clos_Mod -> F
     | clos_IntOp clos_Less -> F
     | clos_IntOp clos_LessEq -> F
     | clos_Install -> F
     | clos_MemOp clos_ConfigGC -> F
     | clos_ThunkOp _ -> F
     | _ -> T`,
  CHEAT_TAC);;

let compile_def,compile_ind = define_shaped_rec
  "cases"
  `(data_live_compile data_Skip live = ((data_Skip:data_prog),live)) /\
   (data_live_compile (data_Return ns) live = ((data_Return
    ns:data_prog),list_insert ns LN)) /\
   (data_live_compile (data_Raise n) live = ((data_Raise
    n:data_prog),sptree_insert n one LN)) /\
   (data_live_compile (data_Move n1 n2) live =
        ((data_Move n1 n2:data_prog),sptree_insert n2 one
            (sptree_delete n1 live))) /\
   (data_live_compile (data_Seq c1 c2) live =
         let (d2,l2) = data_live_compile c2 live in
         let (d1,l1) = data_live_compile c1 l2 in
           (data_Seq d1 d2,l1)) /\
   (data_live_compile data_Tick live = ((data_Tick:data_prog),live)) /\
   (data_live_compile (data_MakeSpace k names) live =
         let l1 = inter names live in (data_MakeSpace k l1,l1)) /\
   (data_live_compile (data_Assign v op vs NONE) live =
         if IS_NONE (sptree_lookup v live) /\ data_live_is_pure op then
             (data_Skip,live) else let l1 = list_insert vs (sptree_delete v
             live) in
             ((data_Assign v op vs NONE:data_prog),l1)) /\
   (data_live_compile (data_Assign v op vs (SOME names)) live =
         let l1 = inter names (sptree_delete v live) in
           (data_Assign v op vs (SOME l1),list_insert vs l1)) /\
   (data_live_compile (data_If n c2 c3) live =
         let (d3,l3) = data_live_compile c3 live in
         let (d2,l2) = data_live_compile c2 live in
           (data_If n d2 d3,sptree_insert n one (sptree_union l2 l3))) /\
   (data_live_compile (data_Force NONE loc src) live =
         ((data_Force NONE loc src:data_prog),sptree_insert src one LN)) /\
   (data_live_compile (data_Force (SOME (n,names)) loc src) live =
         let l1 = inter names (sptree_delete n live) in
         let l2 = sptree_insert src one l1 in
           (data_Force (SOME (n,l1)) loc src,l2)) /\
   (data_live_compile (data_Call NONE dest vs handler) live =
         ((data_Call NONE dest vs handler:data_prog),list_to_num_set
             vs)) /\
   (data_live_compile (data_Call (SOME (ns,names)) dest vs NONE) live =
         let l1 = inter names (list_delete ns live) in
         let l2 = list_insert vs l1 in
           (data_Call (SOME (ns,l1)) dest vs NONE,l2)) /\
   (data_live_compile (data_Call (SOME (ns,names)) dest vs (SOME (v,c))) live =
         let (d,l3) = data_live_compile c live in
         let l0 = sptree_union (list_delete ns live) (sptree_delete v l3)
             in
         let l1 = inter names l0 in
         let l2 = list_insert vs l1 in
           (data_Call (SOME (ns,l1)) dest vs (SOME (v,d)),l2))`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
