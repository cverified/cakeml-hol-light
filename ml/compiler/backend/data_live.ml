(* ======================================================== *)
(*  data_live: ported from HOL4's
    compiler/backend/data_liveScript.sml  *)
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
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "data_live"
  ["dataLang"];;

let _ = do_list hide_constant ["pmatch"];;

let is_pure_def = new_definition
  `data_live_is_pure x1 =
        match x1 with
          (FFI _2:closLang_op) -> F
        | (closLang_IntOp closLang_Add) -> F
        // TODO: these would be pure if space usage were not tracked
        | (closLang_IntOp closLang_Sub) -> F
        // which could be a switch in the semantics
        | (closLang_IntOp closLang_Mult) -> F
        | (closLang_IntOp closLang_Div) -> F
        | (closLang_IntOp closLang_Mod) -> F
        | (closLang_IntOp closLang_Less) -> F
        // TODO: are these really impure?
        | (closLang_IntOp closLang_LessEq) -> F
        | (closLang_WordOp (WordOpw ast_W64 _3)) -> F
        | (closLang_WordOp (WordShift ast_W64 _4 _5)) -> F
        | (closLang_WordOp WordFromInt) -> F
        | (closLang_WordOp WordToInt) -> F
        | (closLang_WordOp (WordFromWord b)) -> F
        | (closLang_WordOp (FP_uop _6)) -> F
        | (closLang_WordOp (FP_bop _7)) -> F
        | (closLang_WordOp (FP_top _8)) -> F
        | (closLang_BlockOp (closLang_Build _9)) -> F
        | (closLang_BlockOp (closLang_Cons _10)) -> F
        | (closLang_BlockOp (closLang_ConsExtend _11)) -> F
        | (closLang_BlockOp (closLang_FromList _12)) -> F
        | (closLang_BlockOp ListAppend) -> F
        | (closLang_BlockOp closLang_Equal) -> F
        | (closLang_GlobOp (closLang_SetGlobal _13)) -> F
        | (closLang_GlobOp closLang_SetGlobalsPtr) -> F
        | (closLang_MemOp closLang_Ref) -> F
        | (closLang_MemOp (closLang_RefByte _14)) -> F
        | (closLang_MemOp closLang_RefArray) -> F
        | (closLang_MemOp closLang_Update) -> F
        | (closLang_MemOp (closLang_MutCons _15 _16)) -> F
        | (closLang_MemOp closLang_UpdateCons) -> F
        | (closLang_MemOp closLang_FinaliseCons) -> F
        | (closLang_MemOp closLang_UpdateByte) -> F
        | (closLang_MemOp closLang_FromListByte) -> F
        | (closLang_MemOp (closLang_CopyByte _17)) -> F
        | (closLang_MemOp closLang_XorByte) -> F
        | (closLang_MemOp ConfigGC) -> F
        | closLang_Install -> F
        | (ThunkOp _18) -> F
        | _19 -> T`;;
hol4_overload "is_pure" "data_live_is_pure";;

let is_pure_pmatch = prove
 (`!op.
   data_live_is_pure op =
     (match op with FFI _20 -> F | closLang_GlobOp
       (closLang_SetGlobal _21) -> F | closLang_GlobOp
       closLang_SetGlobalsPtr -> F | closLang_WordOp (WordOpw ast_W64
       _22) -> F | closLang_WordOp (WordShift ast_W64 _23 _24) -> F |
       closLang_WordOp WordFromInt -> F | closLang_WordOp WordToInt ->
       F | closLang_WordOp (WordFromWord b) -> F | closLang_WordOp
       (FP_uop _25) -> F | closLang_WordOp (FP_bop _26) -> F |
       closLang_WordOp (FP_top _27) -> F | closLang_BlockOp
       (closLang_Build _28) -> F | closLang_BlockOp (closLang_Cons
       _29) -> F | closLang_BlockOp (closLang_ConsExtend _30) -> F |
       closLang_BlockOp (closLang_FromList _31) -> F |
       closLang_BlockOp ListAppend -> F | closLang_BlockOp
       closLang_Equal -> F | closLang_MemOp closLang_Ref -> F |
       closLang_MemOp (closLang_RefByte _32) -> F | closLang_MemOp
       closLang_RefArray -> F | closLang_MemOp closLang_Update -> F |
       closLang_MemOp (closLang_MutCons _33 _34) -> F | closLang_MemOp
       closLang_UpdateCons -> F | closLang_MemOp closLang_FinaliseCons
       -> F | closLang_MemOp closLang_UpdateByte -> F | closLang_MemOp
       closLang_FromListByte -> F | closLang_MemOp (closLang_CopyByte
       _35) -> F | closLang_MemOp closLang_XorByte -> F |
       closLang_IntOp closLang_Add -> F | closLang_IntOp closLang_Sub
       -> F | closLang_IntOp closLang_Mult -> F | closLang_IntOp
       closLang_Div -> F | closLang_IntOp closLang_Mod -> F |
       closLang_IntOp closLang_Less -> F | closLang_IntOp
       closLang_LessEq -> F | closLang_Install -> F | closLang_MemOp
       ConfigGC -> F | ThunkOp _36 -> F | _37 -> T)`,
  CHEAT_TAC);;

let compile_def,compile_ind = define_shaped_rec
  "cases"
  [`data_live_compile (dataLang_Skip:dataLang_prog) live =
  ((dataLang_Skip:dataLang_prog),live)`;
   `data_live_compile (dataLang_Return ns:dataLang_prog) live =
  ((dataLang_Return ns:dataLang_prog),list_insert ns LN)`;
   `data_live_compile (Raise n:dataLang_prog) live = ((Raise
  n:dataLang_prog),sptree_insert n one LN)`;
   `data_live_compile (dataLang_Move n1 n2:dataLang_prog) live =
        ((dataLang_Move n1 n2:dataLang_prog),sptree_insert n2 one
          (sptree_delete n1 live))`;
   `data_live_compile (dataLang_Seq c1 c2:dataLang_prog) live =
         (let (d2,l2) = data_live_compile c2 live in
         let (d1,l1) = data_live_compile c1 l2 in
           (dataLang_Seq d1 d2,l1))`;
   `data_live_compile (Tick:dataLang_prog) live =
  ((Tick:dataLang_prog),live)`;
   `data_live_compile (dataLang_MakeSpace k names) live =
         (let l1 = inter names live in (dataLang_MakeSpace k
           l1,l1))`;
   `data_live_compile (dataLang_Assign v op vs NONE:dataLang_prog) live
  =
         (if IS_NONE (sptree_lookup v live) /\ data_live_is_pure op
           then (dataLang_Skip,live) else
           let l1 = list_insert vs (sptree_delete v live) in
             ((dataLang_Assign v op vs NONE:dataLang_prog),l1))`;
   `data_live_compile (dataLang_Assign v op vs (SOME
  names):dataLang_prog) live =
         (let l1 = inter names (sptree_delete v live) in
           (dataLang_Assign v op vs (SOME l1),list_insert vs l1))`;
   `data_live_compile (If n c2 c3:dataLang_prog) live =
         (let (d3,l3) = data_live_compile c3 live in
         let (d2,l2) = data_live_compile c2 live in
           (If n d2 d3,sptree_insert n one (sptree_union l2 l3)))`;
   `data_live_compile (Force NONE loc src:dataLang_prog) live =
         ((Force NONE loc src:dataLang_prog),sptree_insert src
           one LN)`;
   `data_live_compile (Force (SOME (n,names)) loc src:dataLang_prog)
  live =
         (let l1 = inter names (sptree_delete n live) in
         let l2 = sptree_insert src one l1 in
           (Force (SOME (n,l1)) loc src,l2))`;
   `data_live_compile (Call NONE dest vs handler:dataLang_prog) live =
         ((Call NONE dest vs
           handler:dataLang_prog),list_to_num_set vs)`;
   `data_live_compile (Call (SOME (ns,names)) dest vs
  NONE:dataLang_prog) live =
         (let l1 = inter names (list_delete ns live) in
         let l2 = list_insert vs l1 in
           (Call (SOME (ns,l1)) dest vs NONE,l2))`;
   `data_live_compile (Call (SOME (ns,names)) dest vs (SOME
  (v,c)):dataLang_prog) live =
         (let (d,l3) = data_live_compile c live in
         let l0 = sptree_union (list_delete ns live) (sptree_delete
           v l3) in
         let l1 = inter names l0 in
         let l2 = list_insert vs l1 in
           (Call (SOME (ns,l1)) dest vs (SOME (v,d)),l2))`];;
hol4_overload "compile" "data_live_compile";;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
