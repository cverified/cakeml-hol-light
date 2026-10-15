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
needs "lib/comparison.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

let is_pure_def = cake_define
  `data_live_is_pure x1 =
        match x1 with
          (FFI _1:closLang_op) -> F
        | (closLang_IntOp Add) -> F
        | (closLang_IntOp Sub) -> F
        | (closLang_IntOp closLang_Mult) -> F
        | (closLang_IntOp Div) -> F
        | (closLang_IntOp Mod) -> F
        | (closLang_IntOp Less) -> F
        | (closLang_IntOp closLang_LessEq) -> F
        | (closLang_WordOp (WordOpw W64 _2)) -> F
        | (closLang_WordOp (WordShift W64 _3 _4)) -> F
        | (closLang_WordOp WordFromInt) -> F
        | (closLang_WordOp WordToInt) -> F
        | (closLang_WordOp (WordFromWord b)) -> F
        | (closLang_WordOp (FP_uop _5)) -> F
        | (closLang_WordOp (FP_bop _6)) -> F
        | (closLang_WordOp (FP_top _7)) -> F
        | (closLang_BlockOp (closLang_Build _8)) -> F
        | (closLang_BlockOp (Cons _9)) -> F
        | (closLang_BlockOp (closLang_ConsExtend _10)) -> F
        | (closLang_BlockOp (closLang_FromList _11)) -> F
        | (closLang_BlockOp ListAppend) -> F
        | (closLang_BlockOp Equal) -> F
        | (closLang_GlobOp (SetGlobal _12)) -> F
        | (closLang_GlobOp SetGlobalsPtr) -> F
        | (closLang_MemOp closLang_Ref) -> F
        | (closLang_MemOp (closLang_RefByte _13)) -> F
        | (closLang_MemOp closLang_RefArray) -> F
        | (closLang_MemOp closLang_Update) -> F
        | (closLang_MemOp (closLang_MutCons _14 _15)) -> F
        | (closLang_MemOp closLang_UpdateCons) -> F
        | (closLang_MemOp closLang_FinaliseCons) -> F
        | (closLang_MemOp closLang_UpdateByte) -> F
        | (closLang_MemOp closLang_FromListByte) -> F
        | (closLang_MemOp (closLang_CopyByte _16)) -> F
        | (closLang_MemOp closLang_XorByte) -> F
        | (closLang_MemOp ConfigGC) -> F
        | closLang_Install -> F
        | (ThunkOp _17) -> F
        | _18 -> T`;;
hol4_overload "is_pure" "data_live_is_pure";;

let compile_def = cake_define_list
  [`data_live_compile dataLang_Skip live = (dataLang_Skip,live)`;
   `data_live_compile (dataLang_Return ns) live = (dataLang_Return
  ns,list_insert ns LN)`;
   `data_live_compile (Raise n:dataLang_prog) live = (Raise
  n,sptree_insert n one LN)`;
   `data_live_compile (dataLang_Move n1 n2) live =
        (dataLang_Move n1 n2,sptree_insert n2 one (sptree_delete
          n1 live))`;
   `data_live_compile (dataLang_Seq c1 c2) live =
         (let (d2,l2) = data_live_compile c2 live in
         let (d1,l1) = data_live_compile c1 l2 in
           (dataLang_Seq d1 d2,l1))`;
   `data_live_compile Tick live = (Tick,live)`;
   `data_live_compile (dataLang_MakeSpace k names) live =
         (let l1 = inter names live in (dataLang_MakeSpace k
           l1,l1))`;
   `data_live_compile (dataLang_Assign v op vs NONE) live =
         (if IS_NONE (sptree_lookup v live) /\ data_live_is_pure op
           then (dataLang_Skip,live) else
           let l1 = list_insert vs (sptree_delete v live) in
             (dataLang_Assign v op vs NONE,l1))`;
   `data_live_compile (dataLang_Assign v op vs (SOME names)) live =
         (let l1 = inter names (sptree_delete v live) in
           (dataLang_Assign v op vs (SOME l1),list_insert vs l1))`;
   `data_live_compile (If n c2 c3:dataLang_prog) live =
         (let (d3,l3) = data_live_compile c3 live in
         let (d2,l2) = data_live_compile c2 live in
           (If n d2 d3,sptree_insert n one (sptree_union l2 l3)))`;
   `data_live_compile (Force NONE loc src:dataLang_prog) live =
         (Force NONE loc src,sptree_insert src one LN)`;
   `data_live_compile (Force (SOME (n,names)) loc src:dataLang_prog)
  live =
         (let l1 = inter names (sptree_delete n live) in
         let l2 = sptree_insert src one l1 in
           (Force (SOME (n,l1)) loc src,l2))`;
   `data_live_compile (Call NONE dest vs handler:dataLang_prog) live =
         (Call NONE dest vs handler,list_to_num_set vs)`;
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
