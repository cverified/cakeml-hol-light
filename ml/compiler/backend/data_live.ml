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
needs "lib/ternaryComparisons.ml";;
needs "semantics/ast.ml";;

let is_pure_def = cake_define
  `data_live_is_pure x1 =
        match x1 with
          (FFI _1) -> F
        | (IntOp Add) -> F
        | (IntOp Sub) -> F
        | (IntOp Mult) -> F
        | (IntOp Div) -> F
        | (IntOp Mod) -> F
        | (IntOp (LESS)) -> F
        | (IntOp LessEq) -> F
        | (WordOp (WordOpw W64 _2)) -> F
        | (WordOp (WordShift W64 _3 _4)) -> F
        | (WordOp WordFromInt) -> F
        | (WordOp WordToInt) -> F
        | (WordOp (WordFromWord b)) -> F
        | (WordOp (FP_uop _5)) -> F
        | (WordOp (FP_bop _6)) -> F
        | (WordOp (FP_top _7)) -> F
        | (BlockOp (Build _8)) -> F
        | (BlockOp (Cons _9)) -> F
        | (BlockOp (ConsExtend _10)) -> F
        | (BlockOp (FromList _11)) -> F
        | (BlockOp ListAppend) -> F
        | (BlockOp (EQUAL)) -> F
        | (GlobOp (SetGlobal _12)) -> F
        | (GlobOp SetGlobalsPtr) -> F
        | (MemOp Ref) -> F
        | (MemOp (RefByte _13)) -> F
        | (MemOp RefArray) -> F
        | (MemOp Update) -> F
        | (MemOp (MutCons _14 _15)) -> F
        | (MemOp UpdateCons) -> F
        | (MemOp FinaliseCons) -> F
        | (MemOp UpdateByte) -> F
        | (MemOp FromListByte) -> F
        | (MemOp (CopyByte _16)) -> F
        | (MemOp XorByte) -> F
        | (MemOp ConfigGC) -> F
        | Install -> F
        | (ThunkOp _17) -> F
        | _18 -> T`;;
hol4_overload "is_pure" "data_live_is_pure";;

let compile_def = cake_define
  `data_live_compile x1 live =
        match x1 with
          Skip -> (Skip,live)
        | (Return ns) -> (Return ns,list_insert ns LN)
        | (Raise n) -> (Raise n,insert n one LN)
        | (Move n1 n2) ->
       (Move n1 n2,insert n2 one (delete n1 live))
        | (Seq c1 c2) ->
        let (d2,l2) = data_live_compile c2 live in
        let (d1,l1) = data_live_compile c1 l2 in
          (Seq d1 d2,l1)
        | Tick -> (Tick,live)
        | (MakeSpace k names) ->
        let l1 = inter names live in (MakeSpace k l1,l1)
        | (Assign v op vs NONE) ->
        if IS_NONE (lookup v live) /\ is_pure op then (Skip,live)
          else
          let l1 = list_insert vs (delete v live) in
            (Assign v op vs NONE,l1)
        | (Assign v op vs (SOME names)) ->
        let l1 = inter names (delete v live) in
          (Assign v op vs (SOME l1),list_insert vs l1)
        | (If n c2 c3) ->
        let (d3,l3) = data_live_compile c3 live in
        let (d2,l2) = data_live_compile c2 live in
          (If n d2 d3,insert n one (union l2 l3))
        | (Force NONE loc src) ->
        (Force NONE loc src,insert src one LN)
        | (Force (SOME (n,names)) loc src) ->
        let l1 = inter names (delete n live) in
        let l2 = insert src one l1 in
          (Force (SOME (n,l1)) loc src,l2)
        | (Call NONE dest vs handler) ->
        (Call NONE dest vs handler,list_to_num_set vs)
        | (Call (SOME (ns,names)) dest vs NONE) ->
        let l1 = inter names (list_delete ns live) in
        let l2 = list_insert vs l1 in
          (Call (SOME (ns,l1)) dest vs NONE,l2)
        | (Call (SOME (ns,names)) dest vs (SOME (v,c))) ->
        let (d,l3) = data_live_compile c live in
        let l0 = union (list_delete ns live) (delete v l3) in
        let l1 = inter names l0 in
        let l2 = list_insert vs l1 in
          (Call (SOME (ns,l1)) dest vs (SOME (v,d)),l2)`;;
hol4_overload "compile" "data_live_compile";;
