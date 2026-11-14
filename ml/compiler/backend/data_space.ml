(* ======================================================== *)
(*  data_space: ported from HOL4's
    compiler/backend/data_spaceScript.sml
    A definition theory, with 6 definitions and 1 theorem.  Needed
    by bvi_to_data.ml, dataProps.ml, dataSem.ml, data_spaceProof.ml,
    data_to_word_memoryProof.ml and export.ml.  *)
(* ======================================================== *)

(*
  This dataLang phase lumps together MakeSpace operations. Each
  MakeSpace operations corresponds to a memory allocation in the later
  wordLang code. By lumping together MakeSpace operations we turn
  several calls to the memory allocator into a single efficient call.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "data_space"
  ["dataLang"];;

let _ = do_list hide_constant ["pmatch"];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let num_size_def,num_size_ind = define_wf
  `MEASURE (\x0. (\n. n) x0)`
  [`data_space_num_size (n:num) =
     (if n < 2 EXP 32 then 2:num else 1 + data_space_num_size (n
       DIV 2 EXP 32))`];;

(* HOL4's basicSizeTheory has a num_size of its own (the size
   function of a numeral, which ml/lib/hol4.ml has), and this
   definition shadows it in every theory that has data_spaceTheory
   as an ancestor -- so the num_size of a later statement is this
   one.  Without the overload the port would read those statements
   as the size function, and two of
   compiler/backend/proofs/data_to_word_memoryProof.ml would say
   something false (see ISSUES.md). *)
hol4_overload "num_size" "data_space_num_size";;

let part_space_req_def = define_cases
  [`part_space_req (closLang_W64 s:const_part) = 3`;
   `part_space_req (closLang_Int i:const_part) =
      (if num_of_int (abs i) < 2 EXP 29 then 0 else
          data_space_num_size (num_of_int (abs i)))`;
   `part_space_req (closLang_Str s:const_part) = strlen s DIV 4 + 2`;
   `part_space_req (closLang_Con t ns:const_part) =
      (let l = LENGTH ns in if l = 0 then 0 else l + 1)`];;

let op_space_req_def = new_definition
  `op_space_req x1 l =
        match x1 with
          closLang_MemOp closLang_Ref -> l + 1
        | (closLang_MemOp (closLang_MutCons tag k)) -> l + 1
        | (closLang_BlockOp (closLang_Cons _1)) -> (if l = 0 then 0
          else l + 1)
        | (closLang_BlockOp (closLang_Build parts')) -> SUM (MAP
          part_space_req parts')
        | (closLang_WordOp (WordOpw ast_W64 _2)) -> 3
        | (closLang_WordOp (WordShift ast_W64 _3 _4)) -> 3
        | (closLang_WordOp WordFromInt) -> 3
        | (closLang_WordOp WordToInt) -> 3
        | (closLang_WordOp (WordFromWord F)) -> 3
        | (closLang_WordOp (FP_uop _5)) -> 3
        | (closLang_WordOp (FP_bop _6)) -> 3
        | (closLang_WordOp (FP_top _7)) -> 3
        | (closLang_ThunkOp (AllocThunk _8)) -> l + 1
        | _9 -> 0`;;

(* HOL4 data_spaceScript.sml:46-66: code that the source has in a
   comment *)

let pMakeSpace_def = define_cases
  [`pMakeSpace (INL c) = c`;
   `pMakeSpace (INR (k,names,c)) = dataLang_Seq (dataLang_MakeSpace
    k names) c`];;

let space_def,space_ind = define_shaped_rec
  "match"
  [`space c =
        match c with
          dataLang_MakeSpace k names -> INR (k,names,dataLang_Skip)
        | (dataLang_Seq c1 c2) ->
        (let d1 = pMakeSpace (space c1) in
        let x2 = space c2 in
          match x2 with INL c4 ->
             (match c1 with dataLang_MakeSpace k names -> INR
               (k,names,c4) | dataLang_Skip -> INL c4 | _10 -> INL
               (dataLang_Seq d1 c4)) | INR (k2,names2,c4) ->
             (match c1 with dataLang_Skip -> INR (k2,names2,c4) |
               dataLang_MakeSpace k1 names1 -> INR (k2,inter names1
               names2,c4) | dataLang_Move dest src ->
                  INR (k2,sptree_insert src one (sptree_delete dest
                    names2),
                       dataLang_Seq (dataLang_Move dest src) c4) |
                         dataLang_Assign dest op args NONE ->
                  INR (op_space_req op (LENGTH args) + k2,
                       list_insert args (sptree_delete dest names2),
                       dataLang_Seq (dataLang_Assign dest op args
                         NONE) c4) | _11 -> INL (dataLang_Seq d1
                         (pMakeSpace x2))))
        | (dataLang_If n c2 c3) ->
        INL (dataLang_If n (pMakeSpace (space c2)) (pMakeSpace
          (space c3)))
        | c -> INL c`];;

let space_pmatch = prove
 (`!c.
   space c =
     (match c with dataLang_MakeSpace k names -> INR
       (k,names,dataLang_Skip) | dataLang_Seq c1 c2 -> (
      let d1 = pMakeSpace (space c1) in
      let x2 = space c2 in
        match x2 with INL c4 ->
           (match c1 with dataLang_MakeSpace k names -> INR
             (k,names,c4) | dataLang_Skip -> INL c4 | _12 -> INL
             (dataLang_Seq d1 c4)) | INR (k2,names2,c4) ->
           (match c1 with dataLang_Skip -> INR (k2,names2,c4) |
             dataLang_MakeSpace k1 names1 -> INR (k2,inter names1
             names2,c4) | dataLang_Move dest src ->
                INR (k2,sptree_insert src one (sptree_delete dest
                  names2),
                     dataLang_Seq (dataLang_Move dest src) c4) |
                       dataLang_Assign dest op args NONE ->
                INR (op_space_req op (LENGTH args) + k2,
                     list_insert args (sptree_delete dest names2),
                     dataLang_Seq (dataLang_Assign dest op args NONE)
                       c4) | _13 -> INL (dataLang_Seq d1 (pMakeSpace
                       x2)))) | dataLang_If n c2 c3 ->
       INL (dataLang_If n (pMakeSpace (space c2)) (pMakeSpace
         (space c3))) | c -> INL c)`,
  CHEAT_TAC);;

let data_space_compile_def = new_definition
  `data_space_compile c = pMakeSpace (space c)`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
