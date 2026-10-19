(* ======================================================== *)
(*  clos_constantProof: ported from HOL4's
    compiler/backend/proofs/clos_constantProofScript.sml
    A proof theory, with 13 definitions and 14 theorems.  Needed by
    clos_to_bvlProof.ml, lab_to_targetProof.ml and
    source_to_flatProof.ml.  *)
(* ======================================================== *)

(*
  Some functions that flatten a closLang/BVL/BVI/dataLang const tree
  into a sequence of operations that share common data.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;

(* HOL4 clos_constantProofScript.sml:11-23: code that the source has
   in a comment *)

(* naive implementation *)

let make_part_def = cake_define
  `make_part n p aux =
     (match ALOOKUP aux p with SOME k -> (n,k,aux) | NONE -> (n +
       1,n,(p,n) :: aux))`;;

let parts_def = cake_define
  `parts (ConstInt i) n aux = make_part n (Int i) aux /\
   parts (ConstStr s) n aux = make_part n (closLang_Str s) aux /\
   parts (ConstWord64 w) n aux = make_part n (W64 w) aux /\
   parts (ConstCons t cs) n aux =
     (let (n,rs,aux) = parts_list cs n aux in
        make_part n (Con t rs) aux) /\
   parts_list [] n aux = (n,[],aux) /\
   parts_list (c :: cs) n aux =
     (let (n,r,aux) = parts c n aux in
     let (n,rs,aux) = parts_list cs n aux in
       (n,r :: rs,aux))`;;

let to_parts_def = cake_define
  `to_parts (ConstInt i) = [Int i] /\
   to_parts (ConstStr s) = [closLang_Str s] /\
   to_parts (ConstWord64 w) = [W64 w] /\
   to_parts (ConstCons t cs) =
     (let (n,rs,aux) = parts_list cs 0 [] in
       REVERSE ((Con t rs) :: MAP FST aux))`;;

(* semantics *)

let build_part_def = cake_define_list
  [`build_part mem' (Int i:const_part) = ConstInt i`;
   `build_part mem' (closLang_Str s:const_part) = ConstStr s`;
   `build_part mem' (W64 w:const_part) = ConstWord64 w`;
   `build_part mem' (Con t ns:const_part) = ConstCons t (MAP mem'
  ns)`];;

let build_def = cake_define_list
  [`build mem' i [] = mem' (i - 1)`;
   `build mem' i (p :: rest) = build ((i =+ build_part mem' p)
  mem') (i + 1) rest`];;

let build_const_def = cake_define
  `build_const xs = build (\x. ConstInt (&0)) 0 xs`;;

(* proof *)

let build_map_def = cake_define_list
  [`build_map mem' i [] = mem'`;
   `build_map mem' i (p :: rest) = build_map ((i =+ build_part mem'
  p) mem') (i + 1) rest`];;

let build_mem_thm = cake_theorem "build_mem_thm"
  (fun () ->
    `!mem' i xs y.
       build mem' i (xs ++ [y]) =
         build (build_map mem' i xs) (i + LENGTH xs) [y]`)
  CHEAT_TAC;;

let parts_acc = cake_theorem "parts_acc"
  (fun () ->
    `(!c n aux m r res.
        parts c n aux = (m,r,res) ==> (?a. res = a ++ aux)) /\
     (!cs n aux m rs res.
        parts_list cs n aux = (m,rs,res) ==> (?a. res = a ++
          aux))`)
  CHEAT_TAC;;

let conses_ok_def = cake_define
  `conses_ok aux <=>
     (!n. n < LENGTH aux ==> (?p. EL n (REVERSE aux) = (p,n))) /\
     (!n rs m r. MEM (Con n rs,r) aux /\ MEM m rs ==> m < r)`;;

let IMP_conses_ok_CONS = cake_theorem "IMP_conses_ok_CONS"
  (fun () ->
    `(!n rs. x = Con n rs ==> EVERY (\m. m < LENGTH aux) rs) ==>
     conses_ok aux ==> conses_ok ((x,LENGTH aux) :: aux)`)
  CHEAT_TAC;;

let build_map_APPEND = cake_theorem "build_map_APPEND"
  (fun () ->
    `!xs ys m n.
       build_map m n (xs ++ ys) =
       build_map (build_map m n xs) (n + LENGTH xs) ys`)
  CHEAT_TAC;;

let LIST_REL_eq = cake_theorem "LIST_REL_eq[local]"
  (fun () ->
    `!l rs. LIST_REL (\c r. f r = c) l rs <=> l = MAP f rs`)
  CHEAT_TAC;;

let build_map_ignore = cake_theorem "build_map_ignore"
  (fun () ->
    `!xs m n k. k < n ==> build_map m n xs k = m k`)
  CHEAT_TAC;;

let ALOOKUP_conses_ok_IMP = cake_theorem "ALOOKUP_conses_ok_IMP"
  (fun () ->
    `ALOOKUP aux x = SOME r /\ conses_ok aux ==>
     (?(xs:(const_part#num) list) (ys:(const_part#num) list).
       MAP FST (REVERSE aux) = MAP FST (REVERSE xs) ++ [x] ++ MAP
         FST (REVERSE ys) /\
       LENGTH xs = r /\ r < LENGTH aux /\
       (!t ys y. x = Con t ys /\ MEM y ys ==> y < r))`)
  CHEAT_TAC;;

let parts_thm = cake_theorem "parts_thm"
  (fun () ->
    `(!c n aux m r res.
        parts c n aux = (m,r,res) /\
        ALL_DISTINCT (MAP SND aux) /\
        conses_ok aux /\ n = LENGTH aux /\
        EVERY (\(p,k). k < n) aux ==>
        build_map (\x. ConstInt (&0)) 0 (MAP FST (REVERSE res)) r =
          c /\
        n <= m /\ r < m /\
        ALL_DISTINCT (MAP SND res) /\
        conses_ok res /\ m = LENGTH res /\
        EVERY (\(p,k). k < m) res) /\
     (!cs n aux m rs res.
        parts_list cs n aux = (m,rs,res) /\
        ALL_DISTINCT (MAP SND aux) /\
        conses_ok aux /\ n = LENGTH aux /\
        EVERY (\(p,k). k < n) aux ==>
        LIST_REL (\c r. build_map (\x. ConstInt (&0)) 0 (MAP FST
          (REVERSE res)) r = c) cs rs /\
        n <= m /\ ALL_DISTINCT (MAP SND res) /\
        EVERY (\k. k < m) rs /\
        conses_ok res /\ m = LENGTH res /\
        EVERY (\(p,k). k < m) res)`)
  CHEAT_TAC;;

(*
  EVAL “let c1 = ConstInt 1 in
        let c2 = ConstCons 2 [c1;c1] in
        let c3 = ConstCons 3 [c2;c2] in
        let c4 = ConstCons 4 [c3;c3] in
          to_parts c4”

*)

let build_const_to_parts = cake_theorem "build_const_to_parts"
  (fun () ->
    `!c. build_const (to_parts c) = c`)
  CHEAT_TAC;;

(* verification of the efficent version in clos_to_bvlTheory *)

let update_tag_def = cake_define
  `update_tag x =
      match x with
        (Con t ns:const_part) -> Con (clos_tag_shift t) ns
      | x -> x`;;

let update_tag_11 = cake_theorem "update_tag_11"
  (fun () ->
    `update_tag x = update_tag y <=> x = y`)
  CHEAT_TAC;;

let good_hash_table_def = cake_define
  `good_hash_table m aux =
     (!k v. ALOOKUP aux k = SOME v <=>
           (?bucket. sptree_lookup (part_hash (update_tag k)) m =
             SOME bucket /\
                    ALOOKUP bucket (update_tag k) = SOME v))`;;

let add_part_thm = cake_theorem "add_part_thm"
  (fun () ->
    `add_part n (update_tag x) m (MAP (update_tag o FST) aux) =
  (n1,rs,m1,acc1) /\
     make_part n x aux = (n2,rs1,aux1) /\
     good_hash_table m aux ==>
     n1 = n2 /\ rs = rs1 /\ MAP (update_tag o FST) aux1 = acc1 /\
       good_hash_table m1 aux1`)
  CHEAT_TAC;;

let add_parts_thm = cake_theorem "add_parts_thm"
  (fun () ->
    `(!l n m acc n1 m1 rs m1 acc1 aux n2 rs1 aux1.
       add_parts l n m acc = (n1,rs,m1,acc1) /\
       parts l n aux = (n2,rs1,aux1) /\
       MAP (update_tag o FST) aux = acc /\ good_hash_table m aux
         ==>
       n1 = n2 /\ rs = rs1 /\ MAP (update_tag o FST) aux1 = acc1 /\
         good_hash_table m1 aux1) /\
     (!l n m acc n1 m1 rs m1 acc1 aux n2 rs1 aux1.
       add_parts_list l n m acc = (n1,rs,m1,acc1) /\
       parts_list l n aux = (n2,rs1,aux1) /\
       MAP (update_tag o FST) aux = acc /\ good_hash_table m aux
         ==>
       n1 = n2 /\ rs = rs1 /\ MAP (update_tag o FST) aux1 = acc1
         /\ good_hash_table m1 aux1)`)
  CHEAT_TAC;;

let compile_const_thm = cake_theorem "compile_const_thm"
  (fun () ->
    `(!i. ~(c = ConstInt i)) /\ (!t. ~(c = ConstCons t [])) ==>
     compile_const c = closLang_BlockOp (closLang_Build (MAP
       update_tag (to_parts c)))`)
  CHEAT_TAC;;

(* connection to closSem *)

let build_part'_def = cake_define
  `build_part' mem' (Int i:const_part) = closSem_Number i /\
   build_part' mem' (closLang_Str s) = closSem_ByteVector (MAP (n2w o
     ORD) (explode s)) /\
   build_part' mem' (W64 w) = Word64 w /\
   build_part' mem' (Con t ns) = closSem_Block t (MAP mem' ns)`;;

let build'_def = cake_define_list
  [`build' mem' i [] = mem' (i - 1)`;
   `build' mem' i (p :: rest) = build' ((i =+ build_part' mem' p)
  mem') (i + 1) rest`];;

let build_const'_def = cake_define
  `build_const' xs = build' (\x. closSem_Number (&0)) 0 xs`;;

let make_const_thm = cake_theorem "make_const_thm"
  (fun () ->
    `make_const c = build_const' (to_parts c)`)
  CHEAT_TAC;;
