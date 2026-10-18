(* ======================================================== *)
(*  clos_constantProof: ported from HOL4's
    compiler/backend/proofs/clos_constantProofScript.sml  *)
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

let conses_ok_def = cake_define
  `conses_ok aux <=>
     (!n. n < LENGTH aux ==> (?p. EL n (REVERSE aux) = (p,n))) /\
     (!n rs m r. MEM (Con n rs,r) aux /\ MEM m rs ==> m < r)`;;

(*
  EVAL “let c1 = ConstInt 1 in
        let c2 = ConstCons 2 [c1;c1] in
        let c3 = ConstCons 3 [c2;c2] in
        let c4 = ConstCons 4 [c3;c3] in
          to_parts c4”

*)

(* verification of the efficent version in clos_to_bvlTheory *)

let update_tag_def = cake_define
  `update_tag x =
      match x with
        (Con t ns:const_part) -> Con (clos_tag_shift t) ns
      | x -> x`;;

let good_hash_table_def = cake_define
  `good_hash_table m aux =
     (!k v. ALOOKUP aux k = SOME v <=>
           (?bucket. sptree_lookup (part_hash (update_tag k)) m =
             SOME bucket /\
                    ALOOKUP bucket (update_tag k) = SOME v))`;;

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
