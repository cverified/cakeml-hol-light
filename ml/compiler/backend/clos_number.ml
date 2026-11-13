(* ======================================================== *)
(*  clos_number: ported from HOL4's
    compiler/backend/clos_numberScript.sml
    A definition theory, with 3 definitions and 1 theorem.  Needed
    by backendProof.ml, backend_passes.ml, clos_numberProof.ml,
    clos_to_bvl.ml and clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  This simple compiler phase walks the program and gives each closure
  a unique numeric name.
*)

needs "compiler/backend/closLang.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_number"
  ["closLang"];;

(* add fresh code locations *)

let _ = size_thms "closLang_exp";;
let renumber_code_locs_def,renumber_code_locs_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`renumber_code_locs_list n [] = (n,[])`;
   `renumber_code_locs_list n (x :: xs) =
         (let (n,x) = renumber_code_locs n x in
         let (n,xs) = renumber_code_locs_list n xs in
         (n,x :: xs))`;
   `renumber_code_locs n (Var t v:closLang_exp) = (n,((Var t
  v:closLang_exp)))`;
   `renumber_code_locs n (If t x1 x2 x3:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
         let (n,x2) = renumber_code_locs n x2 in
         let (n,x3) = renumber_code_locs n x3 in
           (n,(If t x1 x2 x3:closLang_exp)))`;
   `renumber_code_locs n (Let t xs x2:closLang_exp) =
         (let (n,xs) = renumber_code_locs_list n xs in
         let (n,x2) = renumber_code_locs n x2 in
           (n,(Let t xs x2:closLang_exp)))`;
   `renumber_code_locs n (Raise t x1:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
           (n,(Raise t x1:closLang_exp)))`;
   `renumber_code_locs n (closLang_Tick t x1:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
           (n,(closLang_Tick t x1:closLang_exp)))`;
   `renumber_code_locs n (closLang_Op t op xs:closLang_exp) =
         (let (n,xs) = renumber_code_locs_list n xs in
           (n,(closLang_Op t op xs:closLang_exp)))`;
   `renumber_code_locs n (App t loc_opt x1 x2:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
         let (n,x2) = renumber_code_locs_list n x2 in
           (n,App t NONE x1 x2))`;
   `renumber_code_locs n (closLang_Fn t loc vs num_args x1) =
         (let (n,x1) = renumber_code_locs n x1 in
           (n + 2,closLang_Fn t (SOME n) vs num_args x1))`;
   `renumber_code_locs n (Letrec t loc vs fns x1:closLang_exp) =
         (let (m,fns') = renumber_code_locs_list n (MAP SND fns) in
         let (n,x1) = renumber_code_locs (m + 2 * LENGTH fns') x1 in
           (n,Letrec t (SOME m) vs (ZIP (MAP FST fns) fns') x1))`;
   `renumber_code_locs n (Handle t x1 x2:closLang_exp) =
         (let (n,x1) = renumber_code_locs n x1 in
         let (n,x2) = renumber_code_locs n x2 in
           (n,(Handle t x1 x2:closLang_exp)))`;
   `renumber_code_locs n (closLang_Call t ticks dest xs:closLang_exp) =
         (let (n,xs) = renumber_code_locs_list n xs in
           (n,closLang_Op t (closLang_IntOp closLang_Add) xs))
    // this case cannot occur`];;

(* HOL4 clos_numberScript.sml:66: ML code, not ported *)

let renumber_code_locs_length = prove
 (`(!x y. LENGTH (SND (renumber_code_locs_list x y)) = LENGTH y) /\
    (!(x:num) (y:closLang_exp). T)`,
  CHEAT_TAC);;

let clos_number_compile_inc_def = new_definition
  `clos_number_compile_inc n xs =
     // leave space in the naming for the daisy chaining of clos_to_bvl
     (let n1 = make_even (n + MAX (LENGTH xs) 1) in
     let (m,ys) = renumber_code_locs_list n1 xs in
       (
        // embed the name of the first free slot (n) in the code
        // no code will be generated for this pure Const expression
        m,closLang_Op backend_common_None (closLang_IntOp
          (closLang_Const (&n))) [] :: ys))`;;
hol4_overload "compile_inc" "clos_number_compile_inc";;

let ignore_table_def = new_definition
  `ignore_table f st (code,aux) = (let (st',code') = f st code in
  (st',(code',aux)))`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
