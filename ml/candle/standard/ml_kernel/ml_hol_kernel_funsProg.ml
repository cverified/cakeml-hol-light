(* ======================================================== *)
(*  ml_hol_kernel_funsProg: ported from HOL4's
    candle/standard/ml_kernel/ml_hol_kernel_funsProgScript.sml
    A definition theory, with 16 definitions and 10 theorems.
    Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  Apply the monadic translator to the Candle kernel to generate the
  deeply embedded CakeML code for the kernel. As a side effect, the
  monadic translator proves certificate theorems that state a formal
  connection between the generated code and the input HOL functions.
*)

needs "basis/basisProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/standard/ml_kernel/runtime_check.ml";;
(* Adds runtime type checks *)
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelPmatch.ml";;
needs "candle/standard/syntax/holAxiomsSyntax.ml";;
(* for setting up the context *)
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "characteristic/cf.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/patternMatches.ml";;
needs "lib/set_sep.ml";;
needs "lib/ternaryComparisons.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/ml_pmatch.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_hol_kernel_funsProg"
  ["ast"; "basisProg"; "cf"; "cfHeapsBase"; "cfStore"; "cfTactics";
   "evaluate"; "holAxiomsSyntax"; "holKernel"; "holKernelPmatch";
   "ml_monadBase"; "ml_monadStore"; "ml_monad_translator"; "ml_pmatch";
   "ml_prog"; "ml_translator"; "runtime_check"; "semanticPrimitives"];;

(* HOL4 ml_hol_kernel_funsProgScript.sml:25: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:27: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:31: the type abbreviation state,
   which the port expands *)

(* construct type refinement invariants *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:35-37: ML code, not ported *)

(* check ``:type`` is known to be an EqualityType *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:40: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:42-44: ML code, not ported *)

(* add an abbreviation mapping hol_type to type for HOL Light *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:48-50: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:52: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:54: ML code, not ported *)

(* Initialize the translation *)

let init_type_constants_def = new_definition
  `init_type_constants = [((implode "bool"),0); ((implode "fun"),(2:num))]`;;

let init_term_constants_def = new_definition
  `init_term_constants = [((implode "="),
     holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A");
        holSyntax_Tyapp (implode "fun")
          [holSyntax_Tyvar (implode "A");
           holSyntax_Tyapp (implode "bool") []]])]`;;

let init_axioms_def = new_definition
  `init_axioms = ([]:thm list)`;;

(* [local] *)
let init_axioms_alt = prove
 (`init_axioms = match [holKernel_Sequent [] (holSyntax_Var (implode "")
  (holSyntax_Tyvar (implode "")))] with [] -> []
                 | (CONS _ xs) -> xs`,
  CHEAT_TAC);;

let init_context_def = new_definition
  `init_context = (rhs (concl (?_init_ctxt_def holSyntaxTheory)))`;;

(* HOL4 ml_hol_kernel_funsProgScript.sml:87-94: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:96-97: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:99-101: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:103-105: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:107-117: ML code, not ported *)

(* Translate type-checking code from checkTheory *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:121-125: ML code, not ported *)

(**************************************************************************************************)
(**************************************************************************************************)
(* --- perform translation --- *)

(* TODO: want builtin support for these *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:132-145: code that the source has
   in a comment *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:147-149: ML code, not ported *)

(* -- *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:152-156: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:158: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:160-162: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:164: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:166: ML code, not ported *)

let call_type_subst_def = new_definition
  `call_type_subst i ty = holKernel_type_subst i ty`;;
add_simp call_type_subst_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:171-173: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:175: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:177: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:179: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:181-182: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:184: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:186: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:188-192: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:194: ML code, not ported *)

let call_frees_def = new_definition
  `call_frees tm = frees tm`;;
add_simp call_frees_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:199-201: ML code, not ported *)

let call_freesin_def = new_definition
  `call_freesin acc tm = freesin acc tm`;;
add_simp call_freesin_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:206-208: ML code, not ported *)

let call_vfree_in_def = new_definition
  `call_vfree_in v tm = vfree_in v tm`;;
add_simp call_vfree_in_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:213-215: ML code, not ported *)

let call_tyvars_def = new_definition
  `call_tyvars x = holKernel_tyvars x`;;
add_simp call_tyvars_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:220-222: ML code, not ported *)

let call_type_vars_in_term_def = new_definition
  `call_type_vars_in_term tm = type_vars_in_term tm`;;
add_simp call_type_vars_in_term_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:227-229: ML code, not ported *)

let call_variant_def = new_definition
  `call_variant avoid v = variant avoid v`;;
add_simp call_variant_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:234-236: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:238: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:240: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:242-248: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:250: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:252: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:254: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:256-258: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:260: ML code, not ported *)

let type_compare_def,type_compare_ind = define_guess
  `(type_compare t1 t2 =
         match (t1,t2) with (holSyntax_Tyvar x1,holSyntax_Tyvar x2) ->
             mlstring_compare x1 x2
         | (holSyntax_Tyvar x1,holSyntax_Tyapp _ _) -> LESS
         | (holSyntax_Tyapp x1 a1,holSyntax_Tyvar _) -> GREATER
         | (holSyntax_Tyapp x1 a1,holSyntax_Tyapp x2 a2) ->
             (match mlstring_compare x1 x2 with (\ty. holSyntax_Const
                 (implode "=") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                 ty (ast_Fun ty (holSyntax_Tyapp (implode "bool") [])))) ->
                 type_list_compare a1 a2
             | other -> other)) /\
   (type_list_compare ts1 ts2 =
         match (ts1,ts2) with ([],[]) -> (\ty. holSyntax_Const (implode
             "=") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (ast_Fun
             ty (holSyntax_Tyapp (implode "bool") []))))
         | ([],CONS t2 ts2) -> LESS
         | (CONS t1 ts1,[]) -> GREATER
         | (CONS t1 ts1,CONS t2 ts2) ->
             (match type_compare t1 t2 with (\ty. holSyntax_Const (implode
                 "=") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
                 (ast_Fun ty (holSyntax_Tyapp (implode "bool") [])))) ->
                 type_list_compare ts1 ts2
              | other -> other))`;;

(* HOL4 ml_hol_kernel_funsProgScript.sml:283-293: a theorem that HOL4 states
   as the value of an ML expression: type_cmp_thm *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:295: ML code, not ported *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:296-298: a theorem that HOL4 states
   as the value of an ML expression: type_cmp_ind *)

let term_compare_def,term_compare_ind = define_guess
  `term_compare t1 t2 =
      match (t1,t2) with
        (holSyntax_Var x1 ty1,holSyntax_Var x2 ty2) ->
          (match mlstring_compare x1 x2 with
             LESS -> LESS
           | (\ty. holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) ty (ast_Fun ty (holSyntax_Tyapp (implode
             "bool") [])))) -> type_cmp ty1 ty2
           | GREATER -> GREATER)
      | (holSyntax_Var x1 ty1,holSyntax_Const v52 v53) -> LESS
      | (holSyntax_Var x1 ty1,holSyntax_Comb v54 v55) -> LESS
      | (holSyntax_Var x1 ty1,holSyntax_Abs v56 v57) -> LESS
      | (holSyntax_Const x1' ty1',holSyntax_Var v66 v67) -> GREATER
      | (holSyntax_Const x1' ty1',holSyntax_Const x2' ty2') ->
          (match mlstring_compare x1' x2' with
             LESS -> LESS
           | (\ty. holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) ty (ast_Fun ty (holSyntax_Tyapp (implode
             "bool") [])))) -> type_cmp ty1' ty2'
           | GREATER -> GREATER)
      | (holSyntax_Const x1' ty1',holSyntax_Comb v70 v71) -> LESS
      | (holSyntax_Const x1' ty1',holSyntax_Abs v72 v73) -> LESS
      | (holSyntax_Comb s1 t1,holSyntax_Var v82 v83) -> GREATER
      | (holSyntax_Comb s1 t1,holSyntax_Const v84 v85) -> GREATER
      | (holSyntax_Comb s1 t1,holSyntax_Comb s2 t2) ->
          (match term_compare s1 s2 with
             LESS -> LESS
           | (\ty. holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) ty (ast_Fun ty (holSyntax_Tyapp (implode
             "bool") [])))) -> term_compare t1 t2
           | GREATER -> GREATER)
      | (holSyntax_Comb s1 t1,holSyntax_Abs v88 v89) -> LESS
      | (holSyntax_Abs s1' t1',holSyntax_Var v98 v99) -> GREATER
      | (holSyntax_Abs s1' t1',holSyntax_Const v100 v101) -> GREATER
      | (holSyntax_Abs s1' t1',holSyntax_Comb v102 v103) -> GREATER
      | (holSyntax_Abs s1' t1',holSyntax_Abs s2' t2') ->
          (match term_compare s1' s2' with
            LESS -> LESS
          | (\ty. holSyntax_Const (implode "=") ((\s t. holSyntax_Tyapp
            (implode "fun") [s; t]) ty (ast_Fun ty (holSyntax_Tyapp (implode
            "bool") [])))) -> term_compare t1' t2'
          | GREATER -> GREATER)`;;

(* term_cmp_thm[local] *)
let ml_hol_kernel_funsProg_term_cmp_thm = prove
 (`term_cmp = term_compare`,
  CHEAT_TAC);;

(* HOL4 ml_hol_kernel_funsProgScript.sml:349: ML code, not ported *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:350-352: a theorem that HOL4 states
   as the value of an ML expression: term_cmp_ind *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:354-359: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:361-364: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:366: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:368-376: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:378-380: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:382: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:384-387: ML code, not ported *)

let call_type_of_def = new_definition
  `call_type_of tm = type_of tm`;;
add_simp call_type_of_def;;
(* HOL4 ml_hol_kernel_funsProgScript.sml:392-394: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:396-397: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:399: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:401-404: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:406: ML code, not ported *)

let check_for_dups_def,check_for_dups_ind = define_guess
  `check_for_dups ls cs =
     match ls with [] -> st_ex_return one
     | (CONS x xs) -> if MEMBER x cs then
                    raise_Failure
                       (strcat (strcat (implode "add_constants: ") x)
                        (implode
                          " appears twice or has already been declared"))
                  else check_for_dups xs (CONS x cs)`;;

let add_constants_alt = prove
 (`add_constants ls =
        st_ex_bind get_the_term_constants (\cs.
        st_ex_bind (check_for_dups (MAP FST ls) (MAP FST cs)) (\_.
          (set_the_term_constants (APPEND ls cs))))`,
  CHEAT_TAC);;

(* HOL4 ml_hol_kernel_funsProgScript.sml:437-438: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:440: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:442: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:444: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:446: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:448: ML code, not ported *)

let call_new_type_def = new_definition
  `call_new_type ((n:mlstring),(arity:int)) =
     if (&0) <= arity then new_type (n,num_of_int (abs arity))
     else raise_Failure (implode "negative arity")`;;
add_simp call_new_type_def;;

(* HOL4 ml_hol_kernel_funsProgScript.sml:456-457: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:459: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:461-462: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:464-466: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:468-469: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:471: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:473: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:475: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:477: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:479: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:481-483: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:485: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:487-490: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:492-497: a theorem that HOL4 states
   as the value of an ML expression: MK_COMB_lemma *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:499: ML code, not ported *)
(* workaround contamination of translator's guts by DoubleProg.abs *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:501: the overload abs_v, which the
   port expands *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:502: a theorem that HOL4 states as
   the value of an ML expression: abs_v_def *)
(* HOL4 ml_hol_kernel_funsProgScript.sml:503: a theorem that HOL4 states as
   the value of an ML expression: abs_v_thm *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:505: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:507-510: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:512-515: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:517: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:519: ML code, not ported *)

(* HOL4 ml_hol_kernel_funsProgScript.sml:521: ML code, not ported *)

(* [local] *)
let axioms_eq = prove
 (`axioms u = 1_CASE u get_the_axioms`,
  CHEAT_TAC);;

(* [local] *)
let types_eq = prove
 (`types u = 1_CASE u get_the_type_constants`,
  CHEAT_TAC);;

(* [local] *)
let constants_eq = prove
 (`constants u = 1_CASE u get_the_term_constants`,
  CHEAT_TAC);;

(* HOL4 ml_hol_kernel_funsProgScript.sml:541-543: ML code, not ported *)

(* The kernel module is closed in subsequent script files:
   ml_hol_kernelProgScript.sml and candle_kernelProgScript.sml *)

(* and the interface *)
let _ = unhide_overloads ();;
