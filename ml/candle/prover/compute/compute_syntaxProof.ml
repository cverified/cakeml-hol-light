(* ======================================================== *)
(*  compute_syntaxProof: ported from HOL4's
    candle/prover/compute/compute_syntaxProofScript.sml
    A proof theory about compute_syntax.ml, with 5 definitions and
    139 theorems.  Needed by computeProof.ml, compute_evalProof.ml
    and compute_execProof.ml.  *)
(* ======================================================== *)

(*
   Proofs related to term embeddings for the Candle compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compute_syntaxProof"
  ["compute_syntax"; "holKernel"; "holKernelProof"; "holSyntax";
   "holSyntaxExtra"; "holSyntaxLib"];;

let _ = do_list hide_constant ["Bool"; "FALSE"; "TRUE"];;

(* HOL4 compute_syntaxProofScript.sml:14-15: ML code, not ported *)

(* -------------------------------------------------------------------------
 * Support
 * ------------------------------------------------------------------------- *)

let trans_equation_simple = prove
 (`(|-) (thy,[]) ((===) a b) /\ (|-) (thy,[]) ((===) b c) ==> (|-) (thy,[])
  ((===) a c)`,
  CHEAT_TAC);;

(* HOL4 compute_syntaxProofScript.sml:31-32: a theorem that HOL4 states as
   the value of an ML expression: MK_COMB_simple *)

let replaceL1 = prove
 (`(|-) (thy,[]) ((===) x y) /\ (|-) (thy,[]) ((===) (holSyntax_Comb
  (holSyntax_Comb f x) r) z) ==> (|-) (thy,[]) ((===) (holSyntax_Comb
  (holSyntax_Comb f y) r) z)`,
  CHEAT_TAC);;

let replaceL2 = prove
 (`(|-) (thy,[]) ((===) x y) /\ (|-) (thy,[]) ((===) (holSyntax_Comb f x) z)
  ==> (|-) (thy,[]) ((===) (holSyntax_Comb f y) z)`,
  CHEAT_TAC);;

let replaceL3 = prove
 (`(|-) (thy,[]) ((===) x y) /\ (|-) (thy,[]) ((===) (holSyntax_Comb
  (holSyntax_Comb (holSyntax_Comb f x) s) t) z) ==> (|-) (thy,[]) ((===)
  (holSyntax_Comb (holSyntax_Comb (holSyntax_Comb f y) s) t) z)`,
  CHEAT_TAC);;

let replaceL_eq1 = prove
 (`(|-) (thy,[]) ((===) x x') /\ (|-) (thy,[]) ((===) ((===) x y) r) ==> (|-)
  (thy,[]) ((===) ((===) x' y) r)`,
  CHEAT_TAC);;

let replaceL_eq2 = prove
 (`(|-) (thy,[]) ((===) x x') /\ (|-) (thy,[]) ((===) ((===) y x) r) ==> (|-)
  (thy,[]) ((===) ((===) y x') r)`,
  CHEAT_TAC);;

let replaceR1 = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL replaceL1));;

let replaceR2 = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL replaceL2));;

let replaceR3 = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL replaceL3));;

let replaceR_eq1 =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL replaceL_eq1));;

let replaceR_eq2 =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL replaceL_eq2));;

let DEDUCT_ANTISYM_simple = prove
 (`(|-) (thy,[]) a /\ (|-) (thy,[]) b ==> (|-) (thy,[]) ((===) a b)`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * Booleans
 * ------------------------------------------------------------------------- *)

let bool_thy_ok_def = new_definition
  `bool_thy_ok thy <=>
     theory_ok thy /\ (|-) (
      // COND
      thy,[]) ((===) ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "bool") []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (ast_Fun
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
        "num") []))))) t) t1) t2) (holSyntax_Const (implode "T")
        (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") []))) /\ (|-) (thy,[]) ((===) ((\t
        t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") []))))) t) t1)
        t2) (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool")
        [])) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num")
        [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num")
        []))) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num")
        []))) /\ (|-) (thy,[]) ((===) ((\t t1 t2. holSyntax_Comb
        (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "COND")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "bool") []) (ast_Fun (holSyntax_Tyapp (implode "bool") [])
        (ast_Fun (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
        (implode "bool") []))))) t) t1) t2) (holSyntax_Const (implode "T")
        (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "x")
        (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "y")
        (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var (implode "x")
        (holSyntax_Tyapp (implode "bool") []))) /\ (|-) (thy,[]) ((===) ((\t
        t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
        (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp
        (implode "bool") []) (holSyntax_Tyapp (implode "bool") []))))) t)
        t1) t2) (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode
        "bool") [])) (holSyntax_Var (implode "x") (holSyntax_Tyapp (implode
        "bool") [])) (holSyntax_Var (implode "y") (holSyntax_Tyapp (implode
        "bool") []))) (holSyntax_Var (implode "y") (holSyntax_Tyapp (implode
        "bool") [])))`;;

let bool_thy_ok_terms_ok = prove
 (`bool_thy_ok thy ==>
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
       (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
       "num") []) (holSyntax_Tyapp (implode "num") []))))) /\
     holSyntax_term_ok (FST thy) (holSyntax_Const (implode "COND") ((\s t.
       holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
       "bool") []) (ast_Fun (holSyntax_Tyapp (implode "bool") []) (ast_Fun
       (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode
       "bool") [])))))`,
  CHEAT_TAC);;

let bool_thy_ok_theory_ok = prove
 (`bool_thy_ok thy ==> theory_ok thy`,
  CHEAT_TAC);;
add_simp bool_thy_ok_theory_ok;;

(* -------------------------------------------------------------------------
 * Natural numbers
 * ------------------------------------------------------------------------- *)

(* All the necessary constants defined with the right types and
 * with the right defining equations (and some lemmas).
 *)

let numeral_thy_ok_def = new_definition
  `numeral_thy_ok thy <=>
     bool_thy_ok thy /\ (|-) (
      // NUMERAL
      thy,[]) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
        []))) tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num")
        []))) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num")
        []))) /\ (|-) (
      // BIT0, BIT1
      thy,[]) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "BIT0")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") [])))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "n") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (thy,[]) ((===) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "BIT1") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") []))) tm) ((\t1 t2. holSyntax_Comb
        (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
        [])))) t1) t2) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
        "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
        "num") []))))) /\ (|-) (
      // ADD
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp (implode "fun")
        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))) /\ (|-) (thy,[])
        ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "+") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp (implode "fun")
        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") [])))))
        /\ (|-) (
      // SUB
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "-") ((\s t. holSyntax_Tyapp (implode "fun")
        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (thy,[])
        ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "-") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) /\ (|-) (thy,[])
        ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "-") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") []))) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp
        (implode "num") [])))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "-") ((\s t. holSyntax_Tyapp (implode "fun")
        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") []))))
        /\ (|-) (
      // MUL
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "*") ((\s t. holSyntax_Tyapp (implode "fun")
        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (thy,[])
        ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "*") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))) ((\t1 t2. holSyntax_Comb
        (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
        [])))) t1) t2) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
        "num") [])) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "*") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") [])))))
        /\ (|-) (
      // DIV, MOD
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "DIV") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
        [])))) t1) t2) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
        "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
        "num") [])))
                 ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
                   []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((===) (holSyntax_Var
                   (implode "n") (holSyntax_Tyapp (implode "num") [])) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))
                       ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                         (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s
                         t. holSyntax_Tyapp (implode "fun") [s; t])
                         (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "num") []))))) t) t1) t2) ((\t1 t2.
                         holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                         (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
                         [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "bool") [])))) t1) t2) (holSyntax_Var
                         (implode "m") (holSyntax_Tyapp (implode "num") []))
                         (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                         "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const
                         (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
                         "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                         (holSyntax_Tyapp (implode "num") []))) tm)
                         (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                         (implode "num") [])))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "SUC") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) ((\t1 t2. holSyntax_Comb
                                (holSyntax_Comb (holSyntax_Const (implode
                                "DIV") ((\s t. holSyntax_Tyapp (implode "fun")
                                [s; t]) (holSyntax_Tyapp (implode "num") [])
                                (ast_Fun (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                                ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                                (holSyntax_Const (implode "-") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") []) (ast_Fun
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                                (holSyntax_Var (implode "m") (holSyntax_Tyapp
                                (implode "num") [])) (holSyntax_Var (implode
                                "n") (holSyntax_Tyapp (implode "num") [])))
                                (holSyntax_Var (implode "n") (holSyntax_Tyapp
                                (implode "num") []))))))) /\ (|-) (thy,[])
                                ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                                (holSyntax_Const (implode "MOD") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") []) (ast_Fun
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                                (holSyntax_Var (implode "m") (holSyntax_Tyapp
                                (implode "num") [])) (holSyntax_Var (implode
                                "n") (holSyntax_Tyapp (implode "num") [])))
                 ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
                   []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((===) (holSyntax_Var
                   (implode "n") (holSyntax_Tyapp (implode "num") [])) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))) (holSyntax_Var (implode "m")
                   (holSyntax_Tyapp (implode "num") []))
                       ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                         (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s
                         t. holSyntax_Tyapp (implode "fun") [s; t])
                         (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "num") []))))) t) t1) t2) ((\t1 t2.
                         holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                         (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
                         [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "bool") [])))) t1) t2) (holSyntax_Var
                         (implode "m") (holSyntax_Tyapp (implode "num") []))
                         (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                         "num") []))) (holSyntax_Var (implode "m")
                         (holSyntax_Tyapp (implode "num") []))
                              ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                                (holSyntax_Const (implode "MOD") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") []) (ast_Fun
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                                ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                                (holSyntax_Const (implode "-") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") []) (ast_Fun
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                                (holSyntax_Var (implode "m") (holSyntax_Tyapp
                                (implode "num") [])) (holSyntax_Var (implode
                                "n") (holSyntax_Tyapp (implode "num") [])))
                                (holSyntax_Var (implode "n") (holSyntax_Tyapp
                                (implode "num") [])))))) /\ (|-) (
      // LESS
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "bool") [])))) t1) t2)
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Const
        (implode "F") (holSyntax_Tyapp (implode "bool") []))) /\ (|-) (thy,[])
        ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "<") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "bool") [])))) t1) t2) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Const (implode "T")
        (holSyntax_Tyapp (implode "bool") []))) /\ (|-) (thy,[]) ((===) ((\t1
        t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "<") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "bool") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp
        (implode "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") []))))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "<")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "bool") [])))) t1) t2) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (
      // EQ
      thy,[]) ((===) ((===) ((\tm. holSyntax_Comb (holSyntax_Const
        (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
        "num") []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
        (implode "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const
        (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
        "num") []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
        (implode "num") [])))) (holSyntax_Const (implode "T")
        (holSyntax_Tyapp (implode "bool") []))) /\ (|-) (thy,[]) ((===)
        ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
        (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num")
        []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
        (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool")
        []))) /\ (|-) (thy,[]) ((===) ((===) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") []))) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const (implode
        "_0") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Const
        (implode "F") (holSyntax_Tyapp (implode "bool") []))) /\ (|-)
        (thy,[]) ((===) ((===) ((\tm. holSyntax_Comb (holSyntax_Const
        (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
        "num") []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp
        (implode "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const
        (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
        "num") []))) tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp
        (implode "num") [])))) ((===) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))))`;;

let numeral_thy_ok_theory_ok = prove
 (`numeral_thy_ok thy ==> theory_ok thy`,
  CHEAT_TAC);;
add_simp numeral_thy_ok_theory_ok;;

let numeral_thy_ok_bool_thy_ok = prove
 (`numeral_thy_ok thy ==> bool_thy_ok thy`,
  CHEAT_TAC);;
add_simp numeral_thy_ok_bool_thy_ok;;

let numeral_thy_ok_terms_ok = prove
 (`numeral_thy_ok thy ==>
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
       (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
       "num") []) (holSyntax_Tyapp (implode "num") []))))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
       (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp (implode
       "bool") []) (holSyntax_Tyapp (implode "bool") []))))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "-") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "*") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "DIV") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "MOD") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "bool") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
       "num") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "BIT0") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
       (implode "num") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "BIT1") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
       (implode "num") []))) /\
     holSyntax_term_ok (FST thy) (holSyntax_Const (implode "NUMERAL") ((\s t.
       holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
       "num") []) (holSyntax_Tyapp (implode "num") [])))`,
  CHEAT_TAC);;

let term_ok_NUMERAL = prove
 (`numeral_thy_ok thy ==>
     holSyntax_term_ok (FST thy) ((\tm. holSyntax_Comb (holSyntax_Const
       (implode
       "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
       (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
       []))) tm) N) = (holSyntax_term_ok (FST thy) N /\ has_type N
         (holSyntax_Tyapp (implode "num")
       []))`,
  CHEAT_TAC);;
add_simp term_ok_NUMERAL;;

let NUMERAL_has_type = prove
 (`has_type ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s
  t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (holSyntax_Tyapp (implode "num") []))) tm) N) (holSyntax_Tyapp (implode
  "num") []) <=> has_type N (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp NUMERAL_has_type;;

let has_type_0 = prove
 (`has_type (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num")
  [])) (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp has_type_0;;

let term_ok_SUC = prove
 (`numeral_thy_ok thy ==>
     holSyntax_term_ok (FST thy) ((\tm. holSyntax_Comb (holSyntax_Const
       (implode
       "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
       (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
       []))) tm) N) = (holSyntax_term_ok (FST thy) N /\ has_type N
         (holSyntax_Tyapp (implode "num")
       []))`,
  CHEAT_TAC);;
add_simp term_ok_SUC;;

let SUC_has_type = prove
 (`has_type ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (holSyntax_Tyapp (implode "num") []))) tm) N) (holSyntax_Tyapp (implode
  "num") []) <=> has_type N (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp SUC_has_type;;

(* The numeral_thy_ok theorems with object variables replaced with meta
   variables.
 *)

let NUMERAL_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     n /\ has_type n (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s
     t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") []))) tm) n) n)`,
  CHEAT_TAC);;

let BIT0_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     n /\ has_type n (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "BIT0") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) n) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") [])))) t1) t2) n n))`,
  CHEAT_TAC);;

let BIT1_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     n /\ has_type n (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "BIT1") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) n) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
     "num") []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) n
     n)))`,
  CHEAT_TAC);;

let ADD_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") []))) n) n) /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm) m) n)
     ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     [])))) t1) t2) m n)))`,
  CHEAT_TAC);;

let SUB_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "-") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") []))) n) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") [])))) /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "-") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     [])))) t1) t2) m ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") [])))) m) /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "-") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm) m) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
     (holSyntax_Tyapp (implode "num") []))) tm) n)) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "-") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     [])))) t1) t2) m n))`,
  CHEAT_TAC);;

let MUL_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "*") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") []))) n) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") [])))) /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "*") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm) m) n)
     ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
     (holSyntax_Tyapp (implode "num") [])))) t1) t2) n ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "*") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") [])))) t1) t2) m n)))`,
  CHEAT_TAC);;

let LESS_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "<") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "bool") [])))) t1) t2) m ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") [])))) (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode
     "bool") []))) /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "<") ((\s t. holSyntax_Tyapp
     (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "bool")
     [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
     "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s
     t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") []))) tm) n))
     (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") [])))
     /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "bool") [])))) t1) t2)
     ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) m) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
     "num") []))) tm) n)) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "bool") [])))) t1) t2) m
     n))`,
  CHEAT_TAC);;

let EQ_eqn1 = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) ((===) ((\tm. holSyntax_Comb
  (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
  (implode "num") []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
  (implode "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode
  "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
  (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
  (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num") []))))
  (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") [])))`,
  CHEAT_TAC);;

let EQ_eqn2 = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     n /\ has_type n (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
     (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num") [])))
     ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) n)) (holSyntax_Const
     (implode "F") (holSyntax_Tyapp (implode "bool") [])))`,
  CHEAT_TAC);;

let EQ_eqn3 = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ has_type m (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm) m) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const (implode
     "_0") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Const (implode
     "F") (holSyntax_Tyapp (implode "bool") [])))`,
  CHEAT_TAC);;

let EQ_eqn4 = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((===)
     ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) m) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
     "num") []))) tm) n)) ((===) m n))`,
  CHEAT_TAC);;

let COND_eqn = prove
 (`bool_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "COND") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
     (holSyntax_Tyapp (implode "num") []))))) t) t1) t2) (holSyntax_Const
     (implode "T") (holSyntax_Tyapp (implode "bool") [])) m n) m) /\ (|-)
     (thy,[]) ((===) ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "bool") []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (ast_Fun
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
     []))))) t) t1) t2) (holSyntax_Const (implode "F") (holSyntax_Tyapp
     (implode "bool") [])) m n) n)`,
  CHEAT_TAC);;

let IF_eqn = prove
 (`bool_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     x /\ holSyntax_term_ok (FST thy)
     y /\ has_type x (holSyntax_Tyapp (implode "bool") []) /\ has_type y
     (holSyntax_Tyapp (implode "bool") []) ==> (|-) (thy,[]) ((===) ((\t t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "COND") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp (implode
     "bool") []) (ast_Fun (holSyntax_Tyapp (implode "bool") [])
     (holSyntax_Tyapp (implode "bool") []))))) t) t1) t2) (holSyntax_Const
     (implode "T") (holSyntax_Tyapp (implode "bool") [])) x y) x) /\ (|-)
     (thy,[]) ((===) ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "bool") []) (ast_Fun (holSyntax_Tyapp (implode "bool") []) (ast_Fun
     (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode "bool")
     []))))) t) t1) t2) (holSyntax_Const (implode "F") (holSyntax_Tyapp
     (implode "bool") [])) x y) y)`,
  CHEAT_TAC);;

let DIV_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy) m
     /\ holSyntax_term_ok (FST thy) n
     /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "DIV") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") [])))) t1) t2) m n)
                 ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
                   []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((===) n ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))
                       ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                         (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s
                         t. holSyntax_Tyapp (implode "fun") [s; t])
                         (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "num") []))))) t) t1) t2) ((\t1 t2.
                         holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                         (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
                         [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "bool") [])))) t1) t2) m n) ((\tm.
                         holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                         ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "num") []))) tm) (holSyntax_Const (implode
                         "_0") (holSyntax_Tyapp (implode "num") [])))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "SUC") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) ((\t1 t2. holSyntax_Comb
                                (holSyntax_Comb (holSyntax_Const (implode
                                "DIV") ((\s t. holSyntax_Tyapp (implode
                                "fun") [s; t]) (holSyntax_Tyapp (implode
                                "num") []) (ast_Fun (holSyntax_Tyapp (implode
                                "num") []) (holSyntax_Tyapp (implode "num")
                                [])))) t1) t2) ((\t1 t2. holSyntax_Comb
                                (holSyntax_Comb (holSyntax_Const (implode
                                "-") ((\s t. holSyntax_Tyapp (implode "fun")
                                [s; t]) (holSyntax_Tyapp (implode "num") [])
                                (ast_Fun (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1)
                                t2) m n) n)))))`,
  CHEAT_TAC);;

let MOD_eqn = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy) m
     /\ holSyntax_term_ok (FST thy) n
     /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "MOD") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") [])))) t1) t2) m n)
                 ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
                   []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((===) n ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))) m
                       ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                         (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s
                         t. holSyntax_Tyapp (implode "fun") [s; t])
                         (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "num") []))))) t) t1) t2) ((\t1 t2.
                         holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                         (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
                         [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                         (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                         (implode "bool") [])))) t1) t2) m n) m
                              ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                                (holSyntax_Const (implode "MOD") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") []) (ast_Fun
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1)
                                t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                                (holSyntax_Const (implode "-") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") []) (ast_Fun
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") [])))) t1)
                                t2) m n) n))))`,
  CHEAT_TAC);;

(* TODO Move *)
let COND_has_type = prove
 (`has_type ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
  (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp
  (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
  (holSyntax_Tyapp (implode "num") []))))) t) t1) t2) p m n) (holSyntax_Tyapp
  (implode "num") []) <=> has_type p (holSyntax_Tyapp (implode "bool") [])
  /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
  (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp COND_has_type;;

(* TODO Move *)
let LESS_has_type = prove
 (`has_type ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
  (implode "<") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
  "num") []) (holSyntax_Tyapp (implode "bool") [])))) t1) t2) m n)
  (holSyntax_Tyapp (implode "bool") []) <=> has_type m (holSyntax_Tyapp
  (implode "num") []) /\ has_type n (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp LESS_has_type;;

(* TODO Move *)
let SUB_has_type = prove
 (`has_type ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
  (implode "-") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
  "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)
  (holSyntax_Tyapp (implode "num") []) <=> has_type m (holSyntax_Tyapp
  (implode "num") []) /\ has_type n (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp SUB_has_type;;

(* TODO Move *)
let MOD_has_type = prove
 (`has_type ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
  (implode "MOD") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
  "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)
  (holSyntax_Tyapp (implode "num") []) <=> has_type m (holSyntax_Tyapp
  (implode "num") []) /\ has_type n (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp MOD_has_type;;

(* TODO Move *)
let DIV_has_type = prove
 (`has_type ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
  (implode "DIV") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
  "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)
  (holSyntax_Tyapp (implode "num") []) <=> has_type m (holSyntax_Tyapp
  (implode "num") []) /\ has_type n (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp DIV_has_type;;

let MOD_eqn1 = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ has_type m (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "MOD") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const (implode
     "_0") (holSyntax_Tyapp (implode "num") [])))) m)`,
  CHEAT_TAC);;

let DIV_eqn1 = prove
 (`numeral_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ has_type m (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "DIV") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const (implode
     "_0") (holSyntax_Tyapp (implode "num") [])))) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") []))) tm) (holSyntax_Const (implode "_0")
     (holSyntax_Tyapp (implode "num") []))))`,
  CHEAT_TAC);;

(* BIT0_0 *)
let compute_syntaxProof_BIT0_0 = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) ((\tm. holSyntax_Comb
  (holSyntax_Const (implode "BIT0") ((\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
  "num") []))) (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode
  "num") [])))`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * num2term, num2bit
 * ------------------------------------------------------------------------- *)

let num2term_typeof = prove
 (`typeof (num2term n) = (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp num2term_typeof;;

let num2term_has_type = prove
 (`has_type (num2term n) (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp num2term_has_type;;

let num2term_welltyped = prove
 (`welltyped (num2term n)`,
  CHEAT_TAC);;
add_simp num2term_welltyped;;

let num2term_term_ok = prove
 (`numeral_thy_ok thy ==> holSyntax_term_ok (FST thy) (num2term n)`,
  CHEAT_TAC);;

let num2term_VSUBST = prove
 (`!n. VSUBST is (num2term n) = num2term n`,
  CHEAT_TAC);;
add_simp num2term_VSUBST;;

let num2bit_typeof = prove
 (`!n. typeof (num2bit n) = (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp num2bit_typeof;;

let num2bit_has_type = prove
 (`!n. has_type (num2bit n) (holSyntax_Tyapp (implode "num") [])`,
  CHEAT_TAC);;
add_simp num2bit_has_type;;

let num2bit_welltyped = prove
 (`!n. welltyped (num2bit n)`,
  CHEAT_TAC);;
add_simp num2bit_welltyped;;

let num2bit_term_ok = prove
 (`numeral_thy_ok thy ==> holSyntax_term_ok (FST thy) (num2bit n)`,
  CHEAT_TAC);;

let num2bit_VSUBST = prove
 (`!n. VSUBST is (num2bit n) = num2bit n`,
  CHEAT_TAC);;
add_simp num2bit_VSUBST;;

let num2term_ADD = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2term (m + n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2term m) (num2term n)))`,
  CHEAT_TAC);;

let ADD_num2term =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2term_ADD));;

let num2term_SUB = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2term (m - n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "-") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2term m) (num2term n)))`,
  CHEAT_TAC);;

let SUB_num2term =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2term_SUB));;

let num2term_MUL = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2term (m * n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "*") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2term m) (num2term n)))`,
  CHEAT_TAC);;

let MUL_num2term =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2term_MUL));;

let bool2term_LESS_num2term = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (bool2term (m < n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "<") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "bool") [])))) t1) t2) (num2term m) (num2term n)))`,
  CHEAT_TAC);;

let LESS_bool2term_num2term =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL bool2term_LESS_num2term));;

let bool2term_EQ_num2term = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (bool2term (m = n)) ((===)
  (num2term m) (num2term n)))`,
  CHEAT_TAC);;

let EQ_bool2term_num2term =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL bool2term_EQ_num2term));;

let SUB_DIV = prove
 (`!m n. 0 < n /\ n <= m ==> SUC ((m - n) DIV n) = m DIV n`,
  CHEAT_TAC);;

let DIV_num2term = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
  (holSyntax_Comb (holSyntax_Const (implode "DIV") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
  (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
  [])))) t1) t2) (num2term m) (num2term n)) (num2term (SAFEDIV m n)))`,
  CHEAT_TAC);;

let num2term_DIV =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL DIV_num2term));;

let MOD_num2term = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
  (holSyntax_Comb (holSyntax_Const (implode "MOD") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
  (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "num")
  [])))) t1) t2) (num2term m) (num2term n)) (num2term (SAFEMOD m n)))`,
  CHEAT_TAC);;

let num2term_MOD =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL MOD_num2term));;

let num2bit_num2term = prove
 (`numeral_thy_ok thy ==>
     (!n. (|-) (thy,[]) ((===) (num2bit n) (num2term n)))`,
  CHEAT_TAC);;

let num2bit_ADD = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2bit (m + n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2bit m) (num2bit n)))`,
  CHEAT_TAC);;

let ADD_num2bit = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2bit_ADD));;

let num2bit_SUB = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2bit (m - n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "-") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2bit m) (num2bit n)))`,
  CHEAT_TAC);;

let SUB_num2bit = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2bit_SUB));;

let num2bit_MUL = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2bit (m * n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "*") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2bit m) (num2bit n)))`,
  CHEAT_TAC);;

let MUL_num2bit = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2bit_MUL));;


let num2bit_DIV = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2bit (SAFEDIV m n)) ((\t1
  t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "DIV") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2bit m) (num2bit n)))`,
  CHEAT_TAC);;

let DIV_num2bit = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2bit_DIV));;

let num2bit_MOD = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (num2bit (SAFEMOD m n)) ((\t1
  t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "MOD") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "num") [])))) t1) t2) (num2bit m) (num2bit n)))`,
  CHEAT_TAC);;

let MOD_num2bit = DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL num2bit_MOD));;

let bool2term_LESS_num2bit = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (bool2term (m < n)) ((\t1 t2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "<") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (ast_Fun (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
  "bool") [])))) t1) t2) (num2bit m) (num2bit n)))`,
  CHEAT_TAC);;

let LESS_bool2term_num2bit =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL bool2term_LESS_num2bit));;

let bool2term_EQ_num2bit = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) (bool2term (m = n)) ((===)
  (num2bit m) (num2bit n)))`,
  CHEAT_TAC);;

let EQ_bool2term_num2bit =
  DISCH_ALL (MATCH_MP sym_equation (UNDISCH_ALL bool2term_EQ_num2bit));;

(* -------------------------------------------------------------------------
 * Compute values
 * ------------------------------------------------------------------------- *)

(* the termination relation that HOL4 gives is
     MEASURE compute_exp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let cexp_consts_def,cexp_consts_ind = define_guess
  `(cexp_consts (compute_syntax_Num n) = {}) /\
   (cexp_consts (compute_syntax_Var s) = {}) /\
   (cexp_consts (compute_syntax_Pair p q) = cexp_consts p UNION cexp_consts
    q) /\
   (cexp_consts (compute_syntax_Uop uop p) = cexp_consts p) /\
   (cexp_consts (compute_syntax_Binop bop p q) = cexp_consts p UNION
    cexp_consts q) /\
   (cexp_consts (compute_syntax_If p q r) = cexp_consts p UNION cexp_consts
    q UNION cexp_consts r) /\
   (cexp_consts (compute_syntax_Let s p q) = cexp_consts p UNION
    cexp_consts q) /\
   (cexp_consts (compute_syntax_App s cs) = {s,LENGTH cs} UNION UNIONS
    (set_of_list (MAP cexp_consts cs)))`;;

(* the termination relation that HOL4 gives is
     MEASURE compute_exp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let cexp_vars_def,cexp_vars_ind = define_guess
  `(cexp_vars (compute_syntax_Num n) = {}) /\
   (cexp_vars (compute_syntax_Var s) = {s}) /\
   (cexp_vars (compute_syntax_Pair p q) = cexp_vars p UNION cexp_vars q) /\
   (cexp_vars (compute_syntax_Uop uop p) = cexp_vars p) /\
   (cexp_vars (compute_syntax_Binop bop p q) = cexp_vars p UNION cexp_vars
    q) /\
   (cexp_vars (compute_syntax_If p q r) = cexp_vars p UNION cexp_vars q
    UNION cexp_vars r) /\
   (cexp_vars (compute_syntax_Let s p q) = cexp_vars p UNION (cexp_vars q
    DIFF {s})) /\
   (cexp_vars (compute_syntax_App s cs) = UNIONS (set_of_list (MAP
    cexp_vars cs)))`;;

(* The semantics of 'ill-typed' operations on the compute_exp type is to
 * return the number 0 (i.e. Num 0n).
 *)

let compute_thy_ok_def = new_definition
  `compute_thy_ok thy <=>
     numeral_thy_ok thy /\ (|-) (
      // Cexp_add
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_add") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num")
        []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
                   "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                   (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp
                   (implode "num") []))))) /\ (|-) (thy,[]) ((===) ((\t1 t2.
                   holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_add") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                   (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                   (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") []))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_pair") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) (holSyntax_Var (implode "m")
                   (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (thy,[])
                   ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_add") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                   "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) (holSyntax_Var (implode "n")
                   (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (thy,[])
                   ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_add") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q2") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (
      // Cexp_sub
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_sub") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num")
        []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "-") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
                   "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                   (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp
                   (implode "num") []))))) /\ (|-) (thy,[]) ((===) ((\t1 t2.
                   holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_sub") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                   (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                   (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") []))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_pair") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) (holSyntax_Var (implode "m")
                   (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (thy,[])
                   ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_sub") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                   "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_sub") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q2") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (
      // Cexp_mul
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_mul") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num")
        []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "*") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
                   "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                   (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp
                   (implode "num") []))))) /\ (|-) (thy,[]) ((===) ((\t1 t2.
                   holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_mul") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                   (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                   (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") []))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_pair") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_mul") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                   "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_mul") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q2") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (
      // Cexp_div
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_div") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num")
        []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "DIV") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
                   "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                   (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp
                   (implode "num") []))))) /\ (|-) (thy,[]) ((===) ((\t1 t2.
                   holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_div") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                   (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                   (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") []))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_pair") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_div") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                   "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_div") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q2") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (
      // Cexp_mod
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_mod") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num")
        []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "MOD") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
                   "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
                   (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp
                   (implode "num") []))))) /\ (|-) (thy,[]) ((===) ((\t1 t2.
                   holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_mod") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                   (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                   (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") []))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_pair") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) (holSyntax_Var (implode "m")
                   (holSyntax_Tyapp (implode "num") [])))) /\ (|-) (thy,[])
                   ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_mod") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                   "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_mod") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q2") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (
      // Cexp_less
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_less") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num")
        []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "COND") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "<") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
                   "num") []) (holSyntax_Tyapp (implode "bool") [])))) t1) t2)
                   (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp
                   (implode "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const
                   (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") []))))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) (holSyntax_Const (implode
                                "_0") (holSyntax_Tyapp (implode "num") []))))))
                                /\ (|-) (thy,[]) ((===) ((\t1 t2.
                                holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                                (implode "Cexp_less") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "cval") []) (ast_Fun (holSyntax_Tyapp
                                (implode "cval") []) (holSyntax_Tyapp (implode
                                "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
                                (holSyntax_Const (implode "Cexp_num") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "cval") []))) tm)
                                (holSyntax_Var (implode "m") (holSyntax_Tyapp
                                (implode "num") []))) ((\t1 t2. holSyntax_Comb
                                (holSyntax_Comb (holSyntax_Const (implode
                                "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                                "fun") [s; t]) (holSyntax_Tyapp (implode
                                "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                                "cval") []) (holSyntax_Tyapp (implode "cval")
                                [])))) t1) t2) (holSyntax_Var (implode "p1")
                                (holSyntax_Tyapp (implode "cval") []))
                                (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                                (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_less") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                   "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_less") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                   (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                   "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
                   (ast_Fun (holSyntax_Tyapp (implode "cval") [])
                   (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q2") (holSyntax_Tyapp
                   (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (
      // Cexp_if
      thy,[]) ((===) ((\t1 t2 t3. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Comb (holSyntax_Const (implode "Cexp_if") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        []))))) t1) t2) t3) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") []))) /\ (|-) (thy,[])
        ((===) ((\t1 t2 t3. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_if") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") []))))) t1) t2)
        t3) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") [])))
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        /\ (|-) (thy,[]) ((===) ((\t1 t2 t3. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Comb (holSyntax_Const (implode "Cexp_if") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        []))))) t1) t2) t3) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
        (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num") []))))
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        /\ (|-) (
      // Cexp_fst, Cexp_snd
      thy,[]) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_fst") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") [])))
        /\ (|-) (thy,[]) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_fst") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "cval") []))) tm)
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") []))))) /\ (|-)
        (thy,[]) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_snd") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        /\ (|-) (thy,[]) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_snd") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "cval") []))) tm)
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") []))))) /\ (|-) (
      // Cexp_ispair
      thy,[]) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "Cexp_ispair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
        (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))) /\ (|-) (thy,[]) ((===) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "Cexp_ispair") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) (holSyntax_Var (implode "m")
                   (holSyntax_Tyapp (implode "num") []))))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") [])))))
                   /\ (|-) (
      // Cexp_eq
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_eq") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
        [])))) t1) t2) (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
        "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode
        "cval") [])))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "COND") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((===) (holSyntax_Var
                   (implode "p1") (holSyntax_Tyapp (implode "cval") []))
                   (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode
                   "cval") []))) ((\tm. holSyntax_Comb (holSyntax_Const
                   (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") []))))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) (holSyntax_Const (implode
                                "_0") (holSyntax_Tyapp (implode "num") []))))))
                                /\ (|-) (thy,[]) ((===) ((===) ((\t1 t2.
                                holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                                (implode "Cexp_pair") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "cval") []) (ast_Fun (holSyntax_Tyapp
                                (implode "cval") []) (holSyntax_Tyapp (implode
                                "cval") [])))) t1) t2) (holSyntax_Var (implode
                                "p1") (holSyntax_Tyapp (implode "cval") []))
                                (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                                (implode "cval") []))) ((\t1 t2. holSyntax_Comb
                                (holSyntax_Comb (holSyntax_Const (implode
                                "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
                                "fun") [s; t]) (holSyntax_Tyapp (implode
                                "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                                "cval") []) (holSyntax_Tyapp (implode "cval")
                                [])))) t1) t2) (holSyntax_Var (implode "p2")
                                (holSyntax_Tyapp (implode "cval") []))
                                (holSyntax_Var (implode "q2") (holSyntax_Tyapp
                                (implode "cval") []))))
                 ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
                   []) (ast_Fun (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                   (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
                   (implode "bool") []))))) t) t1) t2) ((===) (holSyntax_Var
                   (implode "p1") (holSyntax_Tyapp (implode "cval") []))
                   (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode
                   "cval") []))) ((===) (holSyntax_Var (implode "q1")
                   (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
                   (implode "q2") (holSyntax_Tyapp (implode "cval") [])))
                   (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode
                   "bool") [])))) /\ (|-) (thy,[]) ((===) ((===) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) (holSyntax_Var (implode "n")
                   (holSyntax_Tyapp (implode "num") [])))) ((===)
                   (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") [])) (holSyntax_Var (implode "n") (holSyntax_Tyapp
                   (implode "num") [])))) /\ (|-) (thy,[]) ((===) ((===) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                   "num") []))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_pair") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") [])))) (holSyntax_Const (implode "F")
                   (holSyntax_Tyapp (implode "bool") []))) /\ (|-) (thy,[])
                   ((===) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_pair") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
                   "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
                   (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                   "cval") [])) (holSyntax_Var (implode "q1") (holSyntax_Tyapp
                   (implode "cval") []))) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "Cexp_num") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "cval") [])))
                   tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                   "num") [])))) (holSyntax_Const (implode "F")
                   (holSyntax_Tyapp (implode "bool") []))) /\ (|-) (
      // Let
      thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "LET") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode
        "cval") [])) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode
        "cval") []))) (holSyntax_Var (implode "p1") (holSyntax_Tyapp
        (implode "cval") []))) (holSyntax_Comb (holSyntax_Var (implode "f")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval")
        []))))`;;

let LET_eqn = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     f /\ holSyntax_term_ok (FST thy)
     p1 /\ has_type f ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])) /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) ==> (|-)
     (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "LET") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) f p1) (holSyntax_Comb f p1))`,
  CHEAT_TAC);;

let CEXP_IF_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2 t3.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
     "Cexp_if") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") []))))) t1) t2) t3) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
     "num") []))) tm) m)) p1 q1) p1)`,
  CHEAT_TAC);;

let CEXP_IF_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\
   holSyntax_term_ok (FST thy)
     p2 /\ holSyntax_term_ok (FST thy)
     q2 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type p2 (holSyntax_Tyapp
     (implode "cval") []) /\ has_type q2 (holSyntax_Tyapp (implode "cval")
     []) ==> (|-) (thy,[]) ((===) ((\t1 t2 t3. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_if") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     []))))) t1) t2) t3) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p2 q2) p1 q1) q1)`,
  CHEAT_TAC);;

let CEXP_IF_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2
     t3. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_if") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") []))))) t1) t2) t3) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") []))) tm) (holSyntax_Const (implode "_0")
     (holSyntax_Tyapp (implode "num") [])))) p1 q1) q1)`,
  CHEAT_TAC);;

let CEXP_ADD_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_add")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n)) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "+") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)))`,
  CHEAT_TAC);;

let CEXP_ADD_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_add") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1)) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m))`,
  CHEAT_TAC);;

let CEXP_ADD_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     n /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type n (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_add") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) n)) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) n))`,
  CHEAT_TAC);;

let CEXP_ADD_eqn4 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\
   holSyntax_term_ok (FST thy) p2
     /\ holSyntax_term_ok (FST thy)
     q2 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type p2 (holSyntax_Tyapp
     (implode "cval") []) /\ has_type q2 (holSyntax_Tyapp (implode "cval") [])
     ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_add") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p2 q2))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_SUB_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_sub")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n)) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "-") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)))`,
  CHEAT_TAC);;

let CEXP_SUB_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_sub") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1)) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m))`,
  CHEAT_TAC);;

let CEXP_SUB_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) n
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type n (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_sub") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_SUB_eqn4 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\
   holSyntax_term_ok (FST thy) p2
     /\ holSyntax_term_ok (FST thy)
     q2 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type p2 (holSyntax_Tyapp
     (implode "cval") []) /\ has_type q2 (holSyntax_Tyapp (implode "cval") [])
     ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_sub") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p2 q2))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_MUL_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_mul")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n)) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "*") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)))`,
  CHEAT_TAC);;

let CEXP_MUL_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) m
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_mul") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_MUL_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) n
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type n (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_mul") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_MUL_eqn4 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\
   holSyntax_term_ok (FST thy) p2
     /\ holSyntax_term_ok (FST thy)
     q2 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type p2 (holSyntax_Tyapp
     (implode "cval") []) /\ has_type q2 (holSyntax_Tyapp (implode "cval") [])
     ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_mul") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p2 q2))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_DIV_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_div")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n)) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "DIV") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)))`,
  CHEAT_TAC);;

let CEXP_DIV_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) m
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_div") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_DIV_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) n
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type n (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_div") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_DIV_eqn4 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\
   holSyntax_term_ok (FST thy) p2
     /\ holSyntax_term_ok (FST thy)
     q2 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type p2 (holSyntax_Tyapp
     (implode "cval") []) /\ has_type q2 (holSyntax_Tyapp (implode "cval") [])
     ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_div") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p2 q2))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_MOD_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ holSyntax_term_ok (FST thy)
     n /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_mod")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n)) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "MOD") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
     "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2) m n)))`,
  CHEAT_TAC);;

let CEXP_MOD_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) m
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_mod") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) m))`,
  CHEAT_TAC);;

let CEXP_MOD_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) n
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type n (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_mod") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_MOD_eqn4 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\
   holSyntax_term_ok (FST thy) p2
     /\ holSyntax_term_ok (FST thy)
     q2 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type p2 (holSyntax_Tyapp
     (implode "cval") []) /\ has_type q2 (holSyntax_Tyapp (implode "cval") [])
     ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_mod") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p2 q2))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_LESS_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) m
     /\ holSyntax_term_ok (FST thy) n
     /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type n
     (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[]) ((===) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_less") ((\s
     t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) m) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "COND") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((\t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "<") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
                   "num") []) (holSyntax_Tyapp (implode "bool") [])))) t1) t2)
                   m n) ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                   (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
                   (implode "_0") (holSyntax_Tyapp (implode "num") []))))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) (holSyntax_Const (implode
                                "_0") (holSyntax_Tyapp (implode "num")
                                []))))))`,
  CHEAT_TAC);;

let CEXP_LESS_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) m
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type m (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_less") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\tm. holSyntax_Comb (holSyntax_Const
     (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_LESS_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) n
     /\ holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type n (holSyntax_Tyapp (implode "num") []) /\ has_type p1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type q1 (holSyntax_Tyapp
     (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_less") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_LESS_eqn4 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\
   holSyntax_term_ok (FST thy) p2
     /\ holSyntax_term_ok (FST thy)
     q2 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) /\ has_type p2 (holSyntax_Tyapp
     (implode "cval") []) /\ has_type q2 (holSyntax_Tyapp (implode "cval") [])
     ==> (|-) (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_less") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p2 q2))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "NUMERAL") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                   (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_FST_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_fst") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1)) p1)`,
  CHEAT_TAC);;

let CEXP_FST_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ has_type m (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_fst") ((\s
     t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) m)) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") []))) tm) (holSyntax_Const (implode "_0")
     (holSyntax_Tyapp (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_SND_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     p1 /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_snd") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
     holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1)) q1)`,
  CHEAT_TAC);;

let CEXP_SND_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ has_type m (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_snd") ((\s
     t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) m)) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") []))) tm) (holSyntax_Const (implode "_0")
     (holSyntax_Tyapp (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_ISPAIR_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1
     /\ holSyntax_term_ok (FST thy)
     q1 /\ has_type p1 (holSyntax_Tyapp (implode "cval") []) /\ has_type q1
     (holSyntax_Tyapp (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_ispair") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2. holSyntax_Comb
     (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval")
     []) (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
     (implode "cval") [])))) t1) t2) p1 q1))
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                   t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\tm. holSyntax_Comb
                   (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
                   (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
                   []) (holSyntax_Tyapp (implode "num") []))) tm) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s
                   t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))) tm) (holSyntax_Const (implode "_0")
                   (holSyntax_Tyapp (implode "num") []))))))`,
  CHEAT_TAC);;

let CEXP_ISPAIR_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     m /\ has_type m (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_ispair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) m)) ((\tm.
     holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
     holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
     []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "num") []))) tm) (holSyntax_Const (implode "_0")
     (holSyntax_Tyapp (implode "num") [])))))`,
  CHEAT_TAC);;

let CEXP_EQ_eqn1 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1 /\ has_type
     p1 (holSyntax_Tyapp (implode "cval") []) /\
   holSyntax_term_ok (FST thy) q1 /\ has_type
     q1 (holSyntax_Tyapp (implode "cval") []) ==> (|-) (thy,[]) ((===) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_eq")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1)
                 ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
                   ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "cval") []))) tm) ((\t t1 t2. holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
                   "COND") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (ast_Fun
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))))) t) t1) t2) ((===) p1 q1) ((\tm.
                   holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "num") []) (holSyntax_Tyapp (implode "num") [])))
                   tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode
                   "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                   (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                   (implode "num") []))) tm) (holSyntax_Const (implode "_0")
                   (holSyntax_Tyapp (implode "num") []))))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) (holSyntax_Const (implode
                                "_0") (holSyntax_Tyapp (implode "num")
                                []))))))`,
  CHEAT_TAC);;

let CEXP_EQ_eqn2 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) p1 /\ has_type
     p1 (holSyntax_Tyapp (implode "cval") []) /\
   holSyntax_term_ok (FST thy) q1 /\ has_type
     q1 (holSyntax_Tyapp (implode "cval") []) /\
   holSyntax_term_ok (FST thy) p2 /\ has_type
     p2 (holSyntax_Tyapp (implode "cval") []) /\
   holSyntax_term_ok (FST thy) q2 /\ has_type
     q2 (holSyntax_Tyapp (implode "cval") []) ==> (|-) (thy,[]) ((===) ((===)
     ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
     "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1) ((\t1
     t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
     "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
     (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p2 q2))
                 ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                   (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s t.
                   holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                   (implode "bool") []) (ast_Fun (holSyntax_Tyapp (implode
                   "bool") []) (ast_Fun (holSyntax_Tyapp (implode "bool") [])
                   (holSyntax_Tyapp (implode "bool") []))))) t) t1) t2)
                   ((===) p1 p2) ((===) q1 q2) (holSyntax_Const (implode "F")
                   (holSyntax_Tyapp (implode "bool") []))))`,
  CHEAT_TAC);;

let CEXP_EQ_eqn3 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) n /\ has_type n
     (holSyntax_Tyapp (implode "num") []) /\
   holSyntax_term_ok (FST thy)
     m /\ has_type m (holSyntax_Tyapp (implode "num") []) ==> (|-) (thy,[])
     ((===) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num")
     ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) n))
     ((===) m n))`,
  CHEAT_TAC);;

let CEXP_EQ_eqn4 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) m /\ has_type m
     (holSyntax_Tyapp (implode "num") []) /\
   holSyntax_term_ok (FST thy) p1 /\ has_type
     p1 (holSyntax_Tyapp (implode "cval") []) /\
   holSyntax_term_ok (FST thy)
     q1 /\ has_type q1 (holSyntax_Tyapp (implode "cval") []) ==> (|-)
     (thy,[]) ((===) ((===) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) m) ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
     (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
     "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2) p1 q1))
     (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool") [])))`,
  CHEAT_TAC);;

let CEXP_EQ_eqn5 = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy) n /\ has_type n
     (holSyntax_Tyapp (implode "num") []) /\
   holSyntax_term_ok (FST thy) p1 /\ has_type
     p1 (holSyntax_Tyapp (implode "cval") []) /\
   holSyntax_term_ok (FST thy)
     q1 /\ has_type q1 (holSyntax_Tyapp (implode "cval") []) ==> (|-)
     (thy,[]) ((===) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) p1 q1) ((\tm. holSyntax_Comb (holSyntax_Const (implode
     "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode "cval")
     []))) tm) n)) (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode
     "bool") [])))`,
  CHEAT_TAC);;

let compute_thy_ok_terms_ok = prove
 (`compute_thy_ok thy ==>
     // bools
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
       (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
       "num") []) (holSyntax_Tyapp (implode "num") []))))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
       (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp (implode
       "bool") []) (holSyntax_Tyapp (implode "bool") []))))) /\
     // nums
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "-") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "*") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "DIV") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "MOD") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
       (implode "num") []) (holSyntax_Tyapp (implode "bool") [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num") [])) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
       "num") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "BIT0") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
       (implode "num") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "BIT1") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
       (implode "num") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
       (implode "num") []))) /\
     // cexps
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_add") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_sub") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_mul") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_div") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_mod") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_less") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
       (implode "cval") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_if") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode
       "cval") []) (holSyntax_Tyapp (implode "cval") []))))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_pair") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_fst") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
       (implode "cval") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_snd") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
       (implode "cval") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_ispair") ((\s t. holSyntax_Tyapp
       (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
       (holSyntax_Tyapp (implode "cval") []))) /\
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "Cexp_eq") ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     // let
     holSyntax_term_ok (FST thy)
       (holSyntax_Const (implode "LET") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
       (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])) (ast_Fun
       (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
       [])))) /\
     // types
     type_ok (FST (FST thy)) (holSyntax_Tyapp (implode "cval") [])`,
  CHEAT_TAC);;

let compute_thy_ok_theory_ok = prove
 (`compute_thy_ok thy ==> theory_ok thy`,
  CHEAT_TAC);;
add_simp compute_thy_ok_theory_ok;;

let compute_thy_ok_numeral_thy_ok = prove
 (`compute_thy_ok thy ==> numeral_thy_ok thy`,
  CHEAT_TAC);;
add_simp compute_thy_ok_numeral_thy_ok;;

let compute_thy_ok_bool_thy_ok = prove
 (`compute_thy_ok thy ==> bool_thy_ok thy`,
  CHEAT_TAC);;
add_simp compute_thy_ok_bool_thy_ok;;

let cexp2term_typeof = prove
 (`!cv. typeof (cexp2term cv) = (holSyntax_Tyapp (implode "cval") [])`,
  CHEAT_TAC);;
add_simp cexp2term_typeof;;

let cexp2term_has_type = prove
 (`!cv. has_type (cexp2term cv) (holSyntax_Tyapp (implode "cval") [])`,
  CHEAT_TAC);;
add_simp cexp2term_has_type;;

let cexp2term_welltyped = prove
 (`!cv. welltyped (cexp2term cv)`,
  CHEAT_TAC);;
add_simp cexp2term_welltyped;;

let bop2term_term_ok = prove
 (`compute_thy_ok thy ==>
     typeof tm1 = (holSyntax_Tyapp (implode "cval") []) /\ typeof tm2 =
       (holSyntax_Tyapp (implode "cval") []) /\
     holSyntax_term_ok (FST thy)
       tm1 /\ holSyntax_term_ok (FST thy)
       tm2 ==>
       holSyntax_term_ok (FST thy) (bop2term bop tm1 tm2)`,
  CHEAT_TAC);;

let uop2term_term_ok = prove
 (`compute_thy_ok thy ==>
     typeof tm = (holSyntax_Tyapp (implode "cval") []) /\
     holSyntax_term_ok (FST thy)
       tm ==>
       holSyntax_term_ok (FST thy) (uop2term uop tm)`,
  CHEAT_TAC);;

let cexp2term_term_ok = prove
 (`compute_thy_ok thy ==>
     (!cv.
       (!c n.
         (c,n) IN cexp_consts cv ==>
           holSyntax_term_ok (FST thy) (holSyntax_Const c (app_type n))) ==>
         holSyntax_term_ok (FST thy) (cexp2term cv))`,
  CHEAT_TAC);;

(* TODO move *)
let bool2term_term_ok = prove
 (`bool_thy_ok thy ==>
     holSyntax_term_ok (FST thy) (bool2term b)`,
  CHEAT_TAC);;
add_simp bool2term_term_ok;;

let cexp_value_no_consts = prove
 (`!v. cexp_value v ==> cexp_consts v = {}`,
  CHEAT_TAC);;

let bool2term_EQ_cexpterm = prove
 (`compute_thy_ok thy ==>
     cexp_value p /\ cexp_value q ==> (|-) (thy,[]) ((===) (bool2term (p =
       q)) ((===) (cexp2term p) (cexp2term q)))`,
  CHEAT_TAC);;

let EQ_bool2term_cexpterm = prove
 (`compute_thy_ok thy ==>
     cexp_value p /\ cexp_value q ==> (|-) (thy,[]) ((===) ((===)
       (cexp2term p) (cexp2term q)) (bool2term (p = q)))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Bool";
   "FALSE";
   "TRUE"];;

(* and the interface *)
let _ = unhide_overloads ();;
