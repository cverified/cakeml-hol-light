(* ======================================================== *)
(*  compute: ported from HOL4's
    candle/prover/compute/computeScript.sml
    A definition theory, with 11 definitions and 1 theorem.  Needed
    by candle_kernelProg.ml and computeProof.ml.  *)
(* ======================================================== *)

(*
  Implementation of the compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/prover/compute/compute_exec.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "lib/balanced_map.ml";;
needs "lib/peg.ml";;
needs "lib/term.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compute"
  ["compute_eval"; "compute_exec"; "compute_syntax"; "holKernel";
   "holKernelProof"; "holSyntax"; "holSyntaxExtra"; "ml_monadBase"];;

(* HOL4 computeScript.sml:14-21: ML code, not ported *)

(* HOL4 computeScript.sml:27: the overload return, which the port expands *)
(* HOL4 computeScript.sml:28: the overload failwith, which the port expands *)
(* HOL4 computeScript.sml:29: the overload handle, which the port expands *)

(* -------------------------------------------------------------------------
 * Theory initialization
 * ------------------------------------------------------------------------- *)

let compute_thms_def = new_definition
  `compute_thms = MAP (holKernel_Sequent []) [(===)
      // COND_TRUE
      ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))))) t) t1) t2)
        (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") []))
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") [])))
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []));
        (===)
      // COND_FALSE
      ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
        (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))))) t) t1) t2)
        (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool") []))
        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") [])))
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") []));
        (===)
      // IF_TRUE
      ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
        (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp
        (implode "bool") []) (holSyntax_Tyapp (implode "bool") []))))) t) t1)
        t2) (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool")
        [])) (holSyntax_Var (implode "x") (holSyntax_Tyapp (implode "bool")
        [])) (holSyntax_Var (implode "y") (holSyntax_Tyapp (implode "bool")
        []))) (holSyntax_Var (implode "x") (holSyntax_Tyapp (implode "bool")
        [])); (===)
      // IF_FALSE
      ((\t t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "COND") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (ast_Fun
        (holSyntax_Tyapp (implode "bool") []) (ast_Fun (holSyntax_Tyapp
        (implode "bool") []) (holSyntax_Tyapp (implode "bool") []))))) t) t1)
        t2) (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool")
        [])) (holSyntax_Var (implode "x") (holSyntax_Tyapp (implode "bool")
        [])) (holSyntax_Var (implode "y") (holSyntax_Tyapp (implode "bool")
        []))) (holSyntax_Var (implode "y") (holSyntax_Tyapp (implode "bool")
        [])); (===)
      // NUMERAL
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") [])); (===)
      // BIT0
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "BIT0") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "n") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))); (===)
      // BIT1
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "BIT1") ((\s t.
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
        "num") [])))); (===)
      // ADD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "+") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Const (implode "_0")
        (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") [])); (===)
      // ADD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "+") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp
        (implode "num") []))) (holSyntax_Var (implode "n") (holSyntax_Tyapp
        (implode "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm) ((\t1
        t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "+") ((\s
        t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "m") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") [])))); (===)
      // SUB
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "-") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Const (implode "_0")
        (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Const (implode "_0")
        (holSyntax_Tyapp (implode "num") []))); (===)
      // SUB
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "-") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "m") (holSyntax_Tyapp (implode "num") [])) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Const (implode "_0")
        (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") [])); (===)
      // SUB
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "-") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp
        (implode "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const (implode
        "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") []))))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "-")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "m") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))); (===)
      // MUL
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "*") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Const (implode "_0")
        (holSyntax_Tyapp (implode "num") []))) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") []))) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Const (implode "_0")
        (holSyntax_Tyapp (implode "num") []))); (===)
      // MUL
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "*") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Var (implode "m") (holSyntax_Tyapp
        (implode "num") []))) (holSyntax_Var (implode "n") (holSyntax_Tyapp
        (implode "num") []))) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "+") ((\s t. holSyntax_Tyapp (implode "fun")
        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun (holSyntax_Tyapp
        (implode "num") []) (holSyntax_Tyapp (implode "num") [])))) t1) t2)
        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") []))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "*")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "m") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") [])))); (===)
      // DIV
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "DIV") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "m") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") [])))
                      ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                        (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s
                        t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))))) t) t1) t2) ((===)
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") [])) ((\tm. holSyntax_Comb (holSyntax_Const
                        (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
                        "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "num") []))) tm)
                        (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                        (implode "num") [])))) ((\tm. holSyntax_Comb
                        (holSyntax_Const (implode "NUMERAL") ((\s t.
                        holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))
                            ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                              (holSyntax_Comb (holSyntax_Const (implode "COND")
                              ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                              (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                              (holSyntax_Tyapp (implode "num") []) (ast_Fun
                              (holSyntax_Tyapp (implode "num") [])
                              (holSyntax_Tyapp (implode "num") []))))) t) t1)
                              t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                              (holSyntax_Const (implode "<") ((\s t.
                              holSyntax_Tyapp (implode "fun") [s; t])
                              (holSyntax_Tyapp (implode "num") []) (ast_Fun
                              (holSyntax_Tyapp (implode "num") [])
                              (holSyntax_Tyapp (implode "bool") [])))) t1) t2)
                              (holSyntax_Var (implode "m") (holSyntax_Tyapp
                              (implode "num") [])) (holSyntax_Var (implode "n")
                              (holSyntax_Tyapp (implode "num") []))) ((\tm.
                              holSyntax_Comb (holSyntax_Const (implode
                              "NUMERAL") ((\s t. holSyntax_Tyapp (implode
                              "fun") [s; t]) (holSyntax_Tyapp (implode "num")
                              []) (holSyntax_Tyapp (implode "num") []))) tm)
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
                                (implode "num") [])))))); (===)
      // MOD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "MOD") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") [])))) t1) t2) (holSyntax_Var (implode
        "m") (holSyntax_Tyapp (implode "num") [])) (holSyntax_Var (implode "n")
        (holSyntax_Tyapp (implode "num") [])))
                      ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                        (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s
                        t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))))) t) t1) t2) ((===)
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") [])) ((\tm. holSyntax_Comb (holSyntax_Const
                        (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
                        "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "num") []))) tm)
                        (holSyntax_Const (implode "_0") (holSyntax_Tyapp
                        (implode "num") [])))) (holSyntax_Var (implode "m")
                        (holSyntax_Tyapp (implode "num") []))
                            ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                              (holSyntax_Comb (holSyntax_Const (implode "COND")
                              ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                              (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                              (holSyntax_Tyapp (implode "num") []) (ast_Fun
                              (holSyntax_Tyapp (implode "num") [])
                              (holSyntax_Tyapp (implode "num") []))))) t) t1)
                              t2) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
                              (holSyntax_Const (implode "<") ((\s t.
                              holSyntax_Tyapp (implode "fun") [s; t])
                              (holSyntax_Tyapp (implode "num") []) (ast_Fun
                              (holSyntax_Tyapp (implode "num") [])
                              (holSyntax_Tyapp (implode "bool") [])))) t1) t2)
                              (holSyntax_Var (implode "m") (holSyntax_Tyapp
                              (implode "num") [])) (holSyntax_Var (implode "n")
                              (holSyntax_Tyapp (implode "num") [])))
                              (holSyntax_Var (implode "m") (holSyntax_Tyapp
                              (implode "num") []))
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
                                (implode "num") []))))); (===)
      // LESS
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "<") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "bool") [])))) t1) t2) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") [])) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Const
        (implode "F") (holSyntax_Tyapp (implode "bool") [])); (===)
      // LESS
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "<") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "bool") [])))) t1) t2) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Const (implode "_0")
        (holSyntax_Tyapp (implode "num") []))) ((\tm. holSyntax_Comb
        (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
        (implode "num") []))) tm) (holSyntax_Var (implode "n") (holSyntax_Tyapp
        (implode "num") [])))) (holSyntax_Const (implode "T") (holSyntax_Tyapp
        (implode "bool") [])); (===)
      // LESS
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "<") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
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
        (implode "n") (holSyntax_Tyapp (implode "num") []))); (===) ((===)
       // EQ
       ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
         (implode "_0") (holSyntax_Tyapp (implode "num") []))) ((\tm.
         holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
         (implode "_0") (holSyntax_Tyapp (implode "num") []))))
         (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") []));
         (===) ((===)
       // EQ
       ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
         (implode "_0") (holSyntax_Tyapp (implode "num") []))) ((\tm.
         holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
         (implode "n") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Const
         (implode "F") (holSyntax_Tyapp (implode "bool") [])); (===) ((===)
       // EQ
       ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
         (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
         holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
         (implode "_0") (holSyntax_Tyapp (implode "num") []))))
         (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool") []));
         (===) ((===)
       // EQ
       ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
         (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
         holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var
         (implode "n") (holSyntax_Tyapp (implode "num") [])))) ((===)
         (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
         (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") [])));
         (===)
      // CEXP_ADD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_add") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                        (implode "+") ((\s t. holSyntax_Tyapp (implode "fun")
                        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") [])))) t1) t2) (holSyntax_Var (implode
                        "m") (holSyntax_Tyapp (implode "num") []))
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") [])))); (===)
      // CEXP_ADD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_add") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm)
                        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                        "num") []))); (===)
      // CEXP_ADD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_add") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm)
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") []))); (===)
      // CEXP_ADD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_add") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_SUB
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_sub") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                        (implode "-") ((\s t. holSyntax_Tyapp (implode "fun")
                        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") [])))) t1) t2) (holSyntax_Var (implode
                        "m") (holSyntax_Tyapp (implode "num") []))
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") [])))); (===)
      // CEXP_SUB
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_sub") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm)
                        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                        "num") []))); (===)
      // CEXP_SUB
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_sub") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_SUB
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_sub") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_MUL
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mul") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                        (implode "*") ((\s t. holSyntax_Tyapp (implode "fun")
                        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") [])))) t1) t2) (holSyntax_Var (implode
                        "m") (holSyntax_Tyapp (implode "num") []))
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") [])))); (===)
      // CEXP_MUL
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mul") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_MUL
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mul") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_MUL
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mul") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_DIV
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_div") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                        (implode "DIV") ((\s t. holSyntax_Tyapp (implode "fun")
                        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") [])))) t1) t2) (holSyntax_Var (implode
                        "m") (holSyntax_Tyapp (implode "num") []))
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") [])))); (===)
      // CEXP_DIV
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_div") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_DIV
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_div") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_DIV
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_div") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_MOD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mod") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                        (implode "MOD") ((\s t. holSyntax_Tyapp (implode "fun")
                        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") [])))) t1) t2) (holSyntax_Var (implode
                        "m") (holSyntax_Tyapp (implode "num") []))
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") [])))); (===)
      // CEXP_MOD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mod") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm)
                        (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode
                        "num") []))); (===)
      // CEXP_MOD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mod") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_MOD
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_mod") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_LESS
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_less") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\t t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
                        (holSyntax_Const (implode "COND") ((\s t.
                        holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))))) t) t1) t2) ((\t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Const
                        (implode "<") ((\s t. holSyntax_Tyapp (implode "fun")
                        [s; t]) (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "bool") [])))) t1) t2) (holSyntax_Var (implode
                        "m") (holSyntax_Tyapp (implode "num") []))
                        (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode
                        "num") []))) ((\tm. holSyntax_Comb (holSyntax_Const
                        (implode "SUC") ((\s t. holSyntax_Tyapp (implode "fun")
                        [s; t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "num") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") []))))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) (holSyntax_Const (implode
                                "_0") (holSyntax_Tyapp (implode "num") [])))));
                                (===)
      // CEXP_LESS
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_less") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_LESS
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_less") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "n") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_LESS
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_less") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
        ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_IF
      ((\t1 t2 t3. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_if") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") []))))) t1) t2)
        t3) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t. holSyntax_Tyapp
        (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num") [])
        (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Var (implode "m")
        (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Var (implode "p1")
        (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var (implode "q1")
        (holSyntax_Tyapp (implode "cval") []))) (holSyntax_Var (implode "p1")
        (holSyntax_Tyapp (implode "cval") [])); (===)
      // CEXP_IF
      ((\t1 t2 t3. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
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
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") []));
        (===)
      // CEXP_IF
      ((\t1 t2 t3. holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
        (holSyntax_Const (implode "Cexp_if") ((\s t. holSyntax_Tyapp (implode
        "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") []))))) t1) t2)
        t3) ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") [])); (===)
      // CEXP_FST
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_fst") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") [])))) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])); (===)
      // CEXP_FST
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_fst") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") [])))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_SND
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_snd") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") [])))) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") [])); (===)
      // CEXP_SND
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_snd") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") [])))) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "num") []))) tm) (holSyntax_Const
        (implode "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_ISPAIR
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_ispair") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\t1 t2.
        holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
        ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
        (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
        (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
        (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
        (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
                        holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) ((\tm. holSyntax_Comb
                        (holSyntax_Const (implode "NUMERAL") ((\s t.
                        holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") []))))); (===)
      // CEXP_ISPAIR
      ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_ispair") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "cval") []) (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
        holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
        holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
        "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
        (implode "m") (holSyntax_Tyapp (implode "num") []))))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\tm.
                        holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
                        ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))) tm) (holSyntax_Const (implode
                        "_0") (holSyntax_Tyapp (implode "num") [])))); (===)
      // CEXP_EQ
      ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
        "Cexp_eq") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
        (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
        (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
                      ((\tm. holSyntax_Comb (holSyntax_Const (implode
                        "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                        t]) (holSyntax_Tyapp (implode "num") [])
                        (holSyntax_Tyapp (implode "cval") []))) tm) ((\t t1 t2.
                        holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
                        (holSyntax_Const (implode "COND") ((\s t.
                        holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (ast_Fun
                        (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                        (implode "num") []))))) t) t1) t2) ((===)
                        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                        "cval") [])) (holSyntax_Var (implode "q1")
                        (holSyntax_Tyapp (implode "cval") [])))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "SUC") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) ((\tm. holSyntax_Comb
                                (holSyntax_Const (implode "NUMERAL") ((\s t.
                                holSyntax_Tyapp (implode "fun") [s; t])
                                (holSyntax_Tyapp (implode "num") [])
                                (holSyntax_Tyapp (implode "num") []))) tm)
                                (holSyntax_Const (implode "_0")
                                (holSyntax_Tyapp (implode "num") []))))
                              ((\tm. holSyntax_Comb (holSyntax_Const
                                (implode "NUMERAL") ((\s t. holSyntax_Tyapp
                                (implode "fun") [s; t]) (holSyntax_Tyapp
                                (implode "num") []) (holSyntax_Tyapp (implode
                                "num") []))) tm) (holSyntax_Const (implode
                                "_0") (holSyntax_Tyapp (implode "num") [])))));
                                (===) ((===)
       // PAIR_EQ1
       ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
         (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
         (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
         (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
         (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
         ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
         (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
         (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
         (holSyntax_Var (implode "p2") (holSyntax_Tyapp (implode "cval") []))
         (holSyntax_Var (implode "q2") (holSyntax_Tyapp (implode "cval") []))))
                      ((\t t1 t2. holSyntax_Comb (holSyntax_Comb
                        (holSyntax_Comb (holSyntax_Const (implode "COND") ((\s
                        t. holSyntax_Tyapp (implode "fun") [s; t])
                        (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                        (holSyntax_Tyapp (implode "bool") []) (ast_Fun
                        (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
                        (implode "bool") []))))) t) t1) t2) ((===)
                        (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode
                        "cval") [])) (holSyntax_Var (implode "p2")
                        (holSyntax_Tyapp (implode "cval") []))) ((===)
                        (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode
                        "cval") [])) (holSyntax_Var (implode "q2")
                        (holSyntax_Tyapp (implode "cval") [])))
                        (holSyntax_Const (implode "F") (holSyntax_Tyapp
                        (implode "bool") []))); (===) ((===)
       // PAIR_EQ2
       ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
         (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\tm.
         holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
         (implode "n") (holSyntax_Tyapp (implode "num") [])))) ((===)
         (holSyntax_Var (implode "m") (holSyntax_Tyapp (implode "num") []))
         (holSyntax_Var (implode "n") (holSyntax_Tyapp (implode "num") [])));
         (===) ((===)
       // PAIR_EQ3
       ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
         (implode "m") (holSyntax_Tyapp (implode "num") []))) ((\t1 t2.
         holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair")
         ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
         (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
         (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (holSyntax_Var
         (implode "p1") (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Var
         (implode "q1") (holSyntax_Tyapp (implode "cval") []))))
         (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode "bool") []));
         (===) ((===)
       // PAIR_EQ4
       ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
         (holSyntax_Tyapp (implode "cval") []) (ast_Fun (holSyntax_Tyapp
         (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
         (holSyntax_Var (implode "p1") (holSyntax_Tyapp (implode "cval") []))
         (holSyntax_Var (implode "q1") (holSyntax_Tyapp (implode "cval") [])))
         ((\tm. holSyntax_Comb (holSyntax_Const (implode "Cexp_num") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "num") []) (holSyntax_Tyapp (implode "cval") []))) tm) (holSyntax_Var
         (implode "n") (holSyntax_Tyapp (implode "num") [])))) (holSyntax_Const
         (implode "F") (holSyntax_Tyapp (implode "bool") []));
      ((===)
       // LET
       ((\t1 t2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "LET") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "cval") []) (holSyntax_Tyapp (implode "cval") [])) (ast_Fun
         (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode
         "cval") [])))) t1) t2) (holSyntax_Var (implode "f") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "cval") []) (holSyntax_Tyapp (implode "cval") []))) (holSyntax_Var
         (implode "p1") (holSyntax_Tyapp (implode "cval") [])))
         (holSyntax_Comb (holSyntax_Var (implode "f") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "cval") []) (holSyntax_Tyapp (implode "cval") []))) (holSyntax_Var
         (implode "p1") (holSyntax_Tyapp (implode "cval") []))))]`;;

(* [allow_rebind] *)
let compute_compute_thms_def = SIMP_RULE [] compute_thms_def;;

let compute_init_def = new_definition
  `compute_init ths <=> ths = compute_thms`;;

(* -------------------------------------------------------------------------
 * compute_add
 * ------------------------------------------------------------------------- *)

let compute_add_def,compute_add_ind = define_guess
  `compute_add ths tm =
     if ~(compute_init ths) then
       failwith (implode (APPEND
         "compute_add: wrong theorems provided for initializ" "ation"))
     else APPEND (st_ex_bind (dest_binary (holSyntax_Const (implode "+")
       ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
       (implode "num") []) (ast_Fun (holSyntax_Tyapp (implode "num") [])
       (holSyntax_Tyapp (implode "num") [])))) tm) (\(l,r). st_ex_bind
       (dest_numeral l) (\x. st_ex_bind (dest_numeral r) (\y. st_ex_ignore_bind
       (
        res << --(num2bit (x + y))) (st_ex_bind (mk_eq (tm,(\tm.
          holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
          holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
          "num") []) (holSyntax_Tyapp (implode "num") []))) tm) res)) (\c.
        st_ex_return (holKernel_Sequent [] c))))))) (failwith (implode
          "compute_add"))`;;

(* -------------------------------------------------------------------------
 * compute
 * ------------------------------------------------------------------------- *)

(* the clauses in two quotations: n is mlstring and num, which one quotation
   cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE compute_exp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let const_list_def,const_list_ind = define_guess_clauses
  [`(compute_const_list (compute_syntax_Var n) = []) /\
    (compute_const_list (compute_syntax_Pair x y) = APPEND
    (compute_const_list x) (compute_const_list y)) /\
    (compute_const_list (compute_syntax_Uop uop x) = compute_const_list x) /\
    (compute_const_list (compute_syntax_Binop bop x y) = APPEND
    (compute_const_list x) (compute_const_list y)) /\
    (compute_const_list (compute_syntax_If x y z) = APPEND (APPEND
    (compute_const_list x) (compute_const_list y)) (compute_const_list z)) /\
    (compute_const_list (compute_syntax_Let s x y) = APPEND
    (compute_const_list x) (compute_const_list y)) /\
    (compute_const_list (compute_syntax_App s xs) = CONS (s,LENGTH xs)
    (FLAT (MAP compute_const_list xs)))`;
   `compute_const_list (compute_syntax_Num n) = []`];;

(* the clauses in two quotations: n is mlstring and num, which one quotation
   cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE compute_exp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let compute_var_list_def,compute_var_list_ind = define_guess_clauses
  [`(compute_var_list (compute_syntax_Var n) = [n]) /\
    (compute_var_list (compute_syntax_Pair x y) = APPEND (compute_var_list
    x) (compute_var_list y)) /\
    (compute_var_list (compute_syntax_Uop uop x) = compute_var_list x) /\
    (compute_var_list (compute_syntax_Binop bop x y) = APPEND
    (compute_var_list x) (compute_var_list y)) /\
    (compute_var_list (compute_syntax_If x y z) = APPEND (APPEND
    (compute_var_list x) (compute_var_list y)) (compute_var_list z)) /\
    (compute_var_list (compute_syntax_Let s x y) = APPEND (compute_var_list
    x) (FILTER (\n. ~(n = s)) (compute_var_list y))) /\
    (compute_var_list (compute_syntax_App s xs) = FLAT (MAP
    compute_var_list xs))`;
   `compute_var_list (compute_syntax_Num n) = []`];;

(* A valid equation is:
 *   [] |- const var1 ... varN = expr
 * where:
 * - var1 ... varN all have type Cexp
 * - expr contains only the variables var1 ... varN, and has type Cexp
 *)

let check_var_def = new_definition
  `check_var x1 =
   match x1 with
     holSyntax_Var s ty ->
     (if ty = (holSyntax_Tyapp (implode "cval") []) then st_ex_return s else
       failwith (strcat (implode "Kernel.compute: ill-typed variable: ") s))
   | _ ->
     failwith (implode (APPEND
       "Kernel.compute: non-variable argument on lhs of eq" "uation"))`;;

let check_eqn_def = new_definition
  `check_eqn (holKernel_Sequent h c) =
         st_ex_ignore_bind (if h = [] then st_ex_return one else failwith
           (implode "Kernel.compute: non-empty hypotheses in equation"))
           (st_ex_bind (dest_eq c) (\(ls,r). st_ex_bind (match list_dest_comb
           [] ls with CONS f vs ->
                       if ALL_DISTINCT vs then st_ex_return (f,vs)
                       else failwith (implode
                         "Kernel.compute: variables not distinct")
                   | _ -> failwith (implode "")) (\(f,vs). st_ex_bind
                     (APPEND (holKernel_dest_const f)
                 (failwith (implode (APPEND
                   "Kernel.compute: not a constant being applied on lh" "s"))))
                   (\(nm,ty). st_ex_bind (compute_eval_map check_var vs)
                   (\args.
         match dest_cexp r with NONE -> failwith (implode
           "Kernel.compute: rhs is not a cexp")
         | SOME cv ->
               st_ex_ignore_bind (if ALL (\v. MEM v args) (compute_var_list
                 cv) then st_ex_return one else failwith (implode
                 "Kernel.compute: rhs contains free variable")) (
               st_ex_return (nm,args,cv)))))))`;;

let compute_default_clock = new_definition
  `compute_default_clock = 1000000000`;;

let check_consts_def = new_definition
  `check_consts ars fn rhs =
     if ALL (\(c,n). MEM (c,n) ars) (compute_const_list rhs) then
       st_ex_return one else failwith (strcat (strcat (strcat (implode
       "Kernel.compute: rhs of ") fn) (implode " has a constant "))
               (implode "with no equation associated to it."))`;;

(* the clauses in two quotations: n is mlstring and num, which one quotation
   cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (compute_exp_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 computeScript.sml:259-261: the tactic that proves the termination *)
let check_cexp_closed_def,check_cexp_closed_ind = define_guess_clauses
  [`(check_cexp_closed bvs (compute_syntax_Var n) = MEM n bvs) /\
    (check_cexp_closed bvs (compute_syntax_Pair p q) =
      ALL (check_cexp_closed bvs) [p; q]) /\
    (check_cexp_closed bvs (compute_syntax_Uop uop p) =
      check_cexp_closed bvs p) /\
    (check_cexp_closed bvs (compute_syntax_Binop bop p q) =
      ALL (check_cexp_closed bvs) [p; q]) /\
    (check_cexp_closed bvs (compute_syntax_If p q r) =
      ALL (check_cexp_closed bvs) [p; q; r]) /\
    (check_cexp_closed bvs (compute_syntax_Let s p q) =
      (check_cexp_closed bvs p /\ check_cexp_closed (CONS s bvs) q)) /\
    (check_cexp_closed bvs (compute_syntax_App f cs) =
      ALL (check_cexp_closed bvs) cs)`;
   `check_cexp_closed bvs (compute_syntax_Num n) = T`];;

let compute_def,compute_ind = define_guess
  `compute (ths,ceqs) tm =
     C handle_Clash (\e. failwith (implode "impossible"))
     (if ~(compute_init ths) then
       failwith (implode (APPEND
         "Kernel.compute: wrong theorems provided for initia" "lization"))
     else match dest_cexp tm with NONE -> failwith (implode
       "Kernel.compute: term is not a compute_exp")
     | SOME cexp ->
           st_ex_ignore_bind (if check_cexp_closed [] cexp then st_ex_return
             one else failwith (implode (APPEND
             "Kernel.compute: free variables in starting express" "ion")))
             (st_ex_bind (compute_eval_map check_eqn ceqs) (\ceqs.
           st_ex_ignore_bind (if ALL_DISTINCT (MAP FST ceqs) then
             st_ex_return one else failwith (implode (APPEND
             "Kernel.compute: non-distinct function names in equ" "ations")))
             (st_ex_ignore_bind (
           ars << --(MAP (\(f,(n,r)). (f,LENGTH n)) ceqs)) (
           st_ex_ignore_bind (check_consts ars (implode "starting cexpr")
             cexp) (
           st_ex_ignore_bind (compute_eval_map (\(f,(n,r)). check_consts ars
             f r) ceqs) (st_ex_bind (exec (build_funs ceqs) []
             compute_default_clock (to_ce ceqs [] cexp)) (\res. st_ex_bind
             (mk_eq (tm,cv2term res)) (\c.
           st_ex_return (holKernel_Sequent [] c))))))))))`;;

(* and the interface *)
let _ = unhide_overloads ();;
