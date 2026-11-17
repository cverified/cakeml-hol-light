(* ======================================================== *)
(*  candle_basis_evaluate: ported from HOL4's
    candle/prover/candle_basis_evaluateScript.sml
    A definition theory, with 4 definitions and 8 theorems.  Needed
    by candle_prover_semantics.ml.  *)
(* ======================================================== *)

(*
  Proving that the basis program only produces v_ok values.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_prover_evaluate.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/perms.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_basis_evaluate"
  ["ast_extras"; "candle_kernelProg"; "candle_prover_evaluate";
   "candle_prover_inv"; "evaluate"; "evaluateProps"; "misc"; "ml_prog";
   "namespaceProps"; "perms"; "semanticPrimitives";
   "semanticPrimitivesProps"];;

let simple_exp_def = new_definition
  `candle_basis_evaluate_simple_exp = ast_extras_every_exp (\x.
     match x with
       ast_App op xs -> (match op with
         ast_VfromList -> T
       | ast_Aw8alloc -> T
       | ast_Test _ _ -> T
       | ast_Arith _ _ -> T
       | ast_FromTo _ _ -> T
       | _ -> F)
     | ast_Lit lit -> T
     | ast_Var v -> T
     | ast_Con opt xs -> T
     | _ -> F)`;;

(* HOL4 candle_basis_evaluateScript.sml:39-56: a theorem that HOL4 states as
   the value of an ML expression: simple_exp_simps *)

let simple_pat_def = new_definition
  `simple_pat x1 =
   match x1 with
     ast_Pvar p -> T
   | ast_Pany -> T
   | _ -> F`;;
add_simp simple_pat_def;;

let simple_dec_def = new_definition
  `simple_dec = every_dec (\d.
       match d with
         Dlet l p (ast_Fun n x) -> simple_pat p
       | Dlet l p x -> candle_basis_evaluate_simple_exp x /\ simple_pat p
       | Dletrec l f -> T
       | _ -> T)`;;

let simple_dec_Dlet = prove
 (`simple_dec (Dlet l p x) <=>
     ((?n e. x = (\s t. holSyntax_Tyapp (implode "fun") [s; t]) n e) \/
       candle_basis_evaluate_simple_exp x) /\ simple_pat p`,
  CHEAT_TAC);;
add_simp simple_dec_Dlet;;

(* HOL4 candle_basis_evaluateScript.sml:81-91: a theorem that HOL4 states as
   the value of an ML expression: simple_dec_simps *)

(* HOL4 candle_basis_evaluateScript.sml:93-97: the definition *)

let evaluate_post_state_mono = prove
 (`evaluate s env xs = (s',res) /\
   post_state_ok s' ==>
     post_state_ok s`,
  CHEAT_TAC);;

let evaluate_decs_post_state_mono = prove
 (`!s env ds s' res.
     evaluate_evaluate_decs s env ds = (s',res) /\
     post_state_ok s' ==>
       post_state_ok s`,
  CHEAT_TAC);;

(* HOL4 candle_basis_evaluateScript.sml:128-167: ML code, not ported *)

(* HOL4 candle_basis_evaluateScript.sml:169-191: a theorem whose statement
   the port cannot state yet: evaluate_basis_v_ok *)

(* HOL4 candle_basis_evaluateScript.sml:193-195: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:197-202: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:204-207: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:209-217: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:219-223: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:225-253: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:255-257: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:259-268: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:270-287: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:289-298: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:300-327: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:329-332: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:334-342: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:344-351: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:353-363: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:365-377: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:379: a proof *)

(* HOL4 candle_basis_evaluateScript.sml:381: a theorem that HOL4 states as
   the value of an ML expression: evaluate_basis_v_ok_decs *)

let post_state_ok_with_clock = prove
 (`post_state_ok (semanticPrimitives_state_clock_fupd (K ck) s) =
  post_state_ok s`,
  CHEAT_TAC);;
add_simp post_state_ok_with_clock;;

(* and the interface *)
let _ = unhide_overloads ();;
