(* ======================================================== *)
(*  repl_decs_allowed: ported from HOL4's
    compiler/repl/repl_decs_allowedScript.sml
    A definition theory, with 1 definition and 2 theorems.  Needed
    by 6 files of the port.  *)
(* ======================================================== *)

(*
  The REPL puts some restrictions on what decs are acceptable as user input.
  This file defines what those restrictions are.
*)

needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "repl_decs_allowed"
  ["candle_prover_inv"; "evaluate"; "semanticPrimitives"; "semanticsProps"];;

let _ = do_list hide_constant ["id"];;

let _ = do_list hide_constant ["types"];;

(* definition *)

let decs_allowed_def = new_definition
  `decs_allowed (decs:dec list) = ALL safe_dec decs`;;

(* pmatch lemmas *)

(* [local] *)
let safe_exp_pmatch_lemma = prove
 (`safe_exp =
      ast_extras_every_exp (\x. match x with ast_Con opt xs -> (match opt
        with SOME id -> let n = id_to_n id in ~(n IN kernel_ctors)
                              | NONE -> T)
                      | ast_App op xs' -> ~(op = ast_FFI kernel_ffi)
                      | _ -> T)`,
  CHEAT_TAC);;

let safe_exp_pmatch =
  SIMP_RULE [kernel_ctors_def; kernel_ffi_def; IN_UNION; IN_INSERT;
  NOT_IN_EMPTY; GSYM CONJ_ASSOC] safe_exp_pmatch_lemma;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id";
   "types"];;

(* and the interface *)
let _ = unhide_overloads ();;
