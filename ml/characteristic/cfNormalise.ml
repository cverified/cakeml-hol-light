(* ======================================================== *)
(*  cfNormalise: ported from HOL4's
    characteristic/cfNormaliseScript.sml
    A definition theory, with 3 definitions and 6 theorems.  Needed
    by cf.ml, cfApp.ml, cfDiv.ml and cfTactics.ml.  *)
(* ======================================================== *)

(*
  Defines the normalise_prog function which puts an arbitrary program
  in A-normal form.
*)

needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeaps.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/set_sep.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfNormalise"
  ["cfHeaps"; "cfHeapsBase"; "cfStore"; "evaluate"; "ml_translator";
   "semanticPrimitives"];;

(*------------------------------------------------------------------*)
(** The [cf] function assumes that programs are in "normal form"
    (which is close to ANF). These lemmas exploit the fact that some
    program is in normal form.

    The [cfNormaliseLib.normalise_prog] function puts an arbitrary
    program in normal form.
*)

let exp2v_def = new_definition
  `exp2v env x2 =
   match x2 with
     ast_Lit l -> SOME (semanticPrimitives_Litv l)
   | ast_Var name -> nsLookup (sem_env_v env) name
   | _ -> NONE`;;

let exp2v_evaluate = prove
 (`!e env st v. exp2v env e = SOME v ==>
    evaluate st env [e] = (st,Rval [v])`,
  CHEAT_TAC);;

let exp2v_list_def,exp2v_list_ind = define_guess
  `(exp2v_list env [] = SOME []) /\
   (exp2v_list env (CONS x xs) =
      (match exp2v env x with NONE -> NONE
        | SOME v ->
          (match exp2v_list env xs with NONE -> NONE
            | SOME vs -> SOME (CONS v vs))))`;;

let exp2v_list_evaluate = prove
 (`!l lv env st. exp2v_list env l = SOME lv ==>
    evaluate st env l = (st,Rval lv)`,
  CHEAT_TAC);;

let evaluate_rcons = prove
 (`!env st st' st'' l x lv v.
     evaluate st env l = (st',Rval lv) /\
     evaluate st' env [x] = (st'',Rval [v]) ==>
     evaluate st env (APPEND l [x]) = (st'',Rval (APPEND lv [v]))`,
  CHEAT_TAC);;

let exp2v_list_REVERSE = prove
 (`!l (st:'ffi semanticPrimitives_state) lv env. exp2v_list env l = SOME lv ==>
    evaluate st env (REVERSE l) = (st,Rval (REVERSE lv))`,
  CHEAT_TAC);;

let exp2v_list_rcons = prove
 (`!xs x l env.
     exp2v_list env (APPEND xs [x]) = SOME l ==>
     (?xvs xv.
       l = APPEND xvs [xv] /\
       exp2v_list env xs = SOME xvs /\
       exp2v env x = SOME xv)`,
  CHEAT_TAC);;

let exp2v_list_LENGTH = prove
 (`!l lv env. exp2v_list env l = SOME lv ==> LENGTH l = LENGTH lv`,
  CHEAT_TAC);;

(* [dest_opapp]: destruct an n-ary application. *)
let dest_opapp_def,dest_opapp_ind = define_guess
  `dest_opapp x1 =
   match x1 with
     ast_App ast_Opapp l ->
        (match l with [f; x] ->
             (match dest_opapp f with SOME (f',args) -> SOME (f',APPEND args
               [x])
                | NONE -> SOME (f,[x]))
           | _ -> NONE)
   | _ -> NONE`;;

(*------------------------------------------------------------------*)

(* HOL4 cfNormaliseScript.sml:132-522: code that the source has in a comment *)

(* and the interface *)
let _ = unhide_overloads ();;
