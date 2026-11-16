(* ======================================================== *)
(*  printTweaks: ported from HOL4's
    compiler/printing/printTweaksScript.sml
    A definition theory, with 7 definitions and 11 theorems.  Needed
    by printingProg.ml and repl_check_and_tweak.ml.  *)
(* ======================================================== *)

(*
   The top-level printing adjustment, as called by the REPL.
*)

needs "basis/pure/mlsexp.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/printing/addPrintVals.ml";;
needs "compiler/printing/typeDecToPP.ml";;
needs "lib/location.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "printTweaks"
  ["addPrintVals"; "infer"; "ml_monadBase"; "typeDecToPP"];;

let print_failure_message_def = new_definition
  `print_failure_message (s:mlstring) =
   Dlet unknown_loc ast_Pany (ast_App ast_Opapp [ast_Var (Short (implode
     "print_pp"));
         (ast_App ast_Opapp [ast_Var (Long (implode "PrettyPrinter") (Short
           (implode "failure_message")));
             ast_Lit (ast_StrLit s)])])`;;

let add_err_message_def = new_definition
  `add_err_message s decs_ext st =
   // something's gone wrong, try to add a message
   let (ienv,inf_st) = st in
   let pmsg = [print_failure_message s] in
   match infer_ds ienv pmsg inf_st with (M_success msg_ienv,inf_st2) ->
         (APPEND pmsg decs_ext,(extend_dec_ienv msg_ienv ienv,inf_st2))
   | (
      // if even that fails, skip it
      M_failure _,_) -> (decs_ext,(ienv,inf_st))`;;

let add_print_from_opts_def,add_print_from_opts_ind = define_guess
  `(add_print_from_opts nm [] (decs_ext,st) =
    add_err_message (strcat (implode "exhausted print options for ")
        nm) decs_ext st) /\
   (add_print_from_opts nm (CONS print_opt xs) (decs_ext,st) =
    let (ienv,inf_st) = st in
    match infer_ds ienv [print_opt] inf_st with (M_success ienv2,inf_st2)
        ->
          (CONS print_opt decs_ext,(extend_dec_ienv ienv2 ienv,inf_st2))
    | (M_failure x,_) ->
    let (decs_ext,st) = add_err_message
          (strcat (implode "adding val pretty-print: ") (SND x)) decs_ext
              st in
    add_print_from_opts nm xs (decs_ext,st))`;;

(* really just FOLDR but the translator can't get that right *)
let add_prints_from_opts_def,add_prints_from_opts_ind = define_guess
  `(add_prints_from_opts [] decs_plus_st = decs_plus_st) /\
   (add_prints_from_opts (CONS (nm,opts) xs) decs_plus_st =
    add_prints_from_opts xs (add_print_from_opts nm opts decs_plus_st))`;;

let add_print_features_def = new_definition
  `add_print_features st decs =
   (let (tn,ienv,next_id) = st in
   let decs2 = add_pp_decs (addPrintVals_type_names_pp_fixes tn) decs in
   match infer_ds ienv decs2 (init_infer_state (mk_infer_st ARB ARB
     next_id)) with
   (M_success decs_ienv,inf_st) ->
   let (prints,tn2) = val_prints tn ienv decs_ienv in
   let ienv2 = extend_dec_ienv decs_ienv ienv in
   let (print_decs_ext,i_st) = add_prints_from_opts prints
     ([],(ienv2,inf_st)) in
   (M_success (APPEND decs2 (REVERSE print_decs_ext),(tn2,i_st)))
   | (M_failure x,_) ->
   (
    // maybe the default pretty-printer decs are the problem
    match infer_ds ienv decs (init_infer_state (mk_infer_st ARB ARB
      next_id)) with
   (M_success ienv3,inf_st3) ->
   let (decs_ext,i_st) = add_err_message (strcat (implode
     "adding type pp funs: ") (SND x))
         [] (extend_dec_ienv ienv3 ienv,inf_st3) in
   (M_success (APPEND decs (REVERSE decs_ext),(tn,i_st)))
   | (M_failure x,_) -> M_failure x))`;;

let read_next_dec_def = new_definition
  `read_next_dec =
     [Dlet (Locs UNKNOWNpt UNKNOWNpt) ast_Pany
        (ast_App ast_Opapp
           [ast_App ast_Opderef [ast_Var (Long (implode "Repl") (Short
             (implode "readNextString")))];
            ast_Con NONE []])]`;;

let add_print_then_read_def = new_definition
  `add_print_then_read types' decs =
     (match add_print_features types' decs with M_failure x -> M_failure x
     | M_success (new_decs,(tn,ienv,inf_st)) ->
         (match infer_ds ienv read_next_dec inf_st with (M_success
           read_ienv,inf_st2) ->
             (M_success (APPEND new_decs read_next_dec,
                       (tn,extend_dec_ienv read_ienv ienv,infer_st_next_id
                         inf_st2)))
         | (M_failure x,_) -> M_failure x))`;;

(* HOL4 printTweaksScript.sml:91-93: a theorem that HOL4 states as the value
   of an ML expression: eq_inf_x *)

let infer_ds_append = prove
 (`!xs ys ienv st. infer_ds ienv (APPEND xs ys) st =
   (match infer_ds ienv xs st with
     (M_failure x,y) -> (M_failure x,y)
   | (M_success ienv2,st2) ->
   (match infer_ds (extend_dec_ienv ienv2 ienv) ys st2 with
     (M_failure x,y) -> (M_failure x,y)
   | (M_success ienv3,st3) -> (M_success (extend_dec_ienv ienv3
     ienv2),st3)))`,
  CHEAT_TAC);;

let add_err_message_infer = prove
 (`add_err_message s decs_ext (extend_dec_ienv ienv init_ienv,inf_st) =
     (decs_ext2,st2) /\
   infer_ds init_ienv (REVERSE decs_ext) init_inf_st = (M_success
     ienv,inf_st) ==>
   (?ienv_res inf_st2 ienv2.
   st2 = (ienv_res,inf_st2) /\
   infer_ds init_ienv (REVERSE decs_ext2) init_inf_st = (M_success
     ienv2,inf_st2) /\
   ienv_res = extend_dec_ienv ienv2 init_ienv)`,
  CHEAT_TAC);;

let add_print_from_opts_infer = prove
 (`!opts decs_ext ienv inf_st decs_ext2 ienv_res inf_st2.
   add_print_from_opts nm opts (decs_ext,(extend_dec_ienv ienv
     init_ienv,inf_st)) =
     (decs_ext2,st2) /\
   infer_ds init_ienv (REVERSE decs_ext) init_inf_st = (M_success
     ienv,inf_st) ==>
   (?ienv_res inf_st2 ienv2.
   st2 = (ienv_res,inf_st2) /\
   infer_ds init_ienv (REVERSE decs_ext2) init_inf_st = (M_success
     ienv2,inf_st2) /\
   ienv_res = extend_dec_ienv ienv2 init_ienv)`,
  CHEAT_TAC);;

(* [local] *)
let add_prints_from_opts_infer = prove
 (`!opts decs_ext ienv inf_st decs_ext2 st2 ienv_res inf_st2.
   add_prints_from_opts opts
     (decs_ext,(extend_dec_ienv ienv init_ienv,inf_st)) =
     (decs_ext2,st2) /\
   infer_ds init_ienv (REVERSE decs_ext) init_inf_st = (M_success
     ienv,inf_st) ==>
   (?ienv_res inf_st2 ienv2.
   st2 = (ienv_res,inf_st2) /\
   infer_ds init_ienv (REVERSE decs_ext2) init_inf_st = (M_success
     ienv2,inf_st2) /\
   ienv_res = extend_dec_ienv ienv2 init_ienv)`,
  CHEAT_TAC);;

(* [local] *)
let extend_none = prove
 (`extend_dec_ienv (mk_inf_env nsEmpty nsEmpty nsEmpty) ienv = ienv`,
  CHEAT_TAC);;

(* [local] *)
let add_err_message_infer2 =
  SIMP_RULE [infer_d_def; st_ex_return_def; extend_none] (CAKE_SPEC `[]`
  (CAKE_GENL [`decs_ext`; `ienv`; `inf_st`] add_err_message_infer));;

(* [local] *)
let add_prints_from_opts_infer2 =
  SIMP_RULE [infer_d_def; st_ex_return_def; extend_none] (CAKE_SPECL [`xs`;
  `[]`] add_prints_from_opts_infer);;

let add_print_features_succ = prove
 (`add_print_features st decs = (M_success (decs2,st2)) ==>
   (?tn ienv next_id tn2 ienv2 inf_st2.
   st = (tn,ienv,next_id) /\ st2 = (tn2,extend_dec_ienv ienv2 ienv,inf_st2)
     /\
   infer_ds ienv decs2 (init_infer_state (mk_infer_st ARB ARB next_id)) =
     (M_success ienv2,inf_st2))`,
  CHEAT_TAC);;

let add_print_then_read_succ = prove
 (`add_print_then_read st decs = (M_success (decs2,st2)) ==>
   (?tn ienv next_id tn2 ienv2 inf_st2.
   st = (tn,ienv,next_id) /\ st2 = (tn2,extend_dec_ienv ienv2
     ienv,infer_st_next_id inf_st2) /\
   infer_ds ienv decs2 (init_infer_state (mk_infer_st ARB ARB next_id)) =
     (M_success ienv2,inf_st2))`,
  CHEAT_TAC);;

(* preservation of inference invariants will be needed in translation *)
let print_features_infer_st_invs = prove
 (`(!env ds st x st2. infer_ds env ds st = (M_success x,st2) /\ P st ==> P st2)
  ==>
   (!s ds env inf_st x y.
     add_err_message s ds (env,inf_st) = (x,y) /\ P inf_st ==>
         P (SND y)) /\
   (!opts nm ds env inf_st x y.
   add_print_from_opts nm opts (ds,(env,inf_st)) = (x,y) /\ P inf_st ==>
     P (SND y)) /\
   (!xs ds env inf_st x y.
   add_prints_from_opts xs (ds,(env,inf_st)) = (x,y) /\ P inf_st ==>
     P (SND y)) /\
   (!st ds x. add_print_features st ds = M_success x /\
     P (init_infer_state (mk_infer_st ARB ARB (SND (SND st)))) ==> P (SND
       (SND (SND x))))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
