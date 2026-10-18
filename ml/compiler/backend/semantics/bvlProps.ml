(* ======================================================== *)
(*  bvlProps: ported from HOL4's
    compiler/backend/semantics/bvlPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about BVL and its semantics
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "semantics/ast.ml";;

(* HOL4 bvlPropsScript.sml:14: the ML values that the definitions
   below antiquote *)

(* HOL4 bvlPropsScript.sml:34-42: ML code, not ported *)

(* HOL4 bvlPropsScript.sml:213-223: a proof *)

(* HOL4 bvlPropsScript.sml:417: a proof *)

let inc_clock_def = cake_define
  `bvlProps_inc_clock ck s = bvlSem_state_clock_fupd (K
  (bvlSem_state_clock s + ck)) s`;;
hol4_overload "inc_clock" "bvlProps_inc_clock";;

let get_vars_def = cake_define_list
  [`bvlProps_get_vars [] env = SOME []`;
   `bvlProps_get_vars (n :: ns) env =
         (if n < LENGTH env then
           (match bvlProps_get_vars ns env with NONE -> NONE |
             SOME vs -> SOME (EL n env :: vs)) else NONE)`];;
hol4_overload "get_vars" "bvlProps_get_vars";;

let isVar_def = cake_define
  `isVar x1 =
        match x1 with
          ((Var n):bvl_exp) -> T
        | _1 -> F`;;

let destVar_def = cake_define
  `(destVar ((Var n):bvl_exp) = n)`;;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let bVarBound_def = cake_define_list_wf
  `MEASURE (list_size bvl_exp_size o SND)`
  [`bVarBound n [] <=> T`;
   `bVarBound n ((x:bvl_exp) :: y :: xs) <=>
         bVarBound n [x] /\ bVarBound n (y :: xs)`;
   `bVarBound n [(Var v:bvl_exp)] <=> v < n`;
   `bVarBound n [(If x1 x2 x3:bvl_exp)] <=>
         bVarBound n [x1] /\ bVarBound n [x2] /\ bVarBound n [x3]`;
   `bVarBound n [(Let xs x2:bvl_exp)] <=>
         bVarBound n xs /\ bVarBound (n + LENGTH xs) [x2]`;
   `bVarBound n [(Raise x1:bvl_exp)] <=> bVarBound n [x1]`;
   `bVarBound n [(Tick x1:bvl_exp)] <=> bVarBound n [x1]`;
   `bVarBound n [(Op op xs:bvl_exp)] <=> bVarBound n xs`;
   `bVarBound n [(Force loc v:bvl_exp)] <=> v < n`;
   `bVarBound n [(Handle x1 x2:bvl_exp)] <=>
         bVarBound n [x1] /\ bVarBound (n + 1) [x2]`;
   `bVarBound n [(Call ticks dest xs:bvl_exp)] <=> bVarBound n xs`];;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let bEvery_def = cake_define_list_wf
  `MEASURE (list_size bvl_exp_size o SND)`
  [`bEvery P [] <=> T`;
   `bEvery P ((x:bvl_exp) :: y :: xs) <=>
         bEvery P [x] /\ bEvery P (y :: xs)`;
   `bEvery P [(Var v:bvl_exp)] <=> P ((Var v:bvl_exp))`;
   `bEvery P [(If x1 x2 x3:bvl_exp)] <=> P ((If x1 x2 x3:bvl_exp)) /\
         bEvery P [x1] /\ bEvery P [x2] /\ bEvery P [x3]`;
   `bEvery P [(Let xs x2:bvl_exp)] <=> P ((Let xs x2:bvl_exp)) /\
         bEvery P xs /\ bEvery P [x2]`;
   `bEvery P [(Raise x1:bvl_exp)] <=> P ((Raise x1:bvl_exp)) /\
  bEvery P [x1]`;
   `bEvery P [(Tick x1:bvl_exp)] <=> P ((Tick x1:bvl_exp)) /\ bEvery
  P [x1]`;
   `bEvery P [(Force m n:bvl_exp)] <=> P ((Force m n:bvl_exp))`;
   `bEvery P [(Op op xs:bvl_exp)] <=> P ((Op op xs:bvl_exp)) /\
  bEvery P xs`;
   `bEvery P [(Handle x1 x2:bvl_exp)] <=> P ((Handle x1 x2:bvl_exp)) /\
         bEvery P [x1] /\ bEvery P [x2]`;
   `bEvery P [(Call ticks dest xs:bvl_exp)] <=> P ((Call ticks dest
  xs:bvl_exp)) /\ bEvery P xs`];;

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvlPropsScript.sml:888-895: the tactic that proves the
   termination *)
let get_code_labels_def = cake_define_list_try (fun () ->
  `MEASURE flatLang_exp_size`)
  [`bvlProps_get_code_labels (bvl_Var _2) = {}`;
   `bvlProps_get_code_labels (If e1 e2 e3:bvl_exp) =
  bvlProps_get_code_labels e1 UNION bvlProps_get_code_labels e2 UNION
  bvlProps_get_code_labels e3`;
   `bvlProps_get_code_labels (Let es e:bvl_exp) = BIGUNION
  (set_of_list (MAP bvlProps_get_code_labels es)) UNION
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (Raise e:bvl_exp) =
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (Handle e1 e2:bvl_exp) =
  bvlProps_get_code_labels e1 UNION bvlProps_get_code_labels e2`;
   `bvlProps_get_code_labels (Tick e:bvl_exp) =
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (Force loc v:bvl_exp) = {loc}`;
   `bvlProps_get_code_labels (Call _4 d es:bvl_exp) = (match d with
  NONE -> {} | SOME n -> {n}) UNION BIGUNION (set_of_list (MAP
  bvlProps_get_code_labels es))`;
   `bvlProps_get_code_labels (Op op es:bvl_exp) =
  assign_get_code_label op UNION BIGUNION (set_of_list (MAP
  bvlProps_get_code_labels es))`];;
hol4_overload "get_code_labels" "bvlProps_get_code_labels";;
