(* ======================================================== *)
(*  source_let: ported from HOL4's
    compiler/backend/source_letScript.sml
    A definition theory, with 5 definitions and 4 theorems.  Needed
    by source_letProof.ml and source_to_source.ml.  *)
(* ======================================================== *)

(*
  This is a source-to-source transformation that lifts Let/Letrec expressions
  that sit at the top of Dlet:s into their own Dlet/Dletrec:s.
 *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "source_let"
  ["ast"; "evaluate"; "misc"];;


(* HOL4 source_letScript.sml:12: the overload string_size, which the
   port expands *)

let dest_Let_def = new_definition
  `dest_Let x1 =
      match x1 with
        (ast_Let opt x y:ast_exp) -> SOME (opt,x,y)
      | _1 -> NONE`;;

let dest_Let_SOME = prove
 (`dest_Let z = SOME (opt,x,y) <=> z = ast_Let opt x y`,
  CHEAT_TAC);;

let dest_Let_NONE = prove
 (`dest_Let z = NONE <=> (!opt x y. ~(z = ast_Let opt x y))`,
  CHEAT_TAC);;

let dest_Letrec_def = new_definition
  `dest_Letrec x1 =
      match x1 with
        (ast_Letrec funs x:ast_exp) -> SOME (funs,x)
      | _2 -> NONE`;;

let dest_Letrec_SOME = prove
 (`dest_Letrec z = SOME (funs,x) <=> z = ast_Letrec funs x`,
  CHEAT_TAC);;

let dest_Letrec_NONE = prove
 (`dest_Letrec z = NONE <=> (!funs x. ~(z = ast_Letrec funs x))`,
  CHEAT_TAC);;

let lift_let_def = new_definition
  `lift_let x1 =
        match x1 with
          Dlet l p x ->
       (match dest_Let x with SOME (NONE,x,y) -> SOME (Dlet l
         ast_Pany x,Dlet l p y) | SOME (SOME m,x,y) -> SOME (Dlet l
         (ast_Pvar m) x,Dlet l p y) | NONE ->
           (match dest_Letrec x with SOME (funs,x) -> SOME (Dletrec l
             funs,Dlet l p x) | NONE -> NONE))
        | _3 -> NONE`;;

(* the termination relation that HOL4 gives is
     MEASURE (dec_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 source_letScript.sml:68-73: the tactic that proves the
   termination *)
let lift_lets_def,lift_lets_ind = define_guess
  [`lift_lets sofar d =
     (match lift_let d with NONE ->
         (match sofar with [] -> NONE | _4 -> SOME (REVERSE
           sofar,d)) | SOME (d1,d2) -> lift_lets (d1 :: sofar) d2)`];;

let _ = size_thms "dec";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let source_let_compile_decs_def,source_let_compile_decs_ind = define_wf
  `MEASURE (list_size dec_size)`
  [`source_let_compile_decs [] = []`;
   `source_let_compile_decs (d :: ds) =
        (match lift_lets [] d with SOME (pre,d) -> Dlocal pre [d] ::
          source_let_compile_decs ds | NONE ->
            (match d with Dmod mn ds1 ->
                Dmod mn (source_let_compile_decs ds1) ::
                  source_let_compile_decs ds | Dlocal ds1 ds2 ->
                Dlocal (source_let_compile_decs ds1)
                  (source_let_compile_decs ds2) ::
                  source_let_compile_decs ds | _6 -> d ::
                  source_let_compile_decs ds))`];;
hol4_overload "compile_decs" "source_let_compile_decs";;

(*
val test3 = EVAL “
  compile_decs [
    Dlet l (Pvar "foo")
      (Letrec [("bar", "x", App Opapp [Var (Short "baz"); Con NONE []])]
              (Var (Short "glob")))]”;
val test4 = EVAL “
  compile_decs [
    Dlocal [
        Dlet l (Pvar "foo")
          (Letrec [("bar", "x", App Opapp [Var (Short "baz"); Con NONE []])]
                  (Var (Short "glob")))] []
    ]”;
val test5 = EVAL “
  compile_decs [
    Dlet l (Pvar "foo") (Var (Short "bar"))
    ]”;
 *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
