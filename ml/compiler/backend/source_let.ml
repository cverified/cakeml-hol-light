(* ======================================================== *)
(*  source_let: ported from HOL4's
    compiler/backend/source_letScript.sml  *)
(* ======================================================== *)

(*
  This is a source-to-source transformation that lifts Let/Letrec
    expressions
  that sit at the top of Dlet:s into their own Dlet/Dletrec:s.
 *)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;


(* HOL4 overload (expanded in the port):
     string_size = list_size char_size *)

let dest_Let_def = cake_define
  `dest_Let x1 =
      match x1 with
        Let opt x y -> SOME (opt,x,y)
      | _1 -> NONE`;;

let dest_Letrec_def = cake_define
  `dest_Letrec x1 =
      match x1 with
        Letrec funs x -> SOME (funs,x)
      | _2 -> NONE`;;

let lift_let_def = cake_define
  `lift_let x1 =
        match x1 with
          Dlet l p x ->
       (match dest_Let x with SOME (NONE,x,y) -> SOME (Dlet l Pany
         x,Dlet l p y) | SOME (SOME m,x,y) -> SOME (Dlet l (Pvar m)
         x,Dlet l p y) | NONE ->
           (match dest_Letrec x with SOME (funs,x) -> SOME (Dletrec l
             funs,Dlet l p x) | NONE -> NONE))
        | _3 -> NONE`;;

(* TERMINATION: wf_rel_tac ‘measure (dec_size o SND)’
  \\ Cases_on ‘d’ \\ rw [lift_let_def]
  \\ gvs [CaseEqs ["option", "prod"], dec_size_def, exp_size_def,
          dest_Let_SOME, dest_Letrec_SOME] *)
let lift_lets_def = cake_define
  `lift_lets sofar d =
     (match lift_let d with NONE ->
         (match sofar with [] -> NONE | _4 -> SOME (REVERSE
           sofar,d)) | SOME (d1,d2) -> lift_lets (d1 :: sofar) d2)`;;

(* TERMINATION: wf_rel_tac ‘measure (list_size dec_size)’ *)
let compile_decs_def = cake_define
  `(source_let_compile_decs [] = []) /\
   (source_let_compile_decs (d :: ds) =
     (match lift_lets [] d with SOME (pre,d) -> Dlocal pre [d] ::
       source_let_compile_decs ds | NONE ->
         (match d with Dmod mn ds1 ->
             Dmod mn (source_let_compile_decs ds1) ::
               source_let_compile_decs ds | Dlocal ds1 ds2 ->
             Dlocal (source_let_compile_decs ds1)
               (source_let_compile_decs ds2) ::
               source_let_compile_decs ds | _6 -> d ::
               source_let_compile_decs ds)))`;;
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
          (Letrec [("bar", "x", App Opapp [Var (Short "baz"); Con NONE
            []])]
                  (Var (Short "glob")))] []
    ]”;
val test5 = EVAL “
  compile_decs [
    Dlet l (Pvar "foo") (Var (Short "bar"))
    ]”;
 *)
