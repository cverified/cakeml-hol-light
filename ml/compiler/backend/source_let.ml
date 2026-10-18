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


(* HOL4 source_letScript.sml:12: the overload string_size, which the
   port expands *)

let dest_Let_def = cake_define
  `dest_Let x1 =
      match x1 with
        (ast_Let opt x y:ast_exp) -> SOME (opt,x,y)
      | _1 -> NONE`;;

let dest_Let_SOME = cake_theorem "dest_Let_SOME"
  (fun () ->
    `dest_Let z = SOME (opt,x,y) <=> z = ast_Let opt x y`)
  CHEAT_TAC;;

let dest_Let_NONE = cake_theorem "dest_Let_NONE"
  (fun () ->
    `dest_Let z = NONE <=> (!opt x y. ~(z = ast_Let opt x y))`)
  CHEAT_TAC;;

let dest_Letrec_def = cake_define
  `dest_Letrec x1 =
      match x1 with
        (ast_Letrec funs x:ast_exp) -> SOME (funs,x)
      | _2 -> NONE`;;

let dest_Letrec_SOME = cake_theorem "dest_Letrec_SOME"
  (fun () ->
    `dest_Letrec z = SOME (funs,x) <=> z = ast_Letrec funs x`)
  CHEAT_TAC;;

let dest_Letrec_NONE = cake_theorem "dest_Letrec_NONE"
  (fun () ->
    `dest_Letrec z = NONE <=> (!funs x. ~(z = ast_Letrec funs x))`)
  CHEAT_TAC;;

let lift_let_def = cake_define
  `lift_let x1 =
        match x1 with
          Dlet l p x ->
       (match dest_Let x with SOME (NONE,x,y) -> SOME (Dlet l
         ast_Pany x,Dlet l p y) | SOME (SOME m,x,y) -> SOME (Dlet l
         (ast_Pvar m) x,Dlet l p y) | NONE ->
           (match dest_Letrec x with SOME (funs,x) -> SOME (Dletrec l
             funs,Dlet l p x) | NONE -> NONE))
        | _3 -> NONE`;;

let _ = size_thms "dec";;
(* HOL4 source_letScript.sml:68-73: the tactic that proves the
   termination *)
let lift_lets_def = cake_define_wf
  `MEASURE (dec_size o SND)`
  `lift_lets sofar d =
     (match lift_let d with NONE ->
         (match sofar with [] -> NONE | _4 -> SOME (REVERSE
           sofar,d)) | SOME (d1,d2) -> lift_lets (d1 :: sofar) d2)`;;

let _ = size_thms "dec";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let compile_decs_def = cake_define_list_try (fun () ->
  `MEASURE (list_size dec_size)`)
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

(* HOL4 source_letScript.sml:91-108: code that the source has in a
   comment *)
