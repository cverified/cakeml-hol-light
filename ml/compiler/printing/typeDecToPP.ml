(* ======================================================== *)
(*  typeDecToPP: ported from HOL4's
    compiler/printing/typeDecToPPScript.sml
    A definition theory, with 13 definitions and no theorems.
    Needed by addPrintVals.ml and printTweaks.ml.  *)
(* ======================================================== *)

(*
   Maps a Dtype or Dtabbrev declaration (the ast syntax) to
   the default pretty-printer function definition for it
   (also as ast syntax).

   Used by the compiler (in add-pp mode) to set up default
   pretty-printers for user types and by the basis translation
   to set up default pretty-printers for some basis types.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlprettyprinter.ml";;
needs "basis/pure/mlstring.ml";;
needs "lib/indexedLists.ml";;
needs "lib/location.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "typeDecToPP"
  ["ast"; "mlint"; "mlstring"];;


let pppre_def = new_definition
  `pppre nm = strcat (implode "pp_") nm`;;

(* the clauses in two quotations: nm is 'n and 'm, which one quotation cannot
   typecheck *)
let pp_prefix_def,pp_prefix_ind = define_guess_clauses
  [`pp_prefix (Short nm) = Short (pppre nm)`;
   `pp_prefix (Long nm id) = Long nm (pp_prefix id)`];;

(* FIXME: is this elsewhere? *)
let mk_list_exp_def,mk_list_exp_ind = define_guess
  `(mk_list_exp [] = ast_Con (SOME (Short (implode "[]"))) []) /\
   (mk_list_exp (CONS x xs) = ast_Con (SOME (Short (implode "::"))) [x;
    mk_list_exp xs])`;;

let con_x_i_pat_def = new_definition
  `con_x_i_pat cname n =
     ast_Pcon cname (list_of_seq (\i. ast_Pvar (strcat (implode "x")
       (mlint_toString (&i)))) n)`;;

let x_i_list_f_apps_def = new_definition
  `x_i_list_f_apps fs = mk_list_exp
     (MAPi (\i f. ast_App ast_Opapp [f; ast_Var (Short (strcat (implode
       "x") (mlint_toString (&i))))]) fs)`;;

let mod_pp_def = new_definition
  `mod_pp nm = Long (implode "PrettyPrinter") nm`;;

let id_to_str_def,id_to_str_ind = define_guess
  `(id_to_str (Short s) = s) /\
   (id_to_str (Long mnm id) = (strcat (strcat mnm (implode "."))
    (id_to_str id)))`;;

(* Avoids MAP (pp_of_ast_t fixes) so it is possible to use cv_trans *)
(* the clauses in two quotations: nm is tvarN and ((modN , typeN) id); ts is
   (ast_t list) and (_)list; xs is (ast_t list) and (_)list, which one
   quotation cannot typecheck *)
let pp_of_ast_t_def,pp_of_ast_t_ind = define_guess_clauses
  [`(pp_of_ast_t fixes (Atvar nm) = (ast_Var (pp_prefix (Short nm)))) /\
    (pp_of_ast_t fixes (Atfun _ _) = (ast_Fun (implode "x") (ast_Var (Short
    (implode "pp_fun"))))) /\
    (pp_of_ast_t fixes (Attup ts) = (ast_Fun (implode "x") (ast_App ast_Opapp
      [ast_Var (mod_pp (Short (implode "tuple"))); ast_Mat (ast_Var (Short
          (implode "x")))
          [(con_x_i_pat NONE (LENGTH ts),x_i_list_f_apps (pp_of_ast_ts
              fixes ts))]]))) /\
    (pp_of_ast_ts fixes [] = []) /\
    (pp_of_ast_ts fixes (CONS h tl) = CONS (pp_of_ast_t fixes h)
    (pp_of_ast_ts fixes tl))`;
   `pp_of_ast_t fixes (Atapp xs nm) = (match nsLookup fixes nm with
        NONE -> Apps (ast_Var (pp_prefix nm)) (pp_of_ast_ts fixes xs)
      | SOME NONE -> (ast_Fun (implode "x") (ast_App ast_Opapp
              [ast_Var (mod_pp (Short (implode "unprintable"))); ast_Lit
                  (ast_StrLit (id_to_str nm))]))
      | SOME (SOME nm2) -> Apps (ast_Var (pp_prefix nm2)) (pp_of_ast_ts
          fixes xs))`];;

let mk_pps_for_type_def = new_definition
  `mk_pps_for_type fixes (tvars',nm,conss) =
     let (v,exp) = ITLIST (\nm (v,exp). (pppre nm,ast_Fun v exp)) tvars'
         ((implode "x"),ast_Mat (ast_Var (Short (implode "x")))
             (MAP (\(conN,ts). (con_x_i_pat (SOME (Short conN)) (LENGTH ts),
                 Apps (ast_Var (mod_pp (Short (implode "app_block"))))
                   [ast_Lit (ast_StrLit conN);
                     (x_i_list_f_apps (MAP (pp_of_ast_t fixes) ts))]))
                       conss)) in
     (pppre nm,v,exp)`;;

let mk_pp_type_def = new_definition
  `mk_pp_type fixes (funs:(mlstring list#mlstring#(mlstring#ast_t list)
  list) list) = Dletrec unknown_loc (MAP (mk_pps_for_type fixes) funs)`;;

let mk_pp_tabbrev_def = new_definition
  `mk_pp_tabbrev fixes tvars' nm ast_t =
   let body = ITLIST (\nm exp. ast_Fun (pppre nm) exp) tvars' (pp_of_ast_t
     fixes ast_t) in
     // eta-expansion to avoid value restriction violations
     Dlet unknown_loc (ast_Pvar (pppre nm)) (ast_Fun (implode "x")
       (ast_App ast_Opapp [body; ast_Var (Short (implode "x"))]))`;;

let pps_for_dec_def = new_definition
  `pps_for_dec fixes dec =
   match dec with
     Dtype locs type_def -> [mk_pp_type fixes type_def]
   | Dtabbrev locs tvars' nm ast_t -> [mk_pp_tabbrev fixes tvars' nm ast_t]
   | dec -> []`;;

(* the termination relation that HOL4 gives is
     MEASURE (list_size dec_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let add_pp_decs_def,add_pp_decs_ind = define_guess
  `add_pp_decs fixes x2 =
   match x2 with
     [] -> []
   | CONS (Dmod modN decs) decs2 -> CONS (Dmod modN (add_pp_decs fixes
     decs)) (add_pp_decs fixes decs2)
   | CONS (Dlocal ldecs decs) decs2 -> CONS (Dlocal (add_pp_decs fixes
     ldecs) (add_pp_decs fixes decs)) (add_pp_decs fixes decs2)
   | CONS d decs -> APPEND (CONS d (pps_for_dec fixes d)) (add_pp_decs
     fixes decs)`;;

(* and the interface *)
let _ = unhide_overloads ();;
