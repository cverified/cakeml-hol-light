(* ======================================================== *)
(*  holAxiomsSyntax: ported from HOL4's
    candle/standard/syntax/holAxiomsSyntaxScript.sml
    A definition theory, with 3 definitions and 4 theorems.  Needed
    by holAxioms.ml, holConsistency.ml, holLightConsistency.ml and
    ml_hol_kernel_funsProg.ml.  *)
(* ======================================================== *)

(*
  Context extensions for asserting the mathematical axioms.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holAxiomsSyntax"
  ["holBoolSyntax"; "holSyntax"; "holSyntaxExtra"; "holSyntaxLib"];;

let _ = do_list hide_constant ["Bool"; "Fun"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holAxiomsSyntaxScript.sml:14: the ML values that the definitions
   below antiquote *)

(* HOL4 holAxiomsSyntaxScript.sml:16: the overload A, which the port expands *)
(* HOL4 holAxiomsSyntaxScript.sml:17: the overload B, which the port expands *)
(* HOL4 holAxiomsSyntaxScript.sml:18: the overload x, which the port expands *)
(* HOL4 holAxiomsSyntaxScript.sml:19: the overload g, which the port expands *)

(* ETA_AX *)
let mk_eta_ctxt_def = new_definition
  `mk_eta_ctxt ctxt = CONS (NewAxiom ((===) (holSyntax_Abs (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
  (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))
  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))))
  (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))))
  ctxt`;;

let eta_extends = prove
 (`!ctxt. is_std_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
  ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
  ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) ==> extends
  (mk_eta_ctxt ctxt) ctxt`,
  CHEAT_TAC);;

(* HOL4 holAxiomsSyntaxScript.sml:36: the overload Select, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:37: the overload P, which the port expands *)

(* SELECT_AX *)
let mk_select_ctxt_def = new_definition
  `mk_select_ctxt ctxt = CONS (NewAxiom ((\p1 p2. holSyntax_Comb
  (holSyntax_Comb (holSyntax_Const (implode "==>") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
  (holSyntax_Tyapp (implode "bool") [])))) p1) p2) (holSyntax_Comb
  (holSyntax_Var (implode "P") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode "bool") [])))
  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))))
  (holSyntax_Comb (holSyntax_Var (implode "P") ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode
  "bool") []))) (holSyntax_Comb ((\ty. holSyntax_Const (implode "@") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])) ty))
  (holSyntax_Tyvar (implode "A"))) (holSyntax_Var (implode "P") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
  (holSyntax_Tyapp (implode "bool") []))))))) (CONS (NewConst (implode "@")
  ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Tyvar (implode "A"))))
     ctxt)`;;

let select_extends = prove
 (`!ctxt.
    is_std_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
      ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
      ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) /\ ~((implode
      "@") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
      ctxt)) ctxt)) ctxt)) /\
           (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
             consts_of_upd ctxt)) ctxt)) ctxt) (implode "==>") = SOME ((\s t.
             holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
             (implode "bool") []) ((\s t. holSyntax_Tyapp (implode "fun") [s;
             t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
             (implode "bool") [])))) ==> extends (mk_select_ctxt ctxt) ctxt`,
  CHEAT_TAC);;

(* HOL4 holAxiomsSyntaxScript.sml:62: the overload B, which the port expands *)
(* HOL4 holAxiomsSyntaxScript.sml:63: the overload One_One, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:64: the overload Onto, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:65: the overload Ind, which the port
   expands *)

(* HOL4 holAxiomsSyntaxScript.sml:67: the overload EXx, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:68: the overload x1, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:69: the overload FAx1, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:70: the overload x2, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:71: the overload FAx2, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:72: the overload y, which the port expands *)
(* HOL4 holAxiomsSyntaxScript.sml:73: the overload FAy, which the port
   expands *)
(* HOL4 holAxiomsSyntaxScript.sml:74: the overload h, which the port expands *)
(* HOL4 holAxiomsSyntaxScript.sml:75: the overload Exh, which the port
   expands *)

 (* INFINITY_AX *)
let mk_infinity_ctxt_def = new_definition
  `mk_infinity_ctxt ctxt = CONS (NewAxiom (((\x ty p. holSyntax_Comb
  (holSyntax_Const (implode "?") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
  (holSyntax_Var x ty) p)) (implode "f") ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyapp (implode "ind") []) (holSyntax_Tyapp (implode
  "ind") []))) ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
  (implode "/\\") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode
  "bool") [])))) p1) p2) ((\f. holSyntax_Comb (holSyntax_Const (implode
  "ONE_ONE") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (typeof f)
  (holSyntax_Tyapp (implode "bool") []))) f) (holSyntax_Var (implode "f") ((\s
  t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "ind")
  []) (holSyntax_Tyapp (implode "ind") [])))) ((\p. holSyntax_Comb
  (holSyntax_Const (implode "~") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode "bool")
  []))) p) ((\f. holSyntax_Comb (holSyntax_Const (implode "ONTO") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (typeof f) (holSyntax_Tyapp (implode
  "bool") []))) f) (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "ind") []) (holSyntax_Tyapp
  (implode "ind") [])))))))) (CONS (NewType (implode "ind") 0) (CONS ((\x t.
  ConstSpec [(x,t)] ((===) (holSyntax_Var x (typeof t)) t)) (implode "ONTO")
  (holSyntax_Abs (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode
  "B")))) (((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp
  (implode "bool") []))) (holSyntax_Abs (holSyntax_Var x ty) p)) (implode "y")
  (holSyntax_Tyvar (implode "B"))) (((\x ty p. holSyntax_Comb (holSyntax_Const
  (implode "?") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool")
  [])) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs (holSyntax_Var x
  ty) p)) (implode "x") (holSyntax_Tyvar (implode "A"))) ((===) (holSyntax_Var
  (implode "y") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb (holSyntax_Var
  (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))
  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))))))))) (CONS
  ((\x t. ConstSpec [(x,t)] ((===) (holSyntax_Var x (typeof t)) t)) (implode
  "ONE_ONE")
       (holSyntax_Abs (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp
         (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
         (holSyntax_Tyvar (implode "B")))) (((\x ty p. holSyntax_Comb
         (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun")
         [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
         (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
         "bool") []))) (holSyntax_Abs (holSyntax_Var x ty) p)) (implode "x1")
         (holSyntax_Tyvar (implode "A"))) (((\x ty p. holSyntax_Comb
         (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun")
         [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
         (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
         "bool") []))) (holSyntax_Abs (holSyntax_Var x ty) p)) (implode "x2")
         (holSyntax_Tyvar (implode "A"))) ((\p1 p2. holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "==>") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "bool") []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
         (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode
         "bool") [])))) p1) p2) ((===) (holSyntax_Comb (holSyntax_Var (implode
         "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar
         (implode "A")) (holSyntax_Tyvar (implode "B")))) (holSyntax_Var
         (implode "x1") (holSyntax_Tyvar (implode "A")))) (holSyntax_Comb
         (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode "fun")
         [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode
         "B")))) (holSyntax_Var (implode "x2") (holSyntax_Tyvar (implode
         "A"))))) ((===) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
         (implode "A"))) (holSyntax_Var (implode "x2") (holSyntax_Tyvar
         (implode "A")))))))))
     ctxt)))`;;

(* tyvar_inst_exists[local] *)
let holAxiomsSyntax_tyvar_inst_exists = prove
 (`?i. ty = REV_ASSOCD (holSyntax_Tyvar a) i b`,
  CHEAT_TAC);;

let infinity_extends = prove
 (`!ctxt.
       theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
         list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
         ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
         ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
         (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
         ctxt)) ctxt) /\
           DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
             consts_of_upd ctxt)) ctxt)) ctxt)) (IMAGE implode
             {"ONE_ONE","ONTO"}) /\ ~((implode "ind") IN FDOM ((\ctxt.
             alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt))
             /\
           (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
             ctxt)) ctxt)) ctxt) (implode "==>") = SOME ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s
             t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
             (implode "bool") []) (holSyntax_Tyapp (implode "bool") [])))) /\
           (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
             ctxt)) ctxt)) ctxt) (implode "/\\") = SOME ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s
             t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
             (implode "bool") []) (holSyntax_Tyapp (implode "bool") [])))) /\
           (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
             ctxt)) ctxt)) ctxt) (implode "!") = SOME ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun")
             [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode
             "bool") [])) (holSyntax_Tyapp (implode "bool") []))) /\
           (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
             ctxt)) ctxt)) ctxt) (implode "?") = SOME ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun")
             [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode
             "bool") [])) (holSyntax_Tyapp (implode "bool") []))) /\
           (FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
             consts_of_upd ctxt)) ctxt)) ctxt) (implode "~") = SOME ((\s t.
             holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
             (implode "bool") []) (holSyntax_Tyapp (implode "bool") []))) ==>
             extends (mk_infinity_ctxt ctxt) ctxt`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Bool";
   "Fun";
   "mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
