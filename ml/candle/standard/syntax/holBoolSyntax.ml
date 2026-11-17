(* ======================================================== *)
(*  holBoolSyntax: ported from HOL4's
    candle/standard/syntax/holBoolSyntaxScript.sml
    A definition theory, with 18 definitions and 6 theorems.  Needed
    by 8 files of the port.  *)
(* ======================================================== *)

(*
  Definitions to extend a theory context to include the theory of
  Booleans, and some basic syntactic properties about these
  extensions.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holBoolSyntax"
  ["holSyntax"; "holSyntaxExtra"; "holSyntaxLib"];;

let _ = do_list hide_constant ["And"; "Bool"; "Not"; "Or"; "True"];;

(* HOL4 holBoolSyntaxScript.sml:14: the overload True, which the port
   expands *)
(* HOL4 holBoolSyntaxScript.sml:15: the overload And, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:16: the overload Implies, which the port
   expands *)
(* HOL4 holBoolSyntaxScript.sml:17: the overload Forall, which the port
   expands *)
(* HOL4 holBoolSyntaxScript.sml:18: the overload Exists, which the port
   expands *)
(* HOL4 holBoolSyntaxScript.sml:19: the overload Or, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:20: the overload False, which the port
   expands *)
(* HOL4 holBoolSyntaxScript.sml:21: the overload Not, which the port expands *)

(* HOL4 holBoolSyntaxScript.sml:23: the overload p, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:24: the overload FAp, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:25: the overload q, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:26: the overload FAq, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:27: the overload r, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:28: the overload FAr, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:29: the overload f, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:30: the overload A, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:31: the overload P, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:32: the overload x, which the port expands *)
(* HOL4 holBoolSyntaxScript.sml:33: the overload FAx, which the port expands *)

let TrueDef_def = new_definition
  `TrueDef = (===) (holSyntax_Abs (holSyntax_Var (implode "p")
  (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "p")
  (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs (holSyntax_Var
  (implode "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var
  (implode "p") (holSyntax_Tyapp (implode "bool") [])))`;;
let AndDef_def = new_definition
  `AndDef = holSyntax_Abs (holSyntax_Var (implode "p") (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Abs (holSyntax_Var (implode "q")
  (holSyntax_Tyapp (implode "bool") [])) ((===) (holSyntax_Abs
  (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
  (implode "bool") [])))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Var
  (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
  (implode "bool") [])))) (holSyntax_Var (implode "p") (holSyntax_Tyapp
  (implode "bool") []))) (holSyntax_Var (implode "q") (holSyntax_Tyapp
  (implode "bool") [])))) (holSyntax_Abs (holSyntax_Var (implode "f") ((\s
  t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
  "bool") []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode "bool")
  [])))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Var (implode "f") ((\s
  t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
  "bool") []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode "bool")
  [])))) (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool")
  []))) (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool")
  []))))))`;;
let ImpliesDef_def = new_definition
  `ImpliesDef = holSyntax_Abs (holSyntax_Var (implode "p") (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Abs (holSyntax_Var (implode "q")
  (holSyntax_Tyapp (implode "bool") [])) ((===) ((\p1 p2. holSyntax_Comb
  (holSyntax_Comb (holSyntax_Const (implode "/\\") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
  []) (holSyntax_Tyapp (implode "bool") [])))) p1) p2) (holSyntax_Var
  (implode "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var
  (implode "q") (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var
  (implode "p") (holSyntax_Tyapp (implode "bool") []))))`;;
let ForallDef_def = new_definition
  `ForallDef = holSyntax_Abs (holSyntax_Var (implode "P") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
  (holSyntax_Tyapp (implode "bool") []))) ((===) (holSyntax_Var (implode
  "P") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar
  (implode "A")) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
  (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool") []))))`;;
let ExistsDef_def = new_definition
  `ExistsDef = holSyntax_Abs (holSyntax_Var (implode "P") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
  (holSyntax_Tyapp (implode "bool") []))) (((\x ty p. holSyntax_Comb
  (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Tyapp (implode "bool") [])))
  (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))) ty) (holSyntax_Var (implode "p")
  (holSyntax_Tyapp (implode "bool") [])))) (implode "q") (holSyntax_Tyapp
  (implode "bool") [])) ((\p1 p2. holSyntax_Comb (holSyntax_Comb
  (holSyntax_Const (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
  (holSyntax_Tyapp (implode "bool") [])))) p1) p2) (((\x ty p.
  holSyntax_Comb (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
  (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode "bool")
  []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))) ty) (holSyntax_Var (implode "p")
  (holSyntax_Tyapp (implode "bool") [])))) (implode "x") (holSyntax_Tyvar
  (implode "A"))) ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
  (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp
  (implode "bool") [])))) p1) p2) (holSyntax_Comb (holSyntax_Var (implode
  "P") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar
  (implode "A")) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode
  "q") (holSyntax_Tyapp (implode "bool") [])))) (holSyntax_Var (implode "q")
  (holSyntax_Tyapp (implode "bool") []))))`;;
let OrDef_def = new_definition
  `OrDef = holSyntax_Abs (holSyntax_Var (implode "p") (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Abs (holSyntax_Var (implode "q")
  (holSyntax_Tyapp (implode "bool") [])) (((\x ty p. holSyntax_Comb
  (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Tyapp (implode "bool") [])))
  (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))) ty) (holSyntax_Var (implode "p")
  (holSyntax_Tyapp (implode "bool") [])))) (implode "r") (holSyntax_Tyapp
  (implode "bool") [])) ((\p1 p2. holSyntax_Comb (holSyntax_Comb
  (holSyntax_Const (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
  (holSyntax_Tyapp (implode "bool") [])))) p1) p2) ((\p1 p2. holSyntax_Comb
  (holSyntax_Comb (holSyntax_Const (implode "==>") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
  []) (holSyntax_Tyapp (implode "bool") [])))) p1) p2) (holSyntax_Var
  (implode "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var
  (implode "r") (holSyntax_Tyapp (implode "bool") []))) ((\p1 p2.
  holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "==>") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
  []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
  (implode "bool") []) (holSyntax_Tyapp (implode "bool") [])))) p1) p2)
  ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "==>")
  ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
  "bool") []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode "bool")
  [])))) p1) p2) (holSyntax_Var (implode "q") (holSyntax_Tyapp (implode
  "bool") [])) (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode
  "bool") []))) (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode
  "bool") []))))))`;;
let FalseDef_def = new_definition
  `FalseDef = ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s
  t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
  (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs (holSyntax_Var
  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))) ty)
  (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))))
  (implode "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var
  (implode "p") (holSyntax_Tyapp (implode "bool") []))`;;
let NotDef_def = new_definition
  `NotDef = holSyntax_Abs (holSyntax_Var (implode "p") (holSyntax_Tyapp
  (implode "bool") [])) ((\p1 p2. holSyntax_Comb (holSyntax_Comb
  (holSyntax_Const (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun")
  [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
  (holSyntax_Tyapp (implode "bool") [])))) p1) p2) (holSyntax_Var (implode
  "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Const (implode "F")
  (holSyntax_Tyapp (implode "bool") [])))`;;
(* HOL4 holBoolSyntaxScript.sml:59: ML code, not ported *)
let mk_bool_ctxt_def = new_definition
  `mk_bool_ctxt ctxt = CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode "~")
  NotDef) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode "F")
  FalseDef) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode
  "\\/") OrDef) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode "?")
  ExistsDef) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode "!")
  ForallDef) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode
  "==>") ImpliesDef) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode
  "/\\") AndDef) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode "T")
  TrueDef)
     ctxt)))))))`;;

(* bool is a good extension *)

(* HOL4 holBoolSyntaxScript.sml:75-106: a proof *)

(* HOL4 holBoolSyntaxScript.sml:108-111: ML code, not ported *)

let bool_extends = prove
 (`!ctxt.
      theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
        list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
        ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
        ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
        APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
        ctxt) /\
      DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
        consts_of_upd ctxt)) ctxt)) ctxt)) (IMAGE implode
        {"T","F","==>","/\\","\\/","~","!","?"}) ==> extends (mk_bool_ctxt
        ctxt) ctxt`,
  CHEAT_TAC);;

let bool_extends_init = prove
 (`extends (mk_bool_ctxt init_ctxt) init_ctxt`,
  CHEAT_TAC);;

(* signatures of Boolean constants *)

let is_true_sig_def = new_definition
  `is_true_sig tmsig <=> FLOOKUP tmsig (implode "T") = SOME (holSyntax_Tyapp
  (implode "bool") [])`;;
let is_false_sig_def = new_definition
  `is_false_sig tmsig <=> FLOOKUP tmsig (implode "F") = SOME
  (holSyntax_Tyapp (implode "bool") [])`;;
let is_implies_sig_def = new_definition
  `is_implies_sig tmsig <=> FLOOKUP tmsig (implode "==>") = SOME ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
  []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
  (implode "bool") []) (holSyntax_Tyapp (implode "bool") [])))`;;
let is_and_sig_def = new_definition
  `is_and_sig tmsig <=> FLOOKUP tmsig (implode "/\\") = SOME ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
  []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
  (implode "bool") []) (holSyntax_Tyapp (implode "bool") [])))`;;
let is_or_sig_def = new_definition
  `is_or_sig tmsig <=> FLOOKUP tmsig (implode "\\/") = SOME ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
  []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
  (implode "bool") []) (holSyntax_Tyapp (implode "bool") [])))`;;
let is_not_sig_def = new_definition
  `is_not_sig tmsig <=> FLOOKUP tmsig (implode "~") = SOME ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool")
  []) (holSyntax_Tyapp (implode "bool") []))`;;
let is_forall_sig_def = new_definition
  `is_forall_sig tmsig <=> FLOOKUP tmsig (implode "!") = SOME ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode
  "bool") [])) (holSyntax_Tyapp (implode "bool") []))`;;
let is_exists_sig_def = new_definition
  `is_exists_sig tmsig <=> FLOOKUP tmsig (implode "?") = SOME ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode
  "bool") [])) (holSyntax_Tyapp (implode "bool") []))`;;
(* HOL4 holBoolSyntaxScript.sml:166-167: ML code, not ported *)

let is_bool_sig_def = new_definition
  `is_bool_sig (sig:(mlstring,num)fmap#(mlstring,type)fmap) <=>
   is_std_sig sig /\
   is_true_sig (SND sig) /\
   is_false_sig (SND sig) /\
   is_implies_sig (SND sig) /\
   is_and_sig (SND sig) /\
   is_or_sig (SND sig) /\
   is_not_sig (SND sig) /\
   is_forall_sig (SND sig) /\
   is_exists_sig (SND sig)`;;

let bool_has_bool_sig = prove
 (`!ctxt.
   is_std_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
     ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
     ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) ==>
     is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
     ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
     ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) (mk_bool_ctxt
     ctxt))`,
  CHEAT_TAC);;

let is_bool_sig_std = prove
 (`is_bool_sig sig ==> is_std_sig sig`,
  CHEAT_TAC);;

let is_bool_sig_extends = prove
 (`!ctxt1 ctxt2. extends ctxt2 ctxt1 ==> is_bool_sig
  ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  consts_of_upd ctxt)) ctxt)) ctxt)) ctxt1) ==> is_bool_sig
  ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  consts_of_upd ctxt)) ctxt)) ctxt)) ctxt2)`,
  CHEAT_TAC);;

(* Boolean terms are ok *)

let bool_term_ok = prove
 (`!sig. is_bool_sig sig ==>
    holSyntax_term_ok sig (holSyntax_Const (implode "T") (holSyntax_Tyapp
      (implode "bool") [])) /\
    (!p1 p2. holSyntax_term_ok sig ((\p1 p2. holSyntax_Comb (holSyntax_Comb
      (holSyntax_Const (implode "/\\") ((\s t. holSyntax_Tyapp (implode "fun")
      [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") [])))) p1) p2) p1 p2) <=>
      holSyntax_term_ok sig p1 /\ holSyntax_term_ok sig p2 /\ typeof p1 =
      (holSyntax_Tyapp (implode "bool") []) /\ typeof p2 = (holSyntax_Tyapp
      (implode "bool") [])) /\
    (!p1 p2. holSyntax_term_ok sig ((\p1 p2. holSyntax_Comb (holSyntax_Comb
      (holSyntax_Const (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun")
      [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") [])))) p1) p2) p1 p2) <=>
      holSyntax_term_ok sig p1 /\ holSyntax_term_ok sig p2 /\ typeof p1 =
      (holSyntax_Tyapp (implode "bool") []) /\ typeof p2 = (holSyntax_Tyapp
      (implode "bool") [])) /\
    (!z ty p. holSyntax_term_ok sig ((\x ty p. holSyntax_Comb
      (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun")
      [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
      (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode "bool")
      []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
      (holSyntax_Tyvar (implode "A"))) ty) (holSyntax_Var (implode "p")
      (holSyntax_Tyapp (implode "bool") [])))) z ty (holSyntax_Var (implode
      "p") (holSyntax_Tyapp (implode "bool") []))) <=> type_ok (FST sig) ty
      /\ holSyntax_term_ok sig (holSyntax_Var (implode "p") (holSyntax_Tyapp
      (implode "bool") [])) /\ typeof (holSyntax_Var (implode "p")
      (holSyntax_Tyapp (implode "bool") [])) = (holSyntax_Tyapp (implode
      "bool") [])) /\
    (!z ty p. holSyntax_term_ok sig ((\x ty p. holSyntax_Comb
      (holSyntax_Const (implode "?") ((\s t. holSyntax_Tyapp (implode "fun")
      [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
      (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode "bool")
      []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
      (holSyntax_Tyvar (implode "A"))) ty) (holSyntax_Var (implode "p")
      (holSyntax_Tyapp (implode "bool") [])))) z ty (holSyntax_Var (implode
      "p") (holSyntax_Tyapp (implode "bool") []))) <=> type_ok (FST sig) ty
      /\ holSyntax_term_ok sig (holSyntax_Var (implode "p") (holSyntax_Tyapp
      (implode "bool") [])) /\ typeof (holSyntax_Var (implode "p")
      (holSyntax_Tyapp (implode "bool") [])) = (holSyntax_Tyapp (implode
      "bool") [])) /\
    (!p1 p2. holSyntax_term_ok sig ((\p1 p2. holSyntax_Comb (holSyntax_Comb
      (holSyntax_Const (implode "\\/") ((\s t. holSyntax_Tyapp (implode "fun")
      [s; t]) (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
      (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
      (holSyntax_Tyapp (implode "bool") [])))) p1) p2) p1 p2) <=>
      holSyntax_term_ok sig p1 /\ holSyntax_term_ok sig p2 /\ typeof p1 =
      (holSyntax_Tyapp (implode "bool") []) /\ typeof p2 = (holSyntax_Tyapp
      (implode "bool") [])) /\
    holSyntax_term_ok sig (holSyntax_Const (implode "F") (holSyntax_Tyapp
      (implode "bool") [])) /\
    (!p. holSyntax_term_ok sig ((\p. holSyntax_Comb (holSyntax_Const
      (implode "~") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
      (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode "bool")
      []))) (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool")
      []))) (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool")
      []))) <=> holSyntax_term_ok sig (holSyntax_Var (implode "p")
      (holSyntax_Tyapp (implode "bool") [])) /\ typeof (holSyntax_Var
      (implode "p") (holSyntax_Tyapp (implode "bool") [])) = (holSyntax_Tyapp
      (implode "bool") []))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["And";
   "Bool";
   "Not";
   "Or";
   "True"];;

(* and the interface *)
let _ = unhide_overloads ();;
