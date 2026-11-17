(* ======================================================== *)
(*  holLightConsistency: ported from HOL4's
    candle/standard/semantics/holLightConsistencyScript.sml
    A definition theory, with 6 definitions and 58 theorems.  Needed
    by x64BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Consistency of the contexts that HOL Light actually builds.

  holConsistency proves consistency for a context extending init_ctxt,
  fhol_ctxt or hol_ctxt, subject in each case to a condition on the axioms
  the context asserts. A real HOL Light session - Candle running hol.ml -
  meets none of those hypotheses. Its context does extend init_ctxt, but it
  asserts three axioms, so the init_ctxt result does not apply; and it is
  not an extension of fhol_ctxt or hol_ctxt at all, since it interleaves
  ordinary definitions between the axioms, states ETA_AX and SELECT_AX in
  universally closed form, declares the type ind before ONE_ONE and ONTO
  rather than after, and binds those two definitions with generated variable
  names.

  This theory restates consistency for the shape a session really has: a
  predicate constraining only the bool definitions, the three axiom terms,
  the declaration of @ next to SELECT_AX, and the four updates of the
  infinity block, quantifying over everything in between subject only to
  axiom-freeness. Each shape is then shown realisable, and checked against
  the context a Candle session prints after loading core HOL Light.

  The same four differences are visible in the sources of the reference
  implementation, which agree with the ones Candle loads on every file that
  creates a context; but only Candle was run.
*)

needs "basis/pure/mlstring.ml";;
needs "candle/set-theory/setModel.ml";;
needs "candle/set-theory/setSpec.ml";;
needs "candle/standard/semantics/holAxioms.ml";;
needs "candle/standard/semantics/holBool.ml";;
needs "candle/standard/semantics/holConsistency.ml";;
needs "candle/standard/semantics/holExtension.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/semantics/holSoundness.ml";;
needs "candle/standard/syntax/holAxiomsSyntax.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "holLightConsistency"
  ["holAxioms"; "holAxiomsSyntax"; "holBool"; "holBoolSyntax";
   "holConsistency"; "holExtension"; "holSemantics"; "holSemanticsExtra";
   "holSoundness"; "holSyntax"; "holSyntaxExtra"; "holSyntaxLib"; "setModel";
   "setSpec"];;

let _ = do_list hide_constant ["And"; "Bool"; "Fun"; "Not"];;

let _ = do_list hide_constant ["mem"];;

(* HOL4 holLightConsistencyScript.sml:38: the overload A, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:39: the overload B, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:40: the overload x, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:41: the overload P, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:42: the overload tf, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:43: the overload gf, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:44: the overload x1, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:45: the overload x2, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:46: the overload y, which the port
   expands *)
(* HOL4 holLightConsistencyScript.sml:47: the overload h, which the port
   expands *)

(* ------------------------------------------------------------------------
   The three axiom-carrying blocks, in the form HOL Light states them.

   ETA_AX and SELECT_AX are the universal closures of the terms modelled in
   holAxiomsSyntax, with the closure binders pinned to the names HOL Light
   uses (class.ml): the predicates below fix these updates by equality of
   contexts, not up to alpha, so a different binder is a different context.
   The two constants of the infinity block are bound by generated variables,
   so those two names alone are parameters.
   ------------------------------------------------------------------------ *)

let mk_eta_ctxt_cl_def = new_definition
  `mk_eta_ctxt_cl ctxt = CONS (NewAxiom ((\x ty p. holSyntax_Comb
  (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Tyapp (implode "bool") [])))
  (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "t") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
  (holSyntax_Tyvar (implode "B"))) ((===) (holSyntax_Abs (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
  (holSyntax_Var (implode "t") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))
  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))))
  (holSyntax_Var (implode "t") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B")))))))
  ctxt`;;

let mk_select_ctxt_cl_def = new_definition
  `mk_select_ctxt_cl ctxt = CONS (NewAxiom ((\x ty p. holSyntax_Comb
  (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
  (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
  ty) p)) (implode "P") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode "bool") []))
                ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!")
                  ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
                  holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
                  (implode "bool") [])) (holSyntax_Tyapp (implode "bool") [])))
                  (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
                  (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "x")
                  (holSyntax_Tyvar (implode "A")) ((\p1 p2. holSyntax_Comb
                  (holSyntax_Comb (holSyntax_Const (implode "==>") ((\s t.
                  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
                  (implode "bool") []) ((\s t. holSyntax_Tyapp (implode "fun")
                  [s; t]) (holSyntax_Tyapp (implode "bool") [])
                  (holSyntax_Tyapp (implode "bool") [])))) p1) p2)
                  (holSyntax_Comb (holSyntax_Var (implode "P") ((\s t.
                  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar
                  (implode "A")) (holSyntax_Tyapp (implode "bool") [])))
                  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
                  "A")))) (holSyntax_Comb (holSyntax_Var (implode "P") ((\s t.
                  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar
                  (implode "A")) (holSyntax_Tyapp (implode "bool") [])))
                  (holSyntax_Comb ((\ty. holSyntax_Const (implode "@") ((\s t.
                  holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
                  holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
                  (implode "bool") [])) ty)) (holSyntax_Tyvar (implode "A")))
                  (holSyntax_Var (implode "P") ((\s t. holSyntax_Tyapp (implode
                  "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
                  (holSyntax_Tyapp (implode "bool") []))))))))) (CONS (NewConst
                  (implode "@") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyvar (implode "A")) (holSyntax_Tyapp (implode
                  "bool") [])) (holSyntax_Tyvar (implode "A"))))
     ctxt)`;;

let mk_infinity_ctxt_hl_def = new_definition
  `mk_infinity_ctxt_hl b1 b2 ctxt = CONS (NewAxiom ((\x ty p. holSyntax_Comb
  (holSyntax_Const (implode "?") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
  (implode "bool") [])) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
  (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
  ty) p)) (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "ind") []) (holSyntax_Tyapp (implode "ind") []))
  ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "/\\")
  ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
  "bool") []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
  (implode "bool") []) (holSyntax_Tyapp (implode "bool") [])))) p1) p2) ((\f.
  holSyntax_Comb (holSyntax_Const (implode "ONE_ONE") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (typeof f) (holSyntax_Tyapp (implode "bool") []))) f)
  (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "ind") []) (holSyntax_Tyapp (implode "ind") []))))
  ((\p. holSyntax_Comb (holSyntax_Const (implode "~") ((\s t. holSyntax_Tyapp
  (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
  (holSyntax_Tyapp (implode "bool") []))) p) ((\f. holSyntax_Comb
  (holSyntax_Const (implode "ONTO") ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (typeof f) (holSyntax_Tyapp (implode "bool") []))) f) (holSyntax_Var
  (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyapp (implode "ind") []) (holSyntax_Tyapp (implode "ind")
  [])))))))) (CONS ((\x t. ConstSpec [((holSyntax_Var (implode "x")
  (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode
  "ONTO")
       (holSyntax_Abs (holSyntax_Var b2 ((\s t. holSyntax_Tyapp (implode
         "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
         (implode "B"))))
         ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "y") (holSyntax_Tyvar (implode
           "B")) ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "?") ((\s
           t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "x") (holSyntax_Tyvar (implode
           "A")) ((===) (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode
           "B"))) (holSyntax_Comb (holSyntax_Var b2 ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
           (holSyntax_Tyvar (implode "B")))) (holSyntax_Var (implode "x")
           (holSyntax_Tyvar (implode "A"))))))))) (CONS ((\x t. ConstSpec
           [((holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))),t)]
           ((===) (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) (typeof t)) t)) (implode "ONE_ONE")
       (holSyntax_Abs (holSyntax_Var b1 ((\s t. holSyntax_Tyapp (implode
         "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
         (implode "B"))))
         ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "x1") (holSyntax_Tyvar (implode
           "A")) ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s
           t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "x2") (holSyntax_Tyvar (implode
           "A"))
           ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
             (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
             (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
             (holSyntax_Tyapp (implode "bool") [])))) p1) p2) ((===)
             (holSyntax_Comb (holSyntax_Var b1 ((\s t. holSyntax_Tyapp (implode
             "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
             (implode "B")))) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
             (implode "A")))) (holSyntax_Comb (holSyntax_Var b1 ((\s t.
             holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode
             "A")) (holSyntax_Tyvar (implode "B")))) (holSyntax_Var (implode
             "x2") (holSyntax_Tyvar (implode "A")))))
                    ((===) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
                      (implode "A"))) (holSyntax_Var (implode "x2")
                      (holSyntax_Tyvar (implode "A"))))))))) (CONS (NewType
                      (implode "ind") 0)
     ctxt)))`;;

(* HOL4 holLightConsistencyScript.sml:88: the ML values that the definitions
   below antiquote *)

(* HOL4 holLightConsistencyScript.sml:90: the overload axiom_free, which the
   port expands *)

(* ------------------------------------------------------------------------
   Extension chains and their suffixes

   Each step of an extension conses a single update, so the chain from c0 up
   to ctxt visits precisely the suffixes of ctxt. Any suffix that still has
   c0 below it is therefore one of them, and the update sitting directly on
   top of such a suffix is one the chain performed - which is where every
   freshness side condition below comes from.
   ------------------------------------------------------------------------ *)

(* the chain cannot already have arrived at c0, since c0 sits strictly below
   the update on top; so its last step is that update *)

(* [local] *)
let extends_CONS = prove
 (`!u ctxt c0 m. extends (CONS u ctxt) c0 /\ ctxt = APPEND m c0 ==> updates u
  ctxt /\ extends ctxt c0`,
  CHEAT_TAC);;

(* [local] *)
let extends_CONS_I = prove
 (`!u ctxt base. extends ctxt base /\ updates u ctxt ==> extends (CONS u
  ctxt) base`,
  CHEAT_TAC);;

let extends_suffix = prove
 (`!l base c0. extends (APPEND l base) c0 /\ (?m. base = APPEND m c0) ==>
  extends (APPEND l base) base`,
  CHEAT_TAC);;

let extends_suffix_below = prove
 (`!l base c0. extends (APPEND l base) c0 /\ (?m. base = APPEND m c0) ==>
  extends base c0`,
  CHEAT_TAC);;

let extends_updates_at = prove
 (`!l u rest c0. extends (APPEND l (CONS u rest)) c0 /\ (?m. rest = APPEND m
  c0) ==> updates u rest /\ extends rest c0`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   Models along a chain
   ------------------------------------------------------------------------ *)

(* an axiom-free segment carries a model along with it *)

let models_axiom_free_segment = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!l base i. extends (APPEND l base) base /\ theory_ok
     ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list). ((\ctxt.
     alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
     alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
     ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd
     upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) base) /\ models0 mem i
     ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list). ((\ctxt.
     alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
     alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
     ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd
     upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) base) /\ (\l. ALL (\u. !p.
     ~(u = NewAxiom p)) l) l ==>
     (?i'. equal_on ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) base) i i' /\ models0 mem i' ((\(ctxt:holSyntax_update
       list). ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) (APPEND
       l base))))`,
  CHEAT_TAC);;

(* asserting an axiom leaves the signature alone *)

let models_NewAxiom = prove
 (`!i p ctxt. models0 mem i ((\(ctxt:holSyntax_update list).
  ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT
  (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
  ctxt)) (CONS (NewAxiom p) ctxt)) <=> models0 mem i
  ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list). ((\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
  ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd
  upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt) /\ satisfies0 mem i
  ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
  consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,[],p)`,
  CHEAT_TAC);;

(* and a model does not see the names of bound variables *)

let satisfies_ACONV = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!i sig p q.
     ACONV p q /\ welltyped p /\ welltyped q /\ satisfies0 mem i
       (sig,[],p) ==> satisfies0 mem i (sig,[],q))`,
  CHEAT_TAC);;

let models_ACONV = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!i ctxt1 ctxt2.
     (\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt1 = (\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt2 /\
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt1) /\ theory_ok ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt2) /\
     (!p. p IN (\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt2 ==> (?q.
       q IN (\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt1 /\ ACONV
       q p)) /\ models0 mem i ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt1) ==> models0 mem i
       ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
       ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt2))`,
  CHEAT_TAC);;

(* closing an axiom over a variable keeps it satisfied *)

let satisfies_Forall = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!i sig nm ty b.
     (is_interpretation0 mem) sig i /\ (is_std_interpretation0 mem) i /\
     type_ok (FST sig) ty /\ holSyntax_term_ok sig b /\ typeof b =
       (holSyntax_Tyapp
       (implode "bool") []) /\
     is_forall_sig (SND sig) /\ (is_forall_interpretation0 mem)
       ((SND:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
       list->'U) i) /\ satisfies0 mem i (sig,[],b) ==> satisfies0 mem i
       (sig,[],(\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s
       t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
       (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
       (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs (holSyntax_Var
       (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))) ty) p))
       nm ty b))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   The blocks have models
   ------------------------------------------------------------------------ *)

(* [local] *)
let welltyped_eta_ax = prove
 (`!nm. welltyped
          ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
            holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
            (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
            (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
            (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
            (implode "A"))) ty) p)) nm ((\s t. holSyntax_Tyapp (implode "fun")
            [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode
            "B")))
             ((===) (holSyntax_Abs (holSyntax_Var (implode "x")
               (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
               (holSyntax_Var nm ((\s t. holSyntax_Tyapp (implode "fun") [s;
               t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode
               "B")))) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
               "A"))))) (holSyntax_Var nm ((\s t. holSyntax_Tyapp (implode
               "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
               (holSyntax_Tyvar (implode "B"))))))`,
  CHEAT_TAC);;

(* [local] *)
let ACONV_eta_ax = prove
 (`ACONV ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp
  (implode "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode
  "x") (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "f") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
  (holSyntax_Tyvar (implode "B"))) ((===) (holSyntax_Abs (holSyntax_Var
  (implode "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Var
  (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))
  (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))))
  (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
  (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))))
         ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "t") ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
           (holSyntax_Tyvar (implode "B"))) ((===) (holSyntax_Abs
           (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
           (holSyntax_Comb (holSyntax_Var (implode "t") ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode
           "A")) (holSyntax_Tyvar (implode "B")))) (holSyntax_Var (implode
           "x") (holSyntax_Tyvar (implode "A"))))) (holSyntax_Var (implode
           "t") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
           (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode
           "B"))))))`,
  CHEAT_TAC);;

let eta_cl_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!ctxt i.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
       (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
       ctxt)) ctxt) /\ is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt) /\ models0 mem i ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt) /\ (is_bool_interpretation0 mem) i
       ==> models0 mem i ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) (mk_eta_ctxt_cl ctxt)))`,
  CHEAT_TAC);;

(* [local] *)
let equal_on_bool_interpretation = prove
 (`!s j1 j2.
     equal_on s j1 j2 /\ (is_bool_interpretation0 mem) j1 /\ is_bool_sig s
       /\
     (is_std_interpretation0 mem) j2 ==>
     (is_bool_interpretation0 mem) j2`,
  CHEAT_TAC);;

(* [local] *)
let term_ok_Forall = prove
 (`!sig nm ty p.
     is_std_sig sig /\ is_forall_sig (SND sig) /\ type_ok (FST sig) ty /\
     holSyntax_term_ok sig p /\ typeof p = (holSyntax_Tyapp (implode "bool")
       []) ==>
     holSyntax_term_ok sig ((\x ty p. holSyntax_Comb (holSyntax_Const
       (implode "!") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
       holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode
       "bool") [])) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
       (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
       "A"))) ty) p)) nm ty p) /\ typeof ((\x ty p. holSyntax_Comb
       (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
       (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
       "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode
       "x") (holSyntax_Tyvar (implode "A"))) ty) p)) nm ty p) =
       (holSyntax_Tyapp (implode "bool") [])`,
  CHEAT_TAC);;

(* [local] *)
let models_close_axiom = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!i ctxt nm ty p. models0 mem i ((\(ctxt:holSyntax_update list).
     ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
     types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
     consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT
     (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
     ctxt)) (CONS (NewAxiom p) ctxt)) /\
     is_forall_sig ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt) /\ (is_forall_interpretation0 mem)
       ((SND:(mlstring->'U list->'U)#(mlstring->'U list->'U)->mlstring->'U
       list->'U) i) /\
     type_ok ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt) ty /\ holSyntax_term_ok ((\(ctxt:holSyntax_update list).
       ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt) p /\ typeof p = (holSyntax_Tyapp (implode "bool")
       []) ==> models0 mem i ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) (CONS (NewAxiom ((\x ty p. holSyntax_Comb
       (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode "fun")
       [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
       (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
       "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode
       "x") (holSyntax_Tyvar (implode "A"))) ty) p)) nm ty p)) ctxt)))`,
  CHEAT_TAC);;

let select_cl_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!ctxt i.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\ is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt) /\ ~((implode "@") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP consts_of_upd ctxt)) ctxt)) ctxt)) /\ models0 mem i
       ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
       ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt)
       /\ (is_bool_interpretation0 mem) i ==>
     (?i'. equal_on ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt) i i' /\ models0 mem i' ((\(ctxt:holSyntax_update
       list). ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       (mk_select_ctxt_cl ctxt))))`,
  CHEAT_TAC);;

(* HOL Light declares ind at the bottom of the infinity block rather than
   above the two definitions, and binds the two definitions with generated
   variables. A NewType update contributes no constants and no axioms and a
   ConstSpec update contributes no types, so moving ind past them leaves the
   type and constant lists as the very same lists; and a bound variable name
   is invisible to the signature. *)

(* [local] *)
let sigof_mk_infinity_ctxt_hl = prove
 (`!b1 b2 ctxt.
     (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       (mk_infinity_ctxt_hl b1 b2 ctxt) = (\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) (mk_infinity_ctxt ctxt) /\
     (\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
       (mk_infinity_ctxt_hl b1 b2 ctxt) = (\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP consts_of_upd ctxt)) ctxt)) (mk_infinity_ctxt ctxt)`,
  CHEAT_TAC);;

(* [local] *)
let ACONV_ONE_ONE_conext = prove
 (`!b.
     ACONV
       ((===) (holSyntax_Const (implode "ONE_ONE") ((\s t. holSyntax_Tyapp
         (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s;
         t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B")))
         (holSyntax_Tyapp (implode "bool") [])))
        (holSyntax_Abs (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp
          (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
          (holSyntax_Tyvar (implode "B")))) ((\x ty p. holSyntax_Comb
          (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode
          "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
          (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
          "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode
          "x") (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "x1")
          (holSyntax_Tyvar (implode "A")) ((\x ty p. holSyntax_Comb
          (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode
          "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
          (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
          "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode
          "x") (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "x2")
          (holSyntax_Tyvar (implode "A"))
          ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
            "==>") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
            (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
            (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
            (holSyntax_Tyapp (implode "bool") [])))) p1) p2) ((===)
            (holSyntax_Comb (holSyntax_Var (implode "f") ((\s t.
            holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode
            "A")) (holSyntax_Tyvar (implode "B")))) (holSyntax_Var (implode
            "x1") (holSyntax_Tyvar (implode "A")))) (holSyntax_Comb
            (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp (implode
            "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
            (implode "B")))) (holSyntax_Var (implode "x2") (holSyntax_Tyvar
            (implode "A"))))) ((===) (holSyntax_Var (implode "x1")
            (holSyntax_Tyvar (implode "A"))) (holSyntax_Var (implode "x2")
            (holSyntax_Tyvar (implode "A")))))))))
       ((===) (holSyntax_Const (implode "ONE_ONE") ((\s t. holSyntax_Tyapp
         (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s;
         t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B")))
         (holSyntax_Tyapp (implode "bool") [])))
        (holSyntax_Abs (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode
          "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
          (implode "B")))) ((\x ty p. holSyntax_Comb (holSyntax_Const (implode
          "!") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
          holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode
          "bool") [])) (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
          (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
          "A"))) ty) p)) (implode "x1") (holSyntax_Tyvar (implode "A")) ((\x ty
          p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
          holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
          (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
          (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs (holSyntax_Var
          (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))) ty) p))
          (implode "x2") (holSyntax_Tyvar (implode "A"))
          ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
            "==>") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
            (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
            (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
            (holSyntax_Tyapp (implode "bool") [])))) p1) p2) ((===)
            (holSyntax_Comb (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode
            "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
            (implode "B")))) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
            (implode "A")))) (holSyntax_Comb (holSyntax_Var b ((\s t.
            holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode
            "A")) (holSyntax_Tyvar (implode "B")))) (holSyntax_Var (implode
            "x2") (holSyntax_Tyvar (implode "A")))))
                   ((===) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
                     (implode "A"))) (holSyntax_Var (implode "x2")
                     (holSyntax_Tyvar (implode "A")))))))))`,
  CHEAT_TAC);;

(* [local] *)
let ACONV_ONTO_conext = prove
 (`!b.
     ACONV
       ((===) (holSyntax_Const (implode "ONTO") ((\s t. holSyntax_Tyapp
         (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s;
         t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B")))
         (holSyntax_Tyapp (implode "bool") [])))
        (holSyntax_Abs (holSyntax_Var (implode "f") ((\s t. holSyntax_Tyapp
          (implode "fun") [s; t]) (holSyntax_Tyvar (implode "A"))
          (holSyntax_Tyvar (implode "B")))) ((\x ty p. holSyntax_Comb
          (holSyntax_Const (implode "!") ((\s t. holSyntax_Tyapp (implode
          "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
          (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
          "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode
          "x") (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "y")
          (holSyntax_Tyvar (implode "B")) ((\x ty p. holSyntax_Comb
          (holSyntax_Const (implode "?") ((\s t. holSyntax_Tyapp (implode
          "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ty
          (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Tyapp (implode
          "bool") []))) (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode
          "x") (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "x")
          (holSyntax_Tyvar (implode "A")) ((===) (holSyntax_Var (implode "y")
          (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb (holSyntax_Var
          (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
          (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))
          (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))))))))
       ((===) (holSyntax_Const (implode "ONTO") ((\s t. holSyntax_Tyapp
         (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s;
         t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B")))
         (holSyntax_Tyapp (implode "bool") [])))
        (holSyntax_Abs (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode
          "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
          (implode "B"))))
          ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
            holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
            (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
            (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
            (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
            (implode "A"))) ty) p)) (implode "y") (holSyntax_Tyvar (implode
            "B")) ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "?")
            ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
            holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
            (implode "bool") [])) (holSyntax_Tyapp (implode "bool") [])))
            (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
            (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "x")
            (holSyntax_Tyvar (implode "A")) ((===) (holSyntax_Var (implode
            "y") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
            (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
            (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))
            (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
            "A")))))))))`,
  CHEAT_TAC);;

(* [local] *)
let axioms_mk_infinity_ctxt_hl = prove
 (`!b1 b2 ctxt p.
     p IN (\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
       (mk_infinity_ctxt_hl b1 b2 ctxt) ==>
     (?q. q IN (\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
       (mk_infinity_ctxt ctxt) /\ ACONV q p)`,
  CHEAT_TAC);;

let infinity_hl_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) /\ (?inf'. is_infinite (mem:'U->'U->bool)
  inf') ==>
   (!ctxt i b1 b2.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       (mk_infinity_ctxt_hl b1 b2 ctxt)) /\
     is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) /\
     DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) {(implode "ONE_ONE"),(implode "ONTO")}
       /\ ~((implode "ind") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       types_of_upd ctxt)) ctxt)) ctxt)) /\ models0 mem i
       ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
       ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt)
       /\ (is_bool_interpretation0 mem) i ==>
     (?i'. equal_on ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) ctxt) i i' /\ models0 mem i' ((\(ctxt:holSyntax_update
       list). ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
       (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       (mk_infinity_ctxt_hl b1 b2 ctxt))))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   The context shapes a HOL Light session builds

   Everything the predicates pin down is decidable on a printed context: the
   eight boolean definitions on top of the initial context, the three axiom
   terms, the declaration of @ immediately below SELECT_AX, and the four
   updates of the infinity block. Everything else is quantified over, and
   asked only not to assert an axiom.
   ------------------------------------------------------------------------ *)

let fhol_light_ctxt_def = new_definition
  `fhol_light_ctxt ctxt <=>
     (?l2 l1 l0.
       ctxt = APPEND l2 (mk_select_ctxt_cl
                      (APPEND l1 (mk_eta_ctxt_cl (APPEND l0 (mk_bool_ctxt
                        init_ctxt))))) /\
       (\l. ALL (\u. !p. ~(u = NewAxiom p)) l) (APPEND (APPEND l0 l1)
         l2))`;;

let hol_light_ctxt_def = new_definition
  `hol_light_ctxt ctxt <=>
     (?l3 l2 l1 l0 b1 b2.
       ctxt = APPEND l3 (mk_infinity_ctxt_hl b1 b2
                      (APPEND l2 (mk_select_ctxt_cl
                              (APPEND l1 (mk_eta_ctxt_cl
                              (APPEND l0 (mk_bool_ctxt init_ctxt))))))) /\
       (\l. ALL (\u. !p. ~(u = NewAxiom p)) l) (APPEND (APPEND (APPEND l0
         l1) l2) l3))`;;

(* ------------------------------------------------------------------------
   Consistency
   ------------------------------------------------------------------------ *)

(* the facts every cut point of the chain needs: it lies above the boolean
   definitions, so it is a good theory with a boolean signature, and any
   model of it interprets the boolean constants as intended *)

(* [local] *)
let mk_bool_ctxt_APPEND = prove
 (`!ctxt. ?m. mk_bool_ctxt ctxt = APPEND m ctxt`,
  CHEAT_TAC);;

(* [local] *)
let extends_bool_suffix = prove
 (`!l. extends (APPEND l (mk_bool_ctxt init_ctxt)) init_ctxt ==> extends
  (APPEND l (mk_bool_ctxt init_ctxt)) (mk_bool_ctxt init_ctxt)`,
  CHEAT_TAC);;

(* [local] *)
let suffix_facts_m = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!m i. extends (APPEND m (mk_bool_ctxt init_ctxt)) init_ctxt /\ models0
     mem i ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list).
     ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
     ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
     ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
     (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) (APPEND m
     (mk_bool_ctxt init_ctxt))) ==>
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       (APPEND m (mk_bool_ctxt init_ctxt))) /\
     is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) (APPEND m
       (mk_bool_ctxt init_ctxt))) /\
     (is_bool_interpretation0 mem) i)`,
  CHEAT_TAC);;

(* [local] *)
let suffix_facts = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!sfx i. extends sfx init_ctxt /\ (?m. sfx = APPEND m (mk_bool_ctxt
     init_ctxt)) /\ models0 mem i ((\(ctxt:holSyntax_update list).
     ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
     types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
     consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT
     (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
     ctxt)) sfx) ==>
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
       (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
       ctxt)) sfx) /\ is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
       ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt)) sfx) /\ (is_bool_interpretation0 mem) i)`,
  CHEAT_TAC);;

(* [local] *)
let bool_ctxt_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==> (?i. models0 mem i
  ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list). ((\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
  alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
  ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd
  upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) (mk_bool_ctxt init_ctxt)))`,
  CHEAT_TAC);;

(* [local] *)
let climb_axiom_free = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!l sfx i. extends (APPEND l sfx) sfx /\ extends sfx init_ctxt /\ (\l.
     ALL (\u. !p. ~(u = NewAxiom p)) l) l /\ models0 mem i
     ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update list). ((\ctxt.
     alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
     alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
     ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd
     upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) sfx) ==>
     (?i'. models0 mem i' ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) (APPEND l sfx))))`,
  CHEAT_TAC);;

(* [local] *)
let bool_ctxt_suffix_init = prove
 (`!mk. ?m. APPEND mk (mk_bool_ctxt init_ctxt) = APPEND m init_ctxt`,
  CHEAT_TAC);;

(* [local] *)
let chain_cut = prove
 (`!l mk. extends (APPEND l (APPEND mk (mk_bool_ctxt init_ctxt))) init_ctxt ==>
  extends (APPEND l (APPEND mk (mk_bool_ctxt init_ctxt)))
       (APPEND mk (mk_bool_ctxt init_ctxt)) /\ extends (APPEND mk
         (mk_bool_ctxt init_ctxt)) init_ctxt`,
  CHEAT_TAC);;

(* every cut point of the chain is again of the form "something on top of the
   boolean definitions", so one lemma recognises them all *)

(* [local] *)
let above_bool = prove
 (`(?m. mk_bool_ctxt init_ctxt = APPEND m (mk_bool_ctxt init_ctxt)) /\
   (!X l. (?m. X = APPEND m (mk_bool_ctxt init_ctxt)) ==>
          (?m. APPEND l X = APPEND m (mk_bool_ctxt init_ctxt))) /\
   (!X u. (?m. X = APPEND m (mk_bool_ctxt init_ctxt)) ==>
          (?m. CONS u X = APPEND m (mk_bool_ctxt init_ctxt)))`,
  CHEAT_TAC);;

(* [local] *)
let chain_cut2 = prove
 (`!l base. extends (APPEND l base) init_ctxt /\ (?m. base = APPEND m
  (mk_bool_ctxt init_ctxt)) ==> extends (APPEND l base) base /\ extends base
  init_ctxt`,
  CHEAT_TAC);;

(* [local] *)
let chain_cut_CONS = prove
 (`!u base m. extends (CONS u base) init_ctxt /\ base = APPEND m
  (mk_bool_ctxt init_ctxt) ==> extends (CONS u base) base /\ extends base
  init_ctxt`,
  CHEAT_TAC);;

(* [local] *)
let cut_eta = prove
 (`!X. extends (mk_eta_ctxt_cl X) init_ctxt /\
       (?m. X = APPEND m (mk_bool_ctxt init_ctxt)) ==> extends
         (mk_eta_ctxt_cl X) X /\ extends X init_ctxt`,
  CHEAT_TAC);;

(* [local] *)
let cut_select = prove
 (`!X. extends (mk_select_ctxt_cl X) init_ctxt /\
       (?m. X = APPEND m (mk_bool_ctxt init_ctxt)) ==> extends
         (mk_select_ctxt_cl X) X /\ extends X init_ctxt /\ ~((implode "@") IN
         FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
         ctxt)) X))`,
  CHEAT_TAC);;

(* [local] *)
let chain_cut_CONS4 = prove
 (`!u1 u2 u3 u4 base m. extends (CONS u1 (CONS u2 (CONS u3 (CONS u4 base))))
  init_ctxt /\
     base = APPEND m (mk_bool_ctxt init_ctxt) ==> extends (CONS u1 (CONS
       u2 (CONS u3 (CONS u4 base)))) base /\ extends base init_ctxt
       /\ updates u4 base /\ updates u3 (CONS u4 base) /\ updates u2 (CONS u3
       (CONS u4 base))`,
  CHEAT_TAC);;

(* [local] *)
let cut_infinity = prove
 (`!X b1 b2. extends (mk_infinity_ctxt_hl b1 b2 X) init_ctxt /\
     (?m. X = APPEND m (mk_bool_ctxt init_ctxt)) ==> extends
       (mk_infinity_ctxt_hl b1 b2 X) X /\ extends X init_ctxt /\ ~((implode
       "ind") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd
       ctxt)) ctxt)) X)) /\
     DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       consts_of_upd ctxt)) ctxt)) X)) {(implode "ONE_ONE"),(implode "ONTO")}`,
  CHEAT_TAC);;

let fhol_light_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) ==>
   (!ctxt. extends ctxt init_ctxt /\ fhol_light_ctxt ctxt ==>
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
       (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
       ctxt)) ctxt) /\ (?i. models0 mem i ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt)))`,
  CHEAT_TAC);;

let hol_light_has_model = prove
 (`is_set_theory (mem:'U->'U->bool) /\ (?inf'. is_infinite (mem:'U->'U->bool)
  inf') ==>
   (!ctxt. extends ctxt init_ctxt /\ hol_light_ctxt ctxt ==>
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP
       (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt))
       ctxt)) ctxt) /\ (?i. models0 mem i ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt)))`,
  CHEAT_TAC);;

let init_light_consistent = prove
 (`!ctxt. extends ctxt init_ctxt /\ (\l. ALL (\u. !p. ~(u = NewAxiom p)) l)
  ctxt ==>
     consistent_theory ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt)`,
  CHEAT_TAC);;

let fhol_light_consistent = prove
 (`!ctxt. extends ctxt init_ctxt /\ fhol_light_ctxt ctxt ==>
     consistent_theory ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt)`,
  CHEAT_TAC);;

let hol_light_consistent = prove
 (`(?inf'. is_infinite V_mem inf') ==>
   (!ctxt. extends ctxt init_ctxt /\ hol_light_ctxt ctxt ==>
     consistent_theory ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt))`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   The shapes are realisable

   The results above are conditional on a context both extending init_ctxt
   and having one of the shapes, and nothing so far rules out those two
   conditions being jointly unsatisfiable - which would leave the results
   true but empty, the same defect the kernel channel had before it carried
   the extension. So exhibit a context of each shape that really is a
   definitional extension of the initial context. The measured context below
   says more, since it is a context a session actually reached, but it is
   compared against a translation of the kernel printout prepared outside
   the logic; these three owe nothing to anything outside it.
   ------------------------------------------------------------------------ *)

let eta_cl_extends = prove
 (`!ctxt. is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
  ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
  ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) ==> extends
  (mk_eta_ctxt_cl ctxt) ctxt`,
  CHEAT_TAC);;

let select_cl_extends = prove
 (`!ctxt. is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
  ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
  ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) /\ ~((implode
  "@") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
  ctxt)) ctxt)) ==> extends (mk_select_ctxt_cl ctxt) ctxt`,
  CHEAT_TAC);;

(* the two definitions of the infinity block, over any bool signature that
   has not used their names - in particular over one that has already
   declared ind, which is where HOL Light puts them *)

(* [local] *)
let ONE_ONE_def_updates = prove
 (`!b ctxt.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\ is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt) /\ ~((implode "ONE_ONE") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ==> updates ((\x t.
       ConstSpec [((holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
       "A"))),t)] ((===) (holSyntax_Var (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))) (typeof t)) t)) (implode "ONE_ONE")
       (holSyntax_Abs (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode
         "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
         (implode "B"))))
         ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "x1") (holSyntax_Tyvar (implode
           "A")) ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s
           t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "x2") (holSyntax_Tyvar (implode
           "A"))
           ((\p1 p2. holSyntax_Comb (holSyntax_Comb (holSyntax_Const
             (implode "==>") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
             (holSyntax_Tyapp (implode "bool") []) ((\s t. holSyntax_Tyapp
             (implode "fun") [s; t]) (holSyntax_Tyapp (implode "bool") [])
             (holSyntax_Tyapp (implode "bool") [])))) p1) p2) ((===)
             (holSyntax_Comb (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode
             "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
             (implode "B")))) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
             (implode "A")))) (holSyntax_Comb (holSyntax_Var b ((\s t.
             holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyvar (implode
             "A")) (holSyntax_Tyvar (implode "B")))) (holSyntax_Var (implode
             "x2") (holSyntax_Tyvar (implode "A")))))
                    ((===) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
                      (implode "A"))) (holSyntax_Var (implode "x2")
                      (holSyntax_Tyvar (implode "A"))))))))) ctxt`,
  CHEAT_TAC);;

(* [local] *)
let ONTO_def_updates = prove
 (`!b ctxt.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\ is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt) /\ ~((implode "ONTO") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ==>
       updates ((\x t. ConstSpec [((holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))),t)] ((===) (holSyntax_Var
         (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))) (typeof
         t)) t)) (implode "ONTO")
       (holSyntax_Abs (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode
         "fun") [s; t]) (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar
         (implode "B"))))
         ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "!") ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) ty (holSyntax_Tyapp (implode "bool") []))
           (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Abs
           (holSyntax_Var (holSyntax_Var (implode "x") (holSyntax_Tyvar
           (implode "A"))) ty) p)) (implode "y") (holSyntax_Tyvar (implode
           "B")) ((\x ty p. holSyntax_Comb (holSyntax_Const (implode "?")
           ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
           (implode "bool") [])) (holSyntax_Tyapp (implode "bool") [])))
           (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
           (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "x")
           (holSyntax_Tyvar (implode "A")) ((===) (holSyntax_Var (implode
           "y") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
           (holSyntax_Var b ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
           (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B"))))
           (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
           "A"))))))))) ctxt`,
  CHEAT_TAC);;

(* INFINITY_AX is well formed as soon as ind and the two constants are
   there, whatever the definitions bound them with *)

(* [local] *)
let infinity_ax_updates = prove
 (`!ctxt.
     is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt) /\
     FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt) (implode "ONE_ONE") = SOME ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
       (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B")))
       (holSyntax_Tyapp (implode "bool") [])) /\
     FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
       ctxt)) ctxt) (implode "ONTO") = SOME ((\s t. holSyntax_Tyapp (implode
       "fun") [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
       (holSyntax_Tyvar (implode "A")) (holSyntax_Tyvar (implode "B")))
       (holSyntax_Tyapp (implode "bool") [])) /\
     FLOOKUP ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt) (implode "ind") = SOME 0 ==>
       updates (NewAxiom ((\x ty p. holSyntax_Comb (holSyntax_Const
         (implode "?") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) ((\s
         t. holSyntax_Tyapp (implode "fun") [s; t]) ty (holSyntax_Tyapp
         (implode "bool") [])) (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Abs (holSyntax_Var (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) ty) p)) (implode "f") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "ind") []) (holSyntax_Tyapp (implode "ind") [])) ((\p1 p2.
         holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "/\\") ((\s
         t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "bool") []) ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
         (holSyntax_Tyapp (implode "bool") []) (holSyntax_Tyapp (implode
         "bool") [])))) p1) p2) ((\f. holSyntax_Comb (holSyntax_Const
         (implode "ONE_ONE") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
         (typeof f) (holSyntax_Tyapp (implode "bool") []))) f) (holSyntax_Var
         (implode "f") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
         (holSyntax_Tyapp (implode "ind") []) (holSyntax_Tyapp (implode
         "ind") [])))) ((\p. holSyntax_Comb (holSyntax_Const (implode "~")
         ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
         (implode "bool") []) (holSyntax_Tyapp (implode "bool") []))) p)
         ((\f. holSyntax_Comb (holSyntax_Const (implode "ONTO") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (typeof f) (holSyntax_Tyapp
         (implode "bool") []))) f) (holSyntax_Var (implode "f") ((\s t.
         holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
         "ind") []) (holSyntax_Tyapp (implode "ind") [])))))))) ctxt`,
  CHEAT_TAC);;

let infinity_hl_extends = prove
 (`!b1 b2 ctxt.
     theory_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
       list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
       ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd
       ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd.
       APPEND (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
       ctxt) /\ is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt.
       alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt))
       ctxt) /\
     DISJOINT (FDOM ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP
       consts_of_upd ctxt)) ctxt)) ctxt)) {(implode "ONE_ONE"),(implode
       "ONTO")} /\ ~((implode "ind") IN FDOM ((\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt)) ==> extends
       (mk_infinity_ctxt_hl b1 b2 ctxt) ctxt`,
  CHEAT_TAC);;

let init_light_nonempty = prove
 (`?ctxt. extends ctxt init_ctxt /\ (\l. ALL (\u. !p. ~(u = NewAxiom p)) l)
  ctxt`,
  CHEAT_TAC);;

(* the shapes with nothing interleaved anywhere *)

(* [local] *)
let fhol_light_base_extends = prove
 (`extends (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))
     init_ctxt /\
     is_bool_sig ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
       ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) (mk_select_ctxt_cl
       (mk_eta_ctxt_cl
       (mk_bool_ctxt init_ctxt))))`,
  CHEAT_TAC);;

let fhol_light_nonempty = prove
 (`?ctxt. extends ctxt init_ctxt /\ fhol_light_ctxt ctxt`,
  CHEAT_TAC);;

let hol_light_nonempty = prove
 (`?ctxt. extends ctxt init_ctxt /\ hol_light_ctxt ctxt`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------
   The measured context.

   What follows is the first 42 updates - newest first, so the oldest
   position 1 is last - of the record the Candle kernel printed for a
   session that loaded core HOL Light. It is a mechanical retranslation of
   that record's s-expressions through the grammar of print_thm, so the
   theorems below compare the definitions above against the kernel's own
   output rather than against a hand-written guess. Beyond position 42 the
   session declares no further axiom.

   The two generated binder names are the only session-dependent part.
   ------------------------------------------------------------------------ *)

let measured_prefix_def = new_definition
  `measured_prefix =
     [
       // 42
       NewAxiom (holSyntax_Comb (holSyntax_Const (implode "?")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "ind") []; holSyntax_Tyapp (implode "ind")
         []]; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []]))
       (holSyntax_Abs (holSyntax_Var (implode "f") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp (implode "ind") []; holSyntax_Tyapp (implode
         "ind") []])) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb (holSyntax_Const (implode "ONE_ONE") (holSyntax_Tyapp
         (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "ind") [];
         holSyntax_Tyapp (implode "ind") []]; holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Var
       (implode "f") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "ind") []; holSyntax_Tyapp (implode "ind") []]))))
         (holSyntax_Comb (holSyntax_Const (implode "~")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "bool") []])) (holSyntax_Comb
         (holSyntax_Const (implode "ONTO")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "ind") []; holSyntax_Tyapp (implode "ind")
         []]; holSyntax_Tyapp
       (implode "bool") []])) (holSyntax_Var (implode "f") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "ind") []; holSyntax_Tyapp
         (implode "ind")
       []])))))));
       // 41
       ConstSpec [((implode "ONTO"),holSyntax_Abs (holSyntax_Var (implode
         "_2045") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode
         "A"); holSyntax_Tyvar
       (implode "B")])) (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
       (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Abs (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode
         "B"))) (holSyntax_Comb (holSyntax_Const
       (implode "?") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp
       (implode "bool") []])) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "y")
       (holSyntax_Tyvar (implode "B")))) (holSyntax_Comb (holSyntax_Var
         (implode "_2045") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")]))
       (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))))))))))]
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyapp (implode "bool") []];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp
       (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode "ONTO") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyapp (implode "bool") []]))) (holSyntax_Abs (holSyntax_Var
         (implode "_2045") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")])) (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Abs (holSyntax_Var (implode "y")
       (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb (holSyntax_Const
         (implode "?") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []])) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "B")))) (holSyntax_Comb (holSyntax_Var
         (implode "_2045") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")])) (holSyntax_Var (implode "x") (holSyntax_Tyvar
         (implode "A")))))))))));
       // 40
       ConstSpec [((implode "ONE_ONE"),holSyntax_Abs (holSyntax_Var (implode
         "_2040") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode
         "A"); holSyntax_Tyvar
       (implode "B")])) (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Abs (holSyntax_Var (implode "x1") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Comb
       (holSyntax_Const (implode "!") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []];
       holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs (holSyntax_Var
         (implode "x2") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const
       (implode "==>") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb (holSyntax_Var
         (implode "_2040") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")])) (holSyntax_Var (implode "x1") (holSyntax_Tyvar
         (implode "A"))))) (holSyntax_Comb (holSyntax_Var
       (implode "_2040") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")])) (holSyntax_Var
         (implode "x2") (holSyntax_Tyvar
       (implode "A")))))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "x1") (holSyntax_Tyvar (implode "A"))))
         (holSyntax_Var (implode "x2")
       (holSyntax_Tyvar (implode "A"))))))))))] (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyapp (implode "bool") []];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "ONE_ONE") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp
         (implode "bool") []]))) (holSyntax_Abs (holSyntax_Var (implode
         "_2040") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")]))
         (holSyntax_Comb (holSyntax_Const (implode "!") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs (holSyntax_Var
         (implode "x1") (holSyntax_Tyvar
       (implode "A"))) (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Abs (holSyntax_Var (implode "x2") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Comb (holSyntax_Comb
       (holSyntax_Const (implode "==>") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar
       (implode "B"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Var (implode "_2040")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")])) (holSyntax_Var (implode "x1")
         (holSyntax_Tyvar (implode "A"))))) (holSyntax_Comb
       (holSyntax_Var (implode "_2040") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")]))
         (holSyntax_Var (implode "x2") (holSyntax_Tyvar
       (implode "A")))))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "x1") (holSyntax_Tyvar (implode "A"))))
         (holSyntax_Var (implode "x2")
       (holSyntax_Tyvar (implode "A")))))))))));
       // 39
       NewType (implode "ind") 0;
       // 38
       ConstSpec [((implode "PASSOC"),holSyntax_Abs (holSyntax_Var (implode
         "_1297") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "prod")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar (implode "C")];
         holSyntax_Tyvar (implode "D")])) (holSyntax_Abs
       (holSyntax_Var (implode "_1298") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
       (implode "C")]])) (holSyntax_Comb (holSyntax_Var (implode "_1297")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar (implode "D")]))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
       (implode ",") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "C"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
       (implode "C")]]])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode ",") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")]]]))
         (holSyntax_Comb (holSyntax_Const (implode "FST")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
       (implode "C")]]; holSyntax_Tyvar (implode "A")])) (holSyntax_Var
         (implode "_1298") (holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]])))) (holSyntax_Comb (holSyntax_Const (implode "FST")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar (implode "B")]))
         (holSyntax_Comb (holSyntax_Const (implode "SND")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
       (implode "C")]]; holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyvar (implode "C")]])) (holSyntax_Var
         (implode "_1298") (holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]])))))) (holSyntax_Comb
       (holSyntax_Const (implode "SND") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar
       (implode "C")])) (holSyntax_Comb (holSyntax_Const (implode "SND")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]]; holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyvar (implode "C")]]))
       (holSyntax_Var (implode "_1298") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
       (implode "C")]]))))))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "prod") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyvar (implode "C")];
       holSyntax_Tyvar (implode "D")]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
       (implode "B"); holSyntax_Tyvar (implode "C")]]; holSyntax_Tyvar
         (implode "D")]]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar
       (implode "D")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyvar (implode "C")]]; holSyntax_Tyvar (implode "D")]];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "PASSOC") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")];
       holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar (implode "D")];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]]; holSyntax_Tyvar (implode "D")]]))) (holSyntax_Abs
         (holSyntax_Var (implode "_1297")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
       (implode "C")]; holSyntax_Tyvar (implode "D")])) (holSyntax_Abs
         (holSyntax_Var (implode "_1298") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]])) (holSyntax_Comb (holSyntax_Var (implode "_1297")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar
       (implode "D")])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode ",") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "C"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
         (implode "C")]]])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode ",") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "B")]]])) (holSyntax_Comb (holSyntax_Const (implode "FST")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]]; holSyntax_Tyvar (implode "A")]))
         (holSyntax_Var (implode "_1298") (holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]])))) (holSyntax_Comb
       (holSyntax_Const (implode "FST") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar
       (implode "B")])) (holSyntax_Comb (holSyntax_Const (implode "SND")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]]; holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyvar (implode "C")]]))
       (holSyntax_Var (implode "_1298") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
       (implode "C")]])))))) (holSyntax_Comb (holSyntax_Const (implode
         "SND") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "prod") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyvar (implode "C")]; holSyntax_Tyvar (implode "C")]))
         (holSyntax_Comb (holSyntax_Const (implode "SND") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar (implode "C")]];
         holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
       (implode "B"); holSyntax_Tyvar (implode "C")]])) (holSyntax_Var
         (implode "_1298") (holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar (implode
         "C")]])))))))));
       // 37
       ConstSpec [((implode "UNCURRY"),holSyntax_Abs (holSyntax_Var (implode
         "_1280") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode
         "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]])) (holSyntax_Abs (holSyntax_Var (implode "_1281")
         (holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyvar (implode "B")])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Var (implode "_1280") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]])) (holSyntax_Comb (holSyntax_Const
         (implode "FST") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar (implode "A")]))
         (holSyntax_Var (implode "_1281") (holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")])))) (holSyntax_Comb (holSyntax_Const (implode "SND")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar (implode "B")]))
         (holSyntax_Var (implode "_1281") (holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]))))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyvar (implode "C")]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
       (implode "C")]]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar (implode "C")]];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "B")]; holSyntax_Tyvar (implode "C")]]; holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "UNCURRY")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]]; holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
         (implode "C")]]))) (holSyntax_Abs (holSyntax_Var
       (implode "_1280") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyvar (implode "C")]]))
       (holSyntax_Abs (holSyntax_Var (implode "_1281") (holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")])) (holSyntax_Comb (holSyntax_Comb
       (holSyntax_Var (implode "_1280") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
       (implode "C")]])) (holSyntax_Comb (holSyntax_Const (implode "FST")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar (implode "A")]))
         (holSyntax_Var (implode "_1281") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "B")])))) (holSyntax_Comb (holSyntax_Const (implode "SND")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar (implode "B")]))
         (holSyntax_Var (implode "_1281") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "B")])))))));
       // 36
       ConstSpec [((implode "CURRY"),holSyntax_Abs (holSyntax_Var (implode
         "_1259") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "prod") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
         (implode "C")])) (holSyntax_Abs (holSyntax_Var (implode "_1260")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
       (implode "_1261") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
         (holSyntax_Var (implode "_1259") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyvar (implode "C")])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode ",") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]]])) (holSyntax_Var (implode "_1260")
         (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "_1261")
         (holSyntax_Tyvar
       (implode "B"))))))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
         (implode "C")]; holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar (implode "C")]]];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyvar (implode "C")];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]]]; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "CURRY")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyvar (implode "C")]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]]]))) (holSyntax_Abs (holSyntax_Var (implode "_1259")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar (implode "C")]))
         (holSyntax_Abs (holSyntax_Var (implode "_1260")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "_1261") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
         (holSyntax_Var (implode "_1259") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
         (implode "C")])) (holSyntax_Comb (holSyntax_Comb
       (holSyntax_Const (implode ",") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]]])) (holSyntax_Var (implode "_1260") (holSyntax_Tyvar
         (implode "A")))) (holSyntax_Var
       (implode "_1261") (holSyntax_Tyvar (implode "B")))))))));
       // 35
       ConstSpec [((implode "SND"),holSyntax_Abs (holSyntax_Var (implode
         "p") (holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]))
       (holSyntax_Comb (holSyntax_Const (implode "@") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool")
       []]; holSyntax_Tyvar (implode "B")])) (holSyntax_Abs (holSyntax_Var
         (implode "y") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
         (holSyntax_Const (implode "?") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool") []]))
       (holSyntax_Abs (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode ",") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]]])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "B"))))))))))] (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
       (implode "B")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")];
       holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "SND") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyvar (implode "B")]))) (holSyntax_Abs (holSyntax_Var
         (implode "p") (holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")]))
         (holSyntax_Comb (holSyntax_Const (implode "@") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyvar (implode "B")])) (holSyntax_Abs (holSyntax_Var
         (implode "y") (holSyntax_Tyvar (implode "B")))
       (holSyntax_Comb (holSyntax_Const (implode "?") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "bool")
       []]; holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs
         (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
       (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "p")
       (holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode ",") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]]])) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "B")))))))))));
       // 34
       ConstSpec [((implode "FST"),holSyntax_Abs (holSyntax_Var (implode
         "p") (holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]))
       (holSyntax_Comb (holSyntax_Const (implode "@") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "bool")
       []]; holSyntax_Tyvar (implode "A")])) (holSyntax_Abs (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
         (holSyntax_Const (implode "?") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool") []]))
       (holSyntax_Abs (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode
         "B"))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode ",") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]]])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "B"))))))))))] (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyvar
       (implode "A")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")];
       holSyntax_Tyvar (implode "A")]; holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "FST") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyvar (implode "A")]))) (holSyntax_Abs (holSyntax_Var
         (implode "p") (holSyntax_Tyapp (implode "prod")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")]))
         (holSyntax_Comb (holSyntax_Const (implode "@") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyvar (implode "A")])) (holSyntax_Abs (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A")))
       (holSyntax_Comb (holSyntax_Const (implode "?") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool")
       []]; holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs
         (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode "B")))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
       (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "p")
       (holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode ",") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]]])) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "B")))))))))));
       // 33
       ConstSpec [((implode ","),holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "y") (holSyntax_Tyvar (implode "B")))
       (holSyntax_Comb (holSyntax_Const (implode "ABS_prod")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]]; holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "B")]])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "mk_pair") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]]]])) (holSyntax_Var (implode
         "x") (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar
       (implode "B")))))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "prod") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")]]];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
       (implode "prod") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]]]; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode ",") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "prod") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]]]))) (holSyntax_Abs (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs
         (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode "B")))
       (holSyntax_Comb (holSyntax_Const (implode "ABS_prod")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]]; holSyntax_Tyapp (implode "prod")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "B")]])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "mk_pair") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]]]])) (holSyntax_Var (implode
         "x") (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar
       (implode "B"))))))));
       // 32
       TypeDefn (implode "prod") (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Comb (holSyntax_Const (implode "?") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Abs (holSyntax_Var (implode "a")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Const
         (implode "?") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []])) (holSyntax_Abs (holSyntax_Var (implode "b")
         (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Var
       (implode "x") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool")
       []]]))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "mk_pair") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode
         "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]]]])) (holSyntax_Var (implode
         "a") (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "b")
         (holSyntax_Tyvar
       (implode "B")))))))))) (implode "ABS_prod") (implode "REP_prod");
       // 31
       ConstSpec [((implode "mk_pair"),holSyntax_Abs (holSyntax_Var (implode
         "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "y") (holSyntax_Tyvar
       (implode "B"))) (holSyntax_Abs (holSyntax_Var (implode "a")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "b") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "a")
       (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "b")
       (holSyntax_Tyvar (implode "B")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "B")))))))))] (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]]]]; holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]]]]; holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "mk_pair") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]]]])))
       (holSyntax_Abs (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Abs (holSyntax_Var (implode "y") (holSyntax_Tyvar
         (implode "B"))) (holSyntax_Abs (holSyntax_Var (implode "a")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "b") (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "/\\")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "a") (holSyntax_Tyvar
         (implode "A")))) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "b") (holSyntax_Tyvar
         (implode "B")))) (holSyntax_Var (implode "y")
       (holSyntax_Tyvar (implode "B"))))))))));
       // 30
       ConstSpec [((implode "_FUNCTION"),holSyntax_Abs (holSyntax_Var
         (implode "r") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "COND")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar (implode "B")]]]))
         (holSyntax_Comb (holSyntax_Const (implode "?!")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Comb (holSyntax_Var (implode "r") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A")))))) (holSyntax_Comb (holSyntax_Const
         (implode "@") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar
         (implode "B")])) (holSyntax_Comb
       (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
         "A")))))) (holSyntax_Comb (holSyntax_Const (implode "@")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyvar (implode "B")])) (holSyntax_Abs
         (holSyntax_Var (implode "z") (holSyntax_Tyvar
       (implode "B"))) (holSyntax_Const (implode "F") (holSyntax_Tyapp
         (implode "bool") [])))))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "B"); holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]]; holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode
         "B")]]; holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "_FUNCTION") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode
         "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "B")]]))) (holSyntax_Abs (holSyntax_Var (implode "r")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "B"); holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Abs
         (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
       (holSyntax_Const (implode "COND") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "B")]]])) (holSyntax_Comb (holSyntax_Const
         (implode "?!") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Comb
       (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
         "A")))))) (holSyntax_Comb (holSyntax_Const (implode "@")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyvar (implode "B")])) (holSyntax_Comb
         (holSyntax_Var (implode "r") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A")))))) (holSyntax_Comb (holSyntax_Const
         (implode "@") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar (implode
         "B")])) (holSyntax_Abs (holSyntax_Var (implode "z") (holSyntax_Tyvar
         (implode "B"))) (holSyntax_Const (implode "F")
       (holSyntax_Tyapp (implode "bool") []))))))));
       // 29
       ConstSpec [((implode "_MATCH"),holSyntax_Abs (holSyntax_Var (implode
         "e") (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "r") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "COND")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar (implode "B")]]]))
         (holSyntax_Comb (holSyntax_Const (implode "?!")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Comb (holSyntax_Var (implode "r") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "e")
         (holSyntax_Tyvar (implode "A")))))) (holSyntax_Comb (holSyntax_Const
         (implode "@") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar
         (implode "B")])) (holSyntax_Comb
       (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "e") (holSyntax_Tyvar (implode
         "A")))))) (holSyntax_Comb (holSyntax_Const (implode "@")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyvar (implode "B")])) (holSyntax_Abs
         (holSyntax_Var (implode "z") (holSyntax_Tyvar
       (implode "B"))) (holSyntax_Const (implode "F") (holSyntax_Tyapp
         (implode "bool") [])))))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyvar
         (implode "B")]]; holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyvar (implode
         "B")]]; holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "_MATCH") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool") []]];
         holSyntax_Tyvar (implode "B")]])))
       (holSyntax_Abs (holSyntax_Var (implode "e") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Abs (holSyntax_Var (implode "r") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
       (implode "COND") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "B")]]])) (holSyntax_Comb (holSyntax_Const (implode "?!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Comb (holSyntax_Var (implode "r")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]]))
       (holSyntax_Var (implode "e") (holSyntax_Tyvar (implode "A"))))))
         (holSyntax_Comb (holSyntax_Const (implode "@") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyvar (implode "B")])) (holSyntax_Comb (holSyntax_Var
         (implode "r") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "e")
       (holSyntax_Tyvar (implode "A")))))) (holSyntax_Comb (holSyntax_Const
         (implode "@") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar (implode
         "B")])) (holSyntax_Abs (holSyntax_Var (implode "z") (holSyntax_Tyvar
         (implode "B"))) (holSyntax_Const (implode "F")
       (holSyntax_Tyapp (implode "bool") []))))))));
       // 28
       ConstSpec [((implode "_GUARDED_PATTERN"),holSyntax_Abs (holSyntax_Var
         (implode "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Abs
       (holSyntax_Var (implode "g") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Abs (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode
         "bool") [])) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode "g") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Var (implode "r")
       (holSyntax_Tyapp (implode "bool") [])))))))] (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]]]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]]]; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Var (implode "_GUARDED_PATTERN")
         (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]]]))) (holSyntax_Abs (holSyntax_Var (implode "p")
         (holSyntax_Tyapp (implode "bool")
       [])) (holSyntax_Abs (holSyntax_Var (implode "g") (holSyntax_Tyapp
         (implode "bool") [])) (holSyntax_Abs (holSyntax_Var (implode "r")
         (holSyntax_Tyapp (implode "bool") []))
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "/\\")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode
         "bool") [])))
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "/\\")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Var (implode "g") (holSyntax_Tyapp (implode
         "bool") [])))
       (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "bool")
         []))))))));
       // 27
       ConstSpec [((implode "_UNGUARDED_PATTERN"),holSyntax_Abs
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Abs
       (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "/\\")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "bool")
         []]]))
       (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "bool")
         [])))))] (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool") []]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "bool")
         []]];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "_UNGUARDED_PATTERN") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]])))
         (holSyntax_Abs
       (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Abs (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode
         "bool") [])) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Var (implode "r")
       (holSyntax_Tyapp (implode "bool") []))))));
       // 26
       ConstSpec [((implode "_SEQPATTERN"),holSyntax_Abs (holSyntax_Var
         (implode "r") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Abs (holSyntax_Var (implode "s")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Abs (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "COND") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]]]])) (holSyntax_Comb (holSyntax_Const (implode "?")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Abs (holSyntax_Var (implode "y")
       (holSyntax_Tyvar (implode "B"))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))))
         (holSyntax_Var (implode "y") (holSyntax_Tyvar
       (implode "B"))))))) (holSyntax_Comb (holSyntax_Var (implode "r")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "B"); holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A"))))) (holSyntax_Comb
         (holSyntax_Var (implode "s") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))))))))] (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
       (implode "bool") []]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
       (implode "bool") []]]]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyapp (implode "bool") []]]]];
         holSyntax_Tyapp (implode "bool") []]]))
       (holSyntax_Var (implode "_SEQPATTERN") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode
         "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]]]]))) (holSyntax_Abs
         (holSyntax_Var (implode "r") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Abs
       (holSyntax_Var (implode "s") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Abs (holSyntax_Var (implode "x") (holSyntax_Tyvar
         (implode "A"))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "COND")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool")
       []]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyapp (implode "bool") []]]]])) (holSyntax_Comb
         (holSyntax_Const (implode "?")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Abs (holSyntax_Var (implode "y") (holSyntax_Tyvar
         (implode "B"))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Var
         (implode "r") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "B"))))))) (holSyntax_Comb (holSyntax_Var
         (implode "r") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))))) (holSyntax_Comb (holSyntax_Var
         (implode "s") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "B"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
         "A")))))))));
       // 25
       ConstSpec [((implode "GEQ"),holSyntax_Abs (holSyntax_Var (implode
         "a") (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "b") (holSyntax_Tyvar (implode "A")))
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var
         (implode "a") (holSyntax_Tyvar (implode "A")))) (holSyntax_Var
         (implode "b") (holSyntax_Tyvar
       (implode "A"))))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []]];
         holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "GEQ") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []]]))) (holSyntax_Abs
         (holSyntax_Var (implode "a") (holSyntax_Tyvar (implode "A")))
         (holSyntax_Abs (holSyntax_Var (implode "b") (holSyntax_Tyvar
       (implode "A"))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var (implode "a") (holSyntax_Tyvar (implode "A"))))
         (holSyntax_Var (implode "b") (holSyntax_Tyvar
       (implode "A")))))));
       // 24
       ConstSpec [((implode "GABS"),holSyntax_Abs (holSyntax_Var (implode
         "P") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Comb (holSyntax_Const (implode "@") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp
       (implode "bool") []]; holSyntax_Tyvar (implode "A")])) (holSyntax_Var
         (implode "P") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp
       (implode "bool") []]))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar (implode "A")];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyvar (implode "A")];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "GABS") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar (implode
         "A")]))) (holSyntax_Abs (holSyntax_Var (implode "P") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []])) (holSyntax_Comb
         (holSyntax_Const (implode "@") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar
         (implode "A")])) (holSyntax_Var (implode "P") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []])))));
       // 23
       ConstSpec [((implode "LET_END"),holSyntax_Abs (holSyntax_Var (implode
         "t") (holSyntax_Tyvar (implode "A"))) (holSyntax_Var (implode "t")
         (holSyntax_Tyvar
       (implode "A"))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "A")]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "A")]; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "LET_END")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "A")])))
       (holSyntax_Abs (holSyntax_Var (implode "t") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Var (implode "t") (holSyntax_Tyvar (implode
         "A")))));
       // 22
       ConstSpec [((implode "LET"),holSyntax_Abs (holSyntax_Var (implode
         "f") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]))
       (holSyntax_Abs (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Comb (holSyntax_Var (implode "f") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")])) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")]];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]]; holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "LET") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode
         "A"); holSyntax_Tyvar (implode "B")];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")]]))) (holSyntax_Abs (holSyntax_Var
         (implode "f") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")]))
         (holSyntax_Abs (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Comb (holSyntax_Var (implode "f")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")])) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A")))))));
       // 21
       ConstSpec [((implode "one"),holSyntax_Comb (holSyntax_Const (implode
         "@") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "1")
       []; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "1") []])) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyapp (implode "1") []))
       (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool")
         []))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "1") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "1") []; holSyntax_Tyapp (implode "bool")
         []]])) (holSyntax_Var
       (implode "one") (holSyntax_Tyapp (implode "1") []))) (holSyntax_Comb
         (holSyntax_Const (implode "@") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "1") []; holSyntax_Tyapp (implode "bool")
         []]; holSyntax_Tyapp (implode "1") []])) (holSyntax_Abs (holSyntax_Var
         (implode "x") (holSyntax_Tyapp
       (implode "1") [])) (holSyntax_Const (implode "T") (holSyntax_Tyapp
         (implode "bool") [])))));
       // 20
       TypeDefn (implode "1") (holSyntax_Abs (holSyntax_Var (implode "b")
         (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var (implode "b")
         (holSyntax_Tyapp (implode "bool")
       []))) (implode "one_ABS") (implode "one_REP");
       // 19
       ConstSpec [((implode "I"),holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))))]
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
       (implode "A")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "A")]; holSyntax_Tyapp (implode "bool")
       []]])) (holSyntax_Var (implode "I") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "A")])))
         (holSyntax_Abs (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A")))));
       // 18
       ConstSpec [((implode "o"),holSyntax_Abs (holSyntax_Var (implode "f")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "B");
         holSyntax_Tyvar (implode "C")]))
       (holSyntax_Abs (holSyntax_Var (implode "g") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode
         "B")])) (holSyntax_Abs (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Var
         (implode "f") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyvar (implode "C")]))
       (holSyntax_Comb (holSyntax_Var (implode "g") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")])) (holSyntax_Var (implode "x") (holSyntax_Tyvar
       (implode "A"))))))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
         (implode "C")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyvar (implode "B")]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "C")]]];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyvar (implode "C")]; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "C")]]]; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "o") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "B"); holSyntax_Tyvar
       (implode "C")]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "C")]]])))
         (holSyntax_Abs (holSyntax_Var (implode "f") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "B");
       holSyntax_Tyvar (implode "C")])) (holSyntax_Abs (holSyntax_Var
         (implode "g") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")])) (holSyntax_Abs
       (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
         (holSyntax_Comb (holSyntax_Var (implode "f") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "B"); holSyntax_Tyvar
       (implode "C")])) (holSyntax_Comb (holSyntax_Var (implode "g")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A")))))))));
       // 17
       ConstSpec [((implode "COND"),holSyntax_Abs (holSyntax_Var (implode
         "t") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Abs
         (holSyntax_Var (implode "t1")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Abs (holSyntax_Var
         (implode "t2") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
         (holSyntax_Const (implode "@") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar (implode "A")]))
         (holSyntax_Abs (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "/\\") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const
       (implode "==>") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "t") (holSyntax_Tyapp
       (implode "bool") []))) (holSyntax_Const (implode "T")
         (holSyntax_Tyapp (implode "bool") [])))) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]]))
       (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))))
         (holSyntax_Var (implode "t1") (holSyntax_Tyvar (implode "A"))))))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
       (implode "==>") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "t") (holSyntax_Tyapp
       (implode "bool") []))) (holSyntax_Const (implode "F")
         (holSyntax_Tyapp (implode "bool") [])))) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]]))
       (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))))
         (holSyntax_Var (implode "t2") (holSyntax_Tyvar (implode
         "A")))))))))))] (holSyntax_Comb (holSyntax_Comb
       (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "A")]]];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyvar (implode "A")]]]; holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "COND")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar
       (implode "A")]]]))) (holSyntax_Abs (holSyntax_Var (implode "t")
         (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Abs (holSyntax_Var
         (implode "t1") (holSyntax_Tyvar (implode "A")))
       (holSyntax_Abs (holSyntax_Var (implode "t2") (holSyntax_Tyvar
         (implode "A"))) (holSyntax_Comb (holSyntax_Const (implode "@")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyvar (implode "A")])) (holSyntax_Abs (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A")))
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "/\\")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "==>") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool")
       []]])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "t") (holSyntax_Tyapp
         (implode "bool")
       []))) (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode
         "bool") [])))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const
         (implode "=") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A")))) (holSyntax_Var (implode "t1")
         (holSyntax_Tyvar (implode "A")))))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "==>")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "t")
         (holSyntax_Tyapp
       (implode "bool") []))) (holSyntax_Const (implode "F")
         (holSyntax_Tyapp (implode "bool") [])))) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]]))
       (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A"))))
         (holSyntax_Var (implode "t2") (holSyntax_Tyvar (implode
         "A"))))))))))));
       // 16
       NewAxiom (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "bool")
         []]))
       (holSyntax_Abs (holSyntax_Var (implode "P") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode
         "bool") []])) (holSyntax_Comb (holSyntax_Const
       (implode "!") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp
       (implode "bool") []])) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "==>")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Comb (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))))
         (holSyntax_Comb (holSyntax_Var (implode "P") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []])) (holSyntax_Comb
         (holSyntax_Const (implode "@") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyvar
         (implode "A")])) (holSyntax_Var (implode "P") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []])))))))));
       // 15
       NewConst (implode "@") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []];
       holSyntax_Tyvar (implode "A")]);
       // 14
       NewAxiom (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Abs (holSyntax_Var
       (implode "t") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyvar (implode "B")])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar (implode "B")];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyvar
         (implode "B")]; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Abs
         (holSyntax_Var (implode "x") (holSyntax_Tyvar
       (implode "A"))) (holSyntax_Comb (holSyntax_Var (implode "t")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")])) (holSyntax_Var (implode "x")
       (holSyntax_Tyvar (implode "A")))))) (holSyntax_Var (implode "t")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyvar (implode "B")])))));
       // 13
       ConstSpec [((implode "_FALSITY_"),holSyntax_Const (implode "F")
         (holSyntax_Tyapp (implode "bool") []))] (holSyntax_Comb
         (holSyntax_Comb
       (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "_FALSITY_") (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Const
       (implode "F") (holSyntax_Tyapp (implode "bool") [])));
       // 12
       ConstSpec [((implode "?!"),holSyntax_Abs (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "/\\") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "bool") []; holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Comb (holSyntax_Const (implode "?")
         (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool") []]))
       (holSyntax_Var (implode "P") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []])))) (holSyntax_Comb (holSyntax_Const
       (implode "!") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp
       (implode "bool") []])) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb (holSyntax_Const
         (implode "!") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Abs
       (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode "A")))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "==>")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb (holSyntax_Var (implode "P") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []])) (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))))) (holSyntax_Comb (holSyntax_Var
         (implode "P") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode "A"))))))
         (holSyntax_Comb (holSyntax_Comb
       (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "x") (holSyntax_Tyvar
         (implode "A")))) (holSyntax_Var (implode "y") (holSyntax_Tyvar
         (implode "A")))))))))))]
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "bool")
         []]; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "?!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "bool") []]; holSyntax_Tyapp (implode "bool") []])))
         (holSyntax_Abs (holSyntax_Var (implode "P") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Const (implode "?")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Var (implode "P") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []])))) (holSyntax_Comb
       (holSyntax_Const (implode "!") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []];
       holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
         (holSyntax_Const (implode "!") (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool") []]))
       (holSyntax_Abs (holSyntax_Var (implode "y") (holSyntax_Tyvar (implode
         "A"))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "==>") (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "bool")
         []]]))
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "/\\")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Comb (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))))
         (holSyntax_Comb (holSyntax_Var (implode "P")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []])) (holSyntax_Var (implode "y")
         (holSyntax_Tyvar (implode "A"))))))
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A")))) (holSyntax_Var
         (implode "y") (holSyntax_Tyvar
       (implode "A"))))))))))));
       // 11
       ConstSpec [((implode "~"),holSyntax_Abs (holSyntax_Var (implode "p")
         (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const
       (implode "==>") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "p")
         (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Const (implode "F")
         (holSyntax_Tyapp
       (implode "bool") []))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Var (implode "~") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []])))
         (holSyntax_Abs (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode
         "bool") [])) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "==>") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Const (implode "F")
       (holSyntax_Tyapp (implode "bool") [])))));
       // 10
       ConstSpec [((implode "F"),holSyntax_Comb (holSyntax_Const (implode
         "!") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs (holSyntax_Var
         (implode "p") (holSyntax_Tyapp
       (implode "bool") [])) (holSyntax_Var (implode "p") (holSyntax_Tyapp
         (implode "bool") []))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "F") (holSyntax_Tyapp
         (implode "bool") []))) (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Abs (holSyntax_Var (implode "p") (holSyntax_Tyapp
         (implode "bool") [])) (holSyntax_Var (implode "p") (holSyntax_Tyapp
         (implode "bool") [])))));
       // 9
       ConstSpec [((implode "\\/"),holSyntax_Abs (holSyntax_Var (implode
         "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Abs
         (holSyntax_Var (implode "q") (holSyntax_Tyapp
       (implode "bool") [])) (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []])) (holSyntax_Abs (holSyntax_Var (implode "r")
         (holSyntax_Tyapp (implode "bool")
       [])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "==>")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "==>")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "p") (holSyntax_Tyapp
         (implode "bool") []))) (holSyntax_Var (implode "r") (holSyntax_Tyapp
         (implode "bool")
       [])))) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "==>") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "bool") []; holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool") []]])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "==>")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Var (implode "q") (holSyntax_Tyapp
         (implode "bool") []))) (holSyntax_Var (implode "r") (holSyntax_Tyapp
         (implode "bool")
       [])))) (holSyntax_Var (implode "r") (holSyntax_Tyapp (implode "bool")
         []))))))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "bool") []]]))
       (holSyntax_Var (implode "\\/") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]]))) (holSyntax_Abs
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Abs (holSyntax_Var
       (implode "q") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Comb
         (holSyntax_Const (implode "!") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]; holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs
         (holSyntax_Var (implode "r")
       (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "==>") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb
       (holSyntax_Const (implode "==>") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "p") (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var (implode
         "r") (holSyntax_Tyapp
       (implode "bool") [])))) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "==>") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const
       (implode "==>") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "q")
         (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var (implode "r")
         (holSyntax_Tyapp
       (implode "bool") [])))) (holSyntax_Var (implode "r") (holSyntax_Tyapp
         (implode "bool") [])))))))));
       // 8
       ConstSpec [((implode "?"),holSyntax_Abs (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Comb (holSyntax_Const (implode "!") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []])) (holSyntax_Abs (holSyntax_Var (implode "q")
         (holSyntax_Tyapp (implode "bool") []))
       (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "==>")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Comb (holSyntax_Const (implode "!")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Abs
       (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "==>")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb
       (holSyntax_Var (implode "P") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Var (implode "x") (holSyntax_Tyvar
       (implode "A"))))) (holSyntax_Var (implode "q") (holSyntax_Tyapp
         (implode "bool") [])))))) (holSyntax_Var (implode "q")
         (holSyntax_Tyapp (implode "bool")
       []))))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool")
       []]; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "?") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar
       (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool") []]))) (holSyntax_Abs (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Comb (holSyntax_Const (implode "!") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]))
         (holSyntax_Abs (holSyntax_Var
       (implode "q") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "==>") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb
       (holSyntax_Const (implode "!") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []];
       holSyntax_Tyapp (implode "bool") []])) (holSyntax_Abs (holSyntax_Var
         (implode "x") (holSyntax_Tyvar (implode "A"))) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "==>")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Comb (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Var (implode "x") (holSyntax_Tyvar (implode "A")))))
         (holSyntax_Var (implode "q") (holSyntax_Tyapp (implode "bool")
         [])))))) (holSyntax_Var (implode "q")
       (holSyntax_Tyapp (implode "bool") [])))))));
       // 7
       ConstSpec [((implode "!"),holSyntax_Abs (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool")
       []])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool")
       []]; holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode
         "P") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp
       (implode "bool") []]))) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A"))) (holSyntax_Const (implode "T")
         (holSyntax_Tyapp (implode "bool")
       [])))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar
         (implode "A"); holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool") []];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "!")
         (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A");
       holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []]))) (holSyntax_Abs (holSyntax_Var (implode "P")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool")
         []])) (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyvar (implode "A");
         holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "P")
         (holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
         (implode "bool") []]))) (holSyntax_Abs (holSyntax_Var (implode "x")
         (holSyntax_Tyvar (implode "A")))
       (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode "bool")
         []))))));
       // 6
       ConstSpec [((implode "==>"),holSyntax_Abs (holSyntax_Var (implode
         "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Abs
         (holSyntax_Var (implode "q") (holSyntax_Tyapp
       (implode "bool") [])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const
       (implode "/\\") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Var (implode "p")
         (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Var (implode "q")
         (holSyntax_Tyapp
       (implode "bool") [])))) (holSyntax_Var (implode "p") (holSyntax_Tyapp
         (implode "bool") [])))))] (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "bool") []]]))
       (holSyntax_Var (implode "==>") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]]))) (holSyntax_Abs
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Abs (holSyntax_Var
       (implode "q") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Var (implode "q")
       (holSyntax_Tyapp (implode "bool") [])))) (holSyntax_Var (implode "p")
         (holSyntax_Tyapp (implode "bool") []))))));
       // 5
       ConstSpec [((implode "/\\"),holSyntax_Abs (holSyntax_Var (implode
         "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Abs
         (holSyntax_Var (implode "q") (holSyntax_Tyapp
       (implode "bool") [])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool")
       []]]; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]];
         holSyntax_Tyapp
       (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Abs (holSyntax_Var (implode "f") (holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Var (implode "f") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Var (implode "q")
       (holSyntax_Tyapp (implode "bool") []))))) (holSyntax_Abs
         (holSyntax_Var (implode "f") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Comb
         (holSyntax_Comb (holSyntax_Var (implode "f")
       (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Const (implode "T")
         (holSyntax_Tyapp (implode "bool") []))) (holSyntax_Const (implode "T")
         (holSyntax_Tyapp (implode "bool")
       [])))))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode
         "=") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]];
         holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") [];
       holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Var (implode "/\\") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "bool") []]])))
         (holSyntax_Abs
       (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Abs (holSyntax_Var (implode "q") (holSyntax_Tyapp (implode
         "bool") [])) (holSyntax_Comb
       (holSyntax_Comb (holSyntax_Const (implode "=") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "bool") []]]; holSyntax_Tyapp (implode
         "bool") []];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode
         "bool") []]]; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp
         (implode "bool")
       []]])) (holSyntax_Abs (holSyntax_Var (implode "f") (holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Var (implode "f")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "bool")
         []]]))
       (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Var (implode "q") (holSyntax_Tyapp (implode "bool") [])))))
         (holSyntax_Abs (holSyntax_Var
       (implode "f") (holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
         (implode "bool") []; holSyntax_Tyapp
       (implode "bool") []]])) (holSyntax_Comb (holSyntax_Comb
         (holSyntax_Var (implode "f") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") [];
       holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool") [];
         holSyntax_Tyapp (implode "bool") []]])) (holSyntax_Const (implode "T")
         (holSyntax_Tyapp
       (implode "bool") []))) (holSyntax_Const (implode "T")
         (holSyntax_Tyapp (implode "bool") []))))))));
       // 4
       ConstSpec [((implode "T"),holSyntax_Comb (holSyntax_Comb
         (holSyntax_Const (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp
       (implode "bool") []; holSyntax_Tyapp (implode "bool") []];
         holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool")
       []; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "bool") []]])) (holSyntax_Abs (holSyntax_Var (implode "p")
         (holSyntax_Tyapp (implode "bool")
       [])) (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool")
         [])))) (holSyntax_Abs (holSyntax_Var (implode "p") (holSyntax_Tyapp
         (implode "bool") []))
       (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool")
         []))))] (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp (implode "bool")
         []]]))
       (holSyntax_Var (implode "T") (holSyntax_Tyapp (implode "bool") [])))
         (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "=")
         (holSyntax_Tyapp (implode "fun")
       [holSyntax_Tyapp (implode "fun") [holSyntax_Tyapp (implode "bool")
         []; holSyntax_Tyapp (implode "bool") []]; holSyntax_Tyapp (implode
         "fun") [holSyntax_Tyapp
       (implode "fun") [holSyntax_Tyapp (implode "bool") []; holSyntax_Tyapp
         (implode "bool") []]; holSyntax_Tyapp (implode "bool") []]]))
         (holSyntax_Abs
       (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))
         (holSyntax_Var (implode "p") (holSyntax_Tyapp (implode "bool") []))))
         (holSyntax_Abs (holSyntax_Var
       (implode "p") (holSyntax_Tyapp (implode "bool") [])) (holSyntax_Var
         (implode "p") (holSyntax_Tyapp (implode "bool") [])))));
       // 3
       NewConst (implode "=") (holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp (implode "fun")
         [holSyntax_Tyvar (implode "A"); holSyntax_Tyapp
       (implode "bool") []]]);
       // 2
       NewType (implode "bool") 0;
       // 1
       NewType (implode "fun") 2]`;;

(* ------------------------------------------------------------------------
   Each block agrees with the kernel printout update for update. The index
   arithmetic reads the list newest first: positions 42-39 are the infinity
   block, 16-15 the select block, 14 the eta axiom, and 11-1 the booleans on
   top of the initial context.
   ------------------------------------------------------------------------ *)

let measured_infinity_block = prove
 (`TAKE 4 measured_prefix = mk_infinity_ctxt_hl (implode "_2040") (implode
  "_2045") []`,
  CHEAT_TAC);;

let measured_select_block = prove
 (`TAKE 2 (DROP 26 measured_prefix) = mk_select_ctxt_cl []`,
  CHEAT_TAC);;

let measured_eta_block = prove
 (`TAKE 1 (DROP 28 measured_prefix) = mk_eta_ctxt_cl []`,
  CHEAT_TAC);;

let measured_bool_block = prove
 (`DROP 31 measured_prefix = mk_bool_ctxt init_ctxt`,
  CHEAT_TAC);;

(* the four blocks compose, with positions 38-17 and 13-12 in between and
   nothing at all between the eta and select blocks *)

let measured_prefix_decomposition = prove
 (`measured_prefix =
     mk_infinity_ctxt_hl (implode "_2040") (implode "_2045")
       (APPEND (TAKE 22 (DROP 4 measured_prefix))
        (mk_select_ctxt_cl
          (mk_eta_ctxt_cl
             (APPEND (TAKE 2 (DROP 29 measured_prefix)) (mk_bool_ctxt
               init_ctxt)))))`,
  CHEAT_TAC);;

(* so the guarantee fires on the measured session: whatever the session goes
   on to define after position 42, as long as it declares no further axiom -
   and the record shows it does not - the context it reaches is one of the
   shapes above *)

let measured_prefix_hol_light_ctxt = prove
 (`!l. (\l. ALL (\u. !p. ~(u = NewAxiom p)) l) l ==> hol_light_ctxt (APPEND l
  measured_prefix)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["And";
   "Bool";
   "Fun";
   "Not";
   "mem"];;

(* and the interface *)
let _ = unhide_overloads ();;
