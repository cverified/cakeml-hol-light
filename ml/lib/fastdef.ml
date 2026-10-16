(* ================================================================== *)
(*  HOL Light's machinery for a definition by cases, with what it     *)
(*  makes over and over kept.                                         *)
(*                                                                    *)
(*  This is the block of HOL Light's define.ml that makes             *)
(*  instantiate_casewise_recursion,                                   *)
(*  pure_prove_recursive_function_exists and                          *)
(*  prove_general_recursive_function_exists, copied word for word,    *)
(*  with two things kept that it makes anew every time:               *)
(*                                                                    *)
(*  - the proformas (HACK_PROFORMA, EACK_PROFORMA), which only        *)
(*    depend on a number of arguments and a theorem.  Of the 105      *)
(*    seconds that the existence theorem of bvi_let$compile_sing      *)
(*    (twelve clauses) took, 96 went into the fifteen proformas       *)
(*    that it asks for 54 times; with them kept it takes 9 seconds,   *)
(*    and a later definition that asks for the same proformas pays    *)
(*    nothing at all.                                                 *)
(*                                                                    *)
(*  - the last eight existence theorems, as the strategies of         *)
(*    define.ml ask for the same one over and over (once for every    *)
(*    form of the clauses and once more for the guess).               *)
(*                                                                    *)
(*  The names of HOL Light are then bound to the functions of this    *)
(*  file, so that everything after it (define.ml) uses them.          *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* The admissibility of a MAP2, which HOL Light does not have.        *)
(*                                                                    *)
(* Two functions that agree on the elements that a MAP2 takes give    *)
(* the same list, so a recursive call under a MAP2 is admissible      *)
(* (clos_known's merge).  HOL Light's MAP2 takes the elements of the  *)
(* second list with HD and TL, so the elements are the ones at a      *)
(* position of the first list, not the members of the lists.          *)
(* ------------------------------------------------------------------ *)

let MAP2_EQ_EL = prove
 (`!(f:A->B->C) g l1 l2.
     (!i. i < LENGTH l1
          ==> f (EL i l1) (EL i l2) = g (EL i l1) (EL i l2))
     ==> MAP2 f l1 l2 = MAP2 g l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP2_DEF] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B->C) h (HD (l2:B list)) = g h (HD l2)`
   (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[EL; HD; LENGTH; LT_0];
    ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
  ASM_REWRITE_TAC[EL; TL; LENGTH; LT_SUC]);;

let ADMISSIBLE_MAP2 = prove
 (`!(<<) p (s:P->S) (h:(A->B)->P->C->D->E)
     (l1:(A->B)->P->C list) (l2:(A->B)->P->D list).
        admissible(<<) p s l1 /\ admissible(<<) p s l2 /\
        admissible (<<) (\f (i,x). p f x /\ i < LENGTH (l1 f x))
                        (\(i,x). s x)
                        (\f (i,x). h f x (EL i (l1 f x))
                                         (EL i (l2 f x)))
   ==> admissible (<<) p s
         (\(f:A->B) (x:P). MAP2 (h f x) (l1 f x) (l2 f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(l1:(A->B)->P->C list) f a = l1 g a /\
    (l2:(A->B)->P->D list) f a = l2 g a`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MAP2_EQ_EL THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`f:A->B`; `g:A->B`; `i:num`; `a:P`]) THEN
  ASM_REWRITE_TAC[]);;

(* the proformas of the admissibility that a later file of the
   library layer adds, by the name of the function that the
   recursive call is under (ml/lib/hol4.ml has the one of an
   OPTION_MAP, whose OPTION_MAP it defines itself) *)

let admissible_extra = ref ([]:(string * thm) list);;

(* the admissibility of a recursive call in the body of a let,
   which HOL Light has no proforma for: without the equation
   that the let gives, the termination goal of a call on what
   the let binds says nothing (bvl_to_bvi's compile_exps
   recurses on the args of let (args,x0) = destLet x2) *)

let ADMISSIBLE_LET = prove
 (`!(<<) p (s:P->S) (b:(A->B)->P->C->D) (e:(A->B)->P->C).
      admissible(<<) p s e /\
      admissible (<<) (\f (y,x). p f x /\ y = e f x)
                      (\(y,x). s x) (\f (y,x). b f x y)
      ==> admissible (<<) p s
            (\(f:A->B) (x:P). LET (b f x) (e f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM; LET_DEF] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:(A->B)->P->C) f a = e g a`
    (fun th -> ASSUME_TAC th THEN SUBST1_TAC th) THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* the admissibility of an existential, which HOL Light has no
   proforma for: a pattern variable of a match that the arm of
   the match does not use stays as one (wordLang's Call binds
   l2 of its handler, and the body of max_var does not look at
   it) *)

let ADMISSIBLE_EXISTS = prove
 (`!(<<) p s:P->A t:(A->B)->C->P->bool.
     admissible(<<) (\f (u,x). p f x) (\(u,x). s x)
                    (\f (u,x). t f u x)
     ==> admissible(<<) p s (\f x. ?u. t f u x)`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN MESON_TAC[]);;

(* with cake_proforma set, a goal that no proforma of the
   dispatch below takes is written to cakeml/tmp/proforma.txt:
   that says which proforma the library layer is missing *)

let cake_proforma = ref false;;

let cake_proforma_note s =
  let ch = open_out_gen [Open_append; Open_creat] 0o644
    "/home/freek/claude/hol-light/cakeml/tmp/proforma.txt" in
  output_string ch (s ^ "\n");
  close_out ch;;

let cake_proforma_log tm =
  cake_proforma_note ("GOAL " ^ string_of_term tm ^ "\n");;

let cake_instantiate_casewise_recursion,
    cake_pure_prove_recursive_function_exists,
    cake_prove_general_recursive_function_exists,
    cake_admiss_tac =

(* ------------------------------------------------------------------ *)
(* Make some basic simplification of conjunction of                 *)
(* welldefinedness clauses.                                         *)
(* ------------------------------------------------------------------ *)

  let SIMPLIFY_WELLDEFINEDNESS_CONV =
    let LSYM =
      GEN_ALL o CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) o
        SPEC_ALL
    and evensimps = prove
     (`((2 * m + 2 = 2 * n + 1) <=> F) /\
       ((2 * m + 1 = 2 * n + 2) <=> F) /\
       ((2 * m = 2 * n + 1) <=> F) /\
       ((2 * m + 1 = 2 * n) <=> F) /\
       ((2 * m = SUC(2 * n)) <=> F) /\
       ((SUC(2 * m) = 2 * n) <=> F)`,
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH; EVEN]) in
    let allsimps = itlist (mk_rewrites false)
     [EQ_ADD_RCANCEL; EQ_ADD_LCANCEL;
      EQ_ADD_RCANCEL_0; EQ_ADD_LCANCEL_0;
      LSYM EQ_ADD_RCANCEL_0; LSYM EQ_ADD_LCANCEL_0;
      EQ_MULT_RCANCEL; EQ_MULT_LCANCEL;
      EQT_INTRO(SPEC_ALL EQ_REFL);
      ADD_EQ_0; LSYM ADD_EQ_0;
      MULT_EQ_0; LSYM MULT_EQ_0;
      MULT_EQ_1; LSYM MULT_EQ_1;
      ARITH_RULE
        `(m + n = 1) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)`;
      ARITH_RULE
        `(1 = m + n) <=> (m = 1) /\ (n = 0) \/ (m = 0) /\ (n = 1)`;
      evensimps; ARITH_EQ] []
    and [simp1; simp2; simp3] = map MATCH_MP (CONJUNCTS
      (TAUT
       `((a <=> F) /\ (b <=> b) ==> ((a ==> b) <=> T)) /\
        ((a <=> a') /\ (a' ==> (b <=> T)) ==> ((a ==> b) <=> T)) /\
        ((a <=> a') /\ (a' ==> (b <=> b')) ==> ((a ==> b) <=> (a' ==>
          b')))`))
    and false_tm = `F` and and_tm = `(/\)`
    and eq_refl = EQT_INTRO(SPEC_ALL EQ_REFL) in
    fun tm ->
      let net = itlist (net_of_thm false) allsimps
        (!basic_rectype_net) in
      let RECTYPE_ARITH_EQ_CONV =
        TOP_SWEEP_CONV(REWRITES_CONV net) THENC
        GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES; OR_CLAUSES] in
      let SIMPLIFY_CASE_DISTINCTNESS_CLAUSE tm =
        let avs,bod = strip_forall tm in
        let ant,cons = dest_imp bod in
        let ath = RECTYPE_ARITH_EQ_CONV ant in
        let atm = rand(concl ath) in
        let bth = CONJ ath
          (if atm = false_tm then REFL cons
                    else DISCH atm
                          (PURE_REWRITE_CONV[eq_refl; ASSUME atm]
                            cons)) in
        let cth = try simp1 bth with Failure _ -> try simp2 bth
                  with Failure _ -> simp3 bth in
        itlist MK_FORALL avs cth in
      (DEPTH_BINOP_CONV and_tm SIMPLIFY_CASE_DISTINCTNESS_CLAUSE THENC
       GEN_REWRITE_CONV DEPTH_CONV [FORALL_SIMP; AND_CLAUSES]) tm in

(* ------------------------------------------------------------------ *)
(* Simplify an existential question about a pattern. *)
(* ------------------------------------------------------------------ *)

  let EXISTS_PAT_CONV =
    let pth = prove
     (`((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ z y)) <=> s = t) /\
       ((?y. _GUARDED_PATTERN (GEQ s t) g (GEQ z y)) <=> g /\ s = t)`,
      REWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; GEQ_DEF] THEN
      MESON_TAC[]) in
    let basecnv = GEN_REWRITE_CONV I [pth]
    and pushcnv = GEN_REWRITE_CONV I [SWAP_EXISTS_THM] in
    let rec EXISTS_PAT_CONV tm =
     ((pushcnv THENC BINDER_CONV EXISTS_PAT_CONV) ORELSEC
      basecnv) tm in
    fun tm -> if is_exists tm then EXISTS_PAT_CONV tm
              else failwith "EXISTS_PAT_CONV" in

(* ------------------------------------------------------------------ *)
(* Hack a proforma to introduce new pairing or pattern variables. *)
(* ------------------------------------------------------------------ *)

  let HACK_PROFORMA,EACK_PROFORMA =
    let elemma0 = prove
     (`((!z. GEQ (f z) (g z)) <=> (!x y. GEQ (f(x,y)) (g(x,y)))) /\
       ((\p. P p) = (\(x,y). P(x,y)))`,
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM])
    and elemma1 = prove
     (`(!P. (!t:A->B->C#D->E. P t) <=>
            (!t. P (\a b (c,d). t a b d c))) /\
       (!P. (!t:B->C#D->E. P t) <=> (!t. P (\b (c,d). t b d c))) /\
       (!P. (!t:C#D->E. P t) <=> (!t. P (\(c,d). t d c)))`,
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC
         `\a b d c. (t:A->B->C#D->E) a b (c,d)`);
        FIRST_X_ASSUM(MP_TAC o SPEC `\b d c. (t:B->C#D->E) b (c,d)`);
        FIRST_X_ASSUM(MP_TAC o SPEC `\d c. (t:C#D->E) (c,d)`)] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]) in
    let HACK_PROFORMA n th =
      if n <= 1 then th else
      let mkname i = "_P"^string_of_int i in
      let ty = end_itlist (fun s t -> mk_type("prod",[s;t]))
                          (map (mk_vartype o mkname) (1--n)) in
      let conv i =
        let name = "x"^string_of_int i in
        let cnv = ALPHA_CONV (mk_var(name,mk_vartype(mkname i))) in
        fun tm -> if is_abs tm && name_of(bndvar tm) <> name
                  then cnv tm else failwith "conv" in
      let convs = FIRST_CONV (map conv (1--n)) in
      let th1 = INST_TYPE [ty,`:P`] th in
      let th2 = REWRITE_RULE[FORALL_PAIR_THM] th1 in
      let th3 = REWRITE_RULE[elemma0; elemma1] th2 in
      CONV_RULE(REDEPTH_CONV convs) th3
    and EACK_PROFORMA n th =
      if n <= 1 then th else
      let mkname i = "_Q"^string_of_int i in
      let ty = end_itlist (fun s t -> mk_type("prod",[s;t]))
                          (map (mk_vartype o mkname) (1--n)) in
      let conv i =
        let name = "t"^string_of_int i in
        let cnv = ALPHA_CONV (mk_var(name,mk_vartype(mkname i))) in
        fun tm -> if is_abs tm && name_of(bndvar tm) <> name
                  then cnv tm else failwith "conv" in
      let convs = FIRST_CONV (map conv (1--n)) in
      let th1 = INST_TYPE [ty,`:Q`] th in
      let th2 = REWRITE_RULE[EXISTS_PAIR_THM] th1 in
      let th3 = REWRITE_RULE[elemma1] th2 in
      let th4 = REWRITE_RULE[FORALL_PAIR_THM] th3 in
      CONV_RULE(REDEPTH_CONV convs) th4 in
    HACK_PROFORMA,EACK_PROFORMA in

(* ------------------------------------------------------------------ *)
(* Keep the proformas: the one of a number of arguments and a theorem *)
(* is always the same, and making it is slow. *)
(* ------------------------------------------------------------------ *)

  let HACK_PROFORMA,EACK_PROFORMA =
    let hack_cache = ref [] and eack_cache = ref [] in
    let cached c f n th =
      let key = n,concl th in
      try assoc key (!c)
      with Failure _ -> let r = f n th in c := (key,r) :: !c; r in
    cached hack_cache HACK_PROFORMA,cached eack_cache EACK_PROFORMA in

(* ------------------------------------------------------------------ *)
(* Hack and apply. *)
(* ------------------------------------------------------------------ *)

  let APPLY_PROFORMA_TAC th (asl,w as gl) =
    let vs = fst(dest_gabs(body(rand w))) in
    let n = 1 + length(fst(splitlist dest_pair vs)) in
    (MATCH_MP_TAC(HACK_PROFORMA n th) THEN BETA_TAC) gl in

  let is_pattern p n tm =
    try let f,args = strip_comb(snd(strip_exists (body(body tm)))) in
        is_const f && name_of f = p && length args = n
    with Failure _ -> false in

  let SIMPLIFY_MATCH_WELLDEFINED_TAC =
    let pth0 = MESON[]
     `(a /\ x = k ==> x = y ==> d) ==> (a /\ x = k /\ y = k ==> d)`
    and pth1 = MESON[]
     `(a /\ b /\ c /\ x = k ==> x = y ==> d)
      ==> (a /\ x = k /\ b /\ y = k /\ c ==> d)` in
    REPEAT GEN_TAC THEN
    (MATCH_MP_TAC pth1 ORELSE MATCH_MP_TAC pth0) THEN
    CONV_TAC(RAND_CONV SIMPLIFY_WELLDEFINEDNESS_CONV) THEN
    PURE_REWRITE_TAC
      [AND_CLAUSES; IMP_CLAUSES; OR_CLAUSES; EQ_CLAUSES; NOT_CLAUSES] in

  let rec headonly f tm =
    match tm with
      Comb(s,t) -> headonly f s && headonly f t && not(t = f)
    | Abs(x,t) -> headonly f t
    | _ -> true in

  let MAIN_ADMISS_TAC0 (asl,w as gl) =
    let had,args = strip_comb w in
    if not(is_const had) then failwith "ADMISS_TAC" else
    let f,fbod = dest_abs(last args) in
    let xtup,bod = dest_gabs fbod in
    let hop,args = strip_comb bod in
    (if !cake_proforma then
       cake_proforma_note (name_of had ^ " / " ^ name_of hop));
    match (name_of had,name_of hop) with
      "superadmissible","COND"
          -> APPLY_PROFORMA_TAC SUPERADMISSIBLE_COND gl
    | "superadmissible","_MATCH" when
          name_of(repeat rator (last args)) = "_SEQPATTERN"
          -> (APPLY_PROFORMA_TAC SUPERADMISSIBLE_MATCH_SEQPATTERN THEN
              CONV_TAC(ONCE_DEPTH_CONV EXISTS_PAT_CONV)) gl
    | "superadmissible","_MATCH" when
         is_pattern "_UNGUARDED_PATTERN" 2 (last args)
          -> let n = length(fst(strip_exists(body(body(last args))))) in
             let th = EACK_PROFORMA n
               SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN in
             (APPLY_PROFORMA_TAC th THEN CONJ_TAC THENL
               [SIMPLIFY_MATCH_WELLDEFINED_TAC; ALL_TAC]) gl
    | "superadmissible","_MATCH" when
         is_pattern "_GUARDED_PATTERN" 3 (last args)
          -> let n = length(fst(strip_exists(body(body(last args))))) in
             let th = EACK_PROFORMA n
               SUPERADMISSIBLE_MATCH_GUARDED_PATTERN in
             (APPLY_PROFORMA_TAC th THEN CONJ_TAC THENL
               [SIMPLIFY_MATCH_WELLDEFINED_TAC; ALL_TAC]) gl
    | "superadmissible",_ when is_comb bod && rator bod = f
          -> APPLY_PROFORMA_TAC SUPERADMISSIBLE_TAIL gl
    | "admissible","sum"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_SUM gl
    | "admissible","nsum"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_NSUM gl
    | "admissible","MAP"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_MAP gl
    (* a proforma that a later file of the library layer added *)
    | "admissible",c when can (assoc c) (!admissible_extra)
          -> APPLY_PROFORMA_TAC (assoc c (!admissible_extra)) gl
    (* the proforma of a let, which HOL Light does not have *)
    | "admissible","LET"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_LET gl
    (* the proforma of a MAP2, which HOL Light does not have *)
    | "admissible","MAP2"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_MAP2 gl
    (* the proforma of a conditional, which HOL Light proves
       but only uses in tail position *)
    | "admissible","COND"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_COND gl
    (* the proforma of an existential.  The bound variable is
       renamed first: it can have the name of a variable of the
       tuple (the handler of wordLang's Call binds l1 and l2,
       which the return of the Call binds too), and the match
       of the proforma would confuse the two *)
    | "admissible","?"
          -> let avoid = variables w in
             let FRESH_EXISTS_CONV tm =
               let v,_ = dest_exists tm in
               let v' = variant avoid v in
               if v' = v then failwith "FRESH_EXISTS_CONV"
               else GEN_ALPHA_CONV v' tm in
             (TRY(CONV_TAC(ONCE_DEPTH_CONV FRESH_EXISTS_CONV)) THEN
              APPLY_PROFORMA_TAC ADMISSIBLE_EXISTS) gl
    | "admissible","_MATCH" when
          name_of(repeat rator (last args)) = "_SEQPATTERN"
          -> (APPLY_PROFORMA_TAC ADMISSIBLE_MATCH_SEQPATTERN THEN
              CONV_TAC(ONCE_DEPTH_CONV EXISTS_PAT_CONV)) gl
    | "admissible","_MATCH"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_MATCH gl
    | "admissible","_UNGUARDED_PATTERN"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_UNGUARDED_PATTERN gl
    | "admissible","_GUARDED_PATTERN"
          -> APPLY_PROFORMA_TAC ADMISSIBLE_GUARDED_PATTERN gl
    | "admissible",_ when is_abs bod
          -> APPLY_PROFORMA_TAC ADMISSIBLE_LAMBDA gl
    | "admissible",_ when is_comb bod && rator bod = f
          -> if free_in f (rand bod) then
               APPLY_PROFORMA_TAC ADMISSIBLE_NEST gl
             else
               APPLY_PROFORMA_TAC ADMISSIBLE_BASE gl
    | "admissible",_ when is_comb bod && headonly f bod
          -> APPLY_PROFORMA_TAC ADMISSIBLE_COMB gl
    (* the function is only in the argument of the combination *)
    | "admissible",_ when is_comb bod && not(rand bod = f) &&
                          not(free_in f (rator bod))
          -> APPLY_PROFORMA_TAC ADMISSIBLE_RAND gl
    (* the function is an argument of a combination deeper in,
       which the proforma of that combination (a MAP) takes *)
    | "admissible",_ when is_comb bod && not(rand bod = f)
          -> APPLY_PROFORMA_TAC ADMISSIBLE_COMB gl
    | _ -> ((if !cake_proforma then cake_proforma_log w);
            failwith "MAIN_ADMISS_TAC") in

  let MAIN_ADMISS_TAC (asl,w as gl) =
    try MAIN_ADMISS_TAC0 gl
    with Failure e ->
      ((if !cake_proforma then
          (cake_proforma_note ("  FAILED " ^ e);
           cake_proforma_log w));
       failwith e) in

  let ADMISS_TAC =
    CONJ_TAC ORELSE
    MATCH_ACCEPT_TAC ADMISSIBLE_CONST ORELSE
    MATCH_ACCEPT_TAC SUPERADMISSIBLE_CONST ORELSE
    MAIN_ADMISS_TAC ORELSE
    MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE in

(* ------------------------------------------------------------------ *)
(* Instantiate the casewise recursion theorem for existential claim. *)
(* Also make a first attempt to simplify the distinctness clause.   *)
(* This may yield a theorem with just the wellfoundedness "?(<<)"   *)
(* assumption, or it may be that and an additional distinctness     *)
(* one.                                                             *)
(* ------------------------------------------------------------------ *)

  let instantiate_casewise_recursion =
    let EXPAND_PAIRED_ALL_CONV =
      let pth0,pth1 = (CONJ_PAIR o prove)
       (`(ALL (\(s,t). P s t) [a,b] <=> P a b) /\
         (ALL (\(s,t). P s t) (CONS (a,b) l) <=>
          P a b /\ ALL (\(s,t). P s t) l)`,
        REWRITE_TAC[ALL]) in
      let conv0 = REWR_CONV pth0 and conv1 = REWR_CONV pth1 in
      let rec conv tm =
        try conv0 tm with Failure _ ->
        let th = conv1 tm in CONV_RULE (funpow 2 RAND_CONV conv) th in
      conv
    and LAMBDA_PAIR_CONV =
      let rewr1 =  GEN_REWRITE_RULE I [GSYM FORALL_PAIR_THM]
      and rewr2 = GEN_REWRITE_CONV I [FUN_EQ_THM] in
      fun parms tm ->
        let parm = end_itlist (curry mk_pair) parms in
        let x,bod = dest_abs tm in
        let tm' = mk_gabs(parm,vsubst[parm,x] bod) in
        let th1 = BETA_CONV(mk_comb(tm,parm))
        and th2 = GEN_BETA_CONV (mk_comb(tm',parm)) in
        let th3 = TRANS th1 (SYM th2) in
        let th4 = itlist (fun v th -> rewr1 (GEN v th))
                         (butlast parms) (GEN (last parms) th3) in
        EQ_MP (SYM(rewr2(mk_eq(tm,tm')))) th4
    and FORALL_PAIR_CONV =
      let rule = GEN_REWRITE_RULE RAND_CONV [GSYM FORALL_PAIR_THM] in
      let rec depair l t =
        match l with
          [v] -> REFL t
        | v::vs -> rule(BINDER_CONV (depair vs) t) in
      fun parm parms ->
        let p = mk_var("P",mk_fun_ty (type_of parm) bool_ty) in
        let tm = list_mk_forall(parms,mk_comb(p,parm)) in
        GEN p (SYM(depair parms tm)) in
    let ELIM_LISTOPS_CONV =
      PURE_REWRITE_CONV[PAIRWISE; ALL; GSYM CONJ_ASSOC; AND_CLAUSES]
        THENC
      TOP_DEPTH_CONV GEN_BETA_CONV in
    let tuple_function_existence tm =
      let f,def = dest_exists tm in
      let domtys0,ranty0 = splitlist dest_fun_ty (type_of f) in
      let nargs =
        itlist
         (max o length o snd o strip_comb o lhs o snd o strip_forall)
         (conjuncts(snd(strip_forall def))) 0 in
      let domtys,midtys = chop_list nargs domtys0 in
      let ranty = itlist mk_fun_ty midtys ranty0 in
      if length domtys <= 1 then ASSUME tm else
      let dty = end_itlist (fun ty1 ty2 -> mk_type("prod",[ty1;ty2]))
        domtys in
      let f' = variant (frees tm)
                       (mk_var(fst(dest_var f),mk_fun_ty dty ranty)) in
      let gvs = map genvar domtys in
      let f'' = list_mk_abs(gvs,mk_comb(f',end_itlist (curry mk_pair)
        gvs)) in
      let def' = subst [f'',f] def in
      let th1 = EXISTS (tm,f'') (ASSUME def')
      and bth = BETAS_CONV (list_mk_comb(f'',gvs)) in
      let th2 = GEN_REWRITE_CONV TOP_DEPTH_CONV [bth] (hd(hyp th1)) in
      SIMPLE_CHOOSE f' (PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th2)))
        th1) in
    let pinstantiate_casewise_recursion def =
      try PART_MATCH I EXISTS_REFL def with Failure _ ->
      let f,bod = dest_exists def in
      let cjs = conjuncts bod in
      let eqs = map (snd o strip_forall) cjs in
      let lefts,rights = unzip(map dest_eq eqs) in
      let arglists = map (snd o strip_comb) lefts in
      let parms0 = freesl(unions arglists) in
      let parms = if parms0 <> [] then parms0 else [genvar aty] in
      let parm = end_itlist (curry mk_pair) parms in
      let ss = map (fun a -> mk_gabs(parm,end_itlist (curry mk_pair) a))
                   arglists
      and ts = map (fun a -> mk_abs(f,mk_gabs(parm,a))) rights in
      let clauses = mk_flist(map2 (curry mk_pair) ss ts) in
      let pth = ISPEC clauses RECURSION_SUPERADMISSIBLE in
      let FIDDLE_CONV =
        (LAND_CONV o LAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
         GABS_CONV o RATOR_CONV o LAND_CONV o ABS_CONV) in
      let th0 = UNDISCH(CONV_RULE(FIDDLE_CONV(LAMBDA_PAIR_CONV parms))
        pth) in
      let th1 = EQ_MP (GEN_ALPHA_CONV f (concl th0)) th0 in
      let rewr_forall_th = REWR_CONV(FORALL_PAIR_CONV parm parms) in
      let th2 = CONV_RULE (BINDER_CONV
                    (LAND_CONV(GABS_CONV rewr_forall_th) THENC
                     EXPAND_PAIRED_ALL_CONV)) th1 in
      let f2,bod2 = dest_exists(concl th2) in
      let ths3 = map
       (CONV_RULE (COMB2_CONV (funpow 2 RAND_CONV GEN_BETA_CONV)
                  (RATOR_CONV BETA_CONV THENC GEN_BETA_CONV)) o
                    SPEC_ALL)
       (CONJUNCTS(ASSUME bod2)) in
      let ths4 = map2
       (fun th t -> let avs,tbod = strip_forall t in
                    itlist GEN avs (PART_MATCH I th tbod)) ths3 cjs in
      let th5 = SIMPLE_EXISTS f (end_itlist CONJ ths4) in
      let th6 = PROVE_HYP th2 (SIMPLE_CHOOSE f th5) in
      let th7 =
       (RAND_CONV(COMB2_CONV
            (RAND_CONV (LAND_CONV (GABS_CONV(BINDER_CONV
                     (BINDER_CONV(rewr_forall_th) THENC
                       rewr_forall_th)))))
            (LAND_CONV (funpow 2 GABS_CONV(BINDER_CONV
                     (BINDER_CONV(rewr_forall_th) THENC
                      rewr_forall_th))))) THENC
        ELIM_LISTOPS_CONV) (hd(hyp th6)) in
      let th8 = PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th7))) th6 in
      let wfasm,cdasm = dest_conj(hd(hyp th8)) in
      let th9 = PROVE_HYP (CONJ (ASSUME wfasm) (ASSUME cdasm)) th8 in
      let th10 = SIMPLIFY_WELLDEFINEDNESS_CONV cdasm in
      let th11 = PROVE_HYP (UNDISCH(snd(EQ_IMP_RULE th10))) th9 in
      PROVE_HYP TRUTH th11 in
    fun etm ->
      let eth = tuple_function_existence etm in
      let dtm = hd(hyp eth) in
      let dth = pinstantiate_casewise_recursion dtm in
      PROVE_HYP dth eth in

(* ------------------------------------------------------------------ *)
(* Justify existence assertion and try to simplify/remove           *)
(* side-conditions.                                                 *)
(* ------------------------------------------------------------------ *)

  let pure_prove_recursive_function_exists =
    let break_down_admissibility th1 =
      if hyp th1 = [] then th1 else
      let def = concl th1 in
      let f,bod = dest_exists def in
      let cjs = conjuncts bod in
      let eqs = map (snd o strip_forall) cjs in
      let lefts,rights = unzip(map dest_eq eqs) in
      let arglists = map (snd o strip_comb) lefts in
      let parms0 = freesl(unions arglists) in
      let parms = if parms0 <> [] then parms0 else [genvar aty] in
      let wfasm = find is_exists (hyp th1) in
      let ord,bod = dest_exists wfasm in
      let SIMP_ADMISS_TAC =
        REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
        REPEAT ADMISS_TAC THEN
        TRY(W(fun (asl,w) -> let v = fst(dest_forall w) in
                X_GEN_TAC v THEN
                MAP_EVERY
                  (fun v -> TRY(GEN_REWRITE_TAC I [FORALL_PAIR_THM])
                    THEN
                            X_GEN_TAC v)
                  parms THEN
                CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
                MAP_EVERY (fun v -> SPEC_TAC(v,v)) (rev parms @ [v])))
                  THEN
        PURE_REWRITE_TAC[FORALL_SIMP] THEN
        W(fun (asl,w) -> MAP_EVERY (fun t -> SPEC_TAC(t,t))
                                   (subtract (frees w) [ord])) THEN
        W(fun (asl,w) -> ACCEPT_TAC(ASSUME w)) in
      let th2 = TAC_PROOF(([],bod),SIMP_ADMISS_TAC) in
      let th3 = SIMPLE_EXISTS ord th2 in
      let allasms = hyp th3 and wfasm = lhand(concl th2) in
      let th4 = ASSUME(list_mk_conj(wfasm::subtract allasms [wfasm])) in
      let th5 = SIMPLE_CHOOSE ord (itlist PROVE_HYP (CONJUNCTS th4)
        th3) in
      PROVE_HYP th5 th1 in
    fun dtm ->
      let th =  break_down_admissibility(instantiate_casewise_recursion
        dtm) in
      if concl th = dtm then th
      else failwith "prove_general_recursive_function_exists: sanity" in

(* ------------------------------------------------------------------ *)
(* Keep the last existence theorems: the strategies of the port     *)
(* ask for the same one over and over (every form of the clauses,   *)
(* every measure).                                                  *)
(* ------------------------------------------------------------------ *)

  let pure_prove_recursive_function_exists =
    let cache = ref ([]:(term * thm) list) in
    fun etm ->
      try assoc etm (!cache)
      with Failure _ ->
        let th = pure_prove_recursive_function_exists etm in
        cache := (etm,th) ::
                 (if length (!cache) > 7
                  then fst(chop_list 7 (!cache)) else !cache);
        th in

(* ------------------------------------------------------------------ *)
(* Same, but attempt to prove the wellfoundedness hyp by good       *)
(* guesses.                                                         *)
(* ------------------------------------------------------------------ *)

  let prove_general_recursive_function_exists =
    let prove_depth_measure_exists =
      let num_ty = `:num` in
      fun tyname ->
        let _,_,sth = assoc tyname (!inductive_type_store) in
        let ty,zty = dest_fun_ty
         (type_of(fst(dest_exists(snd(strip_forall(concl sth)))))) in
        let rth = INST_TYPE [num_ty,zty] sth in
        let avs,bod = strip_forall(concl rth) in
        let ev,cbod = dest_exists bod in
        let process_clause k t =
          let avs,eq = strip_forall t in
          let l,r = dest_eq eq in
          let fn,cargs = dest_comb l in
          let con,args = strip_comb cargs in
          let bargs = filter (fun t -> type_of t = ty) args in
          let r' = list_mk_binop `(+):num->num->num`
                    (mk_small_numeral k :: map (curry mk_comb fn)
                      bargs) in
          list_mk_forall(avs,mk_eq(l,r')) in
        let cjs = conjuncts cbod in
        let def = map2 process_clause (1--length cjs) cjs in
        prove_recursive_functions_exist sth (list_mk_conj def) in
    let INDUCTIVE_MEASURE_THEN tac (asl,w) =
      let ev,bod = dest_exists w in
      let ty = fst(dest_type(fst(dest_fun_ty(type_of ev)))) in
      let th = prove_depth_measure_exists ty in
      let ev',bod' = dest_exists(concl th) in
      let th' = INST_TYPE(type_match (type_of ev') (type_of ev) [])
        th in
      (MP_TAC th' THEN MATCH_MP_TAC MONO_EXISTS THEN
       GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN tac)
         (asl,w) in
    let CONSTANT_MEASURE_THEN =
      let one_tm = `1` in
      fun tac (asl,w) ->
        let ev,bod = dest_exists w in
        let ty = fst(dest_fun_ty(type_of ev)) in
        (EXISTS_TAC(mk_abs(genvar ty,one_tm)) THEN tac) (asl,w) in
    let GUESS_MEASURE_THEN tac =
      (EXISTS_TAC `\n. n + 1` THEN tac) ORELSE
      (INDUCTIVE_MEASURE_THEN tac) ORELSE
      CONSTANT_MEASURE_THEN tac in
    let pth_lexleft = prove
     (`(?r. WF(r) /\
            ?s. WF(s) /\
                P(\(x1,y1) (x2,y2). r x1 x2 \/ (x1 = x2) /\ s y1 y2))
       ==> ?t:A#B->A#B->bool. WF(t) /\ P t`,
      REPEAT STRIP_TAC THEN EXISTS_TAC
       `\(x1:A,y1:B) (x2:A,y2:B). r x1 x2 \/ (x1 = x2) /\ s y1 y2` THEN
      ASM_SIMP_TAC[WF_LEX]) in
    let pth_lexright = prove
     (`(?r. WF(r) /\
            ?s. WF(s) /\
                P(\(x1,y1) (x2,y2). r y1 y2 \/ (y1 = y2) /\ s x1 x2))
       ==> ?t:A#B->A#B->bool. WF(t) /\ P t`,
      REPEAT STRIP_TAC THEN
      EXISTS_TAC `\u:A#B v:A#B.
                    (\(x1:B,y1:A) (x2:B,y2:A). r x1 x2 \/ (x1 = x2) /\ s
                      y1 y2)
                     ((\(a,b). b,a) u) ((\(a,b). b,a) v)` THEN
      ASM_SIMP_TAC[WF_LEX; ETA_AX;
       ISPECL [`R:A#B->A#B->bool`; `\(b:B,a:A). a,b`] WF_MEASURE_GEN]
         THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN
                              MATCH_MP_TAC EQ_IMP THEN
                              AP_TERM_TAC) THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]) in
    let pth_measure = prove
     (`(?m:A->num. P(MEASURE m)) ==> ?r:A->A->bool. WF(r) /\ P r`,
      MESON_TAC[WF_MEASURE]) in
    let rec GUESS_WF_THEN tac (asl,w) =
     ((MATCH_MP_TAC pth_lexleft THEN GUESS_WF_THEN (GUESS_WF_THEN tac))
       ORELSE
      (MATCH_MP_TAC pth_lexright THEN GUESS_WF_THEN (GUESS_WF_THEN tac))
        ORELSE
      (MATCH_MP_TAC pth_measure THEN
       REWRITE_TAC[MEASURE; MEASURE_LE] THEN
       REWRITE_TAC[FORALL_PAIR_THM] THEN
       GUESS_MEASURE_THEN tac)) (asl,w) in
    let PRE_GUESS_TAC =
      CONV_TAC(BINDER_CONV(DEPTH_BINOP_CONV `(/\)`
       (TRY_CONV SIMPLIFY_WELLDEFINEDNESS_CONV THENC
        TRY_CONV FORALL_UNWIND_CONV))) in
    let GUESS_ORDERING_TAC =
      let false_tm = `\x:A y:A. F` in
      W(fun (asl,w) ->
            let ty = fst(dest_fun_ty(type_of(fst(dest_exists w)))) in
            EXISTS_TAC(inst [ty,aty] false_tm) THEN
            REWRITE_TAC[WF_FALSE] THEN NO_TAC) ORELSE
      GUESS_WF_THEN
       (REWRITE_TAC[FORALL_PAIR_THM] THEN ARITH_TAC) in
    fun etm ->
      let th = pure_prove_recursive_function_exists etm in
      try let wtm = find is_exists (hyp th) in
          let wth = prove(wtm,PRE_GUESS_TAC THEN GUESS_ORDERING_TAC) in
          PROVE_HYP wth th
      with Failure _ -> th in

  instantiate_casewise_recursion,
  pure_prove_recursive_function_exists,
  prove_general_recursive_function_exists,
  ADMISS_TAC;;

(* the names of HOL Light are the functions of this file *)

let instantiate_casewise_recursion =
  cake_instantiate_casewise_recursion;;

let pure_prove_recursive_function_exists =
  cake_pure_prove_recursive_function_exists;;

let prove_general_recursive_function_exists =
  cake_prove_general_recursive_function_exists;;
