(* ======================================================== *)
(*  bvi_let: ported from HOL4's
    compiler/backend/bvi_letScript.sml
    A definition theory, with 6 definitions and 5 theorems.  Needed
    by bvi_letProof.ml, bvl_to_bvi.ml and bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*

   This is a BVI transformation that propagates variable lookups that
   are immediately assigned to a new variable in Let bindings. This
   optimisation is to run immediately when entering BVI.

   This optimisation removes each Var in a Let, i.e.

     Let [ ... ; Var ... ; ... ] ...

   and replaces them with constants

     Let [ ... ; Op (IntOp (Const _)) [] ; ... ] ....

   and then replaces all occurrences of the bound var in the body with
   a lookup to the original variable.

   There is a similar optimisation in BVL (bvl_const). This version
   (which is slightly simpler) is run again because the BVL-to-BVI
   compiler can introduce large Let expressions consisting of only
   variable lookups.

   This BVI version differs from the BVL version (bvl_const) by having
   the ability to move expressions into tail-position, e.g.

     let
       val x = foo ...
       val y = bar x
     in y end

   becomes:

     let
       val x = foo ...
     in bar x end

   This is important because pat-to-clos translates Seq p1 p2 into
   Let [compile p1; compile p2] (Var 1).

*)

needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvi_let"
  ["bvi"];;

let bvi_let_extract_def = new_definition
  `bvi_let_extract x1 ys =
        match x1 with
          ((Var n):bvi_exp) -> n + LENGTH ys + 1
        | _1 -> 0`;;
hol4_overload "extract" "bvi_let_extract";;

let extract_list_def,extract_list_ind = define_rec
  [`bvi_let_extract_list [] = []`;
   `bvi_let_extract_list (x :: xs) = extract x xs ::
  bvi_let_extract_list xs`];;
hol4_overload "extract_list" "bvi_let_extract_list";;

let delete_var_def = new_definition
  `bvi_let_delete_var x =
        match x with
          ((Var n):bvi_exp) -> Op (closLang_IntOp (closLang_Const
            (&0))) []
        | x -> x`;;
hol4_overload "delete_var" "bvi_let_delete_var";;

let exp2_size_APPEND = prove
 (`!xs ys. bvi_exp_size1 (xs ++ ys) = bvi_exp_size1 xs + bvi_exp_size1
  ys`,
  (* bvi_exp_size1 is HOL4's exp2_size, which the size prelude
     states as a list_size (size_thms "bvi_exp"), so this is
     list_size_APPEND under another name *)
  (let sz = size_thms "bvi_exp" in
   REWRITE_TAC sz THEN
   MATCH_ACCEPT_TAC (ISPEC `bvi_exp_size` list_size_APPEND)));;

(* the size facts that the termination of the two definitions of
   this file needs, which ml/lib/define.ml takes from here, and the
   budget that their recursion asks for: eight seconds is what a
   definition of the port is given before it is assumed instead,
   and these two take about twenty each *)

let bvi_let_term_facts = !cake_term_facts;;
let bvi_let_budget = !cake_cheat_budget;;
cake_term_facts := list_size_BUTLAST :: list_size_LAST ::
                   (!cake_term_facts);;
cake_cheat_budget := 300;;

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_letScript.sml:110-116: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let bvi_let_compile_def,bvi_let_compile_ind = define_wf_cheat
  `MEASURE (list_size bvi_exp_size o SND o SND)`
  [`bvi_let_compile env d [] = []`;
   `bvi_let_compile env d (x :: y :: xs) = bvi_let_compile env d [x]
  ++ bvi_let_compile env d (y :: xs)`;
   `bvi_let_compile env d [(Var v):bvi_exp] =
         (match (\l n. oEL n l) env v with SOME n -> [Var (v +
           n)] | _2 -> [Var (v + d)])`;
   `bvi_let_compile env d [(If x1 x2 x3:bvi_exp)] =
         [If (HD (bvi_let_compile env d [x1]))
             (HD (bvi_let_compile env d [x2]))
             (HD (bvi_let_compile env d [x3]))]`;
   `bvi_let_compile env d [(Let xs x2:bvi_exp)] =
         (let l = LENGTH xs in
           if l = 0 then bvi_let_compile env d [x2] else
             let k = l - 1 in
               if x2 = Var k then
                 // moves the last exp into tail-position if the body is a Var
                 let ys = bvi_let_compile env d (BUTLAST xs) in
                   [Let ys (HD (bvi_let_compile (MAP ((+) k) env) (d
                     + k) [LAST xs]))] else
                 let ys = bvi_let_compile env d xs in
                   [Let (MAP bvi_let_delete_var ys)
                     (HD (bvi_let_compile (bvi_let_extract_list
                       ys ++ env) d [x2]))])`;
   `bvi_let_compile env d [(Raise x1:bvi_exp)] =
         [Raise (HD (bvi_let_compile env d [x1]))]`;
   `bvi_let_compile env d [(Op op xs:bvi_exp)] = [Op op
  (bvi_let_compile env d xs)]`;
   `bvi_let_compile env d [(Tick x:bvi_exp)] = [Tick (HD
  (bvi_let_compile env d [x]))]`;
   `bvi_let_compile env d [(Force loc v:bvi_exp)] =
         (match (\l n. oEL n l) env v with SOME n -> [Force loc
           (v + n)] | _5 -> [Force loc (v + d)])`;
   `bvi_let_compile env d [(Call t dest xs h:bvi_exp)] =
         [Call t dest (bvi_let_compile env d xs)
             (match h with NONE -> NONE | SOME e -> SOME (HD
               (bvi_let_compile (0 :: env) d [e])))]`;
   (* Return/LetCall are pass-through (only nested Lets are optimised). TODO(multiret):
      no optimisation specific to them yet -- e.g. the Let tail-position move could
      extend to `Let xs (Return (GENLIST Var n))`. *)
   `bvi_let_compile env d [(bvi_Return xs:bvi_exp)] = [bvi_Return
  (bvi_let_compile env d xs)]`;
   `bvi_let_compile env d [bvi_LetCall rets t dest xs y] =
         [bvi_LetCall rets t dest (bvi_let_compile env d xs)
            (HD (bvi_let_compile (REPLICATE rets 0 ++ env) d
              [y]))]`];;
hol4_overload "compile" "bvi_let_compile";;

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_letScript.sml:158-168: the tactic that proves the
   termination *)
let bvi_let_compile_sing_def,bvi_let_compile_sing_ind =
  define_mutual_shaped_wf_tac
  "maplist>measure"
  `MEASURE (\x. match x with INL (_10,_11,e) -> bvi_exp_size e | INR
  (_12,_13,es) -> list_size bvi_exp_size es)`
  TERM_TAC
  [`bvi_let_compile_sing env d ((Var v):bvi_exp) =
         (match (\l n. oEL n l) env v with SOME n -> Var (v + n)
           | _6 -> Var (v + d))`;
   `bvi_let_compile_sing env d (If x1 x2 x3:bvi_exp) =
         (If (bvi_let_compile_sing env d x1)
             (bvi_let_compile_sing env d x2)
             (bvi_let_compile_sing env d x3))`;
   `bvi_let_compile_sing env d (Let xs x2:bvi_exp) =
         (let l = LENGTH xs in
           if l = 0 then bvi_let_compile_sing env d x2 else
             let k = l - 1 in
               if x2 = Var k then
                 // moves the last exp into tail-position if the body is a Var
                 let ys = bvi_let_compile_list env d (BUTLAST xs) in
                   (Let ys ((bvi_let_compile_sing (MAP ((+) k) env)
                     (d + k) (LAST xs)))) else
                 let ys = bvi_let_compile_list env d xs in
                   (Let (MAP bvi_let_delete_var ys)
                     ((bvi_let_compile_sing (bvi_let_extract_list
                       ys ++ env) d x2))))`;
   `bvi_let_compile_sing env d (Raise x1:bvi_exp) =
         (Raise ((bvi_let_compile_sing env d x1)))`;
   `bvi_let_compile_sing env d (Op op xs:bvi_exp) = (Op op
  (bvi_let_compile_list env d xs))`;
   `bvi_let_compile_sing env d (Tick x:bvi_exp) = (Tick
  (bvi_let_compile_sing env d x))`;
   `bvi_let_compile_sing env d (Force loc v:bvi_exp) =
         (match (\l n. oEL n l) env v with SOME n -> Force loc (v
           + n) | _9 -> Force loc (v + d))`;
   `bvi_let_compile_sing env d (Call t dest xs h:bvi_exp) =
         (Call t dest (bvi_let_compile_list env d xs)
             (match h with NONE -> NONE | SOME e -> SOME
               ((bvi_let_compile_sing (0 :: env) d e))))`;
   `bvi_let_compile_sing env d (bvi_Return xs:bvi_exp) = bvi_Return
  (bvi_let_compile_list env d xs)`;
   `bvi_let_compile_sing env d (bvi_LetCall rets t dest xs y) =
         bvi_LetCall rets t dest (bvi_let_compile_list env d xs)
            (bvi_let_compile_sing (REPLICATE rets 0 ++ env) d y)`;
   `bvi_let_compile_list env d [] = []`;
   `bvi_let_compile_list env d (x :: xs) =
        bvi_let_compile_sing env d x :: bvi_let_compile_list
          env d xs`];;
hol4_overload "compile_list" "bvi_let_compile_list";;
hol4_overload "compile_sing" "bvi_let_compile_sing";;

cake_term_facts := bvi_let_term_facts;;
cake_cheat_budget := bvi_let_budget;;

let compile_sing = prove
 (`(!n d e. bvi_let_compile n d [e] = [bvi_let_compile_sing n d e]) /\
   (!n d e. bvi_let_compile_list n d e = bvi_let_compile n d e)`,
  (let cp = bvi_let_compile_def in
   let cs = bvi_let_compile_sing_def in
   let sz = size_thms "bvi_exp" in
   (* HOL4 does this induction with ho_match_mp_tac compile_sing_ind,
      the induction theorem that its termination proof left behind.
      HOL Light's define keeps no such theorem, so the induction is
      on the measure the definition was made with -- here a mutual
      one, over the size of an expression and over the size of a
      list of them -- and every use of the hypothesis leaves a side
      condition. *)
   let compile_CONS = prove
    (`!n d x xs. bvi_let_compile n d (CONS x xs) =
                 APPEND (bvi_let_compile n d [x])
                        (bvi_let_compile n d xs)`,
     REPEAT GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `xs:bvi_exp list` list_CASES) THEN
     REWRITE_TAC[cp; APPEND_NIL]) in
   (* no expression has size 0, which is what the base case says *)
   let size_pos = prove
    (`!e:bvi_exp. 1 <= bvi_exp_size e`,
     GEN_TAC THEN
     STRUCT_CASES_TAC(ISPEC `e:bvi_exp` (cases_of `:bvi_exp`)) THEN
     REWRITE_TAC sz THEN ARITH_TAC) in
   let size_tac =
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN
     REWRITE_TAC(list_size :: sz) THEN ASM_ARITH_TAC in
   let cond1 t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "bvi_exp_size" [t]) `k:num` in
   let cond2 t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "list_size" [`bvi_exp_size`; t]) `k:num` in
   let use1_by tac t =
     SUBGOAL_THEN (cond1 t)
       (fun c -> FIRST_ASSUM(fun ih ->
          REWRITE_TAC[MATCH_MP (CONJUNCT1 ih) c])) THEN TRY tac in
   let use2_by tac t =
     SUBGOAL_THEN (cond2 t)
       (fun c -> FIRST_ASSUM(fun ih ->
          REWRITE_TAC[MATCH_MP (CONJUNCT2 ih) c])) THEN TRY tac in
   let use1 = use1_by size_tac in
   let use2 = use2_by size_tac in
   let both = REWRITE_TAC[cp; cs] in
   (* Var and Force read the environment, so both sides have the
      same match on it *)
   let match_case =
     REWRITE_TAC[cp; cs] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     EVERY_CASE_TAC THEN REWRITE_TAC[] in
   (* the Let is the one clause that compiles something other than
      a sub-term: the list without its last expression, and that
      last expression as the new body *)
   let sing_let_case =
     REWRITE_TAC[cp; cs; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     COND_CASES_TAC THENL
     [use1 `b2:bvi_exp` THEN REWRITE_TAC[];
      COND_CASES_TAC THENL
      [use2_by (MP_TAC(ISPECL [`bvi_exp_size`; `bs:bvi_exp list`]
                         list_size_BUTLAST) THEN size_tac)
         `BUTLAST (bs:bvi_exp list)` THEN
       use1_by
         (MP_TAC(MATCH_MP (ISPEC `bvi_exp_size` list_size_LAST)
                   (REWRITE_RULE[LENGTH_EQ_NIL]
                      (ASSUME `~(LENGTH (bs:bvi_exp list) = 0)`)))
          THEN size_tac)
         `LAST (bs:bvi_exp list)` THEN
       REWRITE_TAC[HD];
       use2 `bs:bvi_exp list` THEN use1 `b2:bvi_exp` THEN
       REWRITE_TAC[HD]]] in
   let sing_call_case =
     REWRITE_TAC[cp; cs] THEN
     NAMED_CASES_TAC `hh:bvi_exp option` [[]; ["ce"]] THEN
     TRY MATCH_REDUCE_TAC THEN use2 `gs:bvi_exp list` THEN
     TRY(use1 `ce:bvi_exp`) THEN REWRITE_TAC[HD] in
   let part1 =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `e:bvi_exp`
       [["v"]; ["a1"; "a2"; "a3"]; ["bs"; "b2"]; ["r1"]; ["t1"];
        ["tt"; "dd"; "gs"; "hh"]; ["loc"; "fv"]; ["op"; "os"];
        ["rets"; "lt"; "ld"; "ls"; "ly"]; ["rs"]] THENL
     [match_case;
      both THEN use1 `a1:bvi_exp` THEN use1 `a2:bvi_exp` THEN
      use1 `a3:bvi_exp` THEN REWRITE_TAC[HD];
      sing_let_case;
      both THEN use1 `r1:bvi_exp` THEN REWRITE_TAC[HD];
      both THEN use1 `t1:bvi_exp` THEN REWRITE_TAC[HD];
      sing_call_case;
      match_case;
      both THEN use2 `os:bvi_exp list` THEN REWRITE_TAC[];
      both THEN use2 `ls:bvi_exp list` THEN use1 `ly:bvi_exp` THEN
      REWRITE_TAC[HD];
      both THEN use2 `rs:bvi_exp list` THEN REWRITE_TAC[]] in
   (* and the list, where compile takes the head apart with the
      clause for two or more and compile_list with its own *)
   let part2 =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `es:bvi_exp list` [[]; ["y"; "ys"]] THENL
     [REWRITE_TAC[cp; cs];
      REWRITE_TAC[cs] THEN ONCE_REWRITE_TAC[compile_CONS] THEN
      use1 `y:bvi_exp` THEN use2 `ys:bvi_exp list` THEN
      REWRITE_TAC[APPEND]] in
   let sing_base =
     CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `F` CONTR_TAC THEN
      MP_TAC(ISPEC `e:bvi_exp` size_pos) THEN ASM_ARITH_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      NAMED_CASES_TAC `es:bvi_exp list` [[]; ["y"; "ys"]] THENL
      [REWRITE_TAC[cp; cs];
       FIRST_ASSUM MP_TAC THEN
       REWRITE_TAC[list_size; ARITH_RULE `~(1 + a + b <= 0)`]]] in
   SUBGOAL_THEN
     `!k. (!n d e. bvi_exp_size e <= k ==>
             bvi_let_compile n d [e] =
             [bvi_let_compile_sing n d e]) /\
          (!n d es. list_size bvi_exp_size es <= k ==>
             bvi_let_compile_list n d es = bvi_let_compile n d es)`
     (fun th -> CONJ_TAC THEN REPEAT GEN_TAC THENL
        [MP_TAC(CONJUNCT1(SPEC `bvi_exp_size (e:bvi_exp)` th));
         MP_TAC(CONJUNCT2
                  (SPEC `list_size bvi_exp_size (e:bvi_exp list)`
                     th))]
        THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]) THEN
   INDUCT_TAC THENL
   [sing_base; CONJ_TAC THENL [part1; part2]]));;

(* [simp] *)
let compile_length = prove
 (`!n d xs. LENGTH (bvi_let_compile n d xs) = LENGTH xs`,
  (let cp = bvi_let_compile_def in
   let sz = size_thms "bvi_exp" in
   (* HOL4 takes the induction theorem that its termination proof
      left behind (HO_MATCH_MP_TAC compile_ind); the port induces on
      the measure the definition was made with *)
   let cond t =
     mk_binop `(<=):num->num->bool`
       (list_mk_icomb "list_size" [`bvi_exp_size`; t]) `k:num` in
   let size_tac =
     RULE_ASSUM_TAC(REWRITE_RULE(list_size :: sz)) THEN
     REWRITE_TAC(list_size :: sz) THEN ASM_ARITH_TAC in
   let use_ih t =
     SUBGOAL_THEN (cond t)
       (fun c -> FIRST_ASSUM(fun ih -> REWRITE_TAC[MATCH_MP ih c]))
     THEN TRY size_tac in
   (* every clause but the empty list, the list of two or more and
      the Let of nothing makes a list of one *)
   let one = REWRITE_TAC[cp; LENGTH] in
   let sing_case =
     REWRITE_TAC[cp] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     EVERY_CASE_TAC THEN REWRITE_TAC[LENGTH] in
   let let_case =
     REWRITE_TAC[cp; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REPEAT COND_CASES_TAC THEN TRY(use_ih `[e:bvi_exp]`) THEN
     REWRITE_TAC[LENGTH] in
   let single_case =
     NAMED_CASES_TAC `x1:bvi_exp`
       [["v"]; ["e1"; "e2"; "e3"]; ["es"; "e"]; ["e"]; ["e"];
        ["tt"; "dd"; "es"; "hh"]; ["loc"; "v"]; ["op"; "es"];
        ["rets"; "tt"; "dd"; "es"; "e"]; ["es"]] THENL
     [sing_case; one; let_case; one; one; one; sing_case; one; one;
      one] in
   let cons_cons_case =
     REWRITE_TAC[cp; LENGTH_APPEND] THEN
     use_ih `[x1:bvi_exp]` THEN use_ih `(x2:bvi_exp) :: xr2` THEN
     REWRITE_TAC[LENGTH] THEN ARITH_TAC in
   let base_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `xs:bvi_exp list` [[]; ["x1"; "xr"]] THENL
     [REWRITE_TAC[cp];
      FIRST_ASSUM MP_TAC THEN
      REWRITE_TAC[list_size; ARITH_RULE `~(1 + a + b <= 0)`]] in
   let step_case =
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     NAMED_CASES_TAC `xs:bvi_exp list` [[]; ["x1"; "xr"]] THENL
     [REWRITE_TAC[cp];
      NAMED_CASES_TAC `xr:bvi_exp list` [[]; ["x2"; "xr2"]] THENL
      [single_case; cons_cons_case]] in
   MEASURE_INDUCT_TAC `list_size bvi_exp_size` THENL
   [base_case; step_case]));;

let compile_HD_SING = prove
 (`[HD (bvi_let_compile n d [x])] = bvi_let_compile n d [x]`,
  (* the compiled list of one has length one, so it is its own head
     put back into a list *)
  (MP_TAC(SPECL [`n:num list`; `d:num`; `[x:bvi_exp]`]
            compile_length) THEN
   STRUCT_CASES_TAC(ISPEC `bvi_let_compile n d [x]` list_CASES) THEN
   REWRITE_TAC[LENGTH; SUC_INJ; LENGTH_EQ_NIL; NOT_SUC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   TRY(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[HD]));;

let bvi_let_compile_exp_def = new_definition
  `bvi_let_compile_exp x =
     (match bvi_let_compile [] 0 [x] with (y :: _14) -> y | _15 ->
       Var 0)
   // impossible`;;
hol4_overload "compile_exp" "bvi_let_compile_exp";;

(* compile_exp_eq *)
let bvi_let_compile_exp_eq = prove
 (`!x. bvi_let_compile_exp x = bvi_let_compile_sing [] 0 x`,
  (* HOL4 applies compile_sing to compile_exp_def: the compiled
     list of one is a singleton, so the match reduces to its head *)
  (let ce = bvi_let_compile_exp_def in
   GEN_TAC THEN REWRITE_TAC[ce; CONJUNCT1 compile_sing] THEN
   MATCH_REDUCE_TAC THEN REWRITE_TAC[]));;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
