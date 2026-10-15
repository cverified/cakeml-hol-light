(* ======================================================== *)
(*  parmove: ported from HOL4's
    compiler/backend/reg_alloc/parmoveScript.sml  *)
(* ======================================================== *)

(*
  Compiling parallel moves.
  This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
    Tilting at windmills with Coq: formal verification of a compilation
    algorithm for parallel moves
  http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "misc/misc.ml";;
needs "semantics/typeSystem.ml";;

(* Non-deterministic algorithm *)

(* The state is three lists of moves:
   (to-process, being-processed, processed)
   each step (roughly) shifts some move from left to right in the state
     *)

(* NONE is a temporary register; real registers are SOME x. *)

(* HOL4 overload (expanded in the port):
     NoRead = λμ dn. ¬MEM dn (MAP SND μ) *)

(* HOL4 ML code, not ported:
fun replace_quote from to (QUOTE s) = QUOTE(Portable.replace_string
  {from=from,to=to} s)
  | replace_quote _ _ x = x
*)

(* HOL4 ML code, not ported:
val _ = add_infix("step",450,NONASSOC);
*)

(* HOL4 ML code, not ported:
val (step_rules,step_ind,step_cases) = (Hol_reln o
  List.map(replace_quote "\226\150\183" "step"))`
  ((μ1++[(r,r)]++μ2,σ,τ) ▷ (μ1++μ2,σ,τ)) ∧
  ((μ1++[(d,s)]++μ2,[],τ) ▷ (μ1++μ2,[(d,s)],τ)) ∧
  ((μ1++[(r,d)]++μ2,[(d,s)]++σ,τ) ▷ (μ1++μ2,[(r,d);(d,s)]++σ,τ)) ∧
  ((μ,σ++[(d,s)],τ) ▷ (μ,σ++[(d,NONE)],[(NONE,s)]++τ)) ∧
  (NoRead μ dn ∧ dn ≠ s0 ⇒
   (μ,[(dn,sn)]++σ++[(d0,s0)],τ) ▷ (μ,σ++[(d0,s0)],[(dn,sn)]++τ)) ∧
  (NoRead μ d ⇒
   (μ,[(d,s)],τ) ▷ (μ,[],[(d,s)]++τ))`;
*)

(* HOL4 ML code, not ported:
val _ = set_fixity"\226\150\183"(Infix(NONASSOC,450));
*)
(* HOL4 overload (expanded in the port):
     None =  *)

(* HOL4 ML code, not ported:
val _ = set_fixity "\226\150\183*" (Infix(NONASSOC,450));
*)
(* HOL4 overload (expanded in the port):
     None =  *)

(* invariant on states *)

let windmill_def = cake_define
  `windmill (moves:('a#'a) list) = ALL_DISTINCT (MAP FST moves)`;;

let path_def = cake_define
  `(parmove_path [] <=> T) /\ (parmove_path [_1] <=> T) /\
   (parmove_path ((c,b') :: (b,a) :: p) <=>
      (b = b') /\ parmove_path ((b,a) :: p))`;;

let wf_def = cake_define
  `parmove_wf ('gk,'gq,'gr) <=>
     windmill ('gk ++ 'gq) /\
     EVERY IS_SOME (MAP FST 'gk) /\
     EVERY IS_SOME (MAP SND 'gk) /\
     (~NULL 'gq ==> EVERY IS_SOME (MAP SND (FRONT 'gq))) /\
     EVERY IS_SOME (MAP FST 'gq) /\
     parmove_path 'gq`;;
hol4_overload "wf" "parmove_wf";;
(* HOL4 overload (expanded in the port):
     None =  *)

(* The invariant is preserved *)

(* semantics of moves *)

let parsem_def = cake_define
  `parsem 'gk 'gp = =++ 'gp (ZIP (MAP FST 'gk,MAP ('gp o SND) 'gk))`;;

let seqsem_def = cake_define
  `(seqsem [] 'gp = 'gp) /\
   (seqsem ((d,s) :: 'gr) 'gp = seqsem 'gr ((d =+ 'gp s) 'gp))`;;

(* HOL4 ML code, not ported:
val seqsem_ind = theorem"seqsem_ind";
*)

(* semantics of the state *)

let sem_def = cake_define
  `sem ('gk,'gq,'gr) 'gp = parsem ('gk ++ 'gq) (seqsem (REVERSE 'gr)
  'gp)`;;

(* semantic preservation *)

let eqenv_def = cake_define
  `eqenv 'gp 1 'gp 2 <=> (!r. IS_SOME r ==> ('gp 1 r = 'gp 2 r))`;;
(* HOL4 ML code, not ported:
val _ = set_fixity"\226\137\161"(Infix(NONASSOC,450));
*)
(* HOL4 overload (expanded in the port):
     None =  *)

(* deterministic algorithm *)

(* HOL4 ML code, not ported:
val _ = add_infix("dstep",450,NONASSOC);
*)

(* HOL4 ML code, not ported:
val (dstep_rules,dstep_ind,dstep_cases) = (Hol_reln o
  List.map(replace_quote "\226\134\170" "dstep"))`
  (([(r,r)]++μ,[],τ) ↪ (μ,[],τ)) ∧
  (s ≠ d ⇒
   ([(d,s)]++μ,[],τ) ↪ (μ,[(d,s)],τ)) ∧
  (NoRead μ1 d ⇒
   (μ1++[(r,d)]++μ2,[(d,s)]++σ,τ) ↪
   (μ1++μ2,[(r,d);(d,s)]++σ,τ)) ∧
  (NoRead μ r ⇒
   (μ,[(r,s)]++σ++[(d,r)],τ) ↪
   (μ,σ++[(d,NONE)],[(r,s);(NONE,r)]++τ)) ∧
  (NoRead μ dn ∧ dn ≠ s0 ⇒
   (μ,[(dn,sn)]++σ++[(d0,s0)],τ) ↪
   (μ,σ++[(d0,s0)],[(dn,sn)]++τ)) ∧
  (NoRead μ d ⇒
   (μ,[(d,s)],τ) ↪ (μ,[],[(d,s)]++τ))`;
*)

(* HOL4 ML code, not ported:
val _ = set_fixity"\226\134\170"(Infix(NONASSOC,450));
*)
(* HOL4 overload (expanded in the port):
     None =  *)

(* HOL4 ML code, not ported:
val _ = set_fixity "\226\134\170*" (Infix(NONASSOC,450));
*)
(* HOL4 overload (expanded in the port):
     None =  *)

(* ⊢ s1 condition not included in paper;
   not sure if necessary, but couldn't get
   their proof to work *)

(* functional algorithm *)

let fstep_def = cake_define
  `fstep st =
   (match st with ([],[],_2) -> st | ((d,s) :: t,[],l) ->
     (if s = d then (t,[],l) else (t,[(d,s)],l)) | (t,(d,s) :: b,l)
       ->
     splitAtPki (\i p. SND p = d)
       (\t1 rt2.
         match rt2 with (rd :: t2) -> (t1 ++ t2,rd :: (d,s) :: b,l) |
           [] -> (if NULL b then (t,[],(d,s) :: l) else
                 let (b',(d',s')) = (FRONT b,LAST b) in
                 if s' = d then (t,SNOC (d',NONE) b',(d,s) ::
                   (NONE,d) :: l) else (t,b,(d,s) :: l)))
       t)`;;

(* HOL4 ML code, not ported:
val not_or = METIS_PROVE[]``¬a ∨ b ⇔ a ⇒ b``;
*)

(* HOL4 termination: >> rw[fstep_def] >- (
   fs[NULL_LENGTH,LENGTH_NIL,splitAtPki_def] >> simp[UNCURRY] >> rw[]
   >>
   simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL]
   ) >- ( simp[splitAtPki_def,UNCURRY] >> rw[] >> simp[] >>
   fs[NULL_LENGTH,LENGTH_NIL] >>
   simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL]
   ) >> ( every_case_tac >> simp[splitAtPki_def,UNCURRY] >> rw[] >>
   simp[splitAtPki_def,UNCURRY] >> simp[splitAtPki_EQN] >>
   every_case_tac >> simp[] >> TRY ( fs[NULL_LENGTH,LENGTH_NIL] >>
   simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL]
   >> NO_TAC) >> fs[WhileTheory.OLEAST_def] >> rw[] >> pop_assum
   mp_tac >> numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >> rw[]
   >> simp[LENGTH_TAKE,ADD1] >> rfs[DROP_CONS_EL] >> rw[] >>
   simp[ADD1] >> metis_tac[]) *)
let pmov_def = cake_define_wf
  `MEASURE (\('gk,'gq,'gr). 2 * LENGTH 'gk + LENGTH 'gq)`
  `pmov s = (match s with ([],[],_3) -> s | _4 -> pmov (fstep s))`;;

(* HOL4 ML code, not ported:
val pmov_ind = theorem"pmov_ind";
*)

(* The top-level parallel move compiler *)

let parmove_def = cake_define
  `parmove (xs:('a#'a) list) =
     REVERSE (SND (SND (pmov (MAP (\(x,y). (SOME x,SOME y))
       xs,[],[]))))`;;

(* the compiler does not invent new moves *)

(* the compiler does not use uninitialised temporaries *)

let not_use_temp_before_assign_def = cake_define
  `not_use_temp_before_assign x1 =
        match x1 with
          [] -> T
        | ((d,NONE) :: ls) -> F
        | ((NONE,s) :: ls) -> T
        | ((d,s) :: ls) -> not_use_temp_before_assign ls`;;

(* the compiler preserves all-distinct variables *)

(* the compiler retains all non-trivial moves *)

let state_to_list_def = cake_define
  `state_to_list p = APPEND (FST p) (FST (SND p)) ++ SND (SND p)`;;

(* mapping an injective function over compiled moves *)

let map_state_def = cake_define
  `map_state f = (let m = MAP (f ## f) in m ## m ## m)`;;

let inj_on_state_def = cake_define
  `inj_on_state f p =
      (let ls0 = state_to_list p in
      let ls = MAP FST ls0 ++ MAP SND ls0 in
      (!x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y) /\
      (!x. f x = NONE <=> x = NONE))`;;
