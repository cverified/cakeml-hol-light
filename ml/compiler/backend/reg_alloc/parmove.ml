(* ======================================================== *)
(*  parmove: ported from HOL4's
    compiler/backend/reg_alloc/parmoveScript.sml
    A definition theory, with 16 definitions and 57 theorems.
    Needed by word_to_stack.ml and word_to_stackProof.ml.  *)
(* ======================================================== *)

(*
  Compiling parallel moves.
  This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
    Tilting at windmills with Coq: formal verification of a compilation
    algorithm for parallel moves
  http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf
*)

needs "lib/sorting.ml";;
needs "misc/misc.ml";;

(* Non-deterministic algorithm *)

(* The state is three lists of moves:
   (to-process, being-processed, processed)
   each step (roughly) shifts some move from left to right in the state *)

(* NONE is a temporary register; real registers are SOME x. *)

(* HOL4 parmoveScript.sml:22: the overload NoRead, which the port
   expands *)

(* HOL4 parmoveScript.sml:24-25: ML code, not ported *)

(* HOL4 parmoveScript.sml:27: ML code, not ported *)

let step_rules = cake_inductive
  `(step (mu1 ++ [(r,r)] ++ mu2,sigma,tau) (mu1 ++ mu2,sigma,tau)) /\
   (step (mu1 ++ [(d,s)] ++ mu2,[],tau) (mu1 ++ mu2,[(d,s)],tau)) /\
   (step (mu1 ++ [(r,d)] ++ mu2,[(d,s)] ++ sigma,tau) (mu1 ++
     mu2,[(r,d); (d,s)] ++ sigma,tau)) /\
   (step (mu,sigma ++ [(d,s)],tau) (mu,sigma ++ [(d,NONE)],[(NONE,s)]
     ++ tau)) /\
   ((\mu dn. ~(MEM dn (MAP SND mu))) mu dn /\ ~(dn = s0) ==> step
     (mu,[(dn,sn)] ++ sigma ++ [(d0,s0)],tau) (mu,sigma ++
     [(d0,s0)],[(dn,sn)] ++ tau)) /\
   ((\mu dn. ~(MEM dn (MAP SND mu))) mu d ==> step
     (mu,[(d,s)],tau) (mu,[],[(d,s)] ++ tau))`;;

(* HOL4 parmoveScript.sml:39: ML code, not ported *)
(* HOL4 parmoveScript.sml:40: the overload ▷, which the port expands *)

(* HOL4 parmoveScript.sml:42: ML code, not ported *)
(* HOL4 parmoveScript.sml:43: the overload ▷*, which the port expands *)

(* invariant on states *)

let windmill_def = cake_define
  `windmill (moves:('a#'a) list) = ALL_DISTINCT (MAP FST moves)`;;

let windmill_cons = prove
 (`windmill (x :: ls) <=> ~(MEM (FST x) (MAP FST ls)) /\ windmill ls`,
  CHEAT_TAC);;

let path_def = cake_define_list
  [`parmove_path [] <=> T`;
   `parmove_path [_1] <=> T`;
   `parmove_path ((c,b') :: (b,a) :: p) <=>
         (b = b') /\ parmove_path ((b,a) :: p)`];;
hol4_overload "path" "parmove_path";;

let path_change_start = prove
 (`!y z x. parmove_path (SNOC x y) /\ FST x = FST z ==> parmove_path
  (SNOC z y)`,
  CHEAT_TAC);;

let path_tail = prove
 (`!t h. parmove_path (h :: t) ==> parmove_path t`,
  CHEAT_TAC);;

(* [local] *)
let path_imp_mem = prove
 (`parmove_path (x :: y) ==>
    ~(NULL y) ==> MEM (SND x) (MAP FST y)`,
  CHEAT_TAC);;

(* [local] *)
let path_imp_mem2 = prove
 (`parmove_path x ==>
    (!y. MEM y (MAP SND x) /\ ~(y = SND (LAST x)) ==>
        MEM y (MAP FST x))`,
  CHEAT_TAC);;

(* [local] *)
let NoRead_path = prove
 (`!sigma. parmove_path sigma /\ windmill sigma /\ LENGTH sigma >= 2 /\
  ~(FST (HD sigma) = SND (LAST sigma)) ==>
    (\mu dn. ~(MEM dn (MAP SND mu))) (TL sigma) (FST (HD sigma))`,
  CHEAT_TAC);;

let parmove_wf_def = cake_define
  `parmove_wf (mu,sigma,tau) <=>
     windmill (mu ++ sigma) /\
     EVERY IS_SOME (MAP FST mu) /\
     EVERY IS_SOME (MAP SND mu) /\
     (~(NULL sigma) ==> EVERY IS_SOME (MAP SND (FRONT sigma))) /\
     EVERY IS_SOME (MAP FST sigma) /\
     parmove_path sigma`;;
hol4_overload "wf" "parmove_wf";;
(* HOL4 parmoveScript.sml:129: the overload ⊢, which the port expands *)

let wf_init = prove
 (`windmill mu /\
   EVERY IS_SOME (MAP FST mu) /\
   EVERY IS_SOME (MAP SND mu) ==>
    (wf) (mu,[],[])`,
  CHEAT_TAC);;

(* The invariant is preserved *)

let wf_step = prove
 (`!s1 s2. (step) s1 s2 ==> (wf) s1 ==> (wf) s2`,
  CHEAT_TAC);;

let wf_steps = prove
 (`!s1 s2. (wf) s1 /\ (RTC (step)) s1 s2 ==> (wf) s2`,
  CHEAT_TAC);;

(* semantics of moves *)

let parsem_def = cake_define
  `parsem mu rho = UPDATE_LIST rho (ZIP (MAP FST mu) (MAP (rho o SND)
  mu))`;;

(* [simp] *)
let parsem_nil = prove
 (`parsem [] = I`,
  CHEAT_TAC);;

let parsem_cons = prove
 (`~(MEM x (MAP FST mu)) ==>
   parsem ((x,y) :: mu) rho = (x =+ rho y) (parsem mu rho)`,
  CHEAT_TAC);;

let independence = prove
 (`!mu1 s d mu2 mu.
      windmill mu /\ mu = mu1 ++ [(d,s)] ++ mu2 ==>
      parsem mu = parsem ([(d,s)] ++ mu1 ++ mu2)`,
  CHEAT_TAC);;

let parsem_perm = prove
 (`windmill l1 /\ PERM l1 l2 ==> parsem l1 = parsem l2`,
  CHEAT_TAC);;

let parsem_untouched = prove
 (`!rho mu x. windmill mu /\ ~(MEM x (MAP FST mu)) ==> parsem mu rho x
  = rho x`,
  CHEAT_TAC);;

let parsem_change_env = prove
 (`(~(MEM x (MAP FST mu)) ==> rho1 x = rho2 x) /\
   MAP (rho1 o SND) mu = MAP (rho2 o SND) mu ==>
   parsem mu rho1 x = parsem mu rho2 x`,
  CHEAT_TAC);;

let parsem_NoRead = prove
 (`(\mu dn. ~(MEM dn (MAP SND mu))) mu x ==>
   parsem ((x,y) :: mu) rho = parsem mu ((x =+ rho y) rho)`,
  CHEAT_TAC);;

let parsem_MAP_INJ = prove
 (`!ms. windmill ms /\
        INJ f (set_of_list (MAP FST ms ++ MAP SND ms)) UNIV ==>
        (!x. MEM x (MAP FST ms) ==> parsem (MAP (f ## f) ms) r (f
          x) = parsem ms (r o f) x)`,
  CHEAT_TAC);;

let seqsem_def = cake_define_list
  [`seqsem [] rho = rho`;
   `seqsem ((d,s) :: tau) rho = seqsem tau ((d =+ rho s) rho)`];;

(* HOL4 parmoveScript.sml:323: ML code, not ported *)

let seqsem_append = prove
 (`!l1 l2. seqsem (l1 ++ l2) = seqsem l2 o seqsem l1`,
  CHEAT_TAC);;

let seqsem_move_unchanged = prove
 (`!ms r. ~(MEM k (MAP FST ms)) ==> seqsem ms r k = r k`,
  CHEAT_TAC);;

(* semantics of the state *)

let sem_def = cake_define
  `sem (mu,sigma,tau) rho = parsem (mu ++ sigma) (seqsem (REVERSE
  tau) rho)`;;

let sem_init = prove
 (`sem (mu,[],[]) = parsem mu`,
  CHEAT_TAC);;

let sem_final = prove
 (`sem ([],[],tau) = seqsem (REVERSE tau)`,
  CHEAT_TAC);;

(* semantic preservation *)

let eqenv_def = cake_define
  `eqenv rho1 rho2 <=> (!r. IS_SOME r ==> (rho1 r = rho2 r))`;;
(* HOL4 parmoveScript.sml:361: ML code, not ported *)
(* HOL4 parmoveScript.sml:362: the overload ≡, which the port writes
   as an application of eqenv *)

(* [local] *)
let eqenv_sym = prove
 (`eqenv p1 p2 ==> eqenv p2 p1`,
  CHEAT_TAC);;

(* [local] *)
let step_sem = prove
 (`!s1 s2. (step) s1 s2 ==> (wf) s1 ==> (!rho. eqenv (sem s1 rho) (sem
  s2 rho))`,
  CHEAT_TAC);;

let steps_sem = prove
 (`!s1 s2. (RTC (step)) s1 s2 /\ (wf) s1 ==> (!rho. eqenv (sem s1 rho)
  (sem s2 rho))`,
  CHEAT_TAC);;

let steps_correct = prove
 (`windmill mu /\
   EVERY IS_SOME (MAP FST mu) /\
   EVERY IS_SOME (MAP SND mu) /\ (RTC (step)) (mu,[],[]) ([],[],tau)
     ==>
   (!rho. eqenv (parsem mu rho) (seqsem (REVERSE tau) rho))`,
  CHEAT_TAC);;

(* deterministic algorithm *)

(* HOL4 parmoveScript.sml:476: ML code, not ported *)

let dstep_rules = cake_inductive
  `(dstep ([(r,r)] ++ mu,[],tau) (mu,[],tau)) /\
   (~(s = d) ==> dstep ([(d,s)] ++ mu,[],tau) (mu,[(d,s)],tau)) /\
   ((\mu dn. ~(MEM dn (MAP SND mu))) mu1 d ==> dstep (mu1 ++ [(r,d)]
     ++ mu2,[(d,s)] ++ sigma,tau)
    (mu1 ++ mu2,[(r,d); (d,s)] ++ sigma,tau)) /\
   ((\mu dn. ~(MEM dn (MAP SND mu))) mu r ==> dstep (mu,[(r,s)] ++
     sigma ++ [(d,r)],tau)
    (mu,sigma ++ [(d,NONE)],[(r,s); (NONE,r)] ++ tau)) /\
   ((\mu dn. ~(MEM dn (MAP SND mu))) mu dn /\ ~(dn = s0) ==> dstep
     (mu,[(dn,sn)] ++ sigma ++ [(d0,s0)],tau)
    (mu,sigma ++ [(d0,s0)],[(dn,sn)] ++ tau)) /\
   ((\mu dn. ~(MEM dn (MAP SND mu))) mu d ==> dstep
     (mu,[(d,s)],tau) (mu,[],[(d,s)] ++ tau))`;;

(* HOL4 parmoveScript.sml:494: ML code, not ported *)
(* HOL4 parmoveScript.sml:495: the overload ↪, which the port expands *)

(* HOL4 parmoveScript.sml:497: ML code, not ported *)
(* HOL4 parmoveScript.sml:498: the overload ↪*, which the port
   expands *)

(* ⊢ s1 condition not included in paper;
   not sure if necessary, but couldn't get
   their proof to work *)
(* [local] *)
let dstep_step = prove
 (`!s1 s2. (dstep) s1 s2 ==> (wf) s1 ==> (RTC (step)) s1 s2`,
  CHEAT_TAC);;

let dsteps_steps = prove
 (`!s1 s2. (RTC (dstep)) s1 s2 ==> (wf) s1 ==> (RTC (step)) s1 s2`,
  CHEAT_TAC);;

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

(* HOL4 parmoveScript.sml:547: the ML values that the definitions
   below antiquote *)

let fstep_dstep = prove
 (`(!tau. ~(s = ([],[],tau))) ==> (dstep) s (fstep s)`,
  CHEAT_TAC);;

(* HOL4 parmoveScript.sml:610-638: the tactic that proves the
   termination *)
let pmov_def = cake_define_wf
  `MEASURE (\(mu,sigma,tau). 2 * LENGTH mu + LENGTH sigma)`
  `pmov s = (match s with ([],[],_3) -> s | _4 -> pmov (fstep s))`;;

(* HOL4 parmoveScript.sml:640: ML code, not ported *)

let pmov_dsteps = prove
 (`!s. (RTC (dstep)) s (pmov s)`,
  CHEAT_TAC);;

let pmov_final = prove
 (`!s. ?tau. pmov s = ([],[],tau)`,
  CHEAT_TAC);;

(* The top-level parallel move compiler *)

let parmove_def = cake_define
  `parmove (xs:('a#'a) list) =
     REVERSE (SND (SND (pmov (MAP (\(x,y). (SOME x,SOME y))
       xs,[],[]))))`;;

let parmove_correct = prove
 (`windmill xs ==>
   (!rho. eqenv (seqsem (parmove xs) rho)
       (parsem (MAP (\(x,y). (SOME x,SOME y)) xs) rho))`,
  CHEAT_TAC);;

(* the compiler does not invent new moves *)

let MEM_MAP_FST_SND_SND_pmov = prove
 (`!p x.
    MEM (SOME x) (MAP FST (SND (SND (pmov p)))) ==>
    MEM (SOME x) (MAP FST (FST p ++ FST (SND p) ++ SND (SND p)))`,
  CHEAT_TAC);;

let MEM_MAP_FST_parmove = prove
 (`MEM (SOME x) (MAP FST (parmove mvs)) ==> MEM x (MAP FST mvs)`,
  CHEAT_TAC);;

let MEM_MAP_SND_SND_SND_pmov = prove
 (`!p x.
    MEM (SOME x) (MAP SND (SND (SND (pmov p)))) ==>
    MEM (SOME x) (MAP SND (FST p ++ FST (SND p) ++ SND (SND p)))`,
  CHEAT_TAC);;

let MEM_MAP_SND_parmove = prove
 (`MEM (SOME x) (MAP SND (parmove mvs)) ==> MEM x (MAP SND mvs)`,
  CHEAT_TAC);;

(* the compiler does not use uninitialised temporaries *)

let not_use_temp_before_assign_def = cake_define
  `not_use_temp_before_assign x1 =
        match x1 with
          [] -> T
        | ((d,NONE) :: ls) -> F
        | ((NONE,s) :: ls) -> T
        | ((d,s) :: ls) -> not_use_temp_before_assign ls`;;

let not_use_temp_before_assign_append = prove
 (`!l1 l2.
   (not_use_temp_before_assign (l1 ++ l2) <=>
    not_use_temp_before_assign l1 /\
    (EVERY IS_SOME (MAP FST l1) ==> not_use_temp_before_assign l2))`,
  CHEAT_TAC);;

let not_use_temp_before_assign_insert = prove
 (`!l1 l2.
   not_use_temp_before_assign (l1 ++ l2) ==>
   not_use_temp_before_assign (l1 ++ [(SOME x,SOME y)] ++ l2)`,
  CHEAT_TAC);;

let not_use_temp_before_assign_thm = prove
 (`!ls. not_use_temp_before_assign ls =
    (!i. find_index NONE (MAP SND ls) 0 = SOME i ==>
      (?j. find_index NONE (MAP FST ls) 0 = SOME j /\ j < i))`,
  CHEAT_TAC);;

let step_not_use_temp_before_assign = prove
 (`!s1 s2. (step) s1 s2 ==>
     (wf) s1 /\
    not_use_temp_before_assign (REVERSE (FST (SND s1) ++ SND (SND
      s1))) ==>
    not_use_temp_before_assign (REVERSE (FST (SND s2) ++ SND (SND
      s2)))`,
  CHEAT_TAC);;

let steps_not_use_temp_before_assign = prove
 (`!s1 s2.
    (\s1. (wf) s1 /\ not_use_temp_before_assign (REVERSE (FST (SND
      s1) ++ SND (SND s1)))) s1 /\ (RTC (step)) s1 s2 ==>
    (\s1. (wf) s1 /\ not_use_temp_before_assign (REVERSE (FST (SND
      s1) ++ SND (SND s1)))) s2`,
  CHEAT_TAC);;

let pmov_not_use_temp_before_assign = prove
 (`!p i.
    (wf) p /\ not_use_temp_before_assign (REVERSE (FST (SND p) ++
      SND (SND p))) ==> not_use_temp_before_assign (REVERSE (FST (SND
      (pmov p)) ++ SND (SND (pmov p))))`,
  CHEAT_TAC);;

let parmove_not_use_temp_before_assign = prove
 (`windmill mvs ==>
   (match find_index NONE (MAP SND (parmove mvs)) 0 with
      NONE -> T | SOME i ->
      (match find_index NONE (MAP FST (parmove mvs)) 0 with
        NONE -> F | SOME j -> ~(i <= j)))`,
  CHEAT_TAC);;

(* the compiler preserves all-distinct variables *)

let ALL_DISTINCT_step = prove
 (`!s1 s2. (step) s1 s2 ==>
    ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1) ++
      (SND (SND s1))))) ==>
    ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s2 ++ FST (SND s2)
      ++ (SND (SND s2)))))`,
  CHEAT_TAC);;

let ALL_DISTINCT_steps = prove
 (`!s1 s2.
    (\s1. ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND
      s1) ++ (SND (SND s1)))))) s1 /\ (RTC (step)) s1 s2 ==>
    (\s1. ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND
      s1) ++ (SND (SND s1)))))) s2`,
  CHEAT_TAC);;

let ALL_DISTINCT_pmov = prove
 (`!p. (wf) p /\ ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST p ++ FST
  (SND p) ++ SND (SND p)))) ==>
       ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST (pmov p) ++ FST
         (SND (pmov p)) ++ SND (SND (pmov p)))))`,
  CHEAT_TAC);;

let ALL_DISTINCT_parmove = prove
 (`ALL_DISTINCT (MAP FST mvs) ==>
   ALL_DISTINCT (FILTER IS_SOME (MAP FST (parmove mvs)))`,
  CHEAT_TAC);;

(* the compiler retains all non-trivial moves *)

let state_to_list_def = cake_define
  `state_to_list p = APPEND (FST p) (FST (SND p)) ++ SND (SND p)`;;

let step_preserves_moves = prove
 (`!s1 s2. (step) s1 s2 ==>
    (!x. (?y. MEM (x,y) (state_to_list s1) /\ ~(x = y)) ==>
        (?y. MEM (x,y) (state_to_list s2) /\ ~(x = y)))`,
  CHEAT_TAC);;

let steps_preserves_moves = prove
 (`!s1 s2.
    (\s1. (?y. MEM (x,y) (state_to_list s1) /\ ~(x = y))) s1 /\ (RTC
      (step)) s1 s2 ==>
    (\s1. (?y. MEM (x,y) (state_to_list s1) /\ ~(x = y))) s2`,
  CHEAT_TAC);;

let pmov_preserves_moves = prove
 (`!p. (wf) p /\ MEM (x,y) (state_to_list p) /\ ~(x = y) ==>
    MEM x (MAP FST (state_to_list (pmov p)))`,
  CHEAT_TAC);;

let parmove_preserves_moves = prove
 (`windmill moves /\ MEM (x,y) moves /\ ~(x = y) ==> MEM (SOME x) (MAP
  FST (parmove moves))`,
  CHEAT_TAC);;

(* mapping an injective function over compiled moves *)

let map_state_def = cake_define
  `map_state f = (let m = MAP (f ## f) in m ## m ## m)`;;

let inj_on_state_def = cake_define
  `inj_on_state f p =
      (let ls0 = state_to_list p in
      let ls = MAP FST ls0 ++ MAP SND ls0 in
      (!x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y) /\
      (!x. f x = NONE <=> x = NONE))`;;

let step_inj_on_state = prove
 (`!s1 s2. (step) s1 s2 ==> inj_on_state f s1 ==> inj_on_state f s2`,
  CHEAT_TAC);;

let steps_inj_on_state = prove
 (`!s1 s2. inj_on_state f s1 /\ (RTC (step)) s1 s2 ==> inj_on_state f
  s2`,
  CHEAT_TAC);;

let step_MAP_INJ = prove
 (`!s1 s2. (step) s1 s2 ==> inj_on_state f s1 ==> (step) (map_state f
  s1) (map_state f s2)`,
  CHEAT_TAC);;

(* [local] *)
let steps_MAP_INJ = prove
 (`!s1 s2. (RTC (step)) s1 s2 ==>
     inj_on_state f s1 ==> (RTC (step)) (map_state f s1) (map_state
       f s2)`,
  CHEAT_TAC);;

let fstep_MAP_INJ = prove
 (`!p. inj_on_state f p ==> fstep (map_state f p) = map_state f (fstep
  p)`,
  CHEAT_TAC);;

let pmov_MAP_INJ = prove
 (`!p.
   (wf) p /\ inj_on_state f p ==> pmov (map_state f p) = map_state
     f (pmov p)`,
  CHEAT_TAC);;

let parmove_MAP_INJ = prove
 (`(let ls1 = MAP FST ls ++ MAP SND ls in (!x y. MEM x ls1 /\ MEM y ls1
  /\ f x = f y ==> x = y)) /\
   windmill ls ==>
   parmove (MAP (f ## f) ls) = MAP (OPTION_MAP f ## OPTION_MAP f)
     (parmove ls)`,
  CHEAT_TAC);;
