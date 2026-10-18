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
   ((\mu dn. ~MEM dn (MAP SND mu)) mu dn /\ ~(dn = s0) ==> step
    (mu,[(dn,sn)] ++ sigma ++ [(d0,s0)],tau) (mu,sigma ++
      [(d0,s0)],[(dn,sn)] ++ tau)) /\
   ((\mu dn. ~MEM dn (MAP SND mu)) mu d ==> step
    (mu,[(d,s)],tau) (mu,[],[(d,s)] ++ tau))`;;

(* HOL4 parmoveScript.sml:39: ML code, not ported *)
(* HOL4 parmoveScript.sml:40: the overload \226\150\183, which the
   port expands *)

(* HOL4 parmoveScript.sml:42: ML code, not ported *)
(* HOL4 parmoveScript.sml:43: the overload \226\150\183*, which the
   port expands *)

(* invariant on states *)

let windmill_def = cake_define
  `windmill (moves:('a#'a) list) = ALL_DISTINCT (MAP FST moves)`;;

let windmill_cons = cake_theorem "windmill_cons"
  (fun () ->
    `windmill (x :: ls) <=> ~MEM (FST x) (MAP FST ls) /\ windmill ls`)
  CHEAT_TAC;;

let path_def = cake_define_list
  [`parmove_path [] <=> T`;
   `parmove_path [_1] <=> T`;
   `parmove_path ((c,b') :: (b,a) :: p) <=>
         (b = b') /\ parmove_path ((b,a) :: p)`];;
hol4_overload "path" "parmove_path";;

let path_change_start = cake_theorem "path_change_start"
  (fun () ->
    `!y z x. parmove_path (SNOC x y) /\ FST x = FST z ==> parmove_path
  (SNOC z y)`)
  CHEAT_TAC;;

let path_tail = cake_theorem "path_tail"
  (fun () ->
    `!t h. parmove_path (h :: t) ==> parmove_path t`)
  CHEAT_TAC;;

let path_imp_mem = cake_theorem "path_imp_mem[local]"
  (fun () ->
    `parmove_path (x :: y) ==>
      ~NULL y ==> MEM (SND x) (MAP FST y)`)
  CHEAT_TAC;;

let path_imp_mem2 = cake_theorem "path_imp_mem2[local]"
  (fun () ->
    `parmove_path x ==>
      (!y. MEM y (MAP SND x) /\ ~(
          y = SND (LAST x)) ==>
          MEM y (MAP FST x))`)
  CHEAT_TAC;;

let NoRead_path = cake_theorem "NoRead_path[local]"
  (fun () ->
    `!sigma. parmove_path sigma /\ windmill sigma /\ LENGTH sigma >= 2
  /\ ~(
      FST (HD sigma) = SND (LAST sigma)) ==>
      (\mu dn. ~MEM dn (MAP SND mu)) (TL sigma) (FST (HD sigma))`)
  CHEAT_TAC;;

let wf_def = cake_define
  `parmove_wf (mu,sigma,tau) <=>
     windmill (mu ++ sigma) /\
     EVERY IS_SOME (MAP FST mu) /\
     EVERY IS_SOME (MAP SND mu) /\
     (~NULL sigma ==> EVERY IS_SOME (MAP SND (FRONT sigma))) /\
     EVERY IS_SOME (MAP FST sigma) /\
     parmove_path sigma`;;
hol4_overload "wf" "parmove_wf";;
(* HOL4 parmoveScript.sml:129: the overload ⊢, which the port expands *)

(* HOL4 parmoveScript.sml:131-138: a theorem whose statement the port
   cannot state yet *)

(* The invariant is preserved *)

(* HOL4 parmoveScript.sml:142-150: a theorem whose statement the port
   cannot state yet *)

(* HOL4 parmoveScript.sml:152-157: a theorem whose statement the port
   cannot state yet *)

(* semantics of moves *)

let parsem_def = cake_define
  `parsem mu rho = UPDATE_LIST rho (ZIP (MAP FST mu) (MAP (rho o SND)
  mu))`;;

let parsem_nil = cake_theorem "parsem_nil[simp]"
  (fun () ->
    `parsem [] = I`)
  CHEAT_TAC;;

let parsem_cons = cake_theorem "parsem_cons"
  (fun () ->
    `~MEM x (MAP FST mu) ==>
     parsem ((x,y) :: mu) rho = (x =+ rho y) (parsem mu rho)`)
  CHEAT_TAC;;

let independence = cake_theorem "independence"
  (fun () ->
    `!mu1 s d mu2 mu.
        windmill mu /\ mu = mu1 ++ [(d,s)] ++ mu2 ==>
        parsem mu = parsem ([(d,s)] ++ mu1 ++ mu2)`)
  CHEAT_TAC;;

let parsem_perm = cake_theorem "parsem_perm"
  (fun () ->
    `windmill l1 /\ PERM l1 l2 ==> parsem l1 = parsem l2`)
  CHEAT_TAC;;

let parsem_untouched = cake_theorem "parsem_untouched"
  (fun () ->
    `!rho mu x. windmill mu /\ ~MEM x (MAP FST mu) ==> parsem mu rho x
  = rho x`)
  CHEAT_TAC;;

let parsem_change_env = cake_theorem "parsem_change_env"
  (fun () ->
    `(~MEM x (MAP FST mu) ==> rho1 x = rho2 x) /\
     MAP (rho1 o SND) mu = MAP (rho2 o SND) mu ==>
     parsem mu rho1 x = parsem mu rho2 x`)
  CHEAT_TAC;;

let parsem_NoRead = cake_theorem "parsem_NoRead"
  (fun () ->
    `(\mu dn. ~MEM dn (MAP SND mu)) mu x ==>
     parsem ((x,y) :: mu) rho = parsem mu ((x =+ rho y) rho)`)
  CHEAT_TAC;;

let parsem_MAP_INJ = cake_theorem "parsem_MAP_INJ"
  (fun () ->
    `!ms. windmill ms /\
          INJ f (set_of_list (MAP FST ms ++ MAP SND ms)) UNIV ==>
          (!x. MEM x (MAP FST ms) ==> parsem (MAP (f ## f) ms) r
            (f x) = parsem ms (r o f) x)`)
  CHEAT_TAC;;

let seqsem_def = cake_define_list
  [`seqsem [] rho = rho`;
   `seqsem ((d,s) :: tau) rho = seqsem tau ((d =+ rho s) rho)`];;

(* HOL4 parmoveScript.sml:323: ML code, not ported *)

let seqsem_append = cake_theorem "seqsem_append"
  (fun () ->
    `!l1 l2. seqsem (l1 ++ l2) = seqsem l2 o seqsem l1`)
  CHEAT_TAC;;

let seqsem_move_unchanged = cake_theorem "seqsem_move_unchanged"
  (fun () ->
    `!ms r. ~MEM k (MAP FST ms) ==> seqsem ms r k = r k`)
  CHEAT_TAC;;

(* semantics of the state *)

let sem_def = cake_define
  `sem (mu,sigma,tau) rho = parsem (mu ++ sigma) (seqsem (REVERSE
  tau) rho)`;;

let sem_init = cake_theorem "sem_init"
  (fun () ->
    `sem (mu,[],[]) = parsem mu`)
  CHEAT_TAC;;

let sem_final = cake_theorem "sem_final"
  (fun () ->
    `sem ([],[],tau) = seqsem (REVERSE tau)`)
  CHEAT_TAC;;

(* semantic preservation *)

let eqenv_def = cake_define
  `eqenv rho1 rho2 <=> (!r. IS_SOME r ==> (rho1 r = rho2 r))`;;
(* HOL4 parmoveScript.sml:361: ML code, not ported *)
(* HOL4 parmoveScript.sml:362: the overload \226\137\161, which the
   port expands *)

let eqenv_sym = cake_theorem "eqenv_sym[local]"
  (fun () ->
    `≡
       p1 p2 ==> ≡ p2 p1`)
  CHEAT_TAC;;

(* HOL4 parmoveScript.sml:370-445: a theorem whose statement the port
   cannot state yet *)

(* HOL4 parmoveScript.sml:447-457: a theorem whose statement the port
   cannot state yet *)

let steps_correct = cake_theorem "steps_correct"
  (fun () ->
    `windmill mu /\
     EVERY IS_SOME (MAP FST mu) /\
     EVERY IS_SOME (MAP SND mu) /\ ▷*
     (mu,[],[]) ([],[],tau) ==>
     (!rho. ≡ (parsem mu rho) (seqsem (REVERSE tau) rho))`)
  CHEAT_TAC;;

(* deterministic algorithm *)

(* HOL4 parmoveScript.sml:476: ML code, not ported *)

let dstep_rules = cake_inductive
  `(dstep ([(r,r)] ++ mu,[],tau) (mu,[],tau)) /\
   (~(s = d) ==> dstep
    ([(d,s)] ++ mu,[],tau) (mu,[(d,s)],tau)) /\
   ((\mu dn. ~MEM dn (MAP SND mu)) mu1 d ==> dstep
    (mu1 ++ [(r,d)] ++ mu2,[(d,s)] ++ sigma,tau)
    (mu1 ++ mu2,[(r,d); (d,s)] ++ sigma,tau)) /\
   ((\mu dn. ~MEM dn (MAP SND mu)) mu r ==> dstep
    (mu,[(r,s)] ++ sigma ++ [(d,r)],tau)
    (mu,sigma ++ [(d,NONE)],[(r,s); (NONE,r)] ++ tau)) /\
   ((\mu dn. ~MEM dn (MAP SND mu)) mu dn /\ ~(dn = s0) ==> dstep
    (mu,[(dn,sn)] ++ sigma ++ [(d0,s0)],tau)
    (mu,sigma ++ [(d0,s0)],[(dn,sn)] ++ tau)) /\
   ((\mu dn. ~MEM dn (MAP SND mu)) mu d ==> dstep
    (mu,[(d,s)],tau) (mu,[],[(d,s)] ++ tau))`;;

(* HOL4 parmoveScript.sml:494: ML code, not ported *)
(* HOL4 parmoveScript.sml:495: the overload \226\134\170, which the
   port expands *)

(* HOL4 parmoveScript.sml:497: ML code, not ported *)
(* HOL4 parmoveScript.sml:498: the overload \226\134\170*, which the
   port expands *)

(* ⊢ s1 condition not included in paper;
   not sure if necessary, but couldn't get
   their proof to work *)
(* HOL4 parmoveScript.sml:503-515: a theorem whose statement the port
   cannot state yet *)

(* HOL4 parmoveScript.sml:517-522: a theorem whose statement the port
   cannot state yet *)

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

let fstep_dstep = cake_theorem "fstep_dstep"
  (fun () ->
    `(!tau. ~(s = ([],[],tau))) ==> ↪ s (fstep s)`)
  CHEAT_TAC;;

(* HOL4 parmoveScript.sml:610-638: the tactic that proves the
   termination *)
let pmov_def = cake_define_wf
  `MEASURE (\(mu,sigma,tau). 2 * LENGTH mu + LENGTH sigma)`
  `pmov s = (match s with ([],[],_3) -> s | _4 -> pmov (fstep s))`;;

(* HOL4 parmoveScript.sml:640: ML code, not ported *)

let pmov_dsteps = cake_theorem "pmov_dsteps"
  (fun () ->
    `!s. ↪* s (pmov s)`)
  CHEAT_TAC;;

let pmov_final = cake_theorem "pmov_final"
  (fun () ->
    `!s. ?tau. pmov s = ([],[],tau)`)
  CHEAT_TAC;;

(* The top-level parallel move compiler *)

let parmove_def = cake_define
  `parmove (xs:('a#'a) list) =
     REVERSE (SND (SND (pmov (MAP (\(x,y). (SOME x,SOME y))
       xs,[],[]))))`;;

let parmove_correct = cake_theorem "parmove_correct"
  (fun () ->
    `windmill xs ==>
     (!rho. ≡ (seqsem (parmove xs) rho)
         (parsem (MAP (\(x,y). (SOME x,SOME y)) xs) rho))`)
  CHEAT_TAC;;

(* the compiler does not invent new moves *)

let MEM_MAP_FST_SND_SND_pmov = cake_theorem "MEM_MAP_FST_SND_SND_pmov"
  (fun () ->
    `!p x.
      MEM (SOME x) (MAP FST (SND (SND (pmov p)))) ==>
      MEM (SOME x) (MAP FST (FST p ++ FST (SND p) ++ SND (SND
        p)))`)
  CHEAT_TAC;;

let MEM_MAP_FST_parmove = cake_theorem "MEM_MAP_FST_parmove"
  (fun () ->
    `MEM (SOME x) (MAP FST (parmove mvs)) ==> MEM x (MAP FST mvs)`)
  CHEAT_TAC;;

let MEM_MAP_SND_SND_SND_pmov = cake_theorem "MEM_MAP_SND_SND_SND_pmov"
  (fun () ->
    `!p x.
      MEM (SOME x) (MAP SND (SND (SND (pmov p)))) ==>
      MEM (SOME x) (MAP SND (FST p ++ FST (SND p) ++ SND (SND
        p)))`)
  CHEAT_TAC;;

let MEM_MAP_SND_parmove = cake_theorem "MEM_MAP_SND_parmove"
  (fun () ->
    `MEM (SOME x) (MAP SND (parmove mvs)) ==> MEM x (MAP SND mvs)`)
  CHEAT_TAC;;

(* the compiler does not use uninitialised temporaries *)

let not_use_temp_before_assign_def = cake_define
  `not_use_temp_before_assign x1 =
        match x1 with
          [] -> T
        | ((d,NONE) :: ls) -> F
        | ((NONE,s) :: ls) -> T
        | ((d,s) :: ls) -> not_use_temp_before_assign ls`;;

let not_use_temp_before_assign_append =
  cake_theorem "not_use_temp_before_assign_append"
  (fun () ->
    `!l1 l2.
     (not_use_temp_before_assign (l1 ++ l2) <=>
      not_use_temp_before_assign l1 /\
      (EVERY IS_SOME (MAP FST l1) ==> not_use_temp_before_assign
        l2))`)
  CHEAT_TAC;;

let not_use_temp_before_assign_insert =
  cake_theorem "not_use_temp_before_assign_insert"
  (fun () ->
    `!l1 l2.
     not_use_temp_before_assign (l1 ++ l2) ==>
     not_use_temp_before_assign (l1 ++ [(SOME x,SOME y)] ++ l2)`)
  CHEAT_TAC;;

let not_use_temp_before_assign_thm =
  cake_theorem "not_use_temp_before_assign_thm"
  (fun () ->
    `!ls. not_use_temp_before_assign ls =
      (!i. find_index NONE (MAP SND ls) 0 = SOME i ==>
        (?j. find_index NONE (MAP FST ls) 0 = SOME j /\ j < i))`)
  CHEAT_TAC;;

(* HOL4 parmoveScript.sml:880-906: a theorem whose statement the port
   cannot state yet *)

(* HOL4 parmoveScript.sml:908-918: a theorem whose statement the port
   cannot state yet *)

(* HOL4 parmoveScript.sml:920-930: a theorem whose statement the port
   cannot state yet *)

let parmove_not_use_temp_before_assign =
  cake_theorem "parmove_not_use_temp_before_assign"
  (fun () ->
    `windmill mvs ==>
     (match find_index NONE (MAP SND (parmove mvs)) 0 with
        NONE -> T | SOME i ->
        (match find_index NONE (MAP FST (parmove mvs)) 0 with
          NONE -> F | SOME j -> ~(i <= j)))`)
  CHEAT_TAC;;

(* the compiler preserves all-distinct variables *)

let ALL_DISTINCT_step = cake_theorem "ALL_DISTINCT_step"
  (fun () ->
    `!s1 s2. ▷ s1 s2 ==>
      ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1)
        ++ (SND (SND s1))))) ==>
      ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s2 ++ FST (SND
        s2) ++ (SND (SND s2)))))`)
  CHEAT_TAC;;

let ALL_DISTINCT_steps = cake_theorem "ALL_DISTINCT_steps"
  (fun () ->
    `!s1 s2.
      (\s1. ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST
        (SND s1) ++ (SND (SND s1)))))) s1 /\ ▷*
      s1 s2 ==>
      (\s1. ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST
        (SND s1) ++ (SND (SND s1)))))) s2`)
  CHEAT_TAC;;

(* HOL4 parmoveScript.sml:991-1001: a theorem whose statement the
   port cannot state yet *)

let ALL_DISTINCT_parmove = cake_theorem "ALL_DISTINCT_parmove"
  (fun () ->
    `ALL_DISTINCT (MAP FST mvs) ==>
     ALL_DISTINCT (FILTER IS_SOME (MAP FST (parmove mvs)))`)
  CHEAT_TAC;;

(* the compiler retains all non-trivial moves *)

let state_to_list_def = cake_define
  `state_to_list p = APPEND (FST p) (FST (SND p)) ++ SND (SND p)`;;

let step_preserves_moves = cake_theorem "step_preserves_moves"
  (fun () ->
    `!s1 s2. ▷ s1 s2 ==>
      (!x. (?y. MEM (x,y) (state_to_list s1) /\ ~(x = y)) ==>
          (?y. MEM (x,y) (state_to_list s2) /\ ~(x = y)))`)
  CHEAT_TAC;;

let steps_preserves_moves = cake_theorem "steps_preserves_moves"
  (fun () ->
    `!s1 s2.
      (\s1. (?y. MEM (x,y) (state_to_list s1) /\ ~(x = y))) s1 /\
        ▷*
      s1 s2 ==>
      (\s1. (?y. MEM (x,y) (state_to_list s1) /\ ~(x = y))) s2`)
  CHEAT_TAC;;

(* HOL4 parmoveScript.sml:1050-1061: a theorem whose statement the
   port cannot state yet *)

let parmove_preserves_moves = cake_theorem "parmove_preserves_moves"
  (fun () ->
    `windmill moves /\ MEM (x,y) moves /\ ~(x = y) ==> MEM (SOME x)
  (MAP FST (parmove moves))`)
  CHEAT_TAC;;

(* mapping an injective function over compiled moves *)

let map_state_def = cake_define
  `map_state f = (let m = MAP (f ## f) in m ## m ## m)`;;

let inj_on_state_def = cake_define
  `inj_on_state f p =
      (let ls0 = state_to_list p in
      let ls = MAP FST ls0 ++ MAP SND ls0 in
      (!x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y) /\
      (!x. f x = NONE <=> x = NONE))`;;

let step_inj_on_state = cake_theorem "step_inj_on_state"
  (fun () ->
    `!s1 s2. ▷ s1 s2 ==> inj_on_state f s1 ==> inj_on_state f s2`)
  CHEAT_TAC;;

let steps_inj_on_state = cake_theorem "steps_inj_on_state"
  (fun () ->
    `!s1 s2. inj_on_state f s1 /\ ▷* s1 s2 ==> inj_on_state f s2`)
  CHEAT_TAC;;

let step_MAP_INJ = cake_theorem "step_MAP_INJ"
  (fun () ->
    `!s1 s2. ▷ s1 s2 ==> inj_on_state f s1 ==> ▷ (map_state f s1)
  (map_state f s2)`)
  CHEAT_TAC;;

let steps_MAP_INJ = cake_theorem "steps_MAP_INJ[local]"
  (fun () ->
    `!s1 s2. ▷* s1 s2 ==>
       inj_on_state f s1 ==> ▷*
       (map_state f s1) (map_state f s2)`)
  CHEAT_TAC;;

let fstep_MAP_INJ = cake_theorem "fstep_MAP_INJ"
  (fun () ->
    `!p. inj_on_state f p ==> fstep (map_state f p) = map_state f
  (fstep p)`)
  CHEAT_TAC;;

(* HOL4 parmoveScript.sml:1257-1292: a theorem whose statement the
   port cannot state yet *)

let parmove_MAP_INJ = cake_theorem "parmove_MAP_INJ"
  (fun () ->
    `(let ls1 = MAP FST ls ++ MAP SND ls in (!x y. MEM x ls1 /\ MEM y
  ls1 /\ f x = f y ==> x = y)) /\
     windmill ls ==>
     parmove (MAP (f ## f) ls) = MAP (OPTION_MAP f ## OPTION_MAP
       f) (parmove ls)`)
  CHEAT_TAC;;
