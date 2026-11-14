(* ======================================================== *)
(*  ml_monadBase: ported from HOL4's
    translator/monadic/monad_base/ml_monadBaseScript.sml
    A definition theory, with 26 definitions, 2 datatypes and 27
    theorems.  Needed by 18 files of the port.  *)
(* ======================================================== *)

(*
  Definitions for the state-and-exception monad that is supported by the
  proof-producing monadic translator.
*)

needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_monadBase"
  ["semanticPrimitives"];;

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

let exc_INDUCT,exc_RECURSION = define_datatype
  "exc =
     M_success ('a)
   | M_failure ('b)";;

(* HOL4 ml_monadBaseScript.sml:21: the type abbreviation M, which the
   port expands *)

let liftM_def = new_definition
  `((liftM read' (write':('a->'a)->'d->'d)
  (op:'a->('b,'c)exc#'a)):'d->('b,'c)exc#'d) =
     (\state. let (ret,new) = op (read' state) in
                (ret,write' (K new) state))`;;

(* Definitions using monadic syntax *)

let st_ex_bind_def = new_definition
  `(st_ex_bind:('a->('b,'c)exc#'a)->('b->'a->('d,'c)exc#'a)->'a->('d
  ,'c)exc#'a) x f =
     (\s.
       match x s with
         (M_success y,s) -> f y s | (M_failure x,s) -> (M_failure
           x,s))`;;

let st_ex_ignore_bind_def = new_definition
  `(st_ex_ignore_bind:('a->('b,'c)exc#'a)->('a->('d,'c)exc#'a)->'a->('d
  ,'c)exc#'a) x f =
     (\s.
       match x s with
         (M_success y,s) -> f s | (M_failure x,s) -> (M_failure
           x,s))`;;


(*
 * Congruence theorems for st_ex_bind / st_ex_ignore_bind.
 * Used by TFL rewriters when deriving termination conditions.
 * Ensures that intermediate values of the monad bind (y, s'')
 * are captured.
 *)

let st_ex_ignore_bind_CONG = prove
 (`!x s x' s' f f'.
     (x = x') /\ (s = s') /\
     (!y s''. (x' s' = (M_success y,s'')) ==> (f s'' = f' s'')) ==>
       (st_ex_ignore_bind x f s =
       st_ex_ignore_bind x' f' s')`,
  CHEAT_TAC);;
(* HOL4 ml_monadBaseScript.sml:70: ML code, not ported *)

let st_ex_bind_CONG = prove
 (`!x s x' s' f f'.
     (x = x') /\ (s = s') /\
     (!y s''. (x' s' = (M_success y,s'')) ==> (f y s'' = f' y s''))
       ==> (st_ex_bind x f s = st_ex_bind x' f' s')`,
  CHEAT_TAC);;
(* HOL4 ml_monadBaseScript.sml:83: ML code, not ported *)


let st_ex_return_def = new_definition
  `(st_ex_return)
       // : α -> (β, α, γ) M
       x =
     (\s. (M_success x,s))`;;

(* HOL4 ml_monadBaseScript.sml:91: ML code, not ported *)

let otherwise_def = new_definition
  `otherwise x y =
       (\s. match ((x:'a->('b,'c)exc#'a) s) with
             (M_success y,s) -> (M_success y,s) | (M_failure e,s)
               -> (y:'a->('b,'c)exc#'a) s)`;;

let can_def = new_definition
  `can f x = (
              otherwise (st_ex_ignore_bind (f x) (st_ex_return T))
                (st_ex_return F))`;;

(* Dynamic allocation of references *)
let store_ref_INDUCT,store_ref_RECURSION = define_datatype
  "store_ref =
     StoreRef num";;

(* Arrays *)

(* Msub *)
let msub_def,msub_ind = define_shaped_rec
  "match"
  [`Msub e (n:num) l =
     (match l with
       [] -> M_failure e | CONS x l' -> (if n = 0 then M_success
         x else Msub e (n - 1) l'))`];;

(* Msub_eq *)
let msub_eq = prove
 (`!l n e. n < LENGTH l ==> (Msub e n l = M_success (EL n l))`,
  CHEAT_TAC);;

(* Msub_exn_eq *)
let msub_exn_eq = prove
 (`!l n e. n >= LENGTH l ==> (Msub e n l = M_failure e)`,
  CHEAT_TAC);;

(* Mupdate *)
let mupdate_def,mupdate_ind = define_shaped_rec
  "match"
  [`Mupdate e x (n:num) l =
     (match l with
       [] -> M_failure e | CONS x' l' ->
         (if n = 0 then
           M_success (CONS x l') else
           (match Mupdate e x (n - 1) l' with
              M_success l'' -> M_success (CONS x' l'') | other
                -> other)))`];;

(* Mupdate_eq *)
let mupdate_eq = prove
 (`!l n x e. n < LENGTH l ==> (Mupdate e x n l = M_success (LUPDATE x
  n l))`,
  CHEAT_TAC);;

(* Mupdate_exn_eq *)
let mupdate_exn_eq = prove
 (`!l n x e. n >= LENGTH l ==> (Mupdate e x n l = M_failure e)`,
  CHEAT_TAC);;

(* Array resize *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let array_resize_def,array_resize_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x0)`
  [`array_resize (n:num) x a =
     (if n = 0 then
       [] else
       match a with
         [] -> CONS x (array_resize (n - 1) x a) | CONS x' a' ->
           CONS x' (array_resize (n - 1) x a'))`];;

let array_resize_eq = prove
 (`!a n x. array_resize n x a = APPEND (TAKE n a) (REPLICATE (n -
  LENGTH a) x)`,
  CHEAT_TAC);;

(* User functions *)
let marray_length_def = new_definition
  `Marray_length get_arr =
     (\s. (M_success (LENGTH (get_arr s)),s))`;;

let marray_sub_def = new_definition
  `Marray_sub get_arr e n =
     (\s. (Msub e n (get_arr s),s))`;;

let marray_update_def = new_definition
  `Marray_update get_arr set_arr e n x =
     (\s. match Mupdate e x n (get_arr s) with
           M_success a -> (M_success one,set_arr a s) | M_failure
             e -> (M_failure e,s))`;;

let marray_alloc_def = new_definition
  `Marray_alloc set_arr n x =
     (\s. (M_success one,set_arr (REPLICATE n x) s))`;;

let marray_resize_def = new_definition
  `Marray_resize get_arr set_arr n x =
     (\s. (M_success one,set_arr (array_resize n x (get_arr s))
       s))`;;

(* Dynamic allocated references *)
let mref_def = new_definition
  `Mref cons x = (\s. (M_success (StoreRef (LENGTH s)),CONS (cons x)
  s))`;;

let dref_def = new_definition
  `dref n = (\s. EL (LENGTH s - n - 1) s)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let mdref_aux_def,mdref_aux_ind = define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`Mdref_aux e (n:num) =
     (\s. match s with
           [] -> M_failure e | CONS x s -> (if n = 0 then
             M_success x else Mdref_aux e (n - 1) s))`];;

let mdref_def = define_general
  [`Mdref e (StoreRef n) =
     (\s. (Mdref_aux e (LENGTH s - n - 1) s,s))`];;

let mpop_ref_def = new_definition
  `Mpop_ref e =
     (\(r,s). match s with CONS x s -> (r,s) | [] -> (M_failure
       e,s))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let mref_assign_aux_def,mref_assign_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x1)`
  [`Mref_assign_aux e (n:num) x =
     (\s. match s with CONS x' s ->
             (if n = 0 then
               M_success (CONS x s) else
               (match Mref_assign_aux e (n - 1) x s with
                  M_success s -> M_success (CONS x' s) | other
                    -> other)) | [] -> M_failure e)`];;

let mref_assign_def = define_general
  [`Mref_assign e (StoreRef n) x =
     (\s. match Mref_assign_aux e (LENGTH s - n - 1) x s with
           M_success s -> (M_success one,s) | M_failure e ->
             (M_failure e,s))`];;

let ref_assign_def = new_definition
  `ref_assign n x = (\s. LUPDATE x (LENGTH s - n - 1) s)`;;

let dref_cons_state = prove
 (`n < LENGTH state ==> (dref n (CONS x state) = dref n state)`,
  CHEAT_TAC);;

let dref_first = prove
 (`dref (LENGTH s) (CONS r s) = r`,
  (REWRITE_TAC[dref_def; LENGTH; ARITH_RULE `SUC n - n - 1 = 0`; EL;
    HD]));;

(* Mdref_eq *)
let mdref_eq = prove
 (`!state n.
     n < LENGTH state ==>
     (Mdref e (StoreRef n) state = (M_success (dref n
       state),state))`,
  CHEAT_TAC);;

(* Mref_assign_aux_eq *)
let mref_assign_aux_eq = prove
 (`!state e n x.
     n < LENGTH state ==>
     (Mref_assign_aux e (LENGTH state - n - 1) x state =
      M_success (ref_assign n x state))`,
  CHEAT_TAC);;

(* Mref_assign_eq *)
let mref_assign_eq = prove
 (`!state e n x.
     n < LENGTH state ==>
     (Mref_assign e (StoreRef n) x state = (M_success
       one,ref_assign n x state))`,
  CHEAT_TAC);;

let ref_bind_def = new_definition
  `ref_bind create f pop =
     (\s. match create s with
           (M_success x,s) -> pop (f x s) | (M_failure x,s) ->
             (M_failure x,s))`;;

(* TODO: use that *)
let mget_ref_def = new_definition
  `Mget_ref get_var' = (\s. (M_success (get_var' s),s))`;;

let mset_ref_def = new_definition
  `Mset_ref set_var' x = (\s. (M_success one,set_var' x s))`;;

(* Rules to deal with the monads *)
(* [local] *)
let st_ex_return_success = prove
 (`!v st r st'.
      st_ex_return v st = (r,st') <=>
      r = M_success v /\ st' = st`,
  CHEAT_TAC);;

(* [local] *)
let st_ex_bind_success = prove
 (`!f g st st' v.
      st_ex_bind f g st = (M_success v,st') <=>
      (?v' st''.
        f st = (M_success v',st'') /\
        g v' st'' = (M_success v,st'))`,
  CHEAT_TAC);;

(* [local] *)
let otherwise_success = prove
 (`(otherwise x y) s = (M_success v,s') <=>
    x s = (M_success v,s') \/
    (?e s''. x s = (M_failure e,s'') /\ y s'' = (M_success v,s'))`,
  CHEAT_TAC);;

(* [local] *)
let otherwise_failure = prove
 (`(otherwise x y) s = (M_failure e,s') <=>
    (?e' s''. x s = (M_failure e',s'') /\ y s'' = (M_failure e,s'))`,
  CHEAT_TAC);;

(* [local] *)
let otherwise_eq = prove
 (`(otherwise x y) s = (r,s') <=>
    (?v. ((x s = (M_success v,s') /\ r = M_success v) \/
          (?e s''. x s = (M_failure e,s'') /\
                   y s'' = (M_success v,s') /\
                   r = M_success v))) \/
    (?e e' s''. x s = (M_failure e',s'') /\
                y s'' = (M_failure e,s') /\
                r = M_failure e)`,
  CHEAT_TAC);;

(* [local] *)
let can_success = prove
 (`can f x s = (M_failure e,s') <=> F`,
  CHEAT_TAC);;

(* Marray_length_success[local] *)
let marray_length_success = prove
 (`!get_arr s r s'.
      Marray_length get_arr s = (r,s') <=>
      r = M_success (LENGTH (get_arr s)) /\
      s' = s`,
  CHEAT_TAC);;

(* Marray_sub_success[local] *)
let marray_sub_success = prove
 (`!get_arr e n s v s'.
      Marray_sub get_arr e n s = (M_success v,s') <=>
      n < LENGTH (get_arr s) /\ v = EL n (get_arr s) /\ s' = s`,
  CHEAT_TAC);;

(* Marray_sub_failure[local] *)
let marray_sub_failure = prove
 (`!get_arr e n s e' s'.
      Marray_sub get_arr e n s = (M_failure e',s') <=>
      n >= LENGTH (get_arr s) /\ e' = e /\ s' = s`,
  CHEAT_TAC);;

(* Marray_sub_eq[local] *)
let marray_sub_eq = prove
 (`Marray_sub get_arr e n s = (r,s') <=>
    (n < LENGTH (get_arr s) /\ s' = s /\ r = M_success (EL n (get_arr
      s))) \/
    (n >= LENGTH (get_arr s) /\ s' = s /\ r = M_failure e)`,
  CHEAT_TAC);;

(* Marray_update_success[local] *)
let marray_update_success = prove
 (`!get_arr set_arr e n x s s'.
      Marray_update get_arr set_arr e n x s = (M_success v,s') <=>
      n < LENGTH (get_arr s) /\
      v = one /\
      s' = set_arr (LUPDATE x n (get_arr s)) s`,
  CHEAT_TAC);;

(* Marray_update_failure[local] *)
let marray_update_failure = prove
 (`!get_arr set_arr e e' n x s s'.
      Marray_update get_arr set_arr e n x s = (M_failure e',s') <=>
      n >= LENGTH (get_arr s) /\
      e' = e /\
      s' = s`,
  CHEAT_TAC);;

(* Marray_update_eq[local] *)
let marray_update_eq = prove
 (`Marray_update get_arr set_arr e n x s = (r,s') <=>
    (n < LENGTH (get_arr s) /\
     s' = set_arr (LUPDATE x n (get_arr s)) s /\
     r = M_success one) \/
    (n >= LENGTH (get_arr s) /\
     s' = s /\
     r = M_failure e)`,
  CHEAT_TAC);;

(* Marray_alloc_success[local] *)
let marray_alloc_success = prove
 (`Marray_alloc set_arr n x s = (r,s') <=>
    r = M_success one /\
    s' = set_arr (REPLICATE n x) s`,
  CHEAT_TAC);;

(* HOL4 ml_monadBaseScript.sml:557-560: ML code, not ported *)
(* HOL4 ml_monadBaseScript.sml:561-562: a theorem that HOL4 states as
   the value of an ML expression: monad_eqs *)

(* Run *)
let run_def = new_definition
  `run (x:'a->('b,'c)exc#'a) state = FST (x state)`;;
