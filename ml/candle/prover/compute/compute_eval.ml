(* ======================================================== *)
(*  compute_eval: ported from HOL4's
    candle/prover/compute/compute_evalScript.sml
    A definition theory, with 23 definitions and 10 theorems.
    Needed by candle_kernelProg.ml, compute.ml, computeProof.ml,
    compute_evalProof.ml, compute_exec.ml and compute_execProof.ml.  *)
(* ======================================================== *)

(*
   Interpreter function for the Candle compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "lib/errorMonad.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compute_eval"
  ["compute_syntax"; "holKernel"; "holKernelProof"; "holSyntax";
   "holSyntaxExtra"; "holSyntaxLib"; "ml_monadBase"];;

(* -------------------------------------------------------------------------
 * st_ex_monad setup
 * ------------------------------------------------------------------------- *)

(* HOL4 compute_evalScript.sml:18-25: ML code, not ported *)

(* HOL4 compute_evalScript.sml:31: the overload return, which the port
   expands *)
(* HOL4 compute_evalScript.sml:32: the overload failwith, which the port
   expands *)
(* HOL4 compute_evalScript.sml:33: the overload handle, which the port
   expands *)
(* HOL4 compute_evalScript.sml:34: the overload error, which the port
   expands *)
(* HOL4 compute_evalScript.sml:35: the overload timeout, which the port
   expands *)

(* -------------------------------------------------------------------------
 * Destructuring
 * ------------------------------------------------------------------------- *)

let dest_num_def,dest_num_ind = define_guess
  `compute_eval_dest_num tm =
     match tm with
       holSyntax_Const n t -> if tm = (holSyntax_Const (implode "_0")
         (holSyntax_Tyapp (implode "num") [])) then SOME 0 else NONE
     | holSyntax_Comb (holSyntax_Const nm t) r ->
         (match compute_eval_dest_num r with NONE -> NONE
         | SOME n -> if holSyntax_Const nm t = (holSyntax_Const (implode
           "BIT0") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
           (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
           "num") []))) then SOME (2 * n)
                     else if holSyntax_Const nm t = (holSyntax_Const
                       (implode "BIT1") ((\s t. holSyntax_Tyapp (implode "fun")
                       [s; t]) (holSyntax_Tyapp (implode "num") [])
                       (holSyntax_Tyapp (implode "num") []))) then SOME (2 * n
                       + 1)
                     else NONE)
     | _ -> NONE`;;

let dest_numeral_def,dest_numeral_ind = define_guess
  `dest_numeral tm =
     match tm with
       holSyntax_Comb (holSyntax_Const n t) r ->
         if holSyntax_Const n t = (holSyntax_Const (implode "NUMERAL") ((\s
           t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
           "num") []) (holSyntax_Tyapp (implode "num") []))) then
           match compute_eval_dest_num r with NONE -> failwith (implode
             "dest_numeral")
           | SOME n -> st_ex_return n
         else failwith (implode "dest_numeral")
     | _ -> failwith (implode "dest_numeral")`;;

let dest_numeral_opt_def = new_definition
  `dest_numeral_opt tm =
     match tm with
       holSyntax_Comb (holSyntax_Const n t) r ->
         if holSyntax_Const n t = (holSyntax_Const (implode "NUMERAL") ((\s
           t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
           "num") []) (holSyntax_Tyapp (implode "num") []))) then
           match compute_eval_dest_num r with NONE -> NONE
           | SOME n -> SOME n
         else NONE
     | _ -> NONE`;;

let dest_binary_def,dest_binary_ind = define_guess
  `dest_binary tm' tm =
     match tm with
       holSyntax_Comb (holSyntax_Comb (holSyntax_Const n t) l) r ->
         if tm' = holSyntax_Const n t then st_ex_return (l,r)
         else failwith (implode "dest_binary")
     | _ -> failwith (implode "dest_binary")`;;

let list_dest_comb_def,list_dest_comb_ind = define_guess
  `list_dest_comb sofar tm =
   match tm with
     holSyntax_Comb f x -> list_dest_comb (CONS x sofar) f
   | tm -> CONS tm sofar`;;

let list_dest_comb_not_nil = prove
 (`!sofar tm. ~(list_dest_comb sofar tm = [])`,
  CHEAT_TAC);;
add_simp list_dest_comb_not_nil;;

let list_dest_comb_folds_back = prove
 (`!sofar tm h t.
     list_dest_comb sofar tm = CONS h t ==>
       (?xs. t = APPEND xs sofar /\
            FOLDL holSyntax_Comb h xs = tm)`,
  CHEAT_TAC);;

let term_size_alt_def,term_size_alt_ind = define_guess
  `term_size_alt x1 =
   match x1 with
     holSyntax_Comb s t -> term_size_alt s + term_size_alt t
   | holSyntax_Abs s t -> term_size_alt s + term_size_alt t
   | _ -> 1`;;

let list_term_size_alt_def,list_term_size_alt_ind = define_guess
  `(list_term_size_alt [] = 0) /\
   (list_term_size_alt (CONS x xs) = term_size_alt x + list_term_size_alt
    xs)`;;

(* [local] *)
let list_dest_comb_term_size = prove
 (`!sofar tm res.
     list_dest_comb sofar tm = res ==>
       list_term_size_alt res = list_term_size_alt sofar + term_size_alt
         tm`,
  CHEAT_TAC);;

(* [local] *)
let list_term_size_MEM = prove
 (`MEM x xs ==> term_size_alt x <= list_term_size_alt xs`,
  CHEAT_TAC);;

let mapOption_def,mapOption_ind = define_guess
  `(mapOption f [] = SOME []) /\
   (mapOption f (CONS x xs) =
      match f x with NONE -> NONE
      | SOME y ->
          (match mapOption f xs with NONE -> NONE
          | SOME ys -> SOME (CONS y ys)))`;;

(* [defncong] *)
let mapOption_CONG = prove
 (`!xs ys f g.
     xs = ys /\
     (!x. MEM x xs ==> f x = g x) ==>
       mapOption f xs = mapOption g ys`,
  CHEAT_TAC);;

let mapOption_LENGTH = prove
 (`!xs ys. mapOption f xs = SOME ys ==> LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE term_size_alt
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 compute_evalScript.sml:241-252: the tactic that proves the
   termination *)
let dest_cexp_def,dest_cexp_ind = define_guess
  `dest_cexp tm =
     match list_dest_comb [] tm with [holSyntax_Var n ty] -> if ty =
       (holSyntax_Tyapp (implode "cval") []) then SOME (compute_syntax_Var n)
       else NONE
     | CONS (holSyntax_Const n ty) args ->
         (if holSyntax_Const n ty = (holSyntax_Const (implode "LET") ((\s t.
           holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
           (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
           (holSyntax_Tyapp (implode "cval") [])) (ast_Fun (holSyntax_Tyapp
           (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) then
            (match args with [holSyntax_Abs (holSyntax_Var s ty) y; x] ->
                 if ty = (holSyntax_Tyapp (implode "cval") []) then
                   match dest_cexp x with NONE -> NONE
                   | SOME p ->
                       (match dest_cexp y with NONE -> NONE
                       | SOME q -> SOME (compute_syntax_Let s p q))
                 else NONE
             | _ -> NONE)
          else let vs = MAP dest_cexp args in
            match vs with [arg] ->
                if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_num") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
                  (implode "cval") []))) then
                  match dest_numeral_opt (HD args) with NONE -> NONE
                  | SOME n -> SOME ((holSyntax_Tyapp (implode "num") []) n)
                else if ty = (\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") []) then
                  match arg with NONE -> NONE
                  | SOME cv ->
                    if holSyntax_Const n ty = (holSyntax_Const (implode
                      "Cexp_fst") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                      t]) (holSyntax_Tyapp (implode "cval") [])
                      (holSyntax_Tyapp (implode "cval") []))) then
                      SOME (compute_syntax_Uop Fst cv)
                    else if holSyntax_Const n ty = (holSyntax_Const (implode
                      "Cexp_snd") ((\s t. holSyntax_Tyapp (implode "fun") [s;
                      t]) (holSyntax_Tyapp (implode "cval") [])
                      (holSyntax_Tyapp (implode "cval") []))) then
                      SOME (compute_syntax_Uop Snd cv)
                    else if holSyntax_Const n ty = (holSyntax_Const (implode
                      "Cexp_ispair") ((\s t. holSyntax_Tyapp (implode "fun")
                      [s; t]) (holSyntax_Tyapp (implode "cval") [])
                      (holSyntax_Tyapp (implode "cval") []))) then
                      SOME (compute_syntax_Uop Ispair cv)
                    else SOME (compute_syntax_App n [cv])
                else NONE
            | [SOME p; SOME q] ->
                if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_pair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Pair p q)
                else if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_add") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Binop compute_syntax_Add p q)
                else if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_sub") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Binop compute_syntax_Sub p q)
                else if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_mul") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Binop compute_syntax_Mul p q)
                else if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_div") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Binop compute_syntax_Div p q)
                else if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_mod") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Binop compute_syntax_Mod p q)
                else if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_less") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Binop compute_syntax_Less p q)
                else if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_eq") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])))) then
                  SOME (compute_syntax_Binop compute_syntax_Eq p q)
                else if ty = (\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") [])) then
                  SOME (compute_syntax_App n [p; q])
                else NONE
            | [SOME p; SOME q; SOME r] ->
                if holSyntax_Const n ty = (holSyntax_Const (implode
                  "Cexp_if") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") []))))) then
                  SOME (compute_syntax_If p q r)
                else if ty = (\s t. holSyntax_Tyapp (implode "fun") [s; t])
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (ast_Fun
                  (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
                  (implode "cval") []))) then
                  SOME (compute_syntax_App n [p; q; r])
                else NONE
            | args ->
                (match mapOption I args with NONE -> NONE
                | SOME cvs ->
                    if ty = app_type (LENGTH cvs) then
                      SOME (compute_syntax_App n cvs)
                    else NONE))
     | _ -> NONE`;;

(* TODO use term_size and list_size as measure instead *)

let compute_eval_do_arith_def = new_definition
  `compute_eval_do_arith opn x2 x3 =
   match (x2,x3) with
     (compute_syntax_Num m,compute_syntax_Num n) -> st_ex_return
       ((holSyntax_Tyapp (implode "num") []) (opn m n))
   | ((holSyntax_Tyapp (implode "num") []) m,_) -> st_ex_return
     ((holSyntax_Tyapp (implode "num") []) (opn m (&0)))
   | (_,(holSyntax_Tyapp (implode "num") []) n) -> st_ex_return
     ((holSyntax_Tyapp (implode "num") []) (opn (&0) n))
   | (_,_) -> st_ex_return ((holSyntax_Tyapp (implode "num") []) (&0))`;;

let do_reln_def = new_definition
  `do_reln opn x2' x3' =
   match (x2',x3') with
     (compute_syntax_Num m,compute_syntax_Num n) -> st_ex_return
       ((holSyntax_Tyapp (implode "num") []) (if opn m n then SUC (&0) else
       (&0)))
   | (_,_) -> st_ex_return ((holSyntax_Tyapp (implode "num") []) (&0))`;;

let compute_eval_do_eq_def = new_definition
  `compute_eval_do_eq p q = st_ex_return ((holSyntax_Tyapp (implode "num")
  []) (if p = q then SUC (&0) else (&0)))`;;

let do_binop_def = define_cases
  `(do_binop compute_syntax_Add p q = compute_eval_do_arith (+) p q) /\
   (do_binop compute_syntax_Sub p q = compute_eval_do_arith (-) p q) /\
   (do_binop compute_syntax_Mul p q = compute_eval_do_arith (*) p q) /\
   (do_binop compute_syntax_Div p q = compute_eval_do_arith SAFEDIV p q) /\
   (do_binop compute_syntax_Mod p q = compute_eval_do_arith SAFEMOD p q) /\
   (do_binop compute_syntax_Less p q = do_reln (<) p q) /\
   (do_binop compute_syntax_Eq p q = compute_eval_do_eq p q)`;;

let do_fst_def = new_definition
  `do_fst x1 =
   match x1 with
     compute_syntax_Pair p q -> st_ex_return p
   | _ -> st_ex_return ((holSyntax_Tyapp (implode "num") []) (&0))`;;

let do_snd_def = new_definition
  `do_snd x1' =
   match x1' with
     compute_syntax_Pair p q -> st_ex_return q
   | _ -> st_ex_return ((holSyntax_Tyapp (implode "num") []) (&0))`;;

let do_ispair_def = new_definition
  `do_ispair x1'' =
   match x1'' with
     compute_syntax_Pair p q -> st_ex_return ((holSyntax_Tyapp (implode
       "num") []) (&1))
   | _ -> st_ex_return ((holSyntax_Tyapp (implode "num") []) (&0))`;;

let do_uop_def = define_cases
  `(do_uop Fst p = do_fst p) /\
   (do_uop Snd p = do_snd p) /\
   (do_uop Ispair p = do_ispair p)`;;

let compute_eval_map_def,compute_eval_map_ind = define_guess
  `(compute_eval_map f [] = st_ex_return []) /\
   (compute_eval_map f (CONS x xs) =
      st_ex_bind (f x) (\y. st_ex_bind (compute_eval_map f xs) (\ys.
         st_ex_return (CONS y ys))))`;;

(* [defncong] *)
let map_CONG = prove
 (`!xs ys f g.
     xs = ys /\
     (!x. MEM x xs ==> f x = g x) ==>
       compute_eval_map f xs = compute_eval_map g ys`,
  CHEAT_TAC);;

let map_LENGTH = prove
 (`!xs f ys s s'.
     compute_eval_map f xs s = (M_success ys,s') ==>
       LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;

let map_thm = prove
 (`!xs f ys s s'.
     compute_eval_map f xs s = (M_success ys,s') ==>
       LENGTH xs = LENGTH ys /\
       (!n. n < LENGTH xs ==> (?r r'. f (EL n xs) r = (M_success (EL n
         ys),r')))`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * Interpreter for compute values
 * ------------------------------------------------------------------------- *)

let check_def = new_definition
  `compute_eval_check P = if P then st_ex_return one else (raise_Failure
  (implode "error"))`;;

let compute_eval_option_def = new_definition
  `compute_eval_option f x = match f x with SOME r -> st_ex_return r | _ ->
  (raise_Failure (implode "error"))`;;

(* the clauses in two quotations: n is mlstring and num, which one quotation
   cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (compute_exp_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let subst_def,subst_ind = define_guess_clauses
  [`(compute_eval_subst env (compute_syntax_Var n) =
      (match ALOOKUP env n with NONE -> (compute_syntax_Var n:compute_exp)
       | SOME cv -> cv)) /\
    (compute_eval_subst env (compute_syntax_Pair p q) = compute_syntax_Pair
    (compute_eval_subst env p) (compute_eval_subst env q)) /\
    (compute_eval_subst env (compute_syntax_Uop uop p) = compute_syntax_Uop
    uop (compute_eval_subst env p)) /\
    (compute_eval_subst env (compute_syntax_Binop bop p q) =
    compute_syntax_Binop bop (compute_eval_subst env p) (compute_eval_subst
    env q)) /\
    (compute_eval_subst env (compute_syntax_App f cs) = compute_syntax_App f
    (MAP (compute_eval_subst env) cs)) /\
    (compute_eval_subst env (compute_syntax_If p q r) = compute_syntax_If
    (compute_eval_subst env p) (compute_eval_subst env q)
    (compute_eval_subst env r)) /\
    (compute_eval_subst env (compute_syntax_Let s x y) = compute_syntax_Let s
    (compute_eval_subst env x)
                              (compute_eval_subst (FILTER (\(n,x). ~(n
                                  = s)) env) y))`;
   `compute_eval_subst env (compute_syntax_Num n) = ((holSyntax_Tyapp
    (implode "num") []) n:compute_exp)`];;

let subst_empty = prove
 (`compute_eval_subst [] x = x`,
  CHEAT_TAC);;
add_simp subst_empty;;

(* the termination relation that HOL4 gives is
     inv_image ((<) LEX (<))
                     (\x. match x with INL (ck,_,cv) -> (ck,compute_exp_size
                       cv)
                                  | INR (ck,_,cv) -> (ck,list_size
                                    compute_exp_size cv))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let compute_eval_def,compute_eval_ind = define_guess
  `(compute_eval ck ceqs (compute_syntax_Var s) = (raise_Failure (implode
    "error"))) /\
   (compute_eval ck ceqs (compute_syntax_Num n) = st_ex_return
    (((holSyntax_Tyapp (implode "num") []) n:compute_exp))) /\
   (compute_eval ck ceqs (compute_syntax_Pair p q) =
      st_ex_bind (compute_eval ck ceqs p) (\x. st_ex_bind (compute_eval ck
          ceqs q) (\y.
        st_ex_return (compute_syntax_Pair x y)))) /\
   (compute_eval ck ceqs (compute_syntax_Uop uop p) =
      st_ex_bind (compute_eval ck ceqs p) (\x.
         do_uop uop x)) /\
   (compute_eval ck ceqs (compute_syntax_Binop bop p q) =
      st_ex_bind (compute_eval ck ceqs p) (\x. st_ex_bind (compute_eval ck
          ceqs q) (\y.
        do_binop bop x y))) /\
   (compute_eval ck ceqs (compute_syntax_App f cs) =
      (if ck = 0 then (raise_Failure (implode "timeout")) else st_ex_bind
          (compute_eval_option (ALOOKUP ceqs) f) (\(args,exp).
          st_ex_ignore_bind (compute_eval_check (LENGTH args = LENGTH cs))
              (st_ex_bind (compute_eval_list ck ceqs cs) (\cs.
          compute_eval (ck - 1) ceqs (compute_eval_subst (ZIP args cs)
              exp)))))) /\
   (compute_eval ck ceqs (compute_syntax_If p q r) =
      st_ex_bind (compute_eval ck ceqs p) (\x.
        match x with (holSyntax_Tyapp (implode "num") []) (&0) ->
            compute_eval ck ceqs r
        | (holSyntax_Tyapp (implode "num") []) _ -> compute_eval ck ceqs q
        | compute_syntax_Pair _ _ -> compute_eval ck ceqs r
        | _ -> (raise_Failure (implode "error")))) /\
   (compute_eval ck ceqs (compute_syntax_Let s p q) =
      (if ck = 0 then (raise_Failure (implode "timeout")) else st_ex_bind
          (compute_eval ck ceqs p) (\x.
          compute_eval (ck - 1) ceqs (compute_eval_subst [s,x] q)))) /\
   (compute_eval_list ck ceqs [] = st_ex_return []) /\
   (compute_eval_list ck ceqs (CONS c cs) =
      st_ex_bind (compute_eval ck ceqs c) (\x. st_ex_bind
          (compute_eval_list ck ceqs cs) (\xs.
        st_ex_return (CONS x xs))))`;;

(* Let and App cases are modified below to get a more useful ind theorem *)
(* the termination relation that HOL4 gives is
     inv_image ((<) LEX (<))
                     (\x. match x with INL (ck,_,cv) -> (ck,compute_exp_size
                       cv)
                                  | INR (ck,_,cv) -> (ck,list_size
                                    compute_exp_size cv))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let compute_eval_ind_def,compute_eval_ind_ind = define_guess
  `(compute_eval_ind ck ceqs (compute_syntax_Var s) = (raise_Failure
    (implode "error"))) /\
   (compute_eval_ind ck ceqs (compute_syntax_Num n) = st_ex_return
    (((holSyntax_Tyapp (implode "num") []) n:compute_exp))) /\
   (compute_eval_ind ck ceqs (compute_syntax_Pair p q) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x. st_ex_bind
          (compute_eval_ind ck ceqs q) (\y.
        st_ex_return (compute_syntax_Pair x y)))) /\
   (compute_eval_ind ck ceqs (compute_syntax_Uop uop p) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x.
         do_uop uop x)) /\
   (compute_eval_ind ck ceqs (compute_syntax_Binop bop p q) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x. st_ex_bind
          (compute_eval_ind ck ceqs q) (\y.
        do_binop bop x y))) /\
   (compute_eval_ind ck ceqs (compute_syntax_App f cs) =
      (if ck = 0 then (raise_Failure (implode "timeout")) else st_ex_bind
          (compute_eval_option (ALOOKUP ceqs) f) (\(args,exp).
          st_ex_ignore_bind (compute_eval_check (LENGTH args = LENGTH cs))
              (st_ex_bind (compute_eval_ind_list ck ceqs cs) (\cs.
          compute_eval_ind (ck - 1) ceqs exp))))) /\
   (compute_eval_ind ck ceqs (compute_syntax_If p q r) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x.
        match x with (holSyntax_Tyapp (implode "num") []) (&0) ->
            compute_eval_ind ck ceqs r
        | (holSyntax_Tyapp (implode "num") []) _ -> compute_eval_ind ck
            ceqs q
        | compute_syntax_Pair _ _ -> compute_eval_ind ck ceqs r
        | _ -> (raise_Failure (implode "error")))) /\
   (compute_eval_ind ck ceqs (compute_syntax_Let s p q) =
      (if ck = 0 then (raise_Failure (implode "timeout")) else st_ex_bind
          (compute_eval_ind ck ceqs p) (\x.
          compute_eval_ind (ck - 1) ceqs q))) /\
   (compute_eval_ind_list ck ceqs [] = st_ex_return []) /\
   (compute_eval_ind_list ck ceqs (CONS c cs) =
      st_ex_bind (compute_eval_ind ck ceqs c) (\x. st_ex_bind
          (compute_eval_ind_list ck ceqs cs) (\xs.
        st_ex_return (CONS x xs))))`;;

(* HOL4 compute_evalScript.sml:505: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
