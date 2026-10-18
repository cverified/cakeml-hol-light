(* ================================================================== *)
(*  mc_tailrec: the counterpart of HOL4's mc_tailrecLib               *)
(*                                                                    *)
(*  mc_multiword defines the routines of the bignum library from a    *)
(*  step function (tailrec_define_from_step): the function is the     *)
(*  SHORT_TAILREC of the step and its precondition the                *)
(*  SHORT_TAILREC_PRE of it, and HOL4 then proves the equation that   *)
(*  unfolds each of the two.  The port makes the two definitions and  *)
(*  assumes the two equations, as it does with the termination of a   *)
(*  definition.                                                       *)
(* ================================================================== *)

needs "lib/tailrec.ml";;

(* the variable that carries the precondition through a step
   function.  HOL4 calls it cond; the port writes it cond', because
   set_sep has a constant of that name *)

let mc_cond_var = `cond':bool`;;

(* HOL4's tm2ftree reads a binding of that variable as a condition
   node of the tree of the body, which rm_conds drops: the equation
   of the function itself says nothing about the preconditions *)

let is_cond_let (p,_) = p = mc_cond_var;;

let rec mc_rm_conds tm =
  if is_cond tm then
    let b,(x,y) = dest_cond tm in
    mk_cond(b,mc_rm_conds x,mc_rm_conds y)
  else
    try let bs,bod = dest_let tm in
        let bs' = filter (fun b -> not (is_cond_let b)) bs in
        if bs' = [] then mc_rm_conds bod
        else mk_let(bs',mc_rm_conds bod)
    with Failure _ -> tm;;

(* the leaves of the body of a step function: each is a pair of
   INL (the arguments of the next round) or INR (the value) and the
   condition that the round assumes *)

let rec mc_leaves_inl f1 f2 tm =
  if is_cond tm then
    let b,(x,y) = dest_cond tm in
    mk_cond(b,mc_leaves_inl f1 f2 x,mc_leaves_inl f1 f2 y)
  else
    try let bs,bod = dest_let tm in
        mk_let(bs,mc_leaves_inl f1 f2 bod)
    with Failure _ ->
      let x,c = dest_pair tm in
      let op,arg = dest_comb x in
      if fst(dest_const(fst(strip_comb op))) = "INL"
      then f1 arg c else f2 arg c;;

(* an equation that the first pass assumes, as it assumes the
   termination of a definition: the constant is there and has its
   value, and what is left is the proof that the equation unfolds
   it (which is HOL4's tailrec_define_from_step) *)

let mc_assume name why eq =
  let tm = list_mk_forall(frees eq,eq) in
  the_cheats := name :: !the_cheats;
  cheat_why := why;
  print_string ("\ntailrec_define " ^ name ^ " (" ^ why ^ ")\n");
  note_cheat name tm;
  flush stdout;
  new_axiom tm;;

(* the equations of the functions that tailrec_define makes, by
   name: HOL4 finds them in the theory (DB.find), and the deep
   embedding that word_bignum generates looks them up there *)

let the_tailrec_defs = ref ([]:(string * thm) list);;

(* tailrec_define name step makes
     name     = SHORT_TAILREC step
     name_pre = SHORT_TAILREC_PRE step
   and gives the two equations that unfold them, which the first
   pass assumes *)

let tailrec_define name step =
  let f = mk_icomb(`SHORT_TAILREC`,step) in
  let p = mk_icomb(`SHORT_TAILREC_PRE`,step) in
  let _ = new_definition(mk_eq(mk_var(name,type_of f),f)) in
  let _ = new_definition(mk_eq(mk_var(name ^ "_pre",type_of p),p)) in
  let fc = mk_mconst(name,type_of f) in
  let pc = mk_mconst(name ^ "_pre",type_of p) in
  let args,body = dest_gabs step in
  let def_body =
    mc_leaves_inl (fun a _ -> mk_comb(fc,a)) (fun a _ -> a)
                  (mc_rm_conds body) in
  let def_eq = mk_eq(mk_comb(fc,args),def_body) in
  let pre_body =
    mc_leaves_inl (fun a c -> mk_conj(mk_comb(pc,a),c))
                  (fun _ c -> c) body in
  let pre_eq = mk_eq(mk_comb(pc,args),
                     vsubst [`T`,mc_cond_var] pre_body) in
  let def = mc_assume name
              "equation of a tail recursion assumed" def_eq in
  let pre = mc_assume (name ^ "_pre")
              "equation of a tail recursion assumed" pre_eq in
  the_tailrec_defs := (name ^ "_def",def) ::
                      (name ^ "_pre_def",pre) :: !the_tailrec_defs;
  (def,pre);;
