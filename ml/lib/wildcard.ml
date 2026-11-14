(* ================================================================== *)
(*  Wildcards of a quotation.                                         *)
(*                                                                    *)
(*  HOL Light reads every _ of a quotation as one and the same         *)
(*  variable "_", so the two wildcards of CONS _ (CONS _ t), or the   *)
(*  wildcards of two clauses of one definition, would be one          *)
(*  variable of one type -- and the pattern would then say that the   *)
(*  two places are equal.  HOL4 reads each _ as a variable of its     *)
(*  own, which is what a source of CakeML means by it.                *)
(*                                                                    *)
(*  The parse_term below, which the quotation expander calls, gives   *)
(*  every _ token a name of its own before the term is parsed, so a   *)
(*  wildcard is an independent variable of an independent type and a  *)
(*  file of the port can write _ wherever the source does.            *)
(*  cake_wildcard recognises such a name, and the definition          *)
(*  machinery renames them before they reach a theorem                *)
(*  (ml/lib/definition.ml).                                           *)
(* ================================================================== *)

let cake_wild_prefix = "_%w";;

let cake_wildcard n =
  n = "_" ||
  String.length n > String.length cake_wild_prefix &&
  String.sub n 0 (String.length cake_wild_prefix) = cake_wild_prefix;;

let cake_wild_counter = ref 0;;

(* the lexer glues _ to the symbol characters after it (the _: of
   (_:num) lexes as one identifier "_:"), so such a token is split
   and the rest of it lexed again: (_:num) is then a wildcard whose
   type the quotation says *)

let cake_wild_tokens t =
  let fresh () =
    incr cake_wild_counter;
    Ident (cake_wild_prefix ^ string_of_int !cake_wild_counter) in
  match t with
    Ident "_" -> [fresh ()]
  | Ident s when String.length s > 1 && String.sub s 0 1 = "_" &&
                 forall issymb (tl (explode s)) ->
      fresh () :: lex (tl (explode s))
  | _ -> [t];;

(* and the name of a wildcard is not one to carry into a theorem,
   so it is given one of the shape that HOL4 gives it there.  Every
   wildcard of the term gets a name of its own: by then each of
   them has a type of its own, which is what the names above were
   for, and the renaming cannot make two of them one *)

let cake_name_wildcards tm =
  let used = ref (map (fun v -> fst (dest_var v)) (variables tm)) in
  let seen = ref ([] : (term * term) list) in
  let name v =
    try assoc v !seen with Failure _ ->
      let rec go i =
        let n = "_" ^ string_of_int i in
        if mem n !used then go (i + 1) else (used := n :: !used; n) in
      let w = mk_var (go 1, type_of v) in
      seen := (v, w) :: !seen; w in
  let rec go tm =
    match tm with
      Var (n, _) -> if cake_wildcard n then name tm else tm
    | Const (_, _) -> tm
    | Comb (f, x) -> mk_comb (go f, go x)
    | Abs (v, b) -> mk_abs (go v, go b) in
  go tm;;

let parse_term s =
  let before = !cake_wild_counter in
  let ptm, l =
    (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if l <> [] then failwith "Unparsed input following term" else
  let tm = (term_of_preterm o (retypecheck [])) ptm in
  (* a quotation with no wildcard in it is left alone, so that the
     port pays nothing for this where it writes none *)
  if !cake_wild_counter = before then tm else cake_name_wildcards tm;;
