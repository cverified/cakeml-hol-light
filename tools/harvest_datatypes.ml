(* ================================================================== *)
(*  Record what define_datatype makes, so that an abstract can make   *)
(*  the same thing without proving it.                                *)
(*                                                                    *)
(*  An abstract assumes the equations of every definition and skips   *)
(*  every proof, but it was still building all 249 datatypes of the   *)
(*  port for real -- 18% of its processor time -- because the         *)
(*  induction and the recursion theorem of a datatype are proved and  *)
(*  not read off the specification.  Their statements are determined  *)
(*  by the specification all the same, so they are recorded here      *)
(*  once and assumed afterwards.  Everything else about the datatype  *)
(*  -- the type, its arity, the constructors and their types -- the   *)
(*  record carries as well, so that an abstract makes them through    *)
(*  the kernel and nothing but the two theorems is assumed.           *)
(*                                                                    *)
(*  This file is loaded over a session that is about to load the      *)
(*  port; tools/mkdatatypes.py turns what it writes into             *)
(*  ml/lib/datatypes.ml.                                              *)
(* ================================================================== *)

let cake_dt_out = ref "/home/freek/claude/hol-light/cakeml/tmp/datatypes.txt";;

let cake_real_define_datatype = define_datatype;;

(* the types that a family defines, and their arity, read off the
   constructors that the specification names *)

let cake_dt_types spec =
  map (fun (ty, alts) ->
         let nm = dest_vartype ty in
         let cty = get_const_type (fst (hd alts)) in
         let res = itlist (fun _ t -> snd (dest_fun_ty t))
                          (snd (hd alts)) cty in
         nm, (length (snd (dest_type res)), length alts))
      (parse_datatype_spec spec);;

let cake_dt_cons spec =
  itlist (fun (_, alts) l ->
            map (fun (c, _) -> c, get_const_type c) alts @ l)
         (parse_datatype_spec spec) [];;

let define_datatype spec =
  let ith, rth = cake_real_define_datatype spec in
  let f = open_out_gen [Open_append; Open_creat] 0o644 (!cake_dt_out) in
  let p s = output_string f (s ^ "\n") in
  (* a constant of the port may be printed under a name that the
     file overloads with it, and that name would be read back as
     whichever constant the interface resolves it to.  What is
     recorded has to be the constant itself *)
  let old_rev = !reverse_interface_mapping in
  reverse_interface_mapping := false;
  p "SPEC"; p spec; p "ENDSPEC";
  do_list (fun (n, (a, k)) ->
             p (Printf.sprintf "TYPE %s %d %d" n a k))
          (cake_dt_types spec);
  do_list (fun (c, ty) ->
             p ("CON " ^ c); p (string_of_type ty))
          (cake_dt_cons spec);
  p "INDUCT"; p (string_of_term (concl ith)); p "ENDTHM";
  p "RECURSION"; p (string_of_term (concl rth)); p "ENDTHM";
  (* what define_type_raw leaves in HOL Light's own stores: the
     distinctness and the injectivity of the constructors, which a
     statement of the port asks for by the name of the type.  An
     abstract states them and proves neither, so their statements
     are recorded here like the other two *)
  (* the statement is made before the header is written: a type
     of one constructor has no distinctness theorem, and a type
     whose constructors take no arguments has no injectivity, so
     the lookup raises and a header already on the file would
     leave a record that no reader can take apart *)
  do_list (fun (n, _) ->
             (try let st = string_of_term (concl (distinctness n)) in
                  p ("DISTINCT " ^ n); p st; p "ENDTHM"
              with Failure _ -> ());
             (try let st = string_of_term (concl (injectivity n)) in
                  p ("INJECT " ^ n); p st; p "ENDTHM"
              with Failure _ -> ()))
          (cake_dt_types spec);
  p "END";
  reverse_interface_mapping := old_rev;
  close_out f;
  ith, rth;;
