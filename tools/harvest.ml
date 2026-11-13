(* How each definition of the port was made, written out of a
   session that has loaded it, for tools/mkstrategies.py.

   A line is the constant, the strategy that made it, whether the
   termination condition was assumed instead of proved, and the
   relation it was made with, separated by tabs; a field that is
   empty is a "-".  The relation is printed without the types of
   its subterms, because a call site writes it in the context of
   the definition, where they are inferred again. *)

let cake_harvest file =
  let flat s =
    String.map (fun c -> if c = '\n' || c = '\t' then ' ' else c) s in
  let p = !print_types_of_subterms in
  print_types_of_subterms := 0;
  let ch = open_out file in
  do_list
    (fun (n,(w,c,r)) ->
       output_string ch
         (n ^ "\t" ^ (if w = "" then "-" else w) ^ "\t" ^
          (if c then "cheat" else "-") ^ "\t" ^
          (if r = "" then "-" else flat r) ^ "\n"))
    (cake_strategies ());
  close_out ch;
  print_types_of_subterms := p;
  length (cake_strategies ());;
