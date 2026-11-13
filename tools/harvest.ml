(* How each definition of the port was made, written out of a
   session that has loaded it, for tools/mkstrategies.py.

   A line is the constant, the strategy that made it, whether the
   termination condition was assumed instead of proved, and the
   relation it was made with, separated by tabs; a field that is
   empty is a "-". *)

(* The relation was printed with the types of its subterms, which
   is how define.ml captured it, and a file does not write it that
   way.  Parsing it back and printing it without them gives the
   form a file writes -- but an invented type variable prints as
   ?12345, which the parser does not take, so each of them becomes
   a letter first. *)

let letter_tyvars r =
  let buf = Buffer.create (String.length r) in
  let names = ref [] and i = ref 0 in
  let n = String.length r in
  while !i < n do
    if r.[!i] = '?' && !i + 1 < n &&
       r.[!i+1] >= '0' && r.[!i+1] <= '9' then
      (let j = ref (!i + 1) in
       while !j < n && r.[!j] >= '0' && r.[!j] <= '9' do incr j done;
       let key = String.sub r !i (!j - !i) in
       let nm =
         try assoc key !names
         with Failure _ ->
           let nm = String.make 1
                      (Char.chr(Char.code 'A' + length (!names))) in
           (names := (key,nm) :: !names; nm) in
       Buffer.add_string buf nm; i := !j)
    else (Buffer.add_char buf r.[!i]; incr i)
  done;
  Buffer.contents buf;;

let clean_relation r =
  try let t = parse_term (letter_tyvars r) in
      let p = !print_types_of_subterms in
      print_types_of_subterms := 0;
      let s = string_of_term t in
      print_types_of_subterms := p; s
  with Failure _ | Noparse -> r;;

let cake_harvest file =
  let flat s =
    String.map (fun c -> if c = '\n' || c = '\t' then ' ' else c) s in
  let ch = open_out file in
  do_list
    (fun (n,(w,c,r)) ->
       output_string ch
         (n ^ "\t" ^ (if w = "" then "-" else w) ^ "\t" ^
          (if c then "cheat" else "-") ^ "\t" ^
          (if r = "" then "-" else flat (clean_relation r)) ^ "\n"))
    (cake_strategies ());
  close_out ch;
  length (cake_strategies ());;
