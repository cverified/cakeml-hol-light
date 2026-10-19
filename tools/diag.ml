(* diagnose the statements of tmp/stmts.txt in a session that has
   the port loaded: what does not parse, what is not a formula,
   what has free variables (a constant the port lacks becomes
   one), and what takes more than a second to typecheck.  The
   statements are read as ml/lib/theorem.ml reads them: with the
   names that the file hides as variables, and, where that fails,
   with the overloads of the record field names taken away. *)

let slurp_lines f =
  let ic = open_in f in
  let out = ref [] in
  (try while true do out := input_line ic :: !out done
   with End_of_file -> ());
  close_in ic; rev !out;;

(* the overloads of the accessors of a record field: the name and
   the constant of every one (tools/fieldovl.py writes them) *)

let field_ovl =
  map (fun l ->
         let i = String.index l '\t' in
         String.sub l 0 i,
         String.sub l (i + 1) (String.length l - i - 1))
      (filter (fun l -> String.contains l '\t')
         (slurp_lines
            "/home/freek/claude/hol-light/cakeml/tmp/fieldovl.txt"));;

let as_vars f =
  let saved = !the_interface in
  (* as cake_as_vars does: only the accessors of a field go, so a
     name that a constant of its own has as well keeps it *)
  the_interface :=
    filter (fun (n,(c,_)) -> not (mem (n,c) field_ovl)) saved;
  let fin () = the_interface := saved in
  try let x = f () in fin (); x with e -> (fin (); raise e);;

let diag_run infile outfile =
  let ic = open_in infile in
  let oc = open_out outfile in
  let n = ref 0 and bad = ref 0 and fv = ref 0 in
  let hid = ref ([]:string list) in
  let nexthid = ref ([]:string list) in
  (* the pairs that cake_hide_consts of the file takes out of the
     interface: a name that the accessors of a record field have
     as well keeps those *)
  let hidc = ref ([]:(string * string) list) in
  let nexthidc = ref ([]:(string * string) list) in
  let curfile = ref "" in
  let cur = ref ("","","") and buf = ref ([]:string list) in
  let say tag f l nm s =
    output_string oc (tag^"\t"^f^"\t"^l^"\t"^nm^"\t"^s^"\n");
    flush oc in
  let one () =
    let f,l,nm = !cur in
    if nm <> "" then begin
      incr n;
      let s = String.concat "\n" (rev !buf) in
      let t0 = Sys.time () in
      let read () =
        do_list hide_constant !hid;
        let saved = !the_interface in
        if !hidc <> [] then
          the_interface :=
            filter (fun (n,(c,_)) -> not (mem (n,c) !hidc)) saved;
        let fin () =
          do_list unhide_constant !hid;
          if !hidc <> [] then the_interface := saved in
        try let tm = parse_term s in fin (); tm
        with e -> (fin (); raise e) in
      (try
        let tm = (try read () with
                    Failure _ | Invalid_argument _ as e ->
                      (try let tm = as_vars read in
                           incr fv; tm
                       with Failure _ | Invalid_argument _ ->
                         raise e)) in
        let ty = type_of tm in
        if ty <> bool_ty then
          (incr bad; say "BADTYPE" f l nm (string_of_type ty))
        else
          let vs = frees tm in
          if vs <> [] then
            say "FREE" f l nm
              (String.concat " "
                 (map (fun v -> fst (dest_var v)^":"^
                                string_of_type (type_of v)) vs))
       with Failure m -> (incr bad; say "FAIL" f l nm m)
          | Invalid_argument m -> (incr bad; say "FAIL" f l nm m));
      let dt = Sys.time () -. t0 in
      if dt > 1.0 then say "SLOW" f l nm (string_of_float dt)
    end;
    buf := [] in
  (try while true do
    let line = input_line ic in
    if String.length line > 8 && String.sub line 0 8 = "@@@HIDEC"
    then
      (one (); cur := ("","","");
       nexthidc :=
         map (fun w -> let i = String.index w ',' in
                       String.sub w 0 i,
                       String.sub w (i + 1) (String.length w - i - 1))
           (filter (fun s -> String.contains s ',')
              (String.split_on_char ' '
                 (String.sub line 9 (String.length line - 9)))))
    else if String.length line > 7 && String.sub line 0 7 = "@@@HIDE"
    then
      (one (); cur := ("","","");
       nexthid := filter (fun s -> s <> "")
                    (String.split_on_char ' '
                       (String.sub line 8 (String.length line - 8))))
    else if String.length line > 3 && String.sub line 0 3 = "@@@"
    then begin
      one ();
      (match String.split_on_char '\t' line with
         _::f::l::nm::_ -> cur := (f,l,nm)
       | _ -> cur := ("?","0","?"));
      (* a file hides what its own cake_hide says and nothing of
         the file before it *)
      let f,_,_ = !cur in
      if f <> !curfile then
        (curfile := f; hid := !nexthid; nexthid := [];
         hidc := !nexthidc; nexthidc := [])
    end else buf := line :: !buf
  done with End_of_file -> ());
  one ();
  close_in ic; close_out oc;
  !n,!bad,!fv;;
