(* Read every statement of the port with the interface cut down to
   the theories that the source of its file can see
   (tools/scopelib.ml), which is how HOL4 reads one, and
   say what that changes: a statement that then does not parse, one
   that then has a free variable, and one that reads another
   constant than the session has in the theorem itself
   (tmp/csts.txt, written from the theorems that the run made).

   This is the measurement behind ISSUES.md "a name that the load
   order resolves": the port reads a statement with every overload
   of every file in place, so an overloaded name that no type pins
   gets the constant of the theory that registered it last. *)

loadt "/home/freek/claude/hol-light/cakeml/tools/scopelib.ml";;

(* the constants of the statement as the run read it *)

let the_csts = Hashtbl.create 20000;;

let read_csts () =
  Hashtbl.reset the_csts;
  do_list (fun l ->
    match split_tab l with
      [_; b; cs] -> Hashtbl.replace the_csts b
                      (String.split_on_char ' ' cs)
    | _ -> ())
    (slurp_lines (cake_dir ^ "tmp/csts.txt"));;

(* with this the statements are read as the session reads them,
   with no scope at all: that is the baseline, because a re-reading
   in a session that has the whole port loaded fails for statements
   that the file itself read without trouble (tools/diag.py says
   so of bvl_to_bvi$compile_single_eq), and a failure that the
   scope did not cause is no finding *)

let the_no_scope = ref false;;

let scope_run infile outfile =
  read_scopes (); read_csts (); read_cstthy ();
  let ic = open_in infile in
  let oc = open_out outfile in
  let n = ref 0 and nfail = ref 0 and nfree = ref 0
  and nchange = ref 0 and nnoscope = ref 0 in
  let hid = ref ([]:string list) and nexthid = ref ([]:string list) in
  let hidc = ref ([]:(string * string) list)
  and nexthidc = ref ([]:(string * string) list) in
  let curfile = ref "" and scope = ref ([]:string list) in
  let itf = ref ([]:(string * (string * hol_type)) list) in
  let cur = ref ("","","") and buf = ref ([]:string list) in
  let say tag f l nm s =
    output_string oc (tag^"\t"^f^"\t"^l^"\t"^nm^"\t"^s^"\n");
    flush oc in
  let one () =
    let f,l,nm = !cur in
    if nm <> "" then begin
      incr n;
      let s = String.concat "\n" (rev !buf) in
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
      if !scope = [] then
        (incr nnoscope; say "SNOSCOPE" f l nm "")
      else
      (try
        let tm = if !the_no_scope then read ()
                 else with_interface !itf read in
        let vs = frees tm in
        if vs <> [] then begin
          incr nfree;
          say "SFREE" f l nm
            (String.concat " " (map (fun v -> fst(dest_var v)) vs))
        end;
        let cs = setify (map (fun t -> fst(dest_const t))
                             (find_terms is_const tm)) in
        let was = try Hashtbl.find the_csts nm with Not_found -> [] in
        if was <> [] then begin
          let lost = filter (fun c -> not (mem c cs)) was
          and got = filter (fun c -> not (mem c was)) cs in
          if lost <> [] || got <> [] then begin
            incr nchange;
            say "SCHANGE" f l nm
              ("the run " ^ String.concat " " lost ^ " / the scope "
               ^ String.concat " " got)
          end
        end
       with Failure m -> (incr nfail; say "SFAIL" f l nm m)
          | Invalid_argument m -> (incr nfail; say "SFAIL" f l nm m))
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
      (match split_tab line with
         _::f::l::nm::_ -> cur := (f,l,nm)
       | _ -> cur := ("?","0","?"));
      let f,_,_ = !cur in
      if f <> !curfile then
        (curfile := f; hid := !nexthid; nexthid := [];
         hidc := !nexthidc; nexthidc := [];
         scope := (try assoc f (!the_scopes) with Failure _ -> []);
         if !scope <> [] then itf := in_scope !scope)
    end else buf := line :: !buf
  done with End_of_file -> ());
  one ();
  close_in ic; close_out oc;
  print_string ("SCOPE " ^ string_of_int !n ^ " statements, "
    ^ string_of_int !nfail ^ " that the scope of their file cannot "
    ^ "read, " ^ string_of_int !nfree ^ " with a free variable, "
    ^ string_of_int !nchange ^ " that read another constant, "
    ^ string_of_int !nnoscope ^ " of a file with no scope\n");;
