(* ======================================================== *)
(*  grammar: ported from HOL4's
    examples/formal-languages/context-free/grammarScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/location.ml";;
(* HOL4 ancestors outside the port: list pred_set finite_map relation *)
let grammar_symbol_INDUCT,grammar_symbol_RECURSION = define_datatype
  "grammar_symbol = grammar_TOK ('a) | grammar_NT ('b+num)";;
let destTOK_def = cake_define
  `grammar_destTOK x1 =
        match x1 with
          (grammar_TOK tk,_1) -> SOME tk
        | _2 -> NONE`;;
let grammar_FIELDS = define_record "grammar"
  ["start","'b+num";
   "rules","('b+num,((('a,'b)grammar_symbol) list->bool))fmap"];;
let parsetree_INDUCT,parsetree_RECURSION = define_datatype
  "parsetree = Lf (('a,'b)grammar_symbol#'locs) | Nd (('b+num)#'locs) (parsetree list)";;
let ptree_loc_def = cake_define
  `ptree_loc (Lf (_3,l)) = l /\
   ptree_loc (Nd (_4,l) _5) = l`;;
let ptree_list_loc_def = cake_define
  `ptree_list_loc l = merge_list_locs (MAP ptree_loc l)`;;
let ptree_head_def = cake_define
  `(grammar_ptree_head (Lf (tok,l)) = tok) /\
   (grammar_ptree_head (Nd (nt,l) children) = grammar_NT nt)`;;
let valid_ptree_def = cake_define
  `(valid_ptree G (Lf _6) <=> T) /\
   (valid_ptree G (Nd (nt,l) children) <=>
     nt IN FDOM (grammar_rules G) /\ MAP grammar_ptree_head children
       IN FAPPLY (grammar_rules G) nt /\
     (!pt. pt IN set_of_list children ==> valid_ptree G pt))`;;
let real_fringe_def = cake_define
  `(grammar_real_fringe (Lf t) = [t]) /\
   (grammar_real_fringe (Nd n ptl) = FLAT (MAP grammar_real_fringe
     ptl))`;;
let valid_locs_def = cake_define
  `(valid_locs (Lf _7) <=> T) /\
   (valid_locs (Nd (_8,l) children) <=>
      l = merge_list_locs (MAP ptree_loc children) /\
      (!pt. MEM pt children ==> valid_locs pt))`;;
let valid_lptree_def = cake_define
  `valid_lptree G pt <=> valid_locs pt /\ valid_ptree G pt`;;
