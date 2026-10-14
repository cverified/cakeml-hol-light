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
let valid_ptree_list_def,valid_ptree_def =
  let ths = cake_define
    `(valid_ptree G (Lf _1) <=> T) /\
     (valid_ptree G (Nd (nt,l) children) <=>
        nt IN FDOM (grammar_rules G) /\
        MAP grammar_ptree_head children IN
          FAPPLY (grammar_rules G) nt /\
        valid_ptree_list G children) /\
     (valid_ptree_list G [] <=> T) /\
     (valid_ptree_list G (p :: ps) <=>
        valid_ptree G p /\ valid_ptree_list G ps)` in
  let lem = prove
   (`!G l. valid_ptree_list G l <=> ALL (valid_ptree G) l`,
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[ths; ALL]) in
  ths,
  prove
   (`(valid_ptree G (Lf _1) <=> T) /\
     (valid_ptree G (Nd (nt,l) children) <=>
        nt IN FDOM (grammar_rules G) /\
        MAP grammar_ptree_head children IN
          FAPPLY (grammar_rules G) nt /\
        (!pt. pt IN set_of_list children ==> valid_ptree G pt))`,
    REWRITE_TAC[ths; lem; IN_SET_OF_LIST; GSYM ALL_MEM]);;
let valid_locs_list_def,valid_locs_def =
  let ths = cake_define
    `(valid_locs (Lf _6) <=> T) /\
     (valid_locs (Nd (_7,l) children) <=>
        l = merge_list_locs (MAP ptree_loc children) /\
        valid_locs_list children) /\
     (valid_locs_list [] <=> T) /\
     (valid_locs_list (p :: ps) <=>
        valid_locs p /\ valid_locs_list ps)` in
  let lem = prove
   (`!l. valid_locs_list l <=> ALL valid_locs l`,
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ths; ALL]) in
  ths,
  prove
   (`(valid_locs (Lf _6) <=> T) /\
     (valid_locs (Nd (_7,l) children) <=>
        l = merge_list_locs (MAP ptree_loc children) /\
        (!pt. MEM pt children ==> valid_locs pt))`,
    REWRITE_TAC[ths; lem; GSYM ALL_MEM]);;
let valid_lptree_def = cake_define
  `valid_lptree G pt <=> valid_locs pt /\ valid_ptree G pt`;;
