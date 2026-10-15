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
hol4_overload "TOK" "grammar_TOK";;
hol4_overload "NT" "grammar_NT";;

let destTOK_def = cake_define
  `grammar_destTOK x1 =
        match x1 with
          (TOK tk,_1) -> SOME tk
        | _2 -> NONE`;;
hol4_overload "destTOK" "grammar_destTOK";;

let grammar_FIELDS = define_record "grammar"
  ["start","'b+num";
   "rules","('b+num,((('a,'b)grammar_symbol) list->bool))fmap"];;

let parsetree_INDUCT,parsetree_RECURSION = define_datatype
  "parsetree = Lf (('a,'b)grammar_symbol#'locs) | Nd (('b+num)#'locs) \
   (parsetree list)";;

let ptree_loc_def = cake_define_list
  [`ptree_loc (Lf (_3,l):('a,'b,'locs)parsetree) = l`;
   `ptree_loc (Nd (_4,l) _5:('a,'b,'locs)parsetree) = l`];;

let ptree_list_loc_def = cake_define
  `ptree_list_loc l = merge_list_locs (MAP ptree_loc l)`;;

let ptree_head_def = cake_define_list
  [`ptree_head (Lf (tok',l):('a,'b,'locs)parsetree) = tok'`;
   `ptree_head (Nd (nt',l) children:('a,'b,'locs)parsetree) = NT nt'`];;

let valid_ptree_def = cake_define_list
  [`valid_ptree G (Lf _6:('a,'b,'locs)parsetree) <=> T`;
   `valid_ptree G (Nd (nt',l) children:('a,'b,'locs)parsetree) <=>
        nt' IN FDOM (grammar_rules G) /\ MAP ptree_head children IN
          FAPPLY (grammar_rules G) nt' /\
        (!pt. pt IN set_of_list children ==> valid_ptree G pt)`];;

let real_fringe_def = cake_define_list
  [`real_fringe (Lf t:('a,'b,'locs)parsetree) = [t]`;
   `real_fringe (Nd n ptl:('a,'b,'locs)parsetree) = FLAT (MAP
  real_fringe ptl)`];;

let valid_locs_def = cake_define_list
  [`valid_locs (Lf _7:('a,'b,'locs)parsetree) <=> T`;
   `valid_locs (Nd (_8,l) children:('a,'b,'locs)parsetree) <=>
         l = merge_list_locs (MAP ptree_loc children) /\
         (!pt. MEM pt children ==> valid_locs pt)`];;

let valid_lptree_def = cake_define
  `valid_lptree G pt <=> valid_locs pt /\ valid_ptree G pt`;;

let derive_def = cake_define
  `derive G sf1 sf2 <=>
     (?p sym rhs s. sf1 = p ++ [NT sym] ++ s /\ sf2 = p ++ rhs ++ s
       /\
                   sym IN FDOM (grammar_rules G) /\ rhs IN FAPPLY
                     (grammar_rules G) sym)`;;

(* HOL4 overload (expanded in the port):
     derives = λG. RTC (derive G) *)
