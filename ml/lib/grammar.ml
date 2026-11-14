(* ======================================================== *)
(*  grammar: ported from HOL4's
    examples/formal-languages/context-free/grammarScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 10 files of the port.  *)
(* ======================================================== *)

needs "lib/location.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: list pred_set finite_map relation *)
let grammar_symbol_INDUCT,grammar_symbol_RECURSION = define_datatype
  "grammar_symbol =
     grammar_TOK ('a)
   | grammar_NT ('b+num)";;

let destTOK_def = new_definition
  `grammar_destTOK x1 =
        match x1 with
          (grammar_TOK tk,_1) -> SOME tk
        | _2 -> NONE`;;
add_simp destTOK_def;;

let grammar_FIELDS = define_record "grammar"
  ["start","'b+num";
   "rules","('b+num,((('a,'b)grammar_symbol) list->bool))fmap"];;

let parsetree_INDUCT,parsetree_RECURSION = define_datatype
  "parsetree =
     Lf (('a,'b)grammar_symbol#'locs)
   | Nd (('b+num)#'locs) (parsetree list)";;

let ptree_loc_def = define_cases
  [`ptree_loc (Lf (_3,l)) = l`;
   `ptree_loc (Nd (_4,l) _5) = l`];;

let ptree_list_loc_def = new_definition
  `ptree_list_loc l = merge_list_locs (MAP ptree_loc l)`;;

let ptree_head_def = define_cases
  [`ptree_head (Lf (tok',l)) = tok'`;
   `ptree_head (Nd (nt',l) children) = grammar_NT nt'`];;
add_simp ptree_head_def;;

let valid_ptree_def,valid_ptree_ind = define_shaped_rec
  "nested"
  [`valid_ptree G (Lf _6) <=> T`;
   `valid_ptree G (Nd (nt',l) children) <=>
        nt' IN FDOM (grammar_rules G) /\ MAP ptree_head children IN
            FAPPLY (grammar_rules G) nt' /\
        (!pt. pt IN set_of_list children ==> valid_ptree G pt)`];;
add_simp valid_ptree_def;;

let ptree_fringe_def,ptree_fringe_ind = define_shaped_rec
  "nested"
  [`ptree_fringe (Lf (t,_7)) = [t]`;
   `ptree_fringe (Nd _8 children) = FLAT (MAP ptree_fringe
    children)`];;

let real_fringe_def,real_fringe_ind = define_shaped_rec
  "nested"
  [`real_fringe (Lf t) = [t]`;
   `real_fringe (Nd n ptl) = FLAT (MAP real_fringe ptl)`];;
add_simp real_fringe_def;;

let valid_locs_def,valid_locs_ind = define_shaped_rec
  "nested"
  [`valid_locs (Lf _9) <=> T`;
   `valid_locs (Nd (_10,l) children) <=>
         l = merge_list_locs (MAP ptree_loc children) /\
         (!pt. MEM pt children ==> valid_locs pt)`];;
add_simp valid_locs_def;;

let valid_lptree_def = new_definition
  `valid_lptree G pt <=> valid_locs pt /\ valid_ptree G pt`;;

let derive_def = new_definition
  `derive G sf1 sf2 <=>
     (?p sym rhs s. sf1 = APPEND (APPEND p [grammar_NT sym]) s /\ sf2
       = APPEND (APPEND p rhs) s /\
                   sym IN FDOM (grammar_rules G) /\ rhs IN FAPPLY
                     (grammar_rules G) sym)`;;

(* HOL4 grammarScript.sml:157: the overload derives, which the port
   expands *)
