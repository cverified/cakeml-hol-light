(* ======================================================== *)
(*  grammar: ported from HOL4's
    examples/formal-languages/context-free/grammarScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 15 files of the port.  *)
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
       grammar_TOK tk,_ -> SOME tk
     | _ -> NONE`;;
add_simp destTOK_def;;

let grammar_FIELDS = define_record "grammar"
  ["start","'b+num";
   "rules","('b+num,((('a,'b)grammar_symbol) list->bool))fmap"];;

let parsetree_INDUCT,parsetree_RECURSION = define_datatype
  "parsetree =
     Lf (('a,'b)grammar_symbol#'locs)
   | Nd (('b+num)#'locs) (parsetree list)";;

let ptree_loc_def = define_cases
  `(ptree_loc (Lf (_,l)) = l) /\
   (ptree_loc (Nd (_,l) _) = l)`;;

let ptree_list_loc_def = new_definition
  `ptree_list_loc l = merge_list_locs (MAP ptree_loc l)`;;

let ptree_head_def = define_cases
  `(ptree_head (Lf (tok,l)) = tok) /\
   (ptree_head (Nd (nt,l) children) = grammar_NT nt)`;;
add_simp ptree_head_def;;

(* HOL4 grammarScript.sml:50-55: the definition *)

let ptree_fringe_def,ptree_fringe_ind = define_shaped_rec
  "nested"
  `(ptree_fringe (Lf (t,_)) = [t]) /\
   (ptree_fringe (Nd _ children) = FLAT (MAP ptree_fringe children))`;;

let real_fringe_def,real_fringe_ind = define_shaped_rec
  "nested"
  `(real_fringe (Lf t) = [t]) /\
   (real_fringe (Nd n ptl) = FLAT (MAP real_fringe ptl))`;;
add_simp real_fringe_def;;

let valid_locs_def,valid_locs_ind = define_shaped_rec
  "nested"
  `(valid_locs (Lf _) <=> T) /\
   (valid_locs (Nd (_,l) children) <=>
         l = merge_list_locs (MAP ptree_loc children) /\
         (!pt. MEM pt children ==> valid_locs pt))`;;
add_simp valid_locs_def;;

(* HOL4 grammarScript.sml:116-118: the definition *)

let derive_def = new_definition
  `derive G sf1 sf2 <=>
     (?p sym rhs s. sf1 = APPEND (APPEND p [grammar_NT sym]) s /\ sf2 =
       APPEND (APPEND p rhs) s /\
                   sym IN FDOM (grammar_rules G) /\ rhs IN FAPPLY
                     (grammar_rules G) sym)`;;

(* HOL4 grammarScript.sml:157: the overload derives, which the port expands *)
