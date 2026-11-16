(* ======================================================== *)
(*  alist_tree: ported from HOL4's
    src/finite_maps/alist_treeScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by evaluate_dec.ml and ml_prog.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: rich_list alist *)
let option_choice_f_def = new_definition
  `option_choice_f f g = (\x. OPTION_CHOICE (f x) (g x))`;;
