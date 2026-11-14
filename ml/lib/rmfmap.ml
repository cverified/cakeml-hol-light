(* ======================================================== *)
(*  rmfmap: ported from HOL4's
    examples/algorithms/unification/triangular/first-order/
      compilation/rmfmapScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by tcallUnif.ml and unify.ml.  *)
(* ======================================================== *)

needs "lib/fmsp.ml";;
needs "lib/subst.ml";;
needs "lib/unifDef.ml";;
needs "lib/walk.ml";;
needs "lib/walkstar.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: transfer pred_set finite_map *)

let swfs_def = new_definition
  `swfs sp = wfs (sp2fm sp)`;;

let svwalk_def = new_definition
  `svwalk sp t = vwalk (sp2fm sp) t`;;

let swalk_def = new_definition
  `swalk sp t = walk (sp2fm sp) t`;;

let soc_def = new_definition
  `soc sp t v = oc (sp2fm sp) t v`;;


let sunify_def = new_definition
  `sunify sp t1 t2 = OPTION_MAP fm2sp (unify (sp2fm sp) t1 t2)`;;
