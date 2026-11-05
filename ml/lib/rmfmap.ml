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

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: transfer pred_set finite_map *)

let swfs_def = cake_define
  `swfs sp = wfs (sp2fm sp)`;;

let svwalk_def = cake_define
  `svwalk sp t = vwalk (sp2fm sp) t`;;

let swalk_def = cake_define
  `swalk sp t = walk (sp2fm sp) t`;;

let soc_def = cake_define
  `soc sp t v = oc (sp2fm sp) t v`;;


let sunify_def = cake_define
  `sunify sp t1 t2 = OPTION_MAP fm2sp (unify (sp2fm sp) t1 t2)`;;
