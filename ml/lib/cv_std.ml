(* ======================================================== *)
(*  cv_std: ported from HOL4's
    src/num/theories/cv_compute/automation/cv_stdScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 11 files of the port.  *)
(* ======================================================== *)

needs "lib/byte.ml";;
needs "lib/cv_type.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "lib/sum.ml";;
needs "lib/term.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: cv arithmetic words cv_rep cv_prim pair
   list option alist rich_list finite_set *)

(* HOL4 cv_stdScript.sml:11: the overload Num, which the port expands *)
(* HOL4 cv_stdScript.sml:12: the overload Pair, which the port expands *)

(* the termination relation that HOL4 gives is
     MEASURE cv_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 cv_stdScript.sml:352-354: the tactic that proves the termination *)
let cv_map_snd_def,cv_map_snd_ind = define_guess
  `cv_map_snd cv =
     cv_if (cv_ispair cv)
       (Pair (cv_snd (cv_fst cv)) (cv_map_snd (cv_snd cv)))
       (Num (&0))`;;

let cv_right_depth_def,cv_right_depth_ind = define_guess
  `(cv_right_depth (Num _) = (0:num)) /\
   (cv_right_depth (Pair x y) = ((cv_right_depth y + 1):num))`;;

let from_fmap_def = new_definition
  `from_fmap (f:'a->cv) (m:(num,'a)fmap) =
     from_sptree_sptree_spt f (fromAList (fmap_to_alist m))`;;
