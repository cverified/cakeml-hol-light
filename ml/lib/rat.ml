(* ======================================================== *)
(*  rat: ported from HOL4's
    src/rational/ratScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by RatProg.ml, cv_type.ml and
    mlrat.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: arithmetic pred_set integer intExtension
   frac gcd divides primeFactor *)
let rat_minv_def = new_definition
  `rat_minv r1 = abs_rat (frac_minv (rep_rat r1))`;;
hol4_numeral_form "rat_of_num";;

let rat_of_int_def = new_definition
  `(rat_of_int i:rat) = if i < (&0) then --(&(num_of_int (--i))) else
  &(num_of_int i)`;;

let div_gcd_def = new_definition
  `rat_div_gcd a b =
     let d = hol4_gcd (num_of_int a) b in
       if d = 0 \/ d = 1 then (a,b) else (a / &d,b DIV d)`;;

let rat_expn_def,rat_expn_ind = define_guess
  `(rat_expn (r:rat) 0 = (1:rat)) /\
   (rat_expn (r:rat) (SUC n) = ((r * rat_expn r n):rat))`;;

(* HOL4 ratScript.sml:3592: the overload expn, which the port expands *)

let rat_exp_def = new_definition
  `rat_exp r (i:int) = if (&0) <= i then rat_expn r (num_of_int i) else
  rat_minv (rat_expn r (num_of_int i))`;;

(* HOL4 ratScript.sml:3872: the overload exp, which the port expands *)
