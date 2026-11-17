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

new_type("rat",0);;

cake_declare "rat_of_num" `:num->rat`;;
cake_declare "rat_add" `:rat->rat->rat`;;
cake_declare "rat_sub" `:rat->rat->rat`;;
cake_declare "rat_mul" `:rat->rat->rat`;;
cake_declare "rat_div" `:rat->rat->rat`;;
cake_declare "rat_ainv" `:rat->rat`;;
cake_declare "rat_minv" `:rat->rat`;;
cake_declare "rat_les" `:rat->rat->bool`;;
cake_declare "rat_leq" `:rat->rat->bool`;;

(* the operations go at the back of the resolution order, so that
   the + of two numbers is still the one of numbers *)
let _ = do_list (fun (t,c) -> hol4_overload_last t c)
  ["+","rat_add"; "-","rat_sub"; "*","rat_mul"; "/","rat_div";
   "--","rat_ainv"; "<","rat_les"; "<=","rat_leq"];;
(* PENDING: HOL4's fractions, which its rationals are a quotient of
   (abs_rat, frac_minv, rep_rat); rat_minv is declared in the head of this
   file instead *)
(* HOL4 ratScript.sml:213-214: the definition *)
hol4_numeral_form "rat_of_num";;

let rat_of_int_def = new_definition
  `(rat_of_int i:rat) = if i < (&0) then --(&(num_of_int (--i))) else
  &(num_of_int i)`;;

let div_gcd_def = new_definition
  `rat_div_gcd a b =
     let d = gcd(num_of_int a,b) in
       if d = 0 \/ d = 1 then (a,b) else (a / &d,b DIV d)`;;

let rat_expn_def,rat_expn_ind = define_guess
  `(rat_expn (r:rat) 0 = (&1:rat)) /\
   (rat_expn (r:rat) (SUC n) = ((r * rat_expn r n):rat))`;;

(* HOL4 ratScript.sml:3592: the overload expn, which the port expands *)

let rat_exp_def = new_definition
  `rat_exp r (i:int) = if (&0) <= i then rat_expn r (num_of_int i) else
  rat_minv (rat_expn r (num_of_int i))`;;

(* HOL4 ratScript.sml:3872: the overload exp, which the port expands *)
