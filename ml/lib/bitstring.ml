(* ======================================================== *)
(*  bitstring: ported from HOL4's
    src/n-bit/bitstringScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by export_arm8.ml, misc.ml and
    word_to_stackProof.ml.  *)
(* ======================================================== *)

needs "lib/numposrep.ml";;
(* HOL4 ancestors outside the port: bit words *)

new_type_abbrev("bitstring",`: bool list`);;

let boolify_def = cake_define_list
  [`boolify a [] = a`;
   `boolify a (n :: l) = boolify ((~(n = 0)) :: a) l`];;

let bitify_def = cake_define_list
  [`bitify a [] = a`;
   `bitify a (F :: l) = bitify (0 :: a) l`;
   `bitify a (T :: l) = bitify (1 :: a) l`];;

let n2v_def = cake_define
  `n2v n = boolify [] (n2l 2 n)`;;

let v2n_def = cake_define
  `v2n l = l2n 2 (bitify [] l)`;;

let zero_extend_def = cake_define
  `zero_extend n v = PAD_LEFT F n v`;;

let fixwidth_def = cake_define
  `fixwidth n v =
      (let l = LENGTH v in
        if l < n then
           zero_extend n v else
           DROP (l - n) v)`;;

let shiftr_def = cake_define
  `shiftr (v:bool list) m = TAKE (LENGTH v - m) v`;;

let field_def = cake_define
  `field h l v = fixwidth (SUC h - l) (shiftr v l)`;;

let testbit_def = cake_define
  `testbit b v = (field b b v = [T])`;;

let add_def = cake_define
  `add a b =
     (let m = MAX (LENGTH a) (LENGTH b) in
       zero_extend m (n2v (v2n a + v2n b)))`;;
