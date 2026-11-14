(* ======================================================== *)
(*  bitstring: ported from HOL4's
    src/n-bit/bitstringScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by data_to_word_memoryProof.ml,
    export_arm8.ml, misc.ml and word_to_stackProof.ml.  *)
(* ======================================================== *)

needs "lib/numposrep.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: bit words *)

new_type_abbrev("bitstring",`:bool list`);;

let boolify_def,boolify_ind = define_rec
  [`boolify a [] = a`;
   `boolify a (CONS n l) = boolify (CONS (~(n = 0)) a) l`];;

let bitify_def,bitify_ind = define_guess
  [`bitify a [] = a`;
   `bitify a (CONS F l) = bitify (CONS 0 a) l`;
   `bitify a (CONS T l) = bitify (CONS 1 a) l`];;

let n2v_def = new_definition
  `n2v n = boolify [] (n2l 2 n)`;;

let v2n_def = new_definition
  `v2n l = l2n 2 (bitify [] l)`;;

let zero_extend_def = new_definition
  `zero_extend n v = PAD_LEFT F n v`;;

let fixwidth_def = new_definition
  `fixwidth n v =
      (let l = LENGTH v in
        if l < n then
           zero_extend n v else
           DROP (l - n) v)`;;

let shiftr_def = new_definition
  `shiftr (v:bool list) m = TAKE (LENGTH v - m) v`;;

let field_def = new_definition
  `field h l v = fixwidth (SUC h - l) (shiftr v l)`;;

let testbit_def = new_definition
  `testbit b v = (field b b v = [T])`;;

let add_def = new_definition
  `add a b =
     (let m = MAX (LENGTH a) (LENGTH b) in
       zero_extend m (n2v (v2n a + v2n b)))`;;
