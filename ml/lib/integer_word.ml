(* ======================================================== *)
(*  integer_word: ported from HOL4's
    src/integer/integer_wordScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* HOL4 ancestors outside the port: arithmetic bit words integer *)
let toString_def = cake_define
  `integer_word_toString (i:int) =
      (if i < 0 then
        "~" ++ num_to_dec_string (num_of_int (--i)) else
        num_to_dec_string (num_of_int i))`;;
let fromString_def = cake_define
  `integer_word_fromString s =
        match s with
          ((CHR 126) :: t) -> --&(num_from_dec_string t)
        | ((CHR 45) :: t) -> --&(num_from_dec_string t)
        | s -> &(num_from_dec_string s)`;;
let i2w_def = cake_define
  `(i2w (i:int):'a word) =
     (if i < 0 then --(n2w (num_of_int (--i))) else n2w (num_of_int
       i))`;;
let w2i_def = cake_define
  `w2i w = (if word_msb w then --(int_of_num (w2n (word_2comp w))) else
  int_of_num (w2n w))`;;
