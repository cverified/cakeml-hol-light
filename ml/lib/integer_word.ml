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
        "~" ++ num_to_dec_string (Num (~i)) else
        num_to_dec_string (Num i))`;;
let fromString_def = cake_define
  `(integer_word_fromString ((CHR 126) :: t) = ~&(num_from_dec_string
  t)) /\
   (integer_word_fromString ((CHR 45) :: t) = ~&(num_from_dec_string
     t)) /\
   (integer_word_fromString s = &(num_from_dec_string s))`;;
let w2i_def = cake_define
  `w2i w = (if word_msb w then ~(int_of_num (w2n (word_2comp w))) else
  int_of_num (w2n w))`;;
