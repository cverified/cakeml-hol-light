(* ======================================================== *)
(*  byte: ported from HOL4's
    src/n-bit/byteScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: arithmetic list words rich_list *)

let byte_index_def = cake_define
  `byte_index (a:'a word) is_bigendian =
     (let d = dimindex (:'a) DIV 8 in
       if is_bigendian then 8 * ((d - 1) - w2n a MOD d) else 8 *
         (w2n a MOD d))`;;

let get_byte_def = cake_define
  `get_byte (a:'a word) (w:'a word) is_bigendian =
     ((w2w (w >>> byte_index a is_bigendian)):word8)`;;

let set_byte_def = cake_define
  `set_byte (a:'a word) (b:word8) (w:'a word) is_bigendian =
     (let i = byte_index a is_bigendian in
       (
        word_slice_alt (dimindex (:'a)) (i + 8) w || w2w b << i ||
          word_slice_alt i 0 w))`;;

let bytes_in_word_def = cake_define
  `bytes_in_word = (n2w (dimindex (:'a) DIV 8):'a word)`;;

let word_of_bytes_def = cake_define
  `(word_of_bytes be a [] = (n2w 0)) /\
   (word_of_bytes be a (b :: bs) =
      set_byte a b (word_of_bytes be (a + (n2w 1)) bs) be)`;;

let bytes_to_word_def = cake_define
  `bytes_to_word k a bs w be =
     (if k = (0:num) then w else
       match bs with [] -> w | (b :: bs) -> set_byte a b
         (bytes_to_word (k - 1) (a + (n2w 1)) bs w be) be)`;;

let word_to_bytes_aux_def = cake_define
  `word_to_bytes_aux 0 (w:'a word) be = [] /\
   word_to_bytes_aux (SUC n) w be =
     (word_to_bytes_aux n w be) ++ [get_byte (n2w n) w be]`;;

let word_to_bytes_def = cake_define
  `word_to_bytes (w:'a word) be =
   word_to_bytes_aux (dimindex (:'a) DIV 8) w be`;;
