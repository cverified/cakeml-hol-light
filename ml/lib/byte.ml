(* ======================================================== *)
(*  byte: ported from HOL4's
    src/n-bit/byteScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: arithmetic list words rich_list *)

let byte_index_def = new_definition
  `byte_index (a:'a word) is_bigendian =
     (let d = dimindex (:'a) DIV 8 in
       if is_bigendian then 8 * ((d - 1) - w2n a MOD d) else 8 *
         (w2n a MOD d))`;;

let get_byte_def = new_definition
  `get_byte (a:'a word) (w:'a word) is_bigendian =
     ((w2w (w >>> byte_index a is_bigendian)):word8)`;;

let set_byte_def = new_definition
  `set_byte (a:'a word) (b:word8) (w:'a word) is_bigendian =
     (let i = byte_index a is_bigendian in
       (
        word_slice_alt (dimindex (:'a)) (i + 8) w || w2w b << i ||
          word_slice_alt i 0 w))`;;

let bytes_in_word_def = new_definition
  `bytes_in_word = (n2w (dimindex (:'a) DIV 8):'a word)`;;

let word_of_bytes_def,word_of_bytes_ind = define_rec
  [`word_of_bytes be' a [] = (n2w 0)`;
   `word_of_bytes be' a (b :: bs) =
         set_byte a b (word_of_bytes be' (a + (n2w 1)) bs) be'`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let bytes_to_word_def,bytes_to_word_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x0)`
  [`bytes_to_word k a bs w be' =
     (if k = (0:num) then w else
       match bs with [] -> w | (b :: bs) -> set_byte a b
         (bytes_to_word (k - 1) (a + (n2w 1)) bs w be') be')`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let word_to_bytes_aux_def,word_to_bytes_aux_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x0)`
  [`// length, 'a word, endianness
    word_to_bytes_aux 0 (w:'a word) be' = []`;
   `word_to_bytes_aux (SUC n) (w:'a word) be' =
      (word_to_bytes_aux n w be') ++ [get_byte (n2w n) w be']`];;

let word_to_bytes_def = new_definition
  `word_to_bytes (w:'a word) be' =
   word_to_bytes_aux (dimindex (:'a) DIV 8) w be'`;;
