(* ======================================================== *)
(*  alignment: ported from HOL4's
    src/n-bit/alignmentScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: words *)

let align_def = cake_define
  `align p (w:'a word) = (word_slice (dimindex (:'a) - 1) p) w`;;
let aligned_def = cake_define
  `alignment_aligned p w = (align p w = w)`;;

let byte_align_def = cake_define
  `byte_align (w:'a word) = align (LOG2 (dimindex (:'a) DIV 8)) w`;;

let byte_aligned_def = cake_define
  `byte_aligned (w:'a word) = alignment_aligned (LOG2 (dimindex (:'a)
  DIV 8)) w`;;
