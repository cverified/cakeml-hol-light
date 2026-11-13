(* ======================================================== *)
(*  alignment: ported from HOL4's
    src/n-bit/alignmentScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 18 files of the port.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
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
