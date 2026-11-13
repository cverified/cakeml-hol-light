(* ======================================================== *)
(*  ASCIInumbers: ported from HOL4's
    src/string/ASCIInumbersScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 9 files of the port.  *)
(* ======================================================== *)

needs "lib/numposrep.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: string arithmetic list combin
   pair num rich_list logroot bit *)

let s2n_def = new_definition
  `s2n b f (s:string) = l2n b (MAP f (REVERSE s))`;;

let n2s_def = new_definition
  `(n2s b f n:string) = REVERSE (MAP f (n2l b n))`;;

let HEX = new_definition
  `HEX n = (if n < 10 then CHR (ORD (CHR 48) + n) else
           if n < 16 then CHR (ORD (CHR 65) + (n - 10)) else CHR
             0)`;;

let UNHEX = new_definition
  `UNHEX c =
     (let n = ORD c in
       if ORD (CHR 48) <= n /\ n <= ORD (CHR 57) then n - ORD (CHR
         48) else
       if ORD (CHR 97) <= n /\ n <= ORD (CHR 102) then (10 + n) - ORD
         (CHR 97) else
       if ORD (CHR 65) <= n /\ n <= ORD (CHR 70) then (10 + n) -
         ORD (CHR 65) else 0)`;;
let num_from_dec_string_def = new_definition
  `num_from_dec_string = s2n 10 UNHEX`;;
let num_from_hex_string_def = new_definition
  `num_from_hex_string = s2n 16 UNHEX`;;
let num_to_dec_string_def = new_definition
  `num_to_dec_string = n2s 10 HEX`;;
let num_to_hex_string_def = new_definition
  `num_to_hex_string = n2s 16 HEX`;;

(* HOL4 wordsScript.sml:76,114: the definitions of w2s and of
   word_to_hex_string, which the port has here because they need
   the n2s of this theory, while the words layer of the port is
   loaded before it *)

let w2s_def = new_definition
  `w2s b f (w:'a word) = n2s b f (w2n w)`;;

let word_to_hex_string_def = new_definition
  `word_to_hex_string = w2s 16 HEX`;;

hol4_overload "toString" "num_to_dec_string";;
(* HOL4 ASCIInumbersScript.sml:232: the overload toNum, which the
   port expands *)
