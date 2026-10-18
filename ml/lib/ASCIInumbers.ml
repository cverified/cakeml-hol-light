(* ======================================================== *)
(*  ASCIInumbers: ported from HOL4's
    src/string/ASCIInumbersScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by 6 files of the port.  *)
(* ======================================================== *)

needs "lib/numposrep.ml";;
(* HOL4 ancestors outside the port: string arithmetic list combin
   pair num rich_list logroot bit *)

let s2n_def = cake_define
  `s2n b f (s:string) = l2n b (MAP f (REVERSE s))`;;

let n2s_def = cake_define
  `(n2s b f n:string) = REVERSE (MAP f (n2l b n))`;;

let HEX = cake_define
  `HEX n = (if n < 10 then CHR (ORD (CHR 48) + n) else
           if n < 16 then CHR (ORD (CHR 65) + (n - 10)) else CHR
             0)`;;

let UNHEX = cake_define
  `UNHEX c =
     (let n = ORD c in
       if ORD (CHR 48) <= n /\ n <= ORD (CHR 57) then n - ORD (CHR
         48) else
       if ORD (CHR 97) <= n /\ n <= ORD (CHR 102) then (10 + n) - ORD
         (CHR 97) else
       if ORD (CHR 65) <= n /\ n <= ORD (CHR 70) then (10 + n) -
         ORD (CHR 65) else 0)`;;
let num_from_dec_string_def = cake_define
  `num_from_dec_string = s2n 10 UNHEX`;;
let num_from_hex_string_def = cake_define
  `num_from_hex_string = s2n 16 UNHEX`;;
let num_to_dec_string_def = cake_define
  `num_to_dec_string = n2s 10 HEX`;;
let num_to_hex_string_def = cake_define
  `num_to_hex_string = n2s 16 HEX`;;

hol4_overload "toString" "num_to_dec_string";;
