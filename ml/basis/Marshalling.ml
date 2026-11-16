(* ======================================================== *)
(*  Marshalling: ported from HOL4's
    basis/MarshallingScript.sml
    A definition theory, with 4 definitions and 6 theorems.  Needed
    by 9 files of the port.  *)
(* ======================================================== *)

(*
  HOL functions that aid converting to and from the byte arrays that
  CakeML foreign-function interface (FFI) uses.
*)

(* this file needs nothing of the port *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "Marshalling" [];;
(* HOL4 ancestors outside the port: words *)

(* encode/decode nums as 2 or 8 bytes *)
(* similar to n2l & l2n but with padding *)
let n2w2_def = new_definition
  `(n2w2 (i:num):word8 list) = [n2w (i DIV 256); n2w i]`;;

let n2w8_def = new_definition
  `(n2w8 (i:num):word8 list) =
    [n2w (i DIV 256 EXP 7); n2w (i DIV 256 EXP 6);
     n2w (i DIV 256 EXP 5); n2w (i DIV 256 EXP 4);
     n2w (i DIV 256 EXP 3); n2w (i DIV 256 EXP 2);
     n2w (i DIV 256); n2w i]`;;

let w22n_def = new_definition
  `w22n ([b1; b0]:word8 list) = w2n b1 * 256 + w2n b0`;;

let w82n_def = new_definition
  `w82n ([b7; b6; b5; b4; b3; b2; b1; b0]:word8 list) =
   256 * (256 * (256 * (256 * (256 * (256 * (256 *
   w2n b7 + w2n b6) + w2n b5) + w2n b4) + w2n b3) + w2n b2) + w2n b1) +
     w2n b0`;;

let w22n_n2w2 = prove
 (`!i. i < 2 EXP (2 * 8) ==> w22n (n2w2 i) = i`,
  CHEAT_TAC);;

let n2w2_w22n = prove
 (`!b. LENGTH b = 2 ==> n2w2 (w22n b) = b`,
  CHEAT_TAC);;

let w82n_n2w8 = prove
 (`!i. i <= 256 EXP 8 - 1 ==> w82n (n2w8 i) = i`,
  CHEAT_TAC);;


let nw8_w8n = prove
 (`!b. LENGTH b = 8 ==> n2w8 (w82n b) = b`,
  CHEAT_TAC);;

let LENGTH_n2w2 = prove
 (`!n. LENGTH (n2w2 n) = 2`,
  CHEAT_TAC);;

let LENGTH_n2w8 = prove
 (`!n. LENGTH (n2w8 n) = 8`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
