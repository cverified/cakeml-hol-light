(* ======================================================== *)
(*  TextIOProg: ported from HOL4's
    basis/TextIOProgScript.sml
    A definition theory, with 10 definitions, 2 datatypes and no
    theorems.  Needed by SexpProg.ml, TextIOProof.ml and
    basis_ffi.ml.  *)
(* ======================================================== *)

(*
  Module for text-based I/O with the underlying file system.
*)

needs "basis/CommandLineProg.ml";;
needs "basis/Marshalling.ml";;
needs "basis/MarshallingProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "TextIOProg"
  ["CommandLineProg"; "MarshallingProg"; "ml_prog"; "ml_translator"];;

(* HOL4 TextIOProgScript.sml:11: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:13: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:15: ML code, not ported *)

let instream_INDUCT,instream_RECURSION = define_datatype
  "instream =
     Instream mlstring";;

let outstream_INDUCT,outstream_RECURSION = define_datatype
  "outstream =
     Outstream mlstring";;

let get_out_def = new_definition
  `get_out (Outstream s) = s`;;

let get_in_def = new_definition
  `get_in (Instream s) = s`;;

(* HOL4 TextIOProgScript.sml:33-36: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:38-45: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:47-49: the ML values that the definitions below
   antiquote *)

let instreambuffered_con_stamp_def,instreambuffered_con_stamp_ind =
  define_guess
  `instreambuffered_con_stamp = OPTION_MAP SND instreambuffered_con_stamp`;;
add_simp instreambuffered_con_stamp_def;;

(* HOL4 TextIOProgScript.sml:55-58: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:60: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:62-67: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:69-74: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:76: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:78-81: the ML values that the definitions below
   antiquote *)

let BadFileName_exn_def = new_definition
  `BadFileName_exn v = (v = semanticPrimitives_Conv (SOME ((implode
  "BadFileName"))) [])`;;

let InvalidFD_exn_def = new_definition
  `InvalidFD_exn v = (v = semanticPrimitives_Conv (SOME ((implode
  "InvalidFD"))) [])`;;

let EndOfFile_exn_def = new_definition
  `EndOfFile_exn v = (v = semanticPrimitives_Conv (SOME ((implode
  "EndOfFile"))) [])`;;

let IllegalArgument_exn_def = new_definition
  `IllegalArgument_exn v = (v = semanticPrimitives_Conv (SOME ((implode
  "IllegalArgument"))) [])`;;

(* HOL4 TextIOProgScript.sml:99-113: the ML values that the definitions
   below antiquote *)

(* HOL4 TextIOProgScript.sml:115: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:117: ML code, not ported *)

(* stdout, stderr *)

let stdOut_def = new_definition
  `stdOut = Outstream (implode (MAP (CHR o w2n) (n2w8 1)))`;;

let stdErr_def = new_definition
  `stdErr = Outstream (implode (MAP (CHR o w2n) (n2w8 2)))`;;

(* HOL4 TextIOProgScript.sml:129: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:131-133: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:135-137: ML code, not ported *)


(* HOL4 TextIOProgScript.sml:140: ML code, not ported *)

(* Note how we are in a local block: declarations are not exported. This is
   because we want to only expose the more efficient, buffered input to users. *)

let raw_stdIn_def = new_definition
  `raw_stdIn = Instream (implode (MAP (CHR o w2n) (n2w8 0)))`;;

(* HOL4 TextIOProgScript.sml:149: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:151-153: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:155-163: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:165-171: ML code, not ported *)

(* writei: higher-lever write function which calls #write until something is written or
* a filesystem error is raised and outputs the number of bytes written.
* It assumes that iobuff is initialised
* write: idem, but keeps writing until the whole (specified part of the) buffer
* is written *)
(* HOL4 TextIOProgScript.sml:178-195: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:197-205: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:207: ML code, not ported *)

(* Output functions on given file descriptor *)
(* HOL4 TextIOProgScript.sml:210-213: ML code, not ported *)

(* writes a string into a file *)
(* HOL4 TextIOProgScript.sml:216-220: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:222-225: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:227-235: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:237-243: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:245: ML code, not ported *)

(* wrapper for ffi call *)
(* HOL4 TextIOProgScript.sml:248-256: ML code, not ported *)

(* val raw_input : in_channel -> bytes -> int -> int -> int
* input ic buf pos len reads up to len characters from the given channel ic,
* storing them in byte sequence buf, starting at character number pos. *)
(* TODO: input0 as local fun *)
(* HOL4 TextIOProgScript.sml:262-271: ML code, not ported *)

(* helper function:
   extend a byte array, or, more accurately
   copy a byte array into a new one twice the size *)
(* HOL4 TextIOProgScript.sml:276-282: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:284: ML code, not ported *)

(*Buffered IO section*)

(*Open a buffered stdin with a buffer size of bsize.
  Force 1028 <= size < 256^2*)
(* HOL4 TextIOProgScript.sml:290-295: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:297-299: ML code, not ported *)

(*Open a buffered instream with a buffer size of bsize.
  Force 1028 <= size < 256^2*)
(* HOL4 TextIOProgScript.sml:303-312: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:314-316: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:318-322: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:324: ML code, not ported *)
(*input helper function for the case when there are
  enough bytes in instream buffer*)
(* HOL4 TextIOProgScript.sml:327-337: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:339: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:341-352: ML code, not ported *)
           (*If there arent enough bytes in the buffer: copy all of the bytes
           in the buffer and then refill it, and copy the remaining bytes *)
(* HOL4 TextIOProgScript.sml:355-359: ML code, not ported *)
           (*If there are enough bytes in the buffer, just copy them*)
(* HOL4 TextIOProgScript.sml:361-364: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:366: ML code, not ported *)

(* wrapper for ffi call *)
(* HOL4 TextIOProgScript.sml:369-377: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:379-385: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:387-395: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:397-406: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:408: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:410-416: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:418-424: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:426: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:428-435: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:437-452: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:454-459: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:461-473: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:475: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:477-479: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:481-483: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:485-491: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:493: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:495-500: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:502-507: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:509-514: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:516-527: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:529-542: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:544-554: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:556-566: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:568: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:570-573: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:575-583: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:585-592: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:594-596: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:598-606: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:608-611: ML code, not ported *)

(* TODO Maybe should be removed in favor of inputAllTokensFrom? *)
(* HOL4 TextIOProgScript.sml:614-622: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:624-632: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:634-644: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:646-656: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:658-668: ML code, not ported *)

(* HOL4 TextIOProgScript.sml:670-671: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
