(* ================================================================== *)
(*  HOL4's words vocabulary, on top of HOL Light's Library/words.ml.  *)
(*                                                                    *)
(*  Where HOL Light has the same notion under another name, the HOL4  *)
(*  name                                                              *)
(*  is made an interface for it, so that no second constant is        *)
(*  introduced;                                                       *)
(*  the rest is defined in terms of HOL Light's words.                *)
(* ================================================================== *)

new_type_abbrev("word1",`:(1)word`);;
new_type_abbrev("word2",`:(2)word`);;
new_type_abbrev("word3",`:(3)word`);;
new_type_abbrev("word4",`:(4)word`);;
new_type_abbrev("word5",`:(5)word`);;
new_type_abbrev("word6",`:(6)word`);;
new_type_abbrev("word7",`:(7)word`);;
new_type_abbrev("word8",`:(8)word`);;
new_type_abbrev("word9",`:(9)word`);;
new_type_abbrev("word10",`:(10)word`);;
new_type_abbrev("word11",`:(11)word`);;
new_type_abbrev("word12",`:(12)word`);;
new_type_abbrev("word16",`:(16)word`);;
new_type_abbrev("word20",`:(20)word`);;
new_type_abbrev("word24",`:(24)word`);;
new_type_abbrev("word28",`:(28)word`);;
new_type_abbrev("word30",`:(30)word`);;
new_type_abbrev("word32",`:(32)word`);;
new_type_abbrev("word48",`:(48)word`);;
new_type_abbrev("word56",`:(56)word`);;
new_type_abbrev("word64",`:(64)word`);;
new_type_abbrev("word96",`:(96)word`);;
new_type_abbrev("word128",`:(128)word`);;

(* ------------------------------------------------------------------ *)
(* The HOL4 names of HOL Light's word operations.                     *)
(* ------------------------------------------------------------------ *)

override_interface("w2n",`val:(N)word->num`);;
override_interface("n2w",`word:num->(N)word`);;
override_interface("w2i",`ival:(N)word->int`);;
override_interface("i2w",`iword:int->(N)word`);;
override_interface("w2w",`word_zx:(M)word->(N)word`);;
override_interface("sw2sw",`word_sx:(M)word->(N)word`);;
override_interface("word_1comp",`word_not:(N)word->(N)word`);;
override_interface("word_2comp",`word_neg:(N)word->(N)word`);;
override_interface("word_lsl",`word_shl:(N)word->num->(N)word`);;
override_interface("word_lsr",`word_ushr:(N)word->num->(N)word`);;
override_interface("word_asr",`word_ishr:(N)word->num->(N)word`);;
override_interface("word_bit",`bit:num->(N)word->bool`);;
override_interface("word_div",`word_udiv:(N)word->(N)word->(N)word`);;
override_interface("word_mod",`word_umod:(N)word->(N)word->(N)word`);;
override_interface("word_lo",`word_ult:(N)word->(N)word->bool`);;
override_interface("word_ls",`word_ule:(N)word->(N)word->bool`);;
override_interface("word_hi",`word_ugt:(N)word->(N)word->bool`);;
override_interface("word_hs",`word_uge:(N)word->(N)word->bool`);;
override_interface("word_lt",`word_ilt:(N)word->(N)word->bool`);;
override_interface("word_le",`word_ile:(N)word->(N)word->bool`);;
override_interface("word_gt",`word_igt:(N)word->(N)word->bool`);;
override_interface("word_ge",`word_ige:(N)word->(N)word->bool`);;
override_interface("word_min",`word_umin:(N)word->(N)word->(N)word`);;
override_interface("word_max",`word_umax:(N)word->(N)word->(N)word`);;
override_interface("word_smin",`word_imin:(N)word->(N)word->(N)word`);;
override_interface("word_smax",`word_imax:(N)word->(N)word->(N)word`);;
override_interface("word_sdiv",`word_jdiv:(N)word->(N)word->(N)word`);;
override_interface("word_srem",`word_jrem:(N)word->(N)word->(N)word`);;

(* the bounds of a word type (the configurations of the targets) *)

override_interface("INT_MINw",`word_INT_MIN:(N)word`);;
override_interface("INT_MAXw",`word_INT_MAX:(N)word`);;
override_interface("UINT_MAXw",`word_UINT_MAX:(N)word`);;

(* ------------------------------------------------------------------ *)
(* HOL4 overloads the arithmetic operations for words, HOL Light does *)
(* not, so the port makes them overloaded.                            *)
(* ------------------------------------------------------------------ *)

overload_interface("+",`word_add:(N)word->(N)word->(N)word`);;
overload_interface("-",`word_sub:(N)word->(N)word->(N)word`);;
overload_interface("*",`word_mul:(N)word->(N)word->(N)word`);;
overload_interface("<",`word_ilt:(N)word->(N)word->bool`);;
overload_interface("<=",`word_ile:(N)word->(N)word->bool`);;
overload_interface(">",`word_igt:(N)word->(N)word->bool`);;
overload_interface(">=",`word_ige:(N)word->(N)word->bool`);;
overload_interface("--",`word_neg:(N)word->(N)word`);;
(* HOL4's / of two words is the unsigned division (asmSem's
   arith_upd divides the two registers of a Div) *)
overload_interface("/",`word_udiv:(N)word->(N)word->(N)word`);;

(* HOL4 writes the bit of a word as w ' i (the index of fcp),
   which ml/lib/finite_map.ml overloads FAPPLY with *)

let word_index = new_definition
  `word_index (w:(N)word) (i:num) <=> bit i w`;;

(* with the operations overloaded, a numeral whose type is not
   determined otherwise should still be a natural number *)

prioritize_num();;

(* ------------------------------------------------------------------ *)
(* The HOL4 notations.                                                *)
(* ------------------------------------------------------------------ *)

parse_as_infix("&&",(20,"right"));;
override_interface("&&",`word_and:(N)word->(N)word->(N)word`);;

parse_as_infix("||",(16,"right"));;
override_interface("||",`word_or:(N)word->(N)word->(N)word`);;

parse_as_infix("??",(16,"right"));;
override_interface("??",`word_xor:(N)word->(N)word->(N)word`);;

parse_as_infix("<<",(23,"left"));;
override_interface("<<",`word_shl:(N)word->num->(N)word`);;

parse_as_infix(">>",(23,"left"));;
override_interface(">>",`word_ishr:(N)word->num->(N)word`);;

parse_as_infix(">>>",(23,"left"));;
override_interface(">>>",`word_ushr:(N)word->num->(N)word`);;

parse_as_infix("#>>",(23,"left"));;
override_interface("#>>",`word_ror:(N)word->num->(N)word`);;

parse_as_infix("#<<",(23,"left"));;
override_interface("#<<",`word_rol:(N)word->num->(N)word`);;

parse_as_infix("<+",(12,"right"));;
override_interface("<+",`word_ult:(N)word->(N)word->bool`);;

parse_as_infix("<=+",(12,"right"));;
override_interface("<=+",`word_ule:(N)word->(N)word->bool`);;

parse_as_infix(">+",(12,"right"));;
override_interface(">+",`word_ugt:(N)word->(N)word->bool`);;

parse_as_infix(">=+",(12,"right"));;
override_interface(">=+",`word_uge:(N)word->(N)word->bool`);;

parse_as_infix("//",(22,"left"));;
override_interface("//",`word_udiv:(N)word->(N)word->(N)word`);;

(* ------------------------------------------------------------------ *)
(* The HOL4 operations that HOL Light does not have.                  *)
(* ------------------------------------------------------------------ *)

let word_msb = new_definition
  `word_msb (w:(N)word) <=> bit (dimindex(:N) - 1) w`;;

let word_lsb = new_definition
  `word_lsb (w:(N)word) <=> bit 0 w`;;

let word_bits = new_definition
  `word_bits h l (w:(N)word) = (word_subword w (l,h + 1 - l):(N)word)`;;

parse_as_infix("><",(23,"left"));;

let word_extract = new_definition
  `((><) h l (w:(M)word)):(N)word = word_subword w (l,h + 1 - l)`;;

let word_slice = new_definition
  `word_slice h l (w:(N)word) = word_shl (word_bits h l w) l`;;

parse_as_infix("@@",(23,"left"));;

let word_concat = new_definition
  `((@@) (v:(M)word) (w:(N)word)):(P)word =
   word_zx (word_join v w : ((M,N)finite_sum)word)`;;

let bit_field_insert = new_definition
  `bit_field_insert h l (v:(M)word) (w:(N)word) =
   (word_insert w (l,h + 1 - l) v:(N)word)`;;

let word_reverse = new_definition
  `word_reverse (w:(N)word) =
   word_of_bits {i | i < dimindex(:N) /\ bit (dimindex(:N) - 1 - i)
     w}`;;

let word_slice_alt = new_definition
  `word_slice_alt h l (w:(N)word) =
   word_shl (word_subword w (l,h - l):(N)word) l`;;

let word_abs = new_definition
  `word_abs (w:(N)word) = if word_msb w then word_neg w else w`;;

let word_log2 = new_definition
  `word_log2 (w:(N)word) =
   (word (dimindex(:N) - 1 - word_clz w):(N)word)`;;

(* the numbers that bound a word type, as HOL4 defines them *)

let dimword = new_definition
  `dimword (:N) = 2 EXP dimindex(:N)`;;

let INT_MIN = new_definition
  `INT_MIN (:N) = 2 EXP (dimindex(:N) - 1)`;;

let INT_MAX = new_definition
  `INT_MAX (:N) = INT_MIN (:N) - 1`;;

let UINT_MAX = new_definition
  `UINT_MAX (:N) = dimword (:N) - 1`;;

(* HOL4's integer_wordTheory has an INT_MAX and an INT_MIN of its
   own (integer_wordScript.sml:43-49): the integers that a word of
   the type can hold, where the ones of wordsTheory above are
   numbers.  Both names are overloaded with both constants, as
   HOL4 has them, and the type says which one a statement means
   (the ones of this theory keep their place in front, so a
   number is a number). *)

let integer_word_INT_MAX = new_definition
  `integer_word_INT_MAX (:N) = ((&(INT_MIN (:N)) - &1):int)`;;

let integer_word_INT_MIN = new_definition
  `integer_word_INT_MIN (:N) =
   ((--(integer_word_INT_MAX (:N)) - &1):int)`;;

hol4_overload "INT_MAX" "INT_MAX";;
hol4_overload "INT_MIN" "INT_MIN";;
hol4_overload_last "INT_MAX" "integer_word_INT_MAX";;
hol4_overload_last "INT_MIN" "integer_word_INT_MIN";;

let word_L = new_definition
  `word_L = (word (INT_MIN (:N)):(N)word)`;;

let word_H = new_definition
  `word_H = (word (INT_MAX (:N)):(N)word)`;;

let word_T = new_definition
  `word_T = (word (UINT_MAX (:N)):(N)word)`;;

(* the bit list of a word and back, as in HOL4's bitstringTheory *)

let w2v = new_definition
  `w2v (w:(N)word) =
   list_of_seq (\i. bit (dimindex(:N) - 1 - i) w) (dimindex(:N))`;;

let v2w = new_definition
  `v2w l = (word (ITLIST (\b n. 2 * n + (if b then 1 else 0))
                         (REVERSE l) 0):(N)word)`;;

(* the facts about dimword that termination proofs need, as HOL4's
   ONE_LT_dimword and DIV_LT_X do *)

let ONE_LT_dimword = prove
 (`1 < dimword(:N)`,
  REWRITE_TAC[dimword; ARITH_RULE `1 = 2 EXP 0`] THEN
  SIMP_TAC[LT_EXP; LE_1; DIMINDEX_GE_1] THEN ARITH_TAC);;

let DIV_LT_dimword = prove
 (`!n. ~(n = 0) ==> n DIV dimword(:N) < n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT_SELF THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC_ALL ONE_LT_dimword) THEN
  ARITH_TAC);;

cake_term_lemmas := DIV_LT_dimword :: (!cake_term_lemmas);;
