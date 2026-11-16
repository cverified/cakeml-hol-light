(* ======================================================== *)
(*  ag32_prog: ported from HOL4's
    compiler/backend/ag32/proofs/ag32_progScript.sml
    A proof theory, with 13 definitions, 1 datatype and 23 theorems.
    Needed by ag32_ffi_codeProof.ml.  *)
(* ======================================================== *)

(*
  Defines an ag32 instantiation of the machine-code Hoare triple for
  the decompiler.
*)

needs "basis/basis_ffi.ml";;
needs "compiler/backend/ag32/ag32_memory.ml";;
needs "lib/alignment.ml";;
needs "lib/bitstring.ml";;
needs "lib/prog.ml";;
needs "lib/set_sep.ml";;
needs "lib/temporal_state.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_prog"
  ["ag32_memory"];;

let _ = do_list hide_constant ["post"; "seq"];;
(* HOL4 ancestors outside the port: ag32 *)

let v2w_F_T = prove
 (`(
    // TODO: move
    v2w [F] = (n2w 0)) /\ (v2w [T] = (n2w 1))`,
  CHEAT_TAC);;

(* basic definitions *)

let ag32_el_INDUCT,ag32_el_RECURSION = define_datatype
  "ag32_el =
     aState ag32_state
   | aMem word32 word8
   | aPc word32";;

(* HOL4 ag32_progScript.sml:32-33: ML code, not ported *)

new_type_abbrev("ag32_set",`:ag32_el->bool`);;

let ag32_instr_def = new_definition
  `ag32_instr (a,(w:word32)) =
   {aMem (a + (n2w 3)) ((31 >< 24) w),
     aMem (a + (n2w 2)) ((23 >< 16) w),
     aMem (a + (n2w 1)) ((15 >< 8) w),
     aMem (a + (n2w 0)) ((7 >< 0) w)}`;;

let ag32_proj'_def = new_definition
  `ag32_proj' (fs,ms,pc') (s:ag32_state) =
     (if fs then {aState s} else {}) UNION
     IMAGE (\a. aMem a (?_MEM s a)) ms UNION
     (if pc' then {aPc (?_PC s)} else {})`;;

let ag32_proj_def,ag32_proj_ind = define_guess
  `ag32_proj s = ag32_proj' (T,UNIV,T) s`;;
let ag32_proj''_def = new_definition
  `ag32_proj'' x s = ag32_proj s DIFF ag32_proj' x s`;;

let AG32_MODEL_def = new_definition
  `AG32_MODEL = ((ag32_proj,(\x y. y = Next x),ag32_instr,(=),K
  F):(ag32_state->ag32_el->bool)#(ag32_state->ag32_state->bool)#(word32
  #word32->ag32_el->bool)#(ag32_state->ag32_state->bool)#(ag32_state->bool))`;;

let aP_def = new_definition
  `aP x = SEP_EQ {aPc x}`;;
let aM_def = new_definition
  `aM a x = SEP_EQ {aMem a x}`;;
let aS_def = new_definition
  `aS x = SEP_EQ {aState x}`;;
let aB_def = new_definition
  `aB md m = SEP_EQ {aMem a (m a) | a IN md}`;;

let aD_def = new_definition
  `aD md = SEP_EXISTS (\m. aB md m)`;;
let aPC_def = new_definition
  `aPC x = aP x * cond (alignment_aligned 2 x)`;;

(* lemmas about proj *)

(* [local] *)
let ag32_proj'_SUBSET_ag32_proj = prove
 (`!y s. ag32_proj' y s SUBSET ag32_proj s`,
  CHEAT_TAC);;

(* [local] *)
let SPLIT_ag32_proj = prove
 (`!x s. SPLIT (ag32_proj s) (ag32_proj' x s,ag32_proj'' x s)`,
  CHEAT_TAC);;

(* HOL4 ag32_progScript.sml:103-104: ML code, not ported *)

(* [local] *)
let SUBSET_ag32_proj = prove
 (`!u s. u SUBSET ag32_proj s <=> (?y. u = ag32_proj' y s)`,
  CHEAT_TAC);;

(* [local] *)
let SPLIT_ag32_proj_EXISTS = prove
 (`!s u v. SPLIT (ag32_proj s) (u,v) =
           (?y. (u = ag32_proj' y s) /\ (v = ag32_proj'' y s))`,
  CHEAT_TAC);;

(* [local] *)
let IN_ag32_proj = prove
 (`(!x s. aPc x IN (ag32_proj s) <=> (x = ?_PC s)) /\
   (!x s. aPc x IN (ag32_proj' (fs,ms,pc) s) <=> (x = ?_PC s) /\ pc) /\
   (!x s. aPc x IN (ag32_proj'' (fs,ms,pc) s) <=> (x = ?_PC s) /\ ~pc) /\
   (!x s. aState x IN (ag32_proj s) <=> (x = s)) /\
   (!x s. aState x IN (ag32_proj' (fs,ms,pc) s) <=> (x = s) /\ fs) /\
   (!x s. aState x IN (ag32_proj'' (fs,ms,pc) s) <=> (x = s) /\ ~fs) /\
   (!p x s. aMem p x IN (ag32_proj s) <=> (x = ?_MEM s p)) /\
   (!p x s. aMem p x IN (ag32_proj' (fs,ms,pc) s) <=> (x = ?_MEM s p) /\ p
     IN ms) /\
   (!p x s. aMem p x IN (ag32_proj'' (fs,ms,pc) s) <=> (x = ?_MEM s p)
     /\ ~(p IN ms))`,
  CHEAT_TAC);;

(* [local] *)
let ag32_proj''_11 = prove
 (`!y y' s s'. (ag32_proj'' y' s' = ag32_proj'' y s) ==> (y = y')`,
  CHEAT_TAC);;

(* [local] *)
let DELETE_ag32_proj = prove
 (`(!s. (ag32_proj' (fs,ms,pc) s) DELETE aState s =
        (ag32_proj' (F,ms,pc) s)) /\
   (!b s. (ag32_proj' (fs,ms,pc) s) DELETE aMem b (?_MEM s b) =
          (ag32_proj' (fs,ms DELETE b,pc) s)) /\
   (!s. (ag32_proj' (fs,ms,pc) s) DELETE aPc (?_PC s) =
        (ag32_proj' (fs,ms,F) s))`,
  CHEAT_TAC);;

(* [local] *)
let EMPTY_ag32_proj = prove
 (`(ag32_proj' (fs,ms,pc) s = {}) <=> ~fs /\ (ms = {}) /\ ~pc`,
  CHEAT_TAC);;

(* theorems for construction of |- SPEC AG32_MODEL ... *)

(* HOL4 ag32_progScript.sml:197-200: ML code, not ported *)

let AG32_SPEC_SEMANTICS = prove
 (`SPEC AG32_MODEL p {} q =
    (!y s seq. p (ag32_proj' y s) /\ rel_sequence (\x y. y = Next x) seq s
      ==>
              (?k. q (ag32_proj' y (seq k)) /\
                  (ag32_proj'' y s = ag32_proj'' y (seq k))))`,
  CHEAT_TAC);;

let aD_STAR_ag32_proj = prove
 (`(aD md * p) (ag32_proj' (fs,ms,pc) s) <=>
      md SUBSET ms /\ p (ag32_proj' (fs,ms DIFF md,pc) s)`,
  CHEAT_TAC);;

let STAR_ag32_proj = prove
 (`((aS t * p) (ag32_proj' (fs,ms,pc) s) <=>
      (t = s) /\ fs /\ p (ag32_proj' (F,ms,pc) s)) /\
    ((aM b y * p) (ag32_proj' (fs,ms,pc) s) <=>
      (y = ?_MEM s b) /\ b IN ms /\ p (ag32_proj' (fs,ms DELETE b,pc) s)) /\
    ((aD md * p) (ag32_proj' (fs,ms,pc) s) <=>
      md SUBSET ms /\ p (ag32_proj' (fs,ms DIFF md,pc) s)) /\
    ((aP q * p) (ag32_proj' (fs,ms,pc) s) <=>
      (q = ?_PC s) /\ pc /\ p (ag32_proj' (fs,ms,F) s)) /\
    ((cond g * p) (ag32_proj' (fs,ms,pc) s) <=>
      g /\ p (ag32_proj' (fs,ms,pc) s))`,
  CHEAT_TAC);;

(* [local] *)
let CODE_POOL_ag32_proj_LEMMA = prove
 (`!x y z. (x = (z INSERT y)) <=> (z INSERT y) SUBSET x /\
           ((x DIFF (z INSERT y)) = {})`,
  CHEAT_TAC);;

(* [local] *)
let CODE_POOL_ag32_proj = prove
 (`CODE_POOL ag32_instr {(p,c)} (ag32_proj' (fs,ms,pc) s) <=>
     ({p + (n2w 3),p + (n2w 2),p + (n2w 1),p} = ms) /\ ~fs /\ ~pc /\
     (?_MEM s (p + (n2w 0)) = (7 >< 0) c) /\
     (?_MEM s (p + (n2w 1)) = (15 >< 8) c) /\
     (?_MEM s (p + (n2w 2)) = (23 >< 16) c) /\
     (?_MEM s (p + (n2w 3)) = (31 >< 24) c)`,
  CHEAT_TAC);;

(* HOL4 ag32_progScript.sml:296-299: the ML values that the definitions
   below antiquote *)

(* [local] *)
let IMP_AG32_SPEC_LEMMA = prove
 (`!p q.
     (!fs ms pc' s. ?s'.
       (p (ag32_proj' (fs,ms,pc') s) ==>
       (Next s = s') /\ q (ag32_proj' (fs,ms,pc') s') /\
       (ag32_proj'' (fs,ms,pc') s = ag32_proj'' (fs,ms,pc') s'))) ==>
     SPEC AG32_MODEL p {} q`,
  CHEAT_TAC);;

(* HOL4 ag32_progScript.sml:316: ML code, not ported *)
let BYTES_TO_WORD_LEMMA = prove
 (`!w. (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w`,
  CHEAT_TAC);;

(* HOL4 ag32_progScript.sml:323-326: a theorem that HOL4 states as the value
   of an ML expression: IMP_AG32_SPEC *)

let mem_unchanged_def = new_definition
  `mem_unchanged md m1 m2 = (!a. ~(a IN md) ==> m1 a = m2 a)`;;

let mem_unchanged_same = prove
 (`mem_unchanged md m m`,
  CHEAT_TAC);;
add_simp mem_unchanged_same;;

let ANY_AG32_SPEC_LEMMA = prove
 (`!w ast.
      ast = Decode w ==>
      mem_unchanged md (?_MEM (Run ast s)) (?_MEM s) ==>
      SPEC AG32_MODEL
        (aS s * aD md * aPC p)
        {(p,w)}
        (aS (Run ast s) * aD md * aP (?_PC (Run ast s)))`,
  CHEAT_TAC);;

let ANY_AG32_SPEC = prove
 (`!w ast.
      ast = Decode w ==>
      (alignment_aligned 2 (?_PC s) ==> alignment_aligned 2 (?_PC (Run ast
        s))) /\
      mem_unchanged md (?_MEM (Run ast s)) (?_MEM s) ==>
      SPEC AG32_MODEL
        (aS s * aD md * aPC p)
        {(p,w)}
        (aS (Run ast s) * aD md * aPC (?_PC (Run ast s)))`,
  CHEAT_TAC);;

let SPEC_AG32_FIX_POST_PC = prove
 (`SPEC AG32_MODEL (aS s * aD md * aPC p) c (post (?_PC s)) ==>
    SPEC AG32_MODEL (aS s * aD md * aPC p) c (post p)`,
  CHEAT_TAC);;

(* SPEC implies FUNPOW Next *)

let code_set_def,code_set_ind = define_guess
  `(code_set (a:word32) [] = {}) /\
   (code_set (a:word32) (CONS i is) = ((a:word32),i) INSERT code_set (a +
    (n2w 4)) is)`;;

let IN_code_set = prove
 (`!a xs p x.
      LENGTH xs < 2 EXP 30 ==>
      ((p,x) IN code_set a xs <=>
       (?i. p = a + n2w (4 * i) /\ x = EL i xs /\ i < LENGTH xs))`,
  CHEAT_TAC);;

(* HOL4 ag32_progScript.sml:436: ML code, not ported *)

let SPEC_IMP_FUNPOW_Next = prove
 (`SPEC AG32_MODEL
      (aS s * aD md * aPC (?_PC s))
      (code_set a (MAP Encode instr_list))
      (aS s1 * aD md1 * other) ==>
    LENGTH instr_list < 2 EXP 30 ==>
    (!k. k < LENGTH instr_list ==>
         (get_mem_word (?_MEM s) (a + n2w (4 * k)) =
          Encode (EL k instr_list))) /\
    byte_aligned (?_PC s) /\
    DISJOINT md {a + n2w k | k | k DIV 4 < LENGTH instr_list} ==>
    (?k. ITER k Next s = s1)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["post";
   "seq"];;

(* and the interface *)
let _ = unhide_overloads ();;
