(* ======================================================== *)
(*  ag32_ffi_codeProof: ported from HOL4's
    compiler/backend/ag32/proofs/ag32_ffi_codeProofScript.sml
    A proof theory, with 6 definitions and 51 theorems.  Needed by
    ag32BootstrapProof.ml and ag32_basis_ffiProof.ml.  *)
(* ======================================================== *)

(*
  Verify the deep embeddings of the ag32 implementation of the CakeML
  basis FFI primitives.
*)

needs "basis/Marshalling.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/ag32/ag32_memory.ml";;
needs "compiler/backend/ag32/proofs/ag32_prog.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/encoders/ag32/proofs/ag32_targetProof.ml";;
needs "lib/alignment.ml";;
needs "lib/bitstring.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_ffi_codeProof"
  ["ag32_memory"; "ag32_prog"; "ag32_targetProof"];;

let _ = do_list hide_constant ["cf"; "not"];;

(* TODO: move *)

let byte_aligned_imp = prove
 (`byte_aligned (x:word32) ==>
   (((((31 >< 2) x):word30) @@ ((n2w 0):word2)) = x)`,
  CHEAT_TAC);;

(* -- *)

let extcalls_def,extcalls_ind = define_guess
  `extcalls x1 =
   match x1 with
     NONE -> []
   | SOME [] -> []
   | SOME (CONS (ffi_ExtCall n) xs) -> CONS n (extcalls (SOME xs))
   | SOME (CONS _ xs) -> extcalls (SOME xs)`;;

(* HOL4 ag32_ffi_codeProofScript.sml:37-63: a proof *)

(* HOL4 ag32_ffi_codeProofScript.sml:65-114: a proof *)

let ag32_ffi_return_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_return_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_return_code))) /\ byte_aligned (ag32_state_PC
           s) ==>
   (?k. (ITER k Next s = ag32_ffi_return s))`,
  CHEAT_TAC);;

let ag32_ffi_copy_code_thm = prove
 (`!s.
   (!k. k < LENGTH ag32_ffi_copy_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_copy_code))) /\
   byte_aligned (ag32_state_PC s) /\
   w2n (ag32_state_PC s) + 4 * LENGTH ag32_ffi_copy_code < dimword (:32) /\
   w2n (ag32_state_R s (n2w 5)) + w2n (ag32_state_R s (n2w 1)) < dimword
     (:32) /\ DISJOINT {ag32_state_R s (n2w 5) + n2w k | k | k < w2n
     (ag32_state_R s (n2w 1))}
              {ag32_state_PC s + n2w k | k | k DIV 4 < LENGTH
                ag32_ffi_copy_code} ==>
   (?k. (ITER k Next s = ag32_ffi_copy s))`,
  CHEAT_TAC);;


(* HOL4 ag32_ffi_codeProofScript.sml:390: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:392-409: ML code, not ported *)

(* [local] *)
let ltNumeral = prove
 (`(x < NUMERAL (BIT2 n) <=> x < NUMERAL (BIT1 n) \/ x = NUMERAL (BIT1 n)) /\
    (x < NUMERAL (BIT1 n) <=>
       x < PRE (NUMERAL (BIT1 n)) \/ x = PRE (NUMERAL (BIT1 n)))`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:419-430: a proof *)

(* HOL4 ag32_ffi_codeProofScript.sml:432: ML code, not ported *)

(* [local] *)
let sub_common = prove
 (`u <= v ==> ((x:word32) + (n2w u) = y + (n2w v) <=> x = y + n2w (v - u))`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:442-445: a proof *)

(* HOL4 ag32_ffi_codeProofScript.sml:447-462: a proof *)

(* HOL4 ag32_ffi_codeProofScript.sml:464-469: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:471-475: ML code, not ported *)

let v2w_EQ0 = prove
 (`v2w [b] = ((n2w 0):word32) <=> ~b`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:483-490: a proof *)

(* HOL4 ag32_ffi_codeProofScript.sml:492-509: a proof *)

(* HOL4 ag32_ffi_codeProofScript.sml:511: the overload align4, which the
   port expands *)

let ag32_ffi_read_num_written_code_thm = prove
 (`~(ag32_state_R
   s (n2w 3) IN
   {ag32_state_PC s + n2w k | k | k DIV 4 < LENGTH
     ag32_ffi_read_num_written_code}) /\ ~((\(w:word32). (((31 >< 2) w):30
     word):word32) (w2w (n2w stdin_offset:23 word)) IN
      {ag32_state_PC s + n2w k | k | k DIV 4 < LENGTH
        ag32_ffi_read_num_written_code}) /\
   (!k. k < LENGTH ag32_ffi_read_num_written_code ==>
        get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
        Encode (EL k ag32_ffi_read_num_written_code)) /\
   byte_aligned (ag32_state_PC s) ==>
   (?k. ITER k Next s = ag32_ffi_read_num_written s)`,
  CHEAT_TAC);;

let ag32_ffi_write_set_id_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_write_set_id_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_set_id_code))) /\
   byte_aligned (ag32_state_PC s) ==>
   (?k. (ITER k Next s = ag32_ffi_write_set_id s))`,
  CHEAT_TAC);;

let ag32_ffi_write_check_conf_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_write_check_conf_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_check_conf_code))) /\ byte_aligned
           (ag32_state_PC s) ==>
   (?k. (ITER k Next s = ag32_ffi_write_check_conf s))`,
  CHEAT_TAC);;

let ag32_ffi_write_load_noff_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_write_load_noff_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_load_noff_code))) /\ byte_aligned
           (ag32_state_PC s) ==>
   (?k. (ITER k Next s = ag32_ffi_write_load_noff s))`,
  CHEAT_TAC);;

let ag32_ffi_write_check_lengths_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_write_check_lengths_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_check_lengths_code))) /\ byte_aligned
           (ag32_state_PC s) ==>
   (?k. (ITER k Next s = ag32_ffi_write_check_lengths s))`,
  CHEAT_TAC);;

let ag32_ffi_write_write_header_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_write_write_header_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_write_header_code))) /\
   (ag32_state_PC s =
       n2w (
            ffi_code_start_offset + ag32_ffi_write_entrypoint + 4 * (LENGTH
              ag32_ffi_write_set_id_code) + 4 * (LENGTH
              ag32_ffi_write_check_conf_code) + 4 * (LENGTH
              ag32_ffi_write_load_noff_code) + 4 * (LENGTH
              ag32_ffi_write_check_lengths_code))) /\ (ag32_state_R s (n2w 5) =
              n2w output_offset) ==>
   (?k. (ITER k Next s = ag32_ffi_write_write_header s))`,
  CHEAT_TAC);;

let ag32_ffi_write_num_written_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_write_num_written_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_num_written_code))) /\
   byte_aligned (ag32_state_PC s) /\
   w2n (ag32_state_PC s) + 4 * LENGTH ag32_ffi_write_num_written_code <
     dimword (:32) /\
   (!k. k DIV 4 < LENGTH ag32_ffi_write_num_written_code ==> ~(ag32_state_R
     s (n2w 3) + (n2w 1) = ag32_state_PC s + n2w k)) /\ (!k. k DIV 4 < LENGTH
     ag32_ffi_write_num_written_code ==> ~(ag32_state_R s (n2w 3) + (n2w 2) =
     ag32_state_PC s + n2w k)) ==>
   (?k. (ITER k Next s = ag32_ffi_write_num_written s))`,
  CHEAT_TAC);;

let ag32_ffi_write_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_write_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_code))) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_write_entrypoint)) /\
   bytes_in_memory (ag32_state_R s (n2w 1)) conf (ag32_state_MEM s) md /\
   (w2n (ag32_state_R s (n2w 2)) = LENGTH conf) /\
   bytes_in_memory (ag32_state_R s (n2w 3)) (CONS n1 (CONS n0 (CONS off1
     (CONS off0 tll)))) (ag32_state_MEM s) md /\
   (w2n (ag32_state_R s (n2w 4)) = 4 + LENGTH tll) /\
   w2n (ag32_state_R s (n2w 3)) + 4 + LENGTH tll < dimword (:32) /\
   // not sure whether/why this is needed: can't get from bytes_in_memory?
   DISJOINT md {ag32_state_PC s + n2w k | k | k DIV 4 < LENGTH
     ag32_ffi_write_code} /\
   DISJOINT md {w | n2w startup_code_size <=+ w /\ w <+ n2w
     heap_start_offset} ==>
   // ∧ md ⊆ { w | w | r0 <+ w ∧ r0 + w <=+ r0 + n2w memory_size }
   (?k. (ITER k Next s = ag32_ffi_write s))`,
  CHEAT_TAC);;

let ag32_ffi_read_set_id_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_read_set_id_code ==>
         get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_set_id_code)) /\ byte_aligned
           (ag32_state_PC s) ==>
   (?k. ITER k Next s = ag32_ffi_read_set_id s)`,
  CHEAT_TAC);;

let ag32_ffi_read_check_conf_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_read_check_conf_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_check_conf_code))) /\ byte_aligned
           (ag32_state_PC s) ==>
   (?k. (ITER k Next s = ag32_ffi_read_check_conf s))`,
  CHEAT_TAC);;

let ag32_ffi_read_load_lengths_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_read_load_lengths_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_load_lengths_code))) /\ byte_aligned
           (ag32_state_PC s) ==>
   (?k. (ITER k Next s = ag32_ffi_read_load_lengths s))`,
  CHEAT_TAC);;

let ag32_ffi_read_check_length_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_read_check_length_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_check_length_code))) /\ byte_aligned
           (ag32_state_PC s) ==>
   (?k. (ITER k Next s = ag32_ffi_read_check_length s))`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2330-2331: the ML values that the
   definitions below antiquote *)

(* HOL4 ag32_ffi_codeProofScript.sml:2333-2337: ML code, not ported *)

(* [local] *)
let bytes_in_memory_update = prove
 (`!bs a. ~(k IN md) /\ bytes_in_memory a bs mf md ==>
           bytes_in_memory a bs ((k =+ v) mf) md`,
  CHEAT_TAC);;

(* [local] *)
let bytes_in_memory_prefix = prove
 (`!bs sfx a. bytes_in_memory a (APPEND bs sfx) mf md ==>
               bytes_in_memory a bs mf md`,
  CHEAT_TAC);;

(* [local] *)
let asm_write_bytearray_avoiding = prove
 (`!a bs. ~(x IN {a + n2w i | i < LENGTH bs}) ==> asm_write_bytearray a bs f
  x = f x`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2365: ML code, not ported *)

let w22n_bound = prove
 (`!b1 b2. w22n [b1; b2] < 65536`,
  CHEAT_TAC);;

(* [local] *)
let ltSUC = prove
 (`x < SUC y <=> x = 0 \/ (?x0. x = SUC x0 /\ x0 < y)`,
  CHEAT_TAC);;

(* [local] *)
let n2w_o_SUC = prove
 (`n2w o SUC = word_add (n2w 1) o n2w`,
  CHEAT_TAC);;

(* [local] *)
let word_add_o = prove
 (`word_add m o (word_add n o f) = word_add (m + n) o f`,
  CHEAT_TAC);;


let bytes_in_memory_GENLIST = prove
 (`!sz base f.
      bytes_in_memory base (list_of_seq (m o word_add base o n2w) sz) m md
        <=>
      (!a. a < sz ==> base + n2w a IN md)`,
  CHEAT_TAC);;

(* [local] *)
let WORD_ADD_CANCEL_LBARE = prove
 (`y <= x ==> (n2w x = n2w y + z <=> z = n2w (x - y))`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2414-2416: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:2418-2426: a proof *)

(* HOL4 ag32_ffi_codeProofScript.sml:2428-2436: ML code, not ported *)

let ag32_ffi_read_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_read_code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_code))) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_read_entrypoint)) /\
   bytes_in_memory (ag32_state_R s (n2w 1)) conf (ag32_state_MEM s) md /\
   (w2n (ag32_state_R s (n2w 2)) = LENGTH conf) /\
   bytes_in_memory (ag32_state_R s (n2w 3)) (CONS n1 (CONS n0 (CONS off1
     (CONS off0 tll)))) (ag32_state_MEM s) md /\
   (w2n (ag32_state_R s (n2w 4)) = 4 + LENGTH tll) /\
   w2n (ag32_state_R s (n2w 3)) + 4 + LENGTH tll < dimword (:32) /\
   // not sure whether/why this is needed: can't get from bytes_in_memory?
   w2n (get_mem_word (ag32_state_MEM s) (n2w stdin_offset)) <=
     w2n (get_mem_word (ag32_state_MEM s) (n2w (stdin_offset + 4))) /\
   w2n (get_mem_word (ag32_state_MEM s) (n2w (stdin_offset + 4))) <=
     stdin_size /\
   w2n (ag32_state_R s (n2w 3) + (n2w 4)) + output_buffer_size + 1 <
     4294967296 /\
   output_buffer_size + stdin_size + stdin_offset + 8 <= w2n (ag32_state_R s
     (n2w 3)) /\
   DISJOINT md {ag32_state_PC s + n2w k | k | k DIV 4 < LENGTH
     ag32_ffi_read_code} /\
   DISJOINT md {w | n2w startup_code_size <=+ w /\ w <+ n2w
     heap_start_offset} ==>
   (?k. (ITER k Next s = ag32_ffi_read s))`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2842-2844: ML code, not ported *)

(* [local] *)
let ag32_ffi_return_LET = prove
 (`ag32_ffi_return (LET f v) = LET (ag32_ffi_return o f) v`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2852-2853: the ML values that the
   definitions below antiquote *)

(* [local] *)
let div_lemma = prove
 (`0 < c ==> (c * x + y) DIV c = x + y DIV c /\ (c * x) DIV c = x`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2861-2864: ML code, not ported *)

let ag32_ffi_get_arg_count_code_thm = prove
 (`~(ag32_state_R
   s (n2w 3) IN
     {ag32_state_PC s + n2w k | k | k DIV 4 < LENGTH
       ag32_ffi_get_arg_count_code}) /\
   (!k. k < LENGTH ag32_ffi_get_arg_count_code ==>
      (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
       Encode (EL k ag32_ffi_get_arg_count_code))) /\
   byte_aligned (ag32_state_PC s) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_get_arg_count_entrypoint)) ==>
   (?k. (ITER k Next s = ag32_ffi_get_arg_count s))`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2920: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:2922-2925: ML code, not ported *)

let ag32_ffi_get_arg_length_setup_code_thm = prove
 (`~(w2w (n2w (ffi_code_start_offset - 1):23 word) IN
        {ag32_state_PC s + n2w k | k |
          k DIV 4 < LENGTH ag32_ffi_get_arg_length_setup_code}) /\
      (!k. k < LENGTH ag32_ffi_get_arg_length_setup_code ==>
           get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
           Encode (EL k ag32_ffi_get_arg_length_setup_code)) /\
      byte_aligned (ag32_state_PC s) ==>
      (?k. ITER k Next s = ag32_ffi_get_arg_length_setup s)`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_length_loop1_code_def = new_definition
  `ag32_ffi_get_arg_length_loop1_code =
     list_of_seq (\i. EL (i + 2) ag32_ffi_get_arg_length_loop_code) 4`;;

(* HOL4 ag32_ffi_codeProofScript.sml:2954-2957: ML code, not ported *)

let ag32_ffi_get_arg_length_loop1_code_thm = prove
 (`ag32_state_MEM
      s (ag32_state_R s (n2w 5) + n2w zoff) = (n2w 0) /\
      (!k. k < LENGTH ag32_ffi_get_arg_length_loop1_code ==>
           get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
           Encode (EL k ag32_ffi_get_arg_length_loop1_code)) /\
      byte_aligned (ag32_state_PC s) ==>
      (?k. ITER k Next s = ag32_ffi_get_arg_length_loop1 s)`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:2988-2995: ML code, not ported *)


(* HOL4 ag32_ffi_codeProofScript.sml:2999-3000: ML code, not ported *)

let has_n_args_def = define_cases
  `(has_n_args (mem':word32->word8) a 0 <=> T) /\
   (has_n_args (mem':word32->word8) a (SUC n) <=>
         (?off. mem' (a + n2w off) = (n2w 0) /\
               (!i. i < off ==> ~(mem' (a + n2w i) = (n2w 0))) /\
               has_n_args mem' (a + n2w off + (n2w 1)) n))`;;

let ag32_ffi_get_arg_length_loop_code_thm = prove
 (`has_n_args (ag32_state_MEM s) (ag32_state_R s (n2w 5)) argc /\ w2n
  (ag32_state_R s (n2w 6)) <= argc /\
   (!k. k < LENGTH ag32_ffi_get_arg_length_loop_code ==>
        get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
        Encode (EL k ag32_ffi_get_arg_length_loop_code)) /\
   byte_aligned (ag32_state_PC s) ==>
   (?k. ITER k Next s = ag32_ffi_get_arg_length_loop s)`,
  CHEAT_TAC);;

(* ag32_ffi_get_arg_length *)

(*
val (ag32_ffi_get_arg_length_setup_SPEC,
     ag32_ffi_get_arg_length_setup_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_length_setup_code_def

val (ag32_ffi_get_arg_length_loop_SPEC,
     ag32_ffi_get_arg_length_loop_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_length_loop_code_def
*)

(* HOL4 ag32_ffi_codeProofScript.sml:3075-3077: ML code, not ported *)

let ag32_ffi_get_arg_length_store_decomp_thm = prove
 (`FST (ag32_ffi_get_arg_length_store_decomp (s,md)) =
  ag32_ffi_get_arg_length_store s`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:3086-3089: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3091-3132: code that the source has in
   a comment *)

let ag32_ffi_get_arg_length_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_get_arg_length_code ==>
      (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
       Encode (EL k ag32_ffi_get_arg_length_code))) /\
   byte_aligned (ag32_state_PC s) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_get_arg_length_entrypoint)) /\
   bytes_in_memory (ag32_state_R s (n2w 3)) [l0; l1] (ag32_state_MEM s) md
     /\ ~(n2w (ffi_code_start_offset - 1) IN md) /\
   (!j. j < 4 * LENGTH ag32_ffi_get_arg_length_code ==>
        ~(n2w (ffi_code_start_offset + ag32_ffi_get_arg_length_entrypoint +
          j) IN md)) /\
   w2n l0 + 256 * w2n l1 <= cline_size /\
   LENGTH (SND (get_mem_arg ((n2w (ffi_code_start_offset - 1) =+ n2w (THE
     (ALOOKUP FFI_codes (implode "get_arg_length")))) (ag32_state_MEM s))
     (n2w (startup_code_size + 4)) (w2n l0 + 256 * w2n l1))) < dimword (:32)
       /\
   has_n_args ((n2w (ffi_code_start_offset - 1) =+ n2w (THE (ALOOKUP
     FFI_codes (implode "get_arg_length")))) (ag32_state_MEM s))
     (n2w (startup_code_size + 4)) (w2n l0 + (256 * w2n l1) + 1) ==>
   (?k. (ITER k Next s = ag32_ffi_get_arg_length s))`,
  CHEAT_TAC);;

(* ag32_ffi_get_arg *)

(* HOL4 ag32_ffi_codeProofScript.sml:3345-3347: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3349-3351: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3353-3355: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3357-3361: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3363-3370: ML code, not ported *)

let ag32_ffi_get_arg_setup_decomp_thm = prove
 (`FST (ag32_ffi_get_arg_setup_decomp (s,md)) = ag32_ffi_get_arg_setup s`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_find_decomp1_thm = prove
 (`!s.
    (?n. ag32_state_MEM s (ag32_state_R s (n2w 5) + n2w n) = (n2w 0)) ==>
    (ag32_ffi_get_arg_find_decomp1 s = ag32_ffi_get_arg_find1 s)`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_find_decomp_thm = prove
 (`!s. (?n. ag32_state_MEM s (ag32_state_R s (n2w 5) + n2w n) = (n2w 0)) ==>
  (FST (ag32_ffi_get_arg_find_decomp (s,md)) = ag32_ffi_get_arg_find s)`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_store_decomp_thm = prove
 (`!s.
    (?n. ag32_state_MEM s (ag32_state_R s (n2w 5) + n2w n) = (n2w 0) /\
         (!i. i <= n ==> ~(ag32_state_R s (n2w 3) = ag32_state_R s (n2w 5) +
           n2w i))) ==>
    FST (ag32_ffi_get_arg_store_decomp (s,md)) = ag32_ffi_get_arg_store s`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_find_decomp1_pre' = prove
 (`!off s. ag32_state_MEM
     s (ag32_state_R s (n2w 5) + n2w off) = (n2w 0) ==>
       ag32_ffi_get_arg_find_decomp1_pre s`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_find_decomp_pre' = prove
 (`!c md s.
     has_n_args (ag32_state_MEM s) (ag32_state_R s (n2w 5)) c /\ w2n
       (ag32_state_R s (n2w 6)) <= c ==>
     ag32_ffi_get_arg_find_decomp_pre (s,md)`,
  CHEAT_TAC);;

let SND_ag32_ffi_get_arg_find_decomp = prove
 (`!p. (?n. ag32_state_MEM (FST p) (ag32_state_R (FST p) (n2w 5) + n2w n) =
  (n2w 0)) ==> SND (ag32_ffi_get_arg_find_decomp p) = SND p`,
  CHEAT_TAC);;

(* [local] *)
let ag32_ffi_get_arg_setup_decomp_thm' = prove
 (`ag32_ffi_get_arg_setup_decomp (s,md) = (ag32_ffi_get_arg_setup s,md)`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:3597-3612: ML code, not ported *)

let ag32_ffi_get_arg_store_decomp_pre' = prove
 (`!n md s.
     (ag32_state_MEM s (ag32_state_R s (n2w 5) + n2w n) = (n2w 0)) /\
     (!i. i <= n ==> ~(ag32_state_R s (n2w 3) = ag32_state_R s (n2w 5) + n2w
       i)) /\
     (!i. i <= n ==> ag32_state_R s (n2w 3) + n2w i IN md) ==>
     ag32_ffi_get_arg_store_decomp_pre (s,md)`,
  CHEAT_TAC);;

let ag32_ffi_get_arg_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_get_arg_code ==>
      (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
       Encode (EL k ag32_ffi_get_arg_code))) /\
   byte_aligned (ag32_state_PC s) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_get_arg_entrypoint)) /\
   bytes_in_memory (ag32_state_R s (n2w 3)) [l0; l1] (ag32_state_MEM s) md
     /\ ~(n2w (ffi_code_start_offset - 1) IN md) /\
   256 * w2n l1 + w2n l0 <= cline_size /\
   (let m1 = ((n2w (ffi_code_start_offset - 1) =+ (n2w (THE (ALOOKUP
     FFI_codes (implode "get_arg"))))) (ag32_state_MEM s)) in
    let a = (n2w (startup_code_size + 4)) in
    let index = (256 * w2n l1 + w2n l0) in
    let start' = (if 0 < index then FST (get_mem_arg m1 a (index - 1)) +
      (n2w 1) else a) in
    has_n_args m1 a (SUC index) /\
    (?n. m1 (start' + n2w n) = (n2w 0) /\
        (!i. i <= n ==> ~(ag32_state_R s (n2w 3) = start' + n2w i)) /\
        (!i. i <= n ==> ~(ag32_state_R s (n2w 3) + n2w i IN {ag32_state_PC s
          + n2w k | k | k < 4 * LENGTH ag32_ffi_get_arg_code})))) ==>
   (?k. (ITER k Next s = ag32_ffi_get_arg s))`,
  CHEAT_TAC);;

(* ag32_ffi_open_in *)

let ag32_ffi_open_in_fail_code_def = new_definition
  `ag32_ffi_open_in_fail_code = ag32_ffi_fail_code (implode "open_in")`;;
(* HOL4 ag32_ffi_codeProofScript.sml:3779-3780: ML code, not ported *)


(* HOL4 ag32_ffi_codeProofScript.sml:3783-3785: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3787-3789: ML code, not ported *)

let ag32_ffi_open_in_intro = prove
 (`ag32_ffi_return (FST (ag32_ffi_open_in_fail_decomp (s,md))) =
         ag32_ffi_open_in s`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:3804: the ML values that the
   definitions below antiquote *)

let ag32_ffi_open_in_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_open_in_code ==>
          get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
          Encode (EL k ag32_ffi_open_in_code)) /\
   byte_aligned (ag32_state_PC s) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_open_in_entrypoint)) /\ ~(ag32_state_R
   s (n2w 3) IN {ag32_state_PC s + n2w n | n < 4 * LENGTH
     ag32_ffi_open_in_code}) ==>
   (?k. (ITER k Next s = ag32_ffi_open_in s))`,
  CHEAT_TAC);;

(* ag32_ffi_open_out *)

let ag32_ffi_open_out_fail_code_def = new_definition
  `ag32_ffi_open_out_fail_code = ag32_ffi_fail_code (implode "open_out")`;;
(* HOL4 ag32_ffi_codeProofScript.sml:3838-3839: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3841-3843: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3845-3847: ML code, not ported *)

let ag32_ffi_open_out_intro = prove
 (`ag32_ffi_return (FST (ag32_ffi_open_out_fail_decomp (s,md))) =
         ag32_ffi_open_out s`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:3862: the ML values that the
   definitions below antiquote *)
let ag32_ffi_open_out_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_open_out_code ==>
      (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
       Encode (EL k ag32_ffi_open_out_code))) /\
   byte_aligned (ag32_state_PC s) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_open_out_entrypoint)) /\ ~(ag32_state_R
   s (n2w 3) IN {ag32_state_PC s + n2w n | n < 4 * LENGTH
     ag32_ffi_open_out_code}) ==>
   (?k. (ITER k Next s = ag32_ffi_open_out s))`,
  CHEAT_TAC);;

(* ag32_ffi_close *)

let ag32_ffi_close_fail_code_def = new_definition
  `ag32_ffi_close_fail_code = ag32_ffi_fail_code (implode "close")`;;
(* HOL4 ag32_ffi_codeProofScript.sml:3894-3895: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3897-3899: ML code, not ported *)

(* HOL4 ag32_ffi_codeProofScript.sml:3901-3903: ML code, not ported *)

let ag32_ffi_close_intro = prove
 (`ag32_ffi_return (FST (ag32_ffi_close_fail_decomp (s,md))) =
         ag32_ffi_close s`,
  CHEAT_TAC);;

let ag32_ffi_close_code_thm = prove
 (`(!k. k < LENGTH ag32_ffi_close_code ==>
      (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
       Encode (EL k ag32_ffi_close_code))) /\
   byte_aligned (ag32_state_PC s) /\
   (ag32_state_PC s = n2w (ffi_code_start_offset +
     ag32_ffi_close_entrypoint)) /\ ~(ag32_state_R
   s (n2w 3) IN {ag32_state_PC s + n2w n | n < 4 * LENGTH
     ag32_ffi_close_code}) ==>
   (?k. (ITER k Next s = ag32_ffi_close s))`,
  CHEAT_TAC);;

(* ag32_ffi_ *)


let ag32_ffi__code_thm = prove
 (`(!k. k < LENGTH ag32_ffi__code ==>
        (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
         Encode (EL k ag32_ffi__code))) /\ byte_aligned (ag32_state_PC s)
           ==>
   (?k. (ITER k Next s = ag32_ffi_ s))`,
  CHEAT_TAC);;

(* HOL4 ag32_ffi_codeProofScript.sml:3977: the ML values that the
   definitions below antiquote *)

(* mk_jump_ag32 *)

let mk_jump_ag32_code_thm = prove
 (`(ag32_state_PC s = n2w (ffi_jumps_offset + ffi_offset * (LENGTH ffi_names -
  (index + 1)))) /\
   (INDEX_OF nm ffi_names = SOME index) /\
   (ALOOKUP ffi_entrypoints nm = SOME epc) /\
   (!k. k < 4 ==>
     (get_mem_word (ag32_state_MEM s) (ag32_state_PC s + n2w (4 * k)) =
      EL k (mk_jump_ag32_code ffi_names nm))) ==>
   (?k ov cf r5.
     (ITER k Next s = ag32_state_OverflowFlag_fupd (K ov)
       (ag32_state_CarryFlag_fupd (K cf) (ag32_state_R_fupd (K (((n2w 5) =+ r5)
       (ag32_state_R s))) (ag32_state_PC_fupd (K (n2w (ffi_code_start_offset +
       epc)))
      s)))))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["cf";
   "not"];;

(* and the interface *)
let _ = unhide_overloads ();;
