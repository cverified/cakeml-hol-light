# The theorems of data_to_word_memoryProof that wait

Phase three cannot prove these: their statement is about a
definition of `compiler/backend/data_to_word.ml` that the port
does not have, because that file stops loading at its `Unit`
(ISSUES.md, "data_to_word stops loading at its Unit").  The
statement has a free variable where HOL4 has the constant, so
there is nothing to prove about it.  When the definition is
there, these are the ones to take up first.

| theorem | the definitions it waits for |
| --- | --- |
| `bignum_alt_thm` | `small_int` |
| `LENGTH_write_bytes` | `write_bytes` |
| `num_eq_thm` | `small_int` |
| `small_int_IMP_MIN_MAX` | `small_int` |
| `num_less_thm` | `small_int` |
| `abs_ml_inv_Num` | `small_int` |
| `get_lowerbits_LSL_shift_length` | `get_lowerbits` |
| `get_lowerbits_or_1` | `get_lowerbits` |
| `IMP_memory_rel_bignum_alt` | `make_ptr`, `small_int` |
| `memory_rel_Cons1` | `make_cons_ptr` |
| `memory_rel_MutCons` | `make_cons_ptr` |
| `memory_rel_Ref` | `make_ptr` |
| `memory_rel_AllocThunk` | `make_ptr` |
| `memory_rel_Cons_alt` | `make_cons_ptr` |
| `write_bytes_REPLICATE` | `write_bytes` |
| `write_bytes_APPEND` | `write_bytes` |
| `write_bytes_inj_lemma` | `write_bytes` |
| `write_bytes_change_extra` | `byte_len`, `write_bytes` |
| `decode_length_make_byte_header` | `make_byte_header` |
| `memory_rel_RefByte_content` | `byte_len`, `make_byte_header`, `make_ptr`, `write_bytes` |
| `memory_rel_RefByte_alt` | `byte_len`, `make_byte_header`, `make_ptr` |
| `IMP_memory_rel_Number` | `small_int` |
| `memory_rel_FromList` | `make_cons_ptr` |
| `write_bytes_same` | `write_bytes` |
| `memory_rel_ByteArray_IMP` | `make_byte_header` |
| `memory_rel_any_Number_IMP` | `small_int` |
| `memory_rel_Number_IMP` | `small_int` |
| `memory_rel_Number_bignum_IMP_ALT` | `small_int` |
| `memory_rel_Number_bignum_header` | `small_int` |
| `memory_rel_bignum_cmp` | `small_int` |
| `memory_rel_Number_bignum_IMP` | `small_int` |
| `memory_rel_Number_EQ` | `small_int` |
| `memory_rel_Number_LESS` | `small_int` |
| `memory_rel_Number_LESS_EQ` | `small_int` |
| `memory_rel_Number_word_msb` | `small_int` |
| `Smallnum_test` | `small_int` |
| `small_int_w2i_i2w` | `small_int` |
| `small_int_w2n` | `small_int` |
| `make_cons_ptr_thm` | `make_cons_ptr` |
| `write_bytes_inj` | `write_bytes` |
| `memory_rel_Number_const_test` | `small_int` |
| `make_byte_header_eq` | `byte_len`, `make_byte_header` |
| `memory_rel_String_const_test` | `get_Word`, `part_to_words` |
| `memory_rel_bounds_check` | `small_int` |
| `memory_rel_copy_array_NONE` | `byte_len`, `make_byte_header`, `make_ptr` |
| `get_lowerbits_ptrbits` | `get_lowerbits` |
| `append_writes_list_to_BlockReps` | `make_cons_ptr` |
| `memory_rel_append` | `make_cons_ptr` |
| `part_to_words_add` | `lookup_mem`, `part_to_words` |
| `parts_to_words_add` | `lookup_mem`, `parts_to_words` |
| `part_to_words_IMP_build_words` | `part_to_words` |
| `parts_to_words_IMP_build_words` | `lookup_mem`, `parts_to_words` |
| `part_to_words_LENGTH` | `part_to_words` |
| `const_parts_to_words_LENGTH` | `const_parts_to_words` |
| `const_parts_to_words_good_loc` | `const_parts_to_words` |
| `memory_rel_do_build_const` | `const_parts_to_words` |
| `xor_bytes_xor_words` | `write_bytes` |
| `xor_bytes_xor_words` | `write_bytes` |
| `xor_bytes_word_list` | `write_bytes` |
| `xor_bytes_word_list_alias` | `write_bytes` |
