(* ======================================================== *)
(*  stack_allocProof: ported from HOL4's
    compiler/backend/proofs/stack_allocProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for stack_alloc
*)

needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
(* HOL4 ancestors outside the port: (* for memcpy *) *)

(* HOL4 stack_allocProofScript.sml:16: ML code, not ported *)

(* HOL4 stack_allocProofScript.sml:18-21: ML code, not ported *)

(* HOL4 stack_allocProofScript.sml:23-24: the overload good_dimindex,
   which the port expands *)

(* TODO: move and join with stack_remove *)

(* ---- *)

let get_bits_def = cake_define
  `get_bits w = GENLIST (\i. FAPPLY w i) (bit_length w - 1)`;;

(* HOL4 stack_allocProofScript.sml:264-266: ML code, not ported *)

(* HOL4 stack_allocProofScript.sml:372-377: a proof *)

(* HOL4 stack_allocProofScript.sml:379-384: a proof *)

(* HOL4 stack_allocProofScript.sml:386-388: a proof *)

(* gc_kind = Simple *)

(* HOL4 stack_allocProofScript.sml:469-479: ML code, not ported *)

(* HOL4 stack_allocProofScript.sml:519-524: ML code, not ported *)

let word_gc_move_roots_bitmaps_def = cake_define
  `word_gc_move_roots_bitmaps conf (stack',bitmaps,i1,pa1,curr,m,dm) =
     (match enc_stack bitmaps stack' with NONE -> (ARB,ARB,ARB,ARB,F)
       | SOME wl_list ->
         (let (wl,i2,pa2,m2,c2) =
             word_gc_move_roots conf (wl_list,i1,pa1,curr,m,dm) in
           match dec_stack bitmaps wl stack' with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME stack' ->
             (stack',i2,pa2,m2,c2)))`;;

let word_gc_move_bitmaps_def = cake_define
  `word_gc_move_bitmaps conf (w,stack',bitmaps,i1,pa1,curr,m,dm) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack' with NONE -> NONE | SOME
         (ts,ws) ->
         (let (wl,i2,pa2,m2,c2) =
                 word_gc_move_roots conf (ts,i1,pa1,curr,m,dm) in
           match map_bitmap bs wl stack' with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,m2,c2))))`;;

let word_gc_move_bitmap_def = cake_define
  `word_gc_move_bitmap conf (w,stack',i1,pa1,curr,m,dm) =
     (let bs = get_bits w in
       match filter_bitmap bs stack' with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,m2,c2) = word_gc_move_roots conf
            (ts,i1,pa1,curr,m,dm) in
            match map_bitmap bs wl stack' with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 stack_allocProofScript.sml:718-740: a proof *)

(* HOL4 stack_allocProofScript.sml:742-744: the ML values that the
   definitions below antiquote *)

(* gc_kind = Generational *)

(* HOL4 stack_allocProofScript.sml:1717: the ML values that the
   definitions below antiquote *)

(* HOL4 stack_allocProofScript.sml:1719-1729: ML code, not ported *)

(* HOL4 stack_allocProofScript.sml:1835-1840: ML code, not ported *)

let word_gen_gc_move_roots_bitmaps_def = cake_define
  `word_gen_gc_move_roots_bitmaps conf
  (stack',bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
     (match enc_stack bitmaps stack' with NONE ->
       (ARB,ARB,ARB,ARB,ARB,ARB,F) | SOME wl_list ->
         (let (wl,i2,pa2,ib2,pb2,m2,c2) =
             word_gen_gc_move_roots conf
               (wl_list,i1,pa1,ib1,pb1,curr,m,dm) in
           match dec_stack bitmaps wl stack' with NONE ->
             (ARB,ARB,ARB,ARB,ARB,ARB,F) | SOME stack' ->
             (stack',i2,pa2,ib2,pb2,m2,c2)))`;;

let word_gen_gc_partial_move_roots_bitmaps_def = cake_define
  `word_gen_gc_partial_move_roots_bitmaps conf
  (stack',bitmaps,i1,pa1,curr,m,dm,gs,rs) =
     (match enc_stack bitmaps stack' with NONE -> (ARB,ARB,ARB,ARB,F)
       | SOME wl_list ->
         (let (wl,i2,pa2,m2,c2) =
             word_gen_gc_partial_move_roots conf
               (wl_list,i1,pa1,curr,m,dm,gs,rs) in
           match dec_stack bitmaps wl stack' with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME stack' ->
             (stack',i2,pa2,m2,c2)))`;;

let word_gen_gc_move_bitmaps_def = cake_define
  `word_gen_gc_move_bitmaps conf
  (w,stack',bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack' with NONE -> NONE | SOME
         (ts,ws) ->
         (let (wl,i2,pa2,ib2,pb2,m2,c2) =
                 word_gen_gc_move_roots conf
                   (ts,i1,pa1,ib1,pb1,curr,m,dm) in
           match map_bitmap bs wl stack' with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2))))`;;

let word_gen_gc_partial_move_bitmaps_def = cake_define
  `word_gen_gc_partial_move_bitmaps conf
  (w,stack',bitmaps,i1,pa1,curr,m,dm,gs,rs) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack' with NONE -> NONE | SOME
         (ts,ws) ->
         (let (wl,i2,pa2,m2,c2) =
                 word_gen_gc_partial_move_roots conf
                   (ts,i1,pa1,curr,m,dm,gs,rs) in
           match map_bitmap bs wl stack' with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,m2,c2))))`;;

let word_gen_gc_move_bitmap_def = cake_define
  `word_gen_gc_move_bitmap conf (w,stack',i1,pa1,ib1,pb1,curr,m,dm) =
     (let bs = get_bits w in
       match filter_bitmap bs stack' with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,ib2,pb2,m2,c2) =
            word_gen_gc_move_roots conf (ts,i1,pa1,ib1,pb1,curr,m,dm)
              in
            match map_bitmap bs wl stack' with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2)))`;;

let word_gen_gc_partial_move_bitmap_def = cake_define
  `word_gen_gc_partial_move_bitmap conf
  (w,stack',i1,pa1,curr,m,dm,gs,rs) =
     (let bs = get_bits w in
       match filter_bitmap bs stack' with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,m2,c2) =
            word_gen_gc_partial_move_roots conf
              (ts,i1,pa1,curr,m,dm,gs,rs) in
            match map_bitmap bs wl stack' with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 stack_allocProofScript.sml:2225-2247: a proof *)

(* HOL4 stack_allocProofScript.sml:2249-2251: the ML values that the
   definitions below antiquote *)

(* HOL4 stack_allocProofScript.sml:2253-2255: the ML values that the
   definitions below antiquote *)

(* gc_kind = None *)

(* --- *)

(* This proof is very slow! *)

(* HOL4 stack_allocProofScript.sml:5896-5899: ML code, not ported *)
(* HOL4 stack_allocProofScript.sml:5907: ML code, not ported *)

(* TODO: does this have to initialize the data_buffer to empty? *)
let make_init_def = cake_define
  `stack_allocProof_make_init c code oracle'
  (s:('a,'c,'ffi)stackSem_state) = stackSem_state_compile_oracle_fupd (K
  oracle') (stackSem_state_compile_fupd (K (\c. stackSem_state_compile s
  c o (MAP stack_alloc_prog_comp))) (stackSem_state_gc_fun_fupd (K
  (word_gc_fun c)) (stackSem_state_use_stack_fupd (K T)
  (stackSem_state_use_alloc_fupd (K T) (stackSem_state_code_fupd (K
  code)
     s)))))`;;
hol4_overload "make_init" "stack_allocProof_make_init";;
