(* ======================================================== *)
(*  stack_rawcallProof: ported from HOL4's
    compiler/backend/proofs/stack_rawcallProofScript.sml
    A proof theory about stack_rawcall.ml, with 2 definitions and 21
    theorems.  Needed by stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_rawcall
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semantics.ml";;


(* HOL4 stack_rawcallProofScript.sml:12: ML code, not ported *)

(* HOL4 stack_rawcallProofScript.sml:14-16: ML code, not ported *)

(* HOL4 stack_rawcallProofScript.sml:18: the overload good_dimindex,
   which the port expands *)
(* HOL4 stack_rawcallProofScript.sml:19: the overload comp, which the
   port expands *)
(* HOL4 stack_rawcallProofScript.sml:20: the overload compile, which
   the port expands *)
(* HOL4 stack_rawcallProofScript.sml:21: the type abbreviation prog,
   which the port expands *)

let state_ok_def = cake_define
  `stack_rawcallProof_state_ok i code <=>
     (!n v.
       sptree_lookup n i = SOME v ==>
       (?p. sptree_lookup n code = SOME (Seq (stackLang_StackAlloc
         v) p)))`;;
hol4_overload "state_ok" "stack_rawcallProof_state_ok";;

let state_rel_def = cake_define
  `stack_rawcallProof_state_rel i s t <=>
     (?c.
       // co cc
       domain c = domain (state_code s) /\
       t = state_code_fupd (K c) s /\
       // ;
       // compile := cc ;
       // compile_oracle := co
       // s.compile = pure_cc compile t.compile /\
       // t.compile_oracle = (I ## compile ## I) o s.compile_oracle /\
       stack_rawcallProof_state_ok i (state_code s) /\
       (!n b.
         sptree_lookup n (state_code s) = SOME b ==>
         (?i. stack_rawcallProof_state_ok i (state_code s) /\
             lookup n c = SOME (comp_top i b))))`;;
hol4_overload "state_rel" "stack_rawcallProof_state_rel";;

(* HOL4 stack_rawcallProofScript.sml:46-47: a theorem that HOL4
   states as the value of an ML expression: state_rel_thm *)

let with_stack_space = cake_theorem "with_stack_space[local]"
  (fun () ->
    `stackSem_state_stack_space_fupd (K (stackSem_state_stack_space t1))
       t1 = t1`)
  CHEAT_TAC;;

let comp_LN = cake_theorem "comp_LN"
  (fun () ->
    `!(i:num spt) b. comp_top LN b = b /\ stack_rawcall_comp LN b = b`)
  CHEAT_TAC;;

let comp_seq_neq_IMP = cake_theorem "comp_seq_neq_IMP"
  (fun () ->
    `~(comp_seq p1 p2 i default = default) ==>
       (?k dest. p1 = stackLang_StackFree k /\ p2 = Call NONE
         (INL dest) NONE)`)
  CHEAT_TAC;;

let stack_rawcallProof_get_labels_comp = cake_theorem "get_labels_comp"
  (fun () ->
    `!i e.
       get_labels (stack_rawcall_comp i e) = get_labels e /\
       get_labels (comp_top i e) = get_labels e`)
  CHEAT_TAC;;

(* HOL4 stack_rawcallProofScript.sml:107-119: a proof *)

let evaluate_comp_Inst = cake_theorem "evaluate_comp_Inst"
  (fun () ->
    `evaluate (Inst i,s) = (r,s1) /\ ~(r = SOME Error) /\
  stack_rawcallProof_state_rel i' s t ==>
     (?ck t1 k1.
       stack_rawcallProof_state_rel i' s1 t1 /\
       evaluate (stack_rawcall_comp i' (Inst i),state_clock_fupd (K
         (ck + state_clock t)) t) =
       (r,stackSem_state_stack_space_fupd (K k1) t1) /\
       (~(r = SOME TimeOut) /\ ~(r = SOME (Halt (wordLang_Word (n2w
         2)))) ==>
        k1 = stackSem_state_stack_space t1))`)
  CHEAT_TAC;;

let stack_rawcallProof_comp_correct = cake_theorem "comp_correct"
  (fun () ->
    `!p (s:('a,'c,'b)stackSem_state) t i r s1.
       evaluate (p,s) = (r,s1) /\ ~(r = SOME Error) /\
         stack_rawcallProof_state_rel i s t ==>
       (?ck t1 k1.
          stack_rawcallProof_state_rel i s1 t1 /\
          evaluate (comp_top i p,state_clock_fupd (K (state_clock t
            + ck)) t) =
            (r,stackSem_state_stack_space_fupd (K k1) t1) /\
          (~(r = SOME TimeOut) /\ ~(r = SOME (Halt (wordLang_Word
            (n2w 2)))) ==> k1 = stackSem_state_stack_space t1)) /\
       (?ck t1 k1.
          stack_rawcallProof_state_rel i s1 t1 /\
          evaluate (stack_rawcall_comp i p,state_clock_fupd (K
            (state_clock t + ck)) t) =
            (r,stackSem_state_stack_space_fupd (K k1) t1) /\
          (~(r = SOME TimeOut) /\ ~(r = SOME (Halt (wordLang_Word
            (n2w 2)))) ==> k1 = stackSem_state_stack_space t1))`)
  CHEAT_TAC;;

let domain_fromAList_compile = cake_theorem "domain_fromAList_compile"
  (fun () ->
    `domain (fromAList (stack_rawcall_compile code)) = domain
  (fromAList code)`)
  CHEAT_TAC;;

let lookup_collect_info = cake_theorem "lookup_collect_info"
  (fun () ->
    `!xs n rest.
       ALL_DISTINCT (MAP FST xs) ==>
       lookup n (collect_info xs rest) =
         (match ALOOKUP xs n with NONE -> lookup n rest | SOME
           body -> lookup n (collect_info [(n,body)] rest))`)
  CHEAT_TAC;;

let state_ok_collect_info = cake_theorem "state_ok_collect_info"
  (fun () ->
    `ALL_DISTINCT (MAP FST code) ==>
     stack_rawcallProof_state_ok (collect_info code LN)
       (fromAList code)`)
  CHEAT_TAC;;

let stack_rawcallProof_compile_semantics =
  cake_theorem "compile_semantics"
  (fun () ->
    `ALL_DISTINCT (MAP FST code) /\ stackSem_state_use_stack s /\
  state_code
     s = fromAList code /\ ~(semantics start s = Fail) ==>
     semantics start (state_code_fupd (K (fromAList
       (stack_rawcall_compile code))) s) =
     semantics start s`)
  CHEAT_TAC;;

let extract_labels_comp = cake_theorem "extract_labels_comp"
  (fun () ->
    `!i p.
       extract_labels (stack_rawcall_comp i p) = extract_labels p
         /\
       extract_labels (comp_top i p) = extract_labels p`)
  CHEAT_TAC;;

let stack_asm_name_comp = cake_theorem "stack_asm_name_comp"
  (fun () ->
    `!i p.
       (stack_asm_name c (stack_rawcall_comp i p) = stack_asm_name
         c p /\
        stack_asm_name c (comp_top i p) = stack_asm_name c p) /\
       (stack_asm_remove c (stack_rawcall_comp i p) =
         stack_asm_remove c p /\
        stack_asm_remove c (comp_top i p) = stack_asm_remove c p)`)
  CHEAT_TAC;;

let stack_rawcallProof_stack_alloc_stack_asm_convs =
  cake_theorem "stack_alloc_stack_asm_convs"
  (fun () ->
    `EVERY (\(n,p). stack_asm_name c p) (stack_rawcall_compile prog) =
     EVERY (\(n,p). stack_asm_name c p) prog /\
     EVERY (\(n,p). stack_asm_remove c p) (stack_rawcall_compile
       prog) =
     EVERY (\(n,p). stack_asm_remove c p) prog`)
  CHEAT_TAC;;

let reg_bound_comp = cake_theorem "reg_bound_comp"
  (fun () ->
    `!i p.
       reg_bound (stack_rawcall_comp i p) s = reg_bound p s /\
       reg_bound (comp_top i p) s = reg_bound p s`)
  CHEAT_TAC;;

let stack_rawcall_reg_bound = cake_theorem "stack_rawcall_reg_bound"
  (fun () ->
    `EVERY (\p. reg_bound p sp) (MAP SND (stack_rawcall_compile prog1))
  =
     EVERY (\p. reg_bound p sp) (MAP SND prog1)`)
  CHEAT_TAC;;

let call_args_comp = cake_theorem "call_args_comp"
  (fun () ->
    `!i p.
       call_args (stack_rawcall_comp i p) r1 r2 r3 r4 r5 =
         call_args p r1 r2 r3 r4 r5 /\
       call_args (comp_top i p) r1 r2 r3 r4 r5 = call_args p r1
         r2 r3 r4 r5`)
  CHEAT_TAC;;

let stack_rawcallProof_stack_alloc_call_args =
  cake_theorem "stack_alloc_call_args"
  (fun () ->
    `EVERY (\p. call_args p 1 2 3 4 0) (MAP SND (stack_rawcall_compile
  prog1)) =
     EVERY (\p. call_args p 1 2 3 4 0) (MAP SND prog1)`)
  CHEAT_TAC;;

let stack_rawcallProof_MAP_FST_compile = cake_theorem "MAP_FST_compile"
  (fun () ->
    `MAP FST (stack_rawcall_compile code) = MAP FST code`)
  CHEAT_TAC;;

let call_arg_comp = cake_theorem "call_arg_comp"
  (fun () ->
    `!i p.
       alloc_arg (stack_rawcall_comp i p) = alloc_arg p /\
       alloc_arg (comp_top i p) = alloc_arg p`)
  CHEAT_TAC;;

let stack_get_handler_labels_comp =
  cake_theorem "stack_get_handler_labels_comp"
  (fun () ->
    `!i p k.
       stack_get_handler_labels k (stack_rawcall_comp i p) =
       stack_get_handler_labels k p /\
       stack_get_handler_labels k (comp_top i p) =
       stack_get_handler_labels k p`)
  CHEAT_TAC;;
