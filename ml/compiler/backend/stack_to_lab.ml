(* ======================================================== *)
(*  stack_to_lab: ported from HOL4's
    compiler/backend/stack_to_labScript.sml
    A definition theory, with 9 definitions, 1 datatype and 1
    theorem.  Needed by backend.ml, backendProof.ml,
    backend_passes.ml and stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase maps stackLang programs, which have structure
  such as If, While, Return etc, to labLang programs that are a soup
  of goto-like jumps.
*)

needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stack_to_lab"
  ["bvl_to_bvi"; "labLang"; "stackLang"; "stack_alloc"; "stack_names";
   "stack_rawcall"; "stack_remove"; "word_to_stack"];;

(* HOL4 stack_to_labScript.sml:17: the overload Asm, which the port
   expands *)

let compile_jump_def = define_cases
  [`compile_jump (INL n) = labLang_LabAsm (labLang_Jump (labLang_Lab
    n 0)) (n2w 0) [] 0`;
   `compile_jump (INR r) = (\a. labLang_Asm (Asmi a)) (asm_JumpReg
    r) [] 0`];;

let negate_def = define_cases
  [`negate (asm_Less:cmp) = asm_NotLess`;
   `negate (asm_Equal:cmp) = asm_NotEqual`;
   `negate asm_Lower = asm_NotLower`;
   `negate (asm_Test:cmp) = asm_NotTest`;
   `negate asm_NotLess = asm_Less`;
   `negate asm_NotEqual = asm_Equal`;
   `negate asm_NotLower = asm_Lower`;
   `negate asm_NotTest = asm_Test`];;
add_simp negate_def;;

let find_lab_def = new_definition
  `find_lab n labs =
     (match oEL n labs with NONE -> (0:num) | SOME k -> k)`;;

(* HOL4 stack_to_labScript.sml:42: the overload ++, which the port
   writes as an application of misc_Append *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let stack_to_lab_flatten_def,stack_to_lab_flatten_ind =
  define_guess_cheat
  [`stack_to_lab_flatten t p n m conts breaks =
     (match p with stackLang_Tick -> (misc_List [(\a. labLang_Asm
       (Asmi a)) (asm_Inst (asm_Skip)) [] 0],F,m) | asm_Inst a ->
       (misc_List [(\a. labLang_Asm (Asmi a)) (asm_Inst a) [] 0],F,m) |
       stackLang_Halt _1 -> (misc_List [labLang_LabAsm labLang_Halt
       (n2w 0) [] 0],T,m) | stackLang_Seq p1 p2 ->
         (let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts
           breaks in
         let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts breaks
           in
           if t then (misc_Append (misc_Append xs (misc_List
             [labLang_Label n 1 0])) ys,(nr1 \/ nr2),m) else
             (misc_Append xs ys,(nr1 \/ nr2),m)) | stackLang_If c r ri
             p1 p2 ->
         (let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts
           breaks in
         let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts breaks
           in
           if (p1 = asm_Skip) /\ (p2 = asm_Skip) then (misc_List
             [],F,m) else if p1 = asm_Skip then
             (misc_Append (misc_Append (misc_List [labLang_LabAsm
               (asm_JumpCmp c r ri (labLang_Lab n m)) (n2w 0) [] 0])
               ys)
              (misc_List [labLang_Label n m 0]),F,m + 1) else if p2
                = asm_Skip then
             (misc_Append (misc_Append (misc_List [labLang_LabAsm
               (asm_JumpCmp (negate c) r ri (labLang_Lab n m)) (n2w 0)
               [] 0]) xs)
              (misc_List [labLang_Label n m 0]),F,m + 1) else if nr1
                then
             (misc_Append (misc_Append (misc_Append (misc_List
               [labLang_LabAsm (asm_JumpCmp (negate c) r ri
               (labLang_Lab n m)) (n2w 0) [] 0]) xs)
              (misc_List [labLang_Label n m 0])) ys,nr2,m + 1) else
                if nr2 then
             (misc_Append (misc_Append (misc_Append (misc_List
               [labLang_LabAsm (asm_JumpCmp c r ri (labLang_Lab n m))
               (n2w 0) [] 0]) ys)
              (misc_List [labLang_Label n m 0])) xs,nr1,m + 1) else
             (misc_Append (misc_Append (misc_Append (misc_Append
               (misc_List [labLang_LabAsm (asm_JumpCmp c r ri
               (labLang_Lab n m)) (n2w 0) [] 0]) ys)
              (misc_List [labLang_LabAsm (asm_Jump (labLang_Lab n (m
                + 1))) (n2w 0) [] 0; labLang_Label n m 0])) xs)
              (misc_List [labLang_Label n (m + 1) 0]),(nr1 /\ nr2),m
                + 2)) | stackLang_Loop p1 ->
         (let cont_lab = m in
         let break_lab = m + 1 in
         let (xs,_2,m) = stack_to_lab_flatten F p1 n (m + 2) (CONS
           cont_lab conts) (CONS break_lab breaks) in
           (misc_Append (misc_Append (misc_List [labLang_Label n
             cont_lab 0])
            xs)
            (misc_List [labLang_LabAsm (asm_Jump (labLang_Lab n
              cont_lab)) (n2w 0) [] 0;
                  labLang_Label n break_lab 0]),F,m)) |
                    stackLang_Raise r -> (misc_List [(\a. labLang_Asm
                    (Asmi a)) (asm_JumpReg r) [] 0],T,m) |
                    stackLang_Return r -> (misc_List [(\a. labLang_Asm
                    (Asmi a)) (asm_JumpReg r) [] 0],T,m) |
                    stackLang_Break k -> (misc_List [labLang_LabAsm
                    (asm_Jump (labLang_Lab n (find_lab k breaks))) (n2w
                    0) [] 0],T,m) | stackLang_Continue k -> (misc_List
                    [labLang_LabAsm (asm_Jump (labLang_Lab n (find_lab
                    k conts))) (n2w 0) [] 0],T,m) | stackLang_RawCall n
                    -> (misc_List [labLang_LabAsm (asm_Jump
                    (labLang_Lab n 1)) (n2w 0) [] 0],T,m) |
                    stackLang_Call NONE dest handler -> (misc_List
                    [compile_jump dest],T,m) | stackLang_Call (SOME
                    (p1,lr,l1,l2)) dest handler ->
         (let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts
           breaks in
         let prefix = misc_Append (misc_List [labLang_LabAsm
           (labLang_LocValue lr (labLang_Lab l1 l2)) (n2w 0) [] 0;
                  compile_jump dest; labLang_Label l1 l2 0]) xs in
         (match handler with NONE -> (prefix,nr1,m) | SOME
           (p2,k1,k2) ->
             (let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts
               breaks in
               (misc_Append prefix (misc_Append (misc_Append
                 (misc_List [labLang_LabAsm (asm_Jump (labLang_Lab n
                 m)) (n2w 0) [] 0; labLang_Label k1 k2 0])
               ys) (misc_List [labLang_Label n m 0])),(nr1 /\ nr2),m
                 + 1)))) | stackLang_JumpLower r1 r2 target ->
         (misc_List [labLang_LabAsm (asm_JumpCmp asm_Lower r1 (Reg
           r2) (labLang_Lab target 0)) (n2w 0) [] 0],F,m) |
           stackLang_FFI ffi_index _3 _4 _5 _6 lr -> (misc_List
           [labLang_LabAsm (labLang_LocValue lr (labLang_Lab n m)) (n2w
           0) [] 0;
                              labLang_LabAsm (labLang_CallFFI
                                ffi_index) (n2w 0) [] 0;
                              labLang_Label n m 0],F,m + 1) |
                                stackLang_LocValue i l1 l2 ->
                                (misc_List [labLang_LabAsm
                                (labLang_LocValue i (labLang_Lab l1
                                l2)) (n2w 0) [] 0],F,m) |
                                stackLang_Install _7 _8 _9 _10 ret ->
       (misc_List [labLang_LabAsm (labLang_LocValue ret (labLang_Lab
         n m)) (n2w 0) [] 0;
       labLang_LabAsm stackLang_Install (n2w 0) [] 0;
       labLang_Label n m 0],F,m + 1) | stackLang_ShMemOp op r ad ->
         (misc_List [labLang_Asm (ShareMem op r ad) [] 0],F,m) |
         stackLang_CodeBufferWrite r1 r2 ->
       (misc_List [labLang_Asm (Cbw r1 r2) [] 0],F,m) | _11 ->
         (misc_List [],F,m))`];;
(* HOL4 stack_to_labScript.sml:115-124: a theorem that HOL4 states as
   the value of an ML expression: flatten_pmatch *)

let is_Seq_def = new_definition
  `is_Seq x1 =
      match x1 with
        stackLang_Seq p1 p2 -> T
      | _12 -> F`;;

let prog_to_section_def = new_definition
  `prog_to_section (n,p) =
     (let (lines,_13,m) = (stack_to_lab_flatten T p n (next_lab p 2)
       [] []) in
       Section n (append (misc_Append lines
         (misc_List [labLang_Label n (if is_Seq p then m else 1)
           0]))))`;;

let is_gen_gc_def = new_definition
  `is_gen_gc x1 =
        match x1 with
          data_to_word_Generational l -> T
        | _14 -> F`;;

let stack_to_lab_config_FIELDS = define_record "stack_to_lab_config"
  ["reg_names","num spt";
   "jump","bool";
   (* whether to compile to JumpLower or If Lower ... in stack_remove*)
   "perf_calls","bool"
   (* unverified: emit C-stack shadowing for perf call graphs (x64 only) *)
  ];;

let stack_to_lab_compile_def = new_definition
  `stack_to_lab_compile stack_conf data_conf max_heap sp offset prog =
     (let prog = stack_rawcall_compile prog in
     let prog = stack_alloc_compile data_conf prog in
     let prog = stack_remove_compile (stack_to_lab_config_jump
       stack_conf) offset (is_gen_gc (data_to_word_config_gc_kind
       data_conf))
                  max_heap sp InitGlobals_location prog in
     let prog = stack_names_compile (stack_to_lab_config_reg_names
       stack_conf) prog in
       MAP prog_to_section prog)`;;

let compile_no_stubs_def = new_definition
  `compile_no_stubs f jump offset sp prog =
   MAP prog_to_section
     (stack_names_compile f
       (MAP (stack_remove_prog_comp jump offset sp)
         (MAP stack_alloc_prog_comp prog)))`;;
