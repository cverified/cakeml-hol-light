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

needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/comparison.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* HOL4 stack_to_labScript.sml:17: the overload Asm, which the port
   expands *)

let compile_jump_def = cake_define_list
  [`compile_jump (INL n) = labLang_LabAsm (Jump (labLang_Lab n 0))
  (n2w 0) [] 0`;
   `compile_jump (INR r) = (\a. labLang_Asm (Asmi a)) (asm_JumpReg
  r) [] 0`];;

let negate_def = cake_define_list
  [`negate (Less:cmp) = asm_NotLess`;
   `negate (Equal:cmp) = asm_NotEqual`;
   `negate asm_Lower = asm_NotLower`;
   `negate (Test:cmp) = asm_NotTest`;
   `negate asm_NotLess = asm_Less`;
   `negate asm_NotEqual = asm_Equal`;
   `negate asm_NotLower = asm_Lower`;
   `negate asm_NotTest = asm_Test`];;

let find_lab_def = cake_define
  `find_lab n labs =
     (match oEL n labs with NONE -> (0:num) | SOME k -> k)`;;

hol4_overload "++" "misc_Append";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let flatten_def = cake_define_cheat CHEAT_TAC
  `stack_to_lab_flatten t p n m conts breaks =
     (match p with Tick -> (List [(\a. labLang_Asm (Asmi a)) (Inst
       (asm_Skip)) [] 0],F,m) | Inst a -> (List [(\a. labLang_Asm (Asmi
       a)) (Inst a) [] 0],F,m) | Halt _1 -> (List [labLang_LabAsm
       labLang_Halt (n2w 0) [] 0],T,m) | Seq p1 p2 ->
         (let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts breaks
           in
         let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts breaks
           in
           if t then (xs ++ List [Label n 1 0] ++ ys,(nr1 \/ nr2),m)
             else (xs ++ ys,(nr1 \/ nr2),m)) | If c r ri p1 p2 ->
         (let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts breaks
           in
         let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts breaks
           in
           if (p1 = Skip) /\ (p2 = Skip) then (List [],F,m) else if
             p1 = Skip then
             (List [labLang_LabAsm (JumpCmp c r ri (labLang_Lab n m))
               (n2w 0) [] 0] ++ ys ++
              List [Label n m 0],F,m + 1) else if p2 = Skip then
             (List [labLang_LabAsm (JumpCmp (negate c) r ri
               (labLang_Lab n m)) (n2w 0) [] 0] ++ xs ++
              List [Label n m 0],F,m + 1) else if nr1 then
             (List [labLang_LabAsm (JumpCmp (negate c) r ri
               (labLang_Lab n m)) (n2w 0) [] 0] ++ xs ++
              List [Label n m 0] ++ ys,nr2,m + 1) else if nr2 then
             (List [labLang_LabAsm (JumpCmp c r ri (labLang_Lab n m))
               (n2w 0) [] 0] ++ ys ++
              List [Label n m 0] ++ xs,nr1,m + 1) else
             (List [labLang_LabAsm (JumpCmp c r ri (labLang_Lab n m))
               (n2w 0) [] 0] ++ ys ++
              List [labLang_LabAsm (Jump (labLang_Lab n (m + 1)))
                (n2w 0) [] 0; Label n m 0] ++ xs ++
              List [Label n (m + 1) 0],(nr1 /\ nr2),m + 2)) | Loop p1
                ->
         (let cont_lab = m in
         let break_lab = m + 1 in
         let (xs,_2,m) = stack_to_lab_flatten F p1 n (m + 2)
           (cont_lab :: conts) (break_lab :: breaks) in
           (List [Label n cont_lab 0] ++
            xs ++
            List [labLang_LabAsm (Jump (labLang_Lab n cont_lab)) (n2w
              0) [] 0;
                  Label n break_lab 0],F,m)) | Raise r -> (List [(\a.
                    labLang_Asm (Asmi a)) (asm_JumpReg r) [] 0],T,m) |
                    Return r -> (List [(\a. labLang_Asm (Asmi a))
                    (asm_JumpReg r) [] 0],T,m) | Break k -> (List
                    [labLang_LabAsm (Jump (labLang_Lab n (find_lab k
                    breaks))) (n2w 0) [] 0],T,m) | Continue k -> (List
                    [labLang_LabAsm (Jump (labLang_Lab n (find_lab k
                    conts))) (n2w 0) [] 0],T,m) | stackLang_RawCall n ->
                    (List [labLang_LabAsm (Jump (labLang_Lab n 1)) (n2w
                    0) [] 0],T,m) | Call NONE dest handler -> (List
                    [compile_jump dest],T,m) | Call (SOME (p1,lr,l1,l2))
                    dest handler ->
         (let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts breaks
           in
         let prefix = List [labLang_LabAsm (LocValue lr (labLang_Lab
           l1 l2)) (n2w 0) [] 0;
                  compile_jump dest; Label l1 l2 0] ++ xs in
         (match handler with NONE -> (prefix,nr1,m) | SOME (p2,k1,k2)
           ->
             (let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts
               breaks in
               (prefix ++ (List [labLang_LabAsm (Jump (labLang_Lab n
                 m)) (n2w 0) [] 0; Label k1 k2 0] ++
               ys ++ List [Label n m 0]),(nr1 /\ nr2),m + 1)))) |
                 stackLang_JumpLower r1 r2 target ->
         (List [labLang_LabAsm (JumpCmp asm_Lower r1 (Reg r2)
           (labLang_Lab target 0)) (n2w 0) [] 0],F,m) | FFI ffi_index _3
           _4 _5 _6 lr -> (List [labLang_LabAsm (LocValue lr
           (labLang_Lab n m)) (n2w 0) [] 0;
                              labLang_LabAsm (labLang_CallFFI
                                ffi_index) (n2w 0) [] 0;
                              Label n m 0],F,m + 1) | LocValue i l1
                                l2 -> (List [labLang_LabAsm (LocValue i
                                (labLang_Lab l1 l2)) (n2w 0) [] 0],F,m)
                                | Install _7 _8 _9 _10 ret ->
       (List [labLang_LabAsm (LocValue ret (labLang_Lab n m)) (n2w 0)
         [] 0;
       labLang_LabAsm Install (n2w 0) [] 0;
       Label n m 0],F,m + 1) | stackLang_ShMemOp op r ad -> (List
         [labLang_Asm (ShareMem op r ad) [] 0],F,m) | CodeBufferWrite r1
         r2 ->
       (List [labLang_Asm (Cbw r1 r2) [] 0],F,m) | _11 -> (List
         [],F,m))`;;
hol4_overload "flatten" "stack_to_lab_flatten";;
(* HOL4 stack_to_labScript.sml:115-124: a theorem that HOL4 states as
   the value of an ML expression: flatten_pmatch *)

let is_Seq_def = cake_define
  `is_Seq x1 =
      match x1 with
        stackLang_Seq p1 p2 -> T
      | _12 -> F`;;

let prog_to_section_def = cake_define
  `prog_to_section (n,p) =
     (let (lines,_13,m) = (stack_to_lab_flatten T p n (next_lab p 2)
       [] []) in
       Section n (append (Append lines
         (misc_List [Label n (if is_Seq p then m else 1) 0]))))`;;

let is_gen_gc_def = cake_define
  `is_gen_gc x1 =
        match x1 with
          data_to_word_Generational l -> T
        | _14 -> F`;;

let stack_to_lab_config_FIELDS = define_record "stack_to_lab_config"
  ["reg_names","num spt";
   "jump","bool";
   "perf_calls","bool"];;

let compile_def = cake_define
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
hol4_overload "compile" "stack_to_lab_compile";;

let compile_no_stubs_def = cake_define
  `compile_no_stubs f jump offset sp prog =
   MAP prog_to_section
     (stack_names_compile f
       (MAP (stack_remove_prog_comp jump offset sp)
         (MAP stack_alloc_prog_comp prog)))`;;

hol4_only "++" "APPEND";;
