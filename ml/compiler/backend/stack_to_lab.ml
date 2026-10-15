(* ======================================================== *)
(*  stack_to_lab: ported from HOL4's
    compiler/backend/stack_to_labScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase maps stackLang programs, which have structure
  such as If, While, Return etc, to labLang programs that are a soup
  of goto-like jumps.
*)

needs "basis/pure/mlsexp.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* HOL4 overload (expanded in the port):
     Asm = λa. Asm (Asmi a) *)

let compile_jump_def = cake_define
  `(compile_jump (INL n) = LabAsm (Jump (Lab n 0)) (n2w 0) [] 0) /\
   (compile_jump (INR r) = (\a. (\a. (\a. Asm (Asmi a)) (Asmi a))
     (Asmi a)) (JumpReg r) [] 0)`;;

let negate_def = cake_define
  `(negate (LESS) = NotLess) /\
   (negate (EQUAL) = NotEqual) /\
   (negate Lower = NotLower) /\
   (negate Test = NotTest) /\
   (negate NotLess = (LESS)) /\
   (negate NotEqual = (EQUAL)) /\
   (negate NotLower = Lower) /\
   (negate NotTest = Test)`;;

let find_lab_def = cake_define
  `find_lab n labs =
     (match oEL n labs with NONE -> (0:num) | SOME k -> k)`;;

(* HOL4 overload (expanded in the port):
     None =  *)

(* HOL4 ML code, not ported:
local val flatten_quotation = `
  flatten t p n m conts breaks =
    case p of
    | Tick => (List [Asm (Inst (Skip)) [] 0],F,m)
    | Inst a => (List [Asm (Inst a) [] 0],F,m)
    | Halt _ => (List [LabAsm Halt 0w [] 0],T,m)
    | Seq p1 p2 =>
        let (xs,nr1,m) = flatten F p1 n m conts breaks in
        let (ys,nr2,m) = flatten F p2 n m conts breaks in
          if t then (xs ++ List [Label n 1 0] ++ ys, nr1 ∨ nr2, m)
          else (xs ++ ys, nr1 ∨ nr2, m)
    | If c r ri p1 p2 =>
        let (xs,nr1,m) = flatten F p1 n m conts breaks in
        let (ys,nr2,m) = flatten F p2 n m conts breaks in
          if (p1 = Skip) /\ (p2 = Skip) then (List [],F,m)
          else if p1 = Skip then
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [Label n m 0],F,m+1)
          else if p2 = Skip then
            (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0]
              ++ xs ++
             List [Label n m 0],F,m+1)
          else if nr1 then
            (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0]
              ++ xs ++
             List [Label n m 0] ++ ys,nr2,m+1)
          else if nr2 then
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [Label n m 0] ++ xs,nr1,m+1)
          else
            (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             List [LabAsm (Jump (Lab n (m+1))) 0w [] 0; Label n m 0] ++
               xs ++
             List [Label n (m+1) 0],nr1 ∧ nr2,m+2)
    | Loop p1 =>
        let cont_lab = m in
        let break_lab = m+1 in
        let (xs,_,m) = flatten F p1 n (m+2) (cont_lab :: conts)
          (break_lab :: breaks) in
          (List [Label n cont_lab 0] ++
           xs ++
           List [LabAsm (Jump (Lab n cont_lab)) 0w [] 0;
                 Label n break_lab 0],F,m)
    | Raise r => (List [Asm (JumpReg r) [] 0],T,m)
    | Return r => (List [Asm (JumpReg r) [] 0],T,m)
    | Break k => (List [LabAsm (Jump (Lab n (find_lab k breaks))) 0w []
      0],T,m)
    | Continue k => (List [LabAsm (Jump (Lab n (find_lab k conts))) 0w
      [] 0],T,m)
    | RawCall n => (List [LabAsm (Jump (Lab n 1)) 0w [] 0],T,m)
    | Call NONE dest handler => (List [compile_jump dest],T,m)
    | Call (SOME (p1,lr,l1,l2)) dest handler =>
        let (xs,nr1,m) = flatten F p1 n m conts breaks in
        let prefix = List [LabAsm (LocValue lr (Lab l1 l2)) 0w [] 0;
                 compile_jump dest; Label l1 l2 0] ++ xs in
        (case handler of
        | NONE => (prefix, nr1, m)
        | SOME (p2,k1,k2) =>
            let (ys,nr2,m) = flatten F p2 n m conts breaks in
              (prefix ++ (List [LabAsm (Jump (Lab n m)) 0w [] 0; Label
                k1 k2 0] ++
              ys ++ List [Label n m 0]), nr1 ∧ nr2, m+1))
    | JumpLower r1 r2 target =>
        (List [LabAsm (JumpCmp Lower r1 (Reg r2) (Lab target 0)) 0w []
          0],F,m)
    | FFI ffi_index _ _ _ _ lr => (List [LabAsm (LocValue lr (Lab n m))
      0w [] 0;
                                         LabAsm (CallFFI ffi_index) 0w
                                           [] 0;
                                         Label n m 0],F,m+1)
    | LocValue i l1 l2 => (List [LabAsm (LocValue i (Lab l1 l2)) 0w []
      0],F,m)
    | Install _ _ _ _ ret =>
      (List [LabAsm (LocValue ret (Lab n m)) 0w [] 0;
      LabAsm Install 0w [] 0;
      Label n m 0],F,m+1)
    | ShMemOp op r ad => (List [Asm (ShareMem op r ad) [] 0],F,m)
    | CodeBufferWrite r1 r2 =>
      (List [Asm (Cbw r1 r2) [] 0],F,m)
    | _  => (List [],F,m)`
in
val flatten_def = Define flatten_quotation;
*)

let is_Seq_def = cake_define
  `is_Seq x1 =
      match x1 with
        (stackLang_Seq p1 p2) -> T
      | _1 -> F`;;

let prog_to_section_def = cake_define
  `prog_to_section (n,p) =
     (let (lines,_2,m) = (flatten T p n (next_lab p 2) [] []) in
       Section n (append (Append lines
         (List [Label n (if is_Seq p then m else 1) 0]))))`;;

let is_gen_gc_def = cake_define
  `is_gen_gc x1 =
        match x1 with
          (Generational l) -> T
        | _3 -> F`;;

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
       (MAP (prog_comp jump offset sp)
         (MAP prog_comp prog)))`;;
