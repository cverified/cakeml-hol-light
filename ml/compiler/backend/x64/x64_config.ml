(* ======================================================== *)
(*  x64_config: ported from HOL4's
    compiler/backend/x64/x64_configScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the compiler configuration for x64
*)

needs "compiler/backend/backend.ml";;
needs "compiler/backend/presLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: x64_target *)

let x64_names_def = cake_define
  `x64_names =
     ((
      // 16 regs, must avoid 4 and 5, names:
      // r0=rax, r1=rcx, r2=rdx, r3=rbx, r4=rsp, r5=rbp, r6=rsi,
      // r7=rdi, r8=r8, r9, r10, r11, r12, r13, r14, r15
      // The first six arguments are passed in registers. The first
      // argument (1) is passed in rdi(r7), the second(2) in rsi(r6),
      // the third(3) in rdx(r3), the fourth(4) in rcx(2), the fifth(5)
      // in r8 and the sixth in r9.
      // Callee-saved regs: r12-r15, rbx
      insert 1 7 o
      // arg 1
      insert 2 6 o
      // arg 2
      insert 3 2 o
      insert 4 1 o
      insert 5 8 o
      insert 6 9 o
      insert 11 14 o
      insert 12 13 o
      insert 13 12 o
      // the rest just ensures that the mapping is well-formed
      insert 7 3 o
      insert 8 15 o
      insert 9 11 o
      insert 14 4 o
      insert 15 5) LN:num spt)`;;

(* HOL4 x64_configScript.sml:38-39: a theorem that HOL4 states as the
   value of an ML expression: x64_names_def *)

(* HOL4 x64_configScript.sml:41-43: the ML values that the
   definitions below antiquote *)

(* HOL4 x64_configScript.sml:45-46: the ML values that the
   definitions below antiquote *)
(* perf_calls=T yields an unverified binary suitable for
   `perf record --call-graph fp` profiling (x64 only). *)
(* HOL4 x64_configScript.sml:49-50: the ML values that the
   definitions below antiquote *)

let x64_backend_config_def = cake_define
  `x64_backend_config =
              mk_backend_config prim_src_config
                (clos_to_bvl_default_config)
                (bvl_to_bvi_default_config) (mk_data_to_word_config 4
                4 2 32 F T T F F F Simple) (mk_word_to_word_config 2
                []) (mk_word_to_stack_config 0 LN)
                (mk_stack_to_lab_config x64_names T F)
                (mk_lab_to_target_config LN [] 0 5 NONE [] 104729) []
                default_tap_config []`;;
