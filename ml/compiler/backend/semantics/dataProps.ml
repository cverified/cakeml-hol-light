(* ======================================================== *)
(*  dataProps: ported from HOL4's
    compiler/backend/semantics/dataPropsScript.sml
    A proof theory, with 9 definitions and 149 theorems.  Needed by
    10 files of the port.  *)
(* ======================================================== *)

(*
  Properties about dataLang and its semantics
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/comparison.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["vars"];;

let OPTION_CASE_OPTION_MAP =
  cake_theorem "OPTION_CASE_OPTION_MAP[local]"
  (fun () ->
    `(option_CASE (OPTION_MAP f a) e g) = option_CASE a e (g o f)`)
  CHEAT_TAC;;

let _ = size_thms "dataSem_v";;
(* HOL4 dataPropsScript.sml:43-48: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let approx_of_def = cake_define_try_tac (fun () ->
  `(inv_image (MEASURE I LEX MEASURE (list_size dataSem_v_size))
                             (\(lims,vs,refs). (sptree_size
                               refs,vs)))`)
  CHEAT_TAC
  `approx_of lims x2 refs =
        match x2 with
          [] -> 0
        | (x :: y :: ys) ->
       approx_of lims [x] refs + approx_of lims (y :: ys) refs
        | [(Word64 _2:dataSem_v)] -> 3
        | [Number i] ->
       (if small_num (limits_arch_64_bit lims) i then 0 else
         bignum_size (limits_arch_64_bit lims) i)
        | [CodePtr _3] -> 0
        | [RefPtr _4 r] ->
        (match lookup r refs with NONE -> 0 | SOME (ByteArray _5 bs)
          -> LENGTH bs DIV (arch_size lims DIV 8) + 2 | SOME (ValueArray
          vs) ->
            approx_of lims vs (delete r refs) + LENGTH vs + 1 | SOME
              (Thunk _6 v) ->
            approx_of lims [v] (delete r refs) + 2 | SOME
              (bvlSem_MutBlock tg fin ls c rs) ->
            approx_of lims (ls ++ [c] ++ rs) (delete r refs) +
            LENGTH ls + LENGTH rs + 2)
        | [Block ts tag []] -> 0
        | [Block ts tag vs] ->
       approx_of lims vs refs + LENGTH vs + 1`;;

let size_of_approx_of = cake_theorem "size_of_approx_of"
  (fun () ->
    `!lims xs refs seen n1 refs1 seen1.
       size_of lims xs refs seen = (n1,refs1,seen1) ==>
       n1 <= approx_of lims xs refs`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:85: the ML values that the definitions
   below antiquote *)

let OPTION_MAP2_ADD_SOME_0 = cake_theorem "OPTION_MAP2_ADD_SOME_0[simp]"
  (fun () ->
    `OPTION_MAP2 (+) x (SOME 0) = x`)
  CHEAT_TAC;;

let OPTION_MAP2_MAX_CANCEL = cake_theorem "OPTION_MAP2_MAX_CANCEL[simp]"
  (fun () ->
    `OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) y = OPTION_MAP2 MAX x y`)
  CHEAT_TAC;;

(* ops that are not allowed_op have stack_consumed = NONE, which has to
   propagate through do_stack's safe_for_space computation *)
let OPTION_MAP2_NONE = cake_theorem "OPTION_MAP2_NONE[simp]"
  (fun () ->
    `OPTION_MAP2 f NONE y = NONE /\ OPTION_MAP2 f x NONE = NONE`)
  CHEAT_TAC;;

let the_NONE = cake_theorem "the_NONE[simp]"
  (fun () ->
    `the x NONE = x`)
  CHEAT_TAC;;

let dataProps_initial_state_simp =
  cake_theorem "initial_state_simp[simp]"
  (fun () ->
    `state_clock
       (initial_state f c co cc ts l ss k) = k /\
         dataSem_state_locals
       (initial_state f c co cc ts l ss k) = LN /\ state_code
       (initial_state f c co cc ts l ss k) = c /\ state_ffi
       (initial_state f c co cc ts l ss k) = f /\ compile_oracle
       (initial_state f c co cc ts l ss k) = co /\ compile
       (initial_state f c co cc ts l ss k) = cc /\ stack
       (initial_state f c co cc ts l ss k) = [] /\
         dataSem_state_peak_heap_length
       (initial_state f c co cc ts l ss k) = 0`)
  CHEAT_TAC;;

let dataProps_initial_state_with_simp =
  cake_theorem "initial_state_with_simp[simp]"
  (fun () ->
    `(state_clock_fupd (K k') (initial_state f c co cc ts l ss k) =
  initial_state f c co cc ts l ss k') /\
     (stack_fupd (K []) (initial_state f c co cc ts l ss k) =
       initial_state f c co cc ts l ss k) /\
     (dataSem_state_locals_fupd (K LN) (initial_state f c co cc
       ts l ss k) = initial_state f c co cc ts l ss k)`)
  CHEAT_TAC;;
(* HOL4 dataPropsScript.sml:133-153: code that the source has in a
   comment *)
let do_stack_const = cake_theorem "do_stack_const[simp]"
  (fun () ->
    `dataSem_state_locals
       (do_stack op vs s) = dataSem_state_locals s /\
     dataSem_state_locals_size (do_stack op vs s) =
       dataSem_state_locals_size s /\
     stack (do_stack op vs s) = stack s /\
     dataSem_state_stack_frame_sizes (do_stack op vs s) =
       dataSem_state_stack_frame_sizes s /\
     dataSem_state_global (do_stack op vs s) = dataSem_state_global
       s /\
     dataSem_state_handler (do_stack op vs s) =
       dataSem_state_handler s /\
     state_refs (do_stack op vs s) = state_refs s /\
     compile (do_stack op vs s) = compile s /\
     state_clock (do_stack op vs s) = state_clock s /\
     state_code (do_stack op vs s) = state_code s /\
     state_ffi (do_stack op vs s) = state_ffi s /\
     dataSem_state_space (do_stack op vs s) = dataSem_state_space s
       /\
     dataSem_state_tstamps (do_stack op vs s) =
       dataSem_state_tstamps s /\
     dataSem_state_limits (do_stack op vs s) = dataSem_state_limits
       s /\
     dataSem_state_peak_heap_length (do_stack op vs s) =
       dataSem_state_peak_heap_length s /\ compile_oracle (do_stack op
       vs s) = compile_oracle s`)
  CHEAT_TAC;;

let dataProps_Boolv_11 = cake_theorem "Boolv_11[simp]"
  (fun () ->
    `dataSem_Boolv b1 = Boolv b2 <=> b1 = b2`)
  CHEAT_TAC;;

let with_same_locals = cake_theorem "with_same_locals"
  (fun () ->
    `(dataSem_state_locals_fupd (K (dataSem_state_locals s)) s) = s`)
  CHEAT_TAC;;

let var_corr_def = cake_define
  `var_corr env corr t <=>
     EVERY2 (\v x. dataSem_get_var v t = SOME x) corr env`;;

let get_vars_thm = cake_theorem "get_vars_thm"
  (fun () ->
    `!vs a t2. var_corr a vs t2 ==> (dataSem_get_vars vs t2 = SOME a)`)
  CHEAT_TAC;;

let get_vars_append = cake_theorem "get_vars_append"
  (fun () ->
    `!l1 l2 s. dataSem_get_vars (l1 ++ l2) s = OPTION_BIND
  (dataSem_get_vars l1 s) (\y1. OPTION_BIND (dataSem_get_vars l2 s)
  (\y2. SOME (y1 ++ y2)))`)
  CHEAT_TAC;;

let get_vars_reverse = cake_theorem "get_vars_reverse"
  (fun () ->
    `!ls s ys. dataSem_get_vars ls s = SOME ys ==> dataSem_get_vars
  (REVERSE ls) s = SOME (REVERSE ys)`)
  CHEAT_TAC;;

let EVERY_get_vars = cake_theorem "EVERY_get_vars"
  (fun () ->
    `!args s1 s2.
        EVERY (\a. lookup a s1 = lookup a s2) args ==>
        (dataSem_get_vars args s1 = dataSem_get_vars args s2)`)
  CHEAT_TAC;;

let get_vars_IMP_domain = cake_theorem "get_vars_IMP_domain"
  (fun () ->
    `!args x s vs. MEM x args /\ (dataSem_get_vars args s = SOME vs) ==>
                    x IN domain s`)
  CHEAT_TAC;;

let cut_state_opt_with_const = cake_theorem "cut_state_opt_with_const"
  (fun () ->
    `(dataSem_cut_state_opt x (stack_fupd (K z) y) = OPTION_MAP (\s.
  stack_fupd (K z) s) (dataSem_cut_state_opt x y)) /\
      (dataSem_cut_state_opt x (state_clock_fupd (K k) y) =
        OPTION_MAP (\s. state_clock_fupd (K k) s) (dataSem_cut_state_opt
        x y)) /\
     (dataSem_cut_state_opt x (dataSem_state_locals_size_fupd (K
       lsz) y) = OPTION_MAP (\s. dataSem_state_locals_size_fupd (K
       lsz) s) (dataSem_cut_state_opt x y))`)
  CHEAT_TAC;;

(* INFO: only used in bvi_to_dataProof *)
let consume_space_add_space = cake_theorem "consume_space_add_space"
  (fun () ->
    `?sf hp. consume_space k (add_space (dataSem_state_locals_fupd (K
  env1) t) k) =
             SOME (dataSem_state_peak_heap_length_fupd (K hp)
               (dataSem_state_safe_for_space_fupd (K sf)
               (dataSem_state_space_fupd (K 0)
               (dataSem_state_locals_fupd (K env1) t))))`)
  CHEAT_TAC;;

let consume_space_with_stack =
  cake_theorem "consume_space_with_stack[local]"
  (fun () ->
    `consume_space x (stack_fupd (K z) y) = OPTION_MAP (\s. stack_fupd
  (K z) s) (consume_space x y)`)
  CHEAT_TAC;;

let consume_space_with_locals =
  cake_theorem "consume_space_with_locals[local]"
  (fun () ->
    `consume_space x (dataSem_state_locals_fupd (K z) y) = OPTION_MAP
  (\s. dataSem_state_locals_fupd (K z) s) (consume_space x y)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:263: code that the source has in a
   comment *)
(* HOL4 dataPropsScript.sml:264-268: a proof *)

(* HOL4 dataPropsScript.sml:270: code that the source has in a
   comment *)
let do_app_with_stack = cake_theorem "do_app_with_stack[local]"
  (fun () ->
    `do_app op vs (stack_fupd (K z) s) =
      map_result (\(x,y). (x,dataSem_state_peak_heap_length_fupd (K
        ((\op vs s. if op = Install then dataSem_state_peak_heap_length
        s else if MEM op [closLang_IntOp Greater; closLang_IntOp
        closLang_GreaterEq] then dataSem_state_peak_heap_length s else
        (\op vs s. if op_space_reset op then (\k op_args s. MAX
        (dataSem_state_peak_heap_length s) (size_of_heap_args op_args s
        + k)) (space_consumed s op vs) vs s else
        dataSem_state_peak_heap_length s) op vs s) op vs (stack_fupd (K
        z) s))) (dataSem_state_stack_max_fupd (K
        (dataSem_state_stack_max (do_stack op vs (stack_fupd (K z) s))))
        (dataSem_state_safe_for_space_fupd (K ((\op vs s. if allowed_op
        op (LENGTH vs) then ((\op vs s. if op_space_reset op then
                      dataSem_state_safe_for_space s /\
                      no_thunks_in_refs (dataSem_state_refs s) /\
                          size_of_heap_args vs s + space_consumed s
                            op vs <= limits_heap_limit
                            (dataSem_state_limits s) else
                            dataSem_state_safe_for_space s) op vs s /\
                       lim_safe (dataSem_state_limits s) op vs /\
                         the F (OPTION_MAP ((>) (limits_stack_limit
                         (dataSem_state_limits s)))
                              (OPTION_MAP2 (+) (stack_consumed
                                (dataSem_state_stack_frame_sizes s)
                                (dataSem_state_limits s) op vs)
                              (OPTION_MAP2 (+) (size_of_stack
                                (dataSem_state_stack s))
                                (dataSem_state_locals_size s))))) else
                                F) op vs (stack_fupd (K z) s)))
                                (stack_fupd (K z) y)))))
                 I (do_app op vs s)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:296: code that the source has in a
   comment *)
let do_app_with_stack_and_locals =
  cake_theorem "do_app_with_stack_and_locals[local]"
  (fun () ->
    `do_app op vs (stack_fupd (K z) (dataSem_state_locals_size_fupd (K
  lsz) s)) =
     map_result (\(x,y). (x,dataSem_state_peak_heap_length_fupd (K
       ((\op vs s. if op = Install then dataSem_state_peak_heap_length s
       else if MEM op [closLang_IntOp Greater; closLang_IntOp
       closLang_GreaterEq] then dataSem_state_peak_heap_length s else
       (\op vs s. if op_space_reset op then (\k op_args s. MAX
       (dataSem_state_peak_heap_length s) (size_of_heap_args op_args s +
       k)) (space_consumed s op vs) vs s else
       dataSem_state_peak_heap_length s) op vs s) op vs (stack_fupd (K
       z) (dataSem_state_locals_size_fupd (K lsz) s))))
       (dataSem_state_stack_max_fupd (K (dataSem_state_stack_max
       (do_stack op vs (stack_fupd (K z) (dataSem_state_locals_size_fupd
       (K lsz) s))))) (dataSem_state_safe_for_space_fupd (K ((\op vs s.
       if allowed_op op (LENGTH vs) then ((\op vs s. if op_space_reset
       op then
                      dataSem_state_safe_for_space s /\
                      no_thunks_in_refs (dataSem_state_refs s) /\
                          size_of_heap_args vs s + space_consumed s
                            op vs <= limits_heap_limit
                            (dataSem_state_limits s) else
                            dataSem_state_safe_for_space s) op vs s /\
                       lim_safe (dataSem_state_limits s) op vs /\
                         the F (OPTION_MAP ((>) (limits_stack_limit
                         (dataSem_state_limits s)))
                              (OPTION_MAP2 (+) (stack_consumed
                                (dataSem_state_stack_frame_sizes s)
                                (dataSem_state_limits s) op vs)
                              (OPTION_MAP2 (+) (size_of_stack
                                (dataSem_state_stack s))
                                (dataSem_state_locals_size s))))) else
                                F) op vs (stack_fupd (K z)
                                (dataSem_state_locals_size_fupd (K lsz)
                                s)))) (dataSem_state_locals_size_fupd (K
                                lsz) (stack_fupd (K z) y))))))
                 I (do_app op vs s)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:324: code that the source has in a
   comment *)
let do_app_aux_with_space = cake_theorem "do_app_aux_with_space"
  (fun () ->
    `dataSem_do_app_aux op vs (dataSem_state_space_fupd (K z) s) =
  map_result (\(x,y). (x,dataSem_state_space_fupd (K z) y)) I
  (dataSem_do_app_aux op vs s)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:342: code that the source has in a
   comment *)
let do_app_aux_with_locals = cake_theorem "do_app_aux_with_locals"
  (fun () ->
    `dataSem_do_app_aux op vs (dataSem_state_locals_fupd (K z) s) =
  map_result (\(x,y). (x,dataSem_state_locals_fupd (K z) y)) I
  (dataSem_do_app_aux op vs s)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:360: code that the source has in a
   comment *)
let do_app_with_locals = cake_theorem "do_app_with_locals"
  (fun () ->
    `do_app op vs (dataSem_state_locals_fupd (K z) s) =
     map_result (\(x,y). (x,dataSem_state_peak_heap_length_fupd (K
       ((\op vs s. if op = Install then dataSem_state_peak_heap_length s
       else if MEM op [closLang_IntOp Greater; closLang_IntOp
       closLang_GreaterEq] then dataSem_state_peak_heap_length s else
       (\op vs s. if op_space_reset op then (\k op_args s. MAX
       (dataSem_state_peak_heap_length s) (size_of_heap_args op_args s +
       k)) (space_consumed s op vs) vs s else
       dataSem_state_peak_heap_length s) op vs s) op vs
       (dataSem_state_locals_fupd (K z) s)))
       (dataSem_state_stack_max_fupd (K (dataSem_state_stack_max
       (do_stack op vs (dataSem_state_locals_fupd (K z) s))))
       (dataSem_state_safe_for_space_fupd (K ((\op vs s. if allowed_op
       op (LENGTH vs) then ((\op vs s. if op_space_reset op then
                      dataSem_state_safe_for_space s /\
                      no_thunks_in_refs (dataSem_state_refs s) /\
                          size_of_heap_args vs s + space_consumed s
                            op vs <= limits_heap_limit
                            (dataSem_state_limits s) else
                            dataSem_state_safe_for_space s) op vs s /\
                       lim_safe (dataSem_state_limits s) op vs /\
                         the F (OPTION_MAP ((>) (limits_stack_limit
                         (dataSem_state_limits s)))
                              (OPTION_MAP2 (+) (stack_consumed
                                (dataSem_state_stack_frame_sizes s)
                                (dataSem_state_limits s) op vs)
                              (OPTION_MAP2 (+) (size_of_stack
                                (dataSem_state_stack s))
                                (dataSem_state_locals_size s))))) else
                                F) op vs (dataSem_state_locals_fupd (K
                                z) s))) (dataSem_state_locals_fupd (K z)
                                y)))))
                          I (do_app op vs s)`)
  CHEAT_TAC;;

let do_app_aux_err = cake_theorem "do_app_aux_err"
  (fun () ->
    `dataSem_do_app_aux op vs s = Rerr e ==>
                              (e = Rabort Rtype_error) \/
                              (?i x. op = FFI i /\ e = Rabort
                                (Rffi_error x))`)
  CHEAT_TAC;;

let dataProps_do_app_aux_const = cake_theorem "do_app_aux_const"
  (fun () ->
    `dataSem_do_app_aux op vs x = Rval (y,z) ==> stack
     z = stack x /\ dataSem_state_handler z = dataSem_state_handler
       x /\ dataSem_state_locals z = dataSem_state_locals x /\
       state_clock
     z = state_clock x /\ compile z = compile x`)
  CHEAT_TAC;;

let dataProps_do_app_err = cake_theorem "do_app_err"
  (fun () ->
    `do_app op vs s = Rerr e ==>
                              (e = Rabort Rtype_error) \/
                              (?i x. op = FFI i /\ e = Rabort
                                (Rffi_error x))`)
  CHEAT_TAC;;

let dataProps_do_app_const = cake_theorem "do_app_const"
  (fun () ->
    `do_app op vs x = Rval (y,z) ==> stack
      z = stack x /\ dataSem_state_handler z =
        dataSem_state_handler x /\ dataSem_state_locals z =
        dataSem_state_locals x /\ state_clock
      z = state_clock x /\ compile z = compile x`)
  CHEAT_TAC;;

let do_app_locals = cake_theorem "do_app_locals"
  (fun () ->
    `(do_app op x s = Rval (q,r)) ==>
     (do_app op x (dataSem_state_locals_fupd (K extra) s) =
           Rval (q,dataSem_state_peak_heap_length_fupd (K ((\op vs
             s. if op = Install then dataSem_state_peak_heap_length s
             else if MEM op [closLang_IntOp Greater; closLang_IntOp
             closLang_GreaterEq] then dataSem_state_peak_heap_length s
             else (\op vs s. if op_space_reset op then (\k op_args s.
             MAX (dataSem_state_peak_heap_length s) (size_of_heap_args
             op_args s + k)) (space_consumed s op vs) vs s else
             dataSem_state_peak_heap_length s) op vs s) op x
             (dataSem_state_locals_fupd (K extra) s)))
             (dataSem_state_stack_max_fupd (K (dataSem_state_stack_max
             (do_stack op x (dataSem_state_locals_fupd (K extra) s))))
             (dataSem_state_safe_for_space_fupd (K ((\op vs s. if
             allowed_op op (LENGTH vs) then ((\op vs s. if
             op_space_reset op then
                     dataSem_state_safe_for_space s /\
                     no_thunks_in_refs (dataSem_state_refs s) /\
                         size_of_heap_args vs s + space_consumed s
                           op vs <= limits_heap_limit
                           (dataSem_state_limits s) else
                           dataSem_state_safe_for_space s) op vs s /\
                      lim_safe (dataSem_state_limits s) op vs /\
                        the F (OPTION_MAP ((>) (limits_stack_limit
                        (dataSem_state_limits s)))
                             (OPTION_MAP2 (+) (stack_consumed
                               (dataSem_state_stack_frame_sizes s)
                               (dataSem_state_limits s) op vs)
                              (OPTION_MAP2 (+) (size_of_stack
                                (dataSem_state_stack s))
                                (dataSem_state_locals_size s))))) else
                                F) op x (dataSem_state_locals_fupd (K
                                extra) s))) (dataSem_state_locals_fupd
                                (K extra) r)))))`)
  CHEAT_TAC;;

let do_space_alt = cake_theorem "do_space_alt"
  (fun () ->
    `do_space op vs s =
         (if op_space_reset op then SOME
           (dataSem_state_peak_heap_length_fupd (K ((\op vs s. if
           op_space_reset op then (\k op_args s. MAX
           (dataSem_state_peak_heap_length s) (size_of_heap_args op_args
           s + k)) (space_consumed s op vs) vs s else
           dataSem_state_peak_heap_length s) op vs s))
           (dataSem_state_safe_for_space_fupd (K ((\op vs s. if
           op_space_reset op then
                      dataSem_state_safe_for_space s /\
                      no_thunks_in_refs (dataSem_state_refs s) /\
                          size_of_heap_args vs s + space_consumed
                            s op vs <= limits_heap_limit
                            (dataSem_state_limits s) else
                            dataSem_state_safe_for_space s) op vs s))
                            (dataSem_state_space_fupd (K 0) s))) else
                            consume_space (op_space_req op (LENGTH
                            vs)) s)`)
  CHEAT_TAC;;

let Seq_Skip = cake_theorem "Seq_Skip"
  (fun () ->
    `evaluate ((Seq c Skip:dataLang_prog),s) = evaluate (c,s)`)
  CHEAT_TAC;;

let evaluate_safe_alt = cake_theorem "evaluate_safe_alt"
  (fun () ->
    `!c s. evaluate_safe c s = dataSem_state_safe_for_space (SND
  (evaluate (c,s)))`)
  CHEAT_TAC;;

let evaluate_peak_alt = cake_theorem "evaluate_peak_alt"
  (fun () ->
    `!c s. evaluate_peak c s = dataSem_state_peak_heap_length (SND
  (evaluate (c,s)))`)
  CHEAT_TAC;;

let size_of_heap_with_safe = cake_theorem "size_of_heap_with_safe"
  (fun () ->
    `!s safe. size_of_heap (dataSem_state_safe_for_space_fupd (K safe)
  s) = size_of_heap s`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:484: code that the source has in a
   comment *)
(* HOL4 dataPropsScript.sml:485-509: a proof *)


let do_app_aux_safe_peak_swap = cake_theorem "do_app_aux_safe_peak_swap"
  (fun () ->
    `!op vs s q s' safe peak.
       dataSem_do_app_aux op vs s = Rval (q,s') ==> (?safe' peak'.
           dataSem_do_app_aux op vs
             (dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_safe_for_space_fupd (K safe) s)) =
           Rval (q,dataSem_state_peak_heap_length_fupd (K peak')
             (dataSem_state_safe_for_space_fupd (K safe') s')))`)
  CHEAT_TAC;;

let do_app_safe_peak_swap = cake_theorem "do_app_safe_peak_swap"
  (fun () ->
    `!op vs s q s' safe peak.
      do_app op vs s = Rval (q,s') ==> (?new_safe new_peak.
              do_app op vs (dataSem_state_peak_heap_length_fupd (K
                peak) (dataSem_state_safe_for_space_fupd (K safe) s)) =
              Rval (q,dataSem_state_peak_heap_length_fupd (K
                new_peak) (dataSem_state_safe_for_space_fupd (K
                new_safe) s')))`)
  CHEAT_TAC;;

let do_app_err_safe_peak_swap = cake_theorem "do_app_err_safe_peak_swap"
  (fun () ->
    `!op vs s e safe peak.
       do_app op vs s = Rerr e ==> do_app op vs
         (dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe) s)) =
         Rerr e`)
  CHEAT_TAC;;

let do_app_lss_sm_safe_peak_swap_aux =
  cake_theorem "do_app_lss_sm_safe_peak_swap_aux[local]"
  (fun () ->
    `!op vs s q s' lss smx safe peak.
       do_app op vs s = Rval (q,s') ==> (?safe' peak' lss' smx'.
           do_app op vs (dataSem_state_peak_heap_length_fupd (K
             peak) (dataSem_state_safe_for_space_fupd (K safe)
             (dataSem_state_stack_max_fupd (K smx)
             (dataSem_state_locals_size_fupd (K lss) s)))) =
           Rval (q,dataSem_state_peak_heap_length_fupd (K peak')
             (dataSem_state_safe_for_space_fupd (K safe')
             (dataSem_state_stack_max_fupd (K smx')
             (dataSem_state_locals_size_fupd (K lss') s')))))`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:550-551: a theorem that HOL4 states as
   the value of an ML expression: do_app_lss_sm_safe_peak_swap *)

let do_app_sm_safe_peak_swap_aux =
  cake_theorem "do_app_sm_safe_peak_swap_aux[local]"
  (fun () ->
    `!op vs s q s' smx safe peak.
       do_app op vs s = Rval (q,s') ==> (?safe' peak' smx'.
           do_app op vs (dataSem_state_peak_heap_length_fupd (K
             peak) (dataSem_state_safe_for_space_fupd (K safe)
             (dataSem_state_stack_max_fupd (K smx) s))) =
           Rval (q,dataSem_state_peak_heap_length_fupd (K peak')
             (dataSem_state_safe_for_space_fupd (K safe')
             (dataSem_state_stack_max_fupd (K smx') s'))))`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:564-565: a theorem that HOL4 states as
   the value of an ML expression: do_app_sm_safe_peak_swap *)

let do_app_aux_sm_safe_peak_swap =
  cake_theorem "do_app_aux_sm_safe_peak_swap"
  (fun () ->
    `!op vs s q s' smx safe peak.
       dataSem_do_app_aux op vs s = Rval (q,s') ==> (?safe' peak'
         smx'.
           dataSem_do_app_aux op vs
             (dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_safe_for_space_fupd (K safe)
             (dataSem_state_stack_max_fupd (K smx) s))) =
           Rval (q,dataSem_state_peak_heap_length_fupd (K peak')
             (dataSem_state_safe_for_space_fupd (K safe')
             (dataSem_state_stack_max_fupd (K smx') s'))))`)
  CHEAT_TAC;;


let do_app_aux_lss_sm_safe_peak_swap =
  cake_theorem "do_app_aux_lss_sm_safe_peak_swap"
  (fun () ->
    `!op vs s q s' lss smx safe peak.
       dataSem_do_app_aux op vs s = Rval (q,s') ==> (?safe' peak'
         lss' smx'.
           dataSem_do_app_aux op vs
             (dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_safe_for_space_fupd (K safe)
             (dataSem_state_stack_max_fupd (K smx)
             (dataSem_state_locals_size_fupd (K lss) s)))) =
           Rval (q,dataSem_state_peak_heap_length_fupd (K peak')
             (dataSem_state_safe_for_space_fupd (K safe')
             (dataSem_state_stack_max_fupd (K smx')
             (dataSem_state_locals_size_fupd (K lss') s')))))`)
  CHEAT_TAC;;

let do_app_err_lss_sm_safe_peak_swap =
  cake_theorem "do_app_err_lss_sm_safe_peak_swap"
  (fun () ->
    `!op vs s e lss smx safe peak.
       do_app op vs s = Rerr e ==> do_app op vs
         (dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe)
         (dataSem_state_stack_max_fupd (K smx)
         (dataSem_state_locals_size_fupd (K lss) s)))) =
         Rerr e`)
  CHEAT_TAC;;

let do_app_err_sm_safe_peak_swap =
  cake_theorem "do_app_err_sm_safe_peak_swap"
  (fun () ->
    `!op vs s e smx safe peak.
       do_app op vs s = Rerr e ==> do_app op vs
         (dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe)
         (dataSem_state_stack_max_fupd (K smx) s))) =
         Rerr e`)
  CHEAT_TAC;;


let do_app_lss_stk_stfrm_swap_aux =
  cake_theorem "do_app_lss_stk_stfrm_swap_aux[local]"
  (fun () ->
    `!op vs s q s' lss stk stfrm. do_app op vs s = Rval (q,s') ==>
       (?ss pk smx. do_app op vs
         (dataSem_state_stack_frame_sizes_fupd (K stfrm) (stack_fupd (K
         stk) (dataSem_state_locals_size_fupd (K lss) s))) =
         Rval (q,dataSem_state_peak_heap_length_fupd (K pk)
           (dataSem_state_safe_for_space_fupd (K ss)
           (dataSem_state_stack_max_fupd (K smx)
           (dataSem_state_stack_frame_sizes_fupd (K (if op = Install
           then LN else stfrm)) (stack_fupd (K stk)
           (dataSem_state_locals_size_fupd (K lss) s')))))))`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:621: a theorem that HOL4 states as the
   value of an ML expression: do_app_lss_stk_stfrm_swap *)

let do_app_err_lss_stk_stfrm_swap =
  cake_theorem "do_app_err_lss_stk_stfrm_swap"
  (fun () ->
    `!op vs s lss stk stfrm.
       do_app op vs s = Rerr e ==> do_app op vs
         (dataSem_state_stack_frame_sizes_fupd (K stfrm) (stack_fupd (K
         stk) (dataSem_state_locals_size_fupd (K lss) s))) =
         Rerr e`)
  CHEAT_TAC;;

let do_app_lim_swap_aux = cake_theorem "do_app_lim_swap_aux[local]"
  (fun () ->
    `!op vs s q s' lim.
       do_app op vs s = Rval (q,s') ==> (?safe peak smx.
           do_app op vs (dataSem_state_limits_fupd (K lim) s) =
           Rval (q,dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_safe_for_space_fupd (K safe)
             (dataSem_state_stack_max_fupd (K smx)
             (dataSem_state_limits_fupd (K lim) s')))))`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:643: a theorem that HOL4 states as the
   value of an ML expression: do_app_lim_swap *)


let do_app_err_lim_swap = cake_theorem "do_app_err_lim_swap"
  (fun () ->
    `!op vs s e lim.
       do_app op vs s = Rerr e ==> do_app op vs
         (dataSem_state_limits_fupd (K lim) s) =
         Rerr e`)
  CHEAT_TAC;;

let size_of_stack_eq = cake_theorem "size_of_stack_eq"
  (fun () ->
    `(size_of_stack ((Env n l:dataSem_stack) :: stack) = OPTION_MAP2 (+)
  n (size_of_stack stack)) /\
     (size_of_stack (dataSem_Exc n v1 v2 :: stack) =
        OPTION_MAP2 (+) (OPTION_MAP ((+) 3) n) (size_of_stack
          stack)) /\
     (size_of_stack [] = SOME 1)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:663-676: a proof *)

(* HOL4 dataPropsScript.sml:678-686: a proof *)

(* HOL4 dataPropsScript.sml:688-691: a proof *)


(* The field-swap (stack_max/safe_for_space/peak_heap_length) commutes through
   the narrow cut in evaluate(Assign), since cut_state_opt only touches locals. *)
let cut_state_opt_with_swap =
  cake_theorem "cut_state_opt_with_swap[local]"
  (fun () ->
    `dataSem_cut_state_opt names_opt
  (dataSem_state_peak_heap_length_fupd (K peak)
  (dataSem_state_safe_for_space_fupd (K safe)
  (dataSem_state_stack_max_fupd (K smx) s))) =
     OPTION_MAP (\t. dataSem_state_peak_heap_length_fupd (K peak)
       (dataSem_state_safe_for_space_fupd (K safe)
       (dataSem_state_stack_max_fupd (K smx) t)))
                (dataSem_cut_state_opt names_opt s)`)
  CHEAT_TAC;;

let cut_state_opt_stack_max =
  cake_theorem "cut_state_opt_stack_max[local]"
  (fun () ->
    `dataSem_cut_state_opt names_opt s = SOME s2 ==>
  dataSem_state_stack_max s2 = dataSem_state_stack_max s`)
  CHEAT_TAC;;

(* When the swap leaves stack_max at its original value (the fl=F case),
   the merged input update collapses to just safe_for_space/peak_heap_length. *)
let cut_state_opt_swap_input =
  cake_theorem "cut_state_opt_swap_input[local]"
  (fun () ->
    `dataSem_cut_state_opt names_opt s = SOME s2 ==>
  dataSem_state_peak_heap_length_fupd (K peak)
  (dataSem_state_safe_for_space_fupd (K safe)
  (dataSem_state_stack_max_fupd (K (dataSem_state_stack_max s))
       s2)) = dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe)
       s2)`)
  CHEAT_TAC;;


let evaluate_fl_smx_safe_peak_swap_aux =
  cake_theorem "evaluate_fl_smx_safe_peak_swap_aux[local]"
  (fun () ->
    `!c s r s' fl smx safe peak.
      evaluate (c,s) = (r,s') ==>
        (if fl then (let s0 = dataSem_state_peak_heap_length_fupd
          (K peak) (dataSem_state_safe_for_space_fupd (K safe)
          (dataSem_state_stack_max_fupd (K smx) s)) in ?smx safe peak.
          evaluate (c,s0) =
                      (r,dataSem_state_peak_heap_length_fupd (K
                        peak) (dataSem_state_safe_for_space_fupd (K
                        safe) (dataSem_state_stack_max_fupd (K smx)
                        s')))) else
          (let s0 = dataSem_state_peak_heap_length_fupd (K peak)
            (dataSem_state_safe_for_space_fupd (K safe)
            (dataSem_state_stack_max_fupd (K (dataSem_state_stack_max
            s)) s)) in ?smx safe peak. evaluate (c,s0) =
               (r,dataSem_state_peak_heap_length_fupd (K peak)
                 (dataSem_state_safe_for_space_fupd (K safe)
                 (dataSem_state_stack_max_fupd (K
                 (dataSem_state_stack_max s')) s')))))`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:876-877: a theorem that HOL4 states as
   the value of an ML expression: evaluate_smx_safe_peak_swap_aux *)
(* HOL4 dataPropsScript.sml:878: a theorem that HOL4 states as the
   value of an ML expression: evaluate_smx_safe_peak_swap *)


(* HOL4 dataPropsScript.sml:881-882: a theorem that HOL4 states as
   the value of an ML expression: evaluate_safe_peak_swap_aux *)

let evaluate_safe_peak_swap = cake_theorem "evaluate_safe_peak_swap"
  (fun () ->
    `!safe s' s r peak c.
       evaluate (c,s) = (r,s') ==>
       (?safe' peak'.
           evaluate
             (c,dataSem_state_peak_heap_length_fupd (K peak)
               (dataSem_state_safe_for_space_fupd (K safe) s)) =
           (r,dataSem_state_peak_heap_length_fupd (K peak')
             (dataSem_state_safe_for_space_fupd (K safe') s')))`)
  CHEAT_TAC;;

let same_stack_size_def = cake_define
  `same_stack_size x y <=> size_of_stack_frame x =
  size_of_stack_frame y`;;

let same_stack_size_size_of_stack =
  cake_theorem "same_stack_size_size_of_stack"
  (fun () ->
    `!xs ys.
     LIST_REL same_stack_size xs ys ==>
     size_of_stack xs = size_of_stack ys`)
  CHEAT_TAC;;

let s_peak_heap = cake_theorem "s_peak_heap[simp]"
  (fun () ->
    `dataSem_state_peak_heap_length_fupd (K
  (dataSem_state_peak_heap_length s))
       s = s /\ dataSem_state_safe_for_space_fupd (K
         (dataSem_state_safe_for_space s))
       s = s /\ dataSem_state_stack_max_fupd (K
         (dataSem_state_stack_max s))
       s = s /\ dataSem_state_locals_size_fupd (K
         (dataSem_state_locals_size s))
       s = s /\ dataSem_state_safe_for_space_fupd (K ssnew)
         (state_clock_fupd (K clock) (dataSem_state_stack_max_fupd (K
         smnew) (stack_fupd (K (stack s))
       s))) = dataSem_state_safe_for_space_fupd (K ssnew)
         (state_clock_fupd (K clock) (dataSem_state_stack_max_fupd (K
         smnew) s)) /\ dataSem_state_peak_heap_length_fupd (K plnnew)
         (dataSem_state_safe_for_space_fupd (K ssnew)
         (dataSem_state_handler_fupd (K (dataSem_state_handler s))
       s)) = dataSem_state_peak_heap_length_fupd (K plnnew)
         (dataSem_state_safe_for_space_fupd (K ssnew) s)`)
  CHEAT_TAC;;

let evaluate_stack_and_locals_swap =
  cake_theorem "evaluate_stack_and_locals_swap"
  (fun () ->
    `!c (s:('c,'ffi)dataSem_state).
        match evaluate (c,s) with (SOME (Rerr (Rabort
          Rtype_error)),s1) -> T | (SOME (Rerr (Rabort a)),s1) ->
                 (stack s1 = []) /\ (!xs lsz. (LENGTH
                   (dataSem_state_stack s) = LENGTH xs) ==>
                          (?lss sfs smx phl.
                          evaluate
                            (c,dataSem_state_locals_size_fupd (K lsz)
                            (dataSem_state_stack_fupd (K xs) s)) =
                            (SOME (Rerr (Rabort
                              a)),dataSem_state_peak_heap_length_fupd (K
                              phl) (dataSem_state_stack_max_fupd (K smx)
                              (dataSem_state_safe_for_space_fupd (K sfs)
                              (dataSem_state_locals_size_fupd (K lss)
                              s1)))))) | (SOME (Rerr (Rraise t)),s1) ->
                   (?s2. (dataSem_jump_exc s = SOME s2) /\
                     (dataSem_state_locals s2 = dataSem_state_locals s1)
                     /\
                         (stack s2 = stack s1) /\
                           (dataSem_state_handler s2 =
                           dataSem_state_handler s1) /\
                         (!xs s7 lsz. (dataSem_jump_exc
                           (dataSem_state_locals_size_fupd (K lsz)
                           (dataSem_state_stack_fupd (K xs) s)) = SOME
                           s7) /\
                              (LENGTH (dataSem_state_stack s) =
                                LENGTH xs) ==>
                              (?lss sfs smx phl.
                              (evaluate
                                (c,dataSem_state_locals_size_fupd (K
                                lsz) (dataSem_state_stack_fupd (K xs)
                                s)) =
                              (SOME (Rerr (Rraise
                                t)),dataSem_state_peak_heap_length_fupd
                                (K phl) (dataSem_state_stack_max_fupd (K
                                smx) (dataSem_state_safe_for_space_fupd
                                (K sfs) (dataSem_state_locals_size_fupd
                                (K lss) (dataSem_state_locals_fupd (K
                                (dataSem_state_locals s7))
                                (dataSem_state_handler_fupd (K
                                (dataSem_state_handler s7)) (stack_fupd
                                (K (stack s7))
                              s1))))))))))) | (res,s1) -> (stack s1
                                = dataSem_state_stack s) /\
                                (dataSem_state_handler s1 =
                                dataSem_state_handler s) /\
                           (!xs lsz. (LENGTH (dataSem_state_stack
                             s) = LENGTH xs) ==>
                              (?lss sfs smx phl.
                              evaluate
                                (c,dataSem_state_locals_size_fupd (K
                                lsz) (dataSem_state_stack_fupd (K xs)
                                s)) =
                              (res
                                ,dataSem_state_peak_heap_length_fupd
                                (K phl) (dataSem_state_stack_max_fupd
                                (K smx)
                                (dataSem_state_safe_for_space_fupd (K
                                sfs) (stack_fupd (K xs)
                                (dataSem_state_locals_size_fupd (K
                                lss) s1)))))))`)
  CHEAT_TAC;;

let evaluate_stack_swap = cake_theorem "evaluate_stack_swap"
  (fun () ->
    `!c (s:('c,'ffi)dataSem_state).
        match evaluate (c,s) with (SOME (Rerr (Rabort
          Rtype_error)),s1) -> T | (SOME (Rerr (Rabort a)),s1) ->
                 (stack s1 = []) /\ (!xs. (LENGTH
                   (dataSem_state_stack s) = LENGTH xs) ==>
                          (?lss sfs smx phl.
                          evaluate (c,dataSem_state_stack_fupd (K
                            xs) s) =
                            (SOME (Rerr (Rabort
                              a)),dataSem_state_peak_heap_length_fupd (K
                              phl) (dataSem_state_stack_max_fupd (K smx)
                              (dataSem_state_safe_for_space_fupd (K sfs)
                              (dataSem_state_locals_size_fupd (K lss)
                              s1)))))) | (SOME (Rerr (Rraise t)),s1) ->
                   (?s2. (dataSem_jump_exc s = SOME s2) /\
                     (dataSem_state_locals s2 = dataSem_state_locals s1)
                     /\
                         (stack s2 = stack s1) /\
                           (dataSem_state_handler s2 =
                           dataSem_state_handler s1) /\
                         (!xs s7. (dataSem_jump_exc
                           (dataSem_state_stack_fupd (K xs) s) = SOME
                           s7) /\
                              (LENGTH (dataSem_state_stack s) =
                                LENGTH xs) ==>
                              (?lss sfs smx phl.
                              (evaluate (c,dataSem_state_stack_fupd
                                (K xs) s) =
                              (SOME (Rerr (Rraise
                                t)),dataSem_state_peak_heap_length_fupd
                                (K phl) (dataSem_state_stack_max_fupd (K
                                smx) (dataSem_state_safe_for_space_fupd
                                (K sfs) (dataSem_state_locals_size_fupd
                                (K lss) (dataSem_state_locals_fupd (K
                                (dataSem_state_locals s7))
                                (dataSem_state_handler_fupd (K
                                (dataSem_state_handler s7)) (stack_fupd
                                (K (stack s7))
                              s1))))))))))) | (res,s1) -> (stack s1
                                = dataSem_state_stack s) /\
                                (dataSem_state_handler s1 =
                                dataSem_state_handler s) /\
                           (!xs. (LENGTH (dataSem_state_stack s) =
                             LENGTH xs) ==>
                              (?lss sfs smx phl.
                              evaluate (c,dataSem_state_stack_fupd
                                (K xs) s) =
                              (res
                                ,dataSem_state_peak_heap_length_fupd
                                (K phl) (dataSem_state_stack_max_fupd
                                (K smx)
                                (dataSem_state_safe_for_space_fupd (K
                                sfs) (stack_fupd (K xs)
                                (dataSem_state_locals_size_fupd (K
                                lss) s1)))))))`)
  CHEAT_TAC;;

let evaluate_stack = cake_theorem "evaluate_stack"
  (fun () ->
    `!c (s:('c,'ffi)dataSem_state).
        match evaluate (c,s) with (SOME (Rerr (Rabort
          Rtype_error)),s1) -> T | (SOME (Rerr (Rabort _7)),s1) ->
          (stack s1 = []) | (SOME (Rerr _8),s1) ->
              (?s2. (dataSem_jump_exc s = SOME s2) /\
                (dataSem_state_locals s2 = dataSem_state_locals s1) /\
                    (stack s2 = stack s1) /\
                      (dataSem_state_handler s2 =
                      dataSem_state_handler s1)) | (_9,s1) -> (stack
                      s1 = dataSem_state_stack s) /\
                      (dataSem_state_handler s1 =
                      dataSem_state_handler s)`)
  CHEAT_TAC;;

let evaluate_NONE_jump_exc = cake_theorem "evaluate_NONE_jump_exc"
  (fun () ->
    `(evaluate (c,(s:('c,'ffi)dataSem_state)) = (NONE,u1)) /\
  (dataSem_jump_exc u1 = SOME x) ==>
       (dataSem_jump_exc s = SOME (dataSem_state_locals_size_fupd
         (K (dataSem_state_locals_size x)) (dataSem_state_locals_fupd
         (K (dataSem_state_locals x)) (dataSem_state_handler_fupd (K
         (dataSem_state_handler x)) (dataSem_state_stack_fupd (K
         (stack x)) s)))))`)
  CHEAT_TAC;;

let evaluate_NONE_jump_exc_ALT =
  cake_theorem "evaluate_NONE_jump_exc_ALT"
  (fun () ->
    `(evaluate (c,(s:('c,'ffi)dataSem_state)) = (NONE,u1)) /\
  (dataSem_jump_exc s = SOME x) ==>
      (dataSem_jump_exc u1 = SOME (dataSem_state_locals_size_fupd
        (K (dataSem_state_locals_size x)) (dataSem_state_locals_fupd
        (K (dataSem_state_locals x)) (dataSem_state_handler_fupd (K
        (dataSem_state_handler x)) (stack_fupd (K (stack x)) u1)))))`)
  CHEAT_TAC;;

let evaluate_locals_LN_lemma =
  cake_theorem "evaluate_locals_LN_lemma[local]"
  (fun () ->
    `!c (s:('c,'ffi)dataSem_state). ~(FST (evaluate (c,s)) = NONE) /\
  ~(FST (evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error))) ==>
         (dataSem_state_locals (SND (evaluate (c,s))) = LN) \/
         (?t. FST (evaluate (c,s)) = SOME (Rerr (Rraise t)))`)
  CHEAT_TAC;;

let evaluate_locals_LN = cake_theorem "evaluate_locals_LN"
  (fun () ->
    `!c (s:('c,'ffi)dataSem_state) res t.
        (evaluate (c,s) = (res,t)) /\ ~(res = NONE) /\ ~(res = SOME
          (Rerr (Rabort Rtype_error))) ==>
        (dataSem_state_locals t = LN) \/ (?t. res = SOME (Rerr
          (Rraise t)))`)
  CHEAT_TAC;;

let locals_ok_def = cake_define
  `locals_ok l1 l2 =
     (!v x. (sptree_lookup v l1 = SOME x) ==> (sptree_lookup v l2
       = SOME x))`;;

let locals_ok_IMP = cake_theorem "locals_ok_IMP"
  (fun () ->
    `locals_ok l1 l2 ==> domain l1 SUBSET domain l2`)
  CHEAT_TAC;;

let locals_ok_refl = cake_theorem "locals_ok_refl"
  (fun () ->
    `!l. locals_ok l l`)
  CHEAT_TAC;;

let locals_ok_cut_env = cake_theorem "locals_ok_cut_env"
  (fun () ->
    `locals_ok l1 l2 /\
      (dataSem_cut_env names l1 = SOME x) ==>
      (dataSem_cut_env names l2 = SOME x)`)
  CHEAT_TAC;;

let locals_ok_get_var = cake_theorem "locals_ok_get_var"
  (fun () ->
    `locals_ok s l /\
      (get_var x s = SOME w) ==>
      (get_var x l = SOME w)`)
  CHEAT_TAC;;

let locals_ok_get_vars = cake_theorem "locals_ok_get_vars"
  (fun () ->
    `!x w.
        locals_ok s l /\
        (dataSem_get_vars x s = SOME w) ==>
        (dataSem_get_vars x l = SOME w)`)
  CHEAT_TAC;;

let locals_ok_insert = cake_theorem "locals_ok_insert[local]"
  (fun () ->
    `locals_ok a b ==> locals_ok (insert k v a) (insert k v b)`)
  CHEAT_TAC;;

(* Under locals_ok, the narrow cut in evaluate(Assign) succeeds on the larger
   locals and yields a state equal up to (and locals_ok on) its locals. *)
let cut_state_opt_locals_ok =
  cake_theorem "cut_state_opt_locals_ok[local]"
  (fun () ->
    `locals_ok (dataSem_state_locals s) l /\ dataSem_cut_state_opt
  names_opt s = SOME s1 ==>
     (?l'. dataSem_cut_state_opt names_opt
       (dataSem_state_locals_fupd (K l) s) = SOME
       (dataSem_state_locals_fupd (K l') s1) /\
          locals_ok (dataSem_state_locals s1) l')`)
  CHEAT_TAC;;

let evaluate_locals = cake_theorem "evaluate_locals"
  (fun () ->
    `!c s res s2 vars' l. ~(res = SOME (Rerr (Rabort Rtype_error))) /\
  (evaluate (c,s) = (res,s2)) /\
         locals_ok (dataSem_state_locals s) l ==>
         (?w safe peak sm. (evaluate (c,dataSem_state_locals_fupd
           (K l) s) =
                (res,(if res = NONE then
                  (dataSem_state_peak_heap_length_fupd (K peak)
                  (dataSem_state_stack_max_fupd (K sm)
                  (dataSem_state_safe_for_space_fupd (K safe)
                  (dataSem_state_locals_fupd (K w) s2)))) else
                  dataSem_state_peak_heap_length_fupd (K peak)
                  (dataSem_state_stack_max_fupd (K sm)
                  (dataSem_state_safe_for_space_fupd (K safe) s2))))) /\
             locals_ok (dataSem_state_locals s2) w)`)
  CHEAT_TAC;;

let funpow_dec_clock_clock = cake_theorem "funpow_dec_clock_clock"
  (fun () ->
    `!n s. FUNPOW dataSem_dec_clock n s = (state_clock_fupd (K
  (state_clock s - n)) s)`)
  CHEAT_TAC;;

let evaluate_mk_ticks = cake_theorem "evaluate_mk_ticks"
  (fun () ->
    `!p s n.
      evaluate (mk_ticks n p,s) =
      (if state_clock s < n then
        (SOME (Rerr (Rabort
          Rtimeout_error)),dataSem_state_locals_size_fupd (K (SOME 0))
          (stack_fupd (K []) (dataSem_state_locals_fupd (K (fromList
          [])) (state_clock_fupd (K 0)
         s)))) else
        evaluate (p,FUNPOW dec_clock n s))`)
  CHEAT_TAC;;

let FUNPOW_dec_clock_code = cake_theorem "FUNPOW_dec_clock_code[simp]"
  (fun () ->
    `(state_code (FUNPOW dec_clock n t) = state_code t) /\
     (stack (FUNPOW dec_clock n t) = stack t) /\
     (dataSem_state_handler (FUNPOW dec_clock n t) =
       dataSem_state_handler t) /\
     (state_refs (FUNPOW dec_clock n t) = state_refs t) /\
     (state_ffi (FUNPOW dec_clock n t) = state_ffi t) /\
     (dataSem_state_safe_for_space (FUNPOW dec_clock n t) =
       dataSem_state_safe_for_space t) /\
     (dataSem_state_global (FUNPOW dec_clock n t) =
       dataSem_state_global t) /\
     (dataSem_state_locals (FUNPOW dec_clock n t) =
       dataSem_state_locals t) /\
     (compile (FUNPOW dec_clock n t) = compile t) /\
     (compile_oracle (FUNPOW dec_clock n t) = compile_oracle t) /\
     (dataSem_state_peak_heap_length (FUNPOW dec_clock n t) =
       dataSem_state_peak_heap_length t) /\
     (dataSem_state_stack_frame_sizes (FUNPOW dec_clock n t) =
       dataSem_state_stack_frame_sizes t) /\
     (dataSem_state_locals_size (FUNPOW dec_clock n t) =
       dataSem_state_locals_size t) /\
     (state_clock (FUNPOW dec_clock n t) = state_clock t - n)`)
  CHEAT_TAC;;

let jump_exc_NONE = cake_theorem "jump_exc_NONE"
  (fun () ->
    `(dataSem_jump_exc (dataSem_state_locals_fupd (K x) t) = NONE <=>
  dataSem_jump_exc t = NONE) /\
     (dataSem_jump_exc (state_clock_fupd (K c) t) = NONE <=>
       dataSem_jump_exc t = NONE) /\
     (dataSem_jump_exc (dataSem_state_stack_max_fupd (K sm) t) =
       NONE <=> dataSem_jump_exc t = NONE) /\
     (dataSem_jump_exc (dataSem_state_locals_size_fupd (K ls) t) =
       NONE <=> dataSem_jump_exc t = NONE) /\
     (dataSem_jump_exc (dataSem_state_safe_for_space_fupd (K
       safe) t) = NONE <=> dataSem_jump_exc t = NONE)`)
  CHEAT_TAC;;

let jump_exc_IMP = cake_theorem "jump_exc_IMP"
  (fun () ->
    `(dataSem_jump_exc s = SOME t) ==> dataSem_state_handler
      s < LENGTH (stack s) /\
      (?n e ls xs. (LASTN (dataSem_state_handler s + 1) (stack s) =
        dataSem_Exc ls e n :: xs) /\
                  (t = stack_fupd (K xs)
                    (dataSem_state_locals_fupd (K e)
                    (dataSem_state_locals_size_fupd (K ls)
                    (dataSem_state_handler_fupd (K n) s)))))`)
  CHEAT_TAC;;

let do_app_Rerr = cake_theorem "do_app_Rerr"
  (fun () ->
    `dataSem_do_app op vs s = Rerr e ==>
                              (e = Rabort Rtype_error) \/
                              (?i x. op = FFI i /\ e = Rabort
                                (Rffi_error x))`)
  CHEAT_TAC;;

let size_of_heap_with_clock = cake_theorem "size_of_heap_with_clock"
  (fun () ->
    `!s z. size_of_heap (state_clock_fupd (K z) s) = size_of_heap s`)
  CHEAT_TAC;;

let size_of_heap_args_with_clock =
  cake_theorem "size_of_heap_args_with_clock"
  (fun () ->
    `!s z a. size_of_heap_args a (state_clock_fupd (K z) s) =
  size_of_heap_args a s`)
  CHEAT_TAC;;

let space_consumed_with_clock = cake_theorem "space_consumed_with_clock"
  (fun () ->
    `!s op vs. space_consumed (state_clock_fupd (K z) s) op vs =
  space_consumed s op vs`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:1868: code that the source has in a
   comment *)
let do_app_with_clock = cake_theorem "do_app_with_clock"
  (fun () ->
    `do_app op vs (state_clock_fupd (K z) s) =
      map_result (\(x,y). (x,state_clock_fupd (K z) y)) I (do_app
        op vs s)`)
  CHEAT_TAC;;

let dataProps_do_app_change_clock = cake_theorem "do_app_change_clock"
  (fun () ->
    `(do_app op args s1 = Rval (res,s2)) ==>
      (do_app op args (state_clock_fupd (K ck) s1) = Rval
        (res,state_clock_fupd (K ck) s2))`)
  CHEAT_TAC;;

let dataProps_do_app_change_clock_err =
  cake_theorem "do_app_change_clock_err"
  (fun () ->
    `(do_app op args s1 = Rerr e) ==>
     (do_app op args (state_clock_fupd (K ck) s1) = Rerr e)`)
  CHEAT_TAC;;

let cut_state_eq_some = cake_theorem "cut_state_eq_some"
  (fun () ->
    `dataSem_cut_state names s = SOME y <=> (?z. dataSem_cut_env names
  (dataSem_state_locals s) = SOME z /\ y = dataSem_state_locals_fupd
  (K z) s)`)
  CHEAT_TAC;;

let set_var_const = cake_theorem "set_var_const[simp]"
  (fun () ->
    `state_ffi
        (dataSem_set_var x y z) = state_ffi z /\ state_clock
        (dataSem_set_var x y z) = state_clock z`)
  CHEAT_TAC;;

let set_var_with_const = cake_theorem "set_var_with_const"
  (fun () ->
    `(dataSem_set_var x y (state_clock_fupd (K k) z)) =
  state_clock_fupd (K k) (dataSem_set_var x y z)`)
  CHEAT_TAC;;

let set_vars_const = cake_theorem "set_vars_const[simp]"
  (fun () ->
    `state_ffi
        (dataSem_set_vars xs ys z) = state_ffi z /\ state_clock
        (dataSem_set_vars xs ys z) = state_clock z`)
  CHEAT_TAC;;

let set_vars_with_const = cake_theorem "set_vars_with_const[simp]"
  (fun () ->
    `(dataSem_set_vars xs ys (state_clock_fupd (K k) z)) =
  state_clock_fupd (K k) (dataSem_set_vars xs ys z)`)
  CHEAT_TAC;;

let call_env_const = cake_theorem "call_env_const[simp]"
  (fun () ->
    `state_ffi
        (dataSem_call_env x s y) = state_ffi y /\ state_clock
        (dataSem_call_env x s y) = state_clock y`)
  CHEAT_TAC;;

let call_env_with_const = cake_theorem "call_env_with_const"
  (fun () ->
    `(dataSem_call_env x s (state_clock_fupd (K z) y)) =
  state_clock_fupd (K z) (dataSem_call_env x s y)`)
  CHEAT_TAC;;

let push_env_const = cake_theorem "push_env_const[simp]"
  (fun () ->
    `state_ffi
        (dataSem_push_env x y z) = state_ffi z /\ state_clock
        (dataSem_push_env x y z) = state_clock z /\ state_code
        (dataSem_push_env x y z) = state_code z /\ compile_oracle
        (dataSem_push_env x y z) = compile_oracle z /\ compile
        (dataSem_push_env x y z) = compile z /\ state_refs
        (dataSem_push_env x y z) = state_refs z /\
          dataSem_state_global
        (dataSem_push_env x y z) = dataSem_state_global z`)
  CHEAT_TAC;;

let push_env_with_const = cake_theorem "push_env_with_const"
  (fun () ->
    `(dataSem_push_env x y (state_clock_fupd (K k) z)) =
  state_clock_fupd (K k) (dataSem_push_env x y z)`)
  CHEAT_TAC;;

let pop_env_with_const = cake_theorem "pop_env_with_const"
  (fun () ->
    `(dataSem_pop_env (state_clock_fupd (K k) z)) = OPTION_MAP (\z.
  state_clock_fupd (K k) z) (dataSem_pop_env z)`)
  CHEAT_TAC;;

let pop_env_const = cake_theorem "pop_env_const"
  (fun () ->
    `dataSem_pop_env a = SOME b ==> state_ffi
     b = state_ffi a /\ state_clock
     b = state_clock a /\ dataSem_state_stack_max
     b = dataSem_state_stack_max a`)
  CHEAT_TAC;;

let cut_state_eq_none = cake_theorem "cut_state_eq_none"
  (fun () ->
    `dataSem_cut_state names s = NONE <=> dataSem_cut_env names
  (dataSem_state_locals s) = NONE`)
  CHEAT_TAC;;

let dataProps_with_same_clock = cake_theorem "with_same_clock[simp]"
  (fun () ->
    `dataSem_state_clock_fupd (K (dataSem_state_clock s))
       (s:('c,'ffi)dataSem_state) = s`)
  CHEAT_TAC;;

let dataProps_evaluate_add_clock = cake_theorem "evaluate_add_clock"
  (fun () ->
    `!exps s1 res s2.
       evaluate (exps,s1) = (res,s2) /\ ~(res = SOME (Rerr (Rabort
         Rtimeout_error))) ==>
       (!ck. evaluate (exps,state_clock_fupd (K (state_clock s1 +
         ck)) s1) = (res,state_clock_fupd (K (state_clock s2 + ck))
         s2))`)
  CHEAT_TAC;;

let cut_state_opt_const = cake_theorem "cut_state_opt_const"
  (fun () ->
    `dataSem_cut_state_opt x y = SOME z ==> state_ffi
      z = state_ffi y /\ dataSem_state_global
      z = dataSem_state_global y`)
  CHEAT_TAC;;

let dataProps_do_app_io_events_mono =
  cake_theorem "do_app_io_events_mono"
  (fun () ->
    `do_app x y z = Rval (a,b) ==> ffi_state_io_events (state_ffi
     z) <<= ffi_state_io_events (state_ffi b)`)
  CHEAT_TAC;;

let dec_clock_const = cake_theorem "dec_clock_const[simp]"
  (fun () ->
    `state_ffi
        (dec_clock s) = state_ffi s /\ state_code
        (dec_clock s) = state_code s /\ compile_oracle
        (dec_clock s) = compile_oracle s /\ compile
        (dec_clock s) = compile s /\ state_refs
        (dec_clock s) = state_refs s /\ dataSem_state_global
        (dec_clock s) = dataSem_state_global s`)
  CHEAT_TAC;;

let add_space_const = cake_theorem "add_space_const[simp]"
  (fun () ->
    `state_ffi
        (add_space s k) = state_ffi s`)
  CHEAT_TAC;;

let dataProps_evaluate_io_events_mono =
  cake_theorem "evaluate_io_events_mono"
  (fun () ->
    `!exps s1 res s2.
      evaluate (exps,s1) = (res,s2) ==> ffi_state_io_events
        (state_ffi
      s1) <<= ffi_state_io_events (state_ffi s2)`)
  CHEAT_TAC;;

let dataProps_with_clock_ffi = cake_theorem "with_clock_ffi"
  (fun () ->
    `state_ffi
        (dataSem_state_clock_fupd (K y)
          (s:('c,'ffi)dataSem_state)) = dataSem_state_ffi s`)
  CHEAT_TAC;;

let jump_exc_with_const = cake_theorem "jump_exc_with_const"
  (fun () ->
    `dataSem_jump_exc (state_clock_fupd (K k) s) = OPTION_MAP (\s.
  state_clock_fupd (K k) s) (dataSem_jump_exc s)`)
  CHEAT_TAC;;

let dataProps_evaluate_add_clock_io_events_mono =
  cake_theorem "evaluate_add_clock_io_events_mono"
  (fun () ->
    `!exps s extra. ffi_state_io_events (state_ffi
      (SND (evaluate (exps,s)))) <<= ffi_state_io_events (state_ffi
      (SND (evaluate (exps,state_clock_fupd (K (state_clock s +
        extra)) s))))`)
  CHEAT_TAC;;

let semantics_Div_IMP_LPREFIX = cake_theorem "semantics_Div_IMP_LPREFIX"
  (fun () ->
    `semantics ffi prog co cc lim ss start = ffi_Diverge l ==> LPREFIX
  (fromList (ffi_state_io_events ffi)) l`)
  CHEAT_TAC;;

let semantics_Term_IMP_PREFIX = cake_theorem "semantics_Term_IMP_PREFIX"
  (fun () ->
    `semantics ffi prog co cc lim ss start = ffi_Terminate tt l ==>
  ffi_state_io_events ffi <<= l`)
  CHEAT_TAC;;

let resource_limit_hit_implements_semantics =
  cake_theorem "Resource_limit_hit_implements_semantics"
  (fun () ->
    `implements {ffi_Terminate ffi_Resource_limit_hit
  (ffi_state_io_events ffi)}
          {semantics ffi (fromAList prog) co cc lim ss start}`)
  CHEAT_TAC;;

let get_code_labels_def = cake_define
  `dataProps_get_code_labels x1 =
        match x1 with
          (Call r d a h:dataLang_prog) ->
       (match d with SOME x -> {x} | _10 -> {}) UNION
       (match h with SOME (n,p) -> dataProps_get_code_labels p | _11
         -> {})
        | (Force _12 loc _13) -> {loc}
        | (Seq p1 p2) -> dataProps_get_code_labels p1 UNION
          dataProps_get_code_labels p2
        | (If _14 p1 p2) -> dataProps_get_code_labels p1 UNION
          dataProps_get_code_labels p2
        | (Assign _15 op _16 _17) -> assign_get_code_label op
        | _18 -> {}`;;
hol4_overload "get_code_labels" "dataProps_get_code_labels";;

let good_code_labels_def = cake_define
  `dataProps_good_code_labels p elabs <=>
     (BIGUNION (set_of_list (MAP (\(n,m,pp).
       (dataProps_get_code_labels pp)) p))) SUBSET
     (set_of_list (MAP FST p)) UNION elabs`;;
hol4_overload "good_code_labels" "dataProps_good_code_labels";;

let get_code_labels_mk_ticks = cake_theorem "get_code_labels_mk_ticks"
  (fun () ->
    `!n m. dataProps_get_code_labels (mk_ticks n m) SUBSET
  dataProps_get_code_labels m`)
  CHEAT_TAC;;

let v_to_list_SOME_NIL_IFF = cake_theorem "v_to_list_SOME_NIL_IFF"
  (fun () ->
    `!v. v_to_list v = SOME [] <=> (?ts. v = Block ts nil_tag [])`)
  CHEAT_TAC;;

let v_to_list_SOME_CONS_IMP = cake_theorem "v_to_list_SOME_CONS_IMP"
  (fun () ->
    `!v x xs ts.
     v_to_list v = SOME (x :: xs) ==> (?ts' ys. v = Block ts'
       cons_tag [x; ys] /\ v_to_list ys = SOME xs)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:2259: code that the source has in a
   comment *)
let do_app_safe_for_space_mono =
  cake_theorem "do_app_safe_for_space_mono"
  (fun () ->
    `(do_app op xs s = Rval (r,s1)) /\ dataSem_state_safe_for_space s1
  ==> dataSem_state_safe_for_space s`)
  CHEAT_TAC;;

let evaluate_safe_for_space_mono =
  cake_theorem "evaluate_safe_for_space_mono"
  (fun () ->
    `!prog (s:('c,'ffi)dataSem_state) res s1.
       evaluate (prog,s) = (res,s1) /\
         dataSem_state_safe_for_space s1 ==>
         dataSem_state_safe_for_space s`)
  CHEAT_TAC;;

let zero_limits_def = cake_define
  `zero_limits = (mk_limits 0 0 0 ARB ARB ARB:limits)`;;


(* HOL4 dataPropsScript.sml:2311-2314: a proof *)

(* The limits-swap commutes through the narrow cut in evaluate(Assign). *)
let cut_state_opt_with_lim =
  cake_theorem "cut_state_opt_with_lim[local]"
  (fun () ->
    `dataSem_cut_state_opt names_opt (dataSem_state_limits_fupd (K lim)
  s) =
     OPTION_MAP (\t. dataSem_state_limits_fupd (K lim) t)
       (dataSem_cut_state_opt names_opt s)`)
  CHEAT_TAC;;

let evaluate_swap_limits = cake_theorem "evaluate_swap_limits"
  (fun () ->
    `!c s r s' limits.
      evaluate (c,s) = (r,s') ==>
      (?smx safe peak.
        evaluate (c,dataSem_state_limits_fupd (K limits) s) =
          (r,dataSem_state_peak_heap_length_fupd (K peak)
          (dataSem_state_safe_for_space_fupd (K safe)
          (dataSem_state_stack_max_fupd (K smx)
          (dataSem_state_limits_fupd (K limits) s')))))`)
  CHEAT_TAC;;

let evaluate_zero_limits_FST =
  cake_theorem "evaluate_zero_limits_FST[local]"
  (fun () ->
    `!c s r s'.
      FST (evaluate (c,s)) =
      FST (evaluate (c,dataSem_state_limits_fupd (K zero_limits)
        s))`)
  CHEAT_TAC;;

let evaluate_zero_limits_ffi =
  cake_theorem "evaluate_zero_limits_ffi[local]"
  (fun () ->
    `!c s r s'. state_ffi
      (SND (evaluate (c,s))) = state_ffi
      (SND (evaluate (c,dataSem_state_limits_fupd (K zero_limits)
        s)))`)
  CHEAT_TAC;;

(* Stack frames equal up-to size component*)
let stack_frame_size_rel_def = cake_define
  `stack_frame_size_rel x1 x2 =
        match (x1,x2) with
          (dataSem_Exc opt spt num',dataSem_Exc opt' spt' num') ->
       spt = spt' /\ num' = num'
        | ((Env opt spt),(Env opt' spt')) ->
       spt = spt'
        | (_19,_20) -> F`;;

let find_code_upto_size = cake_theorem "find_code_upto_size"
  (fun () ->
    `(find_code dest x code sizes = foo) ==>
      (?other_size.
      find_code dest x code other_sizes = OPTION_MAP
        (\(args,exp,size'). (args,exp,other_size)) foo)`)
  CHEAT_TAC;;


let do_app_stack_eq = cake_theorem "do_app_stack_eq"
  (fun () ->
    `!op vs s q s'. do_app op vs s = Rval (q,s') ==> stack
      s = stack s'`)
  CHEAT_TAC;;


let do_app_stack_frame_size_rel =
  cake_theorem "do_app_stack_frame_size_rel"
  (fun () ->
    `!op vs s q s' stk. do_app op vs s = Rval (q,s') /\
       LIST_REL stack_frame_size_rel (stack s) stk ==>
         LIST_REL stack_frame_size_rel (stack s') stk`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:2541-2545: a proof *)

(* The locals_size/stack/stack_frame_sizes-swap commutes through the narrow
   cut in evaluate(Assign), and the cut preserves the stack. *)
let cut_state_opt_with_sfs =
  cake_theorem "cut_state_opt_with_sfs[local]"
  (fun () ->
    `dataSem_cut_state_opt names_opt
  (dataSem_state_stack_frame_sizes_fupd (K sfs) (stack_fupd (K xs)
  (dataSem_state_locals_size_fupd (K lsz) s))) =
     OPTION_MAP (\t. dataSem_state_stack_frame_sizes_fupd (K sfs)
       (stack_fupd (K xs) (dataSem_state_locals_size_fupd (K lsz) t)))
                (dataSem_cut_state_opt names_opt s)`)
  CHEAT_TAC;;

let cut_state_opt_stack = cake_theorem "cut_state_opt_stack[local]"
  (fun () ->
    `dataSem_cut_state_opt names_opt s = SOME s1 ==> stack s1 = stack
  s`)
  CHEAT_TAC;;

let evaluate_swap_stack_frame_sizes_aux =
  cake_theorem "evaluate_swap_stack_frame_sizes_aux[local]"
  (fun () ->
    `!c s r s' xs lsz sfs.
      evaluate (c,s) = (r,s') /\ LIST_REL stack_frame_size_rel
        (stack s) xs ==>
      (let s0 = dataSem_state_stack_frame_sizes_fupd (K sfs)
        (stack_fupd (K xs) (dataSem_state_locals_size_fupd (K lsz) s))
        in
      ?xs lsz smx safe peak sfs'.
        (evaluate (c,s0) = (r,dataSem_state_peak_heap_length_fupd
          (K peak) (dataSem_state_stack_max_fupd (K smx)
          (dataSem_state_stack_frame_sizes_fupd (K sfs') (stack_fupd (K
          xs) (dataSem_state_safe_for_space_fupd (K safe)
          (dataSem_state_locals_size_fupd (K lsz) s')))))) /\
         LIST_REL stack_frame_size_rel (stack s') xs))`)
  CHEAT_TAC;;

let evaluate_swap_local_sizes = cake_theorem "evaluate_swap_local_sizes"
  (fun () ->
    `!c s r s' lss.
      evaluate (c,s) = (r,s') ==>
      (?xs lsz sfs smx safe peak.
        (evaluate (c,dataSem_state_locals_size_fupd (K lss) s) =
           (r,dataSem_state_peak_heap_length_fupd (K peak)
             (dataSem_state_stack_max_fupd (K smx)
             (dataSem_state_stack_frame_sizes_fupd (K sfs) (stack_fupd
             (K xs) (dataSem_state_safe_for_space_fupd (K safe)
             (dataSem_state_locals_size_fupd (K lsz) s')))))) /\
         LIST_REL stack_frame_size_rel (stack s') xs))`)
  CHEAT_TAC;;

let evaluate_swap_stack_frame_sizes =
  cake_theorem "evaluate_swap_stack_frame_sizes"
  (fun () ->
    `!c s r s' sfs.
      evaluate (c,s) = (r,s') ==>
      (?xs lsz smx safe peak sfs'.
        (evaluate (c,dataSem_state_stack_frame_sizes_fupd (K sfs)
          s) = (r,dataSem_state_peak_heap_length_fupd (K peak)
          (dataSem_state_stack_max_fupd (K smx)
          (dataSem_state_stack_frame_sizes_fupd (K sfs') (stack_fupd (K
          xs) (dataSem_state_safe_for_space_fupd (K safe)
          (dataSem_state_locals_size_fupd (K lsz) s')))))) /\
         LIST_REL stack_frame_size_rel (stack s') xs))`)
  CHEAT_TAC;;

let evaluate_stack_frame_sizes_FST =
  cake_theorem "evaluate_stack_frame_sizes_FST[local]"
  (fun () ->
    `!c s r s'.
      FST (evaluate (c,s)) =
      FST (evaluate (c,dataSem_state_stack_frame_sizes_fupd (K
        LN) s))`)
  CHEAT_TAC;;

let evaluate_stack_frame_sizes_ffi =
  cake_theorem "evaluate_stack_frame_sizes_ffi[local]"
  (fun () ->
    `!c s r s'. state_ffi
      (SND (evaluate (c,s))) = state_ffi
      (SND (evaluate (c,dataSem_state_stack_frame_sizes_fupd (K
        LN) s)))`)
  CHEAT_TAC;;

let semantics_zero_limits = cake_theorem "semantics_zero_limits"
  (fun () ->
    `dataSem_semantics ffi code co cc lim ss start =
     dataSem_semantics ffi code co cc zero_limits LN start`)
  CHEAT_TAC;;

let do_app_stack_max = cake_theorem "do_app_stack_max"
  (fun () ->
    `do_app op xs s1 = Rval (v,s2) ==>
     option_le (dataSem_state_stack_max s1)
       (dataSem_state_stack_max s2)`)
  CHEAT_TAC;;

let evaluate_option_le_stack_max =
  cake_theorem "evaluate_option_le_stack_max"
  (fun () ->
    `!c2 s res s1.
     dataSem_evaluate (c2,s) = (res,s1) ==> option_le
       (dataSem_state_stack_max s) (dataSem_state_stack_max s1)`)
  CHEAT_TAC;;

let cc_co_only_diff_def = cake_define
  `cc_co_only_diff (s:('a,'ffi)dataSem_state) (t:('b,'ffi)dataSem_state)
  <=> dataSem_state_locals
     s = dataSem_state_locals t /\ dataSem_state_locals_size
     s = dataSem_state_locals_size t /\ dataSem_state_stack
     s = dataSem_state_stack t /\ dataSem_state_stack_max
     s = dataSem_state_stack_max t /\ dataSem_state_stack_frame_sizes
     s = dataSem_state_stack_frame_sizes t /\ dataSem_state_global
     s = dataSem_state_global t /\ dataSem_state_handler
     s = dataSem_state_handler t /\ dataSem_state_refs
     s = dataSem_state_refs t /\ dataSem_state_clock
     s = dataSem_state_clock t /\ dataSem_state_code
     s = dataSem_state_code t /\ dataSem_state_ffi
     s = dataSem_state_ffi t /\ dataSem_state_space
     s = dataSem_state_space t /\ dataSem_state_tstamps
     s = dataSem_state_tstamps t /\ dataSem_state_limits
     s = dataSem_state_limits t /\ dataSem_state_safe_for_space
     s = dataSem_state_safe_for_space t /\
       dataSem_state_peak_heap_length
     s = dataSem_state_peak_heap_length t`;;

(* HOL4 dataPropsScript.sml:2992: code that the source has in a
   comment *)
let do_app_cc_co_only_diff_rval =
  cake_theorem "do_app_cc_co_only_diff_rval"
  (fun () ->
    `dataSem_do_app op vs s = Rval (v,s1) /\
  dataSem_state_safe_for_space s1 /\ cc_co_only_diff s t ==>
     (?t1. dataSem_do_app op vs t = Rval (v,t1) /\
       cc_co_only_diff s1 t1)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:3027: code that the source has in a
   comment *)
let do_app_cc_co_only_diff_rerr =
  cake_theorem "do_app_cc_co_only_diff_rerr"
  (fun () ->
    `dataSem_do_app op vs s = Rerr r /\ ~(op = Install) /\
  cc_co_only_diff s t ==>
     dataSem_do_app op vs t = Rerr r`)
  CHEAT_TAC;;

let pop_env_safe_for_space = cake_theorem "pop_env_safe_for_space"
  (fun () ->
    `dataSem_pop_env s2 = SOME s1 ==> dataSem_state_safe_for_space s1
  = dataSem_state_safe_for_space s2`)
  CHEAT_TAC;;

let pop_env_cc_co_only_diff = cake_theorem "pop_env_cc_co_only_diff"
  (fun () ->
    `cc_co_only_diff s2 t2 /\ dataSem_pop_env s2 = SOME s1 ==>
     (?t1. dataSem_pop_env t2 = SOME t1 /\ cc_co_only_diff s1 t1)`)
  CHEAT_TAC;;

let cc_co_only_diff_call_env = cake_theorem "cc_co_only_diff_call_env"
  (fun () ->
    `cc_co_only_diff s t ==>
     cc_co_only_diff (dataSem_call_env args1 ss (dataSem_push_env
       x'' b (dec_clock s)))
                     (dataSem_call_env args1 ss (dataSem_push_env
                       x'' b (dec_clock t)))`)
  CHEAT_TAC;;

(* The narrow cut in evaluate(Assign) only depends on locals (equal under
   cc_co_only_diff), so the t-side cut is determined by the s-side cut and
   preserves cc_co_only_diff. *)
let cut_state_opt_cc_co_full =
  cake_theorem "cut_state_opt_cc_co_full[local]"
  (fun () ->
    `dataSem_state_locals
       (t) = dataSem_state_locals (s) ==>
       dataSem_cut_state_opt names_opt t =
       OPTION_MAP (\u. dataSem_state_locals_fupd (K
         (dataSem_state_locals u)) t) (dataSem_cut_state_opt names_opt
         s)`)
  CHEAT_TAC;;

let cut_cc_co = cake_theorem "cut_cc_co[local]"
  (fun () ->
    `cc_co_only_diff (s) (t) /\
     dataSem_cut_state_opt names_opt s = SOME s1 ==>
     (?t1. dataSem_cut_state_opt names_opt t = SOME t1 /\
       cc_co_only_diff s1 t1)`)
  CHEAT_TAC;;

let evaluate_cc_co_only_diff = cake_theorem "evaluate_cc_co_only_diff"
  (fun () ->
    `!prog (s) res s1 (t).
       evaluate (prog,s) = (res,s1) /\ dataSem_state_safe_for_space
       s1 /\
       cc_co_only_diff s t ==> (?t1. evaluate (prog,t) = (res,t1)
         /\ cc_co_only_diff s1 t1)`)
  CHEAT_TAC;;

let evaluate_stack_limit = cake_theorem "evaluate_stack_limit"
  (fun () ->
    `!c2 s res s1.
     dataSem_evaluate (c2,s) = (res,s1) ==> limits_stack_limit
       (dataSem_state_limits s1) = limits_stack_limit
       (dataSem_state_limits s)`)
  CHEAT_TAC;;

(* TODO: move *)
let the_le_IMP_option_le = cake_theorem "the_le_IMP_option_le"
  (fun () ->
    `the F (OPTION_MAP ((>) n) m) ==>
     option_le m (SOME n)`)
  CHEAT_TAC;;

(* HOL4 dataPropsScript.sml:3303: code that the source has in a
   comment *)
let do_app_stack_max_le_stack_limit =
  cake_theorem "do_app_stack_max_le_stack_limit"
  (fun () ->
    `do_app op xs s = Rval (res,s1) /\ dataSem_state_safe_for_space s1
  /\
     option_le (dataSem_state_stack_max s) (SOME
       (limits_stack_limit (dataSem_state_limits s))) ==>
     option_le (dataSem_state_stack_max s1) (SOME
       (limits_stack_limit (dataSem_state_limits s1)))`)
  CHEAT_TAC;;

let evaluate_stack_max_le_stack_limit =
  cake_theorem "evaluate_stack_max_le_stack_limit"
  (fun () ->
    `!prog s res s1.
       dataSem_evaluate (prog,s) = (res,s1) /\
         dataSem_state_safe_for_space s1 /\
       option_le (dataSem_state_stack_max s) (SOME
         (limits_stack_limit (dataSem_state_limits s))) ==>
       option_le (dataSem_state_stack_max s1) (SOME
         (limits_stack_limit (dataSem_state_limits s1)))`)
  CHEAT_TAC;;

cake_hide [];;
