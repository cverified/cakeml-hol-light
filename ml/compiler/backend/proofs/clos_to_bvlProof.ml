(* ======================================================== *)
(*  clos_to_bvlProof: ported from HOL4's
    compiler/backend/proofs/clos_to_bvlProofScript.sml
    A proof theory about clos_to_bvl.ml, with 31 definitions and 304
    theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_to_bvl
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/proofs/bvl_jumpProof.ml";;
needs "compiler/backend/proofs/clos_annotateProof.ml";;
needs "compiler/backend/proofs/clos_callProof.ml";;
needs "compiler/backend/proofs/clos_constantProof.ml";;
needs "compiler/backend/proofs/clos_fvsProof.ml";;
needs "compiler/backend/proofs/clos_knownProof.ml";;
needs "compiler/backend/proofs/clos_mtiProof.ml";;
needs "compiler/backend/proofs/clos_numberProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_to_bvlProof"
  ["backendProps"; "bvlProps"; "bvlSem"; "closProps"; "closSem";
   "clos_to_bvl"; "ffi"];;

let _ = do_list hide_constant ["C"; "all"; "build_const'";
       "globals_approx_every_Fn_SOME";
       "globals_approx_every_Fn_vs_NONE"; "known_co"; "parts";
       "syntax_ok"; "update_tag"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["next_loc","next_loc"];;

hol4_overload "evaluate" "bvlSem_evaluate";;
(* HOL4 clos_to_bvlProofScript.sml:22-24: an overload that the source
   brings to the front: num_stubs *)
hol4_overload "compile_exps" "clos_to_bvl_compile_exps";;

(* TODO: move? *)

(* HOL4 clos_to_bvlProofScript.sml:28: ML code, not ported *)

(* [local] *)
let EVERY_ZIP_GENLIST = prove
 (`!xs.
       (!i. i < LENGTH xs ==> P (EL i xs,f i)) ==>
       ALL P (ZIP xs (list_of_seq f (LENGTH xs)))`,
  CHEAT_TAC);;

(* [local] *)
let IS_SUBLIST_MEM = prove
 (`!ls ls' x.
   MEM x ls /\ IS_SUBLIST ls' ls ==>
   MEM x ls'`,
  CHEAT_TAC);;

(* [local] *)
let IS_SUBLIST_APPEND1 = prove
 (`!A B C'.
   IS_SUBLIST A C' ==>
   IS_SUBLIST (APPEND A B) C'`,
  CHEAT_TAC);;

(* [local] *)
let IS_SUBLIST_APPEND2 = prove
 (`!A B C'.
   IS_SUBLIST B C' ==>
   IS_SUBLIST (APPEND A B) C'`,
  CHEAT_TAC);;

(* [local] *)
let IS_SUBLIST_REFL = prove
 (`!ls.
   IS_SUBLIST ls ls`,
  CHEAT_TAC);;

(* [local] *)
let map2_snoc = prove
 (`!l1 l2 f x y.
     LENGTH l1 = LENGTH l2 ==>
     MAP2 f (SNOC x l1) (SNOC y l2) = APPEND (MAP2 f l1 l2) [f x y]`,
  CHEAT_TAC);;

(* [local] *)
let el_map2 = prove
 (`!x f l1 l2.
     LENGTH l1 = LENGTH l2 /\ x < LENGTH l1 ==>
     EL x (MAP2 f l1 l2) = f (EL x l1) (EL x l2)`,
  CHEAT_TAC);;

(* [local] *)
let length_take2 = prove
 (`!x l. ~(x <= LENGTH l) ==> LENGTH (TAKE x l) = LENGTH l`,
  CHEAT_TAC);;

(* [local] *)
let el_take_append = prove
 (`!n l x l2. n <= LENGTH l ==> EL n (APPEND (APPEND (TAKE n l) [x])
  l2) = x`,
  CHEAT_TAC);;

(* [local] *)
let el_append2 = prove
 (`!l x. EL (LENGTH l) (APPEND l [x]) = x`,
  CHEAT_TAC);;

(* [local] *)
let el_append2_lemma = prove
 (`!n args.
     n + 1 = LENGTH args ==>
     EL (SUC n) (APPEND args [x]) = x`,
  CHEAT_TAC);;

(* [local] *)
let hd_append = prove
 (`!l1 l2. 0 < LENGTH l1 ==> HD (APPEND l1 l2) = HD l1`,
  CHEAT_TAC);;

(* [local] *)
let tl_append = prove
 (`!l1 l2. 0 < LENGTH l1 ==> TL (APPEND l1 l2) = APPEND (TL l1) l2`,
  CHEAT_TAC);;

(* [local] *)
let twod_table_lemma = prove
 (`!x y z.
     z <= y ==>
     list_of_seq (\t. f ((t + x * y) DIV y) ((t + x * y) MOD y)) z =
     list_of_seq (\t. f x t) z`,
  CHEAT_TAC);;

(* [local] *)
let twod_table = prove
 (`!f x y.
     0 < y ==>
     FLAT (list_of_seq (\m. list_of_seq (\n. f m n) y) x) =
     list_of_seq (\n. f (n DIV y) (n MOD y)) (x * y)`,
  CHEAT_TAC);;

(* [local] *)
let less_rectangle = prove
 (`!(x:num) y m n. m < x /\ n < y ==> x * n + m < x * y`,
  CHEAT_TAC);;

(* [local] *)
let less_rectangle2 = prove
 (`!(x:num) y m n. m < x /\ n < y ==> m + n * x < x * y`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:197: ML code, not ported *)

(* [local] *)
let sum_genlist_triangle_help = prove
 (`!x. SUM (list_of_seq (\y. y) (x + 1)) = (x * (x + 1)) DIV 2`,
  CHEAT_TAC);;

(* [local] *)
let sum_genlist_triangle = prove
 (`!x. SUM (list_of_seq (\y. y) x) = (x * (x - 1)) DIV 2`,
  CHEAT_TAC);;

(* [local] *)
let triangle_table_size = prove
 (`!max' f. LENGTH (FLAT (list_of_seq (\x. (list_of_seq (\y. f x y) x))
  max')) = (
     max' * (max' - 1)) DIV 2`,
  CHEAT_TAC);;

(* [local] *)
let tri_lemma = prove
 (`!tot max_app.
     tot < max_app ==>
     tot + (tot * (tot - 1)) DIV 2 < max_app + ((max_app - 1) *
       (max_app - 2)) DIV 2`,
  CHEAT_TAC);;

(* [local] *)
let triangle_div_lemma = prove
 (`!max_app n tot.
     tot < max_app /\ n < tot ==>
     n + (tot * (tot - 1)) DIV 2 < (max_app * (max_app - 1)) DIV 2`,
  CHEAT_TAC);;

(* [local] *)
let triangle_el = prove
 (`!n tot max_app stuff f g.
     n < tot /\ tot < max_app ==>
     EL (n + (tot * (tot - 1)) DIV 2)
       (APPEND (FLAT
          (list_of_seq
             (\tot.
                list_of_seq
                  (\prev. f tot prev) tot)
             max_app))
        stuff) =
     f tot n`,
  CHEAT_TAC);;

(* [local] *)
let triangle_el_no_suff = prove
 (`!n tot max_app f g.
     n < tot /\ tot < max_app ==>
     EL (n + (tot * (tot - 1)) DIV 2)
       (FLAT
          (list_of_seq
             (\tot.
                list_of_seq
                  (\prev. f tot prev) tot)
             max_app)) =
     f tot n`,
  CHEAT_TAC);;

(* [local] *)
let if_expand = prove
 (`!w x y z. (if x then y else z) = w <=> x /\ y = w \/ ~x /\ z = w`,
  CHEAT_TAC);;

(* [local] *)
let take_drop_lemma = prove
 (`!rem_args arg_list.
    LENGTH arg_list > rem_args ==>
    TAKE (rem_args + 1) (DROP (LENGTH arg_list - (rem_args + 1))
      (APPEND arg_list stuff)) =
    DROP (LENGTH arg_list - (rem_args + 1)) arg_list`,
  CHEAT_TAC);;

(* [local] *)
let ETA2_THM = prove
 (`(\x y. f a b c x y) = f a b c`,
  CHEAT_TAC);;

(* [local] *)
let p_genlist = prove
 (`EL k exps_ps = ((n',e),p) /\
    MAP SND exps_ps = list_of_seq (\n. loc + (num_stubs max_app) + 2
      * n) (LENGTH exps_ps) /\
    k < LENGTH exps_ps ==>
    p = EL k (list_of_seq (\n. loc + (num_stubs max_app) + 2 * n)
      (LENGTH exps_ps))`,
  CHEAT_TAC);;

let list_CASE_same = prove
 (`list_CASE ls (P []) (\x y. P (CONS x y)) = P ls`,
  CHEAT_TAC);;

(* -- *)

(* correctness of partial/over application *)

(* [local] *)
let evaluate_genlist_prev_args = prove
 (`!prev_args z x tag arg_list st.
     evaluate (REVERSE (list_of_seq (\prev_arg.
       (\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b]) (Var
         (LENGTH x)) (prev_arg + LENGTH z)) (LENGTH prev_args)),APPEND x
         (CONS (Block tag (APPEND z prev_args)) arg_list),
            st) =
     (Rval (REVERSE prev_args),st)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_genlist_prev_args1_simpl = prove
 (`!prev_args x y tag p n cl a st.
     evaluate (REVERSE (list_of_seq (\prev_arg.
       (\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b]) (Var
         3) (prev_arg + 3)) (LENGTH prev_args)),
            [x; y; a; (Block tag (CONS p (CONS n (CONS cl
              prev_args))):bvlSem_v)],
            st) =
     (Rval (REVERSE prev_args),st)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_genlist_prev_args_no_rev = prove
 (`!prev_args z x tag arg_list st.
     evaluate (list_of_seq (\prev_arg.
       (\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b]) (Var
         (LENGTH x)) (prev_arg + LENGTH z)) (LENGTH prev_args),APPEND x
         (CONS (Block tag (APPEND z prev_args)) arg_list),
            st) =
     (Rval prev_args,st)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_genlist_prev_args1_no_rev = prove
 (`!prev_args x tag p n cl args st.
     evaluate (list_of_seq (\prev_arg.
       (\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b]) (Var
         (LENGTH args + 1)) (prev_arg + 3)) (LENGTH prev_args),CONS x
         (APPEND args [Block tag (CONS p (CONS n (CONS cl
         prev_args)))]),
            st) =
     (Rval prev_args,st)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_partial_app_fn_location_code = prove
 (`!max_app n total_args st args tag ptr x fvs.
      partial_app_fn_location max_app total_args n IN domain
        (state_code st) /\
      n < total_args /\ total_args < max_app ==>
      evaluate
        ([partial_app_fn_location_code max_app
                ((\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i))
                  [b]) (Var (LENGTH args + 1)) 1)
                (Op (closLang_IntOp (closLang_Const (&n))) [])],
         (CONS x (APPEND args [Block tag (CONS ptr (CONS (Number
           (&total_args)) fvs))])),
         st) =
      (Rval [Number (&((total_args * (total_args - 1)) DIV 2 +
        n))],st)`,
  CHEAT_TAC);;

let global_table_def = new_definition
  `global_table max_app =
     Block tuple_tag
       (FLAT (list_of_seq (\tot. list_of_seq
         (\prev. bvlSem_CodePtr (partial_app_fn_location max_app
           tot prev)) tot) max_app))`;;

(* [local] *)
let evaluate_generic_app1 = prove
 (`!n args st total_args l fvs cl.
     partial_app_fn_location max_app total_args n IN domain
       (state_code st) /\
     n < total_args /\
     total_args < max_app /\
     n + 1 = LENGTH args /\
     get_global 0 (state_globals st) = SOME (SOME (global_table
       max_app)) /\
     cl = Block closure_tag (CONS (bvlSem_CodePtr l) (CONS (Number
       (&total_args)) fvs)) ==>
     evaluate ([generate_generic_app max_app n],APPEND args [cl],st)
       =
       (if state_clock st < n then
         (Rerr (Rabort Rtimeout_error),state_clock_fupd (K 0) st)
           else
         (Rval [Block partial_app_tag (CONS (bvlSem_CodePtr
           (partial_app_fn_location max_app total_args n)) (CONS (Number
           (&(total_args - (n + 1)))) (CONS cl
                              args)))],
          dec_clock n st))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_generic_app2 = prove
 (`!n args st rem_args prev_args l clo cl.
     partial_app_fn_location max_app (rem_args + LENGTH prev_args) (n
       + LENGTH prev_args) IN domain (state_code st) /\
     n < rem_args /\
     n + 1 = LENGTH args /\
     LENGTH prev_args > 0 /\
     rem_args + LENGTH prev_args < max_app /\
     get_global 0 (state_globals st) = SOME (SOME (global_table
       max_app)) /\
     cl = Block partial_app_tag (CONS (bvlSem_CodePtr l) (CONS
       (Number (&rem_args)) (CONS clo prev_args))) ==>
     evaluate ([generate_generic_app max_app n],APPEND args [cl],st)
       =
       (if state_clock st < n then
         (Rerr (Rabort Rtimeout_error),state_clock_fupd (K 0) st)
           else
         (Rval [Block partial_app_tag (APPEND (CONS (bvlSem_CodePtr
           (partial_app_fn_location max_app (rem_args + LENGTH
           prev_args) (n + LENGTH prev_args))) (CONS (Number (&rem_args
           - &(n + 1))) (CONS clo
                              args)))
                              prev_args)],
          dec_clock n st))`,
  CHEAT_TAC);;

let unpack_closure = cake_inductive
  `(
    total_args >= (&0) ==>
    unpack_closure (Block closure_tag (CONS (bvlSem_CodePtr l) (CONS
      (Number total_args) fvs)))
          ([],num_of_int total_args,Block closure_tag (CONS
            (bvlSem_CodePtr l) (CONS (Number total_args) fvs)))) /\
   (
    ~(prev_args = []) /\
    rem_args >= (&0) ==>
    unpack_closure (Block partial_app_tag (CONS (bvlSem_CodePtr l)
      (CONS (Number rem_args) (CONS clo prev_args))))
          (prev_args,num_of_int rem_args + LENGTH prev_args,clo))`;;

(* [local] *)
let evaluate_generic_app_partial = prove
 (`!total_args prev_args st args cl sub_cl.
     partial_app_fn_location
       max_app
       total_args
       (LENGTH prev_args + (LENGTH args - 1)) IN domain (state_code
         st) /\
     total_args < max_app /\
     LENGTH args < (total_args + 1) - LENGTH prev_args /\ ~(LENGTH
       args = 0) /\
     get_global 0 (state_globals st) = SOME (SOME (global_table
       max_app)) /\
     unpack_closure cl (prev_args,total_args,sub_cl) ==>
     evaluate ([generate_generic_app max_app (LENGTH args -
       1)],APPEND args [cl],st) =
     (if state_clock st < LENGTH args - 1 then
       (Rerr (Rabort Rtimeout_error),state_clock_fupd (K 0) st) else
       (Rval [Block partial_app_tag
                    (APPEND (CONS (bvlSem_CodePtr
                      (partial_app_fn_location
                              max_app total_args
                              (LENGTH prev_args + (LENGTH args -
                                1)))) (CONS (Number (&(total_args -
                              (LENGTH prev_args + LENGTH args))))
                                (CONS sub_cl args))) prev_args)],
          dec_clock (LENGTH args - 1) st))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_generic_app_full = prove
 (`!n args st rem_args vs l tag exp clo.
     sptree_lookup l (state_code st) = SOME (rem_args + 2,exp) /\
     n + 1 = LENGTH args /\
     n > rem_args /\
     rem_args < max_app ==>
     evaluate ([generate_generic_app max_app n],APPEND args [Block
       tag (CONS (bvlSem_CodePtr l) (CONS (Number (&rem_args)) vs))],st)
       =
     (if state_clock st < rem_args + 1 then (Rerr (Rabort
       Rtimeout_error),state_clock_fupd (K 0) st) else
       match evaluate ([exp],APPEND (DROP (LENGTH args - (rem_args +
         1)) args)
                      [Block tag (CONS (bvlSem_CodePtr l) (CONS
                        (Number (&rem_args)) vs))],
                      dec_clock (rem_args + 1) st) with (Rval
                        [v],st') ->
             (match
                evaluate
                  ([mk_cl_call (Var 0) (list_of_seq (\n. Var (n + 3))
                    (n - rem_args))],APPEND (CONS v (CONS (Number
                    (&rem_args)) (CONS (Number (&rem_args - &(LENGTH
                    args)))
                       args))) [Block tag (CONS (bvlSem_CodePtr l)
                         (CONS (Number (&rem_args)) vs))],
                   st') with
                (Rval v,s2) -> (Rval [HD v],s2) | x -> x) | x -> x)`,
  CHEAT_TAC);;

(* [local] *)
let mk_cl_lem = prove
 (`l < LENGTH env ==>
    evaluate (list_of_seq (\n. Var (n + 3)) l,CONS a (CONS b (CONS c
      env)),st) =
    evaluate (list_of_seq (\n. Var (n + 1)) l,CONS a env,st)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_mk_cl_simpl = prove
 (`evaluate ([mk_cl_call (Var 0) (list_of_seq (\n. Var (n + 3)) (LENGTH
  args' - (n + 1)))],CONS v (CONS a (CONS b (APPEND args' [Block tag
  (CONS (bvlSem_CodePtr p) (CONS (Number (&n)) xs))]))),
                              st') =
    evaluate ([mk_cl_call (Var 0) (list_of_seq (\n. Var (n + 1))
      (LENGTH args' - (n + 1)))],CONS v (APPEND args' [Block tag (CONS
      (bvlSem_CodePtr p) (CONS (Number (&n)) xs))]),
                              st')`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_mk_cl_call = prove
 (`!cl env s tag p n args args' exp exp2 xs.
     evaluate ([cl],env,s) = (Rval [Block tag (CONS (bvlSem_CodePtr
       p) (CONS (Number (&n)) xs))],s) /\
     evaluate (args,env,s) = (Rval args',s) /\
     sptree_lookup p (state_code s) = SOME (n + 2,exp) /\
     sptree_lookup (generic_app_fn_location (LENGTH args' - 1))
       (state_code s) =
       SOME (LENGTH args' + 1,generate_generic_app max_app (LENGTH
         args' - 1)) /\
     LENGTH args' - 1 >= n /\
     n < max_app /\ ~(LENGTH args = 0) ==>
     evaluate ([mk_cl_call cl args],env,s) =
      (if n = LENGTH args - 1 then
        if state_clock s < LENGTH args then (Rerr (Rabort
          Rtimeout_error),state_clock_fupd (K 0) s) else evaluate
          ([exp],APPEND args' [Block tag (CONS (bvlSem_CodePtr p) (CONS
          (Number (&(LENGTH args - 1))) xs))],
                    dec_clock (LENGTH args) s) else
          if state_clock s < n + 2 then (Rerr (Rabort
            Rtimeout_error),state_clock_fupd (K 0) s) else
          match evaluate ([exp],APPEND (DROP (LENGTH args' - (n + 1))
            args') [Block tag (CONS (bvlSem_CodePtr p) (CONS (Number
            (&n)) xs))],
                      dec_clock (n + 2) s) with (Rval [v],st') ->
                 (match evaluate ([mk_cl_call (Var 0) (list_of_seq
                   (\n. Var (n + 1)) (LENGTH args' - (n + 1)))],CONS v
                   (APPEND args' [Block tag (CONS (bvlSem_CodePtr p)
                   (CONS (Number (&n)) xs))]),
                              st') with (Rval v,s2) -> (Rval [HD
                                v],s2) | x -> x) | x -> x)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_partial_app_fn = prove
 (`!num_args args' num_args' prev_args tag num' tag' l l' fvs exp code.
     sptree_lookup l code = SOME (LENGTH args' + LENGTH prev_args +
       1,exp) /\ ~(LENGTH prev_args = 0) /\
     LENGTH prev_args < num_args /\
     num_args = LENGTH prev_args + LENGTH args' ==>
     (!st. evaluate ([generate_partial_app_closure_fn (num_args - 1)
       (LENGTH prev_args - 1)],APPEND (DROP ((LENGTH args' + LENGTH
       prev_args) - num_args) args')
            [Block tag (CONS l' (CONS num' (CONS (Block tag' (CONS
              (bvlSem_CodePtr l) (CONS num_args' fvs))) prev_args)))],
            (state_code_fupd (K code) st)) =
      (if state_clock st = 0 then
        (Rerr (Rabort Rtimeout_error),(state_code_fupd (K code) st))
          else
        evaluate ([exp],APPEND (APPEND (DROP ((LENGTH args' + LENGTH
          prev_args) - num_args) args') prev_args) [Block tag' (CONS
          (bvlSem_CodePtr l) (CONS num_args' fvs))],
               dec_clock 1 (state_code_fupd (K code) st))))`,
  CHEAT_TAC);;

(* -- *)

(* value relation *)

let code_installed_def = new_definition
  `clos_to_bvlProof_code_installed aux code =
     ALL (\(n,num_args,exp). sptree_lookup n code = SOME
       (num_args,exp)) aux`;;
hol4_overload "code_installed" "clos_to_bvlProof_code_installed";;

let closure_code_installed_def = new_definition
  `closure_code_installed max_app code exps_ps (env:closSem_v list) =
     ALL (\((n,exp),p).
       n <= max_app /\ ~(n = 0) /\
       (?aux c aux1.
         (clos_to_bvl_compile_exps max_app [exp] aux = ([c],aux1)) /\
         (sptree_lookup p code = SOME (n + 1,SND (code_for_recc_case
           (LENGTH env + LENGTH exps_ps) n c))) /\
         clos_to_bvlProof_code_installed aux1 code)) exps_ps`;;

let cl_rel = cake_inductive
  `(
    num_args <= max_app /\ ~(num_args = 0) /\
     every_Fn_SOME [x] /\
     every_Fn_vs_SOME [x] /\
     (clos_to_bvl_compile_exps max_app [x] aux = ([c],aux1)) /\
     clos_to_bvlProof_code_installed aux1 code /\
     (sptree_lookup (p + (num_stubs max_app)) code =
       SOME (num_args + (1:num),Let (APPEND (list_of_seq Var
         num_args) (free_let (Var num_args) (LENGTH env))) c)) ==>
    cl_rel max_app fs refs code
           (env,ys)
           (Closure (SOME p) [] env num_args x)
           (Block closure_tag (CONS (bvlSem_CodePtr (p + (num_stubs
             max_app))) (CONS (Number (&(num_args - 1))) ys)))) /\
   (
     num_args <= max_app /\ ~(num_args = 0) /\
     every_Fn_SOME [x] /\
     every_Fn_vs_SOME [x] /\
     clos_to_bvl_compile_exps max_app [x] aux = ([c],aux1) /\
     clos_to_bvlProof_code_installed aux1 code /\
     sptree_lookup (p + (num_stubs max_app)) code =
       SOME (num_args + (1:num),Let (APPEND (list_of_seq Var
         (num_args + 1)) (free_let (Var num_args) (LENGTH env))) c) ==>
     cl_rel max_app fs refs code (env,ys)
            (Recclosure (SOME p) [] env [(num_args,x)] 0)
            (Block closure_tag (CONS (bvlSem_CodePtr (p + (num_stubs
              max_app))) (CONS (Number (&(num_args - 1))) ys)))) /\
     ((exps = MAP FST exps_ps) /\
      (ps = MAP SND exps_ps) /\ (ps = list_of_seq (\n. loc +
        (num_stubs max_app) + 2 * n) (LENGTH exps_ps)) /\
      (rs = MAP (\((n,e),p). Block closure_tag [bvlSem_CodePtr p;
        Number (&(n - 1)); RefPtr T r]) exps_ps) /\
      ~(r IN fs) /\
      (FLOOKUP refs r = SOME (ValueArray (APPEND rs ys))) /\
      1 < LENGTH exps /\ k < LENGTH exps /\
      every_Fn_SOME (MAP SND exps) /\
      every_Fn_vs_SOME (MAP SND exps) /\
      closure_code_installed max_app code exps_ps env ==>
      cl_rel max_app fs refs code (env,ys) (Recclosure (SOME loc)
        [] env exps k) (EL k rs))`;;

let add_args_def = new_definition
  `add_args x1 args' =
        match x1 with
          (Closure loc_opt args env num_args exp:closSem_v) ->
       SOME (Closure loc_opt (APPEND args' args) env num_args exp)
        | (Recclosure loc_opt args env funs i:closSem_v) ->
       SOME (Recclosure loc_opt (APPEND args' args) env funs i)
        | _1 -> NONE`;;

(* [local] *)
let add_args_append = prove
 (`add_args cl arg_env = SOME func ==>
    add_args cl (APPEND args arg_env) = add_args func args`,
  CHEAT_TAC);;

let get_num_args_def = new_definition
  `get_num_args x1 =
        match x1 with
          (Closure loc_opt args env num_args exp:closSem_v) ->
       SOME num_args
        | (Recclosure loc_opt args env funs i:closSem_v) ->
       SOME (FST (EL i funs))
        | _2 -> NONE`;;

let clos_to_bvlProof_v_rel = cake_inductive
  `(clos_to_bvlProof_v_rel max_app f refs code (Number n) (Number n)) /\
   (clos_to_bvlProof_v_rel max_app f refs code (Word64 w) (Word64 w))
     /\
   (ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs (ys:bvlSem_v
     list) ==>
    clos_to_bvlProof_v_rel max_app f refs code (Block t xs) (Block
      (clos_tag_shift t) ys)) /\
   (FLOOKUP refs p = SOME (ByteArray T bs) /\ ~(p IN FRANGE f) ==>
    clos_to_bvlProof_v_rel max_app f refs code (closSem_ByteVector
      bs) (RefPtr T p)) /\
   ((FLOOKUP f r1 = SOME r2) ==>
    clos_to_bvlProof_v_rel max_app f refs code (RefPtr b r1) (RefPtr
      b r2)) /\
   (
    ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
    cl_rel max_app (FRANGE f) refs code (env,fvs) cl (Block
      closure_tag (CONS (bvlSem_CodePtr p) (CONS (Number n) ys))) ==>
    clos_to_bvlProof_v_rel max_app f refs code cl (Block closure_tag
      (CONS (bvlSem_CodePtr p) (CONS (Number n) ys)))) /\
   (
    ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
    ALL2 (clos_to_bvlProof_v_rel max_app f refs code) arg_env ys /\
      ~(arg_env = []) /\
    LENGTH arg_env < num_args /\
    (sptree_lookup (partial_app_fn_location max_app (num_args - 1)
      (LENGTH ys - 1)) code =
      SOME (num_args - LENGTH arg_env +
        1,generate_partial_app_closure_fn (num_args - 1) (LENGTH ys -
        1))) /\
    add_args cl arg_env = SOME cl_app /\
    get_num_args cl = SOME num_args /\
    cl_rel max_app (FRANGE f) refs code (env,fvs) cl cl' ==>
    clos_to_bvlProof_v_rel max_app f refs code cl_app
                        (Block partial_app_tag
                              (CONS (bvlSem_CodePtr
                                (partial_app_fn_location max_app
                                (num_args - 1) (LENGTH ys - 1)))
                                (CONS (Number (&(num_args - 1 -
                                LENGTH arg_env))) (CONS cl' ys)))))`;;
hol4_overload "v_rel" "clos_to_bvlProof_v_rel";;

(* [local] *)
let cl_rel_F = prove
 (`~(cl_rel max_app f refs code (env,ys) (Number i) cl) /\
    ~(cl_rel max_app f refs code (env,ys) (Word64 w) cl) /\
    ~(cl_rel max_app f refs code (env,ys) (RefPtr b p) cl) /\
    ~(cl_rel max_app f refs code (env,ys) (Block tag xs) cl) /\
    ~(cl_rel max_app f refs code (env,ys) (closSem_ByteVector bs)
      cl)`,
  CHEAT_TAC);;

(* [local] *)
let add_args_F = prove
 (`!cl args p i tag xs. ~(add_args cl args = SOME (RefPtr b p)) /\
  ~(add_args cl args = SOME (Number i)) /\ ~(add_args cl args = SOME
  (Word64 w)) /\ ~(add_args cl args = SOME (Block tag xs)) /\
  ~(add_args cl args = SOME (closSem_ByteVector bs))`,
  CHEAT_TAC);;

(* v_rel_Unit[simp] *)
let clos_to_bvlProof_v_rel_Unit = prove
 (`(v_rel max_app f refs code Unit y <=> (y = Unit)) /\
   (v_rel max_app f refs code x Unit <=> (x = Unit))`,
  CHEAT_TAC);;

(* v_rel_Boolv[simp] *)
let clos_to_bvlProof_v_rel_Boolv = prove
 (`(v_rel max_app f refs code (Boolv b) y <=> (y = Boolv b)) /\
   (v_rel max_app f refs code x (Boolv b) <=> (x = Boolv b))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:984-995: a theorem that HOL4
   states as the value of an ML expression: v_rel_SIMP *)

let _ = size_thms "bvlSem_v";;
let _ = size_thms "closSem_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let clos_to_bvlProof_env_rel_def,clos_to_bvlProof_env_rel_ind =
  define_wf
  `MEASURE (\(x0,x1,x2,x3,x4,x5). closSem_v_size1 x4 + bvlSem_v_size1
  x5)`
  [`clos_to_bvlProof_env_rel max_app f refs code x5 ys =
        match (x5,ys) with
          ([],[]) -> T
        | ([],ys) -> T
        // bvl env allowed to contain extra stuff
        | ((CONS x xs),[]) -> F
        | ((CONS x xs),(CONS y ys)) ->
        v_rel max_app f refs code x y /\
          clos_to_bvlProof_env_rel max_app f refs code xs ys`];;
hol4_overload "env_rel" "clos_to_bvlProof_env_rel";;

(* [local] *)
let env_rel_APPEND = prove
 (`!xs1 xs2.
       ALL2 (v_rel max_app f1 refs code) xs1 xs2 /\
       env_rel max_app f1 refs code ys1 ys2 ==>
       env_rel max_app f1 refs code (APPEND xs1 ys1) (APPEND xs2
         ys2)`,
  CHEAT_TAC);;

(* [local] *)
let list_rel_IMP_env_rel = prove
 (`!xs ys.
       ALL2 (v_rel max_app f refs code) xs ys ==>
       env_rel max_app f refs code xs (APPEND ys ts)`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_IMP_LENGTH = prove
 (`!env1 env2.
       env_rel max_app f refs code env1 env2 ==>
       LENGTH env1 <= LENGTH env2`,
  CHEAT_TAC);;

(* [local] *)
let LESS_LENGTH_env_rel_IMP = prove
 (`!env env2 n.
       n < LENGTH env /\ env_rel max_app f refs code env env2 ==>
       n < LENGTH env2 /\ v_rel max_app f refs code (EL n env) (EL
         n env2)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1041-1043: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:1045-1061: code that the source
   has in a comment *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let clos_to_bvlProof_nth_code_def,clos_to_bvlProof_nth_code_ind =
  define_wf
  `MEASURE (\(x0,x1). (\n. n) x1)`
  [`clos_to_bvlProof_nth_code t_co 0 = LN`;
   `clos_to_bvlProof_nth_code t_co (SUC n) =
      sptree_union (fromAList (SND (t_co 0)))
        (clos_to_bvlProof_nth_code (misc_shift_seq 1 t_co) n)`];;
hol4_overload "nth_code" "clos_to_bvlProof_nth_code";;

let compile_oracle_inv_def = new_definition
  `compile_oracle_inv max_app s_code s_cc s_co t_code t_cc t_co <=>
      s_cc = pure_cc (compile_inc max_app) t_cc /\
      t_co = pure_co (compile_inc max_app) o s_co /\
      (!n cfg ps. t_co n = (cfg,ps) ==> ALL_DISTINCT (MAP FST ps)) /\
      (!n. DISJOINT (domain (sptree_union t_code (nth_code t_co n)))
             (set_of_list (MAP FST (SND (t_co n))))) /\
      (!n cfg e ps.
        s_co n = (cfg,e,ps) ==>
        every_Fn_SOME e /\ every_Fn_vs_SOME e /\
        ALL (\p. every_Fn_SOME [SND (SND p)]) ps /\
        ALL (\p. every_Fn_vs_SOME [SND (SND p)]) ps)`;;

(* HOL4 clos_to_bvlProofScript.sml:1083-1089: code that the source
   has in a comment *)

let clos_to_bvlProof_ref_rel_def = new_definition
  `clos_to_bvlProof_ref_rel R x2 x3 =
        match (x2,x3) with
          (closSem_ValueArray vs,bvlSem_ValueArray ws) -> ALL2 R vs
            ws
        | ((closSem_Thunk m1 v),(bvlSem_Thunk m2 w)) -> m1 = m2 /\ R
          v w
        | ((ByteArray as),(ByteArray g bs)) -> ~g /\ as = bs
        | (_3,_4) -> F`;;
hol4_overload "ref_rel" "clos_to_bvlProof_ref_rel";;

(* ref_rel_simp[simp] *)
let clos_to_bvlProof_ref_rel_simp = prove
 (`(ref_rel R (closSem_ValueArray vs) y <=> (?ws. y = ValueArray ws /\
  ALL2 R vs ws)) /\
   (ref_rel R (Thunk m v) y <=> (?w. y = Thunk m w /\ R v w)) /\
   (ref_rel R (ByteArray bs) y <=> y = ByteArray F bs)`,
  CHEAT_TAC);;

let clos_to_bvlProof_state_rel_def = new_definition
  `clos_to_bvlProof_state_rel f (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     (closSem_state_ffi s = bvlSem_state_ffi t) /\
     ALL2 (OPTREL (v_rel (closSem_state_max_app s) f
       (bvlSem_state_refs t) (bvlSem_state_code t)))
       (closSem_state_globals s) (DROP num_added_globals
       (bvlSem_state_globals t)) /\
     get_global 0 (bvlSem_state_globals t) = SOME (SOME (global_table
       (closSem_state_max_app s))) /\
     INJ ((FAPPLY) f) (FDOM f) (FRANGE f) /\
     (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP (bvlSem_state_refs
       t) y = SOME (ByteArray T bs))) /\
     (FDOM f = FDOM (closSem_state_refs s)) /\
     (FRANGE f SUBSET FDOM (bvlSem_state_refs t)) /\
     (!n x. (FLOOKUP (closSem_state_refs s) n = SOME x) ==>
            (?y m. (FLOOKUP f n = SOME m) /\
                  (FLOOKUP (bvlSem_state_refs t) m = SOME y) /\
                  ref_rel (v_rel (closSem_state_max_app s) f
                    (bvlSem_state_refs t) (bvlSem_state_code t)) x y))
                    /\
     (!n. n < closSem_state_max_app s ==>
          sptree_lookup (generic_app_fn_location n)
            (bvlSem_state_code t) = SOME (n + 2,generate_generic_app
            (closSem_state_max_app s) n)) /\
     (!tot n. tot < closSem_state_max_app s /\ n < tot ==>
       sptree_lookup (partial_app_fn_location (closSem_state_max_app
         s) tot n) (bvlSem_state_code t) = SOME (tot - n +
         1,generate_partial_app_closure_fn tot n)) /\
     sptree_lookup (num_stubs (closSem_state_max_app s) - 2)
       (bvlSem_state_code t) = SOME (2,force_thunk_code) /\
     compile_oracle_inv (closSem_state_max_app s) (closSem_state_code
       s) (closSem_state_compile s) (closSem_state_compile_oracle s)
       (bvlSem_state_code
                              t) (bvlSem_state_compile t)
                                (bvlSem_state_compile_oracle t) /\
     (!name arity c.
       (FLOOKUP (closSem_state_code s) name = SOME (arity,c)) ==>
       (?aux1 c2 aux2.
         (clos_to_bvl_compile_exps (closSem_state_max_app s) [c] aux1
           = ([c2],aux2)) /\
         (sptree_lookup (name + (num_stubs (closSem_state_max_app
           s))) (bvlSem_state_code t) = SOME (arity,c2)) /\
         clos_to_bvlProof_code_installed aux2 (bvlSem_state_code
           t)))`;;
hol4_overload "state_rel" "clos_to_bvlProof_state_rel";;

(* state_rel_globals[local] *)
let clos_to_bvlProof_state_rel_globals = prove
 (`state_rel f s t ==>
     get_global 0 (state_globals t) = SOME (SOME (global_table
       (closSem_state_max_app s))) /\
     ALL2 (OPTREL (v_rel (closSem_state_max_app s) f (state_refs t)
       (state_code t))) (state_globals s) (DROP num_added_globals
       (state_globals t))`,
  CHEAT_TAC);;

(* state_rel_clock[simp] *)
let clos_to_bvlProof_state_rel_clock = prove
 (`(!f s t. state_rel f s (state_clock_fupd (K x) t) = state_rel f s t)
  /\
   (!f s t. state_rel f (state_clock_fupd (K x) s) t = state_rel f
     s t)`,
  CHEAT_TAC);;

let state_rel_refs_lookup = prove
 (`state_rel f s1 s2 /\
   FLOOKUP (state_refs s1) p = SOME x /\
   FLOOKUP f p = SOME p' ==>
   (?x'. FLOOKUP (state_refs s2) p' = SOME x' /\
     ref_rel (v_rel (closSem_state_max_app s1) f (state_refs s2)
       (state_code s2)) x x')`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_SUBMAP = prove
 (`cl_rel max_app f1 refs1 code (env,ys) x y /\
    f1 SUBSET f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
    cl_rel max_app f2 refs2 code (env,ys) x y`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1175-1193: a theorem that HOL4
   states as the value of an ML expression: v_rel_SUBMAP *)

(* env_rel_SUBMAP *)
let clos_to_bvlProof_env_rel_SUBMAP = prove
 (`!env1 env2.
         env_rel max_app f1 refs1 code env1 env2 /\
         f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2
           (FRANGE f2) ==>
         env_rel max_app f2 refs2 code env1 env2`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_NEW_REF = prove
 (`!x y. cl_rel max_app f1 refs1 code (env,ys) x y ==> ~(r IN FDOM
  refs1) ==>
          cl_rel max_app f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1217-1232: a theorem that HOL4
   states as the value of an ML expression: v_rel_NEW_REF *)

(* [local] *)
let cl_rel_UPDATE_REF = prove
 (`!x y. cl_rel max_app f1 refs1 code (env,ys) x y ==>
           (r IN f1) ==>
           cl_rel max_app f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1250-1266: a theorem that HOL4
   states as the value of an ML expression: v_rel_UPDATE_REF *)

(* [local] *)
let OPTREL_v_rel_NEW_REF = prove
 (`OPTREL (v_rel max_app f1 refs1 code) x y /\ ~(r IN FDOM refs1) ==>
     OPTREL (v_rel max_app f1 (refs1 |+ (r,t)) code) x y`,
  CHEAT_TAC);;

(* [local] *)
let OPTREL_v_rel_UPDATE_REF = prove
 (`OPTREL (v_rel max_app f1 refs1 code) x y /\ r IN FRANGE f1 ==>
     OPTREL (v_rel max_app f1 (refs1 |+ (r,t)) code) x y`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_NEW_REF = prove
 (`!x y.
       env_rel max_app f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
       env_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_NEW_F = prove
 (`!x y.
       cl_rel max_app f2 (state_refs t2) (state_code t2) (env,ys) x y
         ==>
       ~(qq IN FDOM (state_refs t2)) ==>
       cl_rel max_app (qq INSERT f2) (state_refs t2) (state_code
         t2) (env,ys) x y`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1304-1323: a theorem that HOL4
   states as the value of an ML expression: v_rel_NEW_F *)

(* HOL4 clos_to_bvlProofScript.sml:1325-1331: a theorem that HOL4
   states as the value of an ML expression: OPTREL_v_rel_NEW_F *)

let state_rel_UPDATE_REF = prove
 (`state_rel f2 p1 t2 /\
   FLOOKUP f2 dst = SOME r2 /\
   FLOOKUP (state_refs p1) dst = SOME v0 /\
   ref_rel (v_rel (closSem_state_max_app p1) f2 (state_refs t2)
     (state_code t2)) v v' /\
   (!bs. ~(v' = ByteArray T bs)) ==>
   state_rel f2 (state_refs_fupd (K (state_refs p1 |+ (dst,v))) p1)
     (state_refs_fupd (K (state_refs t2 |+ (r2,v'))) t2)`,
  CHEAT_TAC);;

let state_rel_NEW_REF = prove
 (`state_rel f2 p1 t2 /\ ~(p IN FDOM (state_refs t2)) ==>
   state_rel f2 p1 (state_refs_fupd (K (state_refs t2 |+ (p,v)))
     t2)`,
  CHEAT_TAC);;

(* semantic functions respect relation *)

(* v_to_list[local] *)
let clos_to_bvlProof_v_to_list = prove
 (`!v l v'.
    v_to_list v = SOME l /\
    v_rel max_app f r c v v' ==>
    (?l'. v_to_list v' = SOME l' /\
         ALL2 (v_rel max_app f r c) l l')`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1445-1449: a theorem whose
   statement the port cannot state yet: not_isClos *)

(* [local] *)
let do_eq = prove
 (`INJ ((FAPPLY) f) (FDOM f) (FRANGE f) /\
    (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP r y = SOME
      (ByteArray T bs))) ==>
     (!x y x1 y1.
            v_rel max_app f r c x x1 /\
            v_rel max_app f r c y y1 ==>
            do_eq x y = do_eq r x1 y1) /\
     (!x y x1 y1.
            ALL2 (v_rel max_app f r c) x x1 /\
            ALL2 (v_rel max_app f r c) y y1 ==>
            do_eq_list x y = do_eq_list r x1 y1)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1490: the ML values that the
   definitions below antiquote *)

(* do_eq_sym[local] *)
let clos_to_bvlProof_do_eq_sym = prove
 (`(!((r:(num,'a bvlSem_ref)fmap)) x y. do_eq r x y = do_eq r y x) /\
    (!((r:(num,'a bvlSem_ref)fmap)) x y. do_eq_list r x y =
      do_eq_list r y x)`,
  CHEAT_TAC);;

let do_eq_list_T_every = prove
 (`!vs1 vs2. do_eq_list r vs1 vs2 = Eq_val T <=> ALL2 (\v1 v2. do_eq r
  v1 v2 = Eq_val T) vs1 vs2`,
  CHEAT_TAC);;

(* list_to_v_v_rel *)
let clos_to_bvlProof_list_to_v_v_rel = prove
 (`!xs ys.
     ALL2 (v_rel app f refs code) xs ys ==>
       v_rel app f refs code (list_to_v xs) (list_to_v ys)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1527-1528: ML code, not ported *)

(* do_app[local] *)
let clos_to_bvlProof_do_app = prove
 (`(do_app op xs s1 = Rval (v,s2)) /\
   state_rel f s1 t1 /\
   ALL2 (v_rel (closSem_state_max_app s1) f (state_refs t1)
     (state_code t1)) xs ys /\
   (~(
    // store updates need special treatment
    op = closLang_MemOp closLang_Ref)) /\ (~(op = closLang_MemOp
      closLang_Update)) /\ (~(op = closLang_MemOp closLang_XorByte)) /\
   (~(op = closLang_MemOp closLang_RefArray)) /\ (!f. ~(op =
     closLang_MemOp (closLang_RefByte f))) /\ (~(op = closLang_MemOp
     closLang_UpdateByte)) /\
   (~(op = closLang_MemOp closLang_FromListByte)) /\ ~(op =
     closLang_MemOp closLang_ConcatByteVec) /\
   (!b. ~(op = closLang_MemOp (closLang_CopyByte b))) /\ (!c. ~(op =
     closLang_BlockOp (closLang_Constant c))) /\
   (!n. ~(op = (FFI n))) /\
   (!t. ~(op = (ThunkOp t))) ==>
   (?w t2.
     (do_app (clos_to_bvl_compile_op op) ys t1 = Rval (w,t2)) /\
     v_rel (closSem_state_max_app s1) f (state_refs t1) (state_code
       t1) v w /\
     state_rel f s2 t2 /\
     (state_refs t1 = state_refs t2) /\ (state_code t1 = state_code
       t2))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1801-1804: ML code, not ported *)

(* do_app_err[local] *)
let clos_to_bvlProof_do_app_err = prove
 (`do_app op xs s1 = Rerr err /\ ~(err = Rabort Rtype_error) /\
    state_rel f s1 t1 /\
    ALL2 (v_rel (closSem_state_max_app s1) f (state_refs t1)
      (state_code t1)) xs ys ==>
    (?e. do_app (clos_to_bvl_compile_op op) ys t1 = Rerr e /\
        exc_rel (v_rel (closSem_state_max_app s1) f (state_refs t1)
          (state_code t1)) err e)`,
  CHEAT_TAC);;

(* correctness of implemented primitives *)

let eq_res_def = new_definition
  `eq_res x1 =
      match x1 with
        Eq_val b -> Rval [bvlSem_Boolv b]
      | _5 -> Rerr (Rabort Rtype_error)`;;

(* [local] *)
let eq_res_not_timeout = prove
 (`~(eq_res x = Rerr (Rabort Rtimeout_error))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_check_closure = prove
 (`n < LENGTH env /\
    EL n env = bvlSem_Block t vs ==>
    evaluate ([check_closure n e],env,s) =
    (if t = closure_tag \/ t = partial_app_tag then
      (eq_res (Eq_val T),s) else
      evaluate ([e],env,s))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1864: the ML values that the
   definitions below antiquote *)

(* compiler correctness *)

(* [local] *)
let EXISTS_NOT_IN_refs = prove
 (`?x. ~(x IN FDOM (bvlSem_state_refs (t1:('c,'ffi)bvlSem_state)))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:1874-1887: a theorem that HOL4
   states as the value of an ML expression: lookup_vars_IMP2 *)

(* [local] *)
let lookup_vars_IMP = prove
 (`!vs env xs env2.
       (lookup_vars vs env = SOME xs) /\
       env_rel max_app f refs code env env2 ==>
       (?ys. (evaluate (MAP Var vs,env2,t1) = (Rval
         ys,(t1:('c,'ffi)bvlSem_state))) /\
            ALL2 (v_rel max_app f refs code) xs ys /\
            (LENGTH vs = LENGTH xs))`,
  CHEAT_TAC);;

(* [local] *)
let compile_exps_IMP_code_installed = prove
 (`(clos_to_bvl_compile_exps max_app xs aux = (c,aux1)) /\
     clos_to_bvlProof_code_installed aux1 code ==>
     clos_to_bvlProof_code_installed aux code`,
  CHEAT_TAC);;

(* [local] *)
let compile_exps_LIST_IMP_compile_exps_EL = prove
 (`!exps aux1 c7 aux7 i n8 n4 aux5 num_args e.
       EL i exps = (num_args,e) /\
       (clos_to_bvl_compile_exps max_app (MAP SND exps) aux1 =
         (c7,aux7)) /\ i < LENGTH exps /\
       (build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c7)
         aux7 = (n4,aux5)) /\
       clos_to_bvlProof_code_installed aux5 (state_code t1) ==>
       (?aux c aux1'.
         clos_to_bvl_compile_exps max_app [e] aux = ([c],aux1') /\
         sptree_lookup (n8 + 2 * i) (state_code t1) = SOME (num_args
           + 1,SND (code_for_recc_case k num_args c)) /\
         clos_to_bvlProof_code_installed aux1' (state_code t1))`,
  CHEAT_TAC);;

let compile_exps_EL = prove
 (`!ls aux l2 aux2 n.
   clos_to_bvl_compile_exps ma ls aux = (l2,aux2) /\
   n < LENGTH ls ==>
   (?auxn aux2n.
   clos_to_bvl_compile_exps ma [EL n ls] auxn = ([EL n l2],aux2n) /\
   IS_SUBLIST aux2 aux2n)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_recc_Lets = prove
 (`!(ll:(num#'a) list) n7 rr env' (t1:('c,'ffi)bvlSem_state) ys c8
  (x:num#'a) (x':num#'a) ck.
      ALL (\n. n7 + ns + 2 * n IN domain (bvlSem_state_code t1))
        (list_of_seq I (LENGTH ll)) ==>
      (evaluate
        ([recc_Lets (n7 + ns) (REVERSE (MAP FST ll)) (LENGTH ll) (HD
          c8)],CONS (Block closure_tag [bvlSem_CodePtr (n7 + (ns + 2 *
          LENGTH ll)); Number (&(FST x - 1)); RefPtr T rr])
          env',bvlSem_state_clock_fupd (K ck) (bvlSem_state_refs_fupd (K
          (bvlSem_state_refs t1 |+ (rr,
                ValueArray
                (APPEND (APPEND (MAP (K (Number (&0))) (MAP FST ll))
                 [Block closure_tag [bvlSem_CodePtr (n7 + (ns + 2 *
                   LENGTH ll)); Number (&(FST x' - 1)); RefPtr T rr]])
                   ys))))
         t1)) =
       evaluate
        ([HD c8],APPEND (MAP2 (\n args. Block closure_tag
          [bvlSem_CodePtr (n7 + ns + 2 * n); Number (&(args - 1));
          RefPtr T rr])
                   (list_of_seq I (LENGTH ll + 1)) (APPEND (MAP FST
                     ll) [FST x])) env',bvlSem_state_clock_fupd (K ck)
                     (bvlSem_state_refs_fupd (K (bvlSem_state_refs t1 |+
                     (rr,
                ValueArray
                (APPEND (MAP2 (\n args. Block closure_tag
                  [bvlSem_CodePtr (n7 + ns + 2 * n); Number (&(args -
                  1)); RefPtr T rr])
                   (list_of_seq I (LENGTH ll + 1)) (APPEND (MAP FST
                     ll) [FST x'])) ys))))
         t1)))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_app_helper = prove
 (`(!x. ~(r = Rval x)) /\ evaluate (c8,env,s) = (r,s') ==>
     evaluate
            ([match loc with
               NONE -> Let (APPEND c8 [c7]) (mk_cl_call (Var
                 (LENGTH c8)) (list_of_seq Var (LENGTH c8))) | SOME
                 loc -> Call (LENGTH c8 - 1) (SOME (loc + num_stubs
                 max_app)) (APPEND c8 [c7])],env,s) = (r,s')`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_app_helper2 = prove
 (`(!x. ~(r = Rval x)) /\ evaluate (c8,env,s) = (Rval x,s') /\ evaluate
  ([c7],env,s') = (r,s'') ==>
     evaluate ([match loc with
               NONE -> Let (APPEND c8 [c7]) (mk_cl_call (Var
                 (LENGTH c8)) (list_of_seq Var (LENGTH c8))) | SOME
                 loc -> Call (LENGTH c8 - 1) (SOME (loc + num_stubs
                 max_app)) (APPEND c8 [c7])],env,s) = (r,s'')`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_simple_genlist_vars = prove
 (`!env1 env2 s.
     0 < LENGTH env1 ==>
     evaluate (list_of_seq Var (LENGTH env1),APPEND env1 env2,s) =
       (Rval env1,s)`,
  CHEAT_TAC);;

let num_remaining_args_def = new_definition
  `num_remaining_args x1 =
        match x1 with
          (Closure loc_opt args env num_args exp:closSem_v) ->
       SOME (num_args - LENGTH args)
        | (Recclosure loc_opt args env funs i:closSem_v) ->
       SOME (FST (EL i funs) - LENGTH args)
        | _6 -> NONE`;;

(* [local] *)
let dest_closure_part_app = prove
 (`!loc_opt func args c f1 t1.
     ~(LENGTH args = 0) /\
     dest_closure max_app loc_opt func args = SOME (Partial_app c)
       ==>
     loc_opt = NONE /\
     SOME c = add_args func args /\
     (?n. num_remaining_args func = SOME n /\ LENGTH args < n /\
       LENGTH args <= max_app)`,
  CHEAT_TAC);;

let get_loc_def = new_definition
  `get_loc x1 =
        match x1 with
          (Closure (SOME loc) args env num_args exp:closSem_v) ->
            SOME loc
        | (Recclosure (SOME loc) args env fns i) -> SOME (loc + 2 *
          i)
        | _7 -> NONE`;;

let get_old_args_def = new_definition
  `get_old_args x1 =
        match x1 with
          (Closure loc args env num_args exp:closSem_v) -> SOME args
        | (Recclosure loc args env fns i) -> SOME args
        | _8 -> NONE`;;

let get_cl_env_def = new_definition
  `get_cl_env x1 =
        match x1 with
          (Closure loc args env num_args exp:closSem_v) -> SOME env
        | (Recclosure loc args env fns i) -> SOME env
        | _9 -> NONE`;;

(* [local] *)
let dest_closure_full_app = prove
 (`!loc_opt func args c f1 t1 exp args1 args2.
     dest_closure max_app loc_opt func args = SOME (Full_app exp
       args1 args2) ==>
     (?rem_args loc num_args old_args cl_env.
       get_loc func = loc /\
       num_remaining_args func = SOME rem_args /\
       get_num_args func = SOME num_args /\
       get_old_args func = SOME old_args /\
       get_cl_env func = SOME cl_env /\
       rem_args <= LENGTH args /\
       rem_args <= num_args /\
       num_args <= LENGTH old_args + LENGTH args /\
       LENGTH args2 = LENGTH args - rem_args /\
       check_loc max_app loc_opt loc num_args (LENGTH args)
         (num_args - rem_args))`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_num_rem_args = prove
 (`!f refs code v1 v2 n.
     v_rel max_app f refs code v1 v2 /\
     num_remaining_args v1 = SOME n ==>
     (?tag ptr rest exp.
       v2 = Block tag (CONS (bvlSem_CodePtr ptr) (CONS (Number (&n -
         (&1))) rest)) /\ ~(n = 0) /\
       sptree_lookup ptr code = SOME (n + 1,exp))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:2209-2240: a theorem that HOL4
   states as the value of an ML expression: unpack_closure_thm *)

(* [local] *)
let cl_rel_get_num_args = prove
 (`cl_rel max_app f1 refs code (env,ys) func (Block tag (CONS p (CONS
  (Number (&(total_args) - (&1))) fvs))) ==>
    get_num_args func = SOME total_args`,
  CHEAT_TAC);;

(* [local] *)
let arith_helper_lem = prove
 (`~(LENGTH args' = 0) ==> x - 1 - (LENGTH args' - 1) = x - LENGTH
  args'`,
  CHEAT_TAC);;

(* [local] *)
let arith_helper_lem3 = prove
 (`LENGTH args' < (total_args + 1) - LENGTH prev_args /\ ~(LENGTH args'
  = 0) /\
    total_args - LENGTH prev_args + 1 = num_args - LENGTH prev_args
      ==>
    total_args - ((LENGTH args' + LENGTH prev_args) - 1) =
      (total_args + 1) - (LENGTH args' + LENGTH prev_args) /\
    LENGTH args' + LENGTH prev_args < total_args + 1 /\
    num_args = total_args + 1`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:2277: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_to_bvlProofScript.sml:2279-2285: ML code, not ported *)

(* [local] *)
let evaluate_mk_cl_call_spec = prove
 (`!s env tag p n args exp xs.
     sptree_lookup p (state_code s) = SOME (n + 2,exp) /\
     sptree_lookup (generic_app_fn_location (LENGTH args - 1))
       (state_code s) =
       SOME (LENGTH args + 1,generate_generic_app max_app (LENGTH
         args - 1)) /\
     LENGTH args - 1 >= n /\
     n < max_app /\ ~(LENGTH args = 0) ==>
     evaluate ([mk_cl_call (Var (LENGTH args)) (list_of_seq Var
       (LENGTH args))],APPEND (APPEND args [Block tag (CONS
       (bvlSem_CodePtr p) (CONS (Number (&n)) xs))]) env,s) =
      (if n = LENGTH args - 1 then
        if state_clock s < LENGTH args then (Rerr (Rabort
          Rtimeout_error),state_clock_fupd (K 0) s) else evaluate
          ([exp],APPEND args [Block tag (CONS (bvlSem_CodePtr p) (CONS
          (Number (&(LENGTH args - 1))) xs))],
                    dec_clock (LENGTH args) s) else
          if state_clock s < n + 2 then (Rerr (Rabort
            Rtimeout_error),state_clock_fupd (K 0) s) else
          match evaluate ([exp],APPEND (DROP (LENGTH args - (n + 1))
            args) [Block tag (CONS (bvlSem_CodePtr p) (CONS (Number
            (&n)) xs))],
                      dec_clock (n + 2) s) with (Rval [v],st') ->
                 (match evaluate ([mk_cl_call (Var 0) (list_of_seq
                   (\n. Var (n + 1)) (LENGTH args - (n + 1)))],CONS v
                   (APPEND args [Block tag (CONS (bvlSem_CodePtr p)
                   (CONS (Number (&n)) xs))]),
                              st') with (Rval v,s2) -> (Rval [HD
                                v],s2) | x -> x) | x -> x)`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_get_loc = prove
 (`cl_rel max_app f1 refs code (env,fvs) func (Block tag (CONS
  (bvlSem_CodePtr p) (CONS n ys))) ==>
    num_stubs max_app <= p /\
    get_loc func = SOME (p - (num_stubs max_app))`,
  CHEAT_TAC);;

(* Differs from check_loc and dest_closure by not checking that max_app *)
let check_loc'_def = define_cases
  [`check_loc' NONE loc num_params num_args so_far <=> T`;
   `check_loc' (SOME p) loc num_params num_args so_far <=>
        (num_params = num_args) /\ (so_far = (0:num)) /\ (SOME
          p = loc)`];;

let dest_closure'_def = new_definition
  `dest_closure' loc_opt f args =
     (match f with Closure loc arg_env clo_env num_args exp ->
         (if check_loc' loc_opt loc num_args (LENGTH args) (LENGTH
           arg_env) /\ LENGTH arg_env < num_args then
           if ~(LENGTH args + LENGTH arg_env < num_args) then
             SOME (Full_app exp
                            (APPEND (APPEND (REVERSE (TAKE (num_args
                              - LENGTH arg_env) (REVERSE args)))
                             arg_env) clo_env)
                            (REVERSE (DROP (num_args - LENGTH
                              arg_env) (REVERSE args)))) else
             SOME (Partial_app (closSem_Closure loc (APPEND args
               arg_env) clo_env num_args exp)) else
           NONE) | Recclosure loc arg_env clo_env fns i ->
         (let (num_args,exp) = EL i fns in
           if LENGTH fns <= i \/
              ~(check_loc' loc_opt (OPTION_MAP ((+) (2 * i)) loc)
                num_args (LENGTH args) (LENGTH arg_env)) \/
              ~(LENGTH arg_env < num_args) then NONE else
             let rs = list_of_seq (Recclosure loc [] clo_env fns)
               (LENGTH fns) in
               if ~(LENGTH args + LENGTH arg_env < num_args) then
                 SOME (Full_app exp
                              (APPEND (APPEND (APPEND (REVERSE (TAKE
                                (num_args - LENGTH arg_env) (REVERSE
                                args)))
                              arg_env) rs) clo_env)
                              (REVERSE (DROP (num_args - LENGTH
                                arg_env) (REVERSE args)))) else
                 SOME (Partial_app (closSem_Recclosure loc (APPEND
                   args arg_env) clo_env fns i))) | _10 -> NONE)`;;

(* [local] *)
let dest_cl_imp_dest_cl' = prove
 (`dest_closure max_app l f a = SOME x ==> dest_closure' l f a = SOME
  x`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_run_lemma1 = prove
 (`num_args <= LENGTH args' ==>
    evaluate (list_of_seq Var num_args,APPEND (DROP (LENGTH args' -
      num_args) args') stuff,t1) =
    (Rval (DROP (LENGTH args' - num_args) args'),t1)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:2420-2431: a theorem that HOL4
   states as the value of an ML expression: cl_rel_run_lemma2 *)

(* [local] *)
let cl_rel_run_lemma3 = prove
 (`ALL2 R args args' ==>
    ALL2 R (DROP (LENGTH args' - n) args) (DROP (LENGTH args' - n)
      args')`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:2444-2456: a theorem that HOL4
   states as the value of an ML expression: bEval_free_let_Block *)

(* HOL4 clos_to_bvlProofScript.sml:2458-2480: a proof *)

(* [local] *)
let genlist_el = prove
 (`!skip st r xs args p n env ys.
     FLOOKUP (state_refs st) r = SOME (ValueArray (APPEND ys xs)) /\
     skip = LENGTH ys ==>
     bvlSem_evaluate (list_of_seq (\i. (\b i. bvl_Op
       (closLang_BlockOp (closLang_ElemAt i)) [b]) (Var 0) (i + skip))
       (LENGTH xs),CONS (RefPtr T r) (APPEND args (CONS (Block
       closure_tag [bvlSem_CodePtr p; Number (&n); RefPtr T r]) env)),
            st) =
     (Rval xs,st)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_code_for_recc_case = prove
 (`!st r xs args c p n env.
     FLOOKUP (state_refs st) r = SOME (ValueArray xs) ==>
     evaluate ([SND (code_for_recc_case (LENGTH xs) (LENGTH args)
       c)],APPEND args (CONS (Block closure_tag [bvlSem_CodePtr p;
       Number (&n); RefPtr T r]) env),
               st) =
     evaluate ([c],APPEND (APPEND (APPEND (APPEND args xs) [RefPtr T
       r]) args) (CONS (Block closure_tag [bvlSem_CodePtr p; Number
       (&n); RefPtr T r]) env),
               st)`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_run = prove
 (`!loc f1 refs code args args' env env' ptr body new_env func func'
  rest n fvs.
     func' = Block closure_tag (CONS (bvlSem_CodePtr ptr) (CONS
       (Number (&n)) env')) /\
     dest_closure' loc func args = SOME (Full_app body new_env rest)
       /\
     v_rel max_app f1 refs code func func' /\
     cl_rel max_app (FRANGE f1) refs code (env,fvs) func func' /\
     ALL2 (v_rel max_app f1 refs code) env fvs /\
     ALL2 (v_rel max_app f1 refs code) args args' ==>
     (?body' aux1 aux2 new_env' exp'.
       sptree_lookup ptr code = SOME (n + 2,exp') /\
       clos_to_bvl_compile_exps max_app [body] aux1 = ([body'],aux2)
         /\ clos_to_bvlProof_code_installed aux2 code /\
       env_rel max_app f1 refs code new_env new_env' /\
       (!t1. evaluate ([exp'],APPEND (DROP (LENGTH args' - (n + 1))
         args') [func'],state_code_fupd (K code) (state_refs_fupd (K
         refs) t1)) =
            evaluate ([body'],new_env',state_code_fupd (K code)
              (state_refs_fupd (K refs) t1))))`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_dest = prove
 (`!f refs code cl cl' fvs fvs'.
     cl_rel max_app f refs code (fvs,fvs') cl cl' ==>
     get_old_args cl = SOME [] /\
     (?l num_args fvs.
       cl' = Block closure_tag (CONS (bvlSem_CodePtr l) (CONS
         (Number (&num_args)) fvs)))`,
  CHEAT_TAC);;

(* [local] *)
let dest_closure_full_of_part = prove
 (`dest_closure max_app loc func args = SOME (Full_app body newenv rest)
  /\ ~(LENGTH arg_env = 0) /\
    add_args cl arg_env = SOME func /\
    get_num_args cl = SOME num_args /\
    LENGTH arg_env < num_args ==>
    dest_closure' loc cl (APPEND args arg_env) = SOME (Full_app
      body newenv rest)`,
  CHEAT_TAC);;

let v_rel_run = prove
 (`!f1 refs code args args' env' ptr body newenv func func' rest tag n
  loc.
       ~(LENGTH args = 0) /\
       func' = Block tag (CONS (bvlSem_CodePtr ptr) (CONS (Number
         (&n)) env')) /\
       dest_closure max_app loc func args = SOME (Full_app body
         newenv rest) /\
       v_rel max_app f1 refs code func func' /\
       ALL2 (v_rel max_app f1 refs code) args args' ==>
       (?ck' body' aux1 aux2 newenv' exp'.
         sptree_lookup ptr code = SOME (n + 2,exp') /\
         clos_to_bvl_compile_exps max_app [body] aux1 =
           ([body'],aux2) /\ clos_to_bvlProof_code_installed aux2 code
           /\
         env_rel max_app f1 refs code newenv newenv' /\
         (!t1.
           evaluate ([exp'],APPEND (DROP (LENGTH args' - (n + 1))
             args') [func'],bvlProps_inc_clock ck' (state_code_fupd (K
             code) (state_refs_fupd (K refs) t1))) =
           evaluate ([body'],newenv',(state_code_fupd (K code)
             (state_refs_fupd (K refs) t1)))))`,
  CHEAT_TAC);;
(* HOL4 clos_to_bvlProofScript.sml:2691: code that the source has in
   a comment *)
(* HOL4 clos_to_bvlProofScript.sml:2692-2765: a proof *)

(* [local] *)
let list_rel_app = prove
 (`!R args args' l0 c l func rem_args.
     dest_closure max_app NONE func args = SOME (Full_app c l l0) /\
     num_remaining_args func = SOME rem_args /\
     ALL2 R args args' ==>
     ALL2 R l0 (TAKE (LENGTH args' - rem_args) args')`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:2788-2812: a theorem that HOL4
   states as the value of an ML expression: mk_call_simp2 *)

(* [local] *)
let no_partial_args = prove
 (`num_remaining_args func = SOME x /\
    get_num_args func = SOME x /\ ~(x = 0) /\
    add_args cl arg_env = SOME func ==>
    arg_env = []`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:2831: the ML values that the
   definitions below antiquote *)


(* HOL4 clos_to_bvlProofScript.sml:2834: ML code, not ported *)

let code_installed_subspt = prove
 (`clos_to_bvlProof_code_installed aux code1 /\ subspt code1 code2 ==>
  clos_to_bvlProof_code_installed aux code2`,
  CHEAT_TAC);;

let closure_code_installed_subspt = prove
 (`closure_code_installed a code1 b c /\ subspt code1 code2 ==>
  closure_code_installed a code2 b c`,
  CHEAT_TAC);;

let cl_rel_subspt = prove
 (`!a b c.
     cl_rel x y z code1 a b c ==> subspt code1 code2 ==> cl_rel x y
       z code2 a b c`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:2866-2880: a theorem that HOL4
   states as the value of an ML expression: v_rel_subspt *)

let env_rel_subspt = prove
 (`!x y z code e1 e2.
    env_rel x y z code e1 e2 ==>
     (!code'. subspt code code' ==> env_rel x y z code' e1 e2)`,
  CHEAT_TAC);;

(* [simp] *)
let clos_tag_shift_eq_nil_tag = prove
 (`(clos_tag_shift tag = nil_tag <=> tag = nil_tag) /\
    (clos_tag_shift tag = cons_tag <=> tag = cons_tag)`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_words_lemma[local] *)
let clos_to_bvlProof_v_rel_IMP_v_to_words_lemma = prove
 (`!x y.
     v_rel max_app f refs code x y ==>
     (!ns. (v_to_list x = SOME (MAP Word64 ns)) <=>
          (v_to_list y = SOME (MAP Word64 ns)))`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_words[local] *)
let clos_to_bvlProof_v_rel_IMP_v_to_words = prove
 (`v_rel max_app f refs code x y ==> v_to_words y = v_to_words x`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_bytes_lemma[local] *)
let clos_to_bvlProof_v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y.
     v_rel max_app f refs code x y ==>
     (!ns. (v_to_list x = SOME (MAP (Number o (&) o (w2n:word8->num))
       ns)) <=>
          (v_to_list y = SOME (MAP (Number o (&) o
            (w2n:word8->num)) ns)))`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_bytes[local] *)
let clos_to_bvlProof_v_rel_IMP_v_to_bytes = prove
 (`v_rel max_app f refs code x y ==> v_to_bytes y = v_to_bytes x`,
  CHEAT_TAC);;

let not_domain_lookup = prove
 (`~(n IN domain x) <=> sptree_lookup n x = NONE`,
  CHEAT_TAC);;

(* [local] *)
let cl_rel_union = prove
 (`!a x y.
     cl_rel max_app f2 refs code a x y ==>
     cl_rel max_app f2 refs (sptree_union code c2) a x y`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_union = prove
 (`!c2 x y.
     v_rel max_app f2 refs code x y ==>
     v_rel max_app f2 refs (sptree_union code c2) x y`,
  CHEAT_TAC);;

let FEVERY_FUPDATE_LIST_SUFF = prove
 (`!progs x p. FEVERY p x /\ ALL p progs ==> FEVERY p (x |++ progs)`,
  CHEAT_TAC);;

let code_installed_union = prove
 (`clos_to_bvlProof_code_installed aux y /\ DISJOINT (set_of_list (MAP
  FST aux)) (domain x) ==>
    clos_to_bvlProof_code_installed aux (sptree_union x y)`,
  CHEAT_TAC);;

let code_installed_union1 = prove
 (`clos_to_bvlProof_code_installed aux t1 ==>
  clos_to_bvlProof_code_installed aux (sptree_union t1 t2)`,
  CHEAT_TAC);;

let code_installed_insert = prove
 (`clos_to_bvlProof_code_installed aux t /\ ~(MEM x (MAP FST aux)) ==>
    clos_to_bvlProof_code_installed aux (sptree_insert x y t)`,
  CHEAT_TAC);;

let code_installed_fromAList = prove
 (`ALL_DISTINCT (MAP FST ls) /\ IS_SUBLIST ls aux ==>
    clos_to_bvlProof_code_installed aux (fromAList ls)`,
  CHEAT_TAC);;

let chain_exps_cons = prove
 (`?k1 k2 other. chain_exps n real_es = CONS (k1,0,k2) other`,
  CHEAT_TAC);;

let compile_exps_APPEND = prove
 (`!max_app xs ys aux.
      clos_to_bvl_compile_exps max_app (APPEND xs ys) aux =
      (let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
       let (c2,aux2) = clos_to_bvl_compile_exps max_app ys aux1 in
         (APPEND c1 c2,aux2))`,
  CHEAT_TAC);;

(* [local] *)
let compile_exps_chain_exps_cons = prove
 (`!n h t a new_exps aux x6 x7.
     clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps n
       (CONS h t))) a =
      (new_exps,aux) /\ clos_to_bvl_compile_exps max_app (CONS h t) a
        = (x6,x7) ==>
     x7 = aux`,
  CHEAT_TAC);;

let compile_exps_same_aux = prove
 (`clos_to_bvl_compile_exps max_app
      (MAP (SND o SND) (chain_exps n real_es)) [] = (new_exps,aux) /\
    extract_name progs0 = (n,real_es) /\
    clos_to_bvl_compile_exps max_app progs0 [] = (x6,x7) ==> x7 =
      aux`,
  CHEAT_TAC);;

let compile_exps_twice_IS_SUBLIST = prove
 (`extract_name progs0 = (n,real_es) /\
    clos_to_bvl_compile_exps max_app
      (APPEND (MAP (SND o SND) (chain_exps n real_es)) progs1) [] =
        (new_exps,aux) /\
    clos_to_bvl_compile_exps max_app progs0 [] = (x6,x7) ==>
    IS_SUBLIST aux x7`,
  CHEAT_TAC);;

let code_installed_cons = prove
 (`clos_to_bvlProof_code_installed (CONS x xs) c ==>
  clos_to_bvlProof_code_installed xs c`,
  CHEAT_TAC);;

let chained_lemma = prove
 (`!index all' x6 t res t1 progs k1 d1 new_exps rest acc x7 max_app aux.
      evaluate (x6,[],t) = (res,t1) /\ HD progs = (k1,0,d1) /\
      Abbrev (progs = APPEND (MAP2 (\(loc,args,_11) exp. (loc +
        num_stubs max_app,args,exp))
                (chain_exps index all') new_exps) rest) /\
      clos_to_bvl_compile_exps max_app all' acc = (x6,x7) /\
      clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps
        index all')) acc =
         (new_exps,aux) /\ clos_to_bvlProof_code_installed progs
           (state_code t) /\ ~(x6 = []) ==>
      (?ck8 res8.
         evaluate ([d1],[],state_clock_fupd (K (ck8 + state_clock t))
           t) = (res8,t1) /\
         (match res with
           Rval vs -> res8 = Rval [LAST vs] | Rerr v3 -> res8 =
             Rerr v3))`,
  CHEAT_TAC);;

let evaluate_IMP_evaluate_chained = prove
 (`bvlSem_evaluate (x6,[],(t:('c,'ffi)bvlSem_state)) = (res,t1) /\
    Abbrev (APPEND progs aux = CONS (k1,0,d1) rest) /\
    Abbrev (progs =
            MAP2 (\(loc,args,_12) exp. (loc + num_stubs
              max_app,args,exp))
              (APPEND (chain_exps n real_es) progs1) new_exps) /\
    clos_to_bvl_compile_exps max_app progs0 [] = (x6,x7) /\
    clos_to_bvl_compile_exps max_app
           (APPEND (MAP (SND o SND) (chain_exps n real_es)) (MAP (SND
             o SND) progs1))
           [] = (new_exps,aux) /\
    extract_name progs0 = (n,real_es) /\
    clos_to_bvlProof_code_installed progs (bvlSem_state_code t) /\
      ~(x6 = []) ==>
    (?ck8 res8.
      bvlSem_evaluate ([d1],[],bvlSem_state_clock_fupd (K
        (bvlSem_state_clock t + ck8)) t) = (res8,t1) /\
      (match res with Rval vs -> res8 = Rval [LAST vs] | err ->
        res8 = err))`,
  CHEAT_TAC);;

(* [local] *)
let refs_lemma = prove
 (`(bvlSem_state_refs_fupd (K (bvlSem_state_refs t2)) t2) =
  (t2:('a,'b)bvlSem_state)`,
  CHEAT_TAC);;

let do_build_const_thm = prove
 (`bvlSem_do_build_const (MAP update_tag parts) (state_refs t2) = (v,rs)
  /\
   state_rel f2 p1 t2 /\ f1 SUBMAP f2 /\
   FDIFF (state_refs t1) (FRANGE f1) SUBMAP FDIFF (state_refs t2)
     (FRANGE f2) ==>
   (?f2'.
     v_rel (closSem_state_max_app p1) f2' rs (state_code t2)
       (build_const' parts) v /\
     state_rel f2' p1 (state_refs_fupd (K rs) t2) /\ f1 SUBMAP f2' /\
     FDIFF (state_refs t1) (FRANGE f1) SUBMAP FDIFF rs (FRANGE
       f2'))`,
  CHEAT_TAC);;

let rel_dest_thunk = prove
 (`state_rel f s t /\
   v_rel (closSem_state_max_app s) f (state_refs t) (state_code t) h
     y /\
   dest_thunk [h] (state_refs s) = IsThunk m r1 ==>
   (?r2.
     dest_thunk y (state_refs t) = IsThunk m r2 /\
     v_rel (closSem_state_max_app s) f (state_refs t) (state_code
       t) r1 r2)`,
  CHEAT_TAC);;

let rel_dest_thunk_NotThunk = prove
 (`state_rel f s t /\
   v_rel (closSem_state_max_app s) f (state_refs t) (state_code t) h
     y /\
   dest_thunk [h] (state_refs s) = NotThunk ==>
     dest_thunk y (state_refs t) = NotThunk`,
  CHEAT_TAC);;

(* compile_exps_correct *)
let clos_to_bvlProof_compile_exps_correct = prove
 (`(!tmp xs env (s1:('c,'ffi)closSem_state) aux1
  (t1:('c,'ffi)bvlSem_state) env' f1 res s2 ys aux2.
     (tmp = (xs,env,s1)) /\
     (evaluate (xs,env,s1) = (res,s2)) /\ ~(res = Rerr (Rabort
       Rtype_error)) /\
     (clos_to_bvl_compile_exps (closSem_state_max_app s1) xs aux1 =
       (ys,aux2)) /\
     every_Fn_SOME xs /\ FEVERY (\p. every_Fn_SOME [SND (SND p)])
       (closSem_state_code s1) /\
     every_Fn_vs_SOME xs /\ FEVERY (\p. every_Fn_vs_SOME [SND (SND
       p)]) (closSem_state_code s1) /\
     clos_to_bvlProof_code_installed aux2 (bvlSem_state_code t1) /\
     env_rel (closSem_state_max_app s1) f1 (bvlSem_state_refs t1)
       (bvlSem_state_code t1) env env' /\
     state_rel f1 s1 t1 ==>
     (?ck res' t2 f2.
        (evaluate (ys,env',bvlSem_state_clock_fupd (K
          (closSem_state_clock s1 + ck)) t1) = (res',t2)) /\
        semanticPrimitivesProps_result_rel (ALL2 (v_rel
          (closSem_state_max_app s1) f2 (state_refs t2) (state_code
          t2))) (v_rel (closSem_state_max_app s1) f2 (state_refs t2)
          (state_code t2)) res res' /\
        state_rel f2 s2 t2 /\
        f1 SUBMAP f2 /\
        (FDIFF (bvlSem_state_refs t1) (FRANGE f1)) SUBMAP (FDIFF
          (state_refs t2) (FRANGE f2)) /\
        FEVERY (\p. every_Fn_SOME [SND (SND p)]) (state_code s2) /\
        FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (state_code s2)
          /\ state_clock
        s2 = state_clock t2)) /\
   (!loc_opt func args (s1:('c,'ffi)closSem_state) res s2 env
     (t1:('c,'ffi)bvlSem_state) args' func' f1.
     evaluate_app loc_opt func args s1 = (res,s2) /\ ~(res = Rerr
       (Rabort Rtype_error)) /\
     FEVERY (\p. every_Fn_SOME [SND (SND p)]) (closSem_state_code s1)
       /\
     FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (closSem_state_code
       s1) /\
     v_rel (closSem_state_max_app s1) f1 (bvlSem_state_refs t1)
       (bvlSem_state_code t1) func func' /\
     ALL2 (v_rel (closSem_state_max_app s1) f1 (bvlSem_state_refs t1)
       (bvlSem_state_code t1)) args args' /\
     state_rel f1 s1 t1 ==>
     (?ck res' t2 f2.
       (~(LENGTH args' = 0) ==>
         (match loc_opt with NONE ->
              evaluate
                    ([mk_cl_call (Var (LENGTH args')) (list_of_seq
                      Var (LENGTH args'))],APPEND (APPEND args' [func'])
                      env,bvlSem_state_clock_fupd (K
                      (closSem_state_clock s1 + ck))
                      t1) =
                (res',t2) | SOME loc ->
               (match find_code (SOME (loc + num_stubs
                 (closSem_state_max_app s1))) (APPEND args' [func'])
                 (bvlSem_state_code t1) with
                     NONE -> (Rerr (Rabort Rtype_error),t2) | SOME
                       (args,exp) ->
                       (if closSem_state_clock s1 + ck < (LENGTH
                         args') then (Rerr (Rabort
                         Rtimeout_error),bvlSem_state_clock_fupd (K 0)
                         t1) else evaluate
                         ([exp],args,bvlSem_state_clock_fupd (K
                         ((closSem_state_clock s1 + ck) - LENGTH args'))
                         t1))) =
                 (res',t2))) /\
       semanticPrimitivesProps_result_rel (ALL2 (v_rel
         (closSem_state_max_app s1) f2 (state_refs t2) (state_code t2)))
         (v_rel (closSem_state_max_app s1) f2 (state_refs t2)
         (state_code t2)) res res' /\
       state_rel f2 s2 t2 /\
       f1 SUBMAP f2 /\
       FDIFF (bvlSem_state_refs t1) (FRANGE f1) SUBMAP FDIFF
         (state_refs t2) (FRANGE f2) /\
       FEVERY (\p. every_Fn_SOME [SND (SND p)]) (state_code s2) /\
       FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (state_code s2) /\
         state_clock
       s2 = state_clock t2))`,
  CHEAT_TAC);;

(* more correctness properties *)

(* [local] *)
let build_aux_thm = prove
 (`!c n aux n7 aux7.
     build_aux n c aux = (n7,APPEND aux7 aux) ==>
     (MAP FST aux7) = (REVERSE (list_of_seq ((+) n o (*) 2) (LENGTH
       c)))`,
  CHEAT_TAC);;

let MEM_build_aux_imp_SND_MEM = prove
 (`!n ls acc m aux x.
    build_aux n ls acc = (m,aux) /\ MEM x aux ==>
     MEM (SND x) ls \/ MEM x acc`,
  CHEAT_TAC);;

(* lemma[local] *)
let clos_to_bvlProof_lemma = prove
 (`clos_to_bvl_compile_exps max_app xs aux = (c,aux1) ==>
   LENGTH c = LENGTH xs /\ (?ys. aux1 = APPEND ys aux)`,
  CHEAT_TAC);;

(* [local] *)
let lemma2 = prove
 (`build_aux n k aux = (a,b) ==>
   (?z. b = APPEND z aux)`,
  CHEAT_TAC);;

let compile_exps_code_locs = prove
 (`!max_app xs aux ys aux2.
    clos_to_bvl_compile_exps max_app xs aux = (ys,APPEND aux2 aux)
      ==>
    MAP FST aux2 = MAP ((+) (num_stubs max_app)) (REVERSE
      (code_locs xs))`,
  CHEAT_TAC);;

let init_code_ok = prove
 (`0 < max_app ==>
   (!n.
      n < max_app ==> sptree_lookup (generic_app_fn_location n)
        (init_code max_app) = SOME (n + 2,generate_generic_app max_app
        n)) /\
   (!tot n.
      tot < max_app /\ n < tot ==>
        sptree_lookup (partial_app_fn_location max_app tot n)
          (init_code max_app) =
          SOME (tot - n + 1,generate_partial_app_closure_fn tot n))`,
  CHEAT_TAC);;

let domain_init_code_lt_num_stubs = prove
 (`!max_app x. x IN domain (init_code max_app) ==> x < (num_stubs
  max_app)`,
  CHEAT_TAC);;

let domain_init_code = prove
 (`0 < max_app ==> domain (init_code max_app) = count (max_app +
  (max_app * (max_app - 1)) DIV 2)`,
  CHEAT_TAC);;

let compile_prog_code_locs = prove
 (`!ls.
   MAP FST (clos_to_bvl_compile_prog max_app ls) = APPEND (MAP ((+)
     (num_stubs max_app) o FST) ls)
   (MAP ((+) (num_stubs max_app)) (REVERSE (code_locs (MAP (SND o
     SND) ls))))`,
  CHEAT_TAC);;

let IMP_PERM_code_merge = prove
 (`!xs ys zs. PERM (APPEND xs ys) zs ==> PERM (code_merge xs ys) zs`,
  CHEAT_TAC);;

let code_split_IMP_PERM = prove
 (`!xs1 xs2 xs3 ts1 ts2.
      code_split xs1 xs2 xs3 = (ts1,ts2) ==>
      PERM (APPEND ts1 ts2) (APPEND (APPEND xs2 xs3) xs1)`,
  CHEAT_TAC);;

let PERM_code_sort = prove
 (`!xs. PERM (code_sort xs) xs`,
  CHEAT_TAC);;

let set_MAP_code_sort = prove
 (`set_of_list (MAP f (code_sort x)) = set_of_list (MAP f x)`,
  CHEAT_TAC);;

let ALL_DISTINCT_code_sort = prove
 (`ALL_DISTINCT (MAP FST (code_sort xs)) <=> ALL_DISTINCT (MAP FST xs)`,
  CHEAT_TAC);;

let PERM_IMP_fromAList_EQ_fromAList = prove
 (`!xs ys.
      PERM xs ys ==> ALL_DISTINCT (MAP FST xs) ==>
      fromAList xs = fromAList ys`,
  CHEAT_TAC);;

let fromAList_code_sort = prove
 (`ALL_DISTINCT (MAP FST xs) ==>
    fromAList (code_sort xs) = fromAList xs`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:5880-5888: code that the source
   has in a comment *)

(* HOL4 clos_to_bvlProofScript.sml:5890: the overload code_loc',
   which the port expands *)

let MAP_FST_chain_exps = prove
 (`!i ls. ~(ls = []) ==> (MAP FST (chain_exps i ls) = MAP ((+) i)
  (COUNT_LIST (LENGTH ls)))`,
  CHEAT_TAC);;

let MAP_FST_chain_exps_any = prove
 (`!i ls. (MAP FST (chain_exps i ls) = MAP ((+) i) (COUNT_LIST (MAX 1
  (LENGTH ls))))`,
  CHEAT_TAC);;

(* [simp] *)
let chain_exps_code_locs = prove
 (`!n es. code_locs (MAP (SND o SND) (chain_exps n es)) = code_locs es`,
  CHEAT_TAC);;

(* [simp] *)
let chain_exps_ALL_DISTINCT = prove
 (`ALL_DISTINCT (MAP FST (chain_exps i ls))`,
  CHEAT_TAC);;

let chain_exps_LE = prove
 (`!n xs. ALL ((<=) n) (MAP FST (chain_exps n xs))`,
  CHEAT_TAC);;

let chain_exps_GT = prove
 (`!n xs. ~(xs = []) ==> ALL ((>) (n + LENGTH xs)) (MAP FST
  (chain_exps n xs))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:5957-5958: ML code, not ported *)

let compile_common_distinct_locs = prove
 (`compile_common c e = (c',p) ==>
   ALL_DISTINCT (APPEND (MAP FST p) (code_locs (MAP (SND o SND)
     p)))`,
  CHEAT_TAC);;

let compile_all_distinct_locs = prove
 (`clos_to_bvl_compile c e = (c',p,n) ==> ALL_DISTINCT (MAP FST p)`,
  CHEAT_TAC);;

(* Initial state *)
let clos_init_def = new_definition
  `clos_init max_app s <=> state_globals
   s = [] /\ state_refs s = FEMPTY /\ state_code s = FEMPTY /\
     closSem_state_max_app s = max_app`;;

(* [simp] *)
let clos_init_with_clock = prove
 (`clos_init max_app (state_clock_fupd (K k) s) <=> clos_init max_app
  s`,
  CHEAT_TAC);;

(* actually, this can be made even stronger *)
(* [local] *)
let code_installed_fromAList_strong = prove
 (`!ls ls'.
   ALL_DISTINCT (MAP FST ls) /\
   IS_SUBLIST ls ls' ==>
   clos_to_bvlProof_code_installed ls' (fromAList ls)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:6106-6124: code that the source
   has in a comment *)

(* [local] *)
let evaluate_init1 = prove
 (`!mapp2 mapp1 tot st.
   (!n. n < mapp2 ==>
   partial_app_fn_location mapp1 tot n IN domain (state_code st)) ==>
   bvlSem_evaluate (REVERSE
   (list_of_seq (\prev. Op (closLang_Label (partial_app_fn_location
     mapp1 tot prev)) []) mapp2),[Unit],st) =
   (Rval (REVERSE
   (list_of_seq (\prev. bvlSem_CodePtr (partial_app_fn_location
     mapp1 tot prev)) mapp2)),st)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_init = prove
 (`!mapp2 mapp1 st.
   (!m n. m < mapp2 /\ n < m ==>
   partial_app_fn_location mapp1 m n IN domain (state_code st)) ==>
   bvlSem_evaluate (REVERSE
   (FLAT (list_of_seq (\tot. list_of_seq
   (\prev. Op (closLang_Label (partial_app_fn_location mapp1 tot
     prev)) []) tot) mapp2)),[Unit],st) =
     (Rval (REVERSE
     (FLAT (list_of_seq (\tot. list_of_seq
     (\prev. bvlSem_CodePtr (partial_app_fn_location mapp1 tot
       prev)) tot) mapp2))),st)`,
  CHEAT_TAC);;

(* FST_EQ_LEMMA[local] *)
let clos_to_bvlProof_FST_EQ_LEMMA = prove
 (`FST x = y <=> (?y1. x = (y,y1))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:6167-6171: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:6173-6177: ML code, not ported *)

let clos_to_bvlProof_eval_sim_def = new_definition
  `clos_to_bvlProof_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2
  start' rel =
     (!k res1 s2.
       evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k) =
         (res1,s2) /\ ~(res1 = Rerr (Rabort Rtype_error)) /\
       rel code1 co1 cc1 es1 code2 co2 cc2 start' ==>
       (?ck res2 t2.
         bvlSem_evaluate ([Call 0 (SOME start') []],[],
           initial_state ffi code2 co2 cc2 (k + ck)) = (res2,t2) /\
         semanticPrimitivesProps_result_rel (\x y. T) (\x y. T)
           res1 res2 /\ state_ffi s2 = state_ffi t2))`;;
hol4_overload "eval_sim" "clos_to_bvlProof_eval_sim";;

(* initial_state_with_clock[local] *)
let clos_to_bvlProof_initial_state_with_clock = prove
 (`(state_clock_fupd (K (state_clock
     (initial_state ffi ma code co cc k) + ck)) (initial_state ffi ma
       code co cc k)) =
   initial_state ffi ma code co cc (k + ck)`,
  CHEAT_TAC);;

(* [local] *)
let initial_state_with_clock_bvl = prove
 (`(state_clock_fupd (K (state_clock
     (initial_state ffi code co cc k) + ck)) (initial_state ffi code
       co cc k)) =
   initial_state ffi code co cc (k + ck) /\
   (bvlProps_inc_clock ck (initial_state ffi code co cc k) =
   initial_state ffi code co cc (k + ck))`,
  CHEAT_TAC);;

(* IMP_semantics_eq *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let clos_to_bvlProof_IMP_semantics_eq = prove
 (cake_as_vars (fun () ->
    `eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 start rel /\
  ~(closSem_semantics (ffi:'ffi ffi_state) max_app code1 co1 cc1 es1 =
  ffi_Fail) ==>
     rel code1 co1 cc1 es1 code2 co2 cc2 start ==>
     bvlSem_semantics ffi code2 co2 cc2 start =
     closSem_semantics ffi max_app code1 co1 cc1 es1`),
  CHEAT_TAC);;

let clos_to_bvlProof_init_code_def = new_definition
  `clos_to_bvlProof_init_code code1 code2 max_app <=>
     (!n.
        n < max_app ==>
        sptree_lookup (generic_app_fn_location n) code2 =
        SOME (n + 2,generate_generic_app max_app n)) /\
     (!tot prev.
        tot < max_app /\ prev < tot ==>
        sptree_lookup (partial_app_fn_location max_app tot prev)
          code2 =
        SOME ((tot + 1) - prev,generate_partial_app_closure_fn tot
          prev)) /\
     (!name arity c.
       FLOOKUP code1 name = SOME (arity,c) ==>
       (?aux1 c2 aux2.
         clos_to_bvl_compile_exps max_app [c] aux1 = ([c2],aux2) /\
         sptree_lookup (name + num_stubs max_app) code2 = SOME
           (arity,c2) /\
         clos_to_bvlProof_code_installed aux2 code2))`;;
hol4_overload "init_code" "clos_to_bvlProof_init_code";;

let chain_installed_def = new_definition
  `chain_installed start' (es:closLang_exp list) code <=>
     (!i. i < LENGTH es ==> closSem_find_code (start' + i)
       ([]:closSem_v list) code =
          SOME ([],(if i + 1 < LENGTH es then Let
            backend_common_None [EL i es] (Call backend_common_None 0
            (start' + i + 1) []) else EL i es)))`;;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let chain_installed_cons = prove
 (cake_as_vars (fun () ->
    `chain_installed start (CONS e es) code <=>
     find_code start ([]:closSem_v list) code = SOME ([],(if es =
       [] then e else Let backend_common_None [e] (Call
       backend_common_None 0 (start + 1) []))) /\
     chain_installed (start + 1) es code`),
  CHEAT_TAC);;

let chain_installed_SUBMAP = prove
 (`!start' es code code'.
   chain_installed start' es code /\ code SUBMAP code' ==>
   chain_installed start' es code'`,
  CHEAT_TAC);;

let chain_installed_thm = prove
 (`!es start'. ?e. !st code res st'.
   chain_installed start' es (state_code st) /\
   closSem_evaluate (es,[],st) = (res,st') /\
   0 < LENGTH es ==>
   (?k res1 st1.
   find_code start' ([]:closSem_v list) (state_code st) = SOME ([],e)
     /\
   closSem_evaluate ([e],[],state_clock_fupd (K (state_clock st + k))
     st) = (res1,st1) /\
   semanticPrimitivesProps_result_rel (\x y. T) (\x y. T) res1 res /\
     state_ffi st' = state_ffi st1)
   // ∧
   // (every_Fn_vs_NONE es ⇒ every_Fn_vs_NONE [e])`,
  CHEAT_TAC);;

let chain_installed_chain_exps = prove
 (`!start' es. chain_installed start' es (alist_to_fmap (chain_exps
  start' es))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let chain_exps_semantics = prove
 (cake_as_vars (fun () ->
    `~(semantics ffi max_app code co cc es = ffi_Fail) /\
      // es ≠ [] ∧
      DISJOINT (IMAGE ((+) start) (count (LENGTH es))) (FDOM code)
        /\
      oracle_monotonic (set_of_list o MAP FST o SND o SND) (<)
           (IMAGE ((+) start) (count (LENGTH es)) UNION FDOM code)
             co ==>
      (?e.
      semantics ffi max_app (FUNION (alist_to_fmap (chain_exps
        start es)) code) co cc [e] =
      semantics ffi max_app code co cc es /\
      ALOOKUP (chain_exps start es) start = SOME (0,e))`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let chain_exps_semantics_call = prove
 (cake_as_vars (fun () ->
    `~(semantics ffi max_app code co cc es = ffi_Fail) /\
      DISJOINT (IMAGE ((+) start) (count (LENGTH es))) (FDOM code)
        /\
      oracle_monotonic (set_of_list o MAP FST o SND o SND) (<)
           (IMAGE ((+) start) (count (LENGTH es)) UNION FDOM code)
             co ==>
      semantics ffi max_app (FUNION (alist_to_fmap (chain_exps
        start es)) code) co cc ([Call backend_common_None 0 start []]) =
      semantics ffi max_app code co cc es`),
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:6572-6630: code that the source
   has in a comment *)

(* TODO: there's lots to move in this file *)

let kcompile_csyntax_ok = prove
 (`clos_known_compile kc es = (x,y) ==>
   clos_callProof_syntax_ok es ==>
    clos_callProof_syntax_ok y`,
  CHEAT_TAC);;

let renumber_code_locs_fv1 = prove
 (`(!n es v. ALL2 (\e1 e2. !v. fv1 v e1 <=> fv1 v e2) (SND
  (renumber_code_locs_list n es)) es) /\
   (!n e v. fv1 v (SND (renumber_code_locs n e)) <=> fv1 v (e))`,
  CHEAT_TAC);;

let renumber_code_locs_list_fv = prove
 (`renumber_code_locs_list n es = (k,es') ==> fv x es' = fv x es`,
  CHEAT_TAC);;

let set_globals_SND_renumber_code_locs = prove
 (`closProps_set_globals (SND (renumber_code_locs x y)) =
  closProps_set_globals y`,
  CHEAT_TAC);;

let elist_globals_FLAT = prove
 (`closProps_elist_globals (FLAT ls) = ITLIST (BAG_UNION) (MAP
  closProps_elist_globals ls) EMPTY_BAG`,
  CHEAT_TAC);;

let elist_globals_SND_renumber_code_locs_list = prove
 (`closProps_elist_globals (SND (renumber_code_locs_list x y)) =
  closProps_elist_globals y`,
  CHEAT_TAC);;

(* [simp] *)
let elist_globals_SND_ncompile_inc = prove
 (`closProps_elist_globals (SND (clos_number_compile_inc x y)) =
  closProps_elist_globals y`,
  CHEAT_TAC);;

let collect_apps_fv1 = prove
 (`!x y z v. fv v (FST (collect_apps x y z)) \/ fv1 v (SND
  (collect_apps x y z)) <=> fv v y \/ fv1 v z`,
  CHEAT_TAC);;

let collect_args_fv1 = prove
 (`!m n e n' e' v.
      (collect_args m n e = (n',e')) ==>
        (fv1 (n' + v) e' <=> fv1 (n + v) e)`,
  CHEAT_TAC);;

let intro_multi_fv1 = prove
 (`!max_app es. ALL2 (\e1 e2. !v. fv1 v e1 <=> fv1 v e2) (intro_multi
  max_app es) es`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:6767-6786: code that the source
   has in a comment *)

let compile_elist_globals = prove
 (`closProps_elist_globals (clos_mti_compile do_mti max_app es) =
  closProps_elist_globals es`,
  CHEAT_TAC);;

let mcompile_inc_uncurry = prove
 (`clos_mti_compile_inc max_app p = ((intro_multi max_app (FST p)),[])`,
  CHEAT_TAC);;

let kcompile_inc_uncurry = prove
 (`clos_known_compile_inc c g p =
     (SND (known (reset_inline_factor c) (FST p) [] g),
      MAP FST (FST (known (reset_inline_factor c) (FST p) [] g)),
      SND p)`,
  CHEAT_TAC);;

let acompile_inc_uncurry = prove
 (`clos_annotate_compile_inc p =
   ((clos_annotate_annotate 0 (FST p)),clos_annotate_compile (SND
     p))`,
  CHEAT_TAC);;

let ccompile_inc_uncurry = prove
 (`clos_call_compile_inc g p =
     (FST (SND (calls (FST p) (g,[]))),
      (FST (calls (FST p) (g,[]))),
      SND (SND (calls (FST p) (g,[]))))`,
  CHEAT_TAC);;

let compile_inc_uncurry = prove
 (`compile_inc max_app p =
    clos_to_bvl_compile_prog max_app (APPEND (chain_exps (FST
      (extract_name (FST p))) (SND (extract_name (FST p)))) (SND p))`,
  CHEAT_TAC);;

let fcompile_inc_uncurry = prove
 (`clos_fvs_compile_inc p = (compile (FST p),[])`,
  CHEAT_TAC);;

let elist_globals_sing = prove
 (`closProps_elist_globals [x] = closProps_set_globals x`,
  CHEAT_TAC);;

let set_globals_HD_intro_multi = prove
 (`closProps_set_globals (HD (intro_multi x [y])) =
  closProps_set_globals y`,
  CHEAT_TAC);;

let renumber_code_locs_list_csyntax_ok = prove
 (`renumber_code_locs_list n es = (k,es') /\
   every_Fn_vs_NONE es ==>
   clos_callProof_syntax_ok es'`,
  CHEAT_TAC);;

(* [simp] *)
let compile_every_Fn_vs_NONE = prove
 (`every_Fn_vs_NONE (clos_mti_compile do_mti max_app es) <=>
   every_Fn_vs_NONE es`,
  CHEAT_TAC);;

let compile_code_locs_ALL_DISTINCT = prove
 (`clos_call_compile do_call es = (xs,g,aux) /\
   ALL_DISTINCT (code_locs es) ==>
   ALL_DISTINCT (APPEND (code_locs xs) (code_locs (MAP (SND o SND)
     aux)))`,
  CHEAT_TAC);;

let chain_exps_every_Fn_vs_NONE = prove
 (`!n xs.
     every_Fn_vs_NONE (MAP (SND o SND) (chain_exps n xs)) <=>
     every_Fn_vs_NONE xs`,
  CHEAT_TAC);;

let calls_compile_csyntax_ok = prove
 (`clos_call_compile p xs = (ys,g,aux) ==>
   clos_callProof_syntax_ok xs ==>
   every_Fn_vs_NONE ys /\
   every_Fn_vs_NONE (MAP (SND o SND) aux)`,
  CHEAT_TAC);;

let HD_FST_calls = prove
 (`[HD (FST (calls [x] y))] = FST (calls [x] y)`,
  CHEAT_TAC);;

let every_Fn_SOME_collect_apps = prove
 (`!max_app es e es' e'.
    collect_apps max_app es e = (es',e') ==>
      (every_Fn_SOME es' /\ every_Fn_SOME [e'] <=>
       every_Fn_SOME es /\ every_Fn_SOME [e])`,
  CHEAT_TAC);;

(* [simp] *)
let every_Fn_SOME_intro_multi = prove
 (`!max_app es. every_Fn_SOME (intro_multi max_app es) <=>
  every_Fn_SOME es`,
  CHEAT_TAC);;

let set_code_locs_collect_apps = prove
 (`!max_app es e es' e'.
    collect_apps max_app es e = (es',e') ==>
      (set_of_list (code_locs [e']) UNION set_of_list (code_locs es')
        =
       set_of_list (code_locs [e]) UNION set_of_list (code_locs
         es))`,
  CHEAT_TAC);;

(* [simp] *)
let every_Fn_SOME_ncompile_inc = prove
 (`every_Fn_SOME (SND (clos_number_compile_inc x y))`,
  CHEAT_TAC);;

(* [simp] *)
let every_Fn_vs_NONE_ncompile_inc = prove
 (`every_Fn_vs_NONE (SND (clos_number_compile_inc x y)) <=>
  every_Fn_vs_NONE y`,
  CHEAT_TAC);;

(* [simp] *)
let ncompile_inc_code_locs_distinct = prove
 (`ALL_DISTINCT (code_locs (SND (clos_number_compile_inc x y)))`,
  CHEAT_TAC);;

(* [simp] *)
let code_locs_FST_letop_compile_inc = prove
 (`code_locs (FST (clos_letop_compile_inc x)) = code_locs (FST x)`,
  CHEAT_TAC);;

(* [simp] *)
let code_locs_FST_ticks_compile_inc = prove
 (`code_locs (FST (clos_ticks_compile_inc x)) = code_locs (FST x)`,
  CHEAT_TAC);;

let code_locs_FST_SND_kcompile_inc = prove
 (`LIST_TO_BAG (code_locs (FST (SND (clos_known_compile_inc x y z)))) <=
   LIST_TO_BAG (code_locs (FST z))`,
  CHEAT_TAC);;

let every_Fn_vs_NONE_cond_call_compile_inc = prove
 (`(
     every_Fn_vs_NONE (FST y) ==> every_Fn_vs_NONE (FST (SND
       (cond_call_compile_inc do_it x y)))) /\
   (
     every_Fn_vs_NONE (FST y) /\ every_Fn_vs_NONE (MAP (SND o SND)
       (SND y)) ==> every_Fn_vs_NONE (MAP (SND o SND) (SND (SND
       (cond_call_compile_inc do_it x y)))))`,
  CHEAT_TAC);;

let every_Fn_SOME_cond_call_compile_inc = prove
 (`(
     every_Fn_SOME (FST y) ==> every_Fn_SOME (FST (SND
       (cond_call_compile_inc do_it x y)))) /\
   (
     every_Fn_SOME (FST y) /\ every_Fn_SOME (MAP (SND o SND) (SND
       y)) ==> every_Fn_SOME (MAP (SND o SND) (SND (SND
       (cond_call_compile_inc do_it x y)))))`,
  CHEAT_TAC);;

let compile_common_inc_def = new_definition
  `compile_common_inc c cc =
   (pure_cc (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
     (clos_to_bvl_config_max_app c))
     (state_cc (ignore_table clos_number_compile_inc)
       (known_cc (clos_to_bvl_config_known_conf c)
         (state_cc (cond_call_compile_inc (clos_to_bvl_config_do_call
           c))
           (pure_cc clos_annotate_compile_inc cc)))))`;;

let clos_state_cc_def = new_definition
  `clos_state_cc inc (cc:'b->closLang_exp list#(num#num#closLang_exp)
  list->(word8 list#word64 list#'b) option) = (state_cc inc
  cc:'a#'b->closLang_exp list#(num#num#closLang_exp) list->(word8
  list#word64 list#'a#'b) option)`;;

let semantics_cond_call_compile_inc = prove
 (`~(semantics ffi max_app FEMPTY co
       (clos_state_cc (cond_call_compile_inc do_call) cc) es =
         ffi_Fail) /\
   clos_call_compile do_call es = (es',g,aux) /\
   code = alist_to_fmap aux /\
   (do_call ==> clos_callProof_syntax_ok es /\
         is_state_oracle clos_call_compile_inc co /\
         g = FST (FST (co 0)) /\
         oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
             (set_of_list (code_locs es)) co /\
         (!k. let (cfg,exp,aux) = co k in
             clos_callProof_syntax_ok exp /\ aux = [])) ==>
   semantics ffi max_app code
       (state_co (cond_call_compile_inc do_call) co) cc es' =
   semantics ffi max_app FEMPTY co
       (clos_state_cc (cond_call_compile_inc do_call) cc) es`,
  CHEAT_TAC);;

let semantics_cond_mti_compile_inc = prove
 (`~(semantics ffi max_app FEMPTY co
           (pure_cc (cond_mti_compile_inc do_mti max_app) cc) xs =
             ffi_Fail) /\
       (do_mti ==>
            (!n. SND (SND (co n)) = [] /\
                ALL no_mti (FST (SND (co n)))) /\
                1 <= max_app /\ ALL no_mti xs) ==>
        semantics ffi max_app FEMPTY
            (pure_co (cond_mti_compile_inc do_mti max_app) o co) cc
            (compile do_mti max_app xs) =
        semantics ffi max_app FEMPTY co
            (pure_cc (cond_mti_compile_inc do_mti max_app) cc) xs`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:7118-7122: the ML values that the
   definitions below antiquote *)

let every_Fn_vs_NONE_known_co = prove
 (`(
     every_Fn_vs_NONE (FST (SND (f n))) /\
       globals_approx_every_Fn_vs_NONE (FST (FST (f n))) ==>
       every_Fn_vs_NONE (FST (SND (known_co conf f n)))) /\
   (every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (f n)))) ==>
       every_Fn_vs_NONE (MAP (SND o SND)
           (SND (SND (known_co conf f n)))))`,
  CHEAT_TAC);;

let every_Fn_SOME_known_co = prove
 (`(
     every_Fn_SOME (FST (SND (f n))) /\ globals_approx_every_Fn_SOME
       (FST (FST (f n))) ==>
       every_Fn_SOME (FST (SND (known_co conf f n)))) /\
   (every_Fn_SOME (MAP (SND o SND) (SND (SND (f n)))) ==>
       every_Fn_SOME (MAP (SND o SND)
           (SND (SND (known_co conf f n)))))`,
  CHEAT_TAC);;

let alist_to_fmap_FEMPTY = prove
 (`ALL_DISTINCT (MAP FST xs) ==> alist_to_fmap xs = FEMPTY |++ xs`,
  CHEAT_TAC);;

(* [local] *)
let obvious_arith_comm = prove
 (`((a:num) = b + a) = (b = 0)`,
  CHEAT_TAC);;

let SND_SND_known_compile_inc = prove
 (`SND (SND (clos_known_compile_inc conf app es)) = SND es`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:7179: the ML values that the
   definitions below antiquote *)

let known_state_oracle_globals_approx = prove
 (`is_state_oracle (clos_known_compile_inc cfg')
       (pure_co (clos_fvs_compile_inc:closLang_exp
         list#(num#num#closLang_exp) list->closLang_exp
         list#(num#num#closLang_exp) list) o co) /\
   FST (FST (co 0)) = spt /\
   known cfg exps [] LN = (k_exps,spt) /\
   every_Fn_vs_NONE exps /\ every_Fn_SOME exps /\
   (!k. every_Fn_vs_NONE (FST (SND (co k))) /\
       every_Fn_SOME (FST (SND (co k)))) ==>
   (!k. globals_approx_every_Fn_vs_NONE (FST (FST (co k))) /\
       globals_approx_every_Fn_SOME (FST (FST (co k))))`,
  CHEAT_TAC);;

let known_co_facts = prove
 (`let co2 = known_co kc co in
   compile kc exps = (kc',exps') ==>
   (IS_SOME kc ==>
       is_state_oracle (clos_known_compile_inc (THE kc))
           (pure_co (clos_fvs_compile_inc:closLang_exp
             list#(num#num#closLang_exp) list->closLang_exp
             list#(num#num#closLang_exp) list) o co) /\
       FST (FST (co 0)) = clos_known_config_val_approx_spt (THE kc')
         /\
       every_Fn_vs_NONE exps /\ every_Fn_SOME exps /\
       (!k. every_Fn_vs_NONE (FST (SND (co k))) /\
           every_Fn_SOME (FST (SND (co k))))) ==>
   (oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
           (set_of_list (code_locs exps)) co ==>
       oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
           (set_of_list (code_locs exps')) co2) /\
   (!k. clos_callProof_syntax_ok (FST (SND (co k))) ==>
       clos_callProof_syntax_ok (FST (SND (co2 k)))) /\
   (!k. SND (SND (co k)) = [] ==> SND (SND (co2 k)) = []) /\
   (!k. (!k. every_Fn_SOME (FST (SND (co k))) /\ SND (SND (co k)) =
     []) ==>
       (every_Fn_SOME (FST (SND (co2 k))) /\
           every_Fn_SOME (MAP (SND o SND) (SND (SND (co2 k))))))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:7285-7293: ML code, not ported *)

let MEM_number_compile_inc_locs = prove
 (`MEM x (code_locs (SND (clos_number_compile_inc n exps))) ==>
   n < x /\ x < FST (clos_number_compile_inc n exps)`,
  CHEAT_TAC);;

let number_oracle_FST_inc = prove
 (`is_state_oracle (ignore_table clos_number_compile_inc) co ==>
   FST (clos_number_compile_inc (FST (FST (co j))) (FST (SND (co
     j)))) =
     FST (FST (co (j + 1)))`,
  CHEAT_TAC);;

let number_oracle_FST_strict_mono = prove
 (`is_state_oracle (ignore_table clos_number_compile_inc) co ==>
   (!j i. i < j ==> FST (FST (co i)) < FST (FST (co j)))`,
  CHEAT_TAC);;

let number_oracle_FST_mono = prove
 (`is_state_oracle (ignore_table clos_number_compile_inc) co ==>
   (!j i. i <= j ==> FST (FST (co i)) <= FST (FST (co j)))`,
  CHEAT_TAC);;

let SND_SND_ignore_table = prove
 (`SND (SND (ignore_table f st p)) = SND p`,
  CHEAT_TAC);;

let FST_SND_ignore_table = prove
 (`FST (SND (ignore_table f st p)) = SND (f st (FST p))`,
  CHEAT_TAC);;

let renumber_code_locs_monotonic = prove
 (`is_state_oracle (ignore_table clos_number_compile_inc) co /\
   FST (FST (co 0)) >= FST (renumber_code_locs_list n exps) ==>
   oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
       (set_of_list (code_locs (SND (renumber_code_locs_list n
         exps))))
       (state_co (ignore_table clos_number_compile_inc) co)`,
  CHEAT_TAC);;

let SND_cond_mti_compile_inc = prove
 (`SND (cond_mti_compile_inc do_it ma v) = (if do_it then [] else SND
  v)`,
  CHEAT_TAC);;

let ccompile_aux_subset = prove
 (`compile (clos_to_bvl_config_do_call c) exps = (exps',g,aux) ==>
   set_of_list (MAP FST aux) SUBSET IMAGE SUC (set_of_list
     (code_locs exps))`,
  CHEAT_TAC);;

let ccompile_locs_subset = prove
 (`compile (clos_to_bvl_config_do_call c) exps = (exps',g,aux) ==>
   set_of_list (code_locs (APPEND exps' (MAP (SND o SND) aux)))
     SUBSET (set_of_list (code_locs exps))`,
  CHEAT_TAC);;

let number_compile_inc_esgc_free = prove
 (`ALL closProps_esgc_free y ==>
   ALL closProps_esgc_free (SND (clos_number_compile_inc x y))`,
  CHEAT_TAC);;

let number_monotonic_elist_globals = prove
 (`oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o SND)
  (<) St co ==>
   oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o
     SND) (<) St
        (state_co (ignore_table clos_number_compile_inc) co)`,
  CHEAT_TAC);;

let cond_mti_monotonic_elist_globals = prove
 (`oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o SND)
  (<)
        (SET_OF_BAG (closProps_elist_globals exps)) co ==>
   oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o
     SND) (<)
        (SET_OF_BAG (closProps_elist_globals (compile do_it ma
          exps)))
        (pure_co (cond_mti_compile_inc do_it ma) o co)`,
  CHEAT_TAC);;

let DISJOINT_LE_GT = prove
 (`(!x. x IN A ==> x <= (n:num)) /\ (!x. x IN B ==> n < x) ==>
   DISJOINT A B`,
  CHEAT_TAC);;

let oracle_monotonic_init_subset = prove
 (`oracle_monotonic f R St co /\ St' SUBSET St ==>
   oracle_monotonic f R St' co`,
  CHEAT_TAC);;

let compile_inc_post_kcompile_def = new_definition
  `compile_inc_post_kcompile c exps = compile
  (clos_to_bvl_config_known_conf c)
     (SND (renumber_code_locs_list
         (make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH
           exps)))
         (compile (clos_to_bvl_config_do_mti c)
           (clos_to_bvl_config_max_app c) exps)))`;;

(* HOL4 clos_to_bvlProofScript.sml:7489-7491: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:7493-7496: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:7498: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:7500: the ML values that the
   definitions below antiquote *)

let FST_known_co = prove
 (`FST (known_co kc co n) = SND (FST (co n))`,
  CHEAT_TAC);;

let compile_common_semantics = prove
 (`~(closSem_semantics (ffi:'ffi ffi_state) (clos_to_bvl_config_max_app
  c) FEMPTY co1
    (compile_common_inc c cc) es1 = ffi_Fail) /\
   compile_common c es1 = (c',code2) /\
   (!n. SND (SND (co1 n)) = []) /\
   (clos_to_bvl_config_do_mti c ==> 1 <= clos_to_bvl_config_max_app c
     /\ ALL no_mti es1 /\
     (!n. ALL no_mti (FST (SND (co1 n))))) /\
   (clos_to_bvl_config_do_call c ==> every_Fn_vs_NONE es1 /\
       is_state_oracle clos_call_compile_inc
           (known_co (clos_to_bvl_config_known_conf c)
               (state_co (ignore_table clos_number_compile_inc)
                   (pure_co (cond_mti_compile_inc
                     (clos_to_bvl_config_do_mti c)
                     (clos_to_bvl_config_max_app c)) o co1))) /\
       FST (SND (SND (FST (co1 0)))) = FST (SND (compile
         (clos_to_bvl_config_do_call c) (SND
           (compile_inc_post_kcompile c es1))))) /\
   (IS_SOME (clos_to_bvl_config_known_conf c) ==>
       1 <= clos_to_bvl_config_max_app c /\
       oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o
         SND) (<)
           (SET_OF_BAG (closProps_elist_globals es1)) co1 /\
       is_state_oracle (clos_known_compile_inc (THE
         (clos_to_bvl_config_known_conf c)))
           (pure_co (clos_fvs_compile_inc:closLang_exp
             list#(num#num#closLang_exp) list->closLang_exp
             list#(num#num#closLang_exp) list) o
               state_co (ignore_table clos_number_compile_inc)
                   (pure_co (cond_mti_compile_inc
                     (clos_to_bvl_config_do_mti c)
                     (clos_to_bvl_config_max_app c)) o co1)) /\
       FST (SND (FST (co1 0))) = clos_known_config_val_approx_spt
           (THE (FST (compile_inc_post_kcompile c es1))) /\
       (!n'. BAG_ALL_DISTINCT (closProps_elist_globals (FST (SND (co1
         n')))) /\
               ALL closProps_esgc_free (FST (SND (co1 n'))))) /\
   ~(contains_App_SOME (clos_to_bvl_config_max_app c) es1) /\
     clos_knownProof_syntax_ok es1 /\
   (!n. ~(contains_App_SOME (clos_to_bvl_config_max_app c) (FST (SND
     (co1 n)))) /\
           every_Fn_vs_NONE (FST (SND (co1 n)))) /\
   is_state_oracle (ignore_table clos_number_compile_inc)
       (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
         (clos_to_bvl_config_max_app c)) o co1) /\
   FST (FST (co1 0)) >= FST (renumber_code_locs_list (make_even
       (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH es1))) (compile
         (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c)
         es1)) /\
   oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (count
     (FST (FST (co1 0))))
      (state_co (cond_call_compile_inc (clos_to_bvl_config_do_call
        c))
         (known_co (clos_to_bvl_config_known_conf c)
            (state_co (ignore_table clos_number_compile_inc)
               (pure_co (cond_mti_compile_inc
                 (clos_to_bvl_config_do_mti c)
                 (clos_to_bvl_config_max_app c)) o co1)))) ==>
   closSem_semantics ffi (clos_to_bvl_config_max_app c)
     (alist_to_fmap code2)
     (pure_co clos_annotate_compile_inc o
       state_co (cond_call_compile_inc (clos_to_bvl_config_do_call
         c))
       (known_co (clos_to_bvl_config_known_conf c)
           (state_co (ignore_table clos_number_compile_inc)
             (pure_co (cond_mti_compile_inc
               (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app
               c)) o co1))))
     cc ([Call backend_common_None 0 (clos_to_bvl_config_start c')
       []]) =
   closSem_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY co1
     (compile_common_inc c cc) es1`,
  CHEAT_TAC);;

(* [local,simp] *)
let REPLICATE_1 = prove
 (`REPLICATE 1 x = [x]`,
  CHEAT_TAC);;

(* compile_prog_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let clos_to_bvlProof_compile_prog_semantics = prove
 (cake_as_vars (fun () ->
    `~(semantics (ffi:'ffi ffi_state) max_app code1 co1 cc1 [Call
  backend_common_None 0 start []] = ffi_Fail) /\
     (!name arity c.
       FLOOKUP code1 name = SOME (arity,c) ==>
       (?aux1 c2 aux2.
         clos_to_bvl_compile_exps max_app [c] aux1 = ([c2],aux2) /\
         sptree_lookup (name + num_stubs max_app) code2 = SOME
           (arity,c2) /\
         clos_to_bvlProof_code_installed aux2 code2)) /\
     clos_to_bvl_compile_prog max_app prog1 = prog2 /\
     init_code code1 code2 max_app /\
     FEVERY (\p. every_Fn_SOME [SND (SND p)]) code1 /\
     FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) code1 /\
     sptree_lookup nsm1 code2 = SOME (0,init_globals max_app
       (num_stubs max_app + start)) /\
     sptree_lookup (num_stubs max_app - 2) code2 = SOME
       (2,force_thunk_code) /\
     compile_oracle_inv max_app code1 cc1 co1 code2 cc2 co2 /\
     clos_to_bvlProof_code_installed prog2 code2 ==>
     bvlSem_semantics ffi code2 (co2:num->'c#(num#num#bvl_exp)
       list) cc2 nsm1 =
     closSem_semantics ffi max_app code1
       (co1:num->'c#closLang_exp list#(num#num#closLang_exp) list) cc1
       [Call backend_common_None 0 start []]`),
  CHEAT_TAC);;

let clos_to_bvlProof_syntax_oracle_ok_def = assume_definition
  "free: known_co:(clos_known_config)option->(num->((val_approx"
  [`clos_to_bvlProof_syntax_oracle_ok c c' es co <=>
    (!n. SND (SND (co n)) = []) /\
    (clos_to_bvl_config_do_mti c ==> 1 <= clos_to_bvl_config_max_app
      c /\ ALL no_mti es /\
      (!n. ALL no_mti (FST (SND (co n))))) /\
    (?v. FST (co 0) = (clos_to_bvl_config_next_loc c',
        option_val_approx_spt (clos_to_bvl_config_known_conf c'),FST
          (clos_to_bvl_config_call_state c'),v)) /\
    (clos_to_bvl_config_do_call c ==> every_Fn_vs_NONE es /\
        is_state_oracle clos_call_compile_inc
            (known_co (clos_to_bvl_config_known_conf c)
                (state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc
                      (clos_to_bvl_config_do_mti c)
                      (clos_to_bvl_config_max_app c)) o co)))) /\
    (IS_SOME (clos_to_bvl_config_known_conf c) ==>
        1 <= clos_to_bvl_config_max_app c /\ every_Fn_vs_NONE es /\
        oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST
          o SND) (<)
            (SET_OF_BAG (closProps_elist_globals es)) co /\
        is_state_oracle (clos_known_compile_inc (THE
          (clos_to_bvl_config_known_conf c)))
            (pure_co (clos_fvs_compile_inc:closLang_exp
              list#(num#num#closLang_exp) list->closLang_exp
              list#(num#num#closLang_exp) list) o
                state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc
                      (clos_to_bvl_config_do_mti c)
                      (clos_to_bvl_config_max_app c)) o co)) /\
        (!n'. BAG_ALL_DISTINCT (closProps_elist_globals (FST (SND
          (co n')))) /\
                ALL closProps_esgc_free (FST (SND (co n'))))) /\
    ~(contains_App_SOME (clos_to_bvl_config_max_app c) es) /\
      clos_knownProof_syntax_ok es /\
    (!n. ~(contains_App_SOME (clos_to_bvl_config_max_app c) (FST
      (SND (co n)))) /\
            every_Fn_vs_NONE (FST (SND (co n)))) /\
    is_state_oracle (ignore_table clos_number_compile_inc)
        (pure_co (cond_mti_compile_inc
          (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app
          c)) o co)`];;
hol4_overload "syntax_oracle_ok" "clos_to_bvlProof_syntax_oracle_ok";;

let compile_exps_IMP_acc = prove
 (`clos_to_bvl_compile_exps max_app xs aux = (c,aux1) ==>
   LENGTH c = LENGTH xs /\ (?ys. aux1 = APPEND ys aux)`,
  CHEAT_TAC);;

let build_aux_append_aux = prove
 (`!xs n aux aux_extra. build_aux n xs (APPEND aux aux_extra) =
     ((\(ys,aux2). (ys,APPEND aux2 aux_extra)) (build_aux n xs
       aux))`,
  CHEAT_TAC);;

let compile_exps_append_aux = prove
 (`!max_app xs aux. clos_to_bvl_compile_exps max_app xs (APPEND aux
  aux_extra) =
     ((\(ys,aux2). (ys,APPEND aux2 aux_extra))
       (clos_to_bvl_compile_exps max_app xs aux))`,
  CHEAT_TAC);;

let compile_exps_eq_append = prove
 (`clos_to_bvl_compile_exps max_app xs aux =
     ((\(ys,aux2). (ys,APPEND aux2 aux)) (I
       clos_to_bvl_compile_exps max_app xs []))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:7836-7837: ML code, not ported *)

let extract_name_code_locs = prove
 (`extract_name exps = (n,real_es) ==>
   code_locs real_es = code_locs exps`,
  CHEAT_TAC);;

let extracted_addrs_def = new_definition
  `extracted_addrs exps = (if exps = [] then [0] else (match
  extract_name exps with
         (n,real_es) -> MAP ((+) n) (COUNT_LIST (MAX 1 (LENGTH
           real_es)))))`;;

let req_compile_inc_addrs_def = new_definition
  `req_compile_inc_addrs extra (exps,code) = APPEND (APPEND (APPEND
  (APPEND (extracted_addrs exps)
     (code_locs exps)) (MAP FST code)) (code_locs (MAP (SND o SND)
       code)))
     (FLAT (MAP (\f. MAP f (code_locs exps)) extra))`;;

let can_extract_def = new_definition
  `can_extract exps = (?t n exps'.
         exps = CONS (Op t (closLang_IntOp (closLang_Const (&n)))
           []) exps')`;;

let extract_name_MAP_FST_addrs = prove
 (`extract_name exps = (n,real_es) ==>
   MAP FST (chain_exps n real_es) = extracted_addrs exps`,
  CHEAT_TAC);;

let compile_inc_req_addrs = prove
 (`(ALL_DISTINCT (req_compile_inc_addrs [] prog) ==>
     ALL_DISTINCT (MAP FST (compile_inc max_app prog))) /\
   (set_of_list (MAP FST (compile_inc max_app prog)) SUBSET
     set_of_list (MAP ((+) (num_stubs max_app))
       (req_compile_inc_addrs [] prog)))`,
  CHEAT_TAC);;

let compile_inc_monotonic = prove
 (`oracle_monotonic (set_of_list o
         MAP ((+) (num_stubs max_app)) o req_compile_inc_addrs [] o
           SND) (<) St co ==>
   oracle_monotonic (set_of_list o MAP FST o SND) (<) St
     (pure_co (compile_inc max_app) o co)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:7921-7922: a theorem that HOL4
   states as the value of an ML expression: code_locs_Op_cons *)

let EXISTS_CONS_NOT_NULL = prove
 (`(?x xs. ys = CONS x xs) = (~(NULL ys))`,
  CHEAT_TAC);;

let can_extract_to_case = prove
 (`can_extract exps ==>
     (?t n. exps = [Op t (closLang_IntOp (closLang_Const (&n)))
       []]) \/ (?t n exp exps'. exps = CONS (Op t (closLang_IntOp
       (closLang_Const (&n))) []) (CONS exp exps'))`,
  CHEAT_TAC);;

(* [local] *)
let show_SUBSET = prove
 (`(!x. x IN s ==> x IN t) ==> s SUBSET t`,
  CHEAT_TAC);;

let trivia_1 = prove
 (`COUNT_LIST 1 = [0] /\ MAX 1 (SUC x) = SUC x /\
   LENGTH (if xs = [] then [v] else xs) = MAX 1 (LENGTH xs)`,
  CHEAT_TAC);;

let subset_req_orac_to_oracle = prove
 (`!orac1 orac2 xs1.
     (!n.
         set_of_list (req_compile_inc_addrs xs2 (SND (orac2 n)))
           SUBSET set_of_list (req_compile_inc_addrs xs1 (SND (orac1
           n)))) /\
   oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs xs1
     o SND) R St orac1 ==>
   oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs
     xs2 o SND) R St orac2`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:7965-7972: ML code, not ported *)

let annotate_compile_code_locs = prove
 (`set_of_list (code_locs (MAP (SND o SND) (clos_annotate_compile xs)))
  SUBSET
     set_of_list (code_locs (MAP (SND o SND) xs)) /\
   (ALL_DISTINCT (code_locs (MAP (SND o SND) xs)) ==>
     ALL_DISTINCT (code_locs (MAP (SND o SND)
       (clos_annotate_compile xs))))`,
  CHEAT_TAC);;

let LENGTH_annotate = prove
 (`LENGTH (clos_annotate_annotate i xs) = LENGTH xs`,
  CHEAT_TAC);;

let annotate_Op_Const = prove
 (`clos_annotate_annotate m (CONS (Op t (closLang_IntOp
  (closLang_Const n)) []:closLang_exp) ls) = CONS (Op t
  (closLang_IntOp (closLang_Const n)) []:closLang_exp)
  (clos_annotate_annotate m ls)`,
  CHEAT_TAC);;

let annotate_compile_inc_req = prove
 (`can_extract (FST prog) ==>
   (ALL_DISTINCT (req_compile_inc_addrs [] prog) ==>
     ALL_DISTINCT (req_compile_inc_addrs []
         (clos_annotate_compile_inc prog))) /\
   can_extract (FST (clos_annotate_compile_inc prog)) /\
   set_of_list (req_compile_inc_addrs [] (clos_annotate_compile_inc
     prog)) SUBSET
     set_of_list (req_compile_inc_addrs [] prog)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:8035-8036: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8038-8039: ML code, not ported *)

let annotate_compile_every_Fn_vs_SOME = prove
 (`every_Fn_vs_SOME (MAP (SND o SND) (clos_annotate_compile es))`,
  CHEAT_TAC);;

let cond_call_compile_inc_req = prove
 (`can_extract (FST prog) ==>
   (ALL_DISTINCT (req_compile_inc_addrs [SUC] prog) ==>
     ALL_DISTINCT (req_compile_inc_addrs []
         (SND (cond_call_compile_inc dc cfg prog)))) /\
   can_extract (FST (SND (cond_call_compile_inc dc cfg prog))) /\
   set_of_list (req_compile_inc_addrs [] (SND (cond_call_compile_inc
     dc cfg prog))) SUBSET
     set_of_list (req_compile_inc_addrs [SUC] prog)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:8092-8093: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8095-8096: ML code, not ported *)

let known_Op_Const = prove
 (`known a (CONS (Op tv (closLang_IntOp (closLang_Const (&n)))
  []:closLang_exp) b) c d =
   ((CONS ((Op tv (closLang_IntOp (closLang_Const (&n)))
     []:closLang_exp),Int (&n))) ## I) (known a b c d)`,
  CHEAT_TAC);;

let BAG_IMAGE_SUB_BAG = prove
 (`x <= y /\ FINITE_BAG x /\ FINITE_BAG y ==>
     BAG_IMAGE f x <= BAG_IMAGE f y`,
  CHEAT_TAC);;

let BAG_UNION_MONO = prove
 (`a <= b /\ c <= d ==> (BAG_UNION) a c <= (BAG_UNION) b d`,
  CHEAT_TAC);;

let remove_ticks_Op_Const = prove
 (`clos_ticks_remove_ticks (CONS (Op t (closLang_IntOp (closLang_Const
  (&n))) []:closLang_exp) ls) = CONS ((Op t (closLang_IntOp
  (closLang_Const (&n))) []:closLang_exp)) (clos_ticks_remove_ticks
  ls)`,
  CHEAT_TAC);;

let let_op_Op_Const = prove
 (`clos_letop_let_op (CONS (Op t (closLang_IntOp (closLang_Const
  (&n))) []:closLang_exp) ls) = CONS ((Op t (closLang_IntOp
  (closLang_Const (&n))) []:closLang_exp)) (clos_letop_let_op ls)`,
  CHEAT_TAC);;

let known_co_req = prove
 (`can_extract (FST (SND (orac n))) ==>
   (ALL_DISTINCT (req_compile_inc_addrs [SUC] (SND (orac n))) ==>
     ALL_DISTINCT (req_compile_inc_addrs [SUC]
         (SND (known_co kc orac n)))) /\
   can_extract (FST (SND (known_co kc orac n))) /\
   set_of_list (req_compile_inc_addrs [SUC] (SND (known_co kc orac
     n))) SUBSET
     set_of_list (req_compile_inc_addrs [SUC] (SND (orac n)))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:8229-8230: ML code, not ported *)

(* HOL4 clos_to_bvlProofScript.sml:8232-8233: ML code, not ported *)

let number_compile_inc_req = prove
 (`let nprog = SND (ignore_table clos_number_compile_inc n prog) in
   SND prog = [] ==>
   ALL_DISTINCT (req_compile_inc_addrs [SUC] nprog) /\
   SND nprog = [] /\ can_extract (FST nprog)`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:8270-8272: ML code, not ported *)

let MEM_number_req = prove
 (`MEM x (req_compile_inc_addrs [SUC]
     (SND (ignore_table clos_number_compile_inc n prog))) /\
   SND prog = [] ==>
   n <= x /\ x < FST (clos_number_compile_inc n (FST prog))`,
  CHEAT_TAC);;

let renumber_code_locs_monotonic_req = prove
 (`is_state_oracle (ignore_table clos_number_compile_inc) co /\
   (!x. x IN St ==> FST (FST (co 0)) + offs > x) /\
   (!n. SND (SND (co n)) = []) ==>
   oracle_monotonic (set_of_list o MAP ((+) offs) o
     req_compile_inc_addrs [SUC] o SND)
       (<) St (state_co (ignore_table clos_number_compile_inc) co)`,
  CHEAT_TAC);;

let domain_nth_code = prove
 (`!n orac. domain (nth_code orac n) = UNIONS
     (set_of_list (MAP (set_of_list o MAP FST o SND o orac)
       (COUNT_LIST n)))`,
  CHEAT_TAC);;

let DISJOINT_nth_code_monotonic = prove
 (`oracle_monotonic (set_of_list o MAP FST o SND) (<) (domain init) orac
  /\
     v = SND (orac n) ==>
   DISJOINT (domain (sptree_union init (nth_code orac n)))
     (set_of_list (MAP FST v))`,
  CHEAT_TAC);;

let UNCURRY_EQ = prove
 (`UNCURRY f = (\x. f (FST x) (SND x))`,
  CHEAT_TAC);;

let LENGTH_FST_cond_mti_compile_inc = prove
 (`LENGTH (FST (cond_mti_compile_inc do_it ma prog)) = LENGTH (FST
  prog)`,
  CHEAT_TAC);;

let every_Fn_vs_NONE_cond_mti_compile_inc = prove
 (`every_Fn_vs_NONE (FST (cond_mti_compile_inc do_it ma prog)) =
     every_Fn_vs_NONE (FST prog)`,
  CHEAT_TAC);;

(* MAP_FST_compile_prog *)
let clos_to_bvlProof_MAP_FST_compile_prog = prove
 (`MAP FST (clos_to_bvl_compile_prog max_app ls) =
    MAP (((+) (num_stubs max_app)))
      (APPEND (MAP FST ls) (REVERSE (code_locs (MAP (SND o SND)
        ls))))`,
  CHEAT_TAC);;

let IMAGE_ADD_SUBSET_count = prove
 (`A SUBSET count (n - m) ==> IMAGE ((+) m) A SUBSET count n`,
  CHEAT_TAC);;

let compile_common_MAP_FST_compile_prog = prove
 (`compile_common c es = (c',p) ==>
   set_of_list (MAP FST (clos_to_bvl_compile_prog
     (clos_to_bvl_config_max_app c) p)) SUBSET
     count (clos_to_bvl_config_next_loc c' + num_stubs
       (clos_to_bvl_config_max_app c))`,
  CHEAT_TAC);;

(* HOL4 clos_to_bvlProofScript.sml:8476-8483: ML code, not ported *)

let syntax_oracle_ok_to_oracle_inv = prove
 (`!cc es co c c'. syntax_oracle_ok c c' es co /\
     compile_common c es = (c',prog') ==>
   (let co' = pure_co clos_annotate_compile_inc o
         state_co (cond_call_compile_inc (clos_to_bvl_config_do_call
           c))
           (known_co (clos_to_bvl_config_known_conf c)
              (state_co (ignore_table clos_number_compile_inc)
                 (pure_co (cond_mti_compile_inc
                   (clos_to_bvl_config_do_mti c)
                   (clos_to_bvl_config_max_app c)) o co))) in
   compile_oracle_inv (clos_to_bvl_config_max_app c) (alist_to_fmap
     prog')
     (pure_cc (compile_inc (clos_to_bvl_config_max_app c)) cc) co'
     (fromAList
        (APPEND (APPEND (toAList (init_code
          (clos_to_bvl_config_max_app c)))
         [(num_stubs (clos_to_bvl_config_max_app c) -
           2,2,force_thunk_code);
          (num_stubs (clos_to_bvl_config_max_app c) - 1,0,
           init_globals (clos_to_bvl_config_max_app c)
             (clos_to_bvl_config_start c'' + num_stubs
             (clos_to_bvl_config_max_app c)))])
         (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c)
           prog'))) cc
     (pure_co (compile_inc (clos_to_bvl_config_max_app c)) o co'))`,
  CHEAT_TAC);;

let compile_every_Fn_SOME = prove
 (`every_Fn_SOME (MAP (SND o SND) es) ==>
   every_Fn_SOME (MAP (SND o SND) (clos_annotate_compile es))`,
  CHEAT_TAC);;

let compile_common_max_app = prove
 (`compile_common c es = (c',es') ==> clos_to_bvl_config_max_app c' =
  clos_to_bvl_config_max_app c`,
  CHEAT_TAC);;

let chain_exps_every_Fn_SOME = prove
 (`!x y. every_Fn_SOME (MAP (SND o SND) (chain_exps x y)) <=>
  every_Fn_SOME y`,
  CHEAT_TAC);;

let chain_exps_every_Fn_vs_SOME = prove
 (`!x y. every_Fn_vs_SOME (MAP (SND o SND) (chain_exps x y)) <=>
  every_Fn_vs_SOME y`,
  CHEAT_TAC);;

let ccompile_every_Fn_SOME = prove
 (`every_Fn_SOME es /\
   clos_call_compile do_call es = (es',g,aux) ==>
   every_Fn_SOME es' /\
   every_Fn_SOME (MAP (SND o SND) aux)`,
  CHEAT_TAC);;

(* TODO: move *)
(* [local] *)
let ALOOKUP_lemma = prove
 (`!l1 l2 n k v.
     (EL n l1 = (k,v)) /\
     ALL_DISTINCT (MAP FST l1) /\
     n < LENGTH l1 /\ LENGTH l2 = LENGTH l1 ==>
   ALOOKUP (MAP2 (\(loc,args,_13) exp. (loc + (m:num),args,exp)) l1
     l2) (k + m) = SOME (FST v,EL n l2)`,
  CHEAT_TAC);;

let ALOOKUP_compile_common = prove
 (`compile_common c es = (c',prog) /\
   ALOOKUP prog name = SOME (arity,exp) ==>
   (?aux1 exp2 aux2.
     clos_to_bvl_compile_exps (clos_to_bvl_config_max_app c) [exp]
       aux1 = ([exp2],aux2) /\
     ALOOKUP (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c)
       prog) (name + num_stubs (clos_to_bvl_config_max_app c)) =
       SOME (arity,exp2) /\
     clos_to_bvlProof_code_installed aux2 (fromAList
       (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c)
       prog)))`,
  CHEAT_TAC);;

let set_code_locs_FST_calls_SUBSET = prove
 (`!x y. set_of_list (code_locs (FST (calls x y))) SUBSET
         set_of_list (code_locs x) UNION set_of_list (code_locs
           (MAP (SND o SND) (SND y)))`,
  CHEAT_TAC);;

let renumber_code_locs_sing = prove
 (`(!n es n' es'.
      LENGTH es = 1 ==>
      (renumber_code_locs_list n es = (n',es') <=>
       LENGTH es' = 1 /\
       renumber_code_locs n (HD es) = (n',HD es'))) /\
   (!n e n' e'.
     renumber_code_locs n e = (n',e') <=>
     renumber_code_locs_list n [e] = (n',[e']))`,
  CHEAT_TAC);;

let MAP_FST_compile_inc = prove
 (`MAP FST (compile_inc max_app p) =
    MAP ((+) (num_stubs max_app))
      (
      APPEND (APPEND (MAP ((+) (FST (extract_name (FST p))))
        (COUNT_LIST (MAX 1 (LENGTH (SND (extract_name (FST p)))))))
          (MAP FST (SND p))) (REVERSE
          (code_locs
            (MAP (SND o SND)
              (APPEND (chain_exps (FST (extract_name (FST p)))
                (SND (extract_name (FST p)))) (SND p))))))`,
  CHEAT_TAC);;

let mcompile_inc_nil = prove
 (`(FST p = [] ==> (clos_mti_compile_inc max_app p = ([],[]))) /\
   (~(FST p = []) ==> ~(FST (clos_mti_compile_inc max_app p) = []))`,
  CHEAT_TAC);;

let renumber_code_locs_list_nil = prove
 (`((xs = []) ==> (SND (renumber_code_locs_list n xs) = [])) /\
   ((~(xs = [])) ==> (~(SND (renumber_code_locs_list n xs) = [])))`,
  CHEAT_TAC);;

let calls_nil = prove
 (`((xs = []) ==> ((calls xs p) = ([],p))) /\
   ((~(xs = [])) ==> (~(FST (calls xs p) = [])))`,
  CHEAT_TAC);;

let annotate_nil = prove
 (`((xs = []) ==> (clos_annotate_annotate n xs = [])) /\
   ((~(xs = [])) ==> (~(clos_annotate_annotate n xs = [])))`,
  CHEAT_TAC);;

let let_op_nil = prove
 (`((xs = []) ==> (clos_letop_let_op xs = [])) /\
   ((~(xs = [])) ==> (~(clos_letop_let_op xs = [])))`,
  CHEAT_TAC);;

let remove_ticks_nil = prove
 (`((xs = []) ==> (clos_ticks_remove_ticks xs = [])) /\
   ((~(xs = [])) ==> (~(clos_ticks_remove_ticks xs = [])))`,
  CHEAT_TAC);;

let known_nil = prove
 (`((b = []) ==> (FST (known a b c d) = [])) /\
   ((~(b = [])) ==> (~(FST (known a b c d) = [])))`,
  CHEAT_TAC);;

let ignore_table_uncurry = prove
 (`ignore_table f st p = (FST (f st (FST p)),(SND (f st (FST p))),SND
  p)`,
  CHEAT_TAC);;

let LENGTH_FST_calls = prove
 (`LENGTH (FST (calls xs g0)) = LENGTH xs`,
  CHEAT_TAC);;

let syntax_oracle_ok_call_FST_monotonic = prove
 (`syntax_oracle_ok c c' es co /\
   compile_common c es = (c',prog') ==>
   oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (count
     (FST (FST (co 0))))
      (state_co (cond_call_compile_inc (clos_to_bvl_config_do_call
        c))
         (known_co (clos_to_bvl_config_known_conf c)
            (state_co (ignore_table clos_number_compile_inc)
               (pure_co (cond_mti_compile_inc
                 (clos_to_bvl_config_do_mti c)
                 (clos_to_bvl_config_max_app c)) o co))))`,
  CHEAT_TAC);;

let syntax_oracle_ok_start = prove
 (`syntax_oracle_ok c (clos_to_bvl_config_start_fupd f c') es co =
   syntax_oracle_ok c c' es co`,
  CHEAT_TAC);;

(* compile_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let clos_to_bvlProof_compile_semantics = prove
 (cake_as_vars (fun () ->
    `~(semantics (ffi:'ffi ffi_state) (clos_to_bvl_config_max_app c)
  FEMPTY co
       (compile_common_inc c (pure_cc (compile_inc
         (clos_to_bvl_config_max_app c)) cc)) es = ffi_Fail) /\
     compile c es = (c',prog,names) /\
     syntax_oracle_ok c c' es co ==>
     semantics ffi (fromAList prog)
       (pure_co (compile_inc (clos_to_bvl_config_max_app c)) o
        pure_co clos_annotate_compile_inc o
        state_co (cond_call_compile_inc (clos_to_bvl_config_do_call
          c))
          (known_co (clos_to_bvl_config_known_conf c)
            (state_co (ignore_table clos_number_compile_inc)
              (pure_co (cond_mti_compile_inc
                (clos_to_bvl_config_do_mti c)
                (clos_to_bvl_config_max_app c)) o co))))
         cc (clos_to_bvl_config_start c') =
     semantics ffi (clos_to_bvl_config_max_app c) FEMPTY co
       (compile_common_inc c (pure_cc (compile_inc
         (clos_to_bvl_config_max_app c)) cc)) es`),
  CHEAT_TAC);;

let compile_inc_phases_all_distinct = prove
 (`SND (SND (orac i)) = [] ==>
   ALL_DISTINCT (MAP FST (clos_to_bvl_compile_inc' max_app
     (clos_annotate_compile_inc
       (SND (cond_call_compile_inc dc c_st
         (SND (known_co kc
           (state_co (ignore_table clos_number_compile_inc) orac)
             i)))))))`,
  CHEAT_TAC);;

let syntax_oracle_ok_bvl_FST_monotonic = prove
 (`syntax_oracle_ok c c' es co /\
   compile c es = (c',prog') ==>
   oracle_monotonic (set_of_list o MAP FST o SND) (<)
      (count (FST (FST (co 0)) + num_stubs
        (clos_to_bvl_config_max_app c)))
      (pure_co (compile_inc (clos_to_bvl_config_max_app c)) o
       pure_co clos_annotate_compile_inc o
       (state_co (cond_call_compile_inc (clos_to_bvl_config_do_call
         c))
         (known_co (clos_to_bvl_config_known_conf c)
            (state_co (ignore_table clos_number_compile_inc)
               (pure_co (cond_mti_compile_inc
                 (clos_to_bvl_config_do_mti c)
                 (clos_to_bvl_config_max_app c)) o co)))))`,
  CHEAT_TAC);;

let assign_get_code_label_compile_op = prove
 (`assign_get_code_label (clos_to_bvl_compile_op op) = (match some
  (\n. op = closLang_Label n) with SOME n -> {n} | _14 -> {})`,
  CHEAT_TAC);;

let recc_Lets_code_labels = prove
 (`!n nargs k rest. get_code_labels (recc_Lets n nargs k rest) =
   IMAGE (\j. n + 2 * j) (count k) UNION get_code_labels rest`,
  CHEAT_TAC);;

let compile_exps_code_labels = prove
 (`!app es1 aux1 es2 aux2.
     clos_to_bvl_compile_exps app es1 aux1 = (es2,aux2) /\
     ALL no_Labels es1 /\ 0 < app /\ ALL (obeys_max_app app) es1 /\
       every_Fn_SOME es1 ==>
     UNIONS (set_of_list (MAP get_code_labels es2)) UNION
     UNIONS (set_of_list (MAP (get_code_labels o SND o SND) aux2))
       SUBSET
     IMAGE (((+) (num_stubs app))) (UNIONS (set_of_list (MAP
       get_code_labels es1))) UNION
     UNIONS (set_of_list (MAP (get_code_labels o SND o SND) aux1))
       UNION
     domain (init_code app) UNION {num_stubs app - 2}`,
  CHEAT_TAC);;

(* compile_prog_code_labels *)
let clos_to_bvlProof_compile_prog_code_labels = prove
 (`0 < max_app /\
   ALL no_Labels (MAP (SND o SND) prog) /\
   ALL (obeys_max_app max_app) (MAP (SND o SND) prog) /\
   every_Fn_SOME (MAP (SND o SND) prog) ==>
   UNIONS (set_of_list (MAP (get_code_labels o SND o SND)
                   (clos_to_bvl_compile_prog max_app prog))) SUBSET
   IMAGE (((+) (num_stubs max_app))) (UNIONS (set_of_list (MAP
     get_code_labels (MAP (SND o SND) prog)))) UNION
   domain (init_code max_app) UNION {num_stubs max_app - 2}`,
  CHEAT_TAC);;

let chain_exps_no_Labels = prove
 (`!es l. ALL no_Labels es ==>
           ALL no_Labels (MAP (SND o SND) (chain_exps l es))`,
  CHEAT_TAC);;

let chain_exps_obeys_max_app = prove
 (`!es l. ALL (obeys_max_app k) es ==>
           ALL (obeys_max_app k) (MAP (SND o SND) (chain_exps l
             es))`,
  CHEAT_TAC);;

(* chain_exps_every_Fn_SOME[allow_rebind] *)
let clos_to_bvlProof_chain_exps_every_Fn_SOME = prove
 (`!es l. every_Fn_SOME es ==>
           every_Fn_SOME (MAP (SND o SND) (chain_exps l es))`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "all";
   "build_const'";
   "globals_approx_every_Fn_SOME";
   "globals_approx_every_Fn_vs_NONE";
   "known_co";
   "parts";
   "syntax_ok";
   "update_tag"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
