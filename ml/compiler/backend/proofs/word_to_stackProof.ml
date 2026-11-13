(* ======================================================== *)
(*  word_to_stackProof: ported from HOL4's
    compiler/backend/proofs/word_to_stackProofScript.sml
    A proof theory about word_to_stack.ml, with 18 definitions and
    364 theorems.  Needed by backendProof.ml and
    stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_to_stack
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
(* for word_add_carry_def *)
needs "compiler/backend/reg_alloc/parmove.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
(* for extract_labels *)
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
(* for list_Seq *)
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/bitstring.ml";;
needs "lib/byte.ml";;
needs "lib/pegexec.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/semanticsProps.ml";;
(* for extend_with_resource_limit *)

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "word_to_stackProof"
  ["backend_common"; "mllist"; "semanticsProps"; "stackLang";
   "stackProps"; "stackSem"; "wordProps"; "wordSem"; "word_to_stack"];;

let _ = do_list hide_constant ["every"; "fv"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["memory","memory"];;

(* Set up ML bindings *)
(* HOL4 word_to_stackProofScript.sml:18-20: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:31-32: ML code, not ported *)
(* HOL4 word_to_stackProofScript.sml:33: the type abbreviation state,
   which the port expands *)
(* HOL4 word_to_stackProofScript.sml:34-35: the overload word_cmp,
   which the port expands *)

(* HOL4 word_to_stackProofScript.sml:37: the ML values that the
   definitions below antiquote *)

(* HOL4 word_to_stackProofScript.sml:39-40: the ML values that the
   definitions below antiquote *)

let StackHandlerArgs_F = prove
 (`StackHandlerArgs F dest arg_count (k,f,f') =
     StackArgs dest arg_count (k,f + 3,f' + 3)`,
  CHEAT_TAC);;

let PushHandler_F = prove
 (`PushHandler F l1 l2 (k,f,f') =
     Seq (stackLang_StackAlloc 3)
    (Seq (Inst (asm_Const k (n2w 1)))
    (Seq (stackLang_StackStore k 0)
    (Seq (LocValue k l1 l2)
    (Seq (stackLang_StackStore k 1)
    (Seq (Get k Handler)
    (Seq (stackLang_StackStore k 2)
    (Seq Skip
    (Seq (stackLang_StackGetSize k)
         (Set Handler k)))))))))`,
  CHEAT_TAC);;

let PopHandler_F = prove
 (`PopHandler F (k,f,f') prog =
     Seq (stackLang_StackLoad k 2)
    (Seq (Set Handler k)
    (Seq (stackLang_StackFree 3) prog))`,
  CHEAT_TAC);;

let raise_stub_F = prove
 (`raise_stub F k =
     Seq (Get k Handler)
    (Seq (stackLang_StackSetSize k)
    (Seq Skip
    (Seq (stackLang_StackLoad k 2)
    (Seq (Set Handler k)
    (Seq (stackLang_StackLoad k 1)
    (Seq (stackLang_StackFree 3)
         (Raise k)))))))`,
  CHEAT_TAC);;

let copy_ret_F = prove
 (`copy_ret F is_handle (k,f,f') vs kont =
     (let n = num_stack_ret k vs in
     if n = 0 then kont else Seq (copy_ret_aux k (if is_handle then f
       + 3 else f) n)
              (SeqStackFree n kont))`,
  CHEAT_TAC);;

(* TODO: move to word/stackProps? *)
let set_var_swap = prove
 (`~(a = a') ==> stackSem_set_var a b (set_var a' b' c) = set_var a'
  b' (set_var a b c)`,
  CHEAT_TAC);;

let set_var_swap_word = prove
 (`~(a = a') ==> wordSem_set_var a b (set_var a' b' c) = set_var a' b'
  (set_var a b c)`,
  CHEAT_TAC);;

let set_var_cancel = prove
 (`stackSem_set_var a b (set_var a b' t) = set_var a b t`,
  CHEAT_TAC);;

let set_var_cancel_word = prove
 (`wordSem_set_var a b (set_var a b' s) = set_var a b s`,
  CHEAT_TAC);;

(* get_var_set_var[simp] *)
let word_to_stackProof_get_var_set_var = prove
 (`stackSem_get_var k (set_var k v st) = SOME v`,
  CHEAT_TAC);;

(* [simp] *)
let state_with_const = prove
 (`(stackSem_state_clock_fupd (K (stackSem_state_clock t)) t) =
  (t:('a,'c,'ffi)stackSem_state)`,
  CHEAT_TAC);;

let set_store_set_var = prove
 (`stackSem_set_store a b (set_var c d e) = set_var c d (set_store a b
  e)`,
  CHEAT_TAC);;

(* Move to props END *)

(* TODO delete *)
let DROP_DROP_EQ = prove
 (`!n m xs. DROP m (DROP n xs) = DROP (m + n) xs`,
  CHEAT_TAC);;

(* [local] *)
let TAKE_TAKE_MIN = prove
 (`!xs m n. TAKE n (TAKE m xs) = TAKE (MIN m n) xs`,
  CHEAT_TAC);;

(* [local] *)
let TAKE_DROP_EQ = prove
 (`!xs n m. TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs)`,
  CHEAT_TAC);;

(* [local] *)
let DROP_TAKE_NIL = prove
 (`DROP n (TAKE n xs) = []`,
  CHEAT_TAC);;

(* delete END *)

let MAX_LIST_GENLIST_evens = prove
 (`!n. MAX_LIST (GENLIST (\x. 2 * x) n) = 2 * (n - 1)`,
  CHEAT_TAC);;

let MAX_LIST_GENLIST_evens2 = prove
 (`!n. MAX_LIST (GENLIST (\x. 2 * (x + 1)) n) = 2 * n`,
  CHEAT_TAC);;

(*misc word stuff*)

(* word_or_eq_0[local] *)
let word_to_stackProof_word_or_eq_0 = prove
 (`((w || v) = (n2w 0)) <=> (w = (n2w 0)) /\ (v = (n2w 0))`,
  CHEAT_TAC);;

(* shift_shift_lemma[local] *)
let word_to_stackProof_shift_shift_lemma = prove
 (`~(word_msb w) ==> (w << 1 >>> 1 = w)`,
  CHEAT_TAC);;

let word_shift_or_1 = prove
 (`(n << 1) || (n2w 1) = (n << 1) + (n2w 1)`,
  CHEAT_TAC);;
(*misc word_stuff end*)

(* TODO figure a normal form.
  Should set_store be pushed out always?*)
(* [local] *)
let push_env_set_store = prove
 (`wordSem_push_env env (NONE:(num#'a wordLang_prog#num#num) option)
  (set_store AllocSize (wordLang_Word c) s) =
     set_store AllocSize (wordLang_Word c) (wordSem_push_env env
       ((NONE:(num#'a wordLang_prog#num#num) option)) s)`,
  CHEAT_TAC);;

(* [local] *)
let LASTN_LENGTH_ID2 = prove
 (`!stack' x.
   (x + 1 = LENGTH stack') ==>
   LASTN (x + 1) stack' =
   HD stack' :: LASTN x stack'`,
  CHEAT_TAC);;

(* [local] *)
let LASTN_MORE = prove
 (`!ls n.
   ~(n < LENGTH ls) ==> LASTN n ls = ls`,
  CHEAT_TAC);;

(*Equality theorems available if n ≤ LENGTH ls*)
(* [local] *)
let LASTN_LENGTH_BOUNDS = prove
 (`!n ls.
   let xs = LASTN n ls in
   LENGTH xs <= n /\
   LENGTH xs <= LENGTH ls`,
  CHEAT_TAC);;

(* [local] *)
let LASTN_CONS_ID = prove
 (`n = LENGTH ls ==>
   LASTN (SUC n) (frame :: ls) = (frame :: ls)`,
  CHEAT_TAC);;

(*Strengthened version of LASTN_DROP after change to make it total*)
(* [local] *)
let LASTN_DROP2 = prove
 (`!l n.
   LASTN n l = DROP (LENGTH l - n) l`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_IMP_EVERY_LASTN = prove
 (`!xs ys P. EVERY P xs /\ LASTN n xs = ys ==> EVERY P ys`,
  CHEAT_TAC);;

(* [local] *)
let LASTN_HD = prove
 (`!ls x.
   x <= LENGTH ls ==>
   HD (LASTN x ls) =
   EL (LENGTH ls - x) ls`,
  CHEAT_TAC);;

let LLOOKUP_TAKE = prove
 (`n < f ==>
   (\l n. oEL n l) (TAKE f xs) (n) = (\l n. oEL n l) xs (n)`,
  CHEAT_TAC);;
(* TODO: many things in this file need moving *)

(* HOL4 word_to_stackProofScript.sml:317: ML code, not ported *)

let index_list_def = cake_define_list
  [`index_list [] n = []`;
   `index_list (x :: xs) n = (n + LENGTH xs,x) :: index_list xs n`];;

let LENGTH_index_list = prove
 (`!l n. LENGTH (index_list l n) = LENGTH l`,
  CHEAT_TAC);;

let EL_index_list = prove
 (`!xs i. i < LENGTH xs ==>
          (EL i (index_list xs k) = ((k + LENGTH xs) - i - 1,EL i
            xs))`,
  CHEAT_TAC);;

let EL_index_list2 = prove
 (`!xs i. i < LENGTH xs ==>
           (EL i (index_list xs k) = ((k + LENGTH xs) - (i + 1),EL
             i xs))`,
  CHEAT_TAC);;

let MAP_SND_index_list = prove
 (`!xs k. MAP SND (index_list xs k) = xs`,
  CHEAT_TAC);;

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)
let MAP_FST_index_list = prove
 (`!xs k. MAP FST (index_list xs k) = REVERSE (MAP ((+) k) (COUNT_LIST
  (LENGTH xs)))`,
  CHEAT_TAC);;

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)
let index_list_eq_ZIP = prove
 (`index_list xs k = ZIP (REVERSE (MAP ((+) k) (COUNT_LIST (LENGTH
  xs)))) xs`,
  CHEAT_TAC);;

(*MEM to an EL characterization for index lists*)
(* [local] *)
let MEM_index_list_LIM = prove
 (`!ls n v k.
   MEM (n,v) (index_list ls k) ==>
   n - k < LENGTH ls`,
  CHEAT_TAC);;

(* [local] *)
let MEM_index_list_EL = prove
 (`!ls n v.
   MEM (n,v) (index_list ls k) ==>
   EL (LENGTH ls - (n - k + 1)) ls = v`,
  CHEAT_TAC);;

let ALOOKUP_index_list = prove
 (`!ls n.
   n < LENGTH ls + k ==>
   ALOOKUP (index_list ls k) n =
   (\l n. oEL n l) ls ((LENGTH ls + k) - (n + 1))`,
  CHEAT_TAC);;

let IMP_filter_bitmap_EQ_SOME_NIL = prove
 (`!xs ys zs.
     (LENGTH xs = LENGTH ys) /\
     zs = MAP FST (FILTER SND (ZIP ys xs)) ==>
     (filter_bitmap xs ys = SOME (zs,[]))`,
  CHEAT_TAC);;

let filter_bitmap_length = prove
 (`!bs ls xs ys.
   filter_bitmap bs ls = SOME (xs,ys) ==>
   LENGTH xs <= LENGTH bs`,
  CHEAT_TAC);;

let filter_bitmap_length_input = prove
 (`!xs ys ls. filter_bitmap xs ys = SOME ls ==> LENGTH xs <= LENGTH ys`,
  CHEAT_TAC);;

let filter_bitmap_MAP_IMP = prove
 (`!ys xs l.
    filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[]) /\
    filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[]) ==>
    filter_bitmap ys xs = SOME (l,[])`,
  CHEAT_TAC);;

let filter_bitmap_IMP_MAP_SND = prove
 (`!ys xs l.
     filter_bitmap ys xs = SOME (l,[]) ==>
     filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[])`,
  CHEAT_TAC);;

let filter_bitmap_IMP_MAP_FST = prove
 (`!ys xs l.
     filter_bitmap ys xs = SOME (l,[]) ==>
     filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[])`,
  CHEAT_TAC);;

let filter_bitmap_TAKE_LENGTH_IMP = prove
 (`!h5 x4 l.
     filter_bitmap h5 (TAKE (LENGTH h5) x4) = SOME (MAP SND l,[]) ==>
     filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)`,
  CHEAT_TAC);;

let filter_bitmap_lemma = prove
 (`filter_bitmap h5 (index_list (TAKE (LENGTH h5) x4) k) = SOME (l,[])
  ==>
   filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)`,
  CHEAT_TAC);;

let filter_bitmap_MEM = prove
 (`!b ls ls' x.
   filter_bitmap b ls = SOME (ls',[]) /\
   MEM x ls' ==> MEM x ls`,
  CHEAT_TAC);;

(* [simp] *)
let TAKE_LUPDATE = prove
 (`!xs n x i. TAKE n (LUPDATE x i xs) = LUPDATE x i (TAKE n xs)`,
  CHEAT_TAC);;

(* [local] *)
let DROP_LUPDATE_lemma1 = prove
 (`!xs n m h. n <= m ==>
                DROP n (LUPDATE h m xs) = LUPDATE h (m - n) (DROP n
                  xs)`,
  CHEAT_TAC);;

(* [local] *)
let DROP_LUPDATE_lemma2 = prove
 (`!xs n m h. m < n ==> DROP n (LUPDATE h m xs) = DROP n xs`,
  CHEAT_TAC);;

(* DROP_LUPDATE *)
let word_to_stackProof_DROP_LUPDATE = prove
 (`!n h m xs.
      DROP n (LUPDATE h m xs) =
      (if m < n then DROP n xs else LUPDATE h (m - n) (DROP n xs))`,
  CHEAT_TAC);;

(* MIN_ADD[local] *)
let word_to_stackProof_MIN_ADD = prove
 (`MIN m1 m2 + n = MIN (m1 + n) (m2 + n)`,
  CHEAT_TAC);;

let list_LUPDATE_def = cake_define_list
  [`list_LUPDATE [] n ys = ys`;
   `list_LUPDATE (x :: xs) n ys = list_LUPDATE xs (n + 1) (LUPDATE
  x n ys)`];;

(* [simp] *)
let LENGTH_list_LUPDATE = prove
 (`!xs n ys. LENGTH (list_LUPDATE xs n ys) = LENGTH ys`,
  CHEAT_TAC);;

(* [simp] *)
let TAKE_list_LUPDATE = prove
 (`!ys xs n i. TAKE n (list_LUPDATE ys i xs) = list_LUPDATE ys i (TAKE
  n xs)`,
  CHEAT_TAC);;

(* [local] *)
let LLOOKUP_list_LUPDATE_IGNORE = prove
 (`!xs i n ys.
       i + LENGTH xs <= n ==>
       (\l n. oEL n l) (list_LUPDATE xs i ys) n = (\l n. oEL n l)
         ys n`,
  CHEAT_TAC);;

(* [local] *)
let DROP_list_LUPDATE = prove
 (`!ys n m xs.
       n <= m ==>
       DROP n (list_LUPDATE ys m xs) =
       list_LUPDATE ys (m - n) (DROP n xs)`,
  CHEAT_TAC);;

(* [local] *)
let DROP_list_LUPDATE_IGNORE = prove
 (`!xs i ys n.
       LENGTH xs + i <= n ==>
       DROP n (list_LUPDATE xs i ys) = DROP n ys`,
  CHEAT_TAC);;

(* [simp] *)
let list_LUPDATE_NIL = prove
 (`!xs i. list_LUPDATE xs i [] = []`,
  CHEAT_TAC);;

(* [local] *)
let LUPDATE_TAKE_LEMMA = prove
 (`!xs n w. LUPDATE w n xs = TAKE n xs ++ LUPDATE w 0 (DROP n xs)`,
  CHEAT_TAC);;

let list_LUPDATE_TAKE_DROP = prove
 (`!xs (ys:'a list) n.
       list_LUPDATE xs n ys = TAKE n ys ++ list_LUPDATE xs 0 (DROP
         n ys)`,
  CHEAT_TAC);;

(* [simp] *)
let list_LUPDATE_0_CONS = prove
 (`!xs x ys y. list_LUPDATE (x :: xs) 0 (y :: ys) = x :: list_LUPDATE
  xs 0 ys`,
  CHEAT_TAC);;

let list_LUPDATE_APPEND = prove
 (`!xs ys zs.
      LENGTH xs = LENGTH ys ==> (list_LUPDATE xs 0 (ys ++ zs) = xs
        ++ zs)`,
  CHEAT_TAC);;

(* move to stackProps? *)

(* [local] *)
let DIV_ADD_1 = prove
 (`0 < d ==> (m DIV d + 1 = (m + d) DIV d)`,
  CHEAT_TAC);;

(* [local] *)
let LENGTH_word_list_lemma = prove
 (`!xs d. 0 < d ==> (LENGTH (word_list xs d) = (LENGTH xs - 1) DIV d +
  1)`,
  CHEAT_TAC);;

let LENGTH_word_list = prove
 (`!xs d. LENGTH (word_list xs d) =
           (if d = 0 then 1 else (LENGTH xs - 1) DIV d + 1)`,
  CHEAT_TAC);;

(* move to wordProps? *)

(* [local] *)
let list_rearrange_I = prove
 (`(list_rearrange I = I)`,
  CHEAT_TAC);;

(* state relation *)

(*Abstracts a stackLang stack w.r.t. wordLang's
  Note: requires assumption on dimindex(:'a) stated in state_rel *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let abs_stack_def = cake_define_cheat CHEAT_TAC
  `abs_stack bitmaps x2 stack' x4 =
        match (bitmaps,x2,stack',x4) with
          ((bitmaps:('a word) list),[],stack',[]) ->
       (if stack' = [wordLang_Word ((n2w 0):'a word)] then SOME []
         else NONE)
        | (bitmaps,(StackFrame n l0 l NONE :: xs),(w :: stack'),(len
          :: lens)) ->
       // Should cover the stack = [] case automatically
       (match full_read_bitmap bitmaps w with NONE -> NONE |
         // read_bitmap reads a bitmap and returns the liveness bits,
         // the words read and the rest of the stack
         SOME bits ->
           (if ~(LENGTH bits = len) then NONE else
           if LENGTH stack' < len then NONE else
             // if the (len + 1) n ≠ len + 1 then NONE else
             let frame = TAKE len stack' in
             let rest = DROP len stack' in
               match abs_stack bitmaps xs rest lens with NONE -> NONE
                 | SOME ys -> SOME ((NONE,bits,frame) :: ys)))
        | (bitmaps,((StackFrame n l0 l (SOME _1)) :: xs),(w ::
          stack'),(len :: lens)) ->
       // Index for bitmap for a handler frame
       (if ~(w = wordLang_Word (n2w 1)) then NONE else
         (match stack' with
           // Read next 2 elements on the stack for the handler
           loc :: hv :: w :: stack' ->
            (match full_read_bitmap bitmaps w with NONE -> NONE |
               // read_bitmap reads a bitmap and returns the liveness bits,
               // the words read and the rest of the stack
               SOME bits ->
                 (if ~(LENGTH bits = len) then NONE else
                 if LENGTH stack' < len then NONE else
                   // if the (len + 1) n ≠ len + 1 then NONE else
                   let frame = TAKE len stack' in
                   let rest = DROP len stack' in
                     match abs_stack bitmaps xs rest lens with NONE
                       -> NONE | SOME ys -> SOME ((SOME
                       (loc,hv),bits,frame) :: ys))) | _2 -> NONE))
        | (bitmaps,_3,_4,_5) -> NONE`;;

(* HOL4 word_to_stackProofScript.sml:742: ML code, not ported *)

let read_bitmap_append_extra = prove
 (`!l1 l2 bits.
   read_bitmap l1 = SOME bits ==>
   read_bitmap (l1 ++ l2) = SOME bits`,
  CHEAT_TAC);;

let full_read_bitmap_append = prove
 (`!bitmaps w bits more_bitmaps.
   full_read_bitmap bitmaps w = SOME bits ==>
   full_read_bitmap (bitmaps ++ more_bitmaps) w = SOME bits`,
  CHEAT_TAC);;

let abs_stack_bitmaps_prefix = prove
 (`!bitmaps frames stack' lens more_bitmaps result.
   abs_stack bitmaps frames stack' lens = SOME result ==>
   abs_stack (bitmaps ++ more_bitmaps) frames stack' lens = SOME
     result`,
  CHEAT_TAC);;

(*TODO this should probably be an Overload*)
let MAP_FST_def = cake_define
  `MAP_FST f xs = MAP (\(x,y). (f x,y)) xs`;;

(* [local] *)
let MAP_SND_MAP_FST = prove
 (`!xs f. MAP SND (MAP_FST f xs) = MAP SND xs`,
  CHEAT_TAC);;

let adjust_names_def = cake_define
  `adjust_names n = n DIV 2`;;

(*handler_val counts the total number of words in the list of frames*)
let handler_val_def = cake_define_list
  [`handler_val [] = 1`;
   `handler_val ((NONE,_6,frame) :: stack') =
        1 + LENGTH frame + handler_val stack'`;
   `handler_val ((SOME _7,_8,frame) :: stack') =
        // 1 for handler bitmaps pointer
        // + 2 more for the pointer and locs
        // + 1 for the next bitmap pointer
        4 + LENGTH frame + handler_val stack'`];;

let is_handler_frame_def = cake_define
  `is_handler_frame x1 =
        match x1 with
          StackFrame n l0 l NONE -> F
        | _9 -> T`;;

(*Checks for consistency of the values*)
let stack_rel_aux_def = cake_define
  `stack_rel_aux k len x3 x4 =
        match (x3,x4) with
          ([],[]) -> T
        | ((StackFrame n l0 l NONE :: xs),((NONE,bits,frame) ::
          stack')) ->
       (!n v.
         ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ==>
         adjust_names n < k + LENGTH bits /\
         oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F
           /\
         ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
       filter_bitmap bits (index_list frame k) = SOME (MAP_FST
         adjust_names l,[]) /\
       the (LENGTH frame + 1) n = LENGTH frame + 1 /\
       stack_rel_aux k len xs stack'
        | (((StackFrame n l0 l (SOME (h1,l1,l2))) :: xs),((SOME
          (loc,hv),bits,frame) :: stack')) ->
       (h1 < LENGTH stack' /\
       is_handler_frame (EL (LENGTH stack' - (h1 + 1)) xs) ==>
       hv = wordLang_Word (n2w (len - handler_val (LASTN (h1 + 1)
         stack')))) /\
       loc = Loc l1 l2 /\
       (!n v.
         ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ==>
         adjust_names n < k + LENGTH bits /\
         oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F
           /\
         ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
       filter_bitmap bits (index_list frame k) = SOME (MAP_FST
         adjust_names l,[]) /\
       the (LENGTH frame + 1) n = LENGTH frame + 1 /\
       stack_rel_aux k len xs stack'
        | (_10,_11) -> F`;;

let sorted_env_def = cake_define
  `sorted_env (StackFrame n l0 l _12) = SORTED (\x y. FST x > FST y)
  l`;;

let word_to_stackProof_stack_rel_def = cake_define
  `word_to_stackProof_stack_rel k s_handler s_stack t_handler
  t_rest_of_stack t_stack_length t_bitmaps lens <=>
     EVERY sorted_env s_stack /\
     (?stack'.
       abs_stack t_bitmaps s_stack t_rest_of_stack lens = SOME stack'
         /\
       (
       s_handler < LENGTH s_stack /\
       is_handler_frame (EL (LENGTH s_stack - (s_handler + 1))
         s_stack) ==>
       t_handler = SOME (wordLang_Word (n2w (t_stack_length -
         handler_val (LASTN (s_handler + 1) stack'))))) /\
       stack_rel_aux k t_stack_length s_stack stack')`;;
hol4_overload "stack_rel" "word_to_stackProof_stack_rel";;

(*f is the size of the current frame + 1 most of the time
  (extra word for the bitmap pointer)
  f' is the size of the current frame
  lens tracks the size of each remaining stack frame on the stackLang stack
*)

(* Stack size as predicted by the wordLang state is a conservative estimate of the
   actual stack usage. *)
let stack_size_rel_def = cake_define
  `stack_size_rel f s_locals_size s_stack_limit s_stack_max s_stack
     t_stack t_stack_space (extra:num) <=>
     (~(f = 0) ==> the f s_locals_size = f) /\
     s_stack_limit = LENGTH t_stack /\
     (!sm. s_stack_max = SOME sm ==>
       LENGTH t_stack - t_stack_space - f - extra <= sm /\
       IS_SOME s_locals_size /\
       (?ss. stack_size s_stack = SOME ss /\
         ss = LENGTH t_stack - t_stack_space - f - extra))`;;

let stack_size_rel_iff = prove
 (`stack_size_rel f s_locals_size s_stack_limit s_stack_max s_stack
     t_stack t_stack_space extra <=>
   (~(f = 0) ==> the f s_locals_size = f) /\
   s_stack_limit = LENGTH t_stack /\
   LENGTH t_stack - t_stack_space - f - extra <= the (LENGTH t_stack
     - t_stack_space - f - extra) s_stack_max /\
   (IS_SOME s_stack_max ==> IS_SOME (stack_size s_stack)) /\
   (IS_SOME s_stack_max ==> IS_SOME s_locals_size) /\
   (IS_SOME s_stack_max ==> the (LENGTH t_stack - t_stack_space - f
     - extra) (stack_size s_stack) = LENGTH t_stack - t_stack_space -
     f - extra)`,
  CHEAT_TAC);;

let word_to_stackProof_state_rel_def = cake_define
  `word_to_stackProof_state_rel ac k f f'
  (s:('a,num#'c,'ffi)wordSem_state) (t:('a,'c,'ffi)stackSem_state) lens
  extra <=>
     (wordSem_state_clock s = stackSem_state_clock t) /\
       (wordSem_state_gc_fun s = stackSem_state_gc_fun t) /\
       (wordSem_state_permute s = K I) /\
     (stackSem_state_ffi t = wordSem_state_ffi s) /\
       stackSem_state_use_stack t /\ stackSem_state_use_store t /\
       stackSem_state_use_alloc t /\
     (stackSem_state_memory t = wordSem_state_memory s) /\
       (stackSem_state_mdomain t = wordSem_state_mdomain s) /\ 4 < k /\
     (stackSem_state_sh_mdomain t = wordSem_state_sh_mdomain s) /\
     (wordSem_state_store s = stackSem_state_store t \\ Handler) /\
       gc_fun_ok (stackSem_state_gc_fun t) /\ wordSem_state_termdep s =
       0 /\ stackSem_state_be
     t = wordSem_state_be s /\ stackSem_state_ffi t =
       wordSem_state_ffi s /\ Handler IN FDOM (stackSem_state_store t)
       /\ stackSem_state_fp_regs
     t = wordSem_state_fp_regs s /\ stackSem_state_data_buffer
     t = wordSem_state_data_buffer s /\ stackSem_state_code_buffer
     t = wordSem_state_code_buffer s /\ wordSem_state_compile
     s = (\(bm0,cfg) progs.
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
       OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND
         bm,cfg)))
         (stackSem_state_compile t cfg progs)) /\
           stackSem_state_compile_oracle
     t = (\n.
       let ((bm0,cfg),progs) = wordSem_state_compile_oracle s n in
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
         (cfg,progs,append (FST bm))) /\
     (!n. let ((bm0,cfg),progs) = wordSem_state_compile_oracle s n in
         EVERY (post_alloc_conventions k o SND o SND) progs /\
         EVERY (flat_exp_conventions o SND o SND) progs /\
         EVERY ((\x y. ~(x = y)) raise_stub_location o FST) progs /\
         EVERY ((\x y. ~(x = y)) store_consts_stub_location o FST)
           progs /\
         (n = 0 ==> bm0 = LENGTH (stackSem_state_bitmaps t))) /\
     domain (stackSem_state_code t) = raise_stub_location INSERT
                       store_consts_stub_location INSERT domain
                         (wordSem_state_code s) /\
     (!n word_prog arg_count.
        (sptree_lookup n (wordSem_state_code s) = SOME
          (arg_count,word_prog)) ==>
        post_alloc_conventions k word_prog /\
        flat_exp_conventions word_prog /\
        (?bs i bs2 i2 f stack_prog.
          word_to_stack_compile_prog ac F word_prog arg_count k
            (bs,i) = (stack_prog,f,(bs2,i2)) /\
          LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH
            (stackSem_state_bitmaps t) /\
          isPREFIX (append bs2) (DROP (i - LENGTH (append bs))
            (stackSem_state_bitmaps t)) /\
          (sptree_lookup n (stackSem_state_code t) = SOME stack_prog)
            /\
          the f (sptree_lookup n (wordSem_state_stack_size s)) = f))
            /\
     (sptree_lookup raise_stub_location (stackSem_state_code t) =
       SOME (raise_stub F k)) /\
     (sptree_lookup store_consts_stub_location (stackSem_state_code
       t) = SOME (store_consts_stub k)) /\
     good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
     LENGTH (stackSem_state_bitmaps t) + LENGTH (buffer_buffer
       (wordSem_state_data_buffer s)) + buffer_space_left
       (wordSem_state_data_buffer s) + 1 < dimword (:'a) /\
     1 <= LENGTH (stackSem_state_bitmaps t) /\ HD
       (stackSem_state_bitmaps t) = (n2w 4) /\
       stackSem_state_stack_space
     t + f <= LENGTH (stackSem_state_stack t) /\ LENGTH
       (stackSem_state_stack t) < dimword (:'a) /\
     (if f' = 0 then f = 0 else (f = f' + 1)) /\
     wf (wordSem_state_locals s) /\
     stack_size_rel f (wordSem_state_locals_size s)
       (wordSem_state_stack_limit s) (wordSem_state_stack_max s)
       (wordSem_state_stack s) (stackSem_state_stack
       t) (stackSem_state_stack_space t) (extra:num) /\
     (let stack' = DROP (stackSem_state_stack_space t + extra)
       (stackSem_state_stack t) in
     // First f things on stack are the live stack vars
     let current_frame = TAKE f stack' in
     let rest_of_stack = DROP f stack' in
       word_to_stackProof_stack_rel k (wordSem_state_handler s)
         (wordSem_state_stack s) (FLOOKUP (stackSem_state_store t)
         Handler)
         rest_of_stack (LENGTH (stackSem_state_stack t))
           (stackSem_state_bitmaps t) lens /\
       (!n v.
         (sptree_lookup n (wordSem_state_locals s) = SOME v) ==>
         EVEN n /\
         (if n DIV 2 < k then (FLOOKUP (stackSem_state_regs t) (n DIV
           2) = SOME v) else ((\l n. oEL n l) current_frame (f - 1 - (n
           DIV 2 - k)) = SOME v) /\
              n DIV 2 < k + f')))`;;
hol4_overload "state_rel" "word_to_stackProof_state_rel";;

(* correctness proof *)

(* [local] *)
let evaluate_SeqStackFree = prove
 (`stackSem_state_use_stack
     t /\ stackSem_state_stack_space t <= LENGTH (stack t) ==>
       evaluate (SeqStackFree f p,t) =
       evaluate (Seq (stackLang_StackFree f) p,t)`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:974-981: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:983-993: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:995-996: a theorem that HOL4
   states as the value of an ML expression: DROP_list_LUPDATE_lemma *)

(* [local] *)
let bits_to_word_bit = prove
 (`!bs i.
       i < dimindex (:'a) /\ i < LENGTH bs ==>
       (FAPPLY (bits_to_word bs:'a word) i = EL i bs)`,
  CHEAT_TAC);;

(* [local] *)
let bits_to_word_miss = prove
 (`!bs i.
       i < dimindex (:'a) /\ LENGTH bs <= i ==>
       ~(FAPPLY (bits_to_word bs:'a word) i)`,
  CHEAT_TAC);;

(* [local] *)
let bits_to_word_SNOC = prove
 (`!bs b.
    bits_to_word (SNOC b bs) =
   (if b then (n2w 1) else (n2w 0)) << (LENGTH bs) || (bits_to_word
     bs)`,
  CHEAT_TAC);;

(* [local] *)
let list_LUPDATE_write_bitmap_NOT_NIL = prove
 (`8 <= dimindex (:'a) ==>
     (~(list_LUPDATE (MAP wordLang_Word (write_bitmap names k f')) 0
       xs =
      [wordLang_Word ((n2w 0):'a word)]))`,
  CHEAT_TAC);;


(* [local] *)
let bit_length_bits_to_word = prove
 (`!qs.
       LENGTH qs + 1 < dimindex (:'a) ==>
       bit_length (bits_to_word (qs ++ [T]):'a word) = LENGTH qs +
         1`,
  CHEAT_TAC);;

let bits_to_word_bitstring_reverse = prove
 (`(bits_to_word xs:'a word) = v2w (REVERSE xs)`,
  CHEAT_TAC);;

(* [local] *)
let GENLIST_bits_to_word_alt = prove
 (`LENGTH (xs ++ ys) <= dimindex (:'a) ==>
     GENLIST (\i. FAPPLY (bits_to_word (xs ++ ys):'a word) i)
       (LENGTH xs) = xs`,
  CHEAT_TAC);;

(* [local] *)
let GENLIST_bits_to_word = prove
 (`LENGTH qs' + 1 < dimindex (:'a) ==>
     GENLIST (\i. FAPPLY (bits_to_word (qs' ++ [T]):'a word) i)
       (LENGTH qs') = qs'`,
  CHEAT_TAC);;

(* [local] *)
let read_bitmap_word_list = prove
 (`8 <= dimindex (:'a) ==>
     read_bitmap
       ((word_list (qs ++ [T]) (dimindex (:'a) - 1)) ++ (xs:('a word)
         list)) =
     SOME qs`,
  CHEAT_TAC);;

(* [local] *)
let APPEND_LEMMA = prove
 (`n1 + n2 + n3 <= LENGTH xs ==>
     (?xs2 xs3. (DROP n1 xs = xs2 ++ xs3) /\ n2 = LENGTH xs2)`,
  CHEAT_TAC);;

let read_bitmap_write_bitmap = prove
 (`8 <= dimindex (:'a) ==>
   read_bitmap ((write_bitmap names k f'):('a word) list) =
   SOME (GENLIST (\x. MEM x (MAP (\(r,y). f' - 1 - (r DIV 2 - k))
     (toAList names))) f')`,
  CHEAT_TAC);;

let read_bitmap_insert_bitmap = prove
 (`!bs n bs' n' i cur.
   i < dimword (:'a) /\
   IS_SOME (read_bitmap bm) /\
   n = LENGTH cur + LENGTH (append bs) /\
   insert_bitmap bm (bs,n) = ((bs',n'),i) ==> read_bitmap (DROP (i
     MOD dimword (:'a)) (cur ++ append bs')) = read_bitmap bm`,
  CHEAT_TAC);;

(* [local] *)
let abs_stack_IMP_LENGTH = prove
 (`!bs wstack sstack lens stack'.
     abs_stack bs wstack sstack lens = SOME stack' ==> LENGTH
       stack' = LENGTH wstack /\ LENGTH lens = LENGTH wstack`,
  CHEAT_TAC);;

(* [local] *)
let SORTED_FST_LESS_IMP = prove
 (`!xs x.
       SORTED (\x y. FST x > (FST y:num)) (x :: xs) ==>
       SORTED (\x y. FST x > FST y) xs /\ ~(MEM x xs) /\
       (!y. MEM y xs ==> FST x > FST y)`,
  CHEAT_TAC);;

(* [local] *)
let SORTED_IMP_EQ_LISTS = prove
 (`!xs ys.
       SORTED (\x y. FST x > (FST y:num)) ys /\
       SORTED (\x y. FST x > FST y) xs /\
       (!x. MEM x ys <=> MEM x xs) ==>
       (xs = ys)`,
  CHEAT_TAC);;

let transitive_key_val_compare = prove
 (`transitive key_val_compare`,
  CHEAT_TAC);;

let total_key_val_compare = prove
 (`total key_val_compare`,
  CHEAT_TAC);;

(* [local] *)
let SORTS_SORT_key_val_compare = prove
 (`SORTS sort key_val_compare`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:1259-1262: ML code, not ported *)

(* [local] *)
let SORTED_weaken2 = prove
 (`!ls. SORTED R ls /\
   ALL_DISTINCT ls /\
   (!x y. MEM x ls /\ MEM y ls /\ ~(x = y) /\ R x y ==> R' x y) ==>
   SORTED R' ls`,
  CHEAT_TAC);;

(* [local] *)
let EVEN_GT = prove
 (`!a b.
   EVEN a /\ EVEN b /\
   a > b ==>
   a DIV 2 > b DIV 2`,
  CHEAT_TAC);;

(* [local] *)
let transitive_GT = prove
 (`transitive ((>):num->num->bool)`,
  CHEAT_TAC);;

(* [local] *)
let env_to_list_K_I_IMP = prove
 (`!env l oracle'.
       env_to_list env (K I) = (l,oracle') ==>
       SORTED (\x y. FST x > FST y) l /\ oracle' = K I /\ PERM
         (toAList env) l`,
  CHEAT_TAC);;

let isPREFIX_DROP = prove
 (`!s t i.
   isPREFIX s t ==>
   isPREFIX (DROP i s) (DROP i t)`,
  CHEAT_TAC);;

(* [local] *)
let LLOOKUP_cons_SUC = prove
 (`m < n ==>
   (\l n. oEL n l) (h :: xs) (n - m) =
   (\l n. oEL n l) xs (n - (m + 1))`,
  CHEAT_TAC);;

let EVEN_DIV2_INJ = prove
 (`EVEN x /\ EVEN y /\ DIV2 x = DIV2 y ==> x = y`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let evaluate_wLive = prove
 (cake_as_vars (fun () ->
    `wLive names (bs,n) (k,f,f') = (wlive_prog,(bs',n')) /\
     (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
     (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2) /\
     word_to_stackProof_state_rel ac k f f'
       (s:('a,num#'c,'ffi)wordSem_state) t lens 0 /\
     1 <= f /\
     (cut_envs names (wordSem_state_locals s) = SOME envs) /\
     LENGTH (append bs) <= n /\ n - LENGTH (append bs) <= LENGTH
       (stackSem_state_bitmaps t) /\
     isPREFIX (append bs') (DROP (n - LENGTH (append bs))
       (stackSem_state_bitmaps t)) ==>
     (?(t5:('a,'c,'ffi)stackSem_state) bs5.
       (evaluate (wlive_prog,t) = (NONE,t5)) /\
       word_to_stackProof_state_rel ac k 0 0
         (wordSem_state_locals_size_fupd (K (SOME 0))
         (wordSem_state_locals_fupd (K LN) (wordSem_push_env envs
         ((NONE:(num#'a wordLang_prog#num#num) option)) s))) t5 (f' ::
         lens) 0 /\
       word_to_stackProof_state_rel ac k f f' s t5 lens 0 /\
       LENGTH (stackSem_state_stack t5) = LENGTH
         (stackSem_state_stack t) /\ stackSem_state_stack_space t5 =
         stackSem_state_stack_space t /\
       (!i. ~(i = k) ==> get_var i t5 = get_var i t))`),
  CHEAT_TAC);;

(* [local] *)
let state_rel_set_store_0 = prove
 (`word_to_stackProof_state_rel ac k 0 0 s5 t5 len extra ==>
   word_to_stackProof_state_rel ac k 0 0 (set_store AllocSize w s5)
     (set_store AllocSize w t5) len extra`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let read_bitmap_not_empty = prove
 (cake_as_vars (fun () ->
    `read_bitmap stack = SOME a ==> ~(stack = [])`),
  CHEAT_TAC);;

(* [local] *)
let n2w_lsr_1 = prove
 (`n < dimword (:'a) ==> n2w n >>> 1 = ((n2w (n DIV 2)):'a word)`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let handler_bitmap_props = prove
 (cake_as_vars (fun () ->
    `good_dimindex (:'a) ==>
     read_bitmap (((n2w 4):'a word) :: stack) = SOME [F; F]`),
  CHEAT_TAC);;

(* [local] *)
let enc_stack_lemma = prove
 (`!bs (wstack:('a stack_frame) list) sstack lens astack bs'.
       good_dimindex (:'a) /\
       LENGTH bs + 1 < dimword (:'a) /\
       abs_stack bs wstack sstack lens = SOME astack /\
       // The first bitmap is the handler one
       1 <= LENGTH bs /\
       HD bs = (n2w 4) /\
       stack_rel_aux k len wstack astack ==>
       enc_stack bs sstack = SOME (enc_stack wstack)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_enc_stack = prove
 (`word_to_stackProof_state_rel ac k 0 0 s1 t1 lens 0 ==>
     (enc_stack (stackSem_state_bitmaps t1) (DROP
       (stackSem_state_stack_space t1) (stack t1)) =
        SOME (enc_stack (stack s1)))`,
  CHEAT_TAC);;

(* [local] *)
let map_bitmap_success = prove
 (`!bs stack' a b ls.
   filter_bitmap bs stack' = SOME (a,b) /\
   LENGTH ls = LENGTH a ==>
   (?x z.
   map_bitmap bs ls stack' = SOME (x,[],DROP (LENGTH bs) stack') /\
   filter_bitmap bs x = SOME (ls,[]))`,
  CHEAT_TAC);;

(*Might need to extend c as well*)
(* [local] *)
let map_bitmap_more = prove
 (`!bs ls stack' n a c ls'.
   map_bitmap bs ls stack' = SOME (a,[],c) ==>
   map_bitmap bs (ls ++ ls') stack' = SOME (a,ls',c)`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let map_bitmap_more_simp = prove
 (cake_as_vars (fun () ->
    `map_bitmap bs (TAKE (LENGTH l) ls) stack = SOME (a,[],c) ==>
     map_bitmap bs ls stack = SOME (a,DROP (LENGTH l) ls,c)`),
  CHEAT_TAC);;

let map_bitmap_LLOOKUP_F = prove
 (`!bm ls stack' n res ls1 stack1.
   (\l n. oEL n l) bm n = SOME F /\
   map_bitmap bm ls stack' = SOME (res,ls1,stack1) ==>
   (?v.
   (\l n. oEL n l) res n = SOME v /\
   (\l n. oEL n l) stack' n = SOME v)`,
  CHEAT_TAC);;

(*These two are actually implied by s_key_eq*)
(* [local] *)
let word_stack_dec_stack_shape = prove
 (`!ls wstack res n.
   dec_stack ls wstack = SOME res /\ n < LENGTH wstack ==>
   (is_handler_frame (EL n wstack) <=> is_handler_frame (EL n res))`,
  CHEAT_TAC);;

(* [local] *)
let sorted_env_zip = prove
 (`!(l:(num#'a word_loc) list) (ls:('a word_loc) list) x n.
   sorted_env (StackFrame n l0 l x) /\
   LENGTH ls = LENGTH l ==>
   sorted_env (StackFrame n l0 (ZIP (MAP FST l) ls) x)`,
  CHEAT_TAC);;

(* [local] *)
let word_stack_dec_stack_sorted = prove
 (`!(ls:('a word_loc) list) (wstack:('a stack_frame) list) res.
   dec_stack ls wstack = SOME res /\
   EVERY sorted_env wstack ==>
   EVERY sorted_env res`,
  CHEAT_TAC);;

(* [local] *)
let abs_stack_empty = prove
 (`!bs ls stack' lens.
   abs_stack bs [] ls lens = SOME stack' ==> ls = [wordLang_Word
     (n2w 0)] /\ lens = []`,
  CHEAT_TAC);;

let abs_frame_eq_def = cake_define
  `abs_frame_eq p q <=>
   FST p = FST q /\
   FST (SND p) = FST (SND q) /\
   LENGTH (SND (SND p)) = LENGTH (SND (SND q))`;;

(* [local] *)
let LIST_REL_abs_frame_eq_handler_val = prove
 (`!xs ys.
   LIST_REL abs_frame_eq xs ys ==>
   handler_val xs = handler_val ys`,
  CHEAT_TAC);;

(*Prove the inductive bits first...*)
(* [local] *)
let dec_stack_lemma1 = prove
 (`!bs (wstack:('a stack_frame) list) sstack lens astack wdec ls.
   good_dimindex (:'a) /\
   1 <= LENGTH bs /\
   HD bs = (n2w 4) /\
   // The things going into GC are the same
   abs_stack bs wstack sstack lens = SOME astack /\
   stack_rel_aux k len wstack astack /\
   // The word stack is successfully decoded
   dec_stack ls wstack = SOME wdec ==>
   (?sdec bstack.
   // The stackLang stack is successfully decoded
   dec_stack bs ls sstack = SOME sdec /\
   abs_stack bs wdec sdec lens = SOME bstack /\
   stack_rel_aux k len wdec bstack /\
   // They have exactly the same shape
   LIST_REL abs_frame_eq astack bstack)`,
  CHEAT_TAC);;

(* [local] *)
let dec_stack_lemma = prove
 (`good_dimindex (:'a) /\
   1 <= LENGTH (stackSem_state_bitmaps t1) /\
   HD (stackSem_state_bitmaps t1) = (n2w 4) /\
     stackSem_state_stack_space
   (t1:('a,'c,'ffi)stackSem_state) <= LENGTH (stackSem_state_stack
     t1) /\
   enc_stack (stackSem_state_bitmaps t1) (DROP
     (stackSem_state_stack_space t1) (stackSem_state_stack t1)) =
       SOME (enc_stack (wordSem_state_stack s1)) /\
     (dec_stack x0 (wordSem_state_stack
       (s1:('a,num#'c,'ffi)wordSem_state)) = SOME x) /\
     word_to_stackProof_stack_rel k (wordSem_state_handler s1)
       (wordSem_state_stack s1) (SOME (FAPPLY (stackSem_state_store t1)
       Handler))
       (DROP (stackSem_state_stack_space t1) (stackSem_state_stack
         t1)) (LENGTH (stackSem_state_stack t1)) (stackSem_state_bitmaps
         t1) lens /\
     (LENGTH (enc_stack (wordSem_state_stack s1)) = LENGTH x0) ==>
     (?(yy:('a word_loc) list). dec_stack (stackSem_state_bitmaps t1)
       x0 (DROP (stackSem_state_stack_space t1) (stackSem_state_stack
       t1)) = SOME yy /\
          (stackSem_state_stack_space t1 + LENGTH yy = LENGTH
            (stackSem_state_stack t1)) /\
          word_to_stackProof_stack_rel k (wordSem_state_handler s1) x
            (SOME (FAPPLY (stackSem_state_store t1) Handler)) yy
             (LENGTH (stackSem_state_stack t1))
               (stackSem_state_bitmaps t1) lens)`,
  CHEAT_TAC);;

(* [local] *)
let dec_stack_stack_size = prove
 (`!xs st st'.
    dec_stack xs st = SOME st' ==>
    stack_size st = stack_size st'`,
  CHEAT_TAC);;

(* [local] *)
let gc_state_rel = prove
 (`gc (s1:('a,num#'c,'ffi)wordSem_state) = SOME s2 /\
   word_to_stackProof_state_rel ac k 0 0 s1
     (t1:('a,'c,'ffi)stackSem_state) lens 0 ==>
   (?(t2:('a,'c,'ffi)stackSem_state).
     gc t1 = SOME t2 /\
     word_to_stackProof_state_rel ac k 0 0 (wordSem_state_locals_fupd
       (K LN) s2) t2 lens 0 /\
     LENGTH (stackSem_state_stack t2) = LENGTH
       (stackSem_state_stack t1) /\ stackSem_state_stack_space t2 =
       stackSem_state_stack_space t1)`,
  CHEAT_TAC);;

(* [local] *)
let alloc_alt = prove
 (`~(FST (alloc c names (s:('a,num#'c,'ffi)wordSem_state)) =
       SOME (Error:'a wordSem_result)) ==>
       (alloc c names (s:('a,num#'c,'ffi)wordSem_state) =
        (match cut_envs names (wordSem_state_locals s) with
          NONE -> (SOME Error,s) | SOME env ->
            (match gc (set_store AllocSize (wordLang_Word c)
                       (wordSem_state_locals_size_fupd (K (SOME 0))
                         (wordSem_state_locals_fupd (K LN)
                         (wordSem_push_env env ((NONE:(num#'a
                         wordLang_prog#num#num) option)) s)))) with
              NONE -> (SOME Error,s) | SOME s' ->
                (match wordSem_pop_env s' with
                  NONE -> (SOME Error,s') | SOME s' ->
                    (match wordSem_get_store AllocSize s' with
                      NONE -> (SOME Error,s') | SOME w ->
                        (match has_space w s' with
                          NONE -> (SOME Error,s') | SOME T ->
                            (NONE,s') | SOME F ->
                            (SOME
                              wordSem_NotEnoughSpace
                              ,wordSem_flush_state T s')))))))`,
  CHEAT_TAC);;


(* HOL4 word_to_stackProofScript.sml:2105: the type abbreviation
   result, which the port expands *)

(* s_key_eq_stack_size *)
let word_to_stackProof_s_key_eq_stack_size = prove
 (`!stack' stack'. s_key_eq stack' stack' ==> stack_size stack' =
  stack_size stack'`,
  CHEAT_TAC);;

let s_key_eq_push_env_locals_size = prove
 (`s_key_eq (stack (wordSem_push_env env opt1 s))
            (StackFrame n l0 l opt2 :: stack') ==>
   n = wordSem_state_locals_size s /\ stack_size (stack s) =
     stack_size stack'`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let alloc_IMP_alloc = prove
 (cake_as_vars (fun () ->
    `(wordSem_alloc c names (s:('a,num#'c,'ffi)wordSem_state) =
  ((res:('a wordSem_result) option),s1)) /\
       (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
       (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2) /\
       1 <= f /\
       word_to_stackProof_state_rel ac k f f' s t5 lens 0 /\
       word_to_stackProof_state_rel ac k 0 0
         (wordSem_state_locals_size_fupd (K (SOME 0))
         (wordSem_state_locals_fupd (K LN) (wordSem_push_env envs
         ((NONE:(num#'a wordLang_prog#num#num) option)) s))) t5 (f' ::
         lens) 0 /\
       (cut_envs names (wordSem_state_locals s) = SOME envs) /\
         ~(res = SOME Error) ==>
       (?(t1:('a,'c,'ffi)stackSem_state) res1.
         (stackSem_alloc c t5 = ((res1:('a stackSem_result)
           option),t1)) /\
         (if res = NONE then
           res1 = NONE /\
           word_to_stackProof_state_rel ac k f f' s1 t1 lens 0 /\
           LENGTH (stackSem_state_stack t1) = LENGTH
             (stackSem_state_stack t5) /\ stackSem_state_stack_space
           t1 = stackSem_state_stack_space t5 else
           res = SOME wordSem_NotEnoughSpace /\ res1 = SOME (Halt
             (wordLang_Word (n2w 1))) /\ state_clock
           s1 = stackSem_state_clock t1 /\ state_ffi s1 =
             stackSem_state_ffi t1))`),
  CHEAT_TAC);;

(* [local] *)
let word_gc_empty_frame = prove
 (`gc (stack_fupd (K (StackFrame n [] [] NONE :: stack s)) s) = SOME x
  /\
   wordSem_pop_env x = SOME y ==> wordSem_state_locals
   y = LN /\
   gc s = SOME (wordSem_state_locals_size_fupd (K
     (wordSem_state_locals_size s)) (wordSem_state_locals_fupd (K
     (wordSem_state_locals s)) y))`,
  CHEAT_TAC);;

(* [local] *)
let inter_eq_empty_2 = prove
 (`domain t = {} ==>
   inter s t = LN`,
  CHEAT_TAC);;

(* [local] *)
let alloc_IMP_alloc2 = prove
 (`(wordSem_alloc c names (s:('a,num#'c,'ffi)wordSem_state) = ((res:('a
  wordSem_result) option),s1)) /\
   word_to_stackProof_state_rel ac k 0 0 s t lens 0 /\
   domain (FST names) = {} /\
   domain (SND names) = {} /\ ~(res = SOME Error) ==>
   (?(t1:('a,'c,'ffi)stackSem_state) res1.
     (stackSem_alloc c t = ((res1:('a stackSem_result) option),t1))
       /\
     (if res = NONE then
       res1 = NONE /\
       word_to_stackProof_state_rel ac k 0 0 s1 t1 lens 0 /\
       LENGTH (stackSem_state_stack t1) = LENGTH (stack t) /\
         stackSem_state_stack_space
       t1 = stackSem_state_stack_space t else
       res = SOME wordSem_NotEnoughSpace /\ res1 = SOME (Halt
         (wordLang_Word (n2w 1))) /\ state_clock
       s1 = stackSem_state_clock t1 /\ state_ffi s1 =
         stackSem_state_ffi t1))`,
  CHEAT_TAC);;

let compile_result_def = cake_define_list
  [`compile_result (wordSem_Result w1 w2) = stackSem_Result w1`;
   `compile_result (wordSem_Exception w1 w2) = stackSem_Exception w1`;
   `compile_result wordSem_TimeOut = stackSem_TimeOut`;
   `compile_result wordSem_NotEnoughSpace = stackSem_Halt
  (wordLang_Word (n2w 1))`;
   `compile_result (wordSem_FinalFFI f) = stackSem_FinalFFI f`;
   `compile_result (wordSem_Break k) = stackSem_Break k`;
   `compile_result (wordSem_Continue k) = stackSem_Continue k`;
   `compile_result wordSem_Error = stackSem_Error`];;

(* [local] *)
let Halt_EQ_compile_result = prove
 (`(Halt (wordLang_Word (n2w 1)) = compile_result z <=> z =
  wordSem_NotEnoughSpace) /\
     (good_dimindex (:'a) ==> ~(Halt (wordLang_Word ((n2w 2):'a
       word)) = compile_result z))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:2429-2431: ML code, not ported *)

let push_locals_def = cake_define
  `push_locals l0 l s = stack_fupd (K (StackFrame
  (wordSem_state_locals_size s) l0 l NONE :: stack s))
  (wordSem_state_locals_size_fupd (K (SOME 0))
  (wordSem_state_locals_fupd (K LN) s))`;;

(* [local] *)
let stack_rel_aux_LENGTH = prove
 (`!k len xs ys.
   stack_rel_aux k len xs ys ==>
   LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;


(* [local] *)
let stack_rel_aux_LASTN = prove
 (`!k len xs ys n.
   stack_rel_aux k len xs ys ==>
   stack_rel_aux k len (LASTN n xs) (LASTN n ys)`,
  CHEAT_TAC);;

(* [local] *)
let abs_stack_to_stack_LENGTH = prove
 (`!bs wstack sstack lens stack'.
   abs_stack bs wstack sstack lens = SOME stack' ==>
   handler_val stack' = LENGTH sstack`,
  CHEAT_TAC);;

(* Allow prefixes of (frames of) stacks to be directly dropped
  using handler_val
*)
(* [local] *)
let abs_stack_prefix_drop = prove
 (`!bs wstack sstack lens stack' h wrest k len.
   h <= LENGTH wstack /\
   LASTN h wstack = wrest /\
   abs_stack bs wstack sstack lens = SOME stack' /\
   stack_rel_aux k len wstack stack' ==>
   (let rest = LASTN h stack' in
   let lrest = LASTN h lens in
   let srest = LASTN (handler_val rest) sstack in
   abs_stack bs wrest srest lrest = SOME rest /\
   stack_rel_aux k len wrest rest)`,
  CHEAT_TAC);;

(* [local] *)
let abs_stack_len = prove
 (`!bs wstack sstack lens stack' handler.
   abs_stack bs wstack sstack lens = SOME stack' ==>
   handler_val (LASTN handler stack') <= LENGTH sstack`,
  CHEAT_TAC);;

(* [local] *)
let EL_REVERSE_REWRITE = prove
 (`!l n k. n < LENGTH l /\ k < n ==>
   EL (LENGTH l - n + k) l = EL (n - k - 1) (REVERSE l)`,
  CHEAT_TAC);;

(* [local] *)
let LASTN_LESS = prove
 (`!ls n x xs.
   n + 1 <= LENGTH ls /\
   LASTN (n + 1) ls = x :: xs ==>
   LASTN n ls = xs`,
  CHEAT_TAC);;

(* [local] *)
let ALOOKUP_IFF_MEM = prove
 (`ALL_DISTINCT (MAP FST l) ==>
     (ALOOKUP l q = SOME r <=> MEM (q,r) l)`,
  CHEAT_TAC);;

(* [local] *)
let SORTED_CONS_IMP = prove
 (`SORTED (\x y. FST x > ((FST y):num)) (h :: t) ==>
     ~(MEM h t) /\ SORTED (\x y. FST x > FST y) t /\
     (!x. MEM x t ==> FST h > FST x)`,
  CHEAT_TAC);;

(* [local] *)
let SORTED_IMP_ALL_DISTINCT_LEMMA = prove
 (`!l. SORTED (\x y. FST x > ((FST y):num)) l ==> ALL_DISTINCT (MAP
  FST l)`,
  CHEAT_TAC);;

(* [local] *)
let MEM_toAList_fromAList = prove
 (`SORTED (\x y. FST x > ((FST y):num)) l ==>
     MEM a (toAList (fromAList l)) = MEM a l`,
  CHEAT_TAC);;

(* [local] *)
let SORTED_FST_PERM_IMP_ALIST_EQ = prove
 (`SORTED (\x y. FST x > FST y) l /\
   SORTED (\x y. FST x > FST y) q /\
   PERM (toAList (fromAList l)) q ==>
   q = l`,
  CHEAT_TAC);;

let inter_union_left = prove
 (`wf s ==>
   inter (sptree_union s t) s = s`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stack_rel_raise = prove
 (cake_as_vars (fun () ->
    `n <= LENGTH sstack /\
     handler + 1 <= LENGTH wstack /\ SORTED (\x y. FST x > FST y) l
       /\
     LASTN (handler + 1) wstack = StackFrame m l0 l (SOME
       (h1,l3,l4)) :: rest /\
     abs_stack bs wstack (DROP n sstack) lens = SOME stack /\
     stack_rel_aux k (LENGTH sstack) wstack stack ==>
     (?ex payload.
       LASTN (handler + 1) stack = (SOME ex,payload) :: LASTN
         handler stack /\
       3 <= LENGTH sstack /\ 3 <= handler_val (LASTN (handler + 1)
         stack) /\
       EL (LENGTH sstack - handler_val (LASTN (handler + 1) stack)
         + 1)
             sstack = Loc l3 l4 /\
       ((h1 < LENGTH rest /\
       is_handler_frame (EL (LENGTH rest - (h1 + 1)) rest) ==>
       EL (LENGTH sstack - handler_val (LASTN (handler + 1) stack)
         + 2) sstack =
           wordLang_Word (n2w
             (LENGTH sstack - handler_val (LASTN (h1 + 1) (LASTN
               (handler + 1) stack)))))) /\
       stack_rel_aux k (LENGTH sstack)
         (StackFrame m l0
           (FST (env_to_list (fromAList l) (K I))) NONE :: rest)
             ((NONE,payload) :: LASTN handler stack) /\
       abs_stack bs
         (StackFrame m l0
           (FST (env_to_list (fromAList l) (K I))) NONE :: rest)
         (DROP (LENGTH sstack - handler_val (LASTN (handler + 1)
           stack) + 3)
            sstack) (LASTN (handler + 1) lens) = SOME
              ((NONE,payload) :: LASTN handler stack))`),
  CHEAT_TAC);;

let insert_bitmap_isPREFIX = prove
 (`!bs bs' i.
   insert_bitmap bm bs = (bs',i) ==>
   append (FST bs) <<= append (FST bs')`,
  CHEAT_TAC);;

let wLive_isPREFIX = prove
 (`!a bs c q bs'. wLive a bs c = (q,bs') ==>
   append (FST bs) <<= append (FST bs')`,
  CHEAT_TAC);;

let comp_IMP_isPREFIX = prove
 (`!ac perf c1 bs r q1 bs'.
   comp ac perf c1 bs r = (q1,bs') ==> append (FST bs) <<= append
     (FST bs')`,
  CHEAT_TAC);;

(* [local] *)
let compile_prog_isPREFIX = prove
 (`word_to_stack_compile_prog ac perf x y k bs = (prog,fs,bs1) ==>
   append (FST bs) <<= append (FST bs1)`,
  CHEAT_TAC);;

let compile_word_to_stack_isPREFIX = prove
 (`!code k bs progs1 fs1 bs1.
   compile_word_to_stack ac perf k code bs = (progs1,fs1,bs1) ==>
   append (FST bs) <<= append (FST bs1)`,
  CHEAT_TAC);;

let wMoveAux_thm = prove
 (`evaluate (wMoveAux [] kf,s) = (NONE,s) /\
   evaluate (wMoveAux (x :: xs) kf,s) =
   evaluate (Seq (wMoveSingle x kf) (wMoveAux xs kf),s)`,
  CHEAT_TAC);;

let state_rel_get_var_imp = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra /\
   get_var (2 * x) s = SOME v /\
   x < k ==>
   FLOOKUP (stackSem_state_regs t) x = SOME v`,
  CHEAT_TAC);;

let state_rel_get_var_imp' = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra /\
   get_var n s = SOME v /\
   EVEN n /\
   (n DIV 2) < k ==>
   get_var (n DIV 2) t = SOME v`,
  CHEAT_TAC);;

let state_rel_get_var_imp2 = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   get_var (2 * x) s = SOME v /\
   ~(x < k) ==>
   (EL (stackSem_state_stack_space t + ((f + k) - (x + 1))) (stack
     t) = v)`,
  CHEAT_TAC);;

(* [simp] *)
let state_rel_set_var_k = prove
 (`(word_to_stackProof_state_rel ac k f f' s (set_var (k + 1) v t) lens
  extra <=>
    word_to_stackProof_state_rel ac k f f' s t lens extra) /\
   (word_to_stackProof_state_rel ac k f f' s (set_var k v t) lens
     extra <=>
    word_to_stackProof_state_rel ac k f f' s t lens extra)`,
  CHEAT_TAC);;

(* state_rel_set_var *)
let word_to_stackProof_state_rel_set_var = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra /\
   x < k ==>
   word_to_stackProof_state_rel ac k f f' (set_var (2 * x) v s)
     (set_var x v t) lens extra`,
  CHEAT_TAC);;

let state_rel_set_var' = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra /\
   x < k /\ y = x * 2 ==>
   word_to_stackProof_state_rel ac k f f' (set_var y v s) (set_var
     x v t) lens extra`,
  CHEAT_TAC);;


let state_rel_set_var2 = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   ~(x < k) /\ x < f' + k /\ st = stack t /\ sp =
     stackSem_state_stack_space t ==>
   word_to_stackProof_state_rel ac k f f' (set_var (2 * x) v s)
     (stack_fupd (K (LUPDATE v (sp + ((f + k) - (x + 1))) st)) t)
       lens 0`,
  CHEAT_TAC);;

let wMoveSingle_thm = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   (match x with NONE -> get_var (k + 1) t = SOME v | SOME x ->
     get_var (x * 2) s = SOME v) /\
   (match y with SOME x -> x < f' + k | _13 -> T) ==>
   (?t'.
     evaluate (wMoveSingle (format_var k y,format_var k x)
       (k,f,f'),t) = (NONE,t') /\
     word_to_stackProof_state_rel ac k f f' (match y with NONE -> s |
       SOME y -> set_var (y * 2) v s) t' lens 0 /\
     (y = NONE ==> get_var (k + 1) t' = SOME v) /\
     (~(y = NONE) ==> get_var (k + 1) t' = get_var (k + 1) t) /\
     LENGTH (stack t') = LENGTH (stack t) /\
       stackSem_state_stack_space t' = stackSem_state_stack_space t)`,
  CHEAT_TAC);;

let IS_SOME_get_vars_set_var = prove
 (`!ls s.
    IS_SOME (wordSem_get_vars ls s) ==>
    IS_SOME (get_vars ls (set_var k v s))`,
  CHEAT_TAC);;

let IS_SOME_get_vars_EVERY = prove
 (`!xs s.
     IS_SOME (wordSem_get_vars xs s) <=> EVERY (\x. IS_SOME
       (get_var x s)) xs`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:3127-3128: a theorem that HOL4
   states as the value of an ML expression: with_same_locals *)

let evaluate_wMoveAux_seqsem = prove
 (`!ms s t r.
   word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   (!i v. r (SOME i) = SOME v <=> get_var (2 * i) s = SOME v) /\
   (!v. r NONE = SOME v ==> get_var (k + 1) t = SOME v) /\
   IS_SOME (get_vars (MAP ((*) 2 o THE) (FILTER IS_SOME (MAP SND
     ms))) s) /\
   (match find_index NONE (MAP SND ms) 0 with NONE -> T | SOME i ->
      (match find_index NONE (MAP FST ms) 0 with NONE -> IS_SOME (r
        NONE) | SOME j -> i <= j ==> IS_SOME (r NONE))) /\
   EVERY (\(x,y). !a. (x = SOME a \/ y = SOME a) ==> a < f' + k) ms
     /\
   ALL_DISTINCT (FILTER IS_SOME (MAP FST ms)) ==>
   (?t'.
     evaluate (wMoveAux (MAP (format_var k ## format_var k) ms)
       (k,f,f'),t) = (NONE,t') /\
     word_to_stackProof_state_rel ac k f f'
       (wordSem_set_vars
         (MAP ((*) 2 o THE) (FILTER IS_SOME (MAP FST (REVERSE ms))))
         (MAP THE (MAP (seqsem ms r) (FILTER IS_SOME (MAP FST
           (REVERSE ms)))))
         s) t' lens 0 /\
     LENGTH (stack t') = LENGTH (stack t) /\
       stackSem_state_stack_space t' = stackSem_state_stack_space t)`,
  CHEAT_TAC);;

(* evaluate_SeqStackFree *)
let word_to_stackProof_evaluate_SeqStackFree = prove
 (`stackSem_state_use_stack
      s /\ stackSem_state_stack_space s <= LENGTH (stack s) ==>
       evaluate (SeqStackFree n p,s) = evaluate (Seq
         (stackLang_StackFree n) p,s)`,
  CHEAT_TAC);;

(* get_vars_eq[local] *)
let word_to_stackProof_get_vars_eq = prove
 (`!ls z.
     get_vars ls st = SOME z ==>
     (let lookups = MAP (\x. sptree_lookup x (wordSem_state_locals
       st)) ls in
       EVERY IS_SOME lookups /\
       z = MAP THE lookups)`,
  CHEAT_TAC);;

(* [local] *)
let LAST_add_ret_loc = prove
 (`~(args' = []) ==>
     LAST (add_ret_loc ret args') = LAST args'`,
  CHEAT_TAC);;

(* [local] *)
let call_dest_lemma = prove
 (`~(bad_dest_args dest args) /\
   word_to_stackProof_state_rel ac k f f'
     (s:('a,num#'c,'ffi)wordSem_state) t lens 0 /\
   call_dest dest args (k,f,f') = (q0,dest') /\
   get_vars args s = SOME args' ==>
   (?(t4:('a,'c,'ffi)stackSem_state).
     evaluate (q0,t) = (NONE,t4) /\
     word_to_stackProof_state_rel ac k f f' s t4 lens 0 /\
     LENGTH (stackSem_state_stack t4) = LENGTH (stack t) /\
       stackSem_state_stack_space
     t4 = stackSem_state_stack_space t /\
     (!real_args prog ssize.
       find_code dest
                 (add_ret_loc (ret:(num list#(1 spt#1 spt)#'a
                   wordLang_prog#num#num) option)
                              args':('a word_loc) list)
                                (wordSem_state_code
                 s) (wordSem_state_stack_size s) = SOME
                   (real_args,prog,ssize) ==>
       (?bs i bs2 i2 fs stack_prog.
         word_to_stack_compile_prog ac F prog (LENGTH real_args) k
           (bs,i) = (stack_prog,fs,(bs2,i2)) /\
         LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH
           (stackSem_state_bitmaps t) /\
         isPREFIX (append bs2) (DROP (i - LENGTH (append bs))
           (stackSem_state_bitmaps t)) /\
         the fs ssize = fs /\
         find_code dest' (stackSem_state_regs t4)
           (stackSem_state_code t4) = SOME stack_prog)))`,
  CHEAT_TAC);;

(* [local] *)
let compile_result_NOT_2 = prove
 (`good_dimindex (:'a) ==> ~(compile_result x = Halt (wordLang_Word
  ((n2w 2):'a word)))`,
  CHEAT_TAC);;

let MAP_o_THE_FILTER_IS_SOME = prove
 (`MAP (f o THE) (FILTER IS_SOME ls) =
   MAP (THE o OPTION_MAP f) (FILTER IS_SOME ls)`,
  CHEAT_TAC);;

let MAP_OPTION_MAP_FILTER_IS_SOME = prove
 (`MAP (OPTION_MAP (f:'a->'a)) (FILTER IS_SOME ls) =
   FILTER IS_SOME (MAP (OPTION_MAP f) ls)`,
  CHEAT_TAC);;

let MAP_FILTER_IS_SOME = prove
 (`MAP f (FILTER IS_SOME ls) = MAP (f o SOME o THE) (FILTER IS_SOME
  ls)`,
  CHEAT_TAC);;

(* [local] *)
let TIMES2_DIV2_lemma = prove
 (`windmill moves /\
    EVERY EVEN (MAP FST moves) /\
    EVERY EVEN (MAP SND moves) ==>
    MAP ((*) 2 o THE) (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2
      ## DIV2) moves)))) = MAP THE (FILTER IS_SOME (MAP FST (parmove
      moves)))`,
  CHEAT_TAC);;

let PAIR_MAP_SOME_SWAP = prove
 (`(SOME ## SOME) o (f ## g) = (OPTION_MAP f ## OPTION_MAP g) o (SOME
  ## SOME)`,
  CHEAT_TAC);;

let IS_SOME_o_OPTION_MAP = prove
 (`IS_SOME o OPTION_MAP f = IS_SOME`,
  CHEAT_TAC);;

(* [local] *)
let parsem_parmove_DIV2_lemma = prove
 (`windmill moves /\
    EVERY EVEN (MAP FST moves) /\
    EVERY EVEN (MAP SND moves) ==>
    MAP (parsem (MAP (SOME ## SOME) (MAP (DIV2 ## DIV2) moves)) r)
       (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2)
         moves)))) =
    (MAP (parsem (MAP (SOME ## SOME) moves) (r o OPTION_MAP DIV2))
      (FILTER IS_SOME (MAP FST (parmove moves))))`,
  CHEAT_TAC);;

let ALOOKUP_MAP_any = prove
 (`!f k h ls a x.
   (INJ k (a INSERT (set_of_list (MAP FST ls))) UNIV) /\
   (!x y. MEM (x,y) ls ==> f (x,y) = (k x,h (k x) y)) /\ k a = x ==>
   ALOOKUP (MAP f ls) x = OPTION_MAP (h x) (ALOOKUP ls a)`,
  CHEAT_TAC);;

let wf_alist_insert = prove
 (`!xs ys z. wf z ==> wf (alist_insert xs ys z)`,
  CHEAT_TAC);;

let ALOOKUP_MAP_INJ_FST = prove
 (`!ls f x k.
   INJ (FST o f) (x INSERT set_of_list ls) UNIV /\
   FST (f x) = k ==>
   ALOOKUP (MAP f ls) k =
   ALOOKUP (MAP (\x. (x,SND (f x))) ls) x`,
  CHEAT_TAC);;

let ALOOKUP_ID_TABULATE = prove
 (`ALOOKUP (MAP (\x. (x,x)) ls) x =
   (if MEM x ls then SOME x else NONE)`,
  CHEAT_TAC);;

let alist_insert_get_vars = prove
 (`!moves s x ls.
   ALL_DISTINCT (MAP FST moves) /\
   get_vars (MAP SND moves) s = SOME x /\
   ALL_DISTINCT (FILTER IS_SOME ls) /\
   wf (wordSem_state_locals s) /\
   (!x. MEM (SOME x) ls ==> MEM x (MAP FST moves)) /\
   (!x y. MEM (x,y) moves /\ ~(x = y) ==> MEM (SOME x) ls) ==>
   alist_insert
     (MAP THE (FILTER IS_SOME ls))
     (MAP (\x. THE (get_var (THE (ALOOKUP moves (THE x))) s)) (FILTER
       IS_SOME ls)) (wordSem_state_locals s) =
   alist_insert (MAP FST moves) x (wordSem_state_locals s)`,
  CHEAT_TAC);;

(* [local] *)
let wf_fromList2 = prove
 (`!ls. wf (fromList2 ls)`,
  CHEAT_TAC);;

let wStackLoad_append = prove
 (`wStackLoad (l1 ++ l2) = wStackLoad l1 o (wStackLoad l2)`,
  CHEAT_TAC);;

let wRegWrite1_thm1 = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   m < f' + k /\
   (!n. n <= k ==>
     evaluate (kont n,t) = (NONE,set_var n v t)) ==>
   (?t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var (2 * m) v s) t'
     lens 0 /\
   LENGTH (stack t') = LENGTH (stack t) /\
     stackSem_state_stack_space t' = stackSem_state_stack_space t)`,
  CHEAT_TAC);;

let wRegWrite1_thm1_weak = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   m < f' + k /\
   (!n. n <= k ==>
     evaluate (kont n,t) = (NONE,set_var n v t)) ==>
   (?t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var (2 * m) v s) t'
     lens 0)`,
  CHEAT_TAC);;

let wRegWrite1_thm2 = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   m < f' + k /\
   (!n. n <= k ==>
     evaluate (kont n,t) = (NONE,set_var 0 v' (set_var n v t))) ==>
   (?t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var 0 v' (set_var (2 *
     m) v s)) t' lens 0 /\
   LENGTH (stack t') = LENGTH (stack t) /\
     stackSem_state_stack_space t' = stackSem_state_stack_space t)`,
  CHEAT_TAC);;
(*
Theorem wRegWrite1_thm3 =
  wRegWrite1_thm2
  |> Q.INST [`t`|-> `set_var v1 v2 t`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm4 =
  wRegWrite1_thm1
  |> Q.INST [`t`|-> `set_var v1 v2 t`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm5 =
  wRegWrite1_thm2
  |> Q.INST [`t`|-> `set_var v1 v2 (set_var v3 v4 t)`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm6 =
  wRegWrite1_thm1
  |> Q.INST [`t`|-> `set_var v1 v2 (set_var v3 v4 t)`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];
*)
let wRegWrite2_thm1 = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   m < f' + k /\
   (!n. n <= k + 1 ==>
     evaluate (kont n,t) = (NONE,set_var n v t)) ==>
   (?t'.
   evaluate (wRegWrite2 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var (2 * m) v s) t'
     lens 0)`,
  CHEAT_TAC);;

(* state_rel_mem_store *)
let word_to_stackProof_state_rel_mem_store = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra /\
   mem_store a b s = SOME s' ==>
   (?t'.
     mem_store a b t = SOME t' /\
     word_to_stackProof_state_rel ac k f f' s' t' lens extra)`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:3847-3890: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:3892-3937: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:3938-3970: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:3971-3995: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:3996-4023: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:4024-4047: code that the source
   has in a comment *)
(*
Theorem wStackLoad_thm3 =
 wStackLoad_thm2
 |> Q.INST [`t`|->`set_var v1 v2 t`]
 |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const]
*)
let _ = size_thms "wordLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 word_to_stackProofScript.sml:4061-4066: the tactic that
   proves the termination *)
let map_var_def = cake_define_list_try (fun () ->
  `MEASURE (wordLang_exp_size ARB o SND)`)
  [`map_var f (wordLang_Var num') = Var (f num')`;
   `map_var f (wordLang_Load exp) = Load (map_var f exp)`;
   `map_var f (wordLang_Op wop ls) = wordLang_Op wop (MAP (map_var f)
  ls)`;
   `map_var f (wordLang_Shift sh e1 e2) = Shift sh (map_var f e1)
  (map_var f e2)`;
   `map_var f (wordLang_Const c) = (Const c:'a wordLang_exp)`;
   `map_var f (wordLang_Lookup v) = wordLang_Lookup v`];;

let the_words_EVERY_IS_SOME_Word = prove
 (`!ls x. the_words ls = SOME x ==> (!a. MEM a ls ==> (?w. a = SOME
  (wordLang_Word w)))`,
  CHEAT_TAC);;

let the_words_SOME_eq = prove
 (`!ls x. the_words ls = SOME x ==> x = MAP (\x. match x with SOME
  (wordLang_Word y) -> y) ls`,
  CHEAT_TAC);;

let the_words_MAP_exists = prove
 (`!ls x a f.
   the_words (MAP f ls) = SOME x /\
   MEM a ls ==>
   (?w. f a = SOME (wordLang_Word w))`,
  CHEAT_TAC);;
(* HOL4 word_to_stackProofScript.sml:4089-4385: code that the source
   has in a comment *)

let state_rel_with_memory = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra ==>
   word_to_stackProof_state_rel ac k f f' (state_memory_fupd (K m)
     s) (state_memory_fupd (K m) t) lens extra`,
  CHEAT_TAC);;

let word_exp_Op_SOME_Word = prove
 (`word_exp s (wordLang_Op op wexps) = SOME x ==> (?w. x =
  wordLang_Word w)`,
  CHEAT_TAC);;

(* state_rel_get_fp_var *)
let word_to_stackProof_state_rel_get_fp_var = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra ==>
   get_fp_var n s = get_fp_var n t`,
  CHEAT_TAC);;

(* state_rel_set_fp_var *)
let word_to_stackProof_state_rel_set_fp_var = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra ==>
   word_to_stackProof_state_rel ac k f f' (set_fp_var n v s)
     (set_fp_var n v t) lens extra`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wStackLoad_wReg1 = prove
 (`wReg1 r (k,f,f') = (x,r') /\
   EVEN r /\
   get_var r (s:('a,num#'c,'ffi)wordSem_state) = SOME c /\
   word_to_stackProof_state_rel ac k f f' s t lens 0 ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (wStackLoad x Skip,t) = (NONE,t') /\ state_clock
   t = stackSem_state_clock t' /\
   word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
   LENGTH (stackSem_state_stack t') = LENGTH (stack t) /\
     stackSem_state_stack_space t' = stackSem_state_stack_space t /\
     stackSem_state_bitmaps
   t' = stackSem_state_bitmaps t /\
    (!r. ~(r = k) ==> get_var r t' = get_var r t) /\ ~(r' = k + 1) /\
   get_var r' t' = SOME c)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wStackLoad_wReg1_with_const = prove
 (`wReg1 r (k,f,f') = (x,r') /\
   EVEN r /\
   word_exp (s:('a,num#'c,'ffi)wordSem_state) (wordLang_Op asm_Add
     [Var r; Const c]) = SOME (
   wordLang_Word w) /\
   word_to_stackProof_state_rel ac k f f' s t lens 0 ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (wStackLoad x Skip,t) = (NONE,t') /\ state_clock
   t = stackSem_state_clock t' /\
   word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
   LENGTH (stackSem_state_stack t') = LENGTH (stack t) /\
     stackSem_state_stack_space t' = stackSem_state_stack_space t /\
     ~(r' = k + 1) /\
   (stackSem_word_exp t' (wordLang_Op asm_Add [Var r'; Const c])) =
     SOME (w))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wStackLoad_clock = prove
 (`!x t.
   evaluate (wStackLoad x Skip,state_clock_fupd (K clk) t) =
   (I ## (\s. state_clock_fupd (K clk) s)) (evaluate (wStackLoad x
     Skip,t))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wStackLoad_wReg2 = prove
 (`wReg2 r (k,f,f') = (x,r') /\
   EVEN r /\
   get_var r (s:('a,num#'c,'ffi)wordSem_state) = SOME c /\
   word_to_stackProof_state_rel ac k f f' s t lens 0 ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (wStackLoad x Skip,t) = (NONE,t') /\ state_clock
   t = stackSem_state_clock t' /\ stackSem_state_bitmaps
   t = stackSem_state_bitmaps t' /\
   word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
   LENGTH (stackSem_state_stack t') = LENGTH (stack t) /\
     stackSem_state_stack_space t' = stackSem_state_stack_space t /\
   (!r. ~(r = k + 1) ==> get_var r t' = get_var r t) /\
   (!r c. ~(r = k + 1) ==>
   word_exp t' (wordLang_Op asm_Add [Var r; Const c]) = word_exp t
     (wordLang_Op asm_Add [Var r; Const c])) /\
   get_var r' t' = SOME c)`,
  CHEAT_TAC);;

let evaluate_wStackLoad_seq = prove
 (`!ls prog s.
   evaluate (wStackLoad ls prog,s) =
   evaluate (Seq (wStackLoad ls Skip) prog,s)`,
  CHEAT_TAC);;

(*The last two are weakened to allow easy irule
*)
(* [local] *)
let evaluate_wStackStore_wReg1 = prove
 (`wReg1 r (k,f,f') = (x,r') /\
   EVEN r /\
   r < 2 * f' + 2 * k /\
   word_to_stackProof_state_rel ac k f f'
     (s:('a,num#'c,'ffi)wordSem_state) (t:('a,'c,'ffi)stackSem_state)
     lens 0 /\
   LENGTH (stackSem_state_stack t) = LENGTH_t_stack /\
     stackSem_state_stack_space
   t = t_stack_space ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (wStackStore x Skip,(set_var r' c t)) = (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var r c s) t' lens 0
     /\
   LENGTH (stackSem_state_stack t') = LENGTH_t_stack /\
     stackSem_state_stack_space t' = t_stack_space)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wStackStore_wReg1_strong = prove
 (`wReg1 r (k,f,f') = (x,r') /\
   EVEN r /\
   r < 2 * f' + 2 * k /\
   word_to_stackProof_state_rel ac k f f'
     (s:('a,num#'c,'ffi)wordSem_state) (t:('a,'c,'ffi)stackSem_state)
     lens 0 ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (wStackStore x Skip,(set_var r' c t)) = (NONE,set_var r'
     c t') /\
   word_to_stackProof_state_rel ac k f f' (set_var r c s) (set_var r'
     c t') lens 0 /\
   LENGTH (stackSem_state_stack t') = LENGTH (stackSem_state_stack
     t) /\ stackSem_state_stack_space t' = stackSem_state_stack_space
     t)`,
  CHEAT_TAC);;


(* [local] *)
let evaluate_wStackStore_wReg1_new = prove
 (`wReg1 r (k,f,f') = (x,r') /\
   EVEN r /\
   r < 2 * f' + 2 * k /\
   (?t'.
   evaluate (kont,t) = (NONE,set_var r' c t') /\
   word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
   LENGTH (stackSem_state_stack t') = LENGTH_t_stack /\
     stackSem_state_stack_space t' = t_stack_space) ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (Seq kont (wStackStore x Skip),t) = (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var r c s) t' lens 0
     /\
   LENGTH (stackSem_state_stack t') = LENGTH_t_stack /\
     stackSem_state_stack_space t' = t_stack_space)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wStackStore_wReg2_new = prove
 (`wReg2 r (k,f,f') = (x,r') /\
   EVEN r /\
   r < 2 * f' + 2 * k /\
   (?t'.
   evaluate (kont,t) = (NONE,set_var r' c t') /\
   word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
   LENGTH (stackSem_state_stack t') = LENGTH_t_stack /\
     stackSem_state_stack_space t' = t_stack_space) ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (Seq kont (wStackStore x Skip),t) = (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var r c s) t' lens 0
     /\
   LENGTH (stackSem_state_stack t') = LENGTH_t_stack /\
     stackSem_state_stack_space t' = t_stack_space)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wStackStore_wReg1_0 = prove
 (`wReg1 r (k,f,f') = (x,r') /\
   EVEN r /\
   r < 2 * f' + 2 * k /\
   word_to_stackProof_state_rel ac k f f'
     (s:('a,num#'c,'ffi)wordSem_state) (t:('a,'c,'ffi)stackSem_state)
     lens 0 /\
   LENGTH (stackSem_state_stack t) = LENGTH_t_stack /\
     stackSem_state_stack_space
   t = t_stack_space ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (wStackStore x Skip,(set_var 0 c1 (set_var r' c t))) =
     (NONE,t') /\
   word_to_stackProof_state_rel ac k f f' (set_var 0 c1 (set_var r c
     s)) t' lens 0 /\
   LENGTH (stackSem_state_stack t') = LENGTH_t_stack /\
     stackSem_state_stack_space t' = t_stack_space)`,
  CHEAT_TAC);;

let evaluate_wRegWrite1_seq = prove
 (`evaluate (wRegWrite1 g r (k,f,f'),t) =
   (let (l,n) = wReg1 r (k,f,f') in
   evaluate ((Seq (g n) (wStackStore l Skip)),t))`,
  CHEAT_TAC);;

let evaluate_wRegWrite2_seq = prove
 (`evaluate (wRegWrite2 g r (k,f,f'),t) =
   (let (l,n) = wReg2 r (k,f,f') in
   evaluate ((Seq (g n) (wStackStore l Skip)),t))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:4688-5130: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_wInst *)

let state_rel_set_store = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra /\ ~(v =
  Handler) ==>
   word_to_stackProof_state_rel ac k f f' (set_store v x s)
     (set_store v x t) lens extra`,
  CHEAT_TAC);;

(*For calls*)
(* [local] *)
let get_vars_fromList2_eq = prove
 (`get_vars (GENLIST (\x. 2 * x) (LENGTH args)) s = SOME x /\
     sptree_lookup n (fromList2 x) = SOME y ==>
     sptree_lookup n (wordSem_state_locals s) = SOME y`,
  CHEAT_TAC);;

(*For returning calls*)
(* [local] *)
let get_vars_fromList2_eq_cons = prove
 (`get_vars (GENLIST (\x. 2 * (x + 1)) (LENGTH args)) s = SOME x /\
     sptree_lookup n (fromList2 (Loc x3 x4 :: x)) = SOME y /\ ~(n =
       0) ==>
     sptree_lookup n (wordSem_state_locals s) = SOME y`,
  CHEAT_TAC);;

(* [local] *)
let lookup_fromList2_prefix = prove
 (`!x z y.
   IS_PREFIX z x /\
   sptree_lookup n (fromList2 x) = SOME y ==>
   sptree_lookup n (fromList2 z) = SOME y`,
  CHEAT_TAC);;


(* HOL4 word_to_stackProofScript.sml:5203-5232: code that the source
   has in a comment *)

(* [local] *)
let evaluate_call_dest_clock = prove
 (`call_dest dest args (k,f,f') = (q0,dest') ==>
   evaluate (q0,stackSem_state_clock_fupd (K clk) t) =
   (I ## (\t. stackSem_state_clock_fupd (K clk) t)) (evaluate
     (q0,(t:('a,'c,'ffi)stackSem_state)))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_wLive_clock = prove
 (`!x t q bs bs'.
   wLive x bs kf = (q,bs') ==>
   evaluate (q,stackSem_state_clock_fupd (K clk) t) =
   (FST (evaluate (q,(t:('a,'c,'ffi)stackSem_state))),
    (state_clock_fupd (K clk) (SND (evaluate (q,t)))))`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_IMP_LENGTH = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra ==>
   LENGTH lens = LENGTH (stack s)`,
  CHEAT_TAC);;

(*NB this lemma can be slightly simpler with
EL (x + offset) stack' = EL (x) stack'*)
(* [local] *)
let evaluate_stack_move = prove
 (`!n tar t offset.
   stackSem_state_use_stack
   t /\ stackSem_state_stack_space
   t + tar + n + offset <= LENGTH (stack t) /\
   n <= offset ==>
   (?t'.
   evaluate (stack_move n tar offset k Skip,t) = (NONE,t') /\
   (?t'_stack t'_regs.
   t' = stackSem_state_regs_fupd (K t'_regs) (stack_fupd (K t'_stack)
     t) /\
   (
    // All regs fixed except k
    !i. ~(i = k) ==> get_var i t' = get_var i t) /\
   // Unnecessary
   LENGTH (stack t) = LENGTH t'_stack /\ stackSem_state_stack_space
   t' = stackSem_state_stack_space t /\
   // Rest of stack is unchanged
   DROP (stackSem_state_stack_space t' + tar + n) t'_stack =
   DROP (stackSem_state_stack_space t + tar + n) (stack t) /\
   // Copying the first frame
   (let stack' = DROP (stackSem_state_stack_space t' + tar) t'_stack
     in
   let stack' = DROP (stackSem_state_stack_space t + tar) (stack t)
     in
   !x. x < n ==>
    EL (x + offset) stack' = EL (x) stack')))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_stack_move_seq = prove
 (`!a b c d prog (t:('a,'c,'ffi)stackSem_state).
   evaluate (stack_move a b c d prog,t) =
   evaluate (Seq prog (stack_move a b c d Skip),t)`,
  CHEAT_TAC);;

let evaluate_stack_move_clock = prove
 (`!a b c d (t:('a,'c,'ffi)stackSem_state).
     let prog = stack_move a b c d Skip in
     evaluate (prog,stackSem_state_clock_fupd (K clk) t) =
     (FST (evaluate (prog,(t:('a,'c,'ffi)stackSem_state))),
      (state_clock_fupd (K clk) (SND (evaluate (prog,t)))))`,
  CHEAT_TAC);;
  (*get_var_set_var?*)
(* HOL4 word_to_stackProofScript.sml:5359: a proof *)

(* [local] *)
let pop_env_ffi = prove
 (`wordSem_pop_env s = SOME s' ==> state_ffi
   s = state_ffi s'`,
  CHEAT_TAC);;

(* [local] *)
let stack_rel_DROP_NONE = prove
 (`word_to_stackProof_stack_rel k whandler (StackFrame n l0 l NONE ::
  wstack) shandler sstack len bs (f' :: lens) ==>
   word_to_stackProof_stack_rel k whandler wstack shandler (DROP
     (f' + 1) sstack) len bs lens`,
  CHEAT_TAC);;

(* [local] *)
let stack_rel_DROP_SOME = prove
 (`word_to_stackProof_stack_rel k whandler (StackFrame n l0 l (SOME
  (whandler',b,c)) :: wstack) shandler sstack len bs (f' :: lens) ==>
   word_to_stackProof_stack_rel k whandler' wstack (SOME (EL 2
     sstack)) (DROP (f' + 4) sstack) len bs lens`,
  CHEAT_TAC);;

(* [local] *)
let LAST_GENLIST_evens = prove
 (`~(n = 0) ==>
     (let reg = LAST (GENLIST (\x. 2 * (x + 1)) n) in ~(reg = 0) /\
       EVEN reg)`,
  CHEAT_TAC);;

(* [local] *)
let stack_rel_cons_LEN_NONE = prove
 (`word_to_stackProof_stack_rel k whandler (StackFrame n l0 l NONE ::
  wstack) shandler sstack len bs (f' :: lens) ==>
   f' + 1 <= LENGTH sstack`,
  CHEAT_TAC);;

(* [local] *)
let stack_rel_cons_LEN_SOME = prove
 (`word_to_stackProof_stack_rel k whandler (StackFrame n l0 l (SOME
  (a,b,c)) :: wstack) shandler sstack len bs (f' :: lens) ==>
   f' + 4 <= LENGTH sstack`,
  CHEAT_TAC);;

let stack_rel_cons_locals_size = prove
 (`word_to_stackProof_stack_rel k whandler (StackFrame n l0 l opt ::
  t'')
     shandler rest_of_stack len
     bitmaps (f' :: lens) ==>
   the (f' + 1) n = (f' + 1)`,
  CHEAT_TAC);;

let IS_SOME_OPTION_MAP2_EQ = prove
 (`IS_SOME (OPTION_MAP2 f A B) <=>
   (IS_SOME A /\ IS_SOME B)`,
  CHEAT_TAC);;

(* [local] *)
let DROP_SUB = prove
 (`a <= LENGTH ls /\ b <= a ==>
   DROP (a - b) ls = (DROP (a - b) (TAKE a ls)) ++ DROP a ls`,
  CHEAT_TAC);;

(* [local] *)
let DROP_SUB2 = prove
 (`!a ls b.
   b <= a /\
   a = LENGTH ls ==>
   (?rest.
   DROP (a - b) ls = rest /\ LENGTH rest = b)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_PushHandler = prove
 (`3 <= stackSem_state_stack_space t /\
   word_to_stackProof_state_rel ac k 0 0
     (wordSem_state_locals_size_fupd (K (SOME 0))
     (wordSem_state_locals_fupd (K LN) (wordSem_push_env x' NONE s))) t
     (f' :: lens) 0 /\
   loc_check (state_code t) (x''2,x''3) ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate (PushHandler F (x''2:num) (x''3:num) (k,(f:num),f'),t) =
     (NONE,t') /\
   t' = state_store_fupd (K (stackSem_state_store t')) (stack_fupd (K
     (stackSem_state_stack t')) (stackSem_state_regs_fupd (K
     (stackSem_state_regs t')) (stackSem_state_stack_space_fupd (K
     (stackSem_state_stack_space t')) t))) /\
   (!n.
     n < LENGTH (stack t) - stackSem_state_stack_space t ==>
     EL n (DROP (stackSem_state_stack_space t) (stack t)) = EL (n +
       3) (DROP (stackSem_state_stack_space t') (stackSem_state_stack
       t'))) /\
   (!i. ~(i = k) ==> get_var i t' = get_var i t) /\
     stackSem_state_stack_space
   t' + 3 = stackSem_state_stack_space t /\
   LENGTH (stackSem_state_stack t') = LENGTH (stack t) /\
   word_to_stackProof_state_rel ac k 0 0
     (wordSem_state_locals_size_fupd (K (SOME 0))
     (wordSem_state_locals_fupd (K LN) (wordSem_push_env x' (SOME
     (x''0,(x''1:'a wordLang_prog),x''2,x''3)) s))) t' (f' :: lens) 0)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_PushHandler_clock = prove
 (`!(t:('a,'c,'ffi)stackSem_state).
   evaluate (PushHandler F a b
     (k,(f:num),(f':num)),stackSem_state_clock_fupd (K clk) t) =
   (FST (evaluate (PushHandler F a b
     (k,(f:num),(f':num)),(t:('a,'c,'ffi)stackSem_state))),
    (state_clock_fupd (K clk) (SND (evaluate (PushHandler F a b
      (k,(f:num),(f':num)),t)))))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_PopHandler_clock = prove
 (`!(t:('a,'c,'ffi)stackSem_state).
   let prog = PopHandler F (k,(f:num),(f':num)) Skip in
   evaluate (prog,stackSem_state_clock_fupd (K clk) t) =
   (FST (evaluate (prog,(t:('a,'c,'ffi)stackSem_state))),
    (state_clock_fupd (K clk) (SND (evaluate (prog,t)))))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_PopHandler_seq = prove
 (`!prog (t:('a,'c,'ffi)stackSem_state).
   evaluate (PopHandler F (k,f,f') prog,t) =
   evaluate (Seq (PopHandler F (k,f,f') Skip) prog,t)`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_MEM_toAList_fromAList = prove
 (`ALL_DISTINCT (MAP FST ls) ==>
   (MEM x (toAList (fromAList ls)) <=>
   MEM x ls)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_code_domain = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra ==>
   domain (state_code s) SUBSET domain (state_code t)`,
  CHEAT_TAC);;

let get_labels_wStackLoad = prove
 (`!xs p. stackSem_get_labels (wStackLoad xs p) = stackSem_get_labels
  p`,
  CHEAT_TAC);;

let loc_check_SUBSET = prove
 (`subspt s t ==>
   loc_check s SUBSET loc_check t`,
  CHEAT_TAC);;

let MAP_FST_compile_word_to_stack = prove
 (`!ac perf k ps bm ps' bm'.
    compile_word_to_stack ac perf k ps bm = (ps',bm') ==> MAP FST
      ps' = MAP FST ps`,
  CHEAT_TAC);;

let wLive_LENGTH = prove
 (`!a bs c q bs'.
   wLive a bs c = (q,bs') /\
   LENGTH (append (FST bs)) <= SND bs ==>
   LENGTH (append (FST bs')) <= SND bs' /\
   SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append
     (FST bs'))`,
  CHEAT_TAC);;

let comp_IMP_LENGTH = prove
 (`!ac perf c1 bs r q1 bs'.
   comp ac perf c1 bs r = (q1,bs') /\
   LENGTH (append (FST bs)) <= SND bs ==>
   LENGTH (append (FST bs')) <= SND bs' /\
   SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append
     (FST bs'))`,
  CHEAT_TAC);;

let compile_prog_LENGTH = prove
 (`word_to_stack_compile_prog ac perf prog arg reg (bm,i) =
  (prog',fs',bm',i') /\
   LENGTH (append bm) <= i ==>
   LENGTH (append bm') <= i' /\
   i - LENGTH (append bm) = i' - LENGTH (append bm')`,
  CHEAT_TAC);;

let compile_word_to_stack_IMP_LENGTH = prove
 (`!code k bm i progs fs bm' i'.
   compile_word_to_stack ac perf k code (bm,i) = (progs,fs,bm',i') /\
   LENGTH (append bm) <= i ==>
   LENGTH (append bm') <= i' /\
   i - LENGTH (append bm) = i' - LENGTH (append bm')`,
  CHEAT_TAC);;

(* Used in backendProof *)
let compile_word_to_stack_bitmaps = prove
 (`word_to_stack_compile c F p = (bitmaps,c2,prog1) ==>
    (match bitmaps with [] -> F | h :: v1 -> (n2w 4) = h) /\
      word_to_stack_config_bitmaps_length c2 = LENGTH bitmaps`,
  CHEAT_TAC);;

(* [local] *)
let compile_word_to_stack_IMP_ALOOKUP = prove
 (`!code k bs i progs fs bs' i' n arg_count word_prog x.
     compile_word_to_stack ac perf k code (bs,i) = (progs,fs,bs',i')
       /\
     ALOOKUP code n = SOME (arg_count,word_prog) /\
     LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH x /\
     isPREFIX (append bs') (DROP (i - LENGTH (append bs)) x) ==>
     (?bs i bs2 i2 f stack_prog.
       word_to_stack_compile_prog ac perf word_prog arg_count k
         (bs,i) = (stack_prog,f,(bs2,i2)) /\
       LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH x
         /\
       isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) x) /\
       ALOOKUP progs n = SOME stack_prog)`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:5719-5752: the ML values that
   the definitions below antiquote *)

(* HOL4 word_to_stackProofScript.sml:5754: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:5756-5787: a theorem whose
   statement the port cannot state yet: comp_correct *)


(* HOL4 word_to_stackProofScript.sml:5790-5796: a proof *)

(* HOL4 word_to_stackProofScript.sml:5798-5853: a proof *)

let chunk_to_bits_bound = prove
 (`!ws.
     LENGTH ws < dimindex (:'a) ==> FAPPLY
     (chunk_to_bits ws:'a word) (LENGTH ws) /\
     (!i. LENGTH ws < i /\ i < dimindex (:'a) ==> ~(FAPPLY
       (chunk_to_bits ws:'a word) i))`,
  CHEAT_TAC);;

let chunk_to_bits_0 = prove
 (`FAPPLY
     (chunk_to_bits ((b,w) :: words)) 0 <=> b`,
  CHEAT_TAC);;

let copy_words_for_pattern_thm = prove
 (`!words xs a off ys dm m.
     LENGTH words < dimindex (:'a) /\ const_addresses a words dm ==>
     copy_words_for_pattern (chunk_to_bits words) (LENGTH xs) (a:'a
       word) off
       (xs ++ MAP SND words ++ ys) dm m =
     SOME (LENGTH xs + LENGTH words,
           a + bytes_in_word * n2w (LENGTH words),
           const_writes a off words m)`,
  CHEAT_TAC);;

let word_msb_chunk_to_bits = prove
 (`LENGTH words < dimindex (:'a) /\ good_dimindex (:'a) ==>
   word_msb (chunk_to_bits words:'a word) = (LENGTH words =
     dimindex (:'a) - 1)`,
  CHEAT_TAC);;

let copy_words = prove
 (`const_addresses a words dm /\ good_dimindex (:'a) /\
   LENGTH words < dimindex (:'a) ==>
   copy_words (LENGTH xs) a off (xs ++ chunk_to_bitmap words ++ ys)
     dm m =
     (if LENGTH words = dimindex (:'a) - 1 then
       copy_words (LENGTH xs + (LENGTH words + 1))
             (a + bytes_in_word * n2w (LENGTH words)) off
             (xs ++ chunk_to_bitmap words ++ ys) dm
             (const_writes a off words m) else
       SOME (a + bytes_in_word * n2w (LENGTH words),
             const_writes (a:'a word) off words m))`,
  CHEAT_TAC);;

let const_writes_append = prove
 (`!h t a off m.
     const_writes a off (h ++ t) m =
     const_writes (a + bytes_in_word * n2w (LENGTH h)) off t
       (const_writes a off h m)`,
  CHEAT_TAC);;

let const_addresses_append = prove
 (`!xs ys dm a.
     const_addresses a (xs ++ ys) dm <=>
     const_addresses a xs dm /\
     const_addresses (a + bytes_in_word * n2w (LENGTH xs)) ys dm`,
  CHEAT_TAC);;

let copy_words_correct = prove
 (`!words xs ys a off dm m.
     const_addresses a words dm /\ good_dimindex (:'a) ==>
     copy_words (LENGTH xs) (a:'a word) off
       (xs ++ const_words_to_bitmap words (LENGTH words) ++ ys) dm m
         =
     SOME (a + bytes_in_word * n2w (LENGTH words),const_writes a
       off words m)`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:6040-6051: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:6053-6117: a proof *)

(* HOL4 word_to_stackProofScript.sml:6119-6130: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:6315-6326: a proof *)

(* HOL4 word_to_stackProofScript.sml:6328-6331: a proof *)

(* HOL4 word_to_stackProofScript.sml:6333-6354: a proof *)

(* HOL4 word_to_stackProofScript.sml:6356-6374: a proof *)

(* HOL4 word_to_stackProofScript.sml:6376-6392: a proof *)
  (*TODO remove by changing word_exp_def*)
(* HOL4 word_to_stackProofScript.sml:6394: a proof *)
  (*TODO remove by changing get_store_def*)
(* HOL4 word_to_stackProofScript.sml:6396-6403: a proof *)

(* HOL4 word_to_stackProofScript.sml:6405-6408: a proof *)

(* HOL4 word_to_stackProofScript.sml:6410-6420: a proof *)

(* HOL4 word_to_stackProofScript.sml:6422-6427: a proof *)

(* HOL4 word_to_stackProofScript.sml:6429-6492: a proof *)

(* HOL4 word_to_stackProofScript.sml:6494-6579: a proof *)

let stack_rel_aux_stack_size = prove
 (`!len k frame bits.
   stack_rel_aux len k frame bits ==>
   the (handler_val bits) (stack_size frame) = handler_val bits`,
  CHEAT_TAC);;

let abs_stack_CONS_NIL = prove
 (`abs_stack bm (x :: rest) [] l = NONE`,
  CHEAT_TAC);;

(* [local] *)
let SUB_ADD_EQ = prove
 (`a <= b ==> a + (b - (a:num)) = b`,
  CHEAT_TAC);;

let abs_stack_LENGTH = prove
 (`!bitmaps wstack tstack lens astack.
   abs_stack bitmaps wstack tstack lens = SOME astack ==>
   handler_val astack = LENGTH tstack`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let abs_stack_empty' = prove
 (cake_as_vars (fun () ->
    `abs_stack bs xs [] lens = SOME stack <=> F`),
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:6626-6741: a proof *)

(* [local] *)
let evaluate_const_inst = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra ==>
   (?(t':('a,'c,'ffi)stackSem_state).
   evaluate ((\r w. Inst (asm_Const r w)) (k + 1) i,t) = (NONE,t') /\
     state_clock
   t = stackSem_state_clock t' /\
   word_to_stackProof_state_rel ac k f f' s t' lens extra /\
   LENGTH (stackSem_state_stack t') = LENGTH (stack t) /\
     stackSem_state_stack_space t' = stackSem_state_stack_space t /\
   stackSem_get_var (k + 1) t' = (SOME (wordLang_Word i)))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_const_inst_clock = prove
 (`evaluate ((\r w. Inst (asm_Const r w)) k i,state_clock_fupd (K clk)
  t) =
   (I ## (\t. state_clock_fupd (K clk) t)) (evaluate ((\r w. Inst
     (asm_Const r w)) k i,t))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:6767-6773: a proof *)
  (* prevent splitting *)
(* HOL4 word_to_stackProofScript.sml:6775-6903: a proof *)

(* HOL4 word_to_stackProofScript.sml:6905-6923: a proof *)

let EXISTS_PULL_FORALL1 = prove
 (`((?x. !y. (Abbrev (y = P)) ==> Q x y) <=> (!y. (Abbrev (y = P)) ==>
  (?x. Q x y)))`,
  CHEAT_TAC);;

let EXISTS_PULL_FORALL2 = prove
 (`((?x. !y z. P = (y,z) ==> Q x y z) <=> (!y z. P = (y,z) ==> (?x. Q
  x y z)))`,
  CHEAT_TAC);;

let EXISTS_PULL_FORALL3 = prove
 (`((?x. !y z a. P = (y,z,a) ==> Q x y z a) <=> (!y z a. P = (y,z,a)
  ==> (?x. Q x y z a)))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:6943-7070: a proof *)

(* HOL4 word_to_stackProofScript.sml:7072-7096: a proof *)

(* HOL4 word_to_stackProofScript.sml:7098-7123: a proof *)

(* HOL4 word_to_stackProofScript.sml:7125-7164: a proof *)

let flat_exp_conventions_ShareInst_exp_simp = prove
 (`flat_exp_conventions (wordLang_ShareInst op v exp) ==>
   (?ad. exp = Var ad) \/
   (?ad offset. exp = wordLang_Op asm_Add [Var ad; Const offset])`,
  CHEAT_TAC);;

let word_exp_Op_Add_0 = prove
 (`wordSem_word_exp s exp = SOME (wordLang_Word x) <=>
     word_exp s (wordLang_Op asm_Add [exp; Const (n2w 0)]) = SOME
       (wordLang_Word x)`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:7186-7205: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_ShareInst_Var_eq_Op_Add *)

let share_load_lemma1 = prove
 (`share_inst op (2 * v) ad' s = (res,s1) /\
   word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   v < f' + k /\
   k <= v /\
   (op = Load \/ op = asm_Load8 \/ op = asm_Load16 \/ op =
     asm_Load32) /\ ~(res = SOME Error) ==>
   (?t1. sh_mem_op op k ad' t =
       (OPTION_MAP compile_result res,t1) /\
   (((?f. (res = SOME (wordSem_FinalFFI f)) /\
     (state_ffi s1 = state_ffi t1) /\ (state_clock s1 = state_clock
       t1))) \/
   (res = NONE /\
     word_to_stackProof_state_rel ac k f f' s1
       (stack_fupd (K (LUPDATE (THE (FLOOKUP (stackSem_state_regs t1)
         k))
         (stackSem_state_stack_space t1 + ((f + k) - (v + 1))) (stack
           t1))) t1) lens 0 /\
       (?x. FLOOKUP (stackSem_state_regs t1) k = SOME x) /\
       (stackSem_state_stack_space t1 = stackSem_state_stack_space t)
         /\
       (LENGTH (stack t1) = LENGTH (stack t)))))`,
  CHEAT_TAC);;

let share_load_lemma2 = prove
 (`share_inst op (2 * v) ad' s = (res,s1) /\
   word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   v < k /\
   (op = Load \/ op = asm_Load8 \/ op = asm_Load16 \/ op =
     asm_Load32) /\ ~(res = SOME Error) ==>
   (?t1.
     sh_mem_op op v ad' t =
       (OPTION_MAP compile_result res,t1) /\
     ((?f. (res = SOME (wordSem_FinalFFI f)) /\
       (state_ffi s1 = state_ffi t1) /\ (state_clock s1 = state_clock
         t1)) \/
     (res = NONE /\
       word_to_stackProof_state_rel ac k f f' s1 t1 lens 0)))`,
  CHEAT_TAC);;

let share_store_lemma1 = prove
 (`share_inst op (2 * v) ad' s = (res,s1) /\
   word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   ~(v < k) /\
   (op = Store \/ op = asm_Store8 \/ op = asm_Store16 \/ op =
     asm_Store32) /\ ~(res = SOME Error) ==>
   (?t1.
     sh_mem_op op (k + 1) ad'
       (stackSem_state_regs_fupd (K (stackSem_state_regs t |+
           (k + 1,EL (stackSem_state_stack_space t + ((f + k) - (v +
             1))) (stack
                 t)))) t) =
       (OPTION_MAP compile_result res,t1) /\
     ((?fv'. (res = SOME (wordSem_FinalFFI fv')) /\
       (state_ffi s1 = state_ffi t1) /\ (state_clock s1 = state_clock
         t1)) \/
     (res = NONE /\
       word_to_stackProof_state_rel ac k f f' s1 t1 lens 0)))`,
  CHEAT_TAC);;

let share_store_lemma2 = prove
 (`share_inst op (2 * v) ad' s = (res,s1) /\
   word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   v < k /\
   (op = Store \/ op = asm_Store8 \/ op = asm_Store16 \/ op =
     asm_Store32) /\ ~(res = SOME Error) ==>
   (?t1.
     sh_mem_op op v ad' t =
       (OPTION_MAP compile_result res,t1) /\
     ((?fv'. (res = SOME (wordSem_FinalFFI fv')) /\
       (state_ffi s1 = state_ffi t1) /\ (state_clock s1 = state_clock
         t1)) \/
     (res = NONE /\
       word_to_stackProof_state_rel ac k f f' s1 t1 lens 0)))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:7386-7445: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_ShareInst_Load *)

(* HOL4 word_to_stackProofScript.sml:7447-7499: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_ShareInst_Store *)

(* HOL4 word_to_stackProofScript.sml:7501-7526: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_ShareInst_correct_lemma *)

(* HOL4 word_to_stackProofScript.sml:7528-7544: a proof *)

let compile_prog_stack_size = prove
 (`word_to_stack_compile_prog ac perf word_prog x k bs =
  (stack_prog,fs,bs2) ==>
   x - k <= fs`,
  CHEAT_TAC);;

(* TODO: clean up *)
(* HOL4 word_to_stackProofScript.sml:7554-7587: ML code, not ported *)

(* [local] *)
let SUB_SUB_SUB_MAX = prove
 (`a - b - (c - b) =
   a - MAX b c`,
  CHEAT_TAC);;

(* [local] *)
let MAX_LE = prove
 (`a <= b ==> MAX a b = b`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_aux_thm = prove
 (`(copy_ret_aux k f 0 = Skip) /\
   (copy_ret_aux k f (SUC n) =
   stackLang_list_Seq [stackLang_StackLoad k n;
     stackLang_StackStore k (n + f); copy_ret_aux k f n])`,
  CHEAT_TAC);;

let evaluate_copy_ret_Seq = prove
 (`evaluate (copy_ret perf b kf vs k0,t) =
   evaluate (Seq (copy_ret perf b kf vs Skip) k0,t)`,
  CHEAT_TAC);;

let evaluate_copy_ret_Seq' = prove
 (`evaluate (copy_ret F is_handle (k,f,f') vs k0,t) =
   (let n = num_stack_ret k vs in
   evaluate (Seq (copy_ret_aux k (if is_handle then f + 3 else f)
     n) (SeqStackFree n k0),t))`,
  CHEAT_TAC);;

let get_labels_copy_ret = prove
 (`stackSem_get_labels (copy_ret perf is_handle kf vs q) =
  stackSem_get_labels q`,
  CHEAT_TAC);;

let evaluate_copy_ret_aux = prove
 (`!k f n t. stackSem_state_use_stack
   t /\ ~(f = 0) /\ f <= LENGTH (stack t) -
     (stackSem_state_stack_space t + n) ==>
   (?t'.
   evaluate (copy_ret_aux k f n,t) = (NONE,t') /\
   (?t'_stack t'_regs.
    t' = stackSem_state_regs_fupd (K t'_regs) (stack_fupd (K
      t'_stack) t) /\
    LENGTH t'_stack = LENGTH (stack t) /\ stackSem_state_stack_space
    t' = stackSem_state_stack_space t /\
    DROP (f + n + stackSem_state_stack_space t') t'_stack =
    DROP (f + n + stackSem_state_stack_space t) (stack t) /\
    (!i. ~(i = k) ==> get_var i t' = get_var i t) /\
    (!m. m < f - n ==>
    EL m (DROP (n + stackSem_state_stack_space t') t'_stack) =
    EL m (DROP (n + stackSem_state_stack_space t) (stack t))) /\
    (let
      stack' = DROP (stackSem_state_stack_space t') t'_stack in let
      stack' = DROP (stackSem_state_stack_space t) (stack t) in
      !x. x < n ==> EL (x + f) stack' = EL x stack')))`,
  CHEAT_TAC);;

let evaluate_copy_ret_aux_clock = prove
 (`!t.
     evaluate (copy_ret_aux k f n,state_clock_fupd (K clk) t) =
     (I ## (\t. state_clock_fupd (K clk) t)) (evaluate
       (copy_ret_aux k f n,t))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:7717-7720: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7722: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7724-7733: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_cont_loop_handler *)

(* [local] *)
let get_labels_loc_check_subspt = prove
 (`stackSem_get_labels p SUBSET loc_check c1 /\ subspt c1 c2 ==>
  stackSem_get_labels p SUBSET loc_check c2`,
  CHEAT_TAC);;

(* state_rel_dec_clock[local] *)
let word_to_stackProof_state_rel_dec_clock = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens extra ==>
   word_to_stackProof_state_rel ac k f f' (dec_clock s) (dec_clock
     t) lens extra`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_cut_state = prove
 (`word_to_stackProof_state_rel ac k f f' s t lens 0 /\
   wordSem_cut_state (names,LN) s = SOME s' ==>
   word_to_stackProof_state_rel ac k f f' s' t lens 0`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:7767-7798: a proof *)
    (* stack-overflow sub-case *)
(* HOL4 word_to_stackProofScript.sml:7800-7828: a proof *)
  (* non-stack-overflow: res_b = OPTION_MAP compile_result q, so IH's "else"
     branch gives us state_rel-like facts about r and t1_b per q. *)
(* HOL4 word_to_stackProofScript.sml:7831-7832: a proof *)
    (* cont_loop q: either q = NONE or q = SOME (Continue 0) *)
(* HOL4 word_to_stackProofScript.sml:7834-7835: a proof *)
      (* TimeOut: s1 = flush_state T r, res = SOME TimeOut *)
(* HOL4 word_to_stackProofScript.sml:7837-7846: a proof *)
    (* recursive case: clock ≠ 0, recurse with dec_clock *)
(* HOL4 word_to_stackProofScript.sml:7848-7908: a proof *)
    (* passthrough: s1 = r, stack exit_loop matches *)
(* HOL4 word_to_stackProofScript.sml:7910-7916: a proof *)
  (* Break 0: s1 = cut_state (exit_names,LN) r *)
(* HOL4 word_to_stackProofScript.sml:7918-7921: a proof *)


(* HOL4 word_to_stackProofScript.sml:7924-7933: a proof *)

(* HOL4 word_to_stackProofScript.sml:7935-8010: a proof *)
    (*preconditions for negation rules*)
(* HOL4 word_to_stackProofScript.sml:8012-8164: a proof *)

(* HOL4 word_to_stackProofScript.sml:8166-8202: a proof *)
    (* Two subgoals *)
(* HOL4 word_to_stackProofScript.sml:8204-8247: a proof *)
    (*TODO shouldn't be unfolding here*)
(* HOL4 word_to_stackProofScript.sml:8249-8251: a proof *)
    (*Get through the eval of stack_move*)
(* HOL4 word_to_stackProofScript.sml:8253-8335: a proof *)
      (*TODO this is very slow*)
(* HOL4 word_to_stackProofScript.sml:8337-8449: a proof *)
    (*This looks hacky but it works*)
(* HOL4 word_to_stackProofScript.sml:8451-8615: a proof *)
    (*hit stack limit during function call*)
(* HOL4 word_to_stackProofScript.sml:8617-8665: a proof *)
    (*2 subgoals*)
(* HOL4 word_to_stackProofScript.sml:8667-8823: a proof *)
      (* GC cutset *)
(* HOL4 word_to_stackProofScript.sml:8825-8901: a proof *)
      (* NON-GC cutset *)
(* HOL4 word_to_stackProofScript.sml:8903-9010: a proof *)
      (*because it can't be the top frame of word_state, which is NONE*)
(* HOL4 word_to_stackProofScript.sml:9012-9027: a proof *)
  (*Space to store handler case*)
(* HOL4 word_to_stackProofScript.sml:9029-9070: a proof *)
  (* Needs to go in wordSem?*)
(* HOL4 word_to_stackProofScript.sml:9072-9104: a proof *)
  (*Space to store args*)
(* HOL4 word_to_stackProofScript.sml:9106-9169: a proof *)
    (*TODO this is very slow*)
(* HOL4 word_to_stackProofScript.sml:9171-9232: a proof *)
  (*space for the function local var*)
(* HOL4 word_to_stackProofScript.sml:9234-9279: a proof *)
  (*This looks hacky but it works*)
(* HOL4 word_to_stackProofScript.sml:9281-9444: a proof *)
  (*hit stack limit during function call*)
(* HOL4 word_to_stackProofScript.sml:9446-9494: a proof *)
  (*2 subgoals*)
(* HOL4 word_to_stackProofScript.sml:9496-9674: a proof *)
    (*GC cutset*)
(* HOL4 word_to_stackProofScript.sml:9676-9751: a proof *)
    (*NON-GC cutset*)
(* HOL4 word_to_stackProofScript.sml:9753-9921: a proof *)
      (*GC cutset *)
(* HOL4 word_to_stackProofScript.sml:9923-10047: a proof *)

(* HOL4 word_to_stackProofScript.sml:10049-10054: a proof *)

(* HOL4 word_to_stackProofScript.sml:10056-10061: a proof *)

(* HOL4 word_to_stackProofScript.sml:10063: a proof *)

(* match original comp_correct shape: n, sprog, bs', n' are free *)
(* HOL4 word_to_stackProofScript.sml:10066-10072: ML code, not ported *)

(* evaluate_Seq_Skip[local] *)
let word_to_stackProof_evaluate_Seq_Skip = prove
 (`stackSem_evaluate (stackLang_Seq Skip p,s) = evaluate (p,s)`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:10080-10088: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10090-10114: a theorem whose
   statement HOL Light does not read (tools/unstated.py): comp_Call *)

(* state_rel_with_clock *)
let word_to_stackProof_state_rel_with_clock = prove
 (`word_to_stackProof_state_rel ac a 0 0 s t lens extra ==>
   word_to_stackProof_state_rel ac a 0 0 (state_clock_fupd (K k) s)
     (state_clock_fupd (K k) t) lens extra`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:10123-10131: the ML values that
   the definitions below antiquote *)

(* HOL4 word_to_stackProofScript.sml:10133-10134: ML code, not ported *)

(* [local] *)
let word_Call_NONE_not_Break_Continue = prove
 (`wordSem_evaluate (Call NONE dest args handler,s) = (res,s') ==>
   (!n. ~(res = SOME (Break n))) /\ (!n. ~(res = SOME (Continue
     n)))`,
  CHEAT_TAC);;

(* [local] *)
let stack_Call_NONE_not_Break_Continue = prove
 (`stackSem_evaluate (Call NONE dest handler,s) = (res,s') ==>
   (!n. ~(res = SOME (Break n))) /\ (!n. ~(res = SOME (Continue
     n)))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:10154-10371: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   state_rel_IMP_semantics *)

let init_state_ok_def = cake_define
  `init_state_ok ac k (t:('a,'c,'ffi)stackSem_state) coracle <=>
     4 < k /\ good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
       stackSem_state_use_stack
     t /\ stackSem_state_use_store t /\ stackSem_state_use_alloc t /\
       gc_fun_ok (stackSem_state_gc_fun t) /\ stackSem_state_stack_space
     t <= LENGTH (stackSem_state_stack t) /\
     FLOOKUP (stackSem_state_regs t) 0 = SOME (Loc 1 0) /\
     LENGTH (stackSem_state_bitmaps t) + 1 < dimword (:'a) /\
     [(n2w 4)] <<= stackSem_state_bitmaps t /\
     LENGTH (stackSem_state_stack t) < dimword (:'a) /\
     DROP (stackSem_state_stack_space t) (stackSem_state_stack t) =
       [wordLang_Word (n2w 0)] /\
     Handler IN FDOM (stackSem_state_store t) /\
     LENGTH (stackSem_state_bitmaps t) + LENGTH (buffer_buffer
       (stackSem_state_data_buffer t)) + buffer_space_left
       (stackSem_state_data_buffer
        t) + 1 < dimword (:'a) /\ stackSem_state_compile_oracle
     t = (\n.
       let ((bm0,cfg),progs) = coracle n in
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
         (cfg,progs,append (FST bm))) /\
     (!n. let ((bm0,cfg),progs) = coracle n in
         EVERY (post_alloc_conventions k o SND o SND) progs /\
         EVERY (flat_exp_conventions o SND o SND) progs /\
         EVERY ((\x y. ~(x = y)) raise_stub_location o FST) progs /\
         EVERY ((\x y. ~(x = y)) store_consts_stub_location o FST)
           progs /\
         (n = 0 ==> bm0 = LENGTH (stackSem_state_bitmaps t)))`;;

let word_to_stackProof_make_init_def = cake_define
  `word_to_stackProof_make_init ac k (t:('a,'c,'ffi)stackSem_state) code
  coracle =
     mk_wordSem_state (sptree_insert 0 (Loc 1 0) LN) (SOME 0)
       (stackSem_state_fp_regs t) (stackSem_state_store t \\ Handler) []
       (LENGTH (stackSem_state_stack t)) (stack_size ([]:('a
       stack_frame) list)) (mapi (\n (arg_count,prog). FST (SND
       (word_to_stack_compile_prog ac F prog arg_count k (misc_Nil,0))))
       code) (stackSem_state_memory t) (stackSem_state_mdomain t)
       (stackSem_state_sh_mdomain t) (K I) (\(bm0,cfg) progs.
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
       OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND
         bm,cfg)))
         (stackSem_state_compile t cfg progs)) coracle
           (stackSem_state_code_buffer t) (stackSem_state_data_buffer t)
           (stackSem_state_gc_fun t) 0 (stackSem_state_clock t) 0 code
           (stackSem_state_be t) (stackSem_state_ffi t)
   // Not sure about Nil,0`;;
hol4_overload "make_init" "word_to_stackProof_make_init";;

(* [local] *)
let init_state_ok_IMP_state_rel = prove
 (`sptree_lookup raise_stub_location (stackSem_state_code t) = SOME
  (raise_stub F k) /\
   sptree_lookup store_consts_stub_location (stackSem_state_code t) =
     SOME (store_consts_stub k) /\
    (!n word_prog arg_count.
       (sptree_lookup n code = SOME (arg_count,word_prog)) ==>
       post_alloc_conventions k word_prog /\
       flat_exp_conventions word_prog /\
       (?bs i bs2 i2 f stack_prog.
         word_to_stack_compile_prog ac F word_prog arg_count k (bs,i)
           = (stack_prog,f,(bs2,i2)) /\
         LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH
           (stackSem_state_bitmaps t) /\
         isPREFIX (append bs2) (DROP (i - LENGTH (append bs))
           (stackSem_state_bitmaps t)) /\
         (sptree_lookup n (stackSem_state_code t) = SOME
           stack_prog))) /\
    domain (stackSem_state_code t) =
      raise_stub_location INSERT store_consts_stub_location INSERT
        domain code /\
    init_state_ok ac k t coracle ==>
    word_to_stackProof_state_rel ac k 0 0
      (word_to_stackProof_make_init ac k t code coracle)
      (t:('a,'c,'ffi)stackSem_state) [] 0`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:10467-10471: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10473-10701: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   state_rel_IMP_semantics' *)

(* HOL4 word_to_stackProofScript.sml:10703-10707: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10709-10758: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   compile_semantics *)

(* [local] *)
let stack_move_no_labs = prove
 (`!n a b c p.
   extract_labels p = [] ==>
   extract_labels (stack_move n a b c p) = []`,
  CHEAT_TAC);;

(* [local,simp] *)
let extract_labels_copy_ret_aux = prove
 (`!k f n. extract_labels (copy_ret_aux k f n) = []`,
  CHEAT_TAC);;

(* [local,simp] *)
let extract_labels_copy_ret = prove
 (`extract_labels (copy_ret perf b kf vs kont) = extract_labels kont`,
  CHEAT_TAC);;

(* [local,simp] *)
let extract_labels_wStackLoad_Skip = prove
 (`extract_labels (wStackLoad xs Skip) = []`,
  CHEAT_TAC);;


(* [local,simp] *)
let extract_labels_stack_move_StackAlloc = prove
 (`!n start' offset i.
     extract_labels (stack_move n start' offset i
       (stackLang_StackAlloc k)) = []`,
  CHEAT_TAC);;

let word_to_stack_lab_pres = prove
 (`!ac perf p bs kf.
     extract_labels p = extract_labels (FST (comp ac perf p bs kf))`,
  CHEAT_TAC);;

let word_to_stack_compile_lab_pres = prove
 (`EVERY (\(n,m,p).
   let labs = extract_labels p in
   EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
   ALL_DISTINCT labs) prog ==>
   (let (bytes,c,f,p) = compile asm_conf F prog in
     MAP FST p = (raise_stub_location :: store_consts_stub_location
       :: MAP FST prog) /\
     EVERY (\(n,p).
       let labs = extract_labels p in
       EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
       ALL_DISTINCT labs) p)`,
  CHEAT_TAC);;

let compile_word_to_stack_lab_pres = prove
 (`!p perf b q r.
   compile_word_to_stack ac perf k p b = (q,r) /\
   EVERY (\(l,m,e).
     EVERY (\(l1,l2). (l1 = l) /\ (~(l2 = 0)) /\ (~(l2 = 1)))
       (extract_labels e) /\
     ALL_DISTINCT (extract_labels e)) p ==>
   EVERY (\(l,e).
     EVERY (\(l1,l2). (l1 = l) /\ (~(l2 = 0)) /\ (~(l2 = 1)))
       (extract_labels e) /\
     ALL_DISTINCT (extract_labels e)) q`,
  CHEAT_TAC);;

(* [local] *)
let EVEN_DIV_2_props = prove
 (`a MOD 2 = 0 /\ b MOD 2 = 0 ==>
   (~(a = b) ==> ~(a DIV 2 = b DIV 2)) /\ (~(a = 0) ==> ~(a DIV 2 =
     0))`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:10956: ML code, not ported *)

(* [local] *)
let call_dest_stack_asm_name = prove
 (`call_dest d a k = (q0,d') ==>
   stack_asm_name c q0 /\
   (match d' with
     INR r -> r <= (FST k) + 1 | INL l -> T)`,
  CHEAT_TAC);;

(* [local] *)
let wLive_stack_asm_name = prove
 (`(FST kf) + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs
  c) /\
   wLive q bs kf = (q1,bs') ==>
   stack_asm_name c q1`,
  CHEAT_TAC);;

(* [local,simp] *)
let stack_move_stack_asm_name = prove
 (`!n start' offset i p.
   stack_asm_name c (stack_move n start' offset i p) <=>
     stack_asm_name c p`,
  CHEAT_TAC);;

(* [local,simp] *)
let copy_ret_aux_stack_asm_name = prove
 (`!k f n. stack_asm_name c (copy_ret_aux k f n)`,
  CHEAT_TAC);;

(* [local,simp] *)
let copy_ret_stack_asm_name = prove
 (`stack_asm_name c (copy_ret perf b kf vs kont) <=> stack_asm_name c
  kont`,
  CHEAT_TAC);;

let word_to_stack_stack_asm_name_lem = prove
 (`!c perf p bs kf.
   perf = F /\
   post_alloc_conventions (FST kf) p /\
   full_inst_ok_less c p /\
   (asm_config_two_reg_arith c ==> every_inst two_reg_inst p) /\
   (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) /\
   (FST kf) + 1 < asm_config_reg_count c - LENGTH
     (asm_config_avoid_regs c) /\
   4 < (FST kf) ==>
   stack_asm_name c (FST (comp c perf p bs kf))`,
  CHEAT_TAC);;

(* [local] *)
let call_dest_stack_asm_remove = prove
 (`(FST k) + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs
  c) /\
   call_dest d a k = (q0,d') ==>
   stack_asm_remove c q0 /\
   (match d' with
     INR r -> r <= (FST k) + 1 | INL l -> T)`,
  CHEAT_TAC);;

(* [local] *)
let wLive_stack_asm_remove = prove
 (`(FST kf) + 1 < asm_config_reg_count c - LENGTH (asm_config_avoid_regs
  c) /\
   wLive q bs kf = (q1,bs') ==>
   stack_asm_remove c q1`,
  CHEAT_TAC);;

(* [local] *)
let stack_move_stack_asm_remove = prove
 (`!n start' offset i p.
   reg_name i c ==>
   (stack_asm_remove c (stack_move n start' offset i p) <=>
     stack_asm_remove c p)`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_aux_stack_asm_remove = prove
 (`!k f n.
   reg_name k c ==>
   stack_asm_remove c (copy_ret_aux k f n)`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_stack_asm_remove = prove
 (`reg_name (FST kf) c ==>
   (stack_asm_remove c (copy_ret F b kf vs kont) <=>
     stack_asm_remove c kont)`,
  CHEAT_TAC);;

let word_to_stack_stack_asm_remove_lem = prove
 (`!(c:'a asm_config) perf (p:'a wordLang_prog) bs kf.
   (FST kf) + 1 < asm_config_reg_count c - LENGTH
     (asm_config_avoid_regs c) /\ perf = F ==>
   stack_asm_remove c (FST (comp c perf p bs kf))`,
  CHEAT_TAC);;

let word_to_stack_stack_asm_convs = prove
 (`EVERY (\(n,m,p).
     full_inst_ok_less c p /\
     (asm_config_two_reg_arith c ==> every_inst two_reg_inst p) /\
     (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) /\
     post_alloc_conventions (asm_config_reg_count c - (LENGTH
       (asm_config_avoid_regs c) + 5)) p) progs /\
     4 < (asm_config_reg_count c - (LENGTH (asm_config_avoid_regs c)
       + 5)) ==>
   EVERY (\(n,p). stack_asm_name c p /\ stack_asm_remove c p) (SND
     (SND (SND (compile c F progs))))`,
  CHEAT_TAC);;

let stack_move_alloc_arg = prove
 (`!n st off i p.
     alloc_arg p ==>
     alloc_arg (stack_move n st off i p)`,
  CHEAT_TAC);;

(* [local] *)
let alloc_arg_copy_ret_aux = prove
 (`!k f n.
   alloc_arg (copy_ret_aux k f n)`,
  CHEAT_TAC);;

(* [local,simp] *)
let alloc_arg_copy_ret = prove
 (`(alloc_arg (copy_ret perf b kf vs kont) <=> alloc_arg kont)`,
  CHEAT_TAC);;

let word_to_stack_alloc_arg = prove
 (`!c perf p n args.
     perf = F ==>
     alloc_arg (FST (word_to_stack_comp c perf p n args))`,
  CHEAT_TAC);;

let stack_move_reg_bound = prove
 (`!n st off i p k.
     i < k /\
     reg_bound p k ==>
     reg_bound (stack_move n st off i p) k`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_aux_reg_bound = prove
 (`!k f n.
   reg_bound (copy_ret_aux k f n) (k + 2)`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_reg_bound = prove
 (`reg_bound kont (k + 2) ==>
   (reg_bound (copy_ret perf b (k,f,f') vs kont) (k + 2))`,
  CHEAT_TAC);;

let word_to_stack_reg_bound = prove
 (`!c perf p n args.
     post_alloc_conventions (FST args) p /\
     4 <= FST args /\ perf = F ==>
     reg_bound (FST (word_to_stack_comp c perf p n args)) (FST args
       + 2)`,
  CHEAT_TAC);;

let stack_move_call_args = prove
 (`!n st off i p.
     call_args p 1 2 3 4 0 ==>
     call_args (stack_move n st off i p) 1 2 3 4 0`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_aux_call_args = prove
 (`!k f n.
   call_args (copy_ret_aux k f n) 1 2 3 4 0`,
  CHEAT_TAC);;

(* [local,simp] *)
let copy_ret_call_args = prove
 (`call_args (copy_ret perf b kf vs kont) 1 2 3 4 0 <=>
   call_args kont 1 2 3 4 0`,
  CHEAT_TAC);;

let word_to_stack_call_args = prove
 (`!c perf p n args.
     post_alloc_conventions (FST args) p /\ perf = F ==>
     call_args (FST (word_to_stack_comp c perf p n args)) 1 2 3 4 0`,
  CHEAT_TAC);;

(* HOL4 word_to_stackProofScript.sml:11585-11587: ML code, not ported *)

let reg_bound_mono = prove
 (`!p k k'.
     reg_bound p k /\
     k <= k' ==>
     reg_bound p k'`,
  CHEAT_TAC);;

(* Gluing all the conventions together *)
let word_to_stack_stack_convs = prove
 (`word_to_stack_compile ac F p = (bytes,c',f',p') /\
   EVERY (post_alloc_conventions k) (MAP (SND o SND) p) /\
   k = (asm_config_reg_count ac - (5 + LENGTH (asm_config_avoid_regs
     ac))) /\
   4 <= k ==>
   EVERY alloc_arg (MAP SND p') /\
   EVERY (\p. reg_bound p (k + 2)) (MAP SND p') /\
   EVERY (\p. call_args p 1 2 3 4 0) (MAP SND p')`,
  CHEAT_TAC);;

let compile_word_to_stack_convs = prove
 (`!p bm q bm'.
    compile_word_to_stack c F k p bm = (q,bm') /\
    EVERY (\(n,m,p).
      full_inst_ok_less c p /\
      (asm_config_two_reg_arith c ==> every_inst two_reg_inst p) /\
      (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) /\
      post_alloc_conventions k p) p /\ 4 < k /\ k + 1 <
        asm_config_reg_count c - LENGTH (asm_config_avoid_regs c) ==>
    EVERY (\(x,y).
      stack_asm_name c y /\
      stack_asm_remove c y /\
      alloc_arg y /\
      reg_bound y (k + 2) /\
      call_args y 1 2 3 4 0) q`,
  CHEAT_TAC);;

(* this is the only property needed of the wRegs  *)
(* HOL4 word_to_stackProofScript.sml:11698-11703: a theorem that HOL4
   states as the value of an ML expression: get_code_labels_wReg *)

(* [local] *)
let get_code_handler_labels_wStackLoad = prove
 (`!ls.
   get_code_labels (wStackLoad ls x) = get_code_labels x /\
   stack_get_handler_labels n (wStackLoad ls x) =
     stack_get_handler_labels n x`,
  CHEAT_TAC);;

(* [local] *)
let wLive_code_labels = prove
 (`wLive q bs kf = (q',bs') ==>
   get_code_labels q' = {}`,
  CHEAT_TAC);;

(* [local] *)
let stack_move_code_labels = prove
 (`!a b c d e.
   get_code_labels (stack_move a b c d e) = get_code_labels e`,
  CHEAT_TAC);;

(* [local] *)
let get_code_handler_labels_copy_ret_aux = prove
 (`!k f n.
   get_code_labels (copy_ret_aux k f n) = {} /\
   stack_get_handler_labels m (copy_ret_aux k f n) = {}`,
  CHEAT_TAC);;

(* [local,simp] *)
let get_code_handler_labels_copy_ret = prove
 (`get_code_labels (copy_ret perf b kf vs kont) =
   get_code_labels kont /\
   stack_get_handler_labels m (copy_ret perf b kf vs kont) =
   stack_get_handler_labels m kont`,
  CHEAT_TAC);;

let word_to_stack_comp_code_labels = prove
 (`!c perf prog bs kf n.
     good_handlers n prog /\ perf = F ==>
     get_code_labels (FST (comp c perf prog bs kf)) SUBSET
     (raise_stub_location,0) INSERT
       (store_consts_stub_location,0) INSERT
         ((IMAGE (\n. (n,0)) (get_code_labels prog)) UNION
          stack_get_handler_labels n (FST (comp c perf prog bs
            kf)))`,
  CHEAT_TAC);;

let compile_word_to_stack_code_labels = prove
 (`!ac perf k p bs p' bs'.
   EVERY (\(n,m,pp). good_handlers n pp) p /\
   perf = F /\
   compile_word_to_stack ac perf k p bs = (p',bs') ==>
   // every label in the compiled code
   BIGUNION (IMAGE get_code_labels (set_of_list (MAP SND p'))) SUBSET
   (raise_stub_location,0) INSERT
   (store_consts_stub_location,0) INSERT (
   // either came from wordLang
   IMAGE (\n. (n,0)) (BIGUNION (set_of_list (MAP (\(n,m,pp).
     (get_code_labels pp)) p))) UNION
   // or has been introduced into the handler labels
   BIGUNION (set_of_list (MAP (\(n,pp). (stack_get_handler_labels n
     pp)) p')))`,
  CHEAT_TAC);;

let word_to_stack_good_code_labels = prove
 (`compile asm_conf F progs = (bytes,bs,fs,prog') /\
   wordConvs_good_code_labels progs elabs ==>
   stack_good_code_labels prog' elabs`,
  CHEAT_TAC);;

let word_to_stack_good_code_labels_incr = prove
 (`raise_stub_location IN elabs /\
   store_consts_stub_location IN elabs /\
   compile_word_to_stack ac F k prog bs = (prog',fs',bs') ==>
   wordConvs_good_code_labels prog elabs ==>
   stack_good_code_labels prog' elabs`,
  CHEAT_TAC);;

(* [local] *)
let sub_union_lemma = prove
 (`x SUBSET y ==> x SUBSET y UNION z`,
  CHEAT_TAC);;

let word_to_stack_good_handler_labels = prove
 (`EVERY (\(n,m,pp). good_handlers n pp) prog ==>
   compile asm_conf F prog = (bytes,bs,fs,prog') ==>
   stack_good_handler_labels prog'`,
  CHEAT_TAC);;

let word_to_stack_good_handler_labels_incr = prove
 (`EVERY (\(n,m,pp). good_handlers n pp) prog ==>
   compile_word_to_stack ac F k prog bs = (prog',fs',bs') ==>
   stack_good_handler_labels prog'`,
  CHEAT_TAC);;

(* no_install is preserved *)

let wMoveAux_no_install_lem = prove
 (`!xs kf. no_install (wMoveAux xs kf)`,
  CHEAT_TAC);;

let wStackLoad_no_install_lem = prove
 (`!l prog. no_install (wStackLoad l prog) = no_install prog`,
  CHEAT_TAC);;

let wRegWrite1_no_install_lem = prove
 (`(!reg. no_install (prog reg)) ==>
   no_install (wRegWrite1 prog r kf)`,
  CHEAT_TAC);;

let wRegWrite2_no_install_lem = prove
 (`(!reg. no_install (prog reg)) ==>
   no_install (wRegWrite2 prog r kf)`,
  CHEAT_TAC);;

let wLive_no_install_lem = prove
 (`no_install (FST (wLive live bs kf))`,
  CHEAT_TAC);;

let stack_move_no_install_lem = prove
 (`!n start' offset i p.
   no_install (stack_move n start' offset i p) = no_install p`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_aux_no_install = prove
 (`!k f n.
   no_install (copy_ret_aux k f n)`,
  CHEAT_TAC);;

(* [local,simp] *)
let copy_ret_no_install = prove
 (`no_install (copy_ret perf b kf vs kont) <=>
   no_install kont`,
  CHEAT_TAC);;

let comp_no_install = prove
 (`!ac perf prog bs kf prog' bs'.
     wordConvs_no_install prog /\
     comp ac perf prog bs kf = (prog',bs') /\ perf = F ==>
     stackProps_no_install prog'`,
  CHEAT_TAC);;

let compile_word_to_stack_no_install = prove
 (`!ac perf k prog bs prog' fs' bs'.
     EVERY (\(n,m,pp). wordConvs_no_install pp) prog /\
     compile_word_to_stack ac perf k prog bs = (prog',fs',bs') /\
     perf = F ==>
     EVERY (\(a,p). no_install p) prog'`,
  CHEAT_TAC);;

(* no_share_mem is preserved *)
let wMoveAux_no_shmemop_lem = prove
 (`!xs kf. no_shmemop (wMoveAux xs kf)`,
  CHEAT_TAC);;

let wStackLoad_no_shmemop_lem = prove
 (`!l prog. no_shmemop (wStackLoad l prog) = no_shmemop prog`,
  CHEAT_TAC);;

let wRegWrite1_no_shmemop_lem = prove
 (`(!reg. no_shmemop (prog reg)) ==>
   no_shmemop (wRegWrite1 prog r kf)`,
  CHEAT_TAC);;

let wRegWrite2_no_shmemop_lem = prove
 (`(!reg. no_shmemop (prog reg)) ==>
   no_shmemop (wRegWrite2 prog r kf)`,
  CHEAT_TAC);;

let wLive_no_shmemop_lem = prove
 (`no_shmemop (FST (wLive live bs kf))`,
  CHEAT_TAC);;

let stack_move_no_shmemop_lem = prove
 (`!n start' offset i p.
   no_shmemop (stack_move n start' offset i p) = no_shmemop p`,
  CHEAT_TAC);;

(* [local] *)
let copy_ret_aux_no_shmemop = prove
 (`!k f n.
   no_shmemop (copy_ret_aux k f n)`,
  CHEAT_TAC);;

(* [local,simp] *)
let copy_ret_no_shmemop = prove
 (`no_shmemop (copy_ret perf b kf vs kont) <=>
   no_shmemop kont`,
  CHEAT_TAC);;

(* [local] *)
let perf_call_prefix_no_shmemop = prove
 (`no_shmemop (perf_call_prefix l1 l2 kf0)`,
  CHEAT_TAC);;

(* [local] *)
let perf_call_suffix_no_shmemop = prove
 (`no_shmemop perf_call_suffix`,
  CHEAT_TAC);;

(* [local] *)
let PushHandler_no_shmemop = prove
 (`no_shmemop (PushHandler perf l1 l2 kff)`,
  CHEAT_TAC);;

(* [local] *)
let PopHandler_no_shmemop = prove
 (`no_shmemop (PopHandler perf kff prog) <=>
     no_shmemop prog`,
  CHEAT_TAC);;

(* [local] *)
let StackHandlerArgs_no_shmemop = prove
 (`no_shmemop (StackHandlerArgs perf dest arg_count kff)`,
  CHEAT_TAC);;

let comp_no_shmemop = prove
 (`!ac perf prog bs kf prog' bs'.
     no_share_inst prog /\
     comp ac perf prog bs kf = (prog',bs') ==>
     no_shmemop prog'`,
  CHEAT_TAC);;

let compile_word_to_stack_no_share_inst = prove
 (`!ac perf k prog bs prog' fs' bs'.
     EVERY (\(n,m,pp). no_share_inst pp) prog /\
     compile_word_to_stack ac perf k prog bs = (prog',fs',bs') ==>
     EVERY (\(a,p). no_shmemop p) prog'`,
  CHEAT_TAC);;

let compile_no_shmemop = prove
 (`compile cf F prog = (bs,fs,ns,prog') /\
   EVERY (\(n,m,pp). no_share_inst pp) prog ==>
   EVERY (\(a,p). no_shmemop p) prog'`,
  CHEAT_TAC);;

let word_to_stack_compile_no_install = prove
 (`ALL_DISTINCT (MAP FST prog) /\
   no_install_code (fromAList prog) /\
   word_to_stack_compile ac F prog = (bm,c,fs,p) ==>
   EVERY (\(n,x). no_install x) p`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["every";
   "fv"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
