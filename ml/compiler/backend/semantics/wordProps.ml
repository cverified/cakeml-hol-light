(* ======================================================== *)
(*  wordProps: ported from HOL4's
    compiler/backend/semantics/wordPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about wordLang and its semantics
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;

(*
Main lemmas:
0) Clock lemmas (add_clock, dec_clock, IO monotonicity)
1) Code table constancy across eval
2) Swapping stack for one with identical values (but different keys)
3) Thms to handle the permutation oracle
4) Effect of extra locals (locals_rel)
*)

(*TODO remove *)

(*TODO move*)

(* TODO: move *)

(* HOL4 wordPropsScript.sml:43-45: ML code, not ported *)

(* HOL4 wordPropsScript.sml:47-49: the ML values that the definitions
   below antiquote *)

(* -- *)
(*drulel takes a list and tries to apply drule
*)
(* HOL4 wordPropsScript.sml:85: ML code, not ported *)
(* HOL4 wordPropsScript.sml:86: code that the source has in a comment *)
(* HOL4 wordPropsScript.sml:87: ML code, not ported *)
(* Clock lemmas *)

(*helps with existence proofs
?l'. (s with locals := l) = (s with locals := l')*)
(*TODO does not work when given a goal like
?k'. (s with <|locals := l; clock := k|>) = (s with <|locals := l, clock
  := k |>)
*)

(*TODO Weaken this simplification
What that is needed to be pulled down is when
f is a record update like (λs. s with clock := k)
*)

(*USEFUL to clean up proofs with the previous lemma*)

(******CONST LEMMAS *****)

(*FIXME dupe*)
(*code and gc_fun are unchanged across eval*)

(*TODO merge*)

(*FIXME dupe*)

(*TODO use PAIRMAP and deal with breakage*)

(* TODO: generated names *)

(* HOL4 wordPropsScript.sml:1303-1309: the ML values that the
   definitions below antiquote *)

(* HOL4 wordPropsScript.sml:1327-1332: the ML values that the
   definitions below antiquote *)

(******CONST LEMMAS END *****)

(*TODO complete for all get set variaents *)

(* Standard add clock lemma for FBS *)

(* HOL4 wordPropsScript.sml:1436-1441: ML code, not ported *)

(* This lemma is interesting in wordLang because of the use of
   MustTerminate

   To remove MustTerminate, we need to inject an exact number of clock
     ticks
   corresponding to the ticks used in the MustTerminate block

   The number of clock ticks is fixed for any program, and can be
     characterized by st.clock - rst.clock *)

(* IO and clock monotonicity *)

(*TODO This format of is really weird can this be changed?*)

(* TODO: monotonicity *)

(* -- *)

(**)

(*--Stack Swap Lemma--*)

(*Stacks look the same to the GC except for the keys (e.g. recoloured
   and in order)*)
let s_frame_val_eq_def = cake_define
  `s_frame_val_eq x1 x2 =
        match (x1,x2) with
          (StackFrame n ls1 ls NONE,StackFrame n' ls1' ls' NONE) ->
        MAP SND ls = MAP SND ls' /\ n = n'
        | ((StackFrame n ls1 ls (SOME y)),(StackFrame n' ls1' ls'
          (SOME y'))) ->
        MAP SND ls = MAP SND ls' /\ y = y' /\ n = n'
        | (_1,_2) -> F`;;

let s_val_eq_def = cake_define
  `s_val_eq x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | ((x :: xs),(y :: ys)) -> (s_val_eq xs ys /\
                              s_frame_val_eq x y)
        | (_3,_4) -> F`;;

(*Stacks look the same except for the values of the GC-ed cutsets (e.g.
   result of gc)*)
let s_frame_key_eq_def = cake_define
  `s_frame_key_eq x1 x2 =
        match (x1,x2) with
          (StackFrame n ls0 ls NONE,StackFrame n' ls0' ls' NONE) ->
            MAP FST ls = MAP FST ls' /\ ls0 = ls0' /\ n = n'
        | ((StackFrame n ls0 ls (SOME y)),(StackFrame n' ls0' ls'
          (SOME y'))) -> MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 =
          ls0' /\ n = n'
        | (_5,_6) -> F`;;

let s_key_eq_def = cake_define
  `s_key_eq x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | ((x :: xs),(y :: ys)) -> (s_key_eq xs ys /\
                              s_frame_key_eq x y)
        | (_7,_8) -> F`;;

(*Reflexive*)

(*transitive*)


(*Symmetric*)

(*gc preserves the stack_key relation*)

(*gc succeeds on all stacks related by stack_val and there are relations
  in the result*)

(*Slightly more general theorem allows the unused locals to be
   differnt*)

(*Most generalised gc_s_val_eq*)

(*pushing and popping maintain the stack_key relation*)

(* Stack swap theorem for evaluate *)

(*--Stack Swap Lemma DONE--*)

(*--Permute Swap Lemma--*)
(*For any target result permute, we can find an initial permute such
   that the
  final permute is equal to the target *)

(* Locals extend lemma *)
let locals_rel_def = cake_define
  `locals_rel temp (s:('a word_loc) spt) t <=> (!x. x < temp ==>
  sptree_lookup x s = sptree_lookup x t)`;;

(*Extra temporaries not mentioned in program
  do not affect evaluation
  TODO: theorem statement needs to be changed *)

(* HOL4 wordPropsScript.sml:3622-3627: a proof *)

(* HOL4 wordPropsScript.sml:3629-3642: a proof *)

(* HOL4 wordPropsScript.sml:3644-3650: a proof *)

(* HOL4 wordPropsScript.sml:3652-3666: a proof *)

(* HOL4 wordPropsScript.sml:3668-3697: a proof *)

(* HOL4 wordPropsScript.sml:3699-3709: a proof *)

(* HOL4 wordPropsScript.sml:3711-3716: a proof *)

(* HOL4 wordPropsScript.sml:3718-3737: a proof *)

(* HOL4 wordPropsScript.sml:3739-3748: a proof *)

(* HOL4 wordPropsScript.sml:3750-3758: a proof *)

(* HOL4 wordPropsScript.sml:3760-3766: a proof *)

(* HOL4 wordPropsScript.sml:3768-3773: a proof *)

(* HOL4 wordPropsScript.sml:3775-3783: a proof *)

(* HOL4 wordPropsScript.sml:3785-3791: a proof *)

(* HOL4 wordPropsScript.sml:3793-3806: a proof *)

(* HOL4 wordPropsScript.sml:3808-3810: a proof *)

(* HOL4 wordPropsScript.sml:3812-3814: a proof *)

(* HOL4 wordPropsScript.sml:3816-3820: a proof *)

(* HOL4 wordPropsScript.sml:3822-3826: a proof *)

(* HOL4 wordPropsScript.sml:3828-3831: a proof *)

(* HOL4 wordPropsScript.sml:3833-3838: a proof *)

(* HOL4 wordPropsScript.sml:3840-3844: a proof *)

(* HOL4 wordPropsScript.sml:3846-3849: a proof *)

(* HOL4 wordPropsScript.sml:3851-3853: a proof *)

(* HOL4 wordPropsScript.sml:3855-3859: a proof *)

(* HOL4 wordPropsScript.sml:3861-3865: a proof *)

(* HOL4 wordPropsScript.sml:3867: a proof *)

let gc_fun_ok_def = cake_define
  `gc_fun_ok (f:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) =
     (!wl m d s wl1 m1 s1.
       Handler IN FDOM s /\
       (f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)) ==>
       (LENGTH wl = LENGTH wl1) /\
       ~(Handler IN FDOM s1) /\
       (f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler,FAPPLY s
         Handler))))`;;

(*I'm pretty sure this is defined somewhere else too
MOVE THIS to backend props.*)

let inc_clock_def = cake_define
  `wordProps_inc_clock n (t:('a,'c,'ffi)wordSem_state) =
  state_clock_fupd (K (state_clock t + n)) t`;;
hol4_overload "inc_clock" "wordProps_inc_clock";;

let no_alloc_code_def = cake_define
  `no_alloc_code (code:(num#'a wordLang_prog) spt) <=>
   (!k n p. sptree_lookup k code = SOME (n,p) ==> no_alloc p)`;;

let no_install_code_def = cake_define
  `no_install_code (code:(num#'a wordLang_prog) spt) <=>
       (!k n p. sptree_lookup k code = SOME (n,p) ==>
         wordConvs_no_install p)`;;

let no_mt_code_def = cake_define
  `no_mt_code (code:(num#'a wordLang_prog) spt) <=>
   (!k n p. sptree_lookup k code = SOME (n,p) ==> no_mt p)`;;


(*** permute_swap for no_install & no_alloc ***)

(* HOL4 wordPropsScript.sml:4792-4795: the overload PERM_STACK, which
   the port expands *)

(* HOL4 wordPropsScript.sml:5146-5166: a proof *)

(* HOL4 wordPropsScript.sml:5168: a proof *)
