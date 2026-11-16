(* ======================================================== *)
(*  num_tree_enc_dec: ported from HOL4's
    compiler/backend/serialiser/num_tree_enc_decScript.sml
    A definition theory, with 25 definitions, 1 datatype and 31
    theorems.  Needed by backend_cv.ml, backend_enc_dec.ml and
    decodeProg.ml.  *)
(* ======================================================== *)

(*
  Encoders and decoders to/from types represented as trees
  consisting of natural numbers.
*)

needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/backend/serialiser/num_list_enc_dec.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "num_tree_enc_dec"
  ["ast"; "evaluateProps"; "fpSem"; "misc"; "ml_prog"; "ml_translator";
   "mlstring"; "mlvector"; "num_list_enc_dec"; "semanticPrimitives";
   "semanticPrimitivesProps"];;
(* HOL4 ancestors outside the port: integer *)

let num_tree_INDUCT,num_tree_RECURSION = define_datatype
  "num_tree =
     Tree num (num_tree list)";;

let num_tree_enc'_def = define_cases
  `(num_tree_enc' [] = misc_List []) /\
   (num_tree_enc' (CONS (Tree k xs) ts) =
      misc_Append (misc_Append (misc_List [k; LENGTH xs]) (num_tree_enc'
          xs))
             (num_tree_enc' ts))`;;

(* fix_res_IMP *)
let num_tree_enc_dec_fix_res_IMP = prove
 (`(x,ns1) = fix_res ns res ==> LENGTH ns1 <= LENGTH ns`,
  CHEAT_TAC);;

let dec_ok_fix_res = prove
 (`dec_ok d ==> (!ns. fix_res ns (d ns) = d ns)`,
  CHEAT_TAC);;

let num_tree_dec'_def = new_definition
  `num_tree_dec' c ns =
     if c = 0 then ([],ns) else match ns with [] -> ([],ns)
        | [t] -> ([],ns)
        | (CONS t (CONS l ns)) ->
             let (ts1,ns1) = fix_res ns (num_tree_dec' l ns) in
             let (ts2,ns2) = fix_res ns1 (num_tree_dec' (c - 1) ns1) in
               (CONS (Tree t ts1) ts2,ns2)`;;

let dec_ok_num_tree_dec' = prove
 (`!l. dec_ok (num_tree_dec' l)`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let num_tree_enc_dec_num_tree_dec'_def =
  SIMP_RULE [MATCH_MP dec_ok_fix_res (SPEC_ALL dec_ok_num_tree_dec')]
  num_tree_dec'_def;;

(* HOL4 num_tree_enc_decScript.sml:68-69: a theorem that HOL4 states as the
   value of an ML expression: num_tree_dec'_ind *)

let num_tree_enc_def,num_tree_enc_ind = define_guess
  `num_tree_enc t = num_tree_enc' [t]`;;

let num_tree_dec_def,num_tree_dec_ind = define_guess
  `num_tree_dec ns =
     match num_tree_dec' 1 ns with ([],ns) -> (Tree 0 [],ns)
     | (CONS t ts,ns) -> (t,ns)`;;

let dec_ok_num_tree_dec = prove
 (`dec_ok num_tree_dec`,
  CHEAT_TAC);;

let num_tree_enc_dec_ok = prove
 (`enc_dec_ok num_tree_enc num_tree_dec`,
  CHEAT_TAC);;

let imp_enc_dec_ok = prove
 (`!e d.
     (!x. d (e x) = x) ==>
     enc_dec_ok (num_tree_enc o e) ((d ## I) o num_tree_dec)`,
  CHEAT_TAC);;

let num_tree_enc_dec_nth_def,num_tree_enc_dec_nth_ind = define_guess
  `(num_tree_enc_dec_nth n [] = Tree 0 []) /\
   (num_tree_enc_dec_nth n (CONS x xs) = if n = 0 then x else
    num_tree_enc_dec_nth (n - 1) xs)`;;
add_simp num_tree_enc_dec_nth_def;;

(* HOL4 num_tree_enc_decScript.sml:116-120: a theorem whose statement the
   port cannot state yet: MEM_num_tree_size *)

(* num *)

let num_enc'_def = new_definition
  `num_enc' n = Tree n []`;;

let num_dec'_def = new_definition
  `num_dec' (Tree n xs) = n`;;
add_simp num_dec'_def;;

let num_dec_enc' = prove
 (`num_dec' (num_enc' n) = n`,
  CHEAT_TAC);;
add_simp num_dec_enc';;

(* int *)

let int_enc'_def = new_definition
  `int_enc' n = if n < (&0:int) then Tree (num_of_int ((&0) - n)) [Tree 0
  []] else Tree (num_of_int n) []`;;

let int_dec'_def = new_definition
  `int_dec' x1 =
   match x1 with
     Tree n [] -> &n
   | Tree n _ -> --((&n):int)`;;

let int_dec_enc' = prove
 (`int_dec' (int_enc' n) = n`,
  CHEAT_TAC);;
add_simp int_dec_enc';;

(* bool *)

let bool_enc'_def = define_cases
  `(bool_enc' F = Tree 0 []) /\
   (bool_enc' T = Tree 1 [])`;;

let bool_dec'_def = new_definition
  `bool_dec' (Tree n xs) = (n = 1)`;;

let bool_dec_enc' = prove
 (`bool_dec' (bool_enc' b) = b`,
  CHEAT_TAC);;
add_simp bool_dec_enc';;

(* chr *)

let chr_enc'_def = new_definition
  `chr_enc' c = Tree (ORD c) []`;;

let chr_dec'_def = new_definition
  `chr_dec' (Tree n xs) = if n < 256 then CHR n else CHR 32`;;

let chr_enc'_thm = prove
 (`chr_dec' (chr_enc' c) = c`,
  CHEAT_TAC);;
add_simp chr_enc'_thm;;

(* list *)

let list_enc'_def = new_definition
  `list_enc' f xs = Tree 0 (MAP f xs)`;;

let num_tree_enc_dec_list_dec'_def = new_definition
  `num_tree_enc_dec_list_dec' f (Tree _ xs) = MAP f xs`;;

let list_enc'_mem = prove
 (`(!x. MEM x xs ==> g (f x) = x) ==>
   num_tree_enc_dec_list_dec' g (list_enc' f xs) = xs`,
  CHEAT_TAC);;

let list_enc'_thm = prove
 (`(!x. g (f x) = x) ==>
   num_tree_enc_dec_list_dec' g (list_enc' f xs) = xs`,
  CHEAT_TAC);;
add_simp list_enc'_thm;;

let list_enc'_cong = prove
 (`!l1 l2 f f'.
     (l1 = l2) /\ (!x. MEM x l2 ==> (f x = f' x)) ==>
     (list_enc' f l1 = list_enc' f' l2)`,
  CHEAT_TAC);;

let list_dec'_cong = prove
 (`!l1 l2 f f'.
     (l1 = l2) /\ (!x. MEM x (num_tree_enc_dec_list_dec' I l2) ==> (f x = f'
       x)) ==>
     (num_tree_enc_dec_list_dec' f l1 = num_tree_enc_dec_list_dec' f' l2)`,
  CHEAT_TAC);;

(* HOL4 num_tree_enc_decScript.sml:229: ML code, not ported *)

(* string *)

let list_chr_dec'_def = define_cases
  `(list_chr_dec' [] = []) /\
   (list_chr_dec' (CONS x xs) = CONS (chr_dec' x) (list_chr_dec' xs))`;;

let string_dec'_def = new_definition
  `string_dec' (Tree _ xs) = IMPLODE (list_chr_dec' xs)`;;

let string_dec'_intro = prove
 (`num_tree_enc_dec_list_dec' chr_dec' = string_dec'`,
  CHEAT_TAC);;

(* pair *)

let pair_enc'_def = new_definition
  `pair_enc' f f' (x,y) = Tree 0 [f x; f' y]`;;

let pair_dec'_def = new_definition
  `pair_dec' f f' (Tree _ xs) = (f (num_tree_enc_dec_nth 0 xs),f'
  (num_tree_enc_dec_nth 1 xs))`;;

let pair_enc'_fst_snd = prove
 (`g (f (FST x)) = FST x /\ g' (f' (SND x)) = SND x ==>
   pair_dec' g g' (pair_enc' f f' x) = x`,
  CHEAT_TAC);;

let pair_enc'_thm = prove
 (`(!x. g (f x) = x) /\ (!x. g' (f' x) = x) ==>
   pair_dec' g g' (pair_enc' f f' x) = x`,
  CHEAT_TAC);;
add_simp pair_enc'_thm;;

let pair_enc'_cong = prove
 (`!l1 l2 f f' g g'.
     (l1 = l2) /\
     (!x. x = FST l1 ==> (f x = f' x)) /\
     (!x. x = SND l1 ==> (g x = g' x)) ==>
     (pair_enc' f g l1 = pair_enc' f' g' l2)`,
  CHEAT_TAC);;

let pair_dec'_cong = prove
 (`!l1 l2 f f' g g'.
     (l1 = l2) /\
     (!x. x = num_tree_enc_dec_nth 0 (num_tree_enc_dec_list_dec' I l1) ==>
       (f x = f' x)) /\
     (!x. x = num_tree_enc_dec_nth 1 (num_tree_enc_dec_list_dec' I l1) ==>
       (g x = g' x)) ==>
     (pair_dec' f g l1 = pair_dec' f' g' l2)`,
  CHEAT_TAC);;

(* HOL4 num_tree_enc_decScript.sml:294: ML code, not ported *)

(* option *)

let option_enc'_def = define_cases
  `(option_enc' f NONE = Tree 0 []) /\
   (option_enc' f (SOME x) = Tree 1 [f x])`;;

let option_dec'_def = new_definition
  `option_dec' f (Tree n xs) = if n = 0 then NONE else SOME (f
  (num_tree_enc_dec_nth 0 xs))`;;

let option_enc'_thm = prove
 (`(!x. g (f x) = x) ==>
   option_dec' g (option_enc' f x) = x`,
  CHEAT_TAC);;
add_simp option_enc'_thm;;

(* The option counterpart of list_enc'_mem: usable when the round-trip
   property is only known for the value actually inside the option. *)
let option_enc'_some = prove
 (`(!y. x = SOME y ==> g (f y) = y) ==>
   option_dec' g (option_enc' f x) = x`,
  CHEAT_TAC);;

(* Needed so that a datatype with a recursive occurrence under an option
   can be defined: without these the termination checker cannot see the
   recursive call. *)

let option_enc'_cong = prove
 (`!l1 l2 f f'.
     (l1 = l2) /\ (!x. l2 = SOME x ==> (f x = f' x)) ==>
     (option_enc' f l1 = option_enc' f' l2)`,
  CHEAT_TAC);;

let option_dec'_cong = prove
 (`!l1 l2 f f'.
     (l1 = l2) /\ (!x. x = num_tree_enc_dec_nth 0
       (num_tree_enc_dec_list_dec' I l1) ==> (f x = f' x)) ==>
     (option_dec' f l1 = option_dec' f' l2)`,
  CHEAT_TAC);;

(* HOL4 num_tree_enc_decScript.sml:343: ML code, not ported *)

(* Size bounds for the decoder side of the above: option_dec'_cong exposes the
   recursive call at [nth 0 (list_dec' I t)], one level deeper than the plain
   [nth] the list case produces. *)

(* HOL4 num_tree_enc_decScript.sml:349-353: a theorem whose statement the
   port cannot state yet: num_tree1_size_eq *)

make_size "num_tree";;
let num_tree_size_nth = prove
 (`!xs i. num_tree_size (num_tree_enc_dec_nth i xs) <= list_size
  num_tree_size xs + 1`,
  CHEAT_TAC);;

let num_tree_size_nth_nth = prove
 (`!xs i j.
     num_tree_size (num_tree_enc_dec_nth i (num_tree_enc_dec_list_dec' I
       (num_tree_enc_dec_nth j xs))) <=
     list_size num_tree_size xs + 1`,
  CHEAT_TAC);;

(* word64 *)

let word64_enc'_def = new_definition
  `word64_enc' (n:word64) = Tree (w2n n) []`;;

let word64_dec'_def = new_definition
  `word64_dec' (Tree n xs) = (n2w n:word64)`;;
add_simp word64_dec'_def;;

let word64_dec_enc' = prove
 (`word64_dec' (word64_enc' n) = n`,
  CHEAT_TAC);;
add_simp word64_dec_enc';;

(* mlstring *)

let mlstring_enc'_def = new_definition
  `mlstring_enc' (implode s) = list_enc' chr_enc' s`;;

let mlstring_dec'_def = new_definition
  `mlstring_dec' = implode o (num_tree_enc_dec_list_dec' chr_dec')`;;

let mlstring_dec_enc' = prove
 (`mlstring_dec' (mlstring_enc' s) = s`,
  CHEAT_TAC);;
add_simp mlstring_dec_enc';;

(* and the interface *)
let _ = unhide_overloads ();;
