(* ======================================================== *)
(*  num_list_enc_dec: ported from HOL4's
    compiler/backend/serialiser/num_list_enc_decScript.sml
    A definition theory, with 52 definitions and 38 theorems.
    Needed by backend_enc_dec.ml, decodeProg.ml and
    num_tree_enc_dec.ml.  *)
(* ======================================================== *)

(*
  Encoders and decoders to/from types represented as prefixes of lists
  of natural numbers.
*)

needs "basis/pure/mlstring.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/namespace.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "num_list_enc_dec"
  ["misc"; "ml_translator"; "namespace"];;
(* HOL4 ancestors outside the port: integer *)

(* definitions of what good enc/dec functions are *)

let dec_ok_def = new_definition
  `dec_ok dec <=>
     (!i. LENGTH ((SND (dec i)):num list) <= LENGTH (i:num list))`;;

let enc_dec_ok_def = new_definition
  `enc_dec_ok enc dec <=>
     dec_ok dec /\
     (!x (xs:num list). dec (APPEND (append (enc x)) xs) = (x,xs))`;;

let dec_ok_simp = prove
 (`dec_ok ((f ## I) o d) = dec_ok d`,
  CHEAT_TAC);;
add_simp dec_ok_simp;;

let enc_dec_ok_o = prove
 (`enc_dec_ok e d /\ (!x. f (g x) = x) ==>
   enc_dec_ok (e o g) ((f ## I) o d)`,
  CHEAT_TAC);;

(* conditional enc/dec functions *)

let enc_dec_ok'_def = new_definition
  `enc_dec_ok' p enc dec <=>
     dec_ok dec /\
     (!x (xs:num list). p x ==> dec (APPEND (append (enc x)) xs) =
       (x,xs))`;;

let IMP_enc_dec_ok = prove
 (`enc_dec_ok enc dec ==> enc_dec_ok' (K T) enc dec`,
  CHEAT_TAC);;

let enc_dec_ok'_IMP = prove
 (`enc_dec_ok' (\x. T) enc dec ==> enc_dec_ok enc dec`,
  CHEAT_TAC);;

let const_dec_def = new_definition
  `const_dec a xs = (a,(xs:num list))`;;

let enc_dec_ok'_const = prove
 (`!x. enc_dec_ok' ((=) x) (K (misc_List [])) (const_dec x)`,
  CHEAT_TAC);;

let enc_dec_ok'_o = prove
 (`enc_dec_ok' p e d /\ (!x. f (g x) = x) ==>
   enc_dec_ok' (p o g) (e o g) ((f ## I) o d)`,
  CHEAT_TAC);;

(* misc *)

let fix_res_def = new_definition
  `fix_res ns (x,ns') =
     if LENGTH ns < LENGTH ns' then (x,ns) else (x,ns')`;;

let fix_res_IMP = prove
 (`(x,ns2) = fix_res ns1 y ==> LENGTH ns2 <= LENGTH ns1`,
  CHEAT_TAC);;

(* unit *)

let unit_enc_def = new_definition
  `unit_enc (n:1) = misc_List []`;;

let unit_dec_def = new_definition
  `unit_dec ns = (one,(ns:num list))`;;

let unit_enc_dec_ok = prove
 (`enc_dec_ok unit_enc unit_dec`,
  CHEAT_TAC);;

(* num *)

let num_enc_def = new_definition
  `num_enc n = misc_List [n:num]`;;

let num_dec_def = new_definition
  `num_dec ns =
     match ns with [] -> ((0:num),[])
     | (CONS r rs) -> (r,rs)`;;

let num_enc_dec_ok = prove
 (`enc_dec_ok num_enc num_dec`,
  CHEAT_TAC);;

(* word64 *)

let word64_enc_def = new_definition
  `word64_enc (w:word64) = misc_List [w2n w]`;;

let word64_dec_def = new_definition
  `word64_dec ns =
     match ns with [] -> (((n2w 0):word64),[])
     | (CONS r rs) -> (n2w r,rs)`;;

let word64_enc_dec_ok = prove
 (`enc_dec_ok word64_enc word64_dec`,
  CHEAT_TAC);;

(* list *)

let list_enc_def = new_definition
  `list_enc e xs =
     misc_Append (misc_List [LENGTH xs]) (ITLIST (\x y. misc_Append (e x)
       y) xs (misc_List []))`;;

let list_dec'_def = define_cases
  `(num_list_enc_dec_list_dec' 0 d ns = ([],ns)) /\
   (num_list_enc_dec_list_dec' (SUC k) d ns =
      let (x1,ns1) = d ns in
      let (xs1,ns2) = num_list_enc_dec_list_dec' k d ns1 in
        (CONS x1 xs1,ns2))`;;

let list_dec_def = new_definition
  `list_dec d ns =
     match ns with [] -> ([],[])
     | (CONS n ns) -> num_list_enc_dec_list_dec' n d ns`;;

let list_dec'_length = prove
 (`!k d ns x ns1.
     num_list_enc_dec_list_dec' k d ns = (x,ns1) /\ dec_ok d ==>
     LENGTH ns1 <= LENGTH ns`,
  CHEAT_TAC);;

let list_dec_ok = prove
 (`dec_ok d ==>
   dec_ok (list_dec d)`,
  CHEAT_TAC);;

let list_enc_dec_ok = prove
 (`enc_dec_ok e d ==>
   enc_dec_ok (list_enc e) (list_dec d)`,
  CHEAT_TAC);;

(* bool *)

let bool_enc_def = new_definition
  `bool_enc = num_enc o (\b. if b then 1 else 0)`;;

let bool_dec_def = new_definition
  `bool_dec = (((=) 1) ## I) o num_dec`;;

let bool_enc_dec_ok = prove
 (`enc_dec_ok bool_enc bool_dec`,
  CHEAT_TAC);;

(* int *)

let int_enc_def = new_definition
  `int_enc =
     num_enc o (\n. if n < (&0) then 2 * num_of_int (abs n) + 1 else 2 *
       num_of_int (abs n))`;;

let int_dec_def = new_definition
  `int_dec =
     ((\r. if ODD r then (&0:int) - &(r DIV 2) else &(r DIV 2)) ## I) o
       num_dec`;;

let int_enc_dec_ok = prove
 (`enc_dec_ok int_enc int_dec`,
  CHEAT_TAC);;

(* word *)

let word_enc_def = new_definition
  `word_enc = num_enc o w2n`;;

let word_dec_def = new_definition
  `word_dec = ((\n. n2w n) ## I) o num_dec`;;

let word_enc_dec_ok = prove
 (`enc_dec_ok word_enc word_dec`,
  CHEAT_TAC);;

(* char *)

let char_enc_def = new_definition
  `char_enc = num_enc o ORD`;;

let safe_chr_def = new_definition
  `safe_chr n = CHR (n MOD 256)`;;

let char_dec_def = new_definition
  `char_dec = (safe_chr ## I) o num_dec`;;

let char_enc_dec_ok = prove
 (`enc_dec_ok char_enc char_dec`,
  CHEAT_TAC);;

(* string *)

let safe_chr_list_def = new_definition
  `safe_chr_list ns = MAP safe_chr ns`;;

let take_pad_def,take_pad_ind = define_guess
  `take_pad n (ns:num list) =
     if n = (0:num) then ([],ns) else let (xs,ys) = take_pad (n - 1) (TL ns)
       in
         match ns with [] -> (CONS 0 xs,ys)
         | (CONS x _) -> (CONS x xs,ys)`;;

let string_dec_def = new_definition
  `string_dec ns =
     match ns with [] -> ("",[])
     | (CONS n ns) ->
         let (xs,ys) = take_pad n ns in
           (IMPLODE (safe_chr_list xs),ys)`;;

let string_dec_thm = prove
 (`string_dec = list_dec char_dec`,
  CHEAT_TAC);;

let string_enc_dec_ok = prove
 (`enc_dec_ok (list_enc char_enc) string_dec`,
  CHEAT_TAC);;

let string_dec_ok = prove
 (`dec_ok string_dec`,
  CHEAT_TAC);;

(* mlstring *)

let mlstring_enc_def = new_definition
  `mlstring_enc (implode s) = list_enc char_enc s`;;

let mlstring_dec_def = new_definition
  `mlstring_dec = (implode ## I) o (list_dec char_dec)`;;

let mlstring_enc_dec_ok = prove
 (`enc_dec_ok mlstring_enc mlstring_dec`,
  CHEAT_TAC);;

let mlstring_dec_ok = prove
 (`dec_ok mlstring_dec`,
  CHEAT_TAC);;

(* prod *)

let prod_enc_def = new_definition
  `prod_enc e1 e2 (x,y) = misc_Append (e1 x) (e2 y)`;;

let prod_dec_def = new_definition
  `prod_dec d1 d2 ns =
     let (x,ns1) = d1 ns in
     let (y,ns2) = d2 ns1 in
       ((x,y),ns2)`;;

let prod_dec_ok = prove
 (`dec_ok d1 /\
   dec_ok d2 ==>
   dec_ok (prod_dec d1 d2)`,
  CHEAT_TAC);;

let prod_enc_dec_ok = prove
 (`enc_dec_ok e1 d1 /\
   enc_dec_ok e2 d2 ==>
   enc_dec_ok (prod_enc e1 e2) (prod_dec d1 d2)`,
  CHEAT_TAC);;

let prod_enc_dec_ok' = prove
 (`enc_dec_ok' p1 e1 d1 /\
   enc_dec_ok' p2 e2 d2 ==>
   enc_dec_ok' (\x. p1 (FST x) /\ p2 (SND x)) (prod_enc e1 e2) (prod_dec
     d1 d2)`,
  CHEAT_TAC);;

(* option *)

let option_enc_def = define_cases
  `(option_enc e NONE = misc_List [0]) /\
   (option_enc e (SOME y) = misc_Append (misc_List [1]) (e y))`;;

let option_dec_def = new_definition
  `option_dec d ns =
     match ns with [] -> (NONE,ns)
     | (CONS n ns) -> if n = 0 then (NONE,ns) else (SOME ## I) (d ns)`;;

let option_enc_dec_ok = prove
 (`enc_dec_ok e d ==>
   enc_dec_ok (option_enc e) (option_dec d)`,
  CHEAT_TAC);;

(* sum *)

let sum_enc_def = define_cases
  `(sum_enc e1 e2 (INL x) = misc_Append (misc_List [0]) (e1 x)) /\
   (sum_enc e1 e2 (INR y) = misc_Append (misc_List [1]) (e2 y))`;;

let sum_dec_def = new_definition
  `sum_dec d1 d2 ns =
     match ns with [] -> (INL ## I) (d1 ns)
     | (CONS n ns) -> if n = 0 then (INL ## I) (d1 ns) else (INR ## I)
       (d2 ns)`;;

let sum_enc_dec_ok = prove
 (`enc_dec_ok e1 d1 /\
   enc_dec_ok e2 d2 ==>
   enc_dec_ok (sum_enc e1 e2) (sum_dec d1 d2)`,
  CHEAT_TAC);;

(* sptree *)

let spt_enc'_def = define_cases
  `(spt_enc' e LN = misc_List [0]) /\
   (spt_enc' e (LS x) = misc_Append (misc_List [1]) (e x)) /\
   (spt_enc' e (BN t1 t2) =
      misc_Append (misc_List [2]) (misc_Append (spt_enc' e t1)
          (spt_enc' e t2))) /\
   (spt_enc' e (BS t1 x t2) =
      misc_Append (misc_List [3]) (misc_Append (spt_enc' e t1)
          (misc_Append (e x) (spt_enc' e t2))))`;;

let spt_depth_def,spt_depth_ind = define_guess
  `spt_depth x1 =
   match x1 with
     BN t1 t2 -> MAX (spt_depth t1) (spt_depth t2) + 1
   | BS t1 _ t2 -> MAX (spt_depth t1) (spt_depth t2) + 1
   | _ -> (0:num)`;;

let spt_enc''_def = new_definition
  `spt_enc'' e t = prod_enc num_enc (spt_enc' e) (spt_depth t,t)`;;

let spt_dec'_def = new_definition
  `spt_dec' k d ns =
     match ns with [] -> (LN,ns)
     | (CONS n ns) ->
        if n = (0:num) then (LN,ns)
        else if n = 1 then
          let (x,ns) = d ns in (LS x,ns)
        else if k = (0:num) then
          (LN,ns)
        else if n = 2 then
          let (t1,ns') = spt_dec' (k - 1) d ns in
          let (t2,ns') = spt_dec' (k - 1) d ns' in
            (BN t1 t2,ns')
        else let (t1,ns1) = spt_dec' (k - 1) d ns in
          let (x,ns2) = d ns1 in
          let (t2,ns3) = spt_dec' (k - 1) d ns2 in
            (BS t1 x t2,ns3)`;;

let spt_dec''_def = new_definition
  `spt_dec'' d ns =
     match ns with [] -> (LN,ns)
     | (CONS m ms) -> spt_dec' m d ms`;;

let spt_enc''_dec_ok = prove
 (`enc_dec_ok e d ==>
   enc_dec_ok (spt_enc'' e) (spt_dec'' d)`,
  CHEAT_TAC);;

let spt_enc_def,spt_enc_ind = define_guess
  `spt_enc e =
     sum_enc
       (list_enc (prod_enc num_enc e)) (spt_enc'' e) o
       (\t. if sptree_wf t then INL (toAList t) else INR t)`;;

let spt_dec_def,spt_dec_ind = define_guess
  `spt_dec d =
     ((\x. match x with INL xs -> fromAList xs | INR t -> t) ## I) o
      sum_dec (list_dec (prod_dec num_dec d)) (spt_dec'' d)`;;

let spt_enc_dec_ok = prove
 (`enc_dec_ok e d ==>
   enc_dec_ok (spt_enc e) (spt_dec d)`,
  CHEAT_TAC);;

(* namespace -- instantiated to (mlstring, mlstring, 'a) *)

(* the clauses in two quotations: xs is (('n , 'v) alist), (_#_)list and
   (_)list; ys is (('m , namespace) alist) and (_)list, which one quotation
   cannot typecheck *)
let namespace_enc'_def,namespace_enc'_ind = define_guess_clauses
  [`namespace_enc' e (Bind xs ys) =
      (let ns1 = list_enc (prod_enc mlstring_enc e) xs in
       let ns2 = namespace_enc'_list e ys in
         misc_Append ns1 ns2)`;
   `(namespace_enc'_list e [] = misc_List [0]) /\
    (namespace_enc'_list e (CONS (m,x) xs) =
      misc_Append (misc_Append (misc_List [1]) (mlstring_enc m))
        (misc_Append (namespace_enc' e x) (namespace_enc'_list e xs)))`];;

(* the clauses in two quotations: xs is (('n , 'v) alist), (_#_)list and
   (_)list; ys is (('m , namespace) alist) and (_)list, which one quotation
   cannot typecheck *)
let namespace_depth_def,namespace_depth_ind = define_guess_clauses
  [`namespace_depth (Bind xs ys) = 1 + namespace_depth_list ys`;
   `(namespace_depth_list [] = 0) /\
    (namespace_depth_list (CONS (m,x) xs) =
      1 + MAX (namespace_depth x) (namespace_depth_list xs))`];;

let namespace_enc_def,namespace_enc_ind = define_guess
  `namespace_enc e t = prod_enc num_enc (namespace_enc' e) (namespace_depth
  t,t)`;;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL (k,_,ns) -> k
                                   | INR (k,_,ns) -> k)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 num_list_enc_decScript.sml:639-643: the tactic that proves the
   termination *)
let namespace_dec'_def,namespace_dec'_ind = define_guess
  `(namespace_dec' k d ns =
      (if k = (0:num) then (Bind [] [],ns) else let (xs,ns1) = list_dec
          (prod_dec mlstring_dec d) ns in
         let (ys,ns2) = namespace_dec'_list (k - 1) d ns1 in
           (Bind xs ys,ns2))) /\
   (namespace_dec'_list k d ns =
      match ns with [] -> ([],ns)
      | (CONS n rest) ->
        if n = 0 then ([],rest) else if k = (0:num) then ([],ns) else let
            (m,ns) = mlstring_dec rest in
          let (x,ns) = namespace_dec' (k - 1) d ns in
          let (ys,ns) = namespace_dec'_list (k - 1) d ns in
            (CONS (m,x) ys,ns))`;;

let namespace_dec_def,namespace_dec_ind = define_guess
  `namespace_dec d ns =
     match ns with [] -> (Bind [] [],ns)
     | (CONS m ms) -> namespace_dec' m d ms`;;

let dec_ok_namespace_dec' = prove
 (`!k. dec_ok d ==> dec_ok (namespace_dec' k d)`,
  CHEAT_TAC);;

let namespace_enc_dec_ok = prove
 (`enc_dec_ok e d ==>
   enc_dec_ok (namespace_enc e) (namespace_dec d)`,
  CHEAT_TAC);;

(* app_rev *)

let append_rev_def,append_rev_ind = define_guess
  `(append_rev misc_Nil res = res) /\
   (append_rev (misc_List xs) res = REV xs res) /\
   (append_rev (misc_Append l1 l2) res = append_rev l2 (append_rev l1 res))`;;

let append_rev_thm = prove
 (`!l res. append_rev l res = APPEND (REVERSE (append l)) res`,
  CHEAT_TAC);;

(* encoding decoding from characters *)

(* HOL4 num_list_enc_decScript.sml:742: the overload CUT, which the port
   expands *)
(* HOL4 num_list_enc_decScript.sml:743: the overload SHIFT, which the port
   expands *)

(* [local] *)
let good_chars = prove
 (`ORD (CHR 32) <= (32:num) /\ (32:num) + (30:num) + (30:num) <= ORD (CHR 92)`,
  CHEAT_TAC);;

let num_list_enc_dec_num_to_chars_def,num_list_enc_dec_num_to_chars_ind =
  define_guess
  `num_list_enc_dec_num_to_chars n =
     if n < (30:num) then [CHR (n + (32:num))]
     else CONS (CHR ((n MOD (30:num)) + (32:num) + (30:num)))
       (num_list_enc_dec_num_to_chars (n DIV (30:num)))`;;

let rev_nums_to_chars_def,rev_nums_to_chars_ind = define_guess
  `(rev_nums_to_chars [] res = res) /\
   (rev_nums_to_chars (CONS n ns) res =
      rev_nums_to_chars ns (APPEND (num_list_enc_dec_num_to_chars n)
          res))`;;

let nums_to_chars_def,nums_to_chars_ind = define_guess
  `(nums_to_chars [] = []) /\
   (nums_to_chars (CONS n ns) =
      if n < (30:num) then CONS (CHR (n + (32:num))) (nums_to_chars ns)
      else CONS (CHR ((n MOD (30:num)) + (32:num) + (30:num)))
          (nums_to_chars (CONS (n DIV (30:num)) ns)))`;;

let dec_next_def,dec_next_ind = define_guess
  `(dec_next k l [] = (k,[])) /\
   (dec_next k l (CONS n ns) =
      let m = ORD n - (32:num) in
        if m < (30:num) then (k + l * m,ns)
        else dec_next (k + l * (m - (30:num))) (l * (30:num)) ns)`;;

(* [local] *)
let dec_next_LENGTH = prove
 (`!k ks n l t. (k,ks) = dec_next n l t ==> LENGTH ks <= LENGTH t`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE LENGTH
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 num_list_enc_decScript.sml:790-796: the tactic that proves the
   termination *)
let chars_to_nums_def,chars_to_nums_ind = define_guess
  `chars_to_nums ns =
     if NULL ns then [] else let (k,ks) = dec_next 0 1 ns in CONS k
       (chars_to_nums ks)`;;

let dec_next_nums_to_chars = prove
 (`!h l ns k.
     dec_next k ((30:num) EXP l) (nums_to_chars (CONS h ns)) = (k +
       ((30:num) EXP l) * h,nums_to_chars ns)`,
  CHEAT_TAC);;

let chars_to_nums_nums_to_chars = prove
 (`!ns. chars_to_nums (nums_to_chars ns) = ns`,
  CHEAT_TAC);;

(* [local] *)
let nums_to_chars_APPEND = prove
 (`!xs ys. nums_to_chars (APPEND xs ys) = APPEND (nums_to_chars xs)
  (nums_to_chars ys)`,
  CHEAT_TAC);;

let rev_nums_to_chars_thm = prove
 (`!ns res. rev_nums_to_chars ns res = APPEND (nums_to_chars (REVERSE ns))
  res`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
