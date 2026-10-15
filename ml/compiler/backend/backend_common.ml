(* ======================================================== *)
(*  backend_common: ported from HOL4's
    compiler/backend/backend_commonScript.sml  *)
(* ======================================================== *)

(*
  Definitions that are common for many parts of the compiler backend.
*)

needs "lib/sptree.ml";;
(* HOL4 ancestors outside the port: arithmetic integer words *)

needs "lib/sptree.ml";;
(* HOL4 ancestors outside the port: (* for delete *) *)

let opw_INDUCT,opw_RECURSION = define_datatype
  "opw = backend_common_Andw | backend_common_Orw | \
   backend_common_Xor | backend_common_Add | backend_common_Sub";;
hol4_overload "Andw" "backend_common_Andw";;
hol4_overload "Orw" "backend_common_Orw";;
hol4_overload "Xor" "backend_common_Xor";;
hol4_overload "Add" "backend_common_Add";;
hol4_overload "Sub" "backend_common_Sub";;

(* Small general definition *)
let small_enough_int_def = cake_define
  `small_enough_int i <=> --268435457 <= i /\ i <= (268435457:int)`;;

(* these must match what the prim_types_program generates *)

let bind_tag_def = cake_define
  `bind_tag = 0`;;
let chr_tag_def = cake_define
  `chr_tag = 1`;;
let div_tag_def = cake_define
  `div_tag = 2`;;
let subscript_tag_def = cake_define
  `subscript_tag = 3`;;

let false_tag_def = cake_define
  `false_tag = 0`;;
let true_tag_def = cake_define
  `true_tag = 1`;;

let nil_tag_def = cake_define
  `nil_tag = 0`;;
let cons_tag_def = cake_define
  `cons_tag = 0`;;

let none_tag_def = cake_define
  `none_tag = 0`;;
let some_tag_def = cake_define
  `some_tag = 0`;;

let tuple_tag_def = cake_define
  `tuple_tag = 0`;;

let closure_tag_def = cake_define
  `closure_tag = (30:num)`;;
let partial_app_tag_def = cake_define
  `partial_app_tag = (31:num)`;;
let clos_tag_shift_def = cake_define
  `clos_tag_shift tag = (if tag < 30 then tag:num else tag + 2)`;;

(* Trace of an expression through the compiler, for exploring
   transformations *)
let tra_INDUCT,tra_RECURSION = define_datatype
  "tra = backend_common_SourceLoc (num) (num) (num) (num) | \
   backend_common_Cons (tra) (num) | backend_common_Union (tra) (tra) \
   | backend_common_None";;
hol4_overload "SourceLoc" "backend_common_SourceLoc";;
hol4_overload "Cons" "backend_common_Cons";;
hol4_overload "Union" "backend_common_Union";;
hol4_overload "None" "backend_common_None";;

(* The code below replaces "Cons" in hol output with the chosen symbol
   *)
(* HOL4 ML code, not ported:
val _ = set_fixity "▷" (Infixl 480);
*)
(* HOL4 overload (expanded in the port):
     None =  *)

(* An "orphan" expression is one that originates directly from a
   declaration.
* This happens in source_to_mod, and in con_to_dec. It is an orphan
  because
* declarations don't come annotated with their source program locations
  right
* now point (but they might in the future).
* This is a trace that can be used as a basis for traces for orphan
  expressions.
* It's structure guarantees it will not conflict with any trace
  originating from
* source, since the always start with four Cons, indicating source
  position. *)
let orphan_trace_def = cake_define
  `orphan_trace = SourceLoc 2 2 1 1`;;

(* Create new Cons trace, unless original trace is `None`, indicating
   traces are
* turned off. *)
let mk_cons_def = cake_define
  `mk_cons tr n =
     (match tr with None -> None | _1 -> Cons tr n)`;;

(* HOL4 ML code, not ported:
val _ = set_fixity "§" (Infixl 480);
*)
(* HOL4 overload (expanded in the port):
     None =  *)

(* Create new Cons trace, unless any of the original traces are `None`,
* indicating traces are turned off. *)
let mk_union_def = cake_define
  `mk_union tr1 tr2 =
     (match tr1 with None -> None | _2 -> (match tr2 with None ->
       None | _3 -> Union tr1 tr2))`;;

let bool_to_tag_def = cake_define
  `bool_to_tag b = (if b then true_tag else false_tag)`;;

let stack_num_stubs_def = cake_define
  `stack_num_stubs = 5`;;

let word_num_stubs_def = cake_define
  `word_num_stubs = stack_num_stubs + 1 + 1`;;

let data_num_stubs_def = cake_define
  `data_num_stubs = word_num_stubs + 32 + 23`;;

let bvl_num_stubs_def = cake_define
  `bvl_num_stubs = data_num_stubs + 9 + 1`;;

let bvl_to_bvi_namespaces_def = cake_define
  `bvl_to_bvi_namespaces = 4`;;

(* shift values, per dimindex(:α) *)
let word_shift_def = cake_define
  `backend_common_word_shift (:'a) =
     (if dimindex (:'a) = 32 then 2 else 3:num)`;;
hol4_overload "word_shift" "backend_common_word_shift";;

let upper_w2w_def = cake_define
  `upper_w2w (w:'a word) =
     (if dimindex (:'a) = 32 then w2w w << 32 else (w2w w):word64)`;;

let word_add_carry_def = cake_define
  `word_add_carry (l) (r) (c) =
   (let
     res = w2n l + w2n r + (if c = (n2w 0) then 0 else 1) in
     (n2w res,(if dimword (:'ga) <= res then (n2w 1) else (n2w
       0))))`;;

(* TODO: prefer this over `FOLDR delete`? Consider upstreaming this and
   its associated lemmas (e.g. `domain_list_delete` in loop_liveProof).
     *)
let list_delete_def = cake_define
  `list_delete [] s = s /\
   list_delete (v :: vs) s = list_delete vs (delete v s)`;;
