(* ======================================================== *)
(*  backend_common: ported from HOL4's
    compiler/backend/backend_commonScript.sml
    A definition theory, with 28 definitions, 2 datatypes and 3
    theorems.  Needed by 67 files of the port.  *)
(* ======================================================== *)

(*
  Definitions that are common for many parts of the compiler backend.
*)

needs "lib/sptree.ml";;
(* for delete *)

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "backend_common" [];;
(* HOL4 ancestors outside the port: arithmetic integer words *)

let opw_INDUCT,opw_RECURSION = define_datatype
  "opw = backend_common_Andw | backend_common_Orw | \
   backend_common_Xor | backend_common_Add | backend_common_Sub";;
hol4_overload "Andw" "backend_common_Andw";;
hol4_overload "Orw" "backend_common_Orw";;
hol4_overload "Xor" "backend_common_Xor";;
hol4_overload "Add" "backend_common_Add";;
hol4_overload "Sub" "backend_common_Sub";;

(* Small general definition *)
let small_enough_int_def = new_definition
  `small_enough_int i <=> --(&268435457) <= i /\ i <=
  ((&268435457):int)`;;

(* these must match what the prim_types_program generates *)

let bind_tag_def = new_definition
  `bind_tag = 0`;;
let chr_tag_def = new_definition
  `chr_tag = 1`;;
let div_tag_def = new_definition
  `div_tag = 2`;;
let subscript_tag_def = new_definition
  `subscript_tag = 3`;;

let false_tag_def = new_definition
  `false_tag = 0`;;
let true_tag_def = new_definition
  `true_tag = 1`;;

let nil_tag_def = new_definition
  `nil_tag = 0`;;
let cons_tag_def = new_definition
  `cons_tag = 0`;;

let none_tag_def = new_definition
  `none_tag = 0`;;
let some_tag_def = new_definition
  `some_tag = 0`;;

let tuple_tag_def = new_definition
  `tuple_tag = 0`;;

let closure_tag_def = new_definition
  `closure_tag = (30:num)`;;
let partial_app_tag_def = new_definition
  `partial_app_tag = (31:num)`;;
let clos_tag_shift_def = new_definition
  `clos_tag_shift tag = (if tag < 30 then tag:num else tag + 2)`;;

(* Trace of an expression through the compiler, for exploring transformations *)
let tra_INDUCT,tra_RECURSION = define_datatype
  "tra = backend_common_SourceLoc (num) (num) (num) (num) \
   // start-row\n\
   // start-col\n\
   // end-row\n\
   // end-col\n\
   | backend_common_Cons (tra) (num) | backend_common_Union (tra) \
   (tra) | backend_common_None \
   // Dead trace, do not make traces at all";;
hol4_overload "SourceLoc" "backend_common_SourceLoc";;
hol4_overload "Cons" "backend_common_Cons";;
hol4_overload "Union" "backend_common_Union";;
hol4_overload "None" "backend_common_None";;

(* The code below replaces "Cons" in hol output with the chosen symbol *)
(* HOL4 backend_commonScript.sml:83: ML code, not ported *)
(* HOL4 backend_commonScript.sml:84: the overload ▷, which the port
   writes as an application of backend_common_Cons *)

(* An "orphan" expression is one that originates directly from a declaration.
* This happens in source_to_mod, and in con_to_dec. It is an orphan because
* declarations don't come annotated with their source program locations right
* now point (but they might in the future).
* This is a trace that can be used as a basis for traces for orphan expressions.
* It's structure guarantees it will not conflict with any trace originating from
* source, since the always start with four Cons, indicating source position. *)
let orphan_trace_def = new_definition
  `orphan_trace = backend_common_SourceLoc 2 2 1 1`;;

(* Create new Cons trace, unless original trace is `None`, indicating traces are
* turned off. *)
let mk_cons_def = new_definition
  `mk_cons tr n =
     (match tr with backend_common_None -> backend_common_None |
       _1 -> backend_common_Cons tr n)`;;

(* HOL4 backend_commonScript.sml:106: ML code, not ported *)
(* HOL4 backend_commonScript.sml:107: the overload §, which the port
   writes as an application of mk_cons *)

(* Create new Cons trace, unless any of the original traces are `None`,
* indicating traces are turned off. *)
let mk_union_def = new_definition
  `mk_union tr1 tr2 =
     (match tr1 with backend_common_None -> backend_common_None |
       _2 -> (match tr2 with backend_common_None ->
       backend_common_None | _3 -> backend_common_Union tr1 tr2))`;;

let bool_to_tag_def = new_definition
  `bool_to_tag b = (if b then true_tag else false_tag)`;;

let stack_num_stubs_def = new_definition
  `stack_num_stubs = 5`;;

let word_num_stubs_def = new_definition
  `word_num_stubs = stack_num_stubs + 1 +
             // raise
             1
   // store consts`;;

let data_num_stubs_def = new_definition
  `data_num_stubs = word_num_stubs +
          // general:
          32 +
              // bignum:
              23`;;

let bvl_num_stubs_def = new_definition
  `bvl_num_stubs = data_num_stubs + 9 +
             // dummy to make it a multiple of 4
             1`;;

let bvl_to_bvi_namespaces_def = new_definition
  `bvl_to_bvi_namespaces = 4`;;

let data_num_stubs_EVEN = prove
 (`EVEN data_num_stubs`,
  (REWRITE_TAC[data_num_stubs_def; word_num_stubs_def;
    stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV));;

let bvl_num_stub_MOD = prove
 (`bvl_num_stubs MOD bvl_to_bvi_namespaces = 0`,
  (REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def;
    word_num_stubs_def;
               stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN
   CONV_TAC NUM_REDUCE_CONV));;

(* shift values, per dimindex(:α) *)
let word_shift_def = new_definition
  `backend_common_word_shift (:'a) =
     // this could be defined as LOG 2 (dimindex(:'a)) - 3, but I want
     // to be sure that LOG doesn't unnecessarily end up in the
     // generated CakeML code
     (if dimindex (:'a) = 32 then 2 else 3:num)`;;
hol4_overload "word_shift" "backend_common_word_shift";;

let upper_w2w_def = new_definition
  `upper_w2w (w:'a word) =
     (if dimindex (:'a) = 32 then w2w w << 32 else (w2w w):word64)`;;

let word_add_carry_def = new_definition
  `(word_add_carry (l:'a word) (r:'a word) (c:'a word):'a word#'a word)
  =
   (let
     res = w2n l + w2n r + (if c = (n2w 0) then 0 else 1) in
     (n2w res,(if dimword (:'a) <= res then (n2w 1) else (n2w
       0))))`;;

(* TODO: prefer this over `FOLDR delete`? Consider upstreaming this and
   its associated lemmas (e.g. `domain_list_delete` in loop_liveProof). *)
let list_delete_def,list_delete_ind = define_rec
  [`list_delete [] s = s`;
   `list_delete (v :: vs) s = list_delete vs (sptree_delete v s)`];;

let lookup_list_delete = prove
 (`!xs l n. sptree_lookup n (list_delete xs l) =
            (if MEM n xs then NONE else sptree_lookup n l)`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
