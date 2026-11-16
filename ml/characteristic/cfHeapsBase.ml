(* ======================================================== *)
(*  cfHeapsBase: ported from HOL4's
    characteristic/cfHeapsBaseScript.sml
    A definition theory, with 34 definitions, 3 datatypes and 99
    theorems.  Needed by 45 files of the port.  *)
(* ======================================================== *)

(*
  Defines the heap type that the separation logic used by CF uses.
  Also defines POSTv etc.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfHeapsBase"
  ["cfFFIType"; "semanticPrimitives"];;
(* HOL4 ancestors outside the port: integer alist llist *)

(*------------------------------------------------------------------*)
(** Heaps *)

(* HOL4 cfHeapsBaseScript.sml:14-22: code that the source has in a comment *)

let encode_pair_def = new_definition
  `encode_pair e1 e2 (x,y) = cfFFIType_Cons (e1 x) (e2 y)`;;

let encode_list_def = new_definition
  `encode_list e l = misc_List (MAP e l)`;;

let encode_list_11 = prove
 (`!xs ys.
      encode_list f xs = encode_list f ys /\
      (!x y. f x = f y <=> x = y) ==>
      xs = ys`,
  CHEAT_TAC);;

let encode_option_def = define_cases
  `(encode_option e NONE = misc_List []) /\
   (encode_option e (SOME x) = misc_List [e x])`;;

let encode_option_11 = prove
 (`!x y. encode_option f x = encode_option f y /\ (!x y. f x = f y <=> x = y)
  ==> x = y`,
  CHEAT_TAC);;

let encode_bool_def = define_cases
  `(encode_bool F = cfFFIType_Num 0) /\
   (encode_bool T = cfFFIType_Num 1)`;;

let encode_bool_11 = prove
 (`!x y. encode_bool x = encode_bool y <=> x = y`,
  CHEAT_TAC);;
add_simp encode_bool_11;;

let encode_int_def = new_definition
  `encode_int i = cfFFIType_Cons (encode_bool ((&0) <= i)) (cfFFIType_Num
  (cfFFIType_Num (abs i)))`;;

let encode_int_11 = prove
 (`!x y. encode_int x = encode_int y <=> x = y`,
  CHEAT_TAC);;
add_simp encode_int_11;;

let cfHeapsBase_ffi_result_INDUCT,cfHeapsBase_ffi_result_RECURSION =
  define_datatype
  "cfHeapsBase_ffi_result =
     FFIreturn (word8 list) ('ffi)
   | FFIdiverge";;

(* make an ffi_next function from base functions and encode/decode *)
let mk_ffi_next_def = new_definition
  `mk_ffi_next (encode,decode',ls) name conf bytes s =
     OPTION_BIND (ALOOKUP ls name) (\f.
     OPTION_BIND (decode' s) (\s.
     OPTION_BIND (f conf bytes s) (\r.
      match r with
        FFIreturn bytes s -> SOME (FFIreturn bytes (encode s))
      | FFIdiverge -> SOME FFIdiverge)))`;;

new_type_abbrev("cfHeapsBase_loc",`:num`);;

new_type_abbrev("ffi_next",`:mlstring->word8 list->word8 list->ffi->(ffi
   cfHeapsBase_ffi_result) option`);;

let heap_part_INDUCT,heap_part_RECURSION = define_datatype
  "heap_part =
     cfHeapsBase_Mem cfHeapsBase_loc (semanticPrimitives_v store_v)
   | cfHeapsBase_FFI_split
   | cfHeapsBase_FFI_part ffi ffi_next (mlstring list) (io_event list)
   | cfHeapsBase_FFI_full (io_event list)";;

new_type_abbrev("heap",`:heap_part->bool`);;
new_type_abbrev("hprop",`:heap->bool`);;

let res_INDUCT,res_RECURSION = define_datatype
  "res =
     cfHeapsBase_Val semanticPrimitives_v
   | cfHeapsBase_Exn semanticPrimitives_v
   | cfHeapsBase_FFIDiv mlstring (word8 list) (word8 list)
   | cfHeapsBase_Div (io_event llist)";;

(* HOL4 cfHeapsBaseScript.sml:109-110: the type abbreviation ffi_proj, which
   the port expands *)

let SPLIT3_def = new_definition
  `SPLIT3 (s:'a->bool) (u,v,w) =
     ((u UNION v UNION w = s) /\
      DISJOINT u v /\ DISJOINT v w /\ DISJOINT u w)`;;

(* HOL4 cfHeapsBaseScript.sml:118: code that the source has in a comment *)
(*                          UNION_DEF,SEP_EQ_def,EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER, *)
(*                          IN_DIFF] *)

(* HOL4 cfHeapsBaseScript.sml:122: code that the source has in a comment *)
(* HOL4 cfHeapsBaseScript.sml:123-125: a proof *)

(*------------------------------------------------------------------*)
(** Heap predicates *)

(* in set_sepTheory: emp, one, STAR, SEP_IMP, SEP_EXISTS, cond *)

(* STAR for post-conditions *)
let STARPOST_def = new_definition
  `STARPOST (Q:res->(heap_part->bool)->bool) (H:(heap_part->bool)->bool) =
     (\r. (Q r) * H)`;;

(* SEP_IMP lifted to post-conditions *)
let SEP_IMPPOST_def = new_definition
  `SEP_IMPPOST (Q1:res->(heap_part->bool)->bool)
  (Q2:res->(heap_part->bool)->bool) =
     (!r. SEP_IMP (Q1 r) (Q2 r))`;;

let SEP_IMPPOSTv_def = new_definition
  `SEP_IMPPOSTv (Q1:res->(heap_part->bool)->bool)
  (Q2:res->(heap_part->bool)->bool) =
     (!v. SEP_IMP (Q1 (cfHeapsBase_Val v)) (Q2 (cfHeapsBase_Val v)))`;;

let SEP_IMPPOSTe_def = new_definition
  `SEP_IMPPOSTe (Q1:res->(heap_part->bool)->bool)
  (Q2:res->(heap_part->bool)->bool) =
     (!e. SEP_IMP (Q1 (cfHeapsBase_Exn e)) (Q2 (cfHeapsBase_Exn e)))`;;

let SEP_IMPPOSTf_def = new_definition
  `SEP_IMPPOSTf (Q1:res->(heap_part->bool)->bool)
  (Q2:res->(heap_part->bool)->bool) =
     (!name conf bytes. SEP_IMP (Q1 (cfHeapsBase_FFIDiv name conf bytes))
       (Q2 (cfHeapsBase_FFIDiv name conf bytes)))`;;

let SEP_IMPPOSTd_def = new_definition
  `SEP_IMPPOSTd (Q1:res->(heap_part->bool)->bool)
  (Q2:res->(heap_part->bool)->bool) =
     (!io. SEP_IMP (Q1 (cfHeapsBase_Div io)) (Q2 (cfHeapsBase_Div io)))`;;

let SEP_IMPPOSTv_inv_def = new_definition
  `SEP_IMPPOSTv_inv (Q1:res->(heap_part->bool)->bool)
  (Q2:res->(heap_part->bool)->bool) =
     (SEP_IMPPOSTe Q1 Q2 /\ SEP_IMPPOSTf Q1 Q2 /\ SEP_IMPPOSTd Q1 Q2)`;;

let SEP_IMPPOSTe_inv_def = new_definition
  `SEP_IMPPOSTe_inv (Q1:res->(heap_part->bool)->bool)
  (Q2:res->(heap_part->bool)->bool) =
     (SEP_IMPPOSTv Q1 Q2 /\ SEP_IMPPOSTf Q1 Q2 /\ SEP_IMPPOSTd Q1 Q2)`;;

(* Garbage collection predicate *)
let GC_def = new_definition
  `(GC:(heap_part->bool)->bool) = SEP_EXISTS (\H. H)`;;

(* Injections for post-conditions *)
let POST_def = new_definition
  `POST (Qv:semanticPrimitives_v->(heap_part->bool)->bool)
  (Qe:semanticPrimitives_v->(heap_part->bool)->bool) (Qf:mlstring->word8
  list->word8 list->(heap_part->bool)->bool) (Qd:io_event llist->bool) = (\r.
     match r with cfHeapsBase_Val v -> Qv v
      | cfHeapsBase_Exn e -> Qe e
      | cfHeapsBase_FFIDiv name conf bytes -> Qf name conf bytes
      | cfHeapsBase_Div io -> cond (Qd io))`;;

let POSTv_def = new_definition
  `(POSTv) (Qv:semanticPrimitives_v->(heap_part->bool)->bool) =
         POST Qv (\e. cond F) (\name conf bytes. cond F) (\io. F)`;;

let POSTe_def = new_definition
  `(POSTe) (Qe:semanticPrimitives_v->(heap_part->bool)->bool) =
         POST (\v. cond F) Qe (\name conf bytes. cond F) (\io. F)`;;

let POSTf_def = new_definition
  `(POSTf) (Qf:mlstring->word8 list->word8 list->(heap_part->bool)->bool) =
         POST (\v. cond F) (\e. cond F) Qf (\io. F)`;;

let POSTd_def = new_definition
  `(POSTd) (Qd:io_event llist->bool) =
         POST (\v. cond F) (\e. cond F) (\name conf bytes. cond F) Qd`;;

let POSTve_def = new_definition
  `POSTve (Qv:semanticPrimitives_v->(heap_part->bool)->bool)
  (Qe:semanticPrimitives_v->(heap_part->bool)->bool) =
     POST Qv Qe (\name conf bytes. cond F) (\io. F)`;;

let POSTvd_def = new_definition
  `POSTvd (Qv:semanticPrimitives_v->(heap_part->bool)->bool) (Qd:io_event
  llist->bool) =
     POST Qv (\e. cond F) (\name conf bytes. cond F) Qd`;;

let POSTed_def = new_definition
  `POSTed (Qe:semanticPrimitives_v->(heap_part->bool)->bool) (Qd:io_event
  llist->bool) =
     POST (\v. cond F) Qe (\name conf bytes. cond F) Qd`;;

let POST_F_def = new_definition
  `(POST_F (r:res):(heap_part->bool)->bool) = cond F`;;

(* cond specialized to equality to some value; as a post-condition *)
let cond_eq_def = new_definition
  `cond_eq v = (\x. cond (x = v))`;;

(* A single memory cell. *)
let cell_def = new_definition
  `cell l v = set_sep_one (cfHeapsBase_Mem l v)`;;

(* A reference cell, as a convenience wrapper over cell and Refv *)
let REF_def = new_definition
  `REF rv xv =
     SEP_EXISTS (\loc. cond (rv = semanticPrimitives_Loc T loc) * cell
       loc (semanticPrimitives_Refv xv))`;;

(* An array cell, as a wrapper over cell and Varray *)
let ARRAY_def = new_definition
  `ARRAY av vl =
     SEP_EXISTS (\loc. cond (av = semanticPrimitives_Loc T loc) * cell
       loc (semanticPrimitives_Varray vl))`;;

(* A bytearray cell, as a wrapper over cell and W8array *)
let W8ARRAY_def = new_definition
  `W8ARRAY av wl =
     SEP_EXISTS (\loc. cond (av = semanticPrimitives_Loc T loc) * cell
       loc (semanticPrimitives_W8array wl))`;;

let IO_def = new_definition
  `IO s u ns = SEP_EXISTS (\events. set_sep_one (cfHeapsBase_FFI_part s u ns
  events) * cond (~(MEM (implode "") ns)))`;;

let IOx_def = new_definition
  `IOx (encode,decode',ls) s =
     IO (encode s) (mk_ffi_next (encode,decode',ls)) (MAP FST ls)`;;

let mk_proj1_def = new_definition
  `mk_proj1 (encode,decode',ls) s =
     MAP (\x. (x,encode s)) (MAP FST ls)`;;

let mk_proj2_def = new_definition
  `mk_proj2 (encode,decode',ls) =
     (MAP FST ls,mk_ffi_next (encode,decode',ls))`;;

(*------------------------------------------------------------------*)
(** Notations for heap predicates *)

(* HOL4 cfHeapsBaseScript.sml:274-275: the overload *+, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:277-278: the overload ==>>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:280-281: the overload ==+>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:283-284: the overload ==v>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:286-287: the overload ==e>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:289-290: the overload ==f>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:292-293: the overload ==d>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:295-296: the overload =~v>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:298-299: the overload =~e>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:301: code that the source has in a comment *)
(*                   block_style = (AroundEachPhrase, (PP.CONSISTENT,2)), *)
(*                   paren_style = OnlyIfNecessary, *)
(*                   pp_elements = [TOK "<", TM, TOK ">"]} *)

(* HOL4 cfHeapsBaseScript.sml:306: code that the source has in a comment *)
(*                   block_style = (AroundEachPhrase, (PP.CONSISTENT,2)), *)
(*                   paren_style = OnlyIfNecessary, *)
(*                   pp_elements = [TOK "<=", TM, TOK ">"]} *)

(* HOL4 cfHeapsBaseScript.sml:311: the overload &, which the port expands *)

(* HOL4 cfHeapsBaseScript.sml:313-314: the overload ~~>>, which the port
   expands *)

(* HOL4 cfHeapsBaseScript.sml:316-317: the overload ~~>, which the port
   expands *)

(*------------------------------------------------------------------*)
(** Low level lemmas about SPLIT and SPLIT3 *)

let SPLIT3_of_SPLIT_emp3 = prove
 (`!h h1 h2. SPLIT h (h1,h2) ==> SPLIT3 h (h1,h2,{})`,
  CHEAT_TAC);;

let SPLIT3_of_SPLIT_emp2 = prove
 (`!h h1 h3. SPLIT h (h1,h3) ==> SPLIT3 h (h1,{},h3)`,
  CHEAT_TAC);;

let SPLIT3_swap23 = prove
 (`!h h1 h2 h3. SPLIT3 h (h1,h2,h3) ==> SPLIT3 h (h1,h3,h2)`,
  CHEAT_TAC);;

let SPLIT_emp1 = prove
 (`!h h'. SPLIT h ({},h') = (h' = h)`,
  CHEAT_TAC);;

let SPLIT_emp2 = prove
 (`!h h'. SPLIT h (h',{}) = (h' = h)`,
  CHEAT_TAC);;

let SPLIT3_emp1 = prove
 (`!h h1 h2. SPLIT3 h ({},h1,h2) = SPLIT h (h1,h2)`,
  CHEAT_TAC);;

let SPLIT3_emp3 = prove
 (`!h h1 h2. SPLIT3 h (h1,h2,{}) = SPLIT h (h1,h2)`,
  CHEAT_TAC);;

let SPLIT_of_SPLIT3_2u3 = prove
 (`!h h1 h2 h3. SPLIT3 h (h1,h2,h3) ==> SPLIT h (h1,h2 UNION h3)`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(** Additionnal properties of STAR *)

let STARPOST_emp = prove
 (`!Q. Q STARPOST emp = Q`,
  CHEAT_TAC);;

let SEP_IMP_frame_single_l = prove
 (`!H' R.
     (emp (SEP_IMP) H') ==>
     (R (SEP_IMP) H' * R)`,
  CHEAT_TAC);;

let SEP_IMP_frame_single_r = prove
 (`!H R.
     (H (SEP_IMP) emp) ==>
     (H * R (SEP_IMP) R)`,
  CHEAT_TAC);;

let SEP_IMP_cell_frame = prove
 (`!H H' l v v'.
     (v = v') /\ (H (SEP_IMP) H') ==>
     (H * l (cell) v (SEP_IMP) H' * l (cell) v')`,
  CHEAT_TAC);;

let SEP_IMP_cell_frame_single_l = prove
 (`!H' l v v'.
     (v = v') /\ (emp (SEP_IMP) H') ==>
     (l (cell) v (SEP_IMP) H' * l (cell) v')`,
  CHEAT_TAC);;

let SEP_IMP_cell_frame_single_r = prove
 (`!H l v v'.
     (v = v') /\ (H (SEP_IMP) emp) ==>
     (H * l (cell) v (SEP_IMP) l (cell) v')`,
  CHEAT_TAC);;

let SEP_IMP_cell_frame_single = prove
 (`!H l v v'.
     (v = v') /\ (emp (SEP_IMP) emp) ==>
     (l (cell) v (SEP_IMP) l (cell) v')`,
  CHEAT_TAC);;

let SEP_IMP_REF_frame = prove
 (`!H H' r v v'.
     (v = v') /\ (H (SEP_IMP) H') ==>
     (H * r (REF) v (SEP_IMP) H' * r (REF) v')`,
  CHEAT_TAC);;

let SEP_IMP_REF_frame_single_l = prove
 (`!H' r v v'.
     (v = v') /\ (emp (SEP_IMP) H') ==>
     (r (REF) v (SEP_IMP) H' * r (REF) v')`,
  CHEAT_TAC);;

let SEP_IMP_REF_frame_single_r = prove
 (`!H r v v'.
     (v = v') /\ (H (SEP_IMP) emp) ==>
     (H * r (REF) v (SEP_IMP) r (REF) v')`,
  CHEAT_TAC);;

let SEP_IMP_REF_frame_single = prove
 (`!H r v v'.
     (v = v') /\ (emp (SEP_IMP) emp) ==>
     (r (REF) v (SEP_IMP) r (REF) v')`,
  CHEAT_TAC);;

let SEP_IMP_ARRAY_frame = prove
 (`!H H' a vl vl'.
     (vl = vl') /\ (H (SEP_IMP) H') ==>
     (H * ARRAY a vl (SEP_IMP) H' * ARRAY a vl')`,
  CHEAT_TAC);;

let SEP_IMP_ARRAY_frame_single_l = prove
 (`!H' a vl vl'.
     (vl = vl') /\ (emp (SEP_IMP) H') ==>
     (ARRAY a vl (SEP_IMP) H' * ARRAY a vl')`,
  CHEAT_TAC);;

let SEP_IMP_ARRAY_frame_single_r = prove
 (`!H a vl vl'.
     (vl = vl') /\ (H (SEP_IMP) emp) ==>
     (H * ARRAY a vl (SEP_IMP) ARRAY a vl')`,
  CHEAT_TAC);;

let SEP_IMP_ARRAY_frame_single = prove
 (`!H a vl vl'.
     (vl = vl') /\ (emp (SEP_IMP) emp) ==>
     (ARRAY a vl (SEP_IMP) ARRAY a vl')`,
  CHEAT_TAC);;

let SEP_IMP_W8ARRAY_frame = prove
 (`!H H' a wl wl'.
     (wl = wl') /\ (H (SEP_IMP) H') ==>
     (H * W8ARRAY a wl (SEP_IMP) H' * W8ARRAY a wl')`,
  CHEAT_TAC);;

let SEP_IMP_W8ARRAY_frame_single_l = prove
 (`!H' a wl wl'.
     (wl = wl') /\ (emp (SEP_IMP) H') ==>
     (W8ARRAY a wl (SEP_IMP) H' * W8ARRAY a wl')`,
  CHEAT_TAC);;

let SEP_IMP_W8ARRAY_frame_single_r = prove
 (`!H a wl wl'.
     (wl = wl') /\ (H (SEP_IMP) emp) ==>
     (H * W8ARRAY a wl (SEP_IMP) W8ARRAY a wl')`,
  CHEAT_TAC);;

let SEP_IMP_W8ARRAY_frame_single = prove
 (`!H a wl wl'.
     (wl = wl') /\ (emp (SEP_IMP) emp) ==>
     (W8ARRAY a wl (SEP_IMP) W8ARRAY a wl')`,
  CHEAT_TAC);;

let SEP_IMP_IO_frame = prove
 (`!H H' idx st u st' u'.
     (st = st' /\ u = u') /\ (H (SEP_IMP) H') ==>
     (H * IO st u idx (SEP_IMP) H' * IO st' u' idx)`,
  CHEAT_TAC);;

let SEP_IMP_IO_frame_single_l = prove
 (`!H' idx st u st' u'.
     (st = st' /\ u = u') /\ (emp (SEP_IMP) H') ==>
     (IO st u idx (SEP_IMP) H' * IO st' u' idx)`,
  CHEAT_TAC);;

let SEP_IMP_IO_frame_single_r = prove
 (`!H idx st u st' u'.
     (st = st' /\ u = u') /\ (H (SEP_IMP) emp) ==>
     (H * IO st u idx (SEP_IMP) IO st' u' idx)`,
  CHEAT_TAC);;

let SEP_IMP_IO_frame_single = prove
 (`!idx st u st' u'.
     (st = st' /\ u = u') /\ (emp (SEP_IMP) emp) ==>
     (IO st u idx (SEP_IMP) IO st' u' idx)`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(** Normalization of STAR *)

(* HOL4 cfHeapsBaseScript.sml:558-561: ML code, not ported *)

(* HOL4 cfHeapsBaseScript.sml:563: ML code, not ported *)

(*------------------------------------------------------------------*)
(* Workaround because of SEP_CLAUSES turning &F into SEP_F *)

let SEP_F_to_cond = prove
 (`SEP_F = &F`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(** Properties of GC *)

let GC_STAR_GC = prove
 (`GC * GC = GC`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* Unfolding + case split lemma for SEP_IMPPOST *)

let SEP_IMPPOST_unfold = prove
 (`!Q1 Q2.
      (Q1 (SEP_IMPPOST) Q2) <=>
      (!v. Q1 (cfHeapsBase_Val v) (SEP_IMP) Q2 (cfHeapsBase_Val v)) /\
      (!v. Q1 (cfHeapsBase_Exn v) (SEP_IMP) Q2 (cfHeapsBase_Exn v)) /\
      (!name conf bytes. Q1 (cfHeapsBase_FFIDiv name conf bytes) (SEP_IMP)
        Q2 (cfHeapsBase_FFIDiv name conf bytes)) /\
      (!io. Q1 (cfHeapsBase_Div io) (SEP_IMP) Q2 (cfHeapsBase_Div io))`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(** Extraction from H1 in H1 ==>> H2 *)

let hpull_prop = prove
 (`!H H' P.
     (P ==> H (SEP_IMP) H') ==>
     (H * cond P (SEP_IMP) H')`,
  CHEAT_TAC);;

let hpull_prop_single = prove
 (`!H' P.
     (P ==> emp (SEP_IMP) H') ==>
     (cond P (SEP_IMP) H')`,
  CHEAT_TAC);;

let hpull_exists_single = prove
 (`!A H' J.
     (!x. (J x) (SEP_IMP) H') ==>
     (SEP_EXISTS J (SEP_IMP) H')`,
  CHEAT_TAC);;

let SEP_IMP_rew = prove
 (`!H1 H2 H1' H2'. (H1 = H2) ==> (H1' = H2') ==> (H1 (SEP_IMP) H1') = (H2
  (SEP_IMP) H2')`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(** Simplification in H2 on H1 ==>> H2 *)

(** Lemmas *)

let hsimpl_prop = prove
 (`!H' H P.
     P /\ (H' (SEP_IMP) H) ==>
     (H' (SEP_IMP) H * cond P)`,
  CHEAT_TAC);;

let hsimpl_prop_single = prove
 (`!H' P.
     P /\ (H' (SEP_IMP) emp) ==>
     (H' (SEP_IMP) cond P)`,
  CHEAT_TAC);;

let hsimpl_exists_single = prove
 (`!x H' J.
     (H' (SEP_IMP) J x) ==>
     (H' (SEP_IMP) SEP_EXISTS J)`,
  CHEAT_TAC);;

let hsimpl_gc = prove
 (`!H. H (SEP_IMP) GC`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* Automatic rewrites for post-condition injections *)

let POST_Val = prove
 (`!Qv Qe Qf Qd v. POST Qv Qe Qf Qd (cfHeapsBase_Val v) = Qv v`,
  CHEAT_TAC);;
add_simp POST_Val;;

let POST_Exn = prove
 (`!Qv Qe Qf Qd v. POST Qv Qe Qf Qd (cfHeapsBase_Exn v) = Qe v`,
  CHEAT_TAC);;
add_simp POST_Exn;;

let POST_FFIDiv = prove
 (`!Qv Qe Qf Qd name conf bytes. POST Qv Qe Qf Qd (cfHeapsBase_FFIDiv name
  conf bytes) = Qf name conf bytes`,
  CHEAT_TAC);;
add_simp POST_FFIDiv;;

let POST_Div = prove
 (`!Qv Qe Qf Qd io. POST Qv Qe Qf Qd (cfHeapsBase_Div io) = &(Qd io)`,
  CHEAT_TAC);;
add_simp POST_Div;;

let POSTv_Val = prove
 (`!Qv v. POSTv Qv (cfHeapsBase_Val v) = Qv v`,
  CHEAT_TAC);;
add_simp POSTv_Val;;

let POSTv_Exn = prove
 (`!Qv v. POSTv Qv (cfHeapsBase_Exn v) = &F`,
  CHEAT_TAC);;
add_simp POSTv_Exn;;

let POSTv_FFIDiv = prove
 (`!Qv name conf bytes. POSTv Qv (cfHeapsBase_FFIDiv name conf bytes) = &F`,
  CHEAT_TAC);;
add_simp POSTv_FFIDiv;;

let POSTv_Div = prove
 (`!Qv io. POSTv Qv (cfHeapsBase_Div io) = &F`,
  CHEAT_TAC);;
add_simp POSTv_Div;;

let POSTe_Val = prove
 (`!Qe v. POSTe Qe (cfHeapsBase_Val v) = &F`,
  CHEAT_TAC);;
add_simp POSTe_Val;;

let POSTe_Exn = prove
 (`!Qe v. POSTe Qe (cfHeapsBase_Exn v) = Qe v`,
  CHEAT_TAC);;
add_simp POSTe_Exn;;

let POSTe_FFIDiv = prove
 (`!Qe name conf bytes. POSTe Qe (cfHeapsBase_FFIDiv name conf bytes) = &F`,
  CHEAT_TAC);;
add_simp POSTe_FFIDiv;;

let POSTe_Div = prove
 (`!Qe io. POSTe Qe (cfHeapsBase_Div io) = &F`,
  CHEAT_TAC);;
add_simp POSTe_Div;;

let POSTf_Val = prove
 (`!Qf v. POSTf Qf (cfHeapsBase_Val v) = &F`,
  CHEAT_TAC);;
add_simp POSTf_Val;;

let POSTf_Exn = prove
 (`!Qf v. POSTf Qf (cfHeapsBase_Exn v) = &F`,
  CHEAT_TAC);;
add_simp POSTf_Exn;;

let POSTf_FFIDiv = prove
 (`!Qf name conf bytes. POSTf Qf (cfHeapsBase_FFIDiv name conf bytes) = Qf
  name conf bytes`,
  CHEAT_TAC);;
add_simp POSTf_FFIDiv;;

let POSTf_Div = prove
 (`!Qf io. POSTf Qf (cfHeapsBase_Div io) = &F`,
  CHEAT_TAC);;
add_simp POSTf_Div;;

let POSTd_Val = prove
 (`!Qd v. POSTd Qd (cfHeapsBase_Val v) = &F`,
  CHEAT_TAC);;
add_simp POSTd_Val;;

let POSTd_Exn = prove
 (`!Qd v. POSTd Qd (cfHeapsBase_Exn v) = &F`,
  CHEAT_TAC);;
add_simp POSTd_Exn;;

let POSTd_FFIDiv = prove
 (`!Qd name conf bytes. POSTd Qd (cfHeapsBase_FFIDiv name conf bytes) = &F`,
  CHEAT_TAC);;
add_simp POSTd_FFIDiv;;

let POSTd_Div = prove
 (`!Qd io. POSTd Qd (cfHeapsBase_Div io) = &(Qd io)`,
  CHEAT_TAC);;
add_simp POSTd_Div;;

let POSTve_Val = prove
 (`!Qv Qe v. POSTve Qv Qe (cfHeapsBase_Val v) = Qv v`,
  CHEAT_TAC);;
add_simp POSTve_Val;;

let POSTve_Exn = prove
 (`!Qv Qe v. POSTve Qv Qe (cfHeapsBase_Exn v) = Qe v`,
  CHEAT_TAC);;
add_simp POSTve_Exn;;

let POSTve_FFIDiv = prove
 (`!Qv Qe name conf bytes. POSTve Qv Qe (cfHeapsBase_FFIDiv name conf bytes)
  = &F`,
  CHEAT_TAC);;
add_simp POSTve_FFIDiv;;

let POSTve_Div = prove
 (`!Qv Qe io. POSTve Qv Qe (cfHeapsBase_Div io) = &F`,
  CHEAT_TAC);;
add_simp POSTve_Div;;

let POSTvd_Val = prove
 (`!Qv Qd v. POSTvd Qv Qd (cfHeapsBase_Val v) = Qv v`,
  CHEAT_TAC);;
add_simp POSTvd_Val;;

let POSTvd_Exn = prove
 (`!Qv Qd v. POSTvd Qv Qd (cfHeapsBase_Exn v) = &F`,
  CHEAT_TAC);;
add_simp POSTvd_Exn;;

let POSTvd_FFIDiv = prove
 (`!Qv Qd name conf bytes. POSTvd Qv Qd (cfHeapsBase_FFIDiv name conf bytes)
  = &F`,
  CHEAT_TAC);;
add_simp POSTvd_FFIDiv;;

let POSTvd_Div = prove
 (`!Qv Qd io. POSTvd Qv Qd (cfHeapsBase_Div io) = &(Qd io)`,
  CHEAT_TAC);;
add_simp POSTvd_Div;;

let POSTed_Val = prove
 (`!Qe Qd v. POSTed Qe Qd (cfHeapsBase_Val v) = &F`,
  CHEAT_TAC);;
add_simp POSTed_Val;;

let POSTed_Exn = prove
 (`!Qe Qd v. POSTed Qe Qd (cfHeapsBase_Exn v) = Qe v`,
  CHEAT_TAC);;
add_simp POSTed_Exn;;

let POSTed_FFIDiv = prove
 (`!Qe Qd name conf bytes. POSTed Qe Qd (cfHeapsBase_FFIDiv name conf bytes)
  = &F`,
  CHEAT_TAC);;
add_simp POSTed_FFIDiv;;

let POSTed_Div = prove
 (`!Qe Qd io. POSTed Qe Qd (cfHeapsBase_Div io) = &(Qd io)`,
  CHEAT_TAC);;
add_simp POSTed_Div;;

(* other lemmas about POSTv *)

let POSTv_ignore = prove
 (`(POSTv (\v. P)) r h <=> (?v. r = cfHeapsBase_Val v /\ P h)`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* Lemmas for ==v> / ==e> / ==f> / ==d> / =~v> / =~e> *)

let SEP_IMPPOSTv_POSTe_left = prove
 (`!Qe Q. POSTe Qe (SEP_IMPPOSTv) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTv_POSTf_left = prove
 (`!Qf Q. POSTf Qf (SEP_IMPPOSTv) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTv_POSTd_left = prove
 (`!Qd Q. POSTd Qd (SEP_IMPPOSTv) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTv_POSTed_left = prove
 (`!Qe Qd Q. POSTed Qe Qd (SEP_IMPPOSTv) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTe_POSTv_left = prove
 (`!Qv Q. POSTv Qv (SEP_IMPPOSTe) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTe_POSTf_left = prove
 (`!Qf Q. POSTf Qf (SEP_IMPPOSTe) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTe_POSTd_left = prove
 (`!Qd Q. POSTd Qd (SEP_IMPPOSTe) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTe_POSTvd_left = prove
 (`!Qv Qd Q. POSTvd Qv Qd (SEP_IMPPOSTe) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTf_POSTv_left = prove
 (`!Qv Q. POSTv Qv (SEP_IMPPOSTf) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTf_POSTe_left = prove
 (`!Qe Q. POSTe Qe (SEP_IMPPOSTf) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTf_POSTd_left = prove
 (`!Qd Q. POSTd Qd (SEP_IMPPOSTf) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTf_POSTve_left = prove
 (`!Qv Qe Q. POSTve Qv Qe (SEP_IMPPOSTf) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTf_POSTvd_left = prove
 (`!Qv Qd Q. POSTvd Qv Qd (SEP_IMPPOSTf) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTf_POSTed_left = prove
 (`!Qe Qd Q. POSTed Qe Qd (SEP_IMPPOSTf) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTd_POSTv_left = prove
 (`!Qv Q. POSTv Qv (SEP_IMPPOSTd) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTd_POSTe_left = prove
 (`!Qe Q. POSTe Qe (SEP_IMPPOSTd) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTd_POSTf_left = prove
 (`!Qf Q. POSTf Qf (SEP_IMPPOSTd) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTd_POSTve_left = prove
 (`!Qv Qe Q. POSTve Qv Qe (SEP_IMPPOSTd) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTv_inv_POSTv_left = prove
 (`!Qv Q. POSTv Qv (SEP_IMPPOSTv_inv) Q`,
  CHEAT_TAC);;

let SEP_IMPPOSTe_inv_POSTe_left = prove
 (`!Qe Q. POSTe Qe (SEP_IMPPOSTe_inv) Q`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
