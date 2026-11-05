(* ======================================================== *)
(*  gc_combined: ported from HOL4's
    compiler/backend/gc/gc_combinedScript.sml
    A definition theory, with 2 definitions, 1 datatype and no
    theorems.  Needed by data_to_word_gcProof.ml and
    data_to_word_memoryProof.ml.  *)
(* ======================================================== *)

(*
  One function that can run any of the GC algorithms.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "gc_combined"
  ["copying_gc"; "data_to_word"; "gc_shared"; "gen_gc";
   "gen_gc_partial"];;

let gen_state_INDUCT,gen_state_RECURSION = define_datatype
  "gen_state = GenState (num) (num list)";;

let make_partial_conf_def = cake_define
  `make_partial_conf (conf:'a gen_gc_conf) (GenState _1 gen_starts) rs =
     mk_gen_gc_partial_conf (gen_gc_conf_limit conf)
       (gen_gc_conf_isRef conf) (HD gen_starts) rs`;;

let gc_combined_def = cake_define
  `gc_combined conf x2 x3 =
      match (x2,x3) with
        ((None:gc_kind),(roots,heap,(gs:gen_state),_2,_3)) ->
     (roots,heap,0,0,gs,T)
      | (Simple,(roots,heap,gs,_4,_5)) ->
     (let (roots,heap,a,c) = full_gc (roots,heap,limit conf) in
        (roots,heap ++ heap_expand (limit conf - a),a,limit conf -
          a,gs,c))
      | ((data_to_word_Generational
        limits),(roots,heap,gs,rs,do_partial')) ->
     (if do_partial' then
       (let partial_conf = make_partial_conf conf gs rs in
        let (roots,state) = partial_gc partial_conf (roots,heap) in
          (roots,gc_state_old state ++ gc_state_h1 state ++
            heap_expand (gc_state_n state) ++ gc_state_r1
            state,gc_state_a
           state,gc_state_n state,GenState 0 (MAP (K (gc_state_a
             state)) limits),gc_state_ok state)) else
       (let (roots,state) = gen_gc conf (roots,heap) in
          (roots,gc_state_h1 state ++ heap_expand (gc_state_n state)
            ++ gc_state_r1 state,gc_state_a
           state,gc_state_n state,GenState 0 (MAP (K (gc_state_a
             state)) limits),gc_state_ok state)))`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
