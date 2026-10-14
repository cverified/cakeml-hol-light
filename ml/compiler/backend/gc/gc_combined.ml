(* ======================================================== *)
(*  gc_combined: ported from HOL4's
    compiler/backend/gc/gc_combinedScript.sml  *)
(* ======================================================== *)

(*
  One function that can run any of the GC algorithms.
*)

needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;

let gen_state_INDUCT,gen_state_RECURSION = define_datatype
  "gen_state = GenState (num) (num list)";;

let make_partial_conf_def = cake_define
  `make_partial_conf (conf:'a gen_gc_conf) (GenState _1 gen_starts) rs =
     mk_? (?_limit conf) (?_isRef conf) (HD gen_starts) rs`;;

let gc_combined_def = cake_define
  `gc_combined conf data_to_word_None (roots,heap,(gs:gen_state),_2,_3)
  =
     (roots,heap,0,0,gs,T) /\
   gc_combined conf data_to_word_Simple (roots,heap,gs,_4,_5) =
     (let (roots,heap,a,c) = full_gc (roots,heap,?_limit conf) in
        (roots,heap ++ heap_expand (?_limit conf - a),a,?_limit conf
          - a,gs,c)) /\
   gc_combined conf (data_to_word_Generational limits)
     (roots,heap,gs,rs,do_partial) =
     (if do_partial then
       (let partial_conf = make_partial_conf conf gs rs in
        let (roots,semanticPrimitives_state) = partial_gc
          partial_conf (roots,heap) in
          (roots,gc_state_old semanticPrimitives_state ++ gc_state_h1
            semanticPrimitives_state ++ heap_expand (gc_state_n
            semanticPrimitives_state) ++ gc_state_r1
            semanticPrimitives_state,gc_state_a
           semanticPrimitives_state,gc_state_n
             semanticPrimitives_state,GenState 0 (MAP (K (gc_state_a
             semanticPrimitives_state)) limits),gc_state_ok
             semanticPrimitives_state)) else
       (let (roots,semanticPrimitives_state) = gen_gc conf
         (roots,heap) in
          (roots,gc_state_h1 semanticPrimitives_state ++ heap_expand
            (gc_state_n semanticPrimitives_state) ++ gc_state_r1
            semanticPrimitives_state,gc_state_a
           semanticPrimitives_state,gc_state_n
             semanticPrimitives_state,GenState 0 (MAP (K (gc_state_a
             semanticPrimitives_state)) limits),gc_state_ok
             semanticPrimitives_state)))`;;
