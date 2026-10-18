(* ======================================================== *)
(*  word_elimProof: ported from HOL4's
    compiler/backend/proofs/word_elimProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_elim
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_elim.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;

(**************************** ANALYSIS LEMMAS
   *****************************)


(**************************** DEFINITIONS *****************************)

let dest_word_loc_def = cake_define
  `dest_word_loc x1 =
        match x1 with
          wordLang_Loc n _2 -> SOME n
        | (_3:'a word_loc) -> NONE`;;

let dest_result_loc_def = cake_define
  `dest_result_loc x1 =
        match x1 with
          SOME (wordSem_Result w ns) ->
       BIGUNION (set_of_list (MAP (\x. match (dest_word_loc x) with
         NONE -> {} | SOME x -> {x}) ns))
        | (SOME (wordSem_Exception w (wordLang_Loc n n0))) -> {n}
        | _4 -> {}`;;

(* TODO could do alt def using toAList -
    not necessary though, may not be cleaner *)
let get_locals_def = cake_define_list
  [`get_locals (LN:('a word_loc) spt) = LN`;
   `get_locals (LS a) = (match (dest_word_loc a) with SOME n ->
  sptree_insert n one LN | NONE -> LN)`;
   `get_locals (BN t1 t2) = sptree_union (get_locals t1) (get_locals
  t2)`;
   `get_locals (BS t1 a t2) =
            (let t = (sptree_union (get_locals t1) (get_locals t2))
              in
                match (dest_word_loc a) with SOME n ->
                  sptree_insert n one t | NONE -> t)`];;

(*TODO fix conflict with get_store in WordSem*)
let get_store_def = cake_define
  `word_elimProof_get_store (st:(store_name,'a word_loc)fmap) =
       (let locSet = SET_TO_LIST (FRANGE st) in
       let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc
         locSet)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locList)`;;
hol4_overload "get_store" "word_elimProof_get_store";;

let get_num_wordloc_alist_def = cake_define
  `get_num_wordloc_alist (l:(num#'a word_loc) list) =
       (let locs = MAP THE (FILTER IS_SOME (MAP (dest_word_loc o SND)
         l)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locs)`;;

let get_stack_def = cake_define_list
  [`word_elimProof_get_stack [] = (LN:1 spt)`;
   `word_elimProof_get_stack (StackFrame lsz e0 e _5 :: xs) =
            ((sptree_union (sptree_union (get_num_wordloc_alist
              e0) (get_num_wordloc_alist e))
              (word_elimProof_get_stack xs)):1 spt)`];;
hol4_overload "get_stack" "word_elimProof_get_stack";;

(* HOL4 word_elimProofScript.sml:210: ML code, not ported *)

let get_memory_def = cake_define
  `get_memory (mem':'a word->'a word_loc) (mdom:'a word->bool) =
       (let locSet = SET_TO_LIST (IMAGE mem' mdom) in
       let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc
         locSet)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locList)`;;

let find_loc_state_def = cake_define
  `find_loc_state s =
       (let loc = (get_locals (wordSem_state_locals s)) in
       let sto = (get_store (wordSem_state_store s)) in
       let sta = (get_stack (stack s)) in
       let mem' = (get_memory (wordSem_state_memory s)
         (wordSem_state_mdomain s)) in
       sptree_union (sptree_union loc sto) (sptree_union sta
         mem'))`;;

let code_rel_def = cake_define
  `word_elimProof_code_rel (reachable:1 spt) s_code (t_code:(num#'a
  wordLang_prog) spt) =
       (!n. n IN domain reachable ==>
           sptree_lookup n s_code = sptree_lookup n t_code)`;;
hol4_overload "code_rel" "word_elimProof_code_rel";;

let code_closed_def = cake_define
  `code_closed reachable c1 <=> (?code1. c1 = fromAList code1 /\
       (!n m. n IN domain reachable /\
       is_reachable (analyse_word_code code1) n m ==>
       m IN domain reachable))`;;

let gc_no_new_locs_def = cake_define
  `gc_no_new_locs (g:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) <=> (!sta
  mem' mdom sto wl mem1 sto1 sta1.
       (g (wordSem_enc_stack sta,mem',mdom,sto) = SOME
         (wl,mem1,sto1)) /\
        wordSem_dec_stack wl sta = SOME sta1 ==>
       domain (get_stack sta1) SUBSET domain (get_stack sta) /\
       domain (get_memory mem1 mdom) SUBSET domain (get_memory mem'
         mdom) /\
       domain (get_store sto1) SUBSET domain (get_store sto))`;;

let word_state_rel_def = cake_define
  `word_state_rel (reachable:1 spt) t s <=> wordSem_state_locals
       s = wordSem_state_locals t /\ wordSem_state_fp_regs
       s = wordSem_state_fp_regs t /\ wordSem_state_store
       s = wordSem_state_store t /\ stack
       s = stack t /\ wordSem_state_memory
       s = wordSem_state_memory t /\ wordSem_state_mdomain
       s = wordSem_state_mdomain t /\ wordSem_state_sh_mdomain
       s = wordSem_state_sh_mdomain t /\ wordSem_state_permute
       s = wordSem_state_permute t /\ wordSem_state_compile
       s = wordSem_state_compile t /\ wordSem_state_compile_oracle
       s = wordSem_state_compile_oracle t /\
         wordSem_state_code_buffer
       s = wordSem_state_code_buffer t /\ wordSem_state_data_buffer
       s = wordSem_state_data_buffer t /\ wordSem_state_gc_fun
       s = wordSem_state_gc_fun t /\ wordSem_state_handler
       s = wordSem_state_handler t /\ state_clock
       s = state_clock t /\ wordSem_state_termdep
       s = wordSem_state_termdep t /\ wordSem_state_be
       s = wordSem_state_be t /\ state_ffi
       s = state_ffi t /\ wordSem_state_locals_size
       s = wordSem_state_locals_size t /\ wordSem_state_stack_max
       s = wordSem_state_stack_max t /\ wordSem_state_stack_limit
       s = wordSem_state_stack_limit t /\ wordSem_state_stack_size
       s = wordSem_state_stack_size t /\
       word_elimProof_code_rel reachable (wordSem_state_code s)
         (wordSem_state_code t) /\
       domain (find_loc_state t) SUBSET domain (reachable)`;;


(**************************** OTHER LEMMAS
   *****************************)

(**************************** WORD STATE REL
   ***************************)

(*TODO maybe depreciate?*)

(*TODO add assum to prove it*)

(*This can be strengthened to an equality*)
(*TODO move*)

(**************************** MAIN LEMMAS *****************************)

(* HOL4 word_elimProofScript.sml:989-992: a proof *)

(* HOL4 word_elimProofScript.sml:994-996: a proof *)

(* HOL4 word_elimProofScript.sml:998-1006: a proof *)

(* HOL4 word_elimProofScript.sml:1008-1014: a proof *)

(* HOL4 word_elimProofScript.sml:1016-1023: a proof *)

(* HOL4 word_elimProofScript.sml:1025-1035: a proof *)

(* HOL4 word_elimProofScript.sml:1037-1044: a proof *)

(* HOL4 word_elimProofScript.sml:1046-1052: a proof *)

(* HOL4 word_elimProofScript.sml:1054-1065: a proof *)

(* HOL4 word_elimProofScript.sml:1067-1079: a proof *)

(* HOL4 word_elimProofScript.sml:1081-1093: a proof *)

(* HOL4 word_elimProofScript.sml:1095-1108: a proof *)

(* HOL4 word_elimProofScript.sml:1110-1132: a proof *)

(* HOL4 word_elimProofScript.sml:1134-1159: a proof *)

(* HOL4 word_elimProofScript.sml:1161-1176: a proof *)

(* HOL4 word_elimProofScript.sml:1178-1186: a proof *)

(* HOL4 word_elimProofScript.sml:1188-1203: a proof *)

(* HOL4 word_elimProofScript.sml:1205-1217: a proof *)

(* HOL4 word_elimProofScript.sml:1219-1232: a proof *)

(* HOL4 word_elimProofScript.sml:1234-1254: a proof *)

(* HOL4 word_elimProofScript.sml:1256-1274: a proof *)

(* HOL4 word_elimProofScript.sml:1276-1295: a proof *)

(* HOL4 word_elimProofScript.sml:1297-1542: a proof *)

(* HOL4 word_elimProofScript.sml:1544-1599: a proof *)

(* HOL4 word_elimProofScript.sml:1601: a proof *)

(**************************** WORD_REMOVAL_THM
   *****************************)
