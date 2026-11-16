(* ======================================================== *)
(*  basis_ffi: ported from HOL4's
    basis/basis_ffiScript.sml
    A definition theory, with 12 definitions and 36 theorems.
    Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  Instantiate the CakeML FFI oracle for the oracle of the basis library.
*)

needs "basis/CommandLineProof.ml";;
needs "basis/RuntimeProof.ml";;
needs "basis/TextIOProg.ml";;
needs "basis/TextIOProof.ml";;
needs "basis/clFFI.ml";;
needs "basis/fsFFI.ml";;
needs "basis/fsFFIProps.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/runtimeFFI.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/location.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "translator/evaluate_dec.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "basis_ffi"
  ["CommandLineProof"; "RuntimeProof"; "TextIOProg"; "TextIOProof"; "cf";
   "clFFI"; "fsFFI"; "fsFFIProps"; "ml_prog"; "ml_translator"; "runtimeFFI"];;

let _ = do_list hide_constant ["C"; "fv"; "prog"];;

(*---------------------------------------------------------------------------*)
(* GENERALISED FFI *)

(* The oracle handles the FFI names of the basis library itself and passes
   every other name on to its parameter ext, so that a program may be given a
   meaning in an environment providing further FFIs. *)
let basis_ffi_oracle_def = new_definition
  `basis_ffi_oracle ext =
     (\CommandLineProof_name (cls,fs) conf bytes.
      if CommandLineProof_name = ffi_ExtCall (implode "write") then
        match ffi_write conf bytes fs with SOME (FFIreturn bytes fs) ->
          Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "read") then
        match ffi_read conf bytes fs with SOME (FFIreturn bytes fs) ->
          Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "get_arg_count") then
        match ffi_get_arg_count conf bytes cls with SOME (FFIreturn bytes
          cls) -> Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "get_arg_length") then
        match ffi_get_arg_length conf bytes cls with SOME (FFIreturn bytes
          cls) -> Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "get_arg") then
        match ffi_get_arg conf bytes cls with SOME (FFIreturn bytes cls) ->
          Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "open_in") then
        match ffi_open_in conf bytes fs with SOME (FFIreturn bytes fs) ->
          Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "open_out") then
        match ffi_open_out conf bytes fs with SOME (FFIreturn bytes fs) ->
          Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "close") then
        match ffi_close conf bytes fs with SOME (FFIreturn bytes fs) ->
          Oracle_return (cls,fs) bytes
        | _ -> Oracle_final FFI_failed else if CommandLineProof_name =
          ffi_ExtCall (implode "exit") then
        match ffi_exit conf bytes one with SOME (FFIreturn bytes one) ->
          Oracle_return (cls,fs) bytes
        | SOME (FFIdiverge) -> Oracle_final FFI_diverged
        | NONE -> Oracle_final FFI_failed else ext CommandLineProof_name
          (cls,fs) conf bytes)`;;

(* the FFI names that basis_ffi_oracle answers itself *)
let is_basis_ffi_name_def = new_definition
  `is_basis_ffi_name CommandLineProof_name <=>
     CommandLineProof_name IN {(implode "write"),(implode "read"),(implode
       "get_arg_count"),(implode "get_arg_length"),(implode "get_arg"),
             (implode "open_in"),(implode "open_out"),(implode
               "close"),(implode "exit")}`;;

let basis_ffi_oracle_ext = prove
 (`~(is_basis_ffi_name nm) ==>
   basis_ffi_oracle ext (ffi_ExtCall nm) st conf bs = ext (ffi_ExtCall nm)
     st conf bs`,
  CHEAT_TAC);;

let basis_ffi_oracle_SharedMem = prove
 (`basis_ffi_oracle ext (ffi_SharedMem sop) st conf bs = ext (ffi_SharedMem
  sop) st conf bs`,
  CHEAT_TAC);;

(* on a basis FFI name the oracle does not consult ext at all *)
let basis_ffi_oracle_is_basis_ffi_name = prove
 (`is_basis_ffi_name nm ==>
   basis_ffi_oracle ext (ffi_ExtCall nm) st conf bs =
   basis_ffi_oracle ext' (ffi_ExtCall nm) st conf bs`,
  CHEAT_TAC);;

(* standard streams are initialized *)
let basis_ffi_def = new_definition
  `basis_ffi ext cl fs =
     mk_ffi_state (basis_ffi_oracle ext) (cl,fs) []`;;

(* the fall-through oracle answering no call at all: the basis FFIs and
   nothing else *)
let no_ext_def = new_definition
  `no_ext = (\(CommandLineProof_name:ffiname) (st:mlstring list#IO_fs)
  (conf:word8 list)
              (bytes:word8 list). Oracle_final FFI_failed)`;;

let basis_proj1_def = new_definition
  `basis_proj1 = (\(cls,fs).
     FEMPTY |++ (
                 APPEND (APPEND (mk_proj1 cl_ffi_part cls) (mk_proj1
                   fs_ffi_part fs)) (mk_proj1 runtime_ffi_part one)))`;;

let basis_proj2_def = new_definition
  `basis_proj2 =
     [mk_proj2 cl_ffi_part;
      mk_proj2 fs_ffi_part;
      mk_proj2 runtime_ffi_part]`;;

let basis_proj1_write = prove
 (`FAPPLY
      (basis_proj1 ffi) (implode "write") = runtimeFFI_encode (SND ffi)`,
  CHEAT_TAC);;

(* builds the file system from a list of events *)

(* The state replayed is the whole oracle state (cls,fs): an event handled by
   ext is replayed by ext, which may change either component. *)
(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o SND o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 basis_ffiScript.sml:160-162: the tactic that proves the termination *)
let extract_fs_with_numchars_def,extract_fs_with_numchars_ind = define_guess
  `(extract_fs_with_numchars ext (st:mlstring list#IO_fs) [] = SOME st) /\
   (extract_fs_with_numchars ext (st:mlstring list#IO_fs) (CONS (IO_event
    (ffi_ExtCall CommandLineProof_name) conf bytes) xs) =
        match (ALOOKUP (SND (SND fs_ffi_part)) CommandLineProof_name) with
            SOME ffi_fun -> (match ffi_fun conf (MAP FST bytes) (SND st) with
            SOME (FFIreturn bytes' fs') ->
                             if bytes' = MAP SND bytes then
                              extract_fs_with_numchars ext (FST st,fs') xs
                             else NONE
                           | _ -> NONE)
        | NONE ->
          (if is_basis_ffi_name CommandLineProof_name then
            extract_fs_with_numchars ext st xs
          else (match ext (ffi_ExtCall CommandLineProof_name) st conf (MAP
              FST bytes) with Oracle_return st' bytes' ->
               if bytes' = MAP SND bytes then
                 extract_fs_with_numchars ext st' xs
               else NONE
             | Oracle_final _ -> NONE))) /\
   (extract_fs_with_numchars ext (st:mlstring list#IO_fs) (CONS (IO_event
    (ffi_SharedMem op) conf bytes) xs) =
         match ext (ffi_SharedMem op) st conf (MAP FST bytes) with
             Oracle_return st' bytes' ->
           if bytes' = MAP SND bytes then
             extract_fs_with_numchars ext st' xs
           else NONE
         | Oracle_final _ -> NONE)`;;

let extract_fs_with_numchars_APPEND = prove
 (`!xs ys ext st. extract_fs_with_numchars ext st (APPEND xs ys) =
    match extract_fs_with_numchars ext st xs with NONE -> NONE
    | SOME st' -> extract_fs_with_numchars ext st' ys`,
  CHEAT_TAC);;

let extract_fs_def = new_definition
  `extract_fs ext st events =
     OPTION_MAP (numchars_fupd (K (IO_fs_numchars (SND st))) o SND)
     (extract_fs_with_numchars ext st events)`;;

(* The two theorems below track how the file system grows along an event trace.
   They are stated for no_ext, the fall-through oracle that answers nothing, so
   the ext branches of the extraction are impossible and drop out.

   They can be generalised to admit a wider class of ext should a caller need it.
   What the proofs actually require is that ext leaves the UStream part of infds
   and inode_tbl alone -- File inodes are irrelevant here -- so the generalised
   form would take such a side condition as an antecedent, and the ext branches
   would transfer that property through the induction instead of being discharged
   as impossible. *)

let extract_fs_with_numchars_keeps_iostreams = prove
 (`!ls cls fs cls' fs' off.
   (extract_fs_with_numchars no_ext (cls,fs) ls = SOME (cls',fs')) /\
   (ALOOKUP (IO_fs_infds fs') fd = SOME (UStream nm,md,off)) ==>
   (?off'.
     (ALOOKUP (IO_fs_infds fs) fd = SOME (UStream nm,md,off')) /\ off' <=
       off /\
     (!content.
       (ALOOKUP (IO_fs_inode_tbl fs) (UStream nm) = SOME content) /\ (off' =
         LENGTH content) /\
       (!fd' md' off'. (ALOOKUP (IO_fs_infds fs) fd' = SOME (UStream
         nm,md',off')) ==> (fd = fd')) ==>
       (?written.
         (ALOOKUP (IO_fs_inode_tbl fs') (UStream nm) = SOME (APPEND content
           written)) /\
         (off = off' + LENGTH written))))`,
  CHEAT_TAC);;

let extract_fs_with_numchars_closes_iostreams = prove
 (`!ls cls fs cls' fs' fd' nm off.
   (extract_fs_with_numchars no_ext (cls,fs) ls = SOME (cls',fs')) /\
   (!fd' off. ~(ALOOKUP (IO_fs_infds fs) fd' = SOME (UStream nm,md,off)))
     ==>
   (~(ALOOKUP (IO_fs_infds fs') fd' = SOME (UStream nm,md,off)))`,
  CHEAT_TAC);;

(* HOL4 basis_ffiScript.sml:294-421: code that the source has in a comment *)

(*-------------------------------------------------------------------------------------------------*)

(*These theorems are need to be remade to use cfMain for projs, oracle or ffi that aren't basis_ffi*)

(* TODO: remove? *)

(* HOL4 basis_ffiScript.sml:429-437: code that the source has in a comment *)

(*RTC_call_FFI_rel_IMP_basis_events show that extracting output from two ffi_states will use the
  same function if the two states are related by a series of FFI_calls. If this is the case for
  your oracle (and projs), then this proof should be relatively similar. Note
  that to make the subsequent proofs similar one should show an equivalence between
  extract_output and proj1  *)
let RTC_call_FFI_rel_IMP_basis_events = prove
 (`!st0 ext st st'. RTC call_FFI_rel st st' ==> ffi_state_oracle st =
  basis_ffi_oracle ext ==>
   (extract_fs_with_numchars ext st0 (ffi_state_io_events st) = SOME
     (ffi_state_ffi_state st) ==>
   extract_fs_with_numchars ext st0 (ffi_state_io_events st') = SOME
     (ffi_state_ffi_state st'))`,
  CHEAT_TAC);;

(* the first condition for the previous theorem holds for the
  init_state ffi  *)
let extract_fs_basis_ffi = prove
 (`extract_fs_with_numchars ext (ffi_state_ffi_state (basis_ffi ext cls fs))
  (ffi_state_io_events
     (basis_ffi ext cls fs)) = SOME (ffi_state_ffi_state (basis_ffi ext
       cls fs))`,
  CHEAT_TAC);;

let append_hprop = prove
 (`A s1 /\ B s2 ==> DISJOINT s1 s2 ==> (A * B) (s1 UNION s2)`,
  CHEAT_TAC);;

(* HOL4 basis_ffiScript.sml:490-492: ML code, not ported *)

(* HOL4 basis_ffiScript.sml:494-504: a theorem that HOL4 states as the value
   of an ML expression: IOFS_precond *)

(* HOL4 basis_ffiScript.sml:506-517: a theorem that HOL4 states as the value
   of an ML expression: STDIO_precond *)

let RUNTIME_precond = prove
 (`RUNTIME {cfHeapsBase_FFI_part (runtimeFFI_encode one) (mk_ffi_next
  runtime_ffi_part)
           (MAP FST (SND (SND runtime_ffi_part))) events}`,
  CHEAT_TAC);;

(*call_main_thm_basis uses call_main_thm2 to get semantics_dec_list, and then uses the previous two
  theorems to prove the outcome of extract_output. If RTC_call_FFI_rel_IMP* uses proj1, after
  showing that post-condition which gives effects your programs output is an FFI_part and
  assuming that parts_ok is satisfied, an assumption about proj1 and the ffi_state should be
  derived which should fit the function on some st.ffi_state which returns extract_output on
  st.io_events  *)

(* HOL4 basis_ffiScript.sml:534-537: the ML values that the definitions
   below antiquote *)

(* PORT FAILED: Definition whole_prog_spec_def: expected ')' but found '.'
   at 194 *)
(* HOL4 basis_ffiScript.sml:539-546: the definition *)

(* PORT FAILED: Definition whole_prog_ffidiv_spec_def: expected ')' but
   found '.' at 172 *)
(* HOL4 basis_ffiScript.sml:548-555: the definition *)

(* PORT FAILED: Definition whole_prog_spec2_def: expected ')' but found '.'
   at 185 *)
(* HOL4 basis_ffiScript.sml:557-565: the definition *)

(* HOL4 basis_ffiScript.sml:567-618: a theorem whose statement the port
   cannot state yet: whole_prog_spec2_semantics_prog *)

(* HOL4 basis_ffiScript.sml:620-646: a theorem whose statement the port
   cannot state yet: whole_prog_spec_semantics_prog *)

(* HOL4 basis_ffiScript.sml:648-697: a theorem whose statement the port
   cannot state yet: whole_prog_spec_semantics_prog_ffidiv *)

(* HOL4 basis_ffiScript.sml:699-704: a theorem that HOL4 states as the value
   of an ML expression: basis_ffi_length_thms *)

let basis_ffi_part_defs =
  end_itlist CONJ [fs_ffi_part_def; cl_ffi_part_def; runtime_ffi_part_def];;

(* This is used to show to show one of the parts of parts_ok for the state after a spec *)
let oracle_parts = prove
 (`!st.
     ffi_state_oracle (semanticPrimitives_state_ffi
     st) = basis_ffi_oracle ext /\
     MEM (ns,u) basis_proj2 /\
     MEM m ns /\
     u m conf bytes (FAPPLY (basis_proj1 x) m) = SOME (FFIreturn new_bytes
       w) ==>
     (?y. ffi_state_oracle (semanticPrimitives_state_ffi st) (ffi_ExtCall m)
       x conf bytes = Oracle_return y new_bytes /\
          basis_proj1 x |++ MAP (\n. (n,w)) ns = basis_proj1 y)`,
  CHEAT_TAC);;

(* TODO: move to fsFFI? *)
let fs_ffi_no_ffi_div = prove
 (`(ffi_open_in conf bytes fs = SOME FFIdiverge ==> F) /\
   (ffi_open_out conf bytes fs = SOME FFIdiverge ==> F) /\
   (ffi_read conf bytes fs = SOME FFIdiverge ==> F) /\
   (ffi_close conf bytes fs = SOME FFIdiverge ==> F) /\
   (ffi_write conf bytes fs = SOME FFIdiverge ==> F)`,
  CHEAT_TAC);;

(* TODO: move to clFFI? *)
let cl_ffi_no_ffi_div = prove
 (`(ffi_get_arg_count conf bytes cls = SOME FFIdiverge ==> F) /\
   (ffi_get_arg_length conf bytes cls = SOME FFIdiverge ==> F) /\
   (ffi_get_arg conf bytes cls = SOME FFIdiverge ==> F)`,
  CHEAT_TAC);;

let oracle_parts_div = prove
 (`!st.
     ffi_state_oracle (semanticPrimitives_state_ffi
     st) = basis_ffi_oracle ext /\ MEM (ns,u) basis_proj2 /\
     MEM m ns /\
     u m conf bytes (FAPPLY (basis_proj1 x) m) = SOME FFIdiverge ==>
       ffi_state_oracle (semanticPrimitives_state_ffi
     st) (ffi_ExtCall m) x conf bytes = Oracle_final FFI_diverged`,
  CHEAT_TAC);;

(* HOL4 basis_ffiScript.sml:784-787: the ML values that the definitions
   below antiquote *)

let parts_ok_basis_st = prove
 (`parts_ok (semanticPrimitives_state_ffi ((basis_ffi ext cls fs)))
  (basis_proj1,basis_proj2)`,
  CHEAT_TAC);;

(* TODO: move somewhere else? *)
let SPLIT_exists = prove
 (`(A * B) s /\ s SUBSET C ==> (?h1 h2. SPLIT C (h1,h2) /\ (A * B) h1)`,
  CHEAT_TAC);;

let same_eval_state = prove
 (`(semanticPrimitives_state_eval_state_fupd (K
  (semanticPrimitives_state_eval_state s)) s) = s`,
  CHEAT_TAC);;

let iobuff_loc_eq = prove
 (`iobuff_loc = semanticPrimitives_Loc T 1`,
  CHEAT_TAC);;

let is_refs_basis_def = new_definition
  `is_refs_basis refs =
     (?bs1 bs2 rest.
        refs = CONS (semanticPrimitives_W8array bs1) (CONS
          (semanticPrimitives_W8array bs2) rest) /\
        2052 <= LENGTH bs2)`;;

(* [local] *)
let SPLIT_eq_SUBSET = prove
 (`(?h_i. h_i SUBSET s /\ P h_i) ==>
   (?h_i h_k. SPLIT s (h_i,h_k) /\ P h_i)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_STDIO_general = prove
 (`semanticPrimitives_state_ffi
   res_st = basis_ffi ext cl fs /\ wfcl cl /\ wfFS fs /\ STD_streams fs /\
   is_refs_basis (semanticPrimitives_state_refs res_st) /\
   (?other. p other /\ other SUBSET store2heap_aux 2 (TL (TL
     (semanticPrimitives_state_refs res_st)))) ==>
   (?h_i h_k.
     SPLIT (st2heap (basis_proj1,basis_proj2) res_st) (h_i,h_k) /\
     (COMMANDLINE cl * STDIO fs * p) h_i)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_STDIO = prove
 (`semanticPrimitives_state_ffi
     res_st = basis_ffi ext cl fs /\ wfcl cl /\ wfFS fs /\ STD_streams fs /\
     is_refs_basis (semanticPrimitives_state_refs res_st) ==>
     (?h_i h_k.
       SPLIT (st2heap (basis_proj1,basis_proj2) res_st) (h_i,h_k) /\
       (COMMANDLINE cl * STDIO fs * &T) h_i)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_STDIO_RUNTIME = prove
 (`semanticPrimitives_state_ffi
   res_st = basis_ffi ext cl fs /\ wfcl cl /\ wfFS fs /\ STD_streams fs /\
   is_refs_basis (semanticPrimitives_state_refs res_st) ==>
   (?h_i h_k.
     SPLIT (st2heap (basis_proj1,basis_proj2) res_st) (h_i,h_k) /\
     (COMMANDLINE cl * STDIO fs * RUNTIME) h_i)`,
  CHEAT_TAC);;

let whole_prog_spec_IMP' = prove
 (`whole_prog_spec main_v cl fs NONE basis_ffi_post /\
   Decls init_env (semanticPrimitives_state_eval_state_fupd (K es)
     (ml_prog_init_state (basis_ffi ext cl fs))) decs res_env res_st ==>
   (!main_name.
     let all_decs = SNOC (Dlet unknown_loc (ast_Pcon NONE [])
                      (ast_App ast_Opapp [ast_Var (Short main_name); ast_Con
                        NONE []])) decs in
     nsLookup (sem_env_v res_env) (Short main_name) = SOME main_v ==>
     semanticPrimitives_state_ffi
     res_st = basis_ffi ext cl fs ==>
     is_refs_basis (semanticPrimitives_state_refs res_st) ==>
     wfcl cl /\ wfFS fs /\ STD_streams fs ==>
     (?io_events result.
       semantics_dec_list
         (semanticPrimitives_state_eval_state_fupd (K es)
           (ml_prog_init_state (basis_ffi ext cl fs))) init_env
         all_decs
         (ffi_Terminate ffi_Success io_events) /\
       extract_fs ext (cl,fs) io_events = SOME result /\
       basis_ffi_post result))`,
  CHEAT_TAC);;

let whole_prog_spec_IMP = prove
 (`whole_prog_spec main_v cl fs NONE basis_ffi_post /\
   Decls init_env (ml_prog_init_state (basis_ffi ext cl fs)) decs res_env
     res_st ==>
   (!main_name.
     let all_decs = SNOC (Dlet unknown_loc (ast_Pcon NONE [])
                      (ast_App ast_Opapp [ast_Var (Short main_name); ast_Con
                        NONE []])) decs in
     nsLookup (sem_env_v res_env) (Short main_name) = SOME main_v ==>
     semanticPrimitives_state_ffi
     res_st = basis_ffi ext cl fs ==>
     is_refs_basis (semanticPrimitives_state_refs res_st) ==>
     wfcl cl /\ wfFS fs /\ STD_streams fs ==>
     (?io_events result.
       semantics_dec_list
         (ml_prog_init_state (basis_ffi ext cl fs)) init_env
         all_decs
         (ffi_Terminate ffi_Success io_events) /\
       extract_fs ext (cl,fs) io_events = SOME result /\
       basis_ffi_post result))`,
  CHEAT_TAC);;

let whole_prog_spec_SOME_IMP = prove
 (`whole_prog_spec main_v cl fs (SOME p) basis_ffi_post /\
   Decls init_env (ml_prog_init_state (basis_ffi ext cl fs)) decs res_env
     res_st ==>
   (!main_name.
     let all_decs = SNOC (Dlet unknown_loc (ast_Pcon NONE [])
                      (ast_App ast_Opapp [ast_Var (Short main_name); ast_Con
                        NONE []])) decs in
     nsLookup (sem_env_v res_env) (Short main_name) = SOME main_v ==>
     semanticPrimitives_state_ffi
     res_st = basis_ffi ext cl fs ==>
     is_refs_basis (semanticPrimitives_state_refs res_st) ==>
     wfcl cl /\ wfFS fs /\ STD_streams fs /\
     (?other. p other /\ other SUBSET store2heap_aux 2 (TL (TL
       (semanticPrimitives_state_refs res_st)))) ==>
     (?io_events result.
       semantics_dec_list
         (ml_prog_init_state (basis_ffi ext cl fs)) init_env
         all_decs
         (ffi_Terminate ffi_Success io_events) /\
       extract_fs ext (cl,fs) io_events = SOME result /\
       basis_ffi_post result))`,
  CHEAT_TAC);;

let whole_prog_spec2_IMP = prove
 (`whole_prog_spec2 main_v cl fs NONE basis_ffi_post /\
   Decls init_env (ml_prog_init_state (basis_ffi ext cl fs)) decs res_env
     res_st ==>
   (!main_name.
     let all_decs = SNOC (Dlet unknown_loc (ast_Pcon NONE [])
                      (ast_App ast_Opapp [ast_Var (Short main_name); ast_Con
                        NONE []])) decs in
     nsLookup (sem_env_v res_env) (Short main_name) = SOME main_v ==>
     semanticPrimitives_state_ffi
     res_st = basis_ffi ext cl fs ==>
     is_refs_basis (semanticPrimitives_state_refs res_st) ==>
     wfcl cl /\ wfFS fs /\ STD_streams fs ==>
     (?io_events result.
       semantics_dec_list
         (ml_prog_init_state (basis_ffi ext cl fs)) init_env
         all_decs
         (ffi_Terminate ffi_Success io_events) /\
       extract_fs ext (cl,fs) io_events = SOME result /\
       basis_ffi_post result))`,
  CHEAT_TAC);;

let whole_prog_spec_ffidiv_IMP = prove
 (`whole_prog_ffidiv_spec main_v cl fs Q /\
   Decls init_env (ml_prog_init_state (basis_ffi ext cl fs)) decs res_env
     res_st ==>
   (!main_name.
     let all_decs = SNOC (Dlet unknown_loc (ast_Pcon NONE [])
                      (ast_App ast_Opapp [ast_Var (Short main_name); ast_Con
                        NONE []])) decs in
     nsLookup (sem_env_v res_env) (Short main_name) = SOME main_v ==>
     semanticPrimitives_state_ffi
     res_st = basis_ffi ext cl fs ==>
     is_refs_basis (semanticPrimitives_state_refs res_st) ==>
     wfcl cl /\ wfFS fs /\ STD_streams fs ==>
     (?io_events fs' n c b.
       semantics_dec_list
         (ml_prog_init_state (basis_ffi ext cl fs)) init_env
         all_decs
         (ffi_Terminate
            (ffi_FFI_outcome (Final_event (ffi_ExtCall n) c b FFI_diverged))
            io_events) /\
       extract_fs ext (cl,fs) io_events = SOME fs' /\ Q n c b fs'))`,
  CHEAT_TAC);;

(* HOL4 basis_ffiScript.sml:1212: the ML values that the definitions below
   antiquote *)
(* HOL4 basis_ffiScript.sml:1213-1217: a theorem that HOL4 states as the
   value of an ML expression: basis_refs_eqs *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "fv";
   "prog"];;

(* and the interface *)
let _ = unhide_overloads ();;
