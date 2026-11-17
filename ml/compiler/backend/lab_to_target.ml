(* ======================================================== *)
(*  lab_to_target: ported from HOL4's
    compiler/backend/lab_to_targetScript.sml
    A definition theory, with 39 definitions, 2 datatypes and 2
    theorems.  Needed by 20 files of the port.  *)
(* ======================================================== *)

(*
  This compiler phase generates concrete (ARM, x64, ag32, RISC-V,
  MIPS) machine code from labLang assembly programs. This phase is the
  CakeML compiler's assembler: it computes label offsets and encodes
  all instructions according to the instruction encoder stored in the
  compiler configuration.
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_filter.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "lab_to_target"
  ["ffi"; "labLang"; "lab_filter"];;

(* Number of bytes per FFI *)
let ffi_offset_def = new_definition
  `ffi_offset = (16:num)`;;

(* basic assemble function *)

let lab_inst_def = define_cases
  `(lab_inst (w:'a word) (lab_Jump _) = asm_Jump w) /\
   (lab_inst (w:'a word) (lab_JumpCmp c r ri _) = asm_JumpCmp c r ri w) /\
   (lab_inst (w:'a word) (lab_Call _) = asm_Call w) /\
   (lab_inst (w:'a word) (lab_LocValue r _) = asm_Loc r (w:'a word)) /\
   (lab_inst (w:'a word) lab_Halt = asm_Jump w) /\
   (lab_inst (w:'a word) lab_Install = asm_Jump w) /\
   (lab_inst (w:'a word) (lab_CallFFI n) = asm_Jump w)`;;

let cbw_to_asm_def = new_definition
  `cbw_to_asm a =
   match a with
     Asmi a -> a
   | Cbw r1 r2 -> asm_Inst (asm_Mem asm_Store8 r2 (Addr r1 (n2w 0)))
   | ShareMem m r ad -> asm_Inst (asm_Mem m r ad)`;;
add_simp cbw_to_asm_def;;


let enc_line_def = define_cases
  `(lab_to_target_enc_line enc skip_len (lab_Label n1 n2 n3) = lab_Label n1
    n2 skip_len) /\
   (lab_to_target_enc_line enc skip_len (lab_Asm a _ _) =
         let bs = enc (cbw_to_asm a) in lab_Asm a bs (LENGTH bs)) /\
   (lab_to_target_enc_line enc skip_len (lab_LabAsm l _ _ _) =
         let bs = enc (lab_inst (n2w 0) l) in
           lab_LabAsm l (n2w 0) bs (LENGTH bs))`;;

let enc_sec_def = define_general
  `lab_to_target_enc_sec enc skip_len (Section k xs) =
     Section k (MAP (lab_to_target_enc_line enc skip_len) xs)`;;

let enc_sec_list_def = new_definition
  `lab_to_target_enc_sec_list enc xs =
     let skip_len = LENGTH (enc (asm_Inst asm_Skip)) in
       MAP (lab_to_target_enc_sec enc skip_len) xs`;;

(* compute labels *)

make_size "line";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let section_labels_def,section_labels_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (line_size (\x. 0)) x1)`
  `(section_labels pos [] labs = (pos,labs)) /\
   (section_labels pos (CONS (lab_Label _ l2 len) xs) labs =
         // Ignore 0 labels
         if l2 = 0 then
           section_labels (pos + len) xs labs
         else section_labels (pos + len) xs (CONS (l2,pos + len) labs)) /\
   (section_labels pos (CONS (lab_Asm _ _ len) xs) labs =
         section_labels (pos + len) xs labs) /\
   (section_labels pos (CONS (lab_LabAsm _ _ _ len) xs) labs =
         section_labels (pos + len) xs labs)`;;

make_size "sec";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let compute_labels_alt_def,compute_labels_alt_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (sec_size (\x. 0)) x1)`
  `(compute_labels_alt pos [] labs = labs) /\
   (compute_labels_alt pos (CONS (Section k lines) rest) labs =
        let (new_pos,sec_labs) = section_labels pos lines [] in
        compute_labels_alt new_pos rest
          (sptree_insert k (fromAList (CONS (0,pos) sec_labs)) labs))`;;

(* update code, but not label lengths *)

let find_pos_def = define_general
  `find_pos (lab_Lab k1 k2) labs =
     ((lookup_any k2 (lookup_any k1 labs LN) 0):num)`;;

let get_label_def = new_definition
  `get_label x1 =
     match x1 with
       lab_Jump l -> l
     | lab_JumpCmp c r ri l -> l
     | lab_Call l -> l
     | lab_LocValue r l -> l
     // cannot happen
     | _ -> lab_Lab 0 0`;;

(* It should never happen that get_ffi_index returns the default 0 ---
   nonetheless, having a default prevents the translator from generating
   painful side conditions.
 *)
let get_ffi_index_def = new_definition
  `get_ffi_index ffis s =
     the 0 (find_index s ffis 0)`;;

let get_jump_offset_def = new_definition
  `get_jump_offset a ffis labs pos =
     match a with
       lab_CallFFI s ->
        (n2w 0) - n2w (pos + (3 + get_ffi_index ffis (ffi_ExtCall s)) *
          ffi_offset)
     | lab_Install ->
        (n2w 0) - n2w (pos + 2 * ffi_offset)
     | lab_Halt ->
        (n2w 0) - n2w (pos + ffi_offset)
     | a ->
        n2w (find_pos (get_label a) labs) - n2w pos`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let enc_lines_again_def,enc_lines_again_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4,x5).      list_size (line_size (\x. 0)) x4 +
  pair_size (list_size (line_size (\x. 0))) (\x. 0) x5)`
  `(lab_to_target_enc_lines_again labs ffis pos enc [] (acc,ok) = (REVERSE
    acc,pos,(ok:bool))) /\
   (lab_to_target_enc_lines_again labs ffis pos enc (CONS (lab_Label k1 k2 l)
    xs) (acc,ok) =
         lab_to_target_enc_lines_again labs ffis (pos + l) enc xs (CONS
             (lab_Label k1 k2 l) acc,ok)) /\
   (lab_to_target_enc_lines_again labs ffis pos enc (CONS (lab_Asm x1 x2 l) xs)
    (acc,ok) =
         lab_to_target_enc_lines_again labs ffis (pos + l) enc xs (CONS
             (lab_Asm x1 x2 l) acc,ok)) /\
   (lab_to_target_enc_lines_again labs ffis pos enc (CONS (lab_LabAsm a w bytes
    l) xs) (acc,ok) =
         let w1 = get_jump_offset a ffis labs pos in
           if w = w1 then
             lab_to_target_enc_lines_again labs ffis (pos + l) enc xs (CONS
                 (lab_LabAsm a w bytes l) acc,ok)
           else let bs = enc (lab_inst w1 a) in
             let l1 = MAX (LENGTH bs) l in
               lab_to_target_enc_lines_again labs ffis (pos + l1) enc xs
                 (CONS (lab_LabAsm a w1 bs l1) acc,(ok /\ (l1 = l))))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let enc_secs_again_def,enc_secs_again_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). list_size (sec_size (\x. 0)) x4)`
  `(lab_to_target_enc_secs_again pos labs ffis enc [] = ([],T)) /\
   (lab_to_target_enc_secs_again pos labs ffis enc (CONS (Section s lines)
    rest) =
         let (lines1,pos1,ok) = lab_to_target_enc_lines_again labs ffis pos
             enc lines ([],T) in
         let (rest1,ok1) = lab_to_target_enc_secs_again pos1 labs ffis enc
             rest in
           (CONS (Section s lines1) rest1,(ok /\ ok1)))`;;

(* update labels *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let lines_upd_lab_len_def,lines_upd_lab_len_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (line_size (\x. 0)) x1)`
  `(lines_upd_lab_len pos [] acc = (REVERSE acc,pos)) /\
   (lines_upd_lab_len pos (CONS (lab_Label k1 k2 l) xs) acc =
         let l1 = (if EVEN pos then 0 else 1) in
           lines_upd_lab_len (pos + l1) xs ((CONS (lab_Label k1 k2 l1)
               acc))) /\
   (lines_upd_lab_len pos (CONS (lab_Asm x1 x2 l) xs) acc =
         lines_upd_lab_len (pos + l) xs (CONS (lab_Asm x1 x2 l) acc)) /\
   (lines_upd_lab_len pos (CONS (lab_LabAsm a w bytes l) xs) acc =
         lines_upd_lab_len (pos + l) xs (CONS (lab_LabAsm a w bytes l)
             acc))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let upd_lab_len_def,upd_lab_len_ind = define_wf
  `MEASURE (\(x0,x1). list_size (sec_size (\x. 0)) x1)`
  `(upd_lab_len pos [] = []) /\
   (upd_lab_len pos (CONS (Section s lines) rest) =
         let (lines1,pos1) = lines_upd_lab_len pos lines [] in
         let rest1 = upd_lab_len pos1 rest in CONS (Section s lines1)
             rest1)`;;

(* checking that all labelled asm instructions are asm_ok *)

let line_ok_light_def = new_definition
  `line_ok_light c x2 =
     match (c,x2) with
       ((c:'a asm_config),lab_Label _ _ l) -> T
     | (c,lab_Asm b bytes l) -> T
     | (c,lab_LabAsm lab_Halt w bytes l) ->
        asm_ok (asm_Jump w) c
     | (c,lab_LabAsm lab_Install w bytes l) ->
        asm_ok (asm_Jump w) c
     | (c,lab_LabAsm (lab_CallFFI index) w bytes l) ->
        asm_ok (asm_Jump w) c
     | (c,lab_LabAsm (lab_Call v24) w bytes l) ->
        F
     // Call not yet supported
     | (c,lab_LabAsm a w bytes l) ->
        asm_ok (lab_inst w a) c`;;

let sec_ok_light_def = define_general
  `sec_ok_light c (Section k ls) <=>
     ALL (line_ok_light c) ls`;;
add_simp sec_ok_light_def;;

(* HOL4 lab_to_targetScript.sml:188: the overload all_enc_ok_light, which
   the port expands *)

(* pad with nop byte, and nop instruction *)

let pad_bytes_def = new_definition
  `pad_bytes bytes len nop =
     let len_bytes = LENGTH bytes in
       if len <= len_bytes then bytes else TAKE len (APPEND bytes (FLAT
         (REPLICATE len nop)))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let add_nop_def,add_nop_ind = define_wf
  `MEASURE (\(x0,x1). list_size (line_size (\x. 0)) x1)`
  `(add_nop nop [] = []) /\
   (add_nop nop (CONS (lab_Label l1 l2 len) xs) = CONS (lab_Label l1 l2
    len) (add_nop nop xs)) /\
   (add_nop nop (CONS (lab_Asm x bytes len) xs) = CONS (lab_Asm x (APPEND
    bytes nop) (len + 1)) xs) /\
   (add_nop nop (CONS (lab_LabAsm y w bytes len) xs) = CONS (lab_LabAsm y
    w (APPEND bytes nop) (len + 1)) xs)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let pad_section_def,pad_section_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (line_size (\x. 0)) x1)`
  `(pad_section nop [] aux = REVERSE aux) /\
   (pad_section nop (CONS (lab_Label l1 l2 len) xs) aux =
         pad_section nop xs (CONS (lab_Label l1 l2 0)
         (if len = 0 then aux else add_nop nop aux))) /\
   (pad_section nop (CONS (lab_Asm x bytes len) xs) aux =
         pad_section nop xs (CONS (lab_Asm x (pad_bytes bytes len nop)
             len) aux)) /\
   (pad_section nop (CONS (lab_LabAsm y w bytes len) xs) aux =
         pad_section nop xs (CONS (lab_LabAsm y w (pad_bytes bytes len
             nop) len) aux))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let pad_code_def,pad_code_ind = define_wf
  `MEASURE (\(x0,x1). list_size (sec_size (\x. 0)) x1)`
  `(pad_code nop [] = []) /\
   (pad_code nop (CONS (Section n xs) ys) = CONS (Section n (pad_section
    nop xs [])) (pad_code nop ys))`;;

let pad_code_MAP = prove
 (`pad_code nop =
    MAP (\x. Section (Section_num x) (pad_section nop (Section_lines x)
      []))`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let sec_length_def,sec_length_ind = define_wf
  `MEASURE (\(x0,x1). list_size (line_size (\x. 0)) x0)`
  `(sec_length [] k = k) /\
   (sec_length (CONS (lab_Label _ _ l) xs) k = sec_length xs (k + l)) /\
   (sec_length (CONS (lab_Asm x1 x2 l) xs) k = sec_length xs (k + l)) /\
   (sec_length (CONS (lab_LabAsm a w bytes l) xs) k = sec_length xs (k +
    l))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_symbols_def,get_symbols_ind = define_wf
  `MEASURE (\(x0,x1). list_size (sec_size (\x. 0)) x1)`
  `(get_symbols pos [] = []) /\
   (get_symbols pos (CONS (Section k l) secs) =
        let len = sec_length l 0 in CONS (k,pos,len) (get_symbols (pos
            + len) secs))`;;

(* Compute the labels whose second part is 0 *)
let zero_labs_acc_of_def = new_definition
  `zero_labs_acc_of x1 acc =
     match x1 with
       lab_LocValue _ (lab_Lab n1 n2) ->
       if n2 = 0 then sptree_insert n1 one acc else acc
     | lab_Jump (lab_Lab n1 n2) ->
       if n2 = 0 then sptree_insert n1 one acc else acc
     | lab_JumpCmp _ _ _ (lab_Lab n1 n2) ->
       if n2 = 0 then sptree_insert n1 one acc else acc
     | _ -> acc`;;
add_simp zero_labs_acc_of_def;;


let line_get_zero_labs_acc_def = new_definition
  `line_get_zero_labs_acc x1' acc =
   match x1' with
     lab_LabAsm a _ _ _ -> zero_labs_acc_of a acc
   | _ -> acc`;;

let sec_get_zero_labs_acc_def = define_general
  `sec_get_zero_labs_acc (Section _ lines) acc =
     ITLIST line_get_zero_labs_acc lines acc`;;

let get_zero_labs_acc_def = new_definition
  `get_zero_labs_acc code =
     ITLIST sec_get_zero_labs_acc code LN`;;

let zero_labs_acc_exist_def = new_definition
  `zero_labs_acc_exist labs code <=>
     (let zlabs = toAList (get_zero_labs_acc code) in
     ALL (\(n,_).
     match sptree_lookup n labs with NONE -> F
     | SOME l -> ~(sptree_lookup 0 l = NONE)) zlabs)`;;

(* top-level assembler function *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let remove_labels_loop_def,remove_labels_loop_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4,x5). (\n. n) x0)`
  `remove_labels_loop clock c pos init_labs ffis sec_list =
     // compute labels
     let labs = compute_labels_alt pos sec_list init_labs in
     // update encodings and lengths (but not label lengths)
     let (sec_list,done) = lab_to_target_enc_secs_again pos labs ffis
       (asm_config_encode c) sec_list in
       // done ==> labs are still fine
       if done then
         // adjust label lengths
         let sec_list = upd_lab_len pos sec_list in
         // compute labels again
         let labs = compute_labels_alt pos sec_list init_labs in
         // update encodings
         let (sec_list,done) = lab_to_target_enc_secs_again pos labs ffis
           (asm_config_encode c) sec_list in
         // move label padding into instructions
         let sec_list = pad_code (asm_config_encode c (asm_Inst asm_Skip))
           sec_list in
           // it ought to be impossible for done to be false here
           if done /\ (\c ls. ALL (sec_ok_light c) ls) c sec_list /\
              zero_labs_acc_exist labs sec_list then SOME (sec_list,labs)
           else NONE
       else
         // repeat
         if clock = (0:num) then NONE else remove_labels_loop (clock -
           1) c pos init_labs ffis sec_list`;;

let remove_labels_def = new_definition
  `remove_labels init_clock c pos labs ffis sec_list =
     // Here init_clock puts an upper limit on the number of times the
     // lengths can be adjusted. In many cases, clock = 0 should be
     // enough. If this were to hit the clock limit for large values of
     // init_clock, then something is badly wrong. Worth testing with
     // the clock limit set to low values to see how many iterations
     // are used.
     remove_labels_loop init_clock c pos labs ffis
       (lab_to_target_enc_sec_list (asm_config_encode c) sec_list)`;;

(* code extraction *)

let line_bytes_def = define_cases
  `(line_bytes (lab_Label _ _ _) = []) /\
   (line_bytes (lab_Asm _ bytes _) = bytes) /\
   (line_bytes (lab_LabAsm _ _ bytes _) = bytes)`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let prog_to_bytes_def,prog_to_bytes_ind = define_guess_cheat
  `(prog_to_bytes [] = []) /\
   (prog_to_bytes (CONS (Section k []) xs) = prog_to_bytes xs) /\
   (prog_to_bytes (CONS (Section k (CONS y ys)) xs) = APPEND (line_bytes
    y) (prog_to_bytes (CONS (Section k ys) xs)))`;;

(* HOL4 lab_to_targetScript.sml:339: ML code, not ported *)

let prog_to_bytes_MAP = prove
 (`!ls. prog_to_bytes ls = FLAT
          (MAP (FLAT o MAP line_bytes o Section_lines) ls)`,
  CHEAT_TAC);;

(* compile labels *)
let shmem_info_num_FIELDS = define_record "shmem_info_num"
  ["entry_pc","num";
   "nbytes","word8";
   "addr_reg","num";
   "addr_off","num";
   "reg","num";
   "exit_pc","num"];;

let lab_to_target_config_FIELDS = define_record "lab_to_target_config"
  ["labels","(num spt) spt";
   "sec_pos_len","(num#num#num) list";
   "pos","num";
   "init_clock","num";
   "ffi_names","(ffiname list) option";
   "shmem_extra","shmem_info_num list";
   "hash_size","num"];;

let list_add_if_fresh_def,list_add_if_fresh_ind = define_rec
  `(list_add_if_fresh e [] = [e]) /\
   (list_add_if_fresh e (CONS f r) =
        if e = f then CONS f r else CONS f (list_add_if_fresh e r))`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let find_ffi_names_def,find_ffi_names_ind = define_guess_cheat
  `(find_ffi_names [] = []) /\
   (find_ffi_names (CONS (Section k []) rest) =
         find_ffi_names rest) /\
   (find_ffi_names (CONS (Section k (CONS x xs)) rest) =
       (match x with lab_LabAsm (lab_CallFFI s) _ _ _ ->
           list_add_if_fresh (ffi_ExtCall s) (find_ffi_names (CONS (Section
               k xs) rest))
       | _ -> find_ffi_names (CONS (Section k xs) rest)))`;;

let get_memop_info_def = define_cases
  `(get_memop_info asm_Load = (MappedRead,((n2w 0):word8))) /\
   (get_memop_info asm_Load32 = (MappedRead,(n2w 4))) /\
   (get_memop_info asm_Load16 = (MappedRead,(n2w 2))) /\
   (get_memop_info asm_Load8 = (MappedRead,(n2w 1))) /\
   (get_memop_info asm_Store = (MappedWrite,(n2w 0))) /\
   (get_memop_info asm_Store32 = (MappedWrite,(n2w 4))) /\
   (get_memop_info asm_Store16 = (MappedWrite,(n2w 2))) /\
   (get_memop_info asm_Store8 = (MappedWrite,(n2w 1)))`;;

(* produce a list of ffi_names for shared memory instructions and
  a list of shmem_infos (e.g. pc of the shared memory instruction) *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_shmem_info_def,get_shmem_info_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). list_size (sec_size (\x. 0)) x0)`
  `get_shmem_info x1 pos ffi_names' shmem_info =
     match (x1,shmem_info) with
       (([]:('a sec) list),(shmem_info:shmem_info_num list)) ->
       (ffi_names',shmem_info)
     | (CONS (Section k []) rest,shmem_info) ->
       get_shmem_info rest pos ffi_names' shmem_info
     | (CONS (Section k (CONS (lab_Label _ _ _) xs)) rest,shmem_info) ->
       get_shmem_info (CONS (Section k xs) rest) pos ffi_names' shmem_info
     | (CONS (Section k (CONS (lab_Asm (ShareMem m r ad) bytes _) xs))
       rest,shmem_info) ->
       let (name,nb) = get_memop_info m in
       get_shmem_info (CONS (Section k xs) rest) (pos + LENGTH bytes)
         (APPEND ffi_names' [ffi_SharedMem name])
         (APPEND shmem_info
         [
           mk_shmem_info_num pos nb (match ad with Addr r off -> r) (match
             ad with Addr r off -> w2n off) r (pos + LENGTH bytes)])
     | (CONS (Section k (CONS (lab_LabAsm _ _ bytes _) xs)) rest,shmem_info)
       ->
       get_shmem_info (CONS (Section k xs) rest) (pos + LENGTH bytes)
         ffi_names' shmem_info
     | (CONS (Section k (CONS (lab_Asm _ bytes _) xs)) rest,shmem_info) ->
       get_shmem_info (CONS (Section k xs) rest) (pos + LENGTH bytes)
         ffi_names' shmem_info`;;

(* HOL4 lab_to_targetScript.sml:429-450: code that the source has in a
   comment *)


let compile_lab_def = new_definition
  `lab_to_target_compile_lab asm_conf c sec_list =
     (let current_ffis = find_ffi_names sec_list in
     let (ffis,ffis_ok) =
         (match lab_to_target_config_ffi_names c with SOME ffis ->
           (ffis,list_subset current_ffis ffis)
          | _ -> (current_ffis,T)) in
     if ffis_ok then
       match remove_labels (lab_to_target_config_init_clock c) asm_conf
         (lab_to_target_config_pos c) (lab_to_target_config_labels c) ffis
         sec_list with SOME (sec_list,l1) ->
           let bytes = prog_to_bytes sec_list in
           let (new_ffis,shmem_infos) = get_shmem_info sec_list
             (lab_to_target_config_pos c) [] [] in
           SOME (bytes,lab_to_target_config_shmem_extra_fupd (K shmem_infos)
             (lab_to_target_config_ffi_names_fupd (K (SOME (APPEND ffis
             new_ffis))) (lab_to_target_config_sec_pos_len_fupd (K (get_symbols
             (lab_to_target_config_pos c) sec_list))
             (lab_to_target_config_pos_fupd (K (LENGTH bytes +
             lab_to_target_config_pos c)) (lab_to_target_config_labels_fupd (K
             l1)
                 c)))))
       | NONE -> NONE
     else NONE)`;;

(* compile labLang *)

let lab_to_target_compile_def = new_definition
  `lab_to_target_compile asm_conf c sec_list = lab_to_target_compile_lab
  asm_conf c (filter_skip sec_list)`;;

(* and the interface *)
let _ = unhide_overloads ();;
