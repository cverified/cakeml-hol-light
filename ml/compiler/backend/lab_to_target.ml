(* ======================================================== *)
(*  lab_to_target: ported from HOL4's
    compiler/backend/lab_to_targetScript.sml  *)
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

(* Number of bytes per FFI *)
let ffi_offset_def = cake_define
  `ffi_offset = (16:num)`;;

(* basic assemble function *)

let lab_inst_def = cake_define
  `(lab_inst w (Jump _1:asm_with_lab) = Jump w) /\
   (lab_inst w (JumpCmp c r ri _2) = JumpCmp c r ri w) /\
   (lab_inst w (Call _3) = Call w) /\
   (lab_inst w (LocValue r _4) = Loc r (w:'a word)) /\
   (lab_inst w (Halt) = Jump w) /\
   (lab_inst w (Install) = Jump w) /\
   (lab_inst w (CallFFI n) = Jump w)`;;

let cbw_to_asm_def = cake_define
  `cbw_to_asm a =
   (match a with
     Asmi a -> a | Cbw r1 r2 -> Inst (Mem Store8 r2 (Addr r1 (n2w
       0))) | ShareMem m r ad -> Inst (Mem m r ad))`;;


let enc_line_def = cake_define
  `(enc_line enc skip_len (Label n1 n2 n3) = Label n1 n2 skip_len) /\
   (enc_line enc skip_len (Asm a _5 _6) =
      (let bs = enc (cbw_to_asm a) in Asm a bs (LENGTH bs))) /\
   (enc_line enc skip_len (LabAsm l _7 _8 _9) =
      (let bs = enc (lab_inst (n2w 0) l) in
        LabAsm l (n2w 0) bs (LENGTH bs)))`;;

let enc_sec_def = cake_define
  `enc_sec enc skip_len (Section k xs) =
     Section k (MAP (enc_line enc skip_len) xs)`;;

let enc_sec_list_def = cake_define
  `enc_sec_list enc xs =
     (let skip_len = LENGTH (enc (Inst Skip)) in
       MAP (enc_sec enc skip_len) xs)`;;

(* compute labels *)

let section_labels_def = cake_define
  `(section_labels pos [] labs = (pos,labs)) /\
   (section_labels pos (Label _10 l2 len :: xs) labs =
      (if l2 = 0 then
        section_labels (pos + len) xs labs else
        section_labels (pos + len) xs ((l2,pos + len) :: labs))) /\
   (section_labels pos (Asm _11 _12 len :: xs) labs =
      section_labels (pos + len) xs labs) /\
   (section_labels pos (LabAsm _13 _14 _15 len :: xs) labs =
      section_labels (pos + len) xs labs)`;;

let compute_labels_alt_def = cake_define
  `(compute_labels_alt pos [] labs = labs) /\
   (compute_labels_alt pos (Section k lines :: rest) labs =
     (let (new_pos,sec_labs) = section_labels pos lines [] in
     compute_labels_alt new_pos rest
       (insert k (fromAList ((0,pos) :: sec_labs)) labs)))`;;

(* update code, but not label lengths *)

let find_pos_def = cake_define
  `find_pos (Lab k1 k2) labs =
     ((lookup_any k2 (lookup_any k1 labs LN) 0):num)`;;

let get_label_def = cake_define
  `get_label x1 =
        match x1 with
          (Jump l:asm_with_lab) -> l
        | (JumpCmp c r ri l) -> l
        | (Call l) -> l
        | (LocValue r l) -> l
        | _16 -> Lab 0 0`;;

(* It should never happen that get_ffi_index returns the default 0 ---
   nonetheless, having a default prevents the translator from generating
   painful side conditions.
 *)
let get_ffi_index_def = cake_define
  `get_ffi_index ffis s =
     the 0 (find_index s ffis 0)`;;

let get_jump_offset_def = cake_define
  `get_jump_offset a ffis labs pos =
        match a with
          CallFFI s ->
        (n2w 0) - n2w (pos + (3 + get_ffi_index ffis (ExtCall s)) *
          ffi_offset)
        | Install ->
        (n2w 0) - n2w (pos + 2 * ffi_offset)
        | Halt ->
        (n2w 0) - n2w (pos + ffi_offset)
        | a ->
        n2w (find_pos (get_label a) labs) - n2w pos`;;

let enc_lines_again_def = cake_define
  `(enc_lines_again labs ffis pos enc [] (acc,ok) = (REVERSE
  acc,pos,(ok:bool))) /\
   (enc_lines_again labs ffis pos enc ((Label k1 k2 l) :: xs)
     (acc,ok) =
      enc_lines_again labs ffis (pos + l) enc xs ((Label k1 k2 l) ::
        acc,ok)) /\
   (enc_lines_again labs ffis pos enc ((Asm x1 x2 l) :: xs) (acc,ok)
     =
      enc_lines_again labs ffis (pos + l) enc xs ((Asm x1 x2 l) ::
        acc,ok)) /\
   (enc_lines_again labs ffis pos enc ((LabAsm a w bytes l) :: xs)
     (acc,ok) =
      (let w1 = get_jump_offset a ffis labs pos in
        if w = w1 then
          enc_lines_again labs ffis (pos + l) enc xs ((LabAsm a w
            bytes l) :: acc,ok) else
          let bs = enc (lab_inst w1 a) in
          let l1 = MAX (LENGTH bs) l in
            enc_lines_again labs ffis (pos + l1) enc xs
              ((LabAsm a w1 bs l1) :: acc,(ok /\ (l1 = l)))))`;;

let enc_secs_again_def = cake_define
  `(enc_secs_again pos labs ffis enc [] = ([],T)) /\
   (enc_secs_again pos labs ffis enc ((Section s lines) :: rest) =
      (let (lines1,pos1,ok) = enc_lines_again labs ffis pos enc lines
        ([],T) in
      let (rest1,ok1) = enc_secs_again pos1 labs ffis enc rest in
        ((Section s lines1) :: rest1,(ok /\ ok1))))`;;

(* update labels *)

let lines_upd_lab_len_def = cake_define
  `(lines_upd_lab_len pos [] acc = (REVERSE acc,pos)) /\
   (lines_upd_lab_len pos ((Label k1 k2 l) :: xs) acc =
      (let l1 = if EVEN pos then 0 else 1 in
        lines_upd_lab_len (pos + l1) xs ((Label k1 k2 l1 :: acc))))
          /\
   (lines_upd_lab_len pos ((Asm x1 x2 l) :: xs) acc =
      lines_upd_lab_len (pos + l) xs ((Asm x1 x2 l) :: acc)) /\
   (lines_upd_lab_len pos ((LabAsm a w bytes l) :: xs) acc =
      lines_upd_lab_len (pos + l) xs ((LabAsm a w bytes l) ::
        acc))`;;

let upd_lab_len_def = cake_define
  `(upd_lab_len pos [] = []) /\
   (upd_lab_len pos ((Section s lines) :: rest) =
      (let (lines1,pos1) = lines_upd_lab_len pos lines [] in
      let rest1 = upd_lab_len pos1 rest in
        (Section s lines1) :: rest1))`;;

(* checking that all labelled asm instructions are asm_ok *)

let line_ok_light_def = cake_define
  `line_ok_light c x2 =
        match (c,x2) with
          ((c:'a asm_config),Label _17 _18 l) -> T
        | (c,(Asm b bytes l)) -> T
        | (c,(LabAsm Halt w bytes l)) ->
        asm_ok (Jump w) c
        | (c,(LabAsm Install w bytes l)) ->
        asm_ok (Jump w) c
        | (c,(LabAsm (CallFFI index) w bytes l)) ->
        asm_ok (Jump w) c
        | (c,(LabAsm (Call v24) w bytes l)) ->
        F
        | (c,(LabAsm a w bytes l)) ->
        asm_ok (lab_inst w a) c`;;

let sec_ok_light_def = cake_define
  `sec_ok_light c (Section k ls) <=>
     EVERY (line_ok_light c) ls`;;

(* HOL4 overload (expanded in the port):
     all_enc_ok_light = λc ls. EVERY (sec_ok_light c) ls *)

(* pad with nop byte, and nop instruction *)

let pad_bytes_def = cake_define
  `pad_bytes bytes len nop =
     (let len_bytes = LENGTH bytes in
       if len <= len_bytes then bytes else
         TAKE len (bytes ++ FLAT (REPLICATE len nop)))`;;

let add_nop_def = cake_define
  `(add_nop nop [] = []) /\
   (add_nop nop ((Label l1 l2 len) :: xs) =
     (Label l1 l2 len) :: add_nop nop xs) /\
   (add_nop nop ((Asm x bytes len) :: xs) =
     Asm x (bytes ++ nop) (len + 1) :: xs) /\
   (add_nop nop ((LabAsm y w bytes len) :: xs) =
     LabAsm y w (bytes ++ nop) (len + 1) :: xs)`;;

let pad_section_def = cake_define
  `(pad_section nop [] aux = REVERSE aux) /\
   (pad_section nop ((Label l1 l2 len) :: xs) aux =
      pad_section nop xs ((Label l1 l2 0) ::
      (if len = 0 then aux else add_nop nop aux))) /\
   (pad_section nop ((Asm x bytes len) :: xs) aux =
      pad_section nop xs (Asm x (pad_bytes bytes len nop) len ::
        aux)) /\
   (pad_section nop ((LabAsm y w bytes len) :: xs) aux =
      pad_section nop xs (LabAsm y w (pad_bytes bytes len nop) len
        :: aux))`;;

let pad_code_def = cake_define
  `(pad_code nop [] = []) /\
   (pad_code nop ((Section n xs) :: ys) =
     Section n (pad_section nop xs []) :: pad_code nop ys)`;;

let sec_length_def = cake_define
  `(sec_length [] k = k) /\
   (sec_length ((Label _19 _20 l) :: xs) k = sec_length xs (k + l))
     /\
   (sec_length ((Asm x1 x2 l) :: xs) k = sec_length xs (k + l)) /\
   (sec_length ((LabAsm a w bytes l) :: xs) k = sec_length xs (k +
     l))`;;

let get_symbols_def = cake_define
  `(get_symbols pos [] = []) /\
   (get_symbols pos ((Section k l) :: secs) =
     (let len = sec_length l 0 in (k,pos,len) :: get_symbols (pos
       + len) secs))`;;

(* Compute the labels whose second part is 0 *)
let zero_labs_acc_of_def = cake_define
  `zero_labs_acc_of x1 acc =
        match x1 with
          LocValue _21 (Lab n1 n2) ->
       (if n2 = 0 then insert n1 one acc else acc)
        | (Jump (Lab n1 n2)) ->
       (if n2 = 0 then insert n1 one acc else acc)
        | (JumpCmp _22 _23 _24 (Lab n1 n2)) ->
       (if n2 = 0 then insert n1 one acc else acc)
        | _25 -> acc`;;


let line_get_zero_labs_acc_def = cake_define
  `line_get_zero_labs_acc x1 acc =
      match x1 with
        LabAsm a _26 _27 _28 -> zero_labs_acc_of a acc
      | _29 -> acc`;;

let sec_get_zero_labs_acc_def = cake_define
  `sec_get_zero_labs_acc (Section _30 lines) acc =
     ITLIST line_get_zero_labs_acc lines acc`;;

let get_zero_labs_acc_def = cake_define
  `get_zero_labs_acc code =
     ITLIST sec_get_zero_labs_acc code LN`;;

let zero_labs_acc_exist_def = cake_define
  `zero_labs_acc_exist labs code <=>
     (let zlabs = toAList (get_zero_labs_acc code) in
     EVERY (\(n,_31).
     match lookup n labs with NONE -> F | SOME l -> ~(lookup 0 l =
       NONE)) zlabs)`;;

(* top-level assembler function *)

let remove_labels_loop_def = cake_define
  `remove_labels_loop clock c pos init_labs ffis sec_list =
     (let labs = compute_labels_alt pos sec_list init_labs in
     let (sec_list,done') = enc_secs_again pos labs ffis
       (asm_config_encode c) sec_list in
       if done' then
         let sec_list = upd_lab_len pos sec_list in
         let labs = compute_labels_alt pos sec_list init_labs in
         let (sec_list,done') = enc_secs_again pos labs ffis
           (asm_config_encode c) sec_list in
         let sec_list = pad_code (asm_config_encode c (Inst Skip))
           sec_list in
           if done' /\ (\c ls. EVERY (sec_ok_light c) ls) c sec_list
             /\
              zero_labs_acc_exist labs sec_list then SOME
                (sec_list,labs) else NONE else
         if clock = (0:num) then NONE else
           remove_labels_loop (clock - 1) c pos init_labs ffis
             sec_list)`;;

let remove_labels_def = cake_define
  `remove_labels init_clock c pos labs ffis sec_list =
     remove_labels_loop init_clock c pos labs ffis (enc_sec_list
       (asm_config_encode c) sec_list)`;;

(* code extraction *)

let line_bytes_def = cake_define
  `(line_bytes (Label _32 _33 _34) = []) /\
   (line_bytes (Asm _35 bytes _36) = bytes) /\
   (line_bytes (LabAsm _37 _38 bytes _39) = bytes)`;;

let prog_to_bytes_def = cake_define
  `(prog_to_bytes [] = []) /\
   (prog_to_bytes ((Section k []) :: xs) = prog_to_bytes xs) /\
   (prog_to_bytes ((Section k (y :: ys)) :: xs) =
      line_bytes y ++ prog_to_bytes ((Section k ys) :: xs))`;;

(* HOL4 ML code, not ported:
val prog_to_bytes_ind = theorem"prog_to_bytes_ind";
*)

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

let list_add_if_fresh_def = cake_define
  `(list_add_if_fresh e [] = [e]) /\
   (list_add_if_fresh e (f :: r) =
     (if e = f then f :: r else f :: list_add_if_fresh e r))`;;

let find_ffi_names_def = cake_define
  `(find_ffi_names [] = []) /\
   (find_ffi_names (Section k [] :: rest) =
      find_ffi_names rest) /\
   (find_ffi_names (Section k (x :: xs) :: rest) =
    (match x with LabAsm (CallFFI s) _40 _41 _42 ->
        list_add_if_fresh (ExtCall s) (find_ffi_names (Section k
          xs :: rest)) | _43 -> find_ffi_names (Section k xs ::
          rest)))`;;

let get_memop_info_def = cake_define
  `get_memop_info Load = (MappedRead,((n2w 0):word8)) /\
   get_memop_info Load32 = (MappedRead,(n2w 4)) /\
   get_memop_info Load16 = (MappedRead,(n2w 2)) /\
   get_memop_info Load8 = (MappedRead,(n2w 1)) /\
   get_memop_info Store = (MappedWrite,(n2w 0)) /\
   get_memop_info Store32 = (MappedWrite,(n2w 4)) /\
   get_memop_info Store16 = (MappedWrite,(n2w 2)) /\
   get_memop_info Store8 = (MappedWrite,(n2w 1))`;;

(* produce a list of ffi_names for shared memory instructions and
  a list of shmem_infos (e.g. pc of the shared memory instruction) *)
let get_shmem_info_def = cake_define
  `get_shmem_info x1 pos ffi_names shmem_info =
        match (x1,shmem_info) with
          (([]:('a sec) list),(shmem_info:shmem_info_num list)) ->
       (ffi_names,shmem_info)
        | ((Section k [] :: rest),shmem_info) ->
       get_shmem_info rest pos ffi_names shmem_info
        | ((Section k ((Label _44 _45 _46) :: xs) ::
          rest),shmem_info) ->
       get_shmem_info (Section k xs :: rest) pos ffi_names shmem_info
        | ((Section k ((Asm (ShareMem m r ad) bytes _47) :: xs) ::
          rest),shmem_info) ->
       (let (name,nb) = get_memop_info m in
       get_shmem_info (Section k xs :: rest) (pos + LENGTH bytes)
         (ffi_names ++ [SharedMem name])
         (shmem_info ++
         [
           mk_shmem_info_num pos nb (match ad with Addr r off -> r)
             (match ad with Addr r off -> w2n off) r (pos + LENGTH
             bytes)]))
        | ((Section k ((LabAsm _48 _49 bytes _50) :: xs) ::
          rest),shmem_info) ->
       get_shmem_info (Section k xs :: rest) (pos + LENGTH bytes)
         ffi_names shmem_info
        | ((Section k ((Asm _51 bytes _52) :: xs) ::
          rest),shmem_info) ->
       get_shmem_info (Section k xs :: rest) (pos + LENGTH bytes)
         ffi_names shmem_info`;;

(*
Definition compile_lab_def:
  compile_lab c sec_list =
    let current_ffis = FILTER (\x. x <> "MappedRead" /\ x <>
      "MappedWrite") $
      find_ffi_names sec_list in
    let (ffis,ffis_ok) =
      case c.ffi_names of SOME ffis => (ffis, list_subset current_ffis
        ffis) | _ => (current_ffis,T)
    in
    if ffis_ok then
      case remove_labels c.init_clock c.asm_conf c.pos c.labels ffis
        sec_list of
      | SOME (sec_list,l1) =>
          let bytes = prog_to_bytes sec_list in
          let (new_ffis,shmem_infos) = get_shmem_info sec_list c.pos []
            [] in
          SOME (bytes,
                c with <| labels := l1; pos := LENGTH bytes + c.pos;
                          sec_pos_len := get_symbols c.pos sec_list;
                          ffi_names := SOME $ ffis ++ new_ffis;
                          shmem_extra := shmem_infos |>)
      | NONE => NONE
    else NONE
End
*)


let compile_lab_def = cake_define
  `compile_lab asm_conf c sec_list =
     (let current_ffis = find_ffi_names sec_list in
     let (ffis,ffis_ok) =
         (match lab_to_target_config_ffi_names c with SOME ffis ->
           (ffis,list_subset current_ffis ffis) | _53 ->
           (current_ffis,T)) in
     if ffis_ok then
       match remove_labels (lab_to_target_config_init_clock c)
         asm_conf (lab_to_target_config_pos c)
         (lab_to_target_config_labels c) ffis sec_list with SOME
         (sec_list,l1) ->
           (let bytes = prog_to_bytes sec_list in
           let (new_ffis,shmem_infos) = get_shmem_info sec_list
             (lab_to_target_config_pos c) [] [] in
           SOME (bytes,lab_to_target_config_shmem_extra_fupd (K
             shmem_infos) (lab_to_target_config_ffi_names_fupd (K (SOME
             (ffis ++ new_ffis))) (lab_to_target_config_sec_pos_len_fupd
             (K (get_symbols (lab_to_target_config_pos c) sec_list))
             (lab_to_target_config_pos_fupd (K (LENGTH bytes +
             lab_to_target_config_pos c))
             (lab_to_target_config_labels_fupd (K l1)
                 c)))))) | NONE -> NONE else NONE)`;;

(* compile labLang *)

let compile_def = cake_define
  `lab_to_target_compile asm_conf c sec_list = compile_lab asm_conf c
  (filter_skip sec_list)`;;
hol4_overload "compile" "lab_to_target_compile";;
