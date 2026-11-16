(* ======================================================== *)
(*  TextIOProof: ported from HOL4's
    basis/TextIOProofScript.sml
    A proof theory, with 43 definitions and 352 theorems.  Needed by
    7 files of the port.  *)
(* ======================================================== *)

(*
  Proofs about the code in the TextIO module.
*)

needs "basis/Marshalling.ml";;
needs "basis/MarshallingProg.ml";;
needs "basis/TextIOProg.ml";;
needs "basis/Word8ArrayProof.ml";;
needs "basis/Word8Prog.ml";;
needs "basis/fsFFI.ml";;
needs "basis/fsFFIProps.ml";;
needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/prover/compute/compute_exec.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfLetAuto.ml";;
needs "characteristic/cfMain.ml";;
needs "lib/int_arith.ml";;
needs "lib/set_sep.ml";;
needs "misc/misc.ml";;
needs "semantics/namespace.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "TextIOProof"
  ["Marshalling"; "MarshallingProg"; "TextIOProg"; "Word8ArrayProof";
   "Word8Prog"; "cf"; "cfLetAuto"; "cfMain"; "cfMonad"; "fsFFI";
   "fsFFIProps"; "ml_monadBase"; "ml_monad_translator"; "ml_prog";
   "ml_translator"; "mlstring"];;

let _ = do_list hide_constant ["TYPE"; "fv"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["name","CommandLineProof_name"];;
(* HOL4 ancestors outside the port: integer *)

(* heap predicate for the file-system state *)

let IOFS_iobuff_def = new_definition
  `IOFS_iobuff =
     SEP_EXISTS (\v. W8ARRAY iobuff_loc v * cond (LENGTH v >= 2052))`;;

let IOFS_def = new_definition
  `IOFS fs = IOx (fs_ffi_part) fs * IOFS_iobuff * &(wfFS fs)`;;

(*Used for read_into where the target buffer is specified*)
let IOFS_WO_iobuff_def = new_definition
  `IOFS_WO_iobuff fs = IOx (fs_ffi_part) fs * &(wfFS fs)`;;

let UNIQUE_IOFS = prove
 (`!s. VALID_HEAP s ==> (!fs1 fs2 H1 H2. (IOFS fs1 * H1) s /\
                              (IOFS fs2 * H2) s ==> fs1 = fs2)`,
  CHEAT_TAC);;

let IOFS_FFI_part_hprop = prove
 (`FFI_part_hprop (IOFS fs)`,
  CHEAT_TAC);;

(* [hprop_inj] *)
let IOFS_iobuff_HPROP_INJ = prove
 (`!fs1 fs2. HPROP_INJ (IOFS fs1) (IOFS fs2) (fs2 = fs1)`,
  CHEAT_TAC);;

(* "end-user" property *)
(* abstracts away the lazy list and ensure that standard streams are opened on
 * their respective standard fds at the right position *)

let STDIO_def = new_definition
  `STDIO fs = (SEP_EXISTS (\ll. IOFS (IO_fs_numchars_fupd (K ll) fs))) *
     &(STD_streams fs)`;;

let STDIO_STD_streams = prove
 (`STDIO fs = STDIO fs * &(STD_streams fs)`,
  CHEAT_TAC);;

let STDIO_consistentFS = prove
 (`STDIO fs = STDIO fs * &(consistentFS fs)`,
  CHEAT_TAC);;

(* Used by the monadic translator *)
let MONAD_IO_def = new_definition
  `MONAD_IO fs = STDIO fs * &((\fs. CARD (set_of_list (MAP FST (IO_fs_infds
  fs))) < MIN (IO_fs_maxFD fs) (256 EXP 8)) fs)`;;

let STDIO_numchars = prove
 (`STDIO (IO_fs_numchars_fupd (K x) fs) = STDIO fs`,
  CHEAT_TAC);;

let STDIO_bumpFD = prove
 (`STDIO (bumpFD fd fs n) = STDIO (forwardFD fs fd n)`,
  CHEAT_TAC);;
add_simp STDIO_bumpFD;;

let UNIQUE_STDIO = prove
 (`!s. VALID_HEAP s ==> (!fs1 fs2 H1 H2. (STDIO fs1 * H1) s /\
                              (STDIO fs2 * H2) s ==>
               (IO_fs_infds fs1 = IO_fs_infds fs2 /\ IO_fs_files fs1 =
                 IO_fs_files fs2 /\ IO_fs_maxFD fs1 = IO_fs_maxFD fs2
                 /\ IO_fs_inode_tbl fs1 = IO_fs_inode_tbl fs2))`,
  CHEAT_TAC);;

(* weak injection theorem *)
(* [hprop_inj] *)
let STDIO_HPROP_INJ = prove
 (`HPROP_INJ (STDIO fs1) (STDIO fs2)
            (IO_fs_infds fs1 = IO_fs_infds fs2 /\ IO_fs_files fs1 =
              IO_fs_files fs2 /\ IO_fs_maxFD fs1 = IO_fs_maxFD fs2
              /\ IO_fs_inode_tbl fs1 = IO_fs_inode_tbl fs2)`,
  CHEAT_TAC);;

(* refinement invariant for filenames *)
let FILENAME_def = new_definition
  `FILENAME s sv =
     (STRING_TYPE s sv /\
      ~(MEM (CHR 0) (explode s)) /\
      strlen s < 256 * 256)`;;

(* HOL4 TextIOProofScript.sml:159: a proof *)

(* [xlet_auto_match] *)
let FILENAME_UNICITY_R = prove
 (`!f fv' fv'. FILENAME f fv' ==> (FILENAME f fv' <=> fv' = fv')`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let FILENAME_UNICITY_L = prove
 (`!f f' fv'. FILENAME f fv' ==> (FILENAME f' fv' <=> f' = f)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let FILENAME_STRING_UNICITY_R = prove
 (`!f fv' fv'. FILENAME f fv' ==> (STRING_TYPE f fv' <=> fv' = fv')`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let FILENAME_STRING_UNICITY_L = prove
 (`!f f' fv'. FILENAME f fv' ==> (STRING_TYPE f' fv' <=> f' = f)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let STRING_FILENAME_UNICITY_R = prove
 (`!f fv' fv'. STRING_TYPE f fv' ==>
     (FILENAME f fv' <=> fv' = fv' /\ ~(MEM (CHR 94) (explode f))
       /\ strlen f < 256 * 256)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let STRING_FILENAME_UNICITY_L = prove
 (`!f f' fv'. STRING_TYPE f fv' ==>
     (FILENAME f' fv' <=> f' = f /\ ~(MEM (CHR 94) (explode f)) /\ strlen
       f < 256 * 256)`,
  CHEAT_TAC);;

(* exception refinement invariant lemmas *)

(* [xlet_auto_match] *)
let BadFileName_UNICITY = prove
 (`!v1 v2. BadFileName_exn v1 ==> (BadFileName_exn v2 <=> v2 = v1)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let InvalidFD_UNICITY = prove
 (`!v1 v2. InvalidFD_exn v1 ==> (InvalidFD_exn v2 <=> v2 = v1)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let EndOfFile_UNICITY = prove
 (`!v1 v2. EndOfFile_exn v1 ==> (EndOfFile_exn v2 <=> v2 = v1)`,
  CHEAT_TAC);;

(* [xlet_auto_match] *)
let IllegalArgument_UNICITY = prove
 (`!v1 v2. IllegalArgument_exn v1 ==> (IllegalArgument_exn v2 <=> v2 = v1)`,
  CHEAT_TAC);;

(* convenient functions for standard output/error
 * n.b. numchars is ignored *)

let stdo_def = new_definition
  `stdo fd' name fs out =
     (ALOOKUP (IO_fs_infds fs) fd' = SOME (UStream (implode
       name),WriteMode,strlen out) /\
      ALOOKUP (IO_fs_inode_tbl fs) (UStream (implode name)) = SOME
        (explode out))`;;

(* HOL4 TextIOProofScript.sml:234: the overload stdout, which the port
   expands *)
(* HOL4 TextIOProofScript.sml:235: the overload stderr, which the port
   expands *)

(* [xlet_auto_match] *)
let stdo_UNICITY_R = prove
 (`!fd' name fs out out'. stdo fd' name fs out ==> (stdo fd' name fs out' <=>
  out = out')`,
  CHEAT_TAC);;

let up_stdo_def = new_definition
  `up_stdo fd' fs out = fsupdate fs fd' 0 (strlen out) (explode out)`;;
(* HOL4 TextIOProofScript.sml:246: the overload up_stdout, which the port
   expands *)
(* HOL4 TextIOProofScript.sml:247: the overload up_stderr, which the port
   expands *)

let stdo_numchars = prove
 (`stdo fd name (IO_fs_numchars_fupd (K l) fs) out <=> stdo fd name fs out`,
  CHEAT_TAC);;

let up_stdo_numchars = prove
 (`IO_fs_numchars
      (up_stdo fd fs x) = IO_fs_numchars fs`,
  CHEAT_TAC);;
add_simp up_stdo_numchars;;

let fsupdate_files = prove
 (`IO_fs_files
     (fsupdate fs fd k pos c) = IO_fs_files fs`,
  CHEAT_TAC);;
add_simp fsupdate_files;;

let up_stdo_files = prove
 (`IO_fs_files
     (up_stdo fd fs x) = IO_fs_files fs`,
  CHEAT_TAC);;
add_simp up_stdo_files;;

let up_stdo_maxFD = prove
 (`IO_fs_maxFD
      (up_stdo fd fs x) = IO_fs_maxFD fs`,
  CHEAT_TAC);;
add_simp up_stdo_maxFD;;

let up_stdo_with_numchars = prove
 (`up_stdo fd (IO_fs_numchars_fupd (K ns) fs) x = IO_fs_numchars_fupd (K ns)
   (up_stdo fd fs x)`,
  CHEAT_TAC);;

let add_stdo_def = new_definition
  `add_stdo fd' nm fs out = up_stdo fd' fs (strcat (@init. stdo fd' nm fs
  init) out)`;;
(* HOL4 TextIOProofScript.sml:291: the overload add_stdout, which the port
   expands *)
(* HOL4 TextIOProofScript.sml:292: the overload add_stderr, which the port
   expands *)


let stdo_add_stdo = prove
 (`stdo fd nm fs init ==> stdo fd nm (add_stdo fd nm fs out) (strcat init
  out)`,
  CHEAT_TAC);;

let up_stdo_unchanged = prove
 (`!fs out. stdo fd nm fs out ==> up_stdo fd fs out = fs`,
  CHEAT_TAC);;

let stdo_up_stdo = prove
 (`!fs out out'. stdo fd nm fs out ==> stdo fd nm (up_stdo fd fs out') out'`,
  CHEAT_TAC);;

let add_stdo_nil = prove
 (`stdo fd nm fs out ==> add_stdo fd nm fs (implode "") = fs`,
  CHEAT_TAC);;

let add_stdout_nil = prove
 (`STD_streams fs ==> (add_stdo 1 "stdout") fs (implode "") = fs`,
  CHEAT_TAC);;

let add_stdo_o = prove
 (`stdo fd nm fs out ==>
   add_stdo fd nm (add_stdo fd nm fs x1) x2 = add_stdo fd nm fs (strcat x1
     x2)`,
  CHEAT_TAC);;

let add_stdo_numchars = prove
 (`IO_fs_numchars
      (add_stdo fd nm fs x) = IO_fs_numchars fs`,
  CHEAT_TAC);;
add_simp add_stdo_numchars;;

let add_stdo_maxFD = prove
 (`IO_fs_maxFD
      (add_stdo fd nm fs x) = IO_fs_maxFD fs`,
  CHEAT_TAC);;
add_simp add_stdo_maxFD;;

let add_stdo_with_numchars = prove
 (`add_stdo fd nm (IO_fs_numchars_fupd (K ns) fs) x = IO_fs_numchars_fupd (K
  ns)
   (add_stdo fd nm fs x)`,
  CHEAT_TAC);;

let up_stdo_MAP_FST_infds = prove
 (`MAP FST (IO_fs_infds (up_stdo fd fs out)) = MAP FST (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp up_stdo_MAP_FST_infds;;

let add_stdo_MAP_FST_infds = prove
 (`MAP FST (IO_fs_infds (add_stdo fd nm fs out)) = MAP FST (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp add_stdo_MAP_FST_infds;;

let up_stdo_MAP_FST_files = prove
 (`MAP FST (IO_fs_files (up_stdo fd fs out)) = MAP FST (IO_fs_files fs)`,
  CHEAT_TAC);;
add_simp up_stdo_MAP_FST_files;;

let up_stdo_MAP_FST_inode_tbl = prove
 (`MAP FST (IO_fs_inode_tbl (up_stdo fd fs out)) = MAP FST (IO_fs_inode_tbl
  fs)`,
  CHEAT_TAC);;
add_simp up_stdo_MAP_FST_inode_tbl;;

let add_stdo_MAP_FST_inode_tbl = prove
 (`MAP FST (IO_fs_inode_tbl (add_stdo fd nm fs out)) = MAP FST
  (IO_fs_inode_tbl fs)`,
  CHEAT_TAC);;
add_simp add_stdo_MAP_FST_inode_tbl;;

let inFS_fname_add_stdo = prove
 (`inFS_fname (add_stdo fd nm fs out) = inFS_fname fs`,
  CHEAT_TAC);;
add_simp inFS_fname_add_stdo;;

let STD_streams_stdout = prove
 (`STD_streams fs ==> (?out. (stdo 1 "stdout") fs out)`,
  CHEAT_TAC);;

let STD_streams_stderr = prove
 (`STD_streams fs ==> (?out. (stdo 2 "stderr") fs out)`,
  CHEAT_TAC);;

let STD_streams_add_stdout = prove
 (`STD_streams fs ==> STD_streams ((add_stdo 1 "stdout") fs out)`,
  CHEAT_TAC);;

let STD_streams_add_stderr = prove
 (`STD_streams fs ==> STD_streams ((add_stdo 2 "stderr") fs out)`,
  CHEAT_TAC);;

let fsupdate_add_stdout_implode = prove
 (`STD_streams fs /\ get_file_content fs 1 = SOME (content,pos) ==>
   (fsupdate fs 1 0 (pos + LENGTH s) (insert_atI s pos content)) =
   ((add_stdo 1 "stdout") fs (implode s))`,
  CHEAT_TAC);;

let fsupdate_add_stdout_str = prove
 (`STD_streams fs /\ get_file_content fs 1 = SOME (content,pos) ==>
   (fsupdate fs 1 0 (pos + 1) (insert_atI [c] pos content)) =
   ((add_stdo 1 "stdout") fs (integer_word_toString c))`,
  CHEAT_TAC);;

let fsupdate_add_stderr_implode = prove
 (`STD_streams fs /\ get_file_content fs 2 = SOME (content,pos) ==>
   (fsupdate fs 2 0 (pos + LENGTH s) (insert_atI s pos content)) =
   ((add_stdo 2 "stderr") fs (implode s))`,
  CHEAT_TAC);;

let fsupdate_add_stderr = prove
 (`STD_streams fs /\ get_file_content fs 2 = SOME (content,pos) ==>
   (fsupdate fs 2 0 (pos + strlen s) (insert_atI (explode s) pos content)) =
   ((add_stdo 2 "stderr") fs s)`,
  CHEAT_TAC);;

let validFD_up_stdo = prove
 (`validFD fd (up_stdo fd' fs out) <=> validFD fd fs`,
  CHEAT_TAC);;
add_simp validFD_up_stdo;;

let validFD_add_stdo = prove
 (`validFD fd (add_stdo fd' nm fs out) <=> validFD fd fs`,
  CHEAT_TAC);;
add_simp validFD_add_stdo;;

let validFileFD_up_stdo = prove
 (`TextIOProof_validFileFD fd (IO_fs_infds (up_stdo fd' fs out)) <=>
  TextIOProof_validFileFD fd (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp validFileFD_up_stdo;;

let validFileFD_add_stdo = prove
 (`TextIOProof_validFileFD fd (IO_fs_infds (add_stdo fd' nm fs out)) <=>
  TextIOProof_validFileFD fd (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp validFileFD_add_stdo;;

let consistentFS_add_stdout = prove
 (`consistentFS ((add_stdo 1 "stdout") fs s) = consistentFS fs`,
  CHEAT_TAC);;
add_simp consistentFS_add_stdout;;

let up_stdo_ADELKEY = prove
 (`~(fd = fd') ==>
      up_stdo fd (IO_fs_infds_fupd (ADELKEY fd') fs) out = IO_fs_infds_fupd
        (ADELKEY fd')
      (up_stdo fd fs out)`,
  CHEAT_TAC);;

let stdo_ADELKEY = prove
 (`~(fd = fd') ==>
      stdo fd nm (IO_fs_infds_fupd (ADELKEY fd') fs) = stdo fd nm fs`,
  CHEAT_TAC);;

let add_stdo_ADELKEY = prove
 (`~(fd = fd') ==>
      add_stdo fd nm (IO_fs_infds_fupd (ADELKEY fd') fs) out =
        IO_fs_infds_fupd (ADELKEY fd')
      (add_stdo fd nm fs out)`,
  CHEAT_TAC);;

let get_file_content_add_stdout = prove
 (`STD_streams fs /\ ~(fd = 1) ==>
   get_file_content ((add_stdo 1 "stdout") fs out) fd = get_file_content
     fs fd`,
  CHEAT_TAC);;

let get_mode_add_stdo = prove
 (`get_mode (add_stdo fd nm fs x) fd' = get_mode fs fd'`,
  CHEAT_TAC);;
add_simp get_mode_add_stdo;;

let get_mode_bumpFD = prove
 (`get_mode (bumpFD fd fs n) fd' = get_mode fs fd'`,
  CHEAT_TAC);;
add_simp get_mode_bumpFD;;

let linesFD_add_stdout = prove
 (`STD_streams fs /\ ~(fd = 1) ==>
   linesFD ((add_stdo 1 "stdout") fs out) fd = linesFD fs fd`,
  CHEAT_TAC);;

let get_file_content_add_stderr = prove
 (`STD_streams fs /\ ~(fd = 2) ==>
   get_file_content ((add_stdo 2 "stderr") fs err) fd = get_file_content
     fs fd`,
  CHEAT_TAC);;

let linesFD_add_stderr = prove
 (`STD_streams fs /\ ~(fd = 2) ==>
   linesFD ((add_stdo 2 "stderr") fs err) fd = linesFD fs fd`,
  CHEAT_TAC);;

let up_stdo_forwardFD = prove
 (`~(fd = fd') ==> up_stdo fd' (forwardFD fs fd n) out = forwardFD (up_stdo
  fd' fs out) fd n`,
  CHEAT_TAC);;

let up_stdout_fastForwardFD = prove
 (`STD_streams fs ==>
   (up_stdo 1) (fastForwardFD fs fd) out = fastForwardFD ((up_stdo 1) fs
     out) fd`,
  CHEAT_TAC);;

let up_stderr_fastForwardFD = prove
 (`STD_streams fs ==>
   (up_stdo 2) (fastForwardFD fs fd) out = fastForwardFD ((up_stdo 2) fs
     out) fd`,
  CHEAT_TAC);;

let stdo_forwardFD = prove
 (`~(fd = fd') ==> (stdo fd' nm (forwardFD fs fd n) out <=> stdo fd' nm fs
  out)`,
  CHEAT_TAC);;

let stdo_fastForwardFD = prove
 (`~(fd = fd') ==> (stdo fd' nm (fastForwardFD fs fd) out <=> stdo fd' nm fs
  out)`,
  CHEAT_TAC);;

let add_stdo_forwardFD = prove
 (`~(fd = fd') ==> add_stdo fd' nm (forwardFD fs fd n) out = forwardFD
  (add_stdo fd' nm fs out) fd n`,
  CHEAT_TAC);;

let add_stdout_lineForwardFD = prove
 (`STD_streams fs /\ ~(fd = 1) ==>
   (add_stdo 1 "stdout") (TextIOProof_lineForwardFD fs fd) out =
     TextIOProof_lineForwardFD ((add_stdo 1 "stdout") fs out) fd`,
  CHEAT_TAC);;

let add_stdout_fastForwardFD = prove
 (`STD_streams fs /\ ~(fd = 1) ==>
   (add_stdo 1 "stdout") (fastForwardFD fs fd) out = fastForwardFD
     ((add_stdo 1 "stdout") fs out) fd`,
  CHEAT_TAC);;

let add_stderr_lineForwardFD = prove
 (`STD_streams fs /\ ~(fd = 2) ==>
   (add_stdo 2 "stderr") (TextIOProof_lineForwardFD fs fd) out =
     TextIOProof_lineForwardFD ((add_stdo 2 "stderr") fs out) fd`,
  CHEAT_TAC);;

let add_stderr_fastForwardFD = prove
 (`STD_streams fs /\ ~(fd = 2) ==>
   (add_stdo 2 "stderr") (fastForwardFD fs fd) out = fastForwardFD
     ((add_stdo 2 "stderr") fs out) fd`,
  CHEAT_TAC);;

let FILTER_File_add_stdo = prove
 (`stdo fd nm fs init ==>
   FILTER ((\inode. ?fnm. inode = File fnm) o FST) (IO_fs_inode_tbl
     (add_stdo fd nm fs out)) = FILTER ((\inode. ?fnm. inode = File fnm) o
     FST) (IO_fs_inode_tbl fs)`,
  CHEAT_TAC);;

let FILTER_File_add_stdout = prove
 (`STD_streams fs ==>
   FILTER ((\inode. ?fnm. inode = File fnm) o FST) (IO_fs_inode_tbl
     ((add_stdo 1 "stdout") fs out)) = FILTER ((\inode. ?fnm. inode = File
     fnm) o FST) (IO_fs_inode_tbl fs)`,
  CHEAT_TAC);;

let FILTER_File_add_stderr = prove
 (`STD_streams fs ==>
   FILTER ((\inode. ?fnm. inode = File fnm) o FST) (IO_fs_inode_tbl
     ((add_stdo 2 "stderr") fs out)) = FILTER ((\inode. ?fnm. inode = File
     fnm) o FST) (IO_fs_inode_tbl fs)`,
  CHEAT_TAC);;

(* Note: more general versions of the following 4 theorems
  can be proved for stdo, but requires
  assumption to ensure that the file descriptors do not overlap *)
let stdout_add_stderr = prove
 (`STD_streams fs /\ (stdo 1 "stdout") fs out ==>
   (stdo 1 "stdout") ((add_stdo 2 "stderr") fs err) out`,
  CHEAT_TAC);;

let stderr_add_stdout = prove
 (`STD_streams fs /\ (stdo 2 "stderr") fs err ==>
   (stdo 2 "stderr") ((add_stdo 1 "stdout") fs out) err`,
  CHEAT_TAC);;

let add_stdout_inj = prove
 (`(add_stdo 1 "stdout") fs1 out1 = (add_stdo 1 "stdout") fs2 out2 /\
   (stdo 1 "stdout") fs1 out /\ (stdo 1 "stdout") fs2 out ==>
   out1 = out2`,
  CHEAT_TAC);;

let add_stderr_inj = prove
 (`(add_stdo 2 "stderr") fs1 err1 = (add_stdo 2 "stderr") fs2 err2 /\
   (stdo 2 "stderr") fs1 err /\ (stdo 2 "stderr") fs2 err ==>
   err1 = err2`,
  CHEAT_TAC);;

let stdin_def,stdin_ind = define_guess
  `stdin fs inp pos = (ALOOKUP (IO_fs_infds fs) 0 = SOME (UStream (implode
  "stdin"),ReadMode,pos) /\
                      ALOOKUP (IO_fs_inode_tbl fs) (UStream (implode
                        "stdin")) = SOME inp)`;;

let up_stdin_def = new_definition
  `up_stdin inp pos fs = fsupdate fs 0 0 pos inp`;;

let get_stdin_def = new_definition
  `get_stdin fs = let (inp,pos) = (@(inp,pos). stdin fs inp pos) in DROP pos
  inp`;;

let stdin_11 = prove
 (`stdin fs i1 p1 /\ stdin fs i2 p2 ==> i1 = i2 /\ p1 = p2`,
  CHEAT_TAC);;

let stdin_get_file_content = prove
 (`stdin fs inp pos ==> get_file_content fs 0 = SOME (inp,pos)`,
  CHEAT_TAC);;

let stdin_forwardFD = prove
 (`stdin fs inp pos ==>
   stdin (forwardFD fs fd n) inp (if fd = 0 then pos + n else pos)`,
  CHEAT_TAC);;

let stdin_get_stdin = prove
 (`stdin fs inp pos ==> get_stdin fs = DROP pos inp`,
  CHEAT_TAC);;

let get_stdin_forwardFD = prove
 (`stdin fs inp pos ==>
   get_stdin (forwardFD fs fd n) =
   (if fd = 0 then
     DROP n (get_stdin fs)
   else get_stdin fs)`,
  CHEAT_TAC);;

let linesFD_splitlines_get_stdin = prove
 (`stdin fs inp pos ==>
    MAP (\l. APPEND l "\n") (splitlines (get_stdin fs)) = linesFD fs 0`,
  CHEAT_TAC);;

(* file descriptors are encoded on 8 bytes *)
let FD_def = new_definition
  `FD fd' fdv = (STRING_TYPE (implode (MAP (CHR o w2n) (n2w8 fd'))) fdv
  /\ fd' < 256 EXP 8)`;;

let INSTREAM_def = new_definition
  `INSTREAM fd' fdv <=>
     INSTREAM_TYPE (Instream (implode (MAP (CHR o w2n) (n2w8 fd')))) fdv /\
     fd' < 256 EXP 8`;;

let OUTSTREAM_def = new_definition
  `OUTSTREAM fd' fdv <=>
     OUTSTREAM_TYPE (Outstream (implode (MAP (CHR o w2n) (n2w8 fd')))) fdv
       /\
     fd' < 256 EXP 8`;;

let INSTREAM_stdin = prove
 (`INSTREAM 0 raw_stdin_v`,
  CHEAT_TAC);;

let OUTSTREAM_stdout = prove
 (`OUTSTREAM 1 stdout_v`,
  CHEAT_TAC);;

let OUTSTREAM_stderr = prove
 (`OUTSTREAM 2 stderr_v`,
  CHEAT_TAC);;

let REF_NUM_def = new_definition
  `REF_NUM loc n =
     SEP_EXISTS (\v. REF loc v * &(NUM n v))`;;

let instream_buffered_inv_def = new_definition
  `instream_buffered_inv r w bcontent bactive =
       (1028 <= LENGTH bcontent /\
        LENGTH bcontent < 256 EXP 2 /\
       4 <= w /\
       4 <= r /\
       r <= LENGTH bcontent /\
       w <= LENGTH bcontent /\
       r <= w /\
       LENGTH bactive = w - r /\
       LENGTH bactive < LENGTH bcontent /\
       bactive = TAKE (w - r) (DROP r bcontent))`;;
      (*(bactive = [] <=> r = w))*)

let instream_buffered_inv_alt = prove
 (`instream_buffered_inv r w bcontent bactive =
     (?old unused.
       bcontent = APPEND (APPEND old bactive) unused /\
       1028 <= LENGTH bcontent /\
       LENGTH bcontent < 256 EXP 2 /\
       4 <= LENGTH old /\
       LENGTH (APPEND old bactive) = w /\
       LENGTH old = r)`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:960: the overload TypeStamp_InstreamBuffered,
   which the port expands *)

let INSTREAM_BUFFERED_def = new_definition
  `INSTREAM_BUFFERED bactive is =
     SEP_EXISTS (\rr r wr w buff bcontent fd' fdv.
       &(is = (semanticPrimitives_Conv instreambuffered_con_stamp [fdv; rr;
         wr; buff]) /\
         INSTREAM fd' fdv /\
         instream_buffered_inv r w bcontent bactive) *
       REF_NUM rr r *
       REF_NUM wr w *
       W8ARRAY buff bcontent)`;;

let INSTREAM_BUFFERED_FD_def = new_definition
  `INSTREAM_BUFFERED_FD bactive fd' is =
     SEP_EXISTS (\rr r wr w buff bcontent fdv.
       &(is = (semanticPrimitives_Conv instreambuffered_con_stamp [fdv; rr;
         wr; buff]) /\
         INSTREAM fd' fdv /\
         instream_buffered_inv r w bcontent bactive) *
       REF_NUM rr r *
       REF_NUM wr w *
       W8ARRAY buff bcontent)`;;

let INSTREAM_BUFFERED_BL_FD_def = new_definition
  `INSTREAM_BUFFERED_BL_FD bcontent bactive fd' is =
     SEP_EXISTS (\rr r wr w buff fdv.
       &(is = (semanticPrimitives_Conv instreambuffered_con_stamp [fdv; rr;
         wr; buff]) /\
         INSTREAM fd' fdv /\
         instream_buffered_inv r w bcontent bactive) *
       REF_NUM rr r *
       REF_NUM wr w *
       W8ARRAY buff bcontent)`;;

let INSTREAM_BUFFERED_BL_FD_RW_def = new_definition
  `INSTREAM_BUFFERED_BL_FD_RW bcontent bactive fd' r w is =
     SEP_EXISTS (\rr wr buff fdv.
       &(is = (semanticPrimitives_Conv instreambuffered_con_stamp [fdv; rr;
         wr; buff]) /\
         INSTREAM fd' fdv /\
         instream_buffered_inv r w bcontent bactive) *
       REF_NUM rr r *
       REF_NUM wr w *
       W8ARRAY buff bcontent)`;;
(* -- *)

let raw_openIn_spec = prove
 (`!s sv fs.
     FILENAME s sv /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
       (IO_fs_maxFD fs) (256 EXP 8) ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_raw_openIn_v [sv]
       (IOFS fs)
       (POSTve
          (\fdv. &(INSTREAM (nextFD fs) fdv /\
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) /\
                  inFS_fname fs s) *
                IOFS (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e /\ ~(inFS_fname fs s)) * IOFS fs))`,
  CHEAT_TAC);;

(* STDIO version *)
let raw_openIn_STDIO_spec = prove
 (`!s sv fs.
     FILENAME s sv /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
       (IO_fs_maxFD fs) (256 EXP 8) ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_raw_openIn_v [sv]
       (STDIO fs)
       (POSTve
          (\fdv. &(INSTREAM (nextFD fs) fdv /\
                  validFD (nextFD fs) (openFileFS s fs ReadMode 0) /\
                  inFS_fname fs s) *
                STDIO (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e /\ ~(inFS_fname fs s)) * STDIO fs))`,
  CHEAT_TAC);;

(* openOut, openAppend here *)

let raw_closeIn_spec = prove
 (`!fdw fdv fs.
     INSTREAM fdw fdv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_raw_closeIn_v [fdv]
       (IOFS fs)
       (POSTve
          (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fdw (IO_fs_infds
            fs)) *
               IOFS (IO_fs_infds_fupd (ADELKEY fdw) fs))
          (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fdw
            (IO_fs_infds fs))) * IOFS fs))`,
  CHEAT_TAC);;

let closeOut_spec = prove
 (`!fdw fdv fs.
     OUTSTREAM fdw fdv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_closeOut_v [fdv]
       (IOFS fs)
       (POSTve
         (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fdw (IO_fs_infds
           fs)) *
              IOFS (IO_fs_infds_fupd (ADELKEY fdw) fs))
         (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fdw
           (IO_fs_infds fs))) * IOFS fs))`,
  CHEAT_TAC);;

let raw_closeIn_STDIO_spec = prove
 (`!fd' fs fdv.
     INSTREAM fd' fdv /\ fd' >= 3 /\ fd' <= IO_fs_maxFD fs ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_raw_closeIn_v [fdv]
       (STDIO fs)
       (POSTve
          (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fd' (IO_fs_infds
            fs)) *
               STDIO (IO_fs_infds_fupd (ADELKEY fd') fs))
          (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fd'
            (IO_fs_infds fs))) * STDIO fs))`,
  CHEAT_TAC);;

let closeOut_STDIO_spec = prove
 (`!fd' fs fdv.
     OUTSTREAM fd' fdv /\ fd' >= 3 /\ fd' <= IO_fs_maxFD fs ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_closeOut_v [fdv]
       (STDIO fs)
       (POSTve
          (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fd' (IO_fs_infds
            fs)) *
               STDIO (IO_fs_infds_fupd (ADELKEY fd') fs))
          (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fd'
            (IO_fs_infds fs))) * STDIO fs))`,
  CHEAT_TAC);;

let writei_spec = prove
 (`wfFS fs ==> 0 < n ==>
    MAX (i + n) 2048 <= LENGTH rest ==> i + n < 256 EXP 2 ==>
   get_file_content fs fd = SOME (content,pos) ==>
   get_mode fs fd = SOME WriteMode ==>
   FD fd fdv ==> NUM n nv ==> NUM i iv ==>
   bc = CONS h1 (CONS h2 (CONS h3 (CONS h4 rest))) ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_writei_v [fdv; nv; iv]
   (IOx fs_ffi_part fs * W8ARRAY iobuff_loc bc)
   (POSTve
     (\nwv. SEP_EXISTS (\nw. &(NUM nw nwv) * &(nw > 0) * &(nw <= n) *
            W8ARRAY iobuff_loc (APPEND (CONS (n2w 0) (n2w2 nw)) (CONS (n2w
              i) rest)) *
            IOx fs_ffi_part
                (fsupdate fs fd (1 + Lnext_pos (IO_fs_numchars fs)) (pos +
                  nw)
                   (insert_atI (TAKE nw (MAP (CHR o w2n) (DROP i rest))) pos
                              content))))
     (\e. &(InvalidFD_exn e) * W8ARRAY iobuff_loc (APPEND (CONS (n2w 1)
       (CONS (n2w n) (n2w2 i))) rest) * &(F) *
          IOFS (IO_fs_numchars_fupd (K (THE (LDROP (1 + Lnext_pos
            (IO_fs_numchars fs)) (IO_fs_numchars fs)))) fs)))`,
  CHEAT_TAC);;

let write_spec = prove
 (`!n fs fd' i pos h1 h2 h3 h4 rest bc fdv nv iv content.
   wfFS fs ==> MAX (i + n) 2048 <= LENGTH rest ==> i + n < 256 EXP 2 ==>
   get_file_content fs fd' = SOME (content,pos) ==>
   get_mode fs fd' = SOME WriteMode ==>
   FD fd' fdv ==> NUM n nv ==> NUM i iv ==>
   bc = CONS h1 (CONS h2 (CONS h3 (CONS h4 rest))) ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_write_v [fdv; nv; iv]
   (IOx fs_ffi_part fs * W8ARRAY iobuff_loc bc)
   (POSTv (?_SEP_EXISTS nwv) (?_IOFS k) (fsupdate fs fd' k (pos + n)
                    (insert_atI (TAKE n (MAP (CHR o w2n) (DROP i rest))) pos
                              content)))`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:1459-1486: a theorem whose statement the port
   cannot state yet: output1_spec *)

(* HOL4 TextIOProofScript.sml:1488-1515: a theorem whose statement the port
   cannot state yet: output1_STDIO_spec *)

(* HOL4 TextIOProofScript.sml:1517-1530: a theorem whose statement the port
   cannot state yet: output1_stdOut_spec *)

(* HOL4 TextIOProofScript.sml:1532-1543: a proof *)

(* HOL4 TextIOProofScript.sml:1545-1555: a theorem whose statement the port
   cannot state yet: output1_stdout_spec *)

(* HOL4 TextIOProofScript.sml:1557-1567: a theorem whose statement the port
   cannot state yet: output1_stderr_spec *)

(* TODO Move? *)
(* [local] *)
let SEG_APPEND3 = prove
 (`!len off z l.
     len + off <= z /\ z <= LENGTH l ==> APPEND (SEG len off l) (SEG (z -
       (off + len)) (off + len) l) = SEG (z - off) off l`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:1581-1666: a theorem whose statement the port
   cannot state yet: output_aux_spec *)

(* HOL4 TextIOProofScript.sml:1668-1687: a theorem whose statement the port
   cannot state yet: output_spec *)

(* HOL4 TextIOProofScript.sml:1689-1717: a theorem whose statement the port
   cannot state yet: output_STDIO_spec *)

(* HOL4 TextIOProofScript.sml:1719-1731: a theorem whose statement the port
   cannot state yet: print_spec *)

let print_def = new_definition
  `print s = (\fs. (M_success one,(add_stdo 1 "stdout") fs s))`;;

let EvalM_print = prove
 (`ast_Eval env exp (STRING_TYPE x) /\
   (nsLookup (sem_env_v env) (Short (implode "print")) = SOME
     TextIO_print_v) ==>
    EvalM F env st (ast_App ast_Opapp [ast_Var (Short (implode "print"));
      exp])
      (MONAD UNIT_TYPE exc_ty (print x))
      (MONAD_IO,(p:('ffi->(mlstring,ffi)fmap)#(mlstring
        list#(mlstring->word8 list->word8 list->ffi->(ffi
        cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:1752-1763: a theorem whose statement the port
   cannot state yet: output_stderr_spec *)

(* HOL4 TextIOProofScript.sml:1765-1776: a theorem whose statement the port
   cannot state yet: print_err_spec *)

let print_err_def = new_definition
  `print_err s = (\fs. (M_success one,(add_stdo 2 "stderr") fs s))`;;

let EvalM_print_err = prove
 (`ast_Eval env exp (STRING_TYPE x) /\
    (nsLookup (sem_env_v env) (Long (implode "TextIO") (Short (implode
      "print_err"))) =
      SOME TextIO_print_err_v) ==>
    EvalM F env st (ast_App ast_Opapp [ast_Var (Long (implode "TextIO")
      (Short (implode "print_err"))); exp])
      (MONAD UNIT_TYPE exc_ty (print_err x))
      (MONAD_IO,(p:('ffi->(mlstring,ffi)fmap)#(mlstring
        list#(mlstring->word8 list->word8 list->ffi->(ffi
        cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let read_spec = prove
 (`!fs fd' fdv n nv. wfFS fs ==> FD fd' fdv ==> NUM n nv ==>
    n < 256 EXP 2 ==> MAX n 2048 <= LENGTH rest ==>
    app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
      TextIO_read_v [fdv; nv]
    (W8ARRAY iobuff_loc (CONS h1 (CONS h2 (CONS h3 (CONS h4 rest)))) * IOx
      fs_ffi_part fs)
    (POSTve
      (\nrv. SEP_EXISTS (\(nr:num).
       &(NUM nr nrv) *
       SEP_EXISTS (\content pos.
         &(get_file_content fs fd' = SOME (content,pos) /\
           get_mode fs fd' = SOME ReadMode /\
           (nr <= MIN n (LENGTH content - pos)) /\
           (nr = 0 <=> eof fd' fs = SOME T \/ n = 0)) *
       IOx fs_ffi_part (bumpFD fd' fs nr) *
       W8ARRAY iobuff_loc (APPEND (CONS (n2w 0) (CONS (n2w (nr DIV 256))
         (CONS (n2w nr) (CONS h4
         (MAP (n2w o ORD) (TAKE nr (DROP pos content))))))) (DROP nr
           rest)))))
      (\e. &(InvalidFD_exn e) * &(get_file_content fs fd' = NONE \/
        ~(get_mode fs fd' = SOME ReadMode)) * IOFS fs))`,
  CHEAT_TAC);;

let read_into_spec = prove
 (`!fs fd' fdv n nv buf. wfFS fs ==> FD fd' fdv ==> NUM n nv ==>
    n < 256 EXP 2 ==> MAX n 1024 <= LENGTH rest ==>
    app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
      TextIO_read_into_v [fdv; buf; nv]
    (W8ARRAY buf (CONS h1 (CONS h2 (CONS h3 (CONS h4 rest)))) * IOx
      fs_ffi_part fs)
    (POSTve
      (\nrv. SEP_EXISTS (\(nr:num).
       &(NUM nr nrv) *
       SEP_EXISTS (\content pos.
         &(get_file_content fs fd' = SOME (content,pos) /\
           get_mode fs fd' = SOME ReadMode /\
           (nr <= MIN n (LENGTH content - pos) /\
            nr <= LENGTH content - pos) /\
           (nr = 0 <=> eof fd' fs = SOME T \/ n = 0)) *
       IOx fs_ffi_part (bumpFD fd' fs nr) *
       W8ARRAY buf (APPEND (CONS (n2w 0) (CONS (n2w (nr DIV 256)) (CONS (n2w
         nr) (CONS h4
         (MAP (n2w o ORD) (TAKE nr (DROP pos content))))))) (DROP nr
           rest)))))
      (\e. &(InvalidFD_exn e) * &(get_file_content fs fd' = NONE \/
        ~(get_mode fs fd' = SOME ReadMode)) * IOFS_WO_iobuff fs))`,
  CHEAT_TAC);;

(* TODO: call the low-level IOFS specs with the non-standard name, not vice versa *)

(* HOL4 TextIOProofScript.sml:2026-2225: a theorem whose statement the port
   cannot state yet: raw_input_IOFS_spec *)

(* HOL4 TextIOProofScript.sml:2227-2263: a theorem whose statement the port
   cannot state yet: raw_input_spec *)

let take_drop_append = prove
 (`x < LENGTH l /\ y < LENGTH l /\ z < LENGTH l /\ ~(y < x) ==> APPEND (TAKE x
  (DROP z l)) (TAKE (y - x) (DROP (x + z) l)) =
    TAKE y (DROP z l)`,
  CHEAT_TAC);;

let openStdInSetBufferSize_spec = prove
 (`!fs bsize bsizev bactive.
      NUM bsize bsizev ==>
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
        TextIO_openStdInSetBufferSize_v [bsizev]
        (IOFS fs)
        (POSTv (?_INSTREAM_BUFFERED_FD is) [] 0 is * IOFS fs)`,
  CHEAT_TAC);;

let openStdIn_spec = prove
 (`!fs uv.
     UNIT_TYPE one uv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_openStdIn_v [uv]
        (IOFS fs)
        (POSTv (?_INSTREAM_BUFFERED_FD is) [] 0 is * IOFS fs)`,
  CHEAT_TAC);;

(* STDIO version *)
let openStdIn_STDIO_spec = prove
 (`!uv fs.
     UNIT_TYPE one uv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_openStdIn_v [uv]
       (STDIO fs)
       (POSTv (?_INSTREAM_BUFFERED_FD is) [] 0 is * STDIO fs)`,
  CHEAT_TAC);;

let openInSetBufferSize_spec = prove
 (`!s sv fs bsize bsizev bactive.
      FILENAME s sv /\
      NUM bsize bsizev /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) <
        MIN (IO_fs_maxFD fs) (256 EXP 8) ==>
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
        TextIO_openInSetBufferSize_v [sv; bsizev]
        (IOFS fs)
        (POSTve
           (\is. &(
                   validFD (nextFD fs) (openFileFS s fs ReadMode 0) /\
                   inFS_fname fs s) *
                 INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                 IOFS (openFileFS s fs ReadMode 0))
           (\e.
                    &(BadFileName_exn e /\ ~(inFS_fname fs s)) * IOFS fs))`,
  CHEAT_TAC);;

let openIn_spec = prove
 (`!s sv fs.
      FILENAME s sv /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
        (IO_fs_maxFD fs) (256 EXP 8) ==>
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
        TextIO_openIn_v [sv]
        (IOFS fs)
        (POSTve
           (\is. &(
                   validFD (nextFD fs) (openFileFS s fs ReadMode 0) /\
                   inFS_fname fs s) *
                 INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                 IOFS (openFileFS s fs ReadMode 0))
           (\e.
                    &(BadFileName_exn e /\ ~(inFS_fname fs s)) * IOFS fs))`,
  CHEAT_TAC);;

(* STDIO version *)
let openIn_STDIO_spec = prove
 (`!s sv fs.
     FILENAME s sv /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
       (IO_fs_maxFD fs) (256 EXP 8) ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_openIn_v [sv]
       (STDIO fs)
       (POSTve
          (\is. &(validFD (nextFD fs) (openFileFS s fs ReadMode 0) /\
                  inFS_fname fs s) *
                INSTREAM_BUFFERED_FD [] (nextFD fs) is *
                STDIO (openFileFS s fs ReadMode 0))
          (\e. &(BadFileName_exn e /\ ~(inFS_fname fs s)) * STDIO fs))`,
  CHEAT_TAC);;

let closeIn_spec = prove
 (`!fd' fs.
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_closeIn_v [is]
       (IOFS fs * INSTREAM_BUFFERED_FD bactive fd' is)
       (POSTve
          (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fd' (IO_fs_infds
            fs)) *
               IOFS (IO_fs_infds_fupd (ADELKEY fd') fs))
          (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fd'
            (IO_fs_infds fs))) * IOFS fs))`,
  CHEAT_TAC);;

let closeIn_STDIO_spec = prove
 (`!fd' fs.
     fd' >= 3 /\ fd' <= IO_fs_maxFD fs ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_closeIn_v [is]
       (STDIO fs * INSTREAM_BUFFERED_FD bactive fd' is)
       (POSTve
          (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fd' (IO_fs_infds
            fs)) *
               STDIO (IO_fs_infds_fupd (ADELKEY fd') fs))
          (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fd'
            (IO_fs_infds fs))) * STDIO fs))`,
  CHEAT_TAC);;

let take_fromI_def = new_definition
  `take_fromI n l i = TAKE n (DROP i l)`;;

let LENGTH_take_fromI = prove
 (`(n <= LENGTH l - i ==> LENGTH (take_fromI n l i) = n) /\
   (LENGTH l - i <= n ==> LENGTH (take_fromI n l i) = LENGTH l - i)`,
  CHEAT_TAC);;

let explode_fromI_def = new_definition
  `explode_fromI n (content:string) pos =
       (take_fromI n (MAP (n2w o ORD) content) pos:word8 list)`;;

let LENGTH_explode_fromI = prove
 (`(n <= LENGTH l - i ==> LENGTH (explode_fromI n l i) = n) /\
   (LENGTH l - i <= n ==> LENGTH (explode_fromI n l i) = LENGTH l - i)`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:2468-2539: a theorem whose statement the port
   cannot state yet: refillBuffer_with_read_spec *)

(* HOL4 TextIOProofScript.sml:2541-2542: ML code, not ported *)

(* HOL4 TextIOProofScript.sml:2544-2546: ML code, not ported *)

(* HOL4 TextIOProofScript.sml:2548-2616: a theorem whose statement the port
   cannot state yet: input1_aux_spec *)

(* HOL4 TextIOProofScript.sml:2618-2678: a theorem whose statement the port
   cannot state yet: peekChar_aux_spec *)

(* DROP_TAKE *)
let TextIOProof_DROP_TAKE = prove
 (`!xs k n. DROP k (TAKE n xs) = TAKE (n - k) (DROP k xs)`,
  CHEAT_TAC);;

let TAKE_DROP_EQ_CONS_IMP = prove
 (`!n pos xs y ys.
     TAKE n (DROP pos xs) = CONS y ys ==>
     TAKE (n - 1) (DROP (pos + 1) xs) = ys`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:2699-2820: a theorem whose statement the port
   cannot state yet: input1_IOFS_spec *)

(* HOL4 TextIOProofScript.sml:2822-2941: a theorem whose statement the port
   cannot state yet: peekChar_IOFS_spec *)

(* HOL4 TextIOProofScript.sml:2943-2994: a theorem whose statement the port
   cannot state yet: input1_spec *)

(* HOL4 TextIOProofScript.sml:2996-3047: a theorem whose statement the port
   cannot state yet: peekChar_spec *)

let takeUntilIncl_def,takeUntilIncl_ind = define_guess
  `(takeUntilIncl p [] = []) /\
   (takeUntilIncl p (CONS x xs) = if p x then [x] else (CONS x
    (takeUntilIncl p xs)))`;;

let dropUntilIncl_def = new_definition
  `dropUntilIncl p l = DROP 1 (dropUntil p l)`;;

let dropUntil_drop_drop = prove
 (`!P l x.
       ALL ((~) o P) (TAKE x l) ==>
         dropUntil P l = dropUntil P (DROP x l)`,
  CHEAT_TAC);;

let dropUntilIncl_drop_drop = prove
 (`!P l x.
       ALL ((~) o P) (TAKE x l) ==>
         dropUntilIncl P l = dropUntilIncl P (DROP x l)`,
  CHEAT_TAC);;

let takeUntil_length_cons = prove
 (`!P l x.
       ((~) o P) h ==>
         LENGTH (takeUntil P (CONS h t)) = SUC (LENGTH (takeUntil P t))`,
  CHEAT_TAC);;

let takeUntilIncl_length_cons = prove
 (`!P l x.
       ((~) o P) h ==>
         LENGTH (takeUntilIncl P (CONS h t)) = SUC (LENGTH (takeUntilIncl
           P t))`,
  CHEAT_TAC);;

let takeUntil_cons = prove
 (`!P l x.
       ((~) o P) h ==>
         takeUntil P (CONS h t) = CONS h (takeUntil P t)`,
  CHEAT_TAC);;

let takeUntilIncl_cons = prove
 (`!P l x.
       ((~) o P) h ==>
         takeUntilIncl P (CONS h t) = CONS h (takeUntilIncl P t)`,
  CHEAT_TAC);;

let takeUntil_length_drop = prove
 (`!P l x.
       ALL ((~) o P) (TAKE x l) ==>
         LENGTH (takeUntil P l) = LENGTH (TAKE x l) + LENGTH (takeUntil P
           (DROP x l))`,
  CHEAT_TAC);;

let takeUntilIncl_length_drop = prove
 (`!P l x.
       ALL ((~) o P) (TAKE x l) ==>
         LENGTH (takeUntilIncl P l) = LENGTH (TAKE x l) + LENGTH
           (takeUntilIncl P (DROP x l))`,
  CHEAT_TAC);;

let takeUntil_drop = prove
 (`!P l x.
       ALL ((~) o P) (TAKE x l) ==>
         takeUntil P l = APPEND (TAKE x l) (takeUntil P (DROP x l))`,
  CHEAT_TAC);;

let takeUntilIncl_drop = prove
 (`!P l x.
       ALL ((~) o P) (TAKE x l) ==>
         takeUntilIncl P l = APPEND (TAKE x l) (takeUntilIncl P (DROP x
           l))`,
  CHEAT_TAC);;

let takeUntil_exists_in_prefix = prove
 (`!P l x.
       EX P (TAKE x l) ==>
         takeUntil P l = takeUntil P (TAKE x l)`,
  CHEAT_TAC);;

let takeUntilIncl_exists_in_prefix = prove
 (`!P l x.
       EX P (TAKE x l) ==>
         takeUntilIncl P l = takeUntilIncl P (TAKE x l)`,
  CHEAT_TAC);;

let dropUntil_take_isPrefix = prove
 (`!P l x.
       dropUntil P (TAKE x l) <<= dropUntil P l`,
  CHEAT_TAC);;

let dropUntilIncl_take_isPrefix = prove
 (`!P l x.
       dropUntilIncl P (TAKE x l) <<= dropUntilIncl P l`,
  CHEAT_TAC);;

let dropUntil_length_gt_0 = prove
 (`!P l x.
       EX P l ==>
         0 < LENGTH (dropUntil P l)`,
  CHEAT_TAC);;

let LENGTH_dropUntil_takeUntil = prove
 (`!P l x.
       EX P l ==>
         LENGTH l = LENGTH (dropUntil P l) + LENGTH (takeUntil P l)`,
  CHEAT_TAC);;

let LENGTH_takeUntil_takeUntilIncl = prove
 (`!P l.
       EX P l ==>
         SUC (LENGTH (takeUntil P l)) = LENGTH (takeUntilIncl P l)`,
  CHEAT_TAC);;


let LENGTH_dropUntil_takeUntilIncl = prove
 (`!P l x.
       EX P l ==>
         LENGTH l = (LENGTH (dropUntil P l) + LENGTH (takeUntilIncl P l))
           - 1`,
  CHEAT_TAC);;

let LENGTH_dropUntil_leq = prove
 (`!P l.
     LENGTH (dropUntil P l) <= LENGTH l`,
  CHEAT_TAC);;

let LENGTH_takeUntil_exists = prove
 (`!P l.
       EX P l <=>
         LENGTH (takeUntil P l) < LENGTH l`,
  CHEAT_TAC);;

let takeUntil_not_exists = prove
 (`!P l.
       ~(EX P l) <=>
         takeUntil P l = l`,
  CHEAT_TAC);;

let LENGTH_takeUntilIncl_exists_geq_1 = prove
 (`!P l.
       EX P l ==>
         1 <= LENGTH (takeUntilIncl P l)`,
  CHEAT_TAC);;

let takeUntilIncl_not_exists = prove
 (`!P l.
       ~(EX P l) ==>
          takeUntilIncl P l = l`,
  CHEAT_TAC);;

let dropUntilIncl_not_exists = prove
 (`!P l.
       ~(EX P l) ==>
         dropUntilIncl P l = []`,
  CHEAT_TAC);;

let LENGTH_dropUntilIncl = prove
 (`!P l.
       (EX P l ==>
         LENGTH (dropUntilIncl P l) < LENGTH l) /\
       (~(EX P l) ==>
         LENGTH (dropUntilIncl P l) = 0) /\
       (LENGTH (dropUntilIncl P l) <= LENGTH l)`,
  CHEAT_TAC);;

let take_drop_eq_hd_cons = prove
 (`!t x y.
       y < LENGTH l ==>
         (CONS (HD (DROP y l)) (TAKE x (DROP (y + 1) l))) = TAKE (x + 1)
           (DROP y l)`,
  CHEAT_TAC);;

let chr_neq_ord_o_w8_neq = prove
 (`~(a = b) ==> ~((n2w:num->(word8 o) ORD) a = (n2w:num->(word8 o) ORD) b)`,
  CHEAT_TAC);;

let chr_eq_ord_o_w8_eq = prove
 (`a = b ==> (n2w:num->(word8 o) ORD) a = (n2w:num->(word8 o) ORD) b`,
  CHEAT_TAC);;

let takeUntilIncl_length_gt_0 = prove
 (`!P l x.
       EX P l ==>
         0 < LENGTH (takeUntilIncl P l)`,
  CHEAT_TAC);;

let takeUntilIncl_length_leq = prove
 (`!P l.
         LENGTH (takeUntilIncl P l) <= LENGTH l`,
  CHEAT_TAC);;

let takeUntilIncl_exists_last = prove
 (`!P l x.
       EX P l ==>
         P (LAST (takeUntilIncl P l))`,
  CHEAT_TAC);;


let exists_chr_isSuffix = prove
 (`!P l.
       EX ((=) c) l ==>
         (isSuffix (integer_word_toString c) (implode (takeUntilIncl ((=) c)
           l)) <=>
           ((=) c) (LAST (takeUntilIncl ((=) c) l)))`,
  CHEAT_TAC);;

let not_exists_chr_not_isSuffix = prove
 (`!l.
       0 < LENGTH l /\
       ~(EX ((=) c) l) ==>
         ~(isSuffix (integer_word_toString c) (implode l))`,
  CHEAT_TAC);;

let isSuffix_char_strlen_gt_0 = prove
 (`!P l.
         isSuffix (integer_word_toString (c:char)) (implode l) ==> 0 <
           LENGTH l`,
  CHEAT_TAC);;

let STRCAT_eq_MAP_n2w_o_ORD_append = prove
 (`APPEND l r = MAP (CHR o (w2n:word8->num)) (APPEND (MAP (n2w o ORD) l) (MAP
  (n2w o ORD) r))`,
  CHEAT_TAC);;

let EL_STRCAT = prove
 (`!l.
         EL (LENGTH r - 1) r = EL (LENGTH r - 1 + LENGTH l) (APPEND l r)`,
  CHEAT_TAC);;

let isSuffix_char_implode_strcat = prove
 (`!l r (c:char).
         0 < LENGTH r ==>
           (isSuffix (integer_word_toString c) (implode r) <=> isSuffix
             (integer_word_toString c) (implode (APPEND l r)))`,
  CHEAT_TAC);;

let exists_eq_o_map = prove
 (`!P l.
       EX ((=) ((n2w o ORD) x)) l <=>
         EX ((=) x) (MAP (CHR o w2n) (l:word8 list))`,
  CHEAT_TAC);;

let exists_eq_o_map2 = prove
 (`!P l.
     EX ((=) ((n2w o ORD) x)) (MAP (n2w:num->(word8 o) ORD) l) <=>
       EX ((=) x) (l:string)`,
  CHEAT_TAC);;

let map_w82c_takeUntilIncl_eq_takeUntilIncl_map_c2w8 = prove
 (`!P l.
       takeUntilIncl ((=) c) (MAP (CHR o w2n) (l:word8 list)) =
         MAP (CHR o (w2n:word8->num)) (takeUntilIncl ((=)
           ((n2w:num->(word8 o) ORD) c)) (l:word8 list))`,
  CHEAT_TAC);;

let map_w82c_takeUntilIncl_eq_takeUntilIncl_map_c2w8_2 = prove
 (`!P l.
       takeUntilIncl ((=) c) (l:string) =
         MAP (CHR o (w2n:word8->num))
           (takeUntilIncl ((=) ((n2w:num->(word8 o) ORD) c)) (MAP
             (n2w:num->(word8 o) ORD) l))`,
  CHEAT_TAC);;

let map_w82c_dropUntilIncl_eq_dropUntilIncl_map_c2w8 = prove
 (`!P l.
       dropUntilIncl ((=) c) (MAP (CHR o w2n) (l:word8 list)) =
         MAP (CHR o (w2n:word8->num)) (dropUntilIncl ((=)
           ((n2w:num->(word8 o) ORD) c)) (l:word8 list))`,
  CHEAT_TAC);;

let map_w82c_dropUntilIncl_eq_dropUntilIncl_map_c2w8_2 = prove
 (`!P l.
       dropUntilIncl ((=) c) (l:string) =
         MAP (CHR o (w2n:word8->num))
           (dropUntilIncl ((=) ((n2w:num->(word8 o) ORD) c)) (MAP
             (n2w:num->(word8 o) ORD) l))`,
  CHEAT_TAC);;

let takeUntilIncl_exists = prove
 (`!P l x.
       EX P l ==>
         EX P (takeUntilIncl P l)`,
  CHEAT_TAC);;

let takeUntilIncl_append_exists_l = prove
 (`!P l x.
       EX P l ==>
         takeUntilIncl P (APPEND l r) = takeUntilIncl P l`,
  CHEAT_TAC);;

let takeUntil_append_exists_l = prove
 (`!P l x.
       EX P l ==>
         takeUntil P (APPEND l r) = takeUntil P l`,
  CHEAT_TAC);;

let takeUntil_append_not_exists_l = prove
 (`!P l x.
       ~(EX P l) ==>
         takeUntil P (APPEND l r) = APPEND l (takeUntil P r)`,
  CHEAT_TAC);;

let takeUntilIncl_append_not_exists_l = prove
 (`!P l x.
       ~(EX P l) ==>
         takeUntilIncl P (APPEND l r) = APPEND l (takeUntilIncl P r)`,
  CHEAT_TAC);;

let dropUntilIncl_append_exists_l = prove
 (`!P l x.
       EX P l ==>
         dropUntilIncl P (APPEND l r) = APPEND (dropUntilIncl P l) r`,
  CHEAT_TAC);;

let dropUntilIncl_append_not_exists_l = prove
 (`!P l x.
       ~(EX P l) ==>
         dropUntilIncl P (APPEND l r) = dropUntilIncl P r`,
  CHEAT_TAC);;

let LENGTH_dropUntil_takeUntilIncl2 = prove
 (`!P l x.
       EX P l ==>
         SUC (LENGTH l) = LENGTH (dropUntil P l) + LENGTH (takeUntilIncl P
           l)`,
  CHEAT_TAC);;

let LENGTH_dropUntilIncl_takeUntilIncl = prove
 (`!P l.
     LENGTH l = LENGTH (dropUntilIncl P l) + LENGTH (takeUntilIncl P l)`,
  CHEAT_TAC);;

let LENGTH_dropUntilIncl_dropUntil = prove
 (`!P ls.
       LENGTH (dropUntilIncl P ls) = LENGTH (dropUntil P ls) - 1`,
  CHEAT_TAC);;

let TextIOProof_lineForwardFD_def = new_definition
  `TextIOProof_lineForwardFD buff fs fd' extra =
        match get_file_content fs fd' with
          NONE -> fs
        | SOME (content,pos') ->
          if EX ((=) ((n2w 10):word8)) buff then fs
           else if pos' < LENGTH content then
            (let
               (l,r) = SPLITP ((=) (CHR 10)) (DROP pos' content) in
               forwardFD fs fd' (LENGTH extra + LENGTH l + (if NULL r then 0
                 else 1)))
          else fs`;;

let takeLine_def = new_definition
  `takeLine s = takeUntilIncl ((=) (CHR 10)) s`;;

let dropLine_def = new_definition
  `dropLine s = dropUntilIncl ((=) (CHR 10)) s`;;

let inputLine_def = new_definition
  `inputLine s =
     implode (if EX ((=) (CHR 10)) s then takeLine s
              else APPEND s "\n")`;;

let gen_inputLine_def = new_definition
  `gen_inputLine c s =
     implode (if EX ((=) c) s then takeUntilIncl ((=) c) s
              else APPEND s [c])`;;

let SPLITP_takeUntil_dropUntil = prove
 (`!P ls.
     SPLITP P ls = (takeUntil P ls,dropUntil P ls)`,
  CHEAT_TAC);;

let LENGTH_dropUntil = prove
 (`!P ls.
     (EX P ls ==> 0 < LENGTH (dropUntil P ls)) /\
     (~(EX P ls) ==> LENGTH (dropUntil P ls) = 0) /\
     LENGTH (dropUntil P ls) <= LENGTH ls`,
  CHEAT_TAC);;

let LENGTH_takeUntilIncl_w8_takeUntilIncl_chr = prove
 (`!ls.
     LENGTH (takeUntilIncl ((=) ((n2w 10):word8)) (MAP (n2w o ORD) (DROP pos
       content))) =
       LENGTH (takeUntilIncl ((=) (CHR 10)) (DROP pos content))`,
  CHEAT_TAC);;

let takeLine_hd_not_newline = prove
 (`!h t. ~(h = (CHR 10)) ==>
         takeLine (CONS h t) = CONS h (takeLine t)`,
  CHEAT_TAC);;

let takeLine_hd_newline = prove
 (`!h t.
       h = (CHR 10) ==>
         takeLine (CONS h t) = CONS (CHR 10) ""`,
  CHEAT_TAC);;

let FIELDS_hd_newline = prove
 (`!t.
         FIELDS ((=) (CHR 10)) (CONS (CHR 10) t) = CONS "" (FIELDS ((=)
           (CHR 10)) t)`,
  CHEAT_TAC);;

let SPLITP_takeUntil = prove
 (`!l.
         SPLITP ((=) (CHR 10)) l =
           (takeUntil ((=) (CHR 10)) l,DROP (LENGTH (takeUntil ((=) (CHR
             10)) l)) l)`,
  CHEAT_TAC);;

let LENGTH_takeUntil = prove
 (`!P l.
       LENGTH (takeUntil P l) <= LENGTH l`,
  CHEAT_TAC);;

let FIELDS_takeUntil = prove
 (`!l.
       LENGTH (takeUntil ((=) (CHR 10)) l) < LENGTH l ==>
       FIELDS ((=) (CHR 10)) l = CONS (takeUntil ((=) (CHR 10)) l)
             (FIELDS ((=) (CHR 10)) (TL (DROP (LENGTH (takeUntil ((=) (CHR
               10)) l)) l)))`,
  CHEAT_TAC);;

let splitlines_hd_newline = prove
 (`!t.
         splitlines (CONS (CHR 10) t) = CONS "" (splitlines t)`,
  CHEAT_TAC);;

let splitlines_takeUntil_exists = prove
 (`!l.
         EX ((=) (CHR 10)) l ==>
         splitlines l =
           (CONS (takeUntil ((=) (CHR 10)) l)
             (splitlines (TL (DROP (LENGTH (takeUntil ((=) (CHR 10)) l))
               l))))`,
  CHEAT_TAC);;

let splitlines_takeUntil_exists2 = prove
 (`!l.
         EX ((=) (CHR 10)) l ==>
         splitlines l =
           (CONS (takeUntil ((=) (CHR 10)) l)
             (splitlines (DROP (SUC (LENGTH (takeUntil ((=) (CHR 10)) l)))
               l)))`,
  CHEAT_TAC);;

let splitlines_not_exists = prove
 (`!l.
         ~(EX ((=) (CHR 10)) l) /\
         ~(NULL l) ==>
         splitlines l = [l]`,
  CHEAT_TAC);;

let TL_APPEND = prove
 (`!l r.
        0 < LENGTH l ==>
        TL (APPEND l r) = (APPEND (TL l) r)`,
  CHEAT_TAC);;

let splitlines_append_exists_l = prove
 (`!l.
       EX ((=) (CHR 10)) (l:string) ==>
         splitlines (APPEND l r) =
           (CONS (takeUntil ((=) (CHR 10)) l)
             (splitlines (APPEND (TL (DROP (LENGTH (takeUntil ((=) (CHR
               10)) l)) l)) r)))`,
  CHEAT_TAC);;

let splitlines_append_exists_r = prove
 (`!l.
       ~(EX ((=) (CHR 10)) (l:string)) /\
       EX ((=) (CHR 10)) (r:string) ==>
         splitlines (APPEND l r) =
           (CONS (APPEND l (takeUntil ((=) (CHR 10)) r))
             (splitlines (TL (DROP (LENGTH (takeUntil ((=) (CHR 10)) r))
               r))))`,
  CHEAT_TAC);;

let splitlines_not_exists2 = prove
 (`!l.
         ~(EX ((=) (CHR 10)) l) ==>
         splitlines l = (if l = "" then [] else [l])`,
  CHEAT_TAC);;

let splitlines_append_not_exists_l = prove
 (`!l.
       ~(EX ((=) (CHR 10)) (l:string)) /\ ~(NULL (APPEND l r)) ==>
         splitlines (APPEND l r) =
           (CONS (APPEND l (takeUntil ((=) (CHR 10)) r))
             (splitlines (DROP (SUC (LENGTH (takeUntil ((=) (CHR 10)) r)))
               r)))`,
  CHEAT_TAC);;

let LENGTH_splitlines = prove
 (`!ls. (NULL (LAST (FIELDS ((=) (CHR 10)) ls)) ==>
     LENGTH (splitlines ls) = LENGTH (FILTER ((=) (CHR 10)) ls)) /\
      (~(NULL (LAST (FIELDS ((=) (CHR 10)) ls))) ==>
     LENGTH (splitlines ls) = LENGTH (FILTER ((=) (CHR 10)) ls) + 1)`,
  CHEAT_TAC);;

let FILTER_dropUntilIncl = prove
 (`!ls. (EX P ls ==> FILTER P (dropUntilIncl P ls) = TL (FILTER P ls)) /\
         (~(EX P ls) ==> FILTER P (dropUntilIncl P ls) = [])`,
  CHEAT_TAC);;

let isPREFIX_FILTER = prove
 (`!ls bs. ls <<= bs ==> FILTER P ls <<= FILTER P bs`,
  CHEAT_TAC);;

let LENGTH_FILTER_EXISTS = prove
 (`!ls.
     (EX P ls ==> 0 < LENGTH (FILTER P ls)) /\
     (~(EX P ls) ==> LENGTH (FILTER P ls) = 0)`,
  CHEAT_TAC);;

let LENGTH_isPREFIX = prove
 (`!ls bs. ls <<= bs ==> LENGTH ls <= LENGTH bs`,
  CHEAT_TAC);;

let isPREFIX_dropUntilIncl_LENGTH_FILTER = prove
 (`!ls bs.
     ls <<= dropUntilIncl P bs ==>
     (EX P bs ==>
     LENGTH (FILTER P ls) < LENGTH (FILTER P bs)) /\
     (~(EX P bs) ==>
       LENGTH (FILTER P ls) = 0)`,
  CHEAT_TAC);;

let isPREFIX_EQ_LENGTH = prove
 (`!ls rs.
     (LENGTH ls = LENGTH rs /\ ls <<= rs) <=>
       ls = rs`,
  CHEAT_TAC);;

let NULL_LAST_FIELDS_IMPL_P_LAST = prove
 (`!ls. ~(ls = []) ==> (NULL (LAST (FIELDS P ls)) ==> P (LAST ls))`,
  CHEAT_TAC);;

let P_LAST_IMPL_NULL_LAST_FIELDS = prove
 (`!ls. ~(ls = []) ==> (P (LAST ls) ==> NULL (LAST (FIELDS P ls)))`,
  CHEAT_TAC);;

let NULL_LAST_FIELDS_THM = prove
 (`!P ls. ~(ls = []) ==> (P (LAST ls) <=> NULL (LAST (FIELDS P ls)))`,
  CHEAT_TAC);;

let EXISTS_dropUntilIncl_right = prove
 (`!P ls.
     EX P ls /\ ~(P (LAST ls)) ==> ~(dropUntilIncl P ls = [])`,
  CHEAT_TAC);;

let EXISTS_dropUntilIncl_left = prove
 (`!P ls. ~(ls = []) /\ ~(dropUntilIncl P ls = []) ==> EX P ls`,
  CHEAT_TAC);;

let NOT_EXISTS_FRONT = prove
 (`!ls.
     EX P ls /\ ~(EX P (BUTLAST ls)) ==> P (LAST ls)`,
  CHEAT_TAC);;

let EXISTS_FRONT_dropUntilIncl_neq_nil = prove
 (`!ls. ~(ls = []) /\ EX P (BUTLAST ls) ==> ~(dropUntilIncl P ls = [])`,
  CHEAT_TAC);;

let NOT_EXISTS_FRONT_dropUntilIncl_eq_nil = prove
 (`!ls. ~(ls = []) /\ ~(EX P (BUTLAST ls)) ==> dropUntilIncl P ls = []`,
  CHEAT_TAC);;

let NOT_EXISTS_FRONT_takeUntil_eq_FRONT = prove
 (`!ls.
     EX P ls /\ ~(EX P (BUTLAST ls)) ==> takeUntil P ls = BUTLAST ls`,
  CHEAT_TAC);;

let NOT_EXISTS_FRONT_takeUntilIncl_eq_FRONT_LAST = prove
 (`!ls.
     EX P ls /\ ~(EX P (BUTLAST ls)) ==>
     takeUntilIncl P ls = APPEND (BUTLAST ls) [LAST ls]`,
  CHEAT_TAC);;


let EXISTS_takeUntilIncl_APPEND_takeUntil_EL = prove
 (`!ls.
     EX P ls ==>
     (takeUntilIncl P ls = APPEND (takeUntil P ls) [EL (LENGTH (takeUntil P
       ls)) ls] /\
     P (EL (LENGTH (takeUntil P ls)) ls))`,
  CHEAT_TAC);;

let EXISTS_FRONT_dropUntilIncl_thm = prove
 (`!P ls. ~(ls = []) ==>
      (EX P (BUTLAST ls) <=> ~(dropUntilIncl P ls = []))`,
  CHEAT_TAC);;

let EXISTS_FRONT_LAST_dropUntilIncl_eq = prove
 (`!P ls. ~(ls = []) /\ EX P (BUTLAST ls) ==> LAST (dropUntilIncl P ls) =
  LAST ls`,
  CHEAT_TAC);;

let LENGTH_FILTER_dropUntilIncl_one_less = prove
 (`!ls. ~(ls = []) /\ EX P (BUTLAST ls) ==>
       LENGTH (FILTER P (dropUntilIncl P ls)) = LENGTH (FILTER P ls) - 1`,
  CHEAT_TAC);;

let LENGTH_FILTER_dropUntilIncl = prove
 (`!ls. ~(ls = []) /\ EX P (BUTLAST ls) ==>
       LENGTH (FILTER P (dropUntilIncl P ls)) < LENGTH (FILTER P ls)`,
  CHEAT_TAC);;

let NOT_EXISTS_FRONT_FILTER = prove
 (`!ls. ~(ls = []) /\ ~(EX P (BUTLAST ls)) /\ EX P ls ==>
       FILTER P ls = [LAST ls]`,
  CHEAT_TAC);;

let LENGTH_splitlines_dropUntilIncl = prove
 (`!ls n.
       EX ((=) (CHR 10)) ls ==>
       LENGTH (splitlines (dropUntilIncl ((=) (CHR 10)) ls)) < LENGTH
         (splitlines ls)`,
  CHEAT_TAC);;

let LENGTH_splitlines_dropUntilIncl_one_less = prove
 (`!ls n.
       EX ((=) (CHR 10)) ls ==>
       LENGTH (splitlines (dropUntilIncl ((=) (CHR 10)) ls)) = LENGTH
         (splitlines ls) - 1`,
  CHEAT_TAC);;

let DROP_LENGTH_takeUntil_eq_dropUntil = prove
 (`!ls.
      DROP (LENGTH (takeUntil P ls)) ls = dropUntil P ls`,
  CHEAT_TAC);;

let LENGTH_splitlines_append_exists_r = prove
 (`!ls rs.
       ~(EX ((=) (CHR 10)) ls) /\ EX ((=) (CHR 10)) rs ==>
         LENGTH (splitlines (APPEND ls rs)) = LENGTH (splitlines rs)`,
  CHEAT_TAC);;

let LENGTH_splitlines_append_same = prove
 (`!ls rs. ~(ls = []) /\ LAST ls = LAST rs /\
     LENGTH (splitlines ls) < LENGTH (splitlines rs) ==>
         LENGTH (splitlines (APPEND ls xs)) < LENGTH (splitlines (APPEND
           rs xs))`,
  CHEAT_TAC);;

let dropUntilIncl_eq_TL_dropUntil = prove
 (`!ls. ~(dropUntil P ls = []) ==>
     dropUntilIncl P ls = TL (dropUntil P ls)`,
  CHEAT_TAC);;

let DROP_SUC_DROP_1_DROP = prove
 (`!ls n.
     DROP (SUC n) ls = DROP 1 (DROP n ls)`,
  CHEAT_TAC);;

let isPREFIX_TAKE_LENGTH = prove
 (`!ls rs.
     ls <<= rs <=> (ls = TAKE (LENGTH ls) rs /\ LENGTH ls <= LENGTH rs)`,
  CHEAT_TAC);;

let isPREFIX_LENGTH_LEQ = prove
 (`!ls rs.
     ls <<= rs ==> LENGTH ls <= LENGTH rs`,
  CHEAT_TAC);;

let isPREFIX_SEG = prove
 (`!ls rs.
     ls <<= rs <=>
       ls = SEG (LENGTH ls) 0 rs /\ LENGTH ls <= LENGTH rs`,
  CHEAT_TAC);;

let SEG_dropUntilIncl_SEG_takeUntilIncl = prove
 (`!ls.
      SEG n 0 (dropUntilIncl P ls) = SEG n (LENGTH (takeUntilIncl P ls))
        ls`,
  CHEAT_TAC);;

let isPREFIX_dropUntilIncl_eq_SEG_LENGTH_takeUntilIncl = prove
 (`!ls rs.
     ls <<= dropUntilIncl P rs ==>
       ls = SEG (LENGTH ls) (LENGTH (takeUntilIncl P rs)) rs`,
  CHEAT_TAC);;

let dropUntilIncl_takeUntilIncl = prove
 (`!ls.
     dropUntilIncl P ls = DROP (LENGTH (takeUntilIncl P ls)) ls`,
  CHEAT_TAC);;

let SEG_APPEND_part_of_DROP = prove
 (`!ls n k. ~(ls = []) /\ n + k <= LENGTH ls ==> APPEND (SEG n k ls) (DROP (n
  + k) ls) = DROP k ls`,
  CHEAT_TAC);;

let isPREFIX_MAP = prove
 (`!ls rs.
     ls <<= rs ==> MAP f ls <<= MAP f rs`,
  CHEAT_TAC);;

let LENGTH_takeUntilIncl_DROP_PREFIX = prove
 (`!ls xs.
     ~(EX P xs) /\ xs <<= ls ==>
       LENGTH (takeUntilIncl P (DROP (LENGTH xs) ls)) =
       LENGTH (DROP (LENGTH xs) (takeUntilIncl P ls))`,
  CHEAT_TAC);;

let takeUntilIncl_eq_takeUntil_append = prove
 (`!ls c.
     EX ((=) c) ls /\ ((=) c) a ==>
       takeUntilIncl ((=) c) ls = APPEND (takeUntil ((=) c) ls) [a]`,
  CHEAT_TAC);;

let forwardFD_lineForwardFD_not_in_buffer = prove
 (`!buff fs fd' extra.
     get_file_content fs fd' = SOME (content,pos) /\
     (extra <<= dropUntilIncl ((=) ((n2w 10):word8)) (MAP (n2w:num->(word8
       o) ORD) (DROP pos content)) \/
      extra = []) /\
     ~(EX ((=) ((n2w 10):word8)) buff) ==>
       (forwardFD fs fd' (LENGTH extra + LENGTH (takeUntilIncl ((=) (CHR
         10)) (DROP pos content))) =
         TextIOProof_lineForwardFD buff fs fd' extra)`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:5063-5090: a theorem whose statement the port
   cannot state yet: input_aux_w_content_spec *)

(* HOL4 TextIOProofScript.sml:5092-5119: a theorem whose statement the port
   cannot state yet: input_aux_spec *)

let input_spec = prove
 (`!fd' fdv fs content pos off offv req reqv buf bufv bactive pbactive.
   NUM off offv /\ NUM req reqv /\
   get_file_content fs fd' = SOME (content,pos) ==>
   get_mode fs fd' = SOME ReadMode ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_input_v [is; bufv; offv; reqv]
   (STDIO fs * W8ARRAY bufv buf * INSTREAM_BUFFERED_FD bactive fd' is)
   (POSTve
     (\nv. SEP_EXISTS (\pbactive.
       &(NUM (MIN req ((LENGTH content - pos) + LENGTH bactive)) nv /\
         req + off <= LENGTH buf) *
       INSTREAM_BUFFERED_FD pbactive fd' is *
       W8ARRAY bufv (insert_atI (APPEND (TAKE req bactive) (TAKE (req -
         LENGTH bactive)
                              (DROP pos (MAP (n2w o ORD) content))))
                              off buf) *
       STDIO (fsupdate fs fd' 0 (MIN ((req + LENGTH pbactive) - LENGTH
         bactive + pos)
                              (MAX pos (LENGTH content))) content)))
     (\e. &(IllegalArgument_exn e /\ LENGTH buf < req + off) *
           STDIO fs * W8ARRAY bufv buf * INSTREAM_BUFFERED_FD bactive fd'
             is))`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:5474-5493: a theorem whose statement the port
   cannot state yet: print_list_spec *)

(* a layer that makes buffered I/O nicer to work with *)

let INSTREAM_STR_def = new_definition
  `INSTREAM_STR fd' is (str:string) fs =
     SEP_EXISTS (\fsFFI_read active left.
       INSTREAM_BUFFERED_FD (MAP (n2w o ORD) active) fd' is *
       &(str = APPEND active left /\
          get_file_content fs fd' = SOME (APPEND fsFFI_read str,LENGTH
            fsFFI_read + LENGTH active) /\
          get_mode fs fd' = SOME ReadMode))`;;

let INSTREAM_STR_fd_neq = prove
 (`STD_streams fs ==>
   INSTREAM_STR fd is s fs =
   INSTREAM_STR fd is s fs * &(~(fd = 1) /\ ~(fd = 2))`,
  CHEAT_TAC);;

let INSTREAM_STR_add_stdout = prove
 (`STD_streams fs ==>
   INSTREAM_STR fd is rest ((add_stdo 1 "stdout") fs s) =
   INSTREAM_STR fd is rest fs`,
  CHEAT_TAC);;

let INSTREAM_STR'_def = new_definition
  `INSTREAM_STR' fd' is (str:string) fs non_empty is_empty =
     SEP_EXISTS (\fsFFI_read active left.
       INSTREAM_BUFFERED_FD (MAP (n2w o ORD) active) fd' is *
       &(str = APPEND active left /\
          (non_empty ==> ~(active = [])) /\ (is_empty ==> active = []) /\
          get_file_content fs fd' = SOME (APPEND fsFFI_read str,LENGTH
            fsFFI_read + LENGTH active) /\
          get_mode fs fd' = SOME ReadMode))`;;

(* [local] *)
let INSTREAM_STR'_F_F = prove
 (`INSTREAM_STR' fd is input fs F F = INSTREAM_STR fd is input fs`,
  CHEAT_TAC);;

(* Useful for applying fastForwardFD_forwardFD *)
let INSTREAM_STR'_get_file_content = prove
 (`INSTREAM_STR' fd is s (forwardFD fs fd k) ne ie =
   INSTREAM_STR' fd is s (forwardFD fs fd k) ne ie *
   &(?content pos.
       get_file_content fs fd = SOME (content,pos) /\ pos + k <= LENGTH
         content)`,
  CHEAT_TAC);;

(* Useful for applying fastForwardFD_forwardFD *)
let INSTREAM_STR_get_file_content = prove
 (`INSTREAM_STR fd is s (forwardFD fs fd k) =
   INSTREAM_STR fd is s (forwardFD fs fd k) *
   &(?content pos.
       get_file_content fs fd = SOME (content,pos) /\ pos + k <= LENGTH
         content)`,
  CHEAT_TAC);;

let splitlines_at_def = new_definition
  `splitlines_at c0 ls =
     (let
        lines = FIELDS ((=) c0) ls in
        if NULL (LAST lines) then BUTLAST lines else lines)`;;

let lines_of_gen_def = new_definition
  `lines_of_gen c0 s =
     MAP (\x. strcat (implode x) (integer_word_toString c0))
       (splitlines_at c0 (explode s))`;;

(* TODO Maybe splitlines should be defined exactly like this. *)
let splitlines_at_splitlines = prove
 (`splitlines_at (CHR 10) s = splitlines s`,
  CHEAT_TAC);;

(* TODO Maybe lines_of should be defined exactly like this. *)
let lines_of_gen_lines_of = prove
 (`lines_of_gen (CHR 10) s = lines_of s`,
  CHEAT_TAC);;

let INSTREAM_LINES_def = new_definition
  `INSTREAM_LINES c0 fd' is (lines:mlstring list) fs =
     SEP_EXISTS (\rest.
       INSTREAM_STR fd' is rest fs *
       &(lines_of_gen c0 (implode rest) = lines))`;;

(* Useful for applying fastForwardFD_forwardFD *)
let INSTREAM_LINES_get_file_content = prove
 (`INSTREAM_LINES c0 fd is lines (forwardFD fs fd k) =
   INSTREAM_LINES c0 fd is lines (forwardFD fs fd k) *
   &(?content pos.
       get_file_content fs fd = SOME (content,pos) /\ pos + k <= LENGTH
         content)`,
  CHEAT_TAC);;

let INSTREAM_LINES_fd_neq = prove
 (`STD_streams fs ==>
   INSTREAM_LINES c0 fd is s fs =
   INSTREAM_LINES c0 fd is s fs * &(~(fd = 1) /\ ~(fd = 2))`,
  CHEAT_TAC);;

let INSTREAM_LINES_add_stdout = prove
 (`STD_streams fs ==>
   INSTREAM_LINES c0 fd is rest ((add_stdo 1 "stdout") fs s) =
   INSTREAM_LINES c0 fd is rest fs`,
  CHEAT_TAC);;

(* TODO: COPIED THEOREMS ABOUT splitlines *)
let splitlines_at_next = prove
 (`splitlines_at c0 ls = CONS ln lns ==>
   splitlines_at c0 (DROP (SUC (LENGTH ln)) ls) = lns /\
   ln <<= ls /\ (LENGTH ln < LENGTH ls ==> APPEND ln [c0] <<= ls)`,
  CHEAT_TAC);;

let splitlines_at_nil = CAKE_EVAL [splitlines_at_def] `splitlines_at c0 ""`;;
add_simp splitlines_at_nil;;

let splitlines_at_eq_nil = prove
 (`splitlines_at c0 ls = [] <=> (ls = [])`,
  CHEAT_TAC);;
add_simp splitlines_at_eq_nil;;

let lines_of_gen_nil = prove
 (`lines_of_gen c0 s = [] <=> s = (implode "")`,
  CHEAT_TAC);;
add_simp lines_of_gen_nil;;

let splitlines_at_CONS_FST_SPLITP = prove
 (`splitlines_at c0 ls = CONS ln lns ==> FST (SPLITP ((=) c0) ls) = ln`,
  CHEAT_TAC);;

let splitlines_at_not_exists2 = prove
 (`!l.
         ~(EX ((=) c0) l) ==>
         splitlines_at c0 l = (if l = "" then [] else [l])`,
  CHEAT_TAC);;

let FIELDS_hd_c0 = prove
 (`!t.
         FIELDS ((=) c0) (CONS c0 t) = CONS "" (FIELDS ((=) c0) t)`,
  CHEAT_TAC);;

let SPLITP_takeUntil_c0 = prove
 (`!l.
         SPLITP ((=) c0) l =
           (takeUntil ((=) c0) l,DROP (LENGTH (takeUntil ((=) c0) l)) l)`,
  CHEAT_TAC);;

let FIELDS_takeUntil_c0 = prove
 (`!l.
       LENGTH (takeUntil ((=) c0) l) < LENGTH l ==>
       FIELDS ((=) c0) l = CONS (takeUntil ((=) c0) l)
             (FIELDS ((=) c0) (TL (DROP (LENGTH (takeUntil ((=) c0) l))
               l)))`,
  CHEAT_TAC);;

let splitlines_at_hd_c0 = prove
 (`!t.
         splitlines_at c0 (CONS c0 t) = CONS "" (splitlines_at c0 t)`,
  CHEAT_TAC);;

let splitlines_at_takeUntil_exists = prove
 (`!l.
         EX ((=) c0) l ==>
         splitlines_at c0 l =
           (CONS (takeUntil ((=) c0) l)
             (splitlines_at c0 (TL (DROP (LENGTH (takeUntil ((=) c0) l))
               l))))`,
  CHEAT_TAC);;

let splitlines_at_takeUntil_exists2 = prove
 (`!l.
         EX ((=) c0) l ==>
         splitlines_at c0 l =
           (CONS (takeUntil ((=) c0) l)
             (splitlines_at c0 (DROP (SUC (LENGTH (takeUntil ((=) c0) l)))
               l)))`,
  CHEAT_TAC);;

(*** END TODO COPIED ***)

(* [local] *)
let MAP_MAP_n2w_ORD = prove
 (`(!xs. MAP (n2w o ORD) (MAP (CHR o (w2n:word8->num)) xs) = xs) /\
   (!xs. MAP (CHR o (w2n:word8->num)) (MAP (n2w o ORD) xs) = xs)`,
  CHEAT_TAC);;

let input1_spec_str = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  TextIO_input1_v [is]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (POSTv (?_SEP_EXISTS chv) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_STR fd is (TL s) (forwardFD fs fd k) *
          &(OPTION_TYPE CHAR (oHD s) chv))`,
  CHEAT_TAC);;

let peekChar_spec_str = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  TextIO_peekChar_v [is]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (POSTv (?_SEP_EXISTS chv) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_STR fd is s (forwardFD fs fd k) *
          &(OPTION_TYPE CHAR (oHD s) chv))`,
  CHEAT_TAC);;

let peekChar_spec_lines = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  TextIO_peekChar_v [is]
      (STDIO fs * INSTREAM_LINES c0 fd is s fs)
      (POSTv (?_SEP_EXISTS chv) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_LINES c0 fd is s (forwardFD fs fd k) *
          &(OPTION_TYPE CHAR (match s with [] -> NONE | (CONS l ls) -> oHD
            (APPEND (explode l) [c0])) chv))`,
  CHEAT_TAC);;

let file_content_def = new_definition
  `file_content fs fname =
     (match ALOOKUP (IO_fs_files fs) fname with NONE -> NONE
     | SOME ino -> ALOOKUP (IO_fs_inode_tbl fs) (File ino))`;;

let stdin_content_def = new_definition
  `stdin_content fs =
     (if ALOOKUP (IO_fs_infds fs) 0 = SOME (UStream (implode
       "stdin"),ReadMode,0) then
       SOME (THE (ALOOKUP (IO_fs_inode_tbl fs) (UStream (implode "stdin"))))
     else NONE)`;;

let openStdIn_spec_str = prove
 (`stdin_content fs = SOME text /\
   UNIT_TYPE one uv ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_openStdIn_v [uv]
      (STDIO fs)
      (POSTv (?_STDIO is) fs * INSTREAM_STR 0 is text fs)`,
  CHEAT_TAC);;

let openIn_spec_str = prove
 (`FILENAME s sv /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
  (IO_fs_maxFD fs) (256 EXP 8) /\ file_content fs s = SOME text ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_openIn_v [sv]
      (STDIO fs)
      (POSTv (?_STDIO is) (openFileFS s fs ReadMode 0) *
         INSTREAM_STR (nextFD fs) is text (openFileFS s fs ReadMode 0))`,
  CHEAT_TAC);;

let closeIn_spec_str = prove
 (`fd >= 3 /\ fd <= IO_fs_maxFD fs ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_closeIn_v [is]
     (STDIO fs * INSTREAM_STR fd is text fs)
     (POSTve
        (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fd (IO_fs_infds
          fs)) *
             STDIO (IO_fs_infds_fupd (ADELKEY fd) fs))
        (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fd
          (IO_fs_infds fs))) * STDIO fs))`,
  CHEAT_TAC);;

let toString_STRING = prove
 (`integer_word_toString h = implode (CONS h "")`,
  CHEAT_TAC);;

let TOKENS_EQ_SING = prove
 (`ALL ((~) o f) xs /\ ~(xs = []) ==> TOKENS f xs = [xs]`,
  CHEAT_TAC);;

let TOKENS_CONS = prove
 (`f x ==> TOKENS f (CONS x xs) = TOKENS f xs`,
  CHEAT_TAC);;

let openStdIn_spec_lines = prove
 (`stdin_content fs = SOME text /\
   UNIT_TYPE one uv ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_openStdIn_v [uv]
      (STDIO fs)
      (POSTv (?_STDIO is) fs * INSTREAM_LINES c0 0 is (lines_of_gen c0
        (implode text)) fs)`,
  CHEAT_TAC);;

(* TODO: copied from fsFFIProps *)
(* HOL4 TextIOProofScript.sml:6106-6107: the overload all_lines_inode_gen,
   which the port expands *)

let all_lines_file_gen_def = new_definition
  `all_lines_file_gen c0 fs fname =
     (\c0 fs ino. lines_of_gen c0 (implode (THE (ALOOKUP (IO_fs_inode_tbl
       fs) ino)))) c0 fs (File (THE (ALOOKUP (IO_fs_files fs) fname)))`;;

(* end TODO: copied from fsFFIProps *)

let all_lines_file_gen_all_lines_file = prove
 (`all_lines_file_gen (CHR 10) fs f =
   all_lines_file fs f`,
  CHEAT_TAC);;
add_simp all_lines_file_gen_all_lines_file;;

(* TODO Move to fsFFIProps? *)
let all_lines_file_gen_lines_of_gen = prove
 (`file_content fs fname = SOME s ==>
   all_lines_file_gen c0 fs fname = lines_of_gen c0 (implode s)`,
  CHEAT_TAC);;

let openIn_spec_lines = prove
 (`FILENAME s sv /\ CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN
  (IO_fs_maxFD fs) (256 EXP 8) /\ inFS_fname fs s ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_openIn_v [sv]
      (STDIO fs)
      (POSTv (?_STDIO is) (openFileFS s fs ReadMode 0) *
         INSTREAM_LINES c0 (nextFD fs) is (all_lines_file_gen c0 fs s)
           (openFileFS s fs ReadMode 0))`,
  CHEAT_TAC);;

let closeIn_spec_lines = prove
 (`fd >= 3 /\ fd <= IO_fs_maxFD fs ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_closeIn_v [is]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
     (POSTve
        (\u. &(UNIT_TYPE one u /\ TextIOProof_validFileFD fd (IO_fs_infds
          fs)) *
             STDIO (IO_fs_infds_fupd (ADELKEY fd) fs))
        (\e. &(InvalidFD_exn e /\ ~(TextIOProof_validFileFD fd
          (IO_fs_infds fs))) * STDIO fs))`,
  CHEAT_TAC);;

(* [local] *)
let split_exists = prove
 (`!input.
     ?to_read text.
       input = APPEND to_read text /\
       ((~(text = "") ==> HD text = c0) /\ ALL (\c. ~(c = c0)) to_read)`,
  CHEAT_TAC);;

(* [local] *)
let fastForwardFD_eq_forwardFD = prove
 (`!fs fd' c off x.
     get_file_content fs fd' = SOME (c,off) /\ LENGTH c = off + x ==>
       forwardFD fs fd' x = fastForwardFD fs fd'`,
  CHEAT_TAC);;

(* [local] *)
let fastForwardFD_same_infds = prove
 (`!fs n. MAP FST (IO_fs_infds (fastForwardFD fs n)) = MAP FST (IO_fs_infds
  fs)`,
  CHEAT_TAC);;

let INSTREAM_STR_fastForwardFD = prove
 (`SEP_IMP (
     STDIO (forwardFD fs fd x) * INSTREAM_STR fd is "" (forwardFD fs fd x))
       (
     STDIO (fastForwardFD fs fd) * INSTREAM_STR fd is "" (fastForwardFD fs
       fd) * GC)`,
  CHEAT_TAC);;

let INSTREAM_LINES_fastForwardFD = prove
 (`SEP_IMP (
     STDIO (forwardFD fs fd x) * INSTREAM_LINES c0 fd is [] (forwardFD fs fd
       x)) (
     STDIO (fastForwardFD fs fd) * INSTREAM_LINES c0 fd is []
       (fastForwardFD fs fd) * GC)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\(c,wl,i,j). (LENGTH wl + 1) - i)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 TextIOProofScript.sml:6257-6260: the tactic that proves the
   termination *)
let find_surplus_fun_def,find_surplus_fun_ind = define_guess
  `find_surplus_fun c (wl:word8 list) (i:num) (j:num) =
     if i = j \/ LENGTH wl < i \/ LENGTH wl < j then NONE else if ORD c
       = w2n (EL i wl) then SOME i else find_surplus_fun c wl (i + 1) j`;;

let find_surplus = prove
 (`CHAR c cv /\ NUM i iv /\ NUM j jv /\ i <= j /\ j <= LENGTH wl /\ av =
  semanticPrimitives_Loc T a ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_find_surplus_v [cv; av; iv; jv]
     (cell a (semanticPrimitives_W8array wl))
     (cell (POSTv (?_a retv)) (semanticPrimitives_W8array wl) *
         &(OPTION_TYPE NUM (find_surplus_fun c wl i j) retv))`,
  CHEAT_TAC);;

(* [local] *)
let to_W8ARRAY = prove
 (`cell loc (semanticPrimitives_W8array bcontent) = W8ARRAY
  (semanticPrimitives_Loc T loc) bcontent`,
  CHEAT_TAC);;

(* [local] *)
let ind_surplus_fun_eq_NONE = prove
 (`!c bcontent r w.
     w <= LENGTH bcontent /\ r <= w /\
     (!i. r <= i /\ i < w ==> ~(w2n (EL i bcontent) = ORD c)) ==>
     find_surplus_fun c bcontent r w = NONE`,
  CHEAT_TAC);;

(* [local] *)
let ind_surplus_fun_eq_SOME = prove
 (`!c bcontent r w.
     w <= LENGTH bcontent /\ r <= j /\ j < LENGTH bcontent /\
     w2n (EL j bcontent) = ORD c /\ r < w /\ j < w /\
     (!i. r <= i /\ i < j ==> ~(w2n (EL i bcontent) = ORD c)) ==>
     find_surplus_fun c bcontent r w = SOME j`,
  CHEAT_TAC);;

let inputUntil_1_not_found = prove
 (`CHAR c cv /\ ALL (\w. ~(w2n w = ORD c)) bactive ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputUntil_1_v [is; cv]
     (INSTREAM_BUFFERED_FD bactive fd is)
     (POSTv (?_INSTREAM_BUFFERED_FD retv) [] fd is *
         &(SUM_TYPE STRING_TYPE STRING_TYPE
              (INL (implode (MAP (CHR o w2n) bactive))) retv))`,
  CHEAT_TAC);;

(* [local] *)
let TAKE_LENGTH_ADD1 = prove
 (`TAKE (LENGTH xs + 1) (APPEND xs (CONS y ys)) = APPEND xs [y]`,
  CHEAT_TAC);;

let inputUntil_1_found = prove
 (`CHAR c cv /\ ALL (\w. ~(w2n w = ORD c)) bs1 ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputUntil_1_v [is; cv]
     (INSTREAM_BUFFERED_FD (APPEND bs1 (CONS (n2w (ORD c)) bs2)) fd is)
     (POSTv (?_INSTREAM_BUFFERED_FD retv) bs2 fd is *
         &(SUM_TYPE STRING_TYPE STRING_TYPE
              (INR (implode (APPEND (MAP (CHR o w2n) bs1) [c]))) retv))`,
  CHEAT_TAC);;

(* [local] *)
let not_EVERY_imp = prove
 (`!xs. ~(ALL p xs) ==> (?ys z zs. xs = APPEND ys (CONS z zs) /\ ALL p ys
  /\ ~(p z))`,
  CHEAT_TAC);;

let inputUntil_1_spec = prove
 (`CHAR c cv ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputUntil_1_v [is; cv]
     (INSTREAM_STR' fd is input fs non_empty is_empty)
     (POSTv (?_SEP_EXISTS retv) bs1 bs2 (?_INSTREAM_STR' is_empty1) fd is
       bs2 fs F is_empty1 *
           &(input = APPEND bs1 bs2 /\
              (non_empty ==> ~(bs1 = [])) /\
              (
               ALL (\v. ~(v = c)) bs1 /\ is_empty1 /\
               SUM_TYPE STRING_TYPE STRING_TYPE (INL (implode bs1)) retv \/
               ALL (\v. ~(v = c)) (BUTLAST bs1) /\ LAST bs1 = c /\ ~(bs1 =
                 []) /\
               SUM_TYPE STRING_TYPE STRING_TYPE (INR (implode bs1))
                 retv)))`,
  CHEAT_TAC);;

let refillBuffer_with_read_spec_STR = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  TextIO_refillBuffer_with_read_v [is]
     (STDIO fs * INSTREAM_STR' fd is input fs F T)
     (POSTv (?_SEP_EXISTS retv) (?_STDIO nr) (forwardFD fs fd nr) *
          INSTREAM_STR' fd is input (forwardFD fs fd nr) (~(NULL input))
            (NULL input))`,
  CHEAT_TAC);;

let refillBuffer_with_read_guard_spec_STR = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  TextIO_refillBuffer_with_read_guard_v [is]
     (STDIO fs * INSTREAM_STR' fd is input fs F T)
     (POSTv (?_SEP_EXISTS retv) (?_STDIO nr) (forwardFD fs fd nr) *
          INSTREAM_STR' fd is input (forwardFD fs fd nr) (~(NULL input))
            (NULL input) *
          &(BOOL (NULL input) retv))`,
  CHEAT_TAC);;

let takeUnitlIncl_append = prove
 (`!bs1 bs2 p.
     ALL (\x. ~(p x)) bs1 ==>
     takeUntilIncl p (APPEND bs1 bs2) =
     APPEND bs1 (takeUntilIncl p bs2)`,
  CHEAT_TAC);;

let gen_inputLine_lem1 = prove
 (`!bs1 bs2.
     ALL (\v. ~(v = c)) bs1 ==>
     gen_inputLine c (APPEND bs1 bs2) = strcat (implode bs1) (gen_inputLine
       c bs2) /\
     dropUntilIncl ((=) c) (APPEND bs1 bs2) = dropUntilIncl ((=) c) bs2`,
  CHEAT_TAC);;

let gen_inputLine_lem2 = prove
 (`ALL (\v. ~(v = LAST bs1)) (BUTLAST bs1) /\ ~(bs1 = "") ==>
   gen_inputLine (LAST bs1) (APPEND bs1 bs2) = implode bs1 /\
   dropUntilIncl ((=) (LAST bs1)) (APPEND bs1 bs2) = bs2`,
  CHEAT_TAC);;

(* [local] *)
let inputUntil_2_spec_STR_lemma = prove
 (`!input acc accv fs.
     CHAR c cv /\ LIST_TYPE STRING_TYPE acc accv /\ ~(acc = []) ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_inputUntil_2_v [is; cv; accv]
       (STDIO fs * INSTREAM_STR' fd is input fs T F)
       (POSTv (?_SEP_EXISTS retv) (?_STDIO nr) (forwardFD fs fd nr) *
            INSTREAM_STR fd is (dropUntilIncl ((=) c) input) (forwardFD fs
              fd nr) *
            &(OPTION_TYPE STRING_TYPE
                (SOME (strcat (mlstring_concat (REVERSE acc))
                  (gen_inputLine c input))) retv))`,
  CHEAT_TAC);;

let inputUntil_2_spec_STR = prove
 (`CHAR c cv /\ LIST_TYPE STRING_TYPE [] accv ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputUntil_2_v [is; cv; accv]
     (STDIO fs * INSTREAM_STR fd is input fs)
     (POSTv (?_SEP_EXISTS retv) (?_STDIO nr) (forwardFD fs fd nr) *
          INSTREAM_STR fd is (dropUntilIncl ((=) c) input) (forwardFD fs fd
            nr) *
          &(OPTION_TYPE STRING_TYPE
              (if input = "" then NONE else SOME (gen_inputLine c input))
                retv))`,
  CHEAT_TAC);;

let dropUntilIncl_empty = prove
 (`ALL (\c. ~(c = c0)) ls ==>
   dropUntilIncl ((=) c0) ls = ""`,
  CHEAT_TAC);;

let dropUntilIncl_cons = prove
 (`dropUntilIncl P (CONS x xs) =
   if P x then xs
   else dropUntilIncl P xs`,
  CHEAT_TAC);;

let takeUntilIncl_cons2 = prove
 (`takeUntilIncl P (CONS x xs) =
   if P x then [x]
   else CONS x (takeUntilIncl P xs)`,
  CHEAT_TAC);;

let implode_cons_str = prove
 (`strcat (integer_word_toString c) (implode cs) =
     implode (CONS c cs)`,
  CHEAT_TAC);;

let gen_inputLine_cons = prove
 (`gen_inputLine c (CONS x xs) =
   if x = c then integer_word_toString c else strcat
     (integer_word_toString x) (gen_inputLine c xs)`,
  CHEAT_TAC);;

(* [local] *)
let inputLineWith_spec_STR = prove
 (`CHAR c0 c0v /\
   ALL (\c. ~(c = c0)) to_read /\
   (~(text = "") ==> HD text = c0) ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputLineWith_v [c0v; is]
     (STDIO fs * INSTREAM_STR fd is (APPEND to_read text) fs)
     (POSTv (?_SEP_EXISTS v) (?_cond k) (OPTION_TYPE STRING_TYPE
                         (match to_read with [] -> (if text = "" then NONE
                           else SOME (integer_word_toString c0))
                          | _ -> SOME (implode (APPEND to_read [c0]))) v) *
                 STDIO (forwardFD fs fd k) *
                 INSTREAM_STR fd is (TL text) (forwardFD fs fd k))`,
  CHEAT_TAC);;

(* [local] *)
let inputLineTokens_spec_STR = prove
 (`CHAR c0 c0v /\
   (CHAR (Arrow) BOOL) f fv /\
   (STRING_TYPE (Arrow) (a:'a->semanticPrimitives_v->bool)) g gv /\
   ALL (\c. ~(c = c0)) to_read /\
   (~(text = "") ==> HD text = c0) /\
   f c0 ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputLineTokens_v [c0v; is; fv; gv]
     (STDIO fs * INSTREAM_STR fd is (APPEND to_read text) fs)
     (POSTv (?_SEP_EXISTS v) (?_cond k) (OPTION_TYPE (LIST_TYPE a)
                         (OPTION_MAP (MAP g o tokens f)
                           (if NULL text /\ NULL to_read then NONE
                            else SOME (implode to_read))) v) *
                 STDIO (forwardFD fs fd k) *
                 INSTREAM_STR fd is (TL text) (forwardFD fs fd k))`,
  CHEAT_TAC);;

let inputLineTokens_spec_lines = prove
 (`CHAR c0 c0v /\
   (CHAR (Arrow) BOOL) f fv /\ (STRING_TYPE (Arrow)
     (a:'a->semanticPrimitives_v->bool)) g gv /\ f c0 ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputLineTokens_v [c0v; is; fv; gv]
      (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
      (POSTv (?_SEP_EXISTS v) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_LINES c0 fd is (TL lines) (forwardFD fs fd k) *
          &(OPTION_TYPE (LIST_TYPE a)
              (OPTION_MAP (MAP g o tokens f) (oHD lines)) v))`,
  CHEAT_TAC);;

let inputAllTokens_aux_spec = prove
 (`!lines acc accv fs.
     CHAR c0 c0v /\
     (CHAR (Arrow) BOOL) f fv /\ (STRING_TYPE (Arrow)
       (a:'a->semanticPrimitives_v->bool)) g gv /\ f c0 /\
     LIST_TYPE (LIST_TYPE a) acc accv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_inputAllTokens_aux_v
      [c0v; is; fv; gv; accv]
      (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
        (POSTv (?_SEP_EXISTS v) (?_STDIO k) (forwardFD fs fd k) *
                 INSTREAM_LINES c0 fd is [] (forwardFD fs fd k) *
                 &(LIST_TYPE (LIST_TYPE a)
                     (APPEND (REVERSE acc) (MAP (MAP g o tokens f) lines))
                       v))`,
  CHEAT_TAC);;

let inputAllTokens_spec = prove
 (`CHAR c0 c0v /\
   (CHAR (Arrow) BOOL) f fv /\ (STRING_TYPE (Arrow)
     (a:'a->semanticPrimitives_v->bool)) g gv /\ f c0 ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputAllTokens_v
     [c0v; is; fv; gv]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
       (POSTv (?_STDIO v) (fastForwardFD fs fd) *
          INSTREAM_LINES c0 fd is [] (fastForwardFD fs fd) *
          &(LIST_TYPE (LIST_TYPE a) (MAP (MAP g o tokens f) lines) v))`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:7092-7159: a theorem whose statement the port
   cannot state yet: inputAllTokensFile_spec *)

let open_option_SOME_fail = prove
 (`OPTION_TYPE FILENAME (SOME s) fnv /\ ~(inFS_fname fs s) /\ CARD (set_of_list
  (MAP FST (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs) (256 EXP 8) ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_open_option_v [fnv]
     (STDIO fs)
     (POSTv (?_STDIO retv) fs * &(OPTION_TYPE a NONE retv))`,
  CHEAT_TAC);;

(* PORT FAILED: Definition sub_spec_def: expected ')' but found '.' at 228 *)
(* HOL4 TextIOProofScript.sml:7190-7198: the definition *)

let open_option_SOME = prove
 (`OPTION_TYPE FILENAME (SOME s) fnv /\ inFS_fname fs s /\ CARD (set_of_list
  (MAP FST (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs) (256 EXP 8) /\
   file_content fs s = SOME text ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_open_option_v [fnv]
     (STDIO fs)
     (POSTv (?_SEP_EXISTS retv) is (?_STDIO f) (openFileFS s fs ReadMode 0)
       *
        INSTREAM_STR (nextFD fs) is text (openFileFS s fs ReadMode 0) *
        &(OPTION_TYPE (PAIR_TYPE (\x v. v = is) (\x v. v = f)) (SOME
          (one,one)) retv /\
           sub_spec f p is (nextFD fs)))`,
  CHEAT_TAC);;

let sub_spec_none_def = new_definition
  `sub_spec_none f p is =
           (!fs text v k.
             UNIT_TYPE one v ==>
             app (p:('ffi->(mlstring,ffi)fmap)#(mlstring
               list#(mlstring->word8 list->word8 list->ffi->(ffi
               cfHeapsBase_ffi_result) option)) list) f [v]
               (STDIO (forwardFD fs 0 k) *
                INSTREAM_STR 0 is text (forwardFD fs 0 k))
               (POSTv (?_STDIO u) (fastForwardFD fs 0)))`;;

let consume_rest_spec = prove
 (`!s fs fd' k.
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_consume_rest_v [is]
       (STDIO (forwardFD fs fd' k) * INSTREAM_STR fd' is s (forwardFD fs fd'
         k))
       (POSTv (?_STDIO retv) (fastForwardFD fs fd'))`,
  CHEAT_TAC);;

let STDIO_ADELKEY = prove
 (`CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs) (256
  EXP 8) ==> SEP_IMP (STDIO (IO_fs_infds_fupd (ADELKEY (nextFD fs))
  (forwardFD (openFileFS s fs ReadMode 0) (nextFD fs) k))) (STDIO fs * GC)`,
  CHEAT_TAC);;

let open_option_NONE = prove
 (`OPTION_TYPE b NONE fnv /\
   stdin_content fs = SOME text ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_open_option_v [fnv]
     (STDIO fs)
     (POSTv (?_SEP_EXISTS retv) is (?_STDIO f) fs * INSTREAM_STR 0 is text
       fs *
        &(OPTION_TYPE (PAIR_TYPE (\x v. v = is) (\x v. v = f)) (SOME
          (one,one)) retv /\
           sub_spec_none f p is))`,
  CHEAT_TAC);;

let inFS_fname_file_content_SOME = prove
 (`inFS_fname fs fname /\ consistentFS fs ==>
   (?s. file_content fs fname = SOME s)`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:7358-7436: a theorem whose statement the port
   cannot state yet: inputAllTokensFrom_SOME *)

let fs_with_infds_updated_by = prove
 (`IO_fs_infds_fupd (AFUPDKEY k f)
     fs = IO_fs_infds_fupd (K (AFUPDKEY k f (IO_fs_infds fs)))
     fs`,
  CHEAT_TAC);;

(* TODO Can we formulate this generally and stuff it into automation? *)
let STDIO_INSTREAM_STR_fastForwardFD_forwardFD = prove
 (`?k. SEP_IMP (STDIO (fastForwardFD fs 0) *
       INSTREAM_STR 0 is rest (fastForwardFD fs 0)) (
       STDIO (forwardFD fs 0 k) *
       INSTREAM_STR 0 is rest (forwardFD fs 0 k))`,
  CHEAT_TAC);;

let inputAllTokensFrom_NONE = prove
 (`CHAR c0 c0v /\
   OPTION_TYPE FILENAME NONE fnamev /\ stdin_content fs = SOME text /\
   (CHAR (Arrow) BOOL) f fv /\ (STRING_TYPE (Arrow)
     (a:'a->semanticPrimitives_v->bool)) g gv /\ f c0 ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputAllTokensFrom_v
     [c0v; fnamev; fv; gv]
     (STDIO fs)
     (POSTv (?_STDIO sv) (fastForwardFD fs 0) *
        &(OPTION_TYPE (LIST_TYPE (LIST_TYPE a))
          (SOME (MAP (MAP g o tokens f) (lines_of_gen c0 (implode text))))
            sv))`,
  CHEAT_TAC);;

let inputLineWith_spec_lines_and_terminator = prove
 (`CHAR c0 c0v ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputLineWith_v [c0v; is]
      (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
      (POSTv (?_SEP_EXISTS v) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_LINES c0 fd is (TL lines) (forwardFD fs fd k) *
          &(OPTION_TYPE STRING_TYPE (oHD lines) v /\
             (!s. oHD lines = SOME s ==> (?s0. s = strcat s0
               (integer_word_toString c0)))))`,
  CHEAT_TAC);;

let inputLine_spec_lines_and_terminator = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  TextIO_inputLine_v [is]
      (STDIO fs * INSTREAM_LINES (CHR 10) fd is lines fs)
      (POSTv (?_SEP_EXISTS v) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_LINES (CHR 10) fd is (TL lines) (forwardFD fs fd k) *
          &(OPTION_TYPE STRING_TYPE (oHD lines) v /\
             (!s. oHD lines = SOME s ==> (?s0. s = strcat s0
               (integer_word_toString (CHR 10))))))`,
  CHEAT_TAC);;

let inputLineWith_spec_lines = prove
 (`CHAR c0 c0v ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputLineWith_v [c0v; is]
      (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
      (POSTv (?_SEP_EXISTS v) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_LINES c0 fd is (TL lines) (forwardFD fs fd k) *
          &(OPTION_TYPE STRING_TYPE (oHD lines) v))`,
  CHEAT_TAC);;

let inputLine_spec_lines = prove
 (`app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  TextIO_inputLine_v [is]
      (STDIO fs * INSTREAM_LINES (CHR 10) fd is lines fs)
      (POSTv (?_SEP_EXISTS v) (?_STDIO k) (forwardFD fs fd k) *
          INSTREAM_LINES (CHR 10) fd is (TL lines) (forwardFD fs fd k) *
          &(OPTION_TYPE STRING_TYPE (oHD lines) v))`,
  CHEAT_TAC);;

let inputLines_aux_spec = prove
 (`!lines acc accv fs.
     CHAR c0 c0v /\
     LIST_TYPE STRING_TYPE acc accv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_inputLines_aux_v
      [c0v; is; accv]
      (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
        (POSTv (?_SEP_EXISTS v) (?_STDIO k) (forwardFD fs fd k) *
                 INSTREAM_LINES c0 fd is [] (forwardFD fs fd k) *
                 &(LIST_TYPE STRING_TYPE (APPEND (REVERSE acc) lines) v))`,
  CHEAT_TAC);;

let inputLines_spec = prove
 (`CHAR c0 c0v ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_inputLines_v
     [c0v; is]
     (STDIO fs * INSTREAM_LINES c0 fd is lines fs)
       (POSTv (?_STDIO v) (fastForwardFD fs fd) *
         INSTREAM_LINES c0 fd is [] (fastForwardFD fs fd) *
         &(LIST_TYPE STRING_TYPE lines v))`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:7707-7772: a theorem whose statement the port
   cannot state yet: inputLinesFile_spec *)

(* HOL4 TextIOProofScript.sml:7774-7800: a theorem whose statement the port
   cannot state yet: inputLinesStdIn_spec *)

let extend_array_spec = prove
 (`!arrv arr.
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_extend_array_v [arrv] (W8ARRAY arrv arr)
         (POSTv (?_W8ARRAY v) v (APPEND arr (REPLICATE (LENGTH arr) (n2w
           0))))`,
  CHEAT_TAC);;

let map_n2w_ord = prove
 (`!xs ys.
     MAP (n2w o ORD) xs = (ys:word8 list) ==>
     xs = MAP (CHR o w2n) ys`,
  CHEAT_TAC);;

(* HOL4 TextIOProofScript.sml:7822-7870: a theorem whose statement the port
   cannot state yet: inputBuff_spec *)

(* HOL4 TextIOProofScript.sml:7872-7925: a theorem whose statement the port
   cannot state yet: inputAll_aux_spec *)

(* HOL4 TextIOProofScript.sml:7927-7944: a theorem whose statement the port
   cannot state yet: inputAll_spec *)

(* HOL4 TextIOProofScript.sml:7946-8002: a theorem whose statement the port
   cannot state yet: inputAllFrom_SOME_spec *)

(* HOL4 TextIOProofScript.sml:8004-8034: a theorem whose statement the port
   cannot state yet: inputAllFrom_NONE_spec *)

let fold_chars_loop_thm = prove
 (`!is a f fv' s y yv fs fd'.
     (CHAR (Arrow) a (Arrow) a) f fv' /\ a y yv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_fold_chars_loop_v [fv'; is; yv]
       (STDIO fs * INSTREAM_STR fd' is s fs)
       (POSTv (?_SEP_EXISTS retv) (?_STDIO k) (forwardFD fs fd' k) *
          INSTREAM_STR fd' is [] (forwardFD fs fd' k) *
          &(a (mllist_foldl f y s) retv))`,
  CHEAT_TAC);;

let fold_lines_loop_thm = prove
 (`!is a f fv' s y yv fs fd' c0 c0v.
     CHAR c0 c0v /\
     (STRING_TYPE (Arrow) a (Arrow) a) f fv' /\ a y yv ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       TextIO_fold_lines_loop_v [c0v; fv'; is; yv]
       (STDIO fs * INSTREAM_LINES c0 fd' is s fs)
       (POSTv (?_SEP_EXISTS retv) (?_STDIO k) (forwardFD fs fd' k) *
          INSTREAM_LINES c0 fd' is [] (forwardFD fs fd' k) *
          &(a (mllist_foldl f y s) retv))`,
  CHEAT_TAC);;

let foldChars_SOME = prove
 (`(CHAR (Arrow) a (Arrow) a) f fv /\ a x xv /\
   OPTION_TYPE FILENAME (SOME s) fnv /\ CARD (set_of_list (MAP FST
     (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs) (256 EXP 8) ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_foldChars_v [fv; xv; fnv]
     (STDIO fs)
     (POSTv (?_STDIO retv) fs *
                  &(OPTION_TYPE a
                       (OPTION_MAP (mlvector_foldl f x) (file_content fs s))
                       retv))`,
  CHEAT_TAC);;

let foldChars_NONE = prove
 (`(CHAR (Arrow) a (Arrow) a) f fv /\ a x xv /\
   OPTION_TYPE FILENAME NONE fnv /\
   stdin_content fs = SOME text ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_foldChars_v [fv; xv; fnv]
     (STDIO fs)
     (POSTv (?_STDIO retv) (fastForwardFD fs 0) *
                  &(OPTION_TYPE a (SOME (mlvector_foldl f x text)) retv))`,
  CHEAT_TAC);;

let foldLines_SOME = prove
 (`CHAR c0 c0v /\
   (STRING_TYPE (Arrow) a (Arrow) a) f fv /\ a x xv /\
   OPTION_TYPE FILENAME (SOME s) fnv /\ CARD (set_of_list (MAP FST
     (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs) (256 EXP 8) ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_foldLines_v [c0v; fv; xv; fnv]
     (STDIO fs)
     (POSTv (?_STDIO retv) fs *
                  &(OPTION_TYPE a
                       (OPTION_MAP (mlvector_foldl f x o lines_of_gen c0 o
                         implode) (file_content fs s))
                       retv))`,
  CHEAT_TAC);;

let foldLines_NONE = prove
 (`CHAR c0 c0v /\
   (STRING_TYPE (Arrow) a (Arrow) a) f fv /\ a x xv /\
   OPTION_TYPE FILENAME NONE fnv /\
   stdin_content fs = SOME text ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     TextIO_foldLines_v [c0v; fv; xv; fnv]
     (STDIO fs)
     (POSTv (?_STDIO retv) (fastForwardFD fs 0) *
         &(OPTION_TYPE a (SOME (mlvector_foldl f x (lines_of_gen c0
           (implode text)))) retv))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["TYPE";
   "fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
