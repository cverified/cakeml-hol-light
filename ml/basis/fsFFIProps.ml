(* ======================================================== *)
(*  fsFFIProps: ported from HOL4's
    basis/fsFFIPropsScript.sml
    A proof theory about fsFFI.ml, with 19 definitions and 127
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  Lemmas about the file system model used by the proof about TextIO.
*)

needs "basis/Marshalling.ml";;
needs "basis/fsFFI.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "fsFFIProps"
  ["Marshalling"; "cfHeapsBase"; "fsFFI"; "mlstring"];;

let _ = do_list hide_constant ["stdin"];;

let numchars_self = prove
 (`!fs. fs = IO_fs_numchars_fupd (K (IO_fs_numchars fs)) fs`,
  CHEAT_TAC);;

(* we can actually open a file if the OS limit has not been reached and we can
* still encode the file descriptor on 8 bits *)
(* HOL4 fsFFIPropsScript.sml:23: the overload hasFreeFD, which the port
   expands *)

(* nextFD lemmas *)

let nextFD_ltX = prove
 (`CARD (set_of_list (MAP FST (IO_fs_infds fs))) < x ==> nextFD fs < x`,
  CHEAT_TAC);;

let nextFD_maxFD = prove
 (`CARD (set_of_list (MAP FST (IO_fs_infds fs))) < MIN (IO_fs_maxFD fs) (256
  EXP 8) ==> nextFD fs <= IO_fs_maxFD fs`,
  CHEAT_TAC);;

let nextFD_leX = prove
 (`CARD (set_of_list (MAP FST (IO_fs_infds fs))) <= x ==> nextFD fs <= x`,
  CHEAT_TAC);;

let nextFD_NOT_MEM = prove
 (`!f m n fs. ~(MEM (nextFD fs,f,m,n) (IO_fs_infds fs))`,
  CHEAT_TAC);;

let nextFD_numchars = prove
 (`!fs ll. nextFD (IO_fs_numchars_fupd (K ll) fs) = nextFD fs`,
  CHEAT_TAC);;

(* bumpFD lemmas *)

let bumpFD_numchars = prove
 (`!fs fd n ll. bumpFD fd (IO_fs_numchars_fupd (K ll) fs) n =
  IO_fs_numchars_fupd (K (THE (LTL ll)))
         (bumpFD fd fs n)`,
  CHEAT_TAC);;

let bumpFD_inode_tbl = prove
 (`IO_fs_inode_tbl
     (bumpFD fd fs n) = IO_fs_inode_tbl fs`,
  CHEAT_TAC);;
add_simp bumpFD_inode_tbl;;

let bumpFD_files = prove
 (`IO_fs_files
      (bumpFD fd fs n) = IO_fs_files fs`,
  CHEAT_TAC);;
add_simp bumpFD_files;;

let bumpFD_o = prove
 (`!fs fd n1 n2.
     bumpFD fd (bumpFD fd fs n1) n2 = IO_fs_numchars_fupd (K (THE (LTL (THE
       (LTL (IO_fs_numchars fs))))))
     (bumpFD fd fs (n1 + n2))`,
  CHEAT_TAC);;

let bumpFD_0 = prove
 (`bumpFD fd fs 0 = IO_fs_numchars_fupd (K (THE (LTL (IO_fs_numchars fs))))
  fs`,
  CHEAT_TAC);;

(* validFD lemmas *)

let validFD_numchars = prove
 (`!fd fs ll. validFD fd fs <=> validFD fd (IO_fs_numchars_fupd (K ll) fs)`,
  CHEAT_TAC);;

let validFD_bumpFD = prove
 (`validFD fd' fs ==> validFD fd' (bumpFD fd fs n)`,
  CHEAT_TAC);;

let validFD_ALOOKUP = prove
 (`validFD fd fs ==> (?v. ALOOKUP (IO_fs_infds fs) fd = SOME v)`,
  CHEAT_TAC);;

let ALOOKUP_validFD = prove
 (`ALOOKUP (IO_fs_infds fs) fd = SOME (fname,md,pos) ==> validFD fd fs`,
  CHEAT_TAC);;

let validFileFD_def = new_definition
  `validFileFD fd infds <=>
     (?fnm md off. ALOOKUP infds fd = SOME (File fnm,md,off))`;;

let validFD_nextFD = prove
 (`~(validFD (nextFD fs) fs)`,
  CHEAT_TAC);;

(* getNullTermStr lemmas *)

let getNullTermStr_add_null = prove
 (`!cs. ~(MEM (n2w 0) cs) ==> getNullTermStr (APPEND cs (CONS (n2w 0) ls)) =
  SOME (MAP (CHR o w2n) cs)`,
  CHEAT_TAC);;

let getNullTermStr_insert_atI = prove
 (`!cs l. LENGTH cs < LENGTH l /\ ~(MEM (n2w 0) cs) ==>
          getNullTermStr (insert_atI (APPEND cs [(n2w 0)]) 0 l) = SOME
            (MAP (CHR o w2n) cs)`,
  CHEAT_TAC);;

(* the filesystem will always eventually allow to write something *)

let live_numchars_def = new_definition
  `live_numchars ns <=>
     ~(LFINITE ns) /\
     always (eventually (\ll. ?k. LHD ll = SOME k /\ ~(k = 0))) ns`;;

let liveFS_def = new_definition
  `liveFS fs <=> live_numchars (IO_fs_numchars fs)`;;

(* each inode refered to by a filename has a content *)
let consistentFS_def = new_definition
  `consistentFS fs = (!fname ino. ALOOKUP (IO_fs_files fs) fname = SOME ino ==>
         (File ino) IN FDOM (alist_to_fmap (IO_fs_inode_tbl fs)))`;;

(* well formed file descriptor: all descriptors are <= maxFD
*  and correspond to file names in files *)

let wfFS_def = new_definition
  `wfFS fs =
     ((!fd. fd IN FDOM (alist_to_fmap (IO_fs_infds fs)) ==>
          fd <= IO_fs_maxFD fs /\
          (?ino off. ALOOKUP (IO_fs_infds fs) fd = SOME (ino,off) /\
                    ino IN FDOM (alist_to_fmap (IO_fs_inode_tbl fs)))) /\
      consistentFS fs /\ liveFS fs)`;;

let consistentFS_with_numchars = prove
 (`!fs ll. consistentFS fs ==> consistentFS (IO_fs_numchars_fupd (K ll) fs)`,
  CHEAT_TAC);;
add_simp consistentFS_with_numchars;;

let wfFS_numchars = prove
 (`!fs ll. wfFS fs ==> ~(LFINITE ll) ==>
           always (eventually (\ll. ?k. LHD ll = SOME k /\ ~(k = 0))) ll ==>
           wfFS (IO_fs_numchars_fupd (K ll) fs)`,
  CHEAT_TAC);;

let wfFS_LTL = prove
 (`!fs ll. wfFS (IO_fs_numchars_fupd (K ll) fs) ==>
           wfFS (IO_fs_numchars_fupd (K (THE (LTL ll))) fs)`,
  CHEAT_TAC);;

let wfFS_openFile = prove
 (`wfFS fs ==> wfFS (openFileFS fnm fs md off)`,
  CHEAT_TAC);;

let wfFS_ADELKEY = prove
 (`wfFS fs ==> wfFS (IO_fs_infds_fupd (ADELKEY k) fs)`,
  CHEAT_TAC);;
add_simp wfFS_ADELKEY;;

let wfFS_LDROP = prove
 (`wfFS fs ==> wfFS (IO_fs_numchars_fupd (K (THE (LDROP k (IO_fs_numchars
  fs)))) fs)`,
  CHEAT_TAC);;

let wfFS_bumpFD = prove
 (`wfFS fs ==> wfFS (bumpFD fd fs n)`,
  CHEAT_TAC);;
add_simp wfFS_bumpFD;;

(* end of file is reached when the position index is the length of the file *)

let eof_def = new_definition
  `eof fd fsys =
     OPTION_BIND (ALOOKUP (IO_fs_infds fsys) fd) (\(ino,md,pos). OPTION_BIND
       (ALOOKUP (IO_fs_inode_tbl fsys) ino) (\contents.
       SOME (LENGTH contents <= pos)))`;;

let eof_numchars = prove
 (`eof fd (IO_fs_numchars_fupd (K ll) fs) = eof fd fs`,
  CHEAT_TAC);;
add_simp eof_numchars;;

let wfFS_eof_EQ_SOME = prove
 (`wfFS fs /\ validFD fd fs ==>
   (?b. eof fd fs = SOME b)`,
  CHEAT_TAC);;

(* HOL4 fsFFIPropsScript.sml:302-314: code that the source has in a comment *)

let eof_read = prove
 (`!fd fs n fs'. 0 < n ==> fsFFI_read fd fs n = SOME ([],fs') ==> eof fd fs =
  SOME T`,
  CHEAT_TAC);;

(* HOL4 fsFFIPropsScript.sml:325-341: code that the source has in a comment *)

let get_file_content_eof = prove
 (`get_file_content fs fd = SOME (content,pos) ==> eof fd fs = SOME (~(pos <
  LENGTH content))`,
  CHEAT_TAC);;

(* inFS_fname *)

let inFS_fname_def = new_definition
  `inFS_fname fs s = (?ino. ALOOKUP (IO_fs_files fs) s = SOME ino)`;;

let not_inFS_fname_openFile = prove
 (`~(inFS_fname fs iname) ==> openFile iname fs md off = NONE`,
  CHEAT_TAC);;

let inFS_fname_ALOOKUP_EXISTS = prove
 (`!fs fname. consistentFS fs /\ inFS_fname fs fname ==>
    (?ino content.
      ALOOKUP (IO_fs_files fs) fname = SOME ino /\
      ALOOKUP (IO_fs_inode_tbl fs) (File ino) = SOME content)`,
  CHEAT_TAC);;

let ALOOKUP_SOME_inFS_fname = prove
 (`ALOOKUP (IO_fs_files fs) fnm = SOME ino ==> inFS_fname fs fnm`,
  CHEAT_TAC);;

let ALOOKUP_inFS_fname_openFileFS_nextFD = prove
 (`!fs f ino off md.
   consistentFS fs /\ inFS_fname fs f /\ nextFD fs <= IO_fs_maxFD fs /\
   ALOOKUP (IO_fs_files fs) f = SOME ino ==>
   ALOOKUP (IO_fs_infds (openFileFS f fs md off)) (nextFD fs) = SOME (File
     ino,md,off)`,
  CHEAT_TAC);;


let inFS_fname_numchars = prove
 (`!s fs ll. inFS_fname (IO_fs_numchars_fupd (K ll) fs) s = inFS_fname fs s`,
  CHEAT_TAC);;

(* ffi lengths *)

let ffi_open_in_length = prove
 (`ffi_open_in conf bytes fs = SOME (FFIreturn bytes' fs') ==> LENGTH bytes'
  = LENGTH bytes`,
  CHEAT_TAC);;

let ffi_open_out_length = prove
 (`ffi_open_out conf bytes fs = SOME (FFIreturn bytes' fs') ==> LENGTH bytes'
  = LENGTH bytes`,
  CHEAT_TAC);;

let read_length = prove
 (`fsFFI_read fd fs k = SOME (l,fs') ==> LENGTH l <= k`,
  CHEAT_TAC);;

let ffi_read_length = prove
 (`ffi_read conf bytes fs = SOME (FFIreturn bytes' fs') ==> LENGTH bytes' =
  LENGTH bytes`,
  CHEAT_TAC);;

let ffi_write_length = prove
 (`ffi_write conf bytes fs = SOME (FFIreturn bytes' fs') ==> LENGTH bytes' =
  LENGTH bytes`,
  CHEAT_TAC);;

let ffi_close_length = prove
 (`ffi_close conf bytes fs = SOME (FFIreturn bytes' fs') ==> LENGTH bytes' =
  LENGTH bytes`,
  CHEAT_TAC);;

(* fastForwardFD *)

let fastForwardFD_def = new_definition
  `fastForwardFD fs fd =
     the fs (OPTION_BIND (ALOOKUP (IO_fs_infds fs) fd) (\(ino,md,off).
       OPTION_BIND (ALOOKUP (IO_fs_inode_tbl fs) ino) (\content.
       SOME (IO_fs_infds_fupd (AFUPDKEY fd (I ## I ## MAX (LENGTH
         content))) fs))))`;;

let validFD_fastForwardFD = prove
 (`validFD fd (fastForwardFD fs fd) = validFD fd fs`,
  CHEAT_TAC);;
add_simp validFD_fastForwardFD;;

let validFileFD_fastForwardFD = prove
 (`validFileFD fd (IO_fs_infds (fastForwardFD fs x)) <=> validFileFD fd
  (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp validFileFD_fastForwardFD;;

let fastForwardFD_inode_tbl = prove
 (`IO_fs_inode_tbl
      (fastForwardFD fs fd) = IO_fs_inode_tbl fs`,
  CHEAT_TAC);;
add_simp fastForwardFD_inode_tbl;;

let fastForwardFD_files = prove
 (`!fs fd. IO_fs_files (fastForwardFD fs fd) = IO_fs_files fs`,
  CHEAT_TAC);;
add_simp fastForwardFD_files;;

let ADELKEY_fastForwardFD_elim = prove
 (`ADELKEY fd (IO_fs_infds (fastForwardFD fs fd)) = ADELKEY fd (IO_fs_infds
  fs)`,
  CHEAT_TAC);;
add_simp ADELKEY_fastForwardFD_elim;;

let fastForwardFD_ADELKEY_same = prove
 (`IO_fs_infds_fupd (ADELKEY fd)
      (fastForwardFD fs fd) = IO_fs_infds_fupd (ADELKEY fd)
      fs`,
  CHEAT_TAC);;
add_simp fastForwardFD_ADELKEY_same;;

let fastForwardFD_0 = prove
 (`(!content pos. get_file_content fs fd = SOME (content,pos) ==> LENGTH
  content <= pos) ==>
   fastForwardFD fs fd = fs`,
  CHEAT_TAC);;

let fastForwardFD_with_numchars = prove
 (`fastForwardFD (IO_fs_numchars_fupd (K ns) fs) fd = IO_fs_numchars_fupd (K
  ns) (fastForwardFD fs fd)`,
  CHEAT_TAC);;

let fastForwardFD_numchars = prove
 (`IO_fs_numchars
      (fastForwardFD fs fd) = IO_fs_numchars fs`,
  CHEAT_TAC);;
add_simp fastForwardFD_numchars;;

let fastForwardFD_maxFD = prove
 (`IO_fs_maxFD
      (fastForwardFD fs fd) = IO_fs_maxFD fs`,
  CHEAT_TAC);;
add_simp fastForwardFD_maxFD;;

let wfFS_fastForwardFD = prove
 (`!fs fd. validFD fd fs /\ wfFS fs ==> wfFS (fastForwardFD fs fd)`,
  CHEAT_TAC);;
add_simp wfFS_fastForwardFD;;

let fsupdate_fastForwardFD_comm = prove
 (`!fs fd1 fd2 k p c.
     ALOOKUP (IO_fs_infds fs) fd1 = SOME (ino1,r,pos1) /\
     ALOOKUP (IO_fs_infds fs) fd2 = SOME (ino2,r',pos2) /\
     ALOOKUP (IO_fs_inode_tbl fs) ino1 = SOME content1 /\
     ALOOKUP (IO_fs_inode_tbl fs) ino2 = SOME content2 /\ ~(ino1 = ino2) ==>
         fsupdate (fastForwardFD fs fd1) fd2 k p c =
         fastForwardFD (fsupdate fs fd2 k p c) fd1`,
  CHEAT_TAC);;

(* fsupdate *)

let wfFS_fsupdate = prove
 (`!fs fd content pos k. wfFS fs ==> MEM fd (MAP FST (IO_fs_infds fs)) ==>
                          wfFS (fsupdate fs fd k pos content)`,
  CHEAT_TAC);;

let fsupdate_unchanged = prove
 (`get_file_content fs fd = SOME (content,pos) ==>
     fsupdate fs fd 0 pos content = fs`,
  CHEAT_TAC);;

let fsupdate_o = prove
 (`liveFS fs ==>
   fsupdate (fsupdate fs fd k1 pos1 c1) fd k2 pos2 c2 =
   fsupdate fs fd (k1 + k2) pos2 c2`,
  CHEAT_TAC);;

let fsupdate_o_0 = prove
 (`fsupdate (fsupdate fs fd 0 pos1 c1) fd 0 pos2 c2 =
   fsupdate fs fd 0 pos2 c2`,
  CHEAT_TAC);;
add_simp fsupdate_o_0;;

let fsupdate_comm = prove
 (`!fs fd1 fd2 k1 p1 c1 fnm1 pos1 k2 p2 c2 fnm2 pos2.
     ALOOKUP (IO_fs_infds fs) fd1 = SOME (fnm1,pos1) /\
     ALOOKUP (IO_fs_infds fs) fd2 = SOME (fnm2,pos2) /\ ~(fnm1 = fnm2)
       /\ ~(fd1 = fd2) /\ ~(LFINITE (IO_fs_numchars fs)) ==>
   fsupdate (fsupdate fs fd1 k1 p1 c1) fd2 k2 p2 c2 =
   fsupdate (fsupdate fs fd2 k2 p2 c2) fd1 k1 p1 c1`,
  CHEAT_TAC);;

let fsupdate_MAP_FST_infds = prove
 (`MAP FST (IO_fs_infds (fsupdate fs fd k pos c)) = MAP FST (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp fsupdate_MAP_FST_infds;;

let fsupdate_MAP_FST_inode_tbl = prove
 (`MAP FST (IO_fs_inode_tbl (fsupdate fs fd k pos c)) = MAP FST
  (IO_fs_inode_tbl fs)`,
  CHEAT_TAC);;
add_simp fsupdate_MAP_FST_inode_tbl;;

let fsupdate_MAP_FST_files = prove
 (`MAP FST (IO_fs_files (fsupdate fs fd k pos c)) = MAP FST (IO_fs_files fs)`,
  CHEAT_TAC);;
add_simp fsupdate_MAP_FST_files;;

let validFD_fsupdate = prove
 (`validFD fd (fsupdate fs fd' x y z) <=> validFD fd fs`,
  CHEAT_TAC);;
add_simp validFD_fsupdate;;

let validFileFD_fsupdate = prove
 (`validFileFD fd (IO_fs_infds (fsupdate fs fd' x y z)) <=> validFileFD fd
  (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp validFileFD_fsupdate;;

let fsupdate_numchars = prove
 (`!fs fd k p c ll. IO_fs_numchars_fupd (K ll) (fsupdate fs fd k p c) =
                    fsupdate (IO_fs_numchars_fupd (K ll) fs) fd 0 p c`,
  CHEAT_TAC);;

let fsupdate_ADELKEY = prove
 (`~(fd = fd') ==>
      fsupdate (IO_fs_infds_fupd (ADELKEY fd') fs) fd k pos content =
        IO_fs_infds_fupd (ADELKEY fd')
      (fsupdate fs fd k pos content)`,
  CHEAT_TAC);;

let fsupdate_0_numchars = prove
 (`IS_SOME (ALOOKUP (IO_fs_infds fs) fd) ==>
   fsupdate fs fd n pos content =
   fsupdate (IO_fs_numchars_fupd (K (THE (LDROP n (IO_fs_numchars fs))))
     fs) fd 0 pos content`,
  CHEAT_TAC);;

let fsupdate_maxFD = prove
 (`!fs fd k pos content. IO_fs_maxFD
    (fsupdate fs fd k pos content) = IO_fs_maxFD fs`,
  CHEAT_TAC);;
add_simp fsupdate_maxFD;;

(* get_file_content *)

let get_file_content_numchars = prove
 (`!fs fd. get_file_content fs fd =
               get_file_content (IO_fs_numchars_fupd (K ll) fs) fd`,
  CHEAT_TAC);;

let get_file_content_validFD = prove
 (`get_file_content fs fd = SOME (c,p) ==> validFD fd fs`,
  CHEAT_TAC);;

let get_file_content_fsupdate = prove
 (`!fs fd x i c u. get_file_content fs fd = SOME u ==>
   get_file_content (fsupdate fs fd x i c) fd = SOME (c,i)`,
  CHEAT_TAC);;

let get_file_content_fsupdate_unchanged = prove
 (`!fs fd u fnm pos fd' fnm' pos' x i c.
   get_file_content fs fd = SOME u ==>
   ALOOKUP (IO_fs_infds fs) fd = SOME (fnm,pos) ==>
   ALOOKUP (IO_fs_infds fs) fd' = SOME (fnm',pos') ==> ~(fnm = fnm') ==>
   get_file_content (fsupdate fs fd' x i c) fd = SOME u`,
  CHEAT_TAC);;

let get_file_content_bumpFD = prove
 (`!fs fd c pos n.
    get_file_content (bumpFD fd fs n) fd =
    OPTION_MAP (I ## (+) n) (get_file_content fs fd)`,
  CHEAT_TAC);;
add_simp get_file_content_bumpFD;;

(* liveFS *)

let liveFS_openFileFS = prove
 (`liveFS fs ==> liveFS (openFileFS s fs md n)`,
  CHEAT_TAC);;

let liveFS_fsupdate = prove
 (`liveFS fs ==> liveFS (fsupdate fs fd n k c)`,
  CHEAT_TAC);;

let liveFS_bumpFD = prove
 (`liveFS fs ==> liveFS (bumpFD fd fs k)`,
  CHEAT_TAC);;

(* openFile, openFileFS *)

let openFile_fupd_numchars = prove
 (`!s fs k ll fd fs'. openFile s (IO_fs_numchars_fupd (K ll) fs) md k =
       match openFile s fs md k with
         SOME (fd,fs') -> SOME (fd,IO_fs_numchars_fupd (K ll) fs')
       | NONE -> NONE`,
  CHEAT_TAC);;

let openFileFS_numchars = prove
 (`!s fs k. IO_fs_numchars (openFileFS s fs md k) = IO_fs_numchars fs`,
  CHEAT_TAC);;
add_simp openFileFS_numchars;;

let openFileFS_inode_tbl = prove
 (`!s fs k md. IO_fs_inode_tbl (openFileFS s fs md k) = IO_fs_inode_tbl fs`,
  CHEAT_TAC);;
add_simp openFileFS_inode_tbl;;

let openFileFS_files = prove
 (`!s fs k md. IO_fs_files (openFileFS s fs md k) = IO_fs_files fs`,
  CHEAT_TAC);;
add_simp openFileFS_files;;

let wfFS_openFileFS = prove
 (`!f fs k md. CARD (FDOM (alist_to_fmap (IO_fs_infds fs))) <= IO_fs_maxFD fs
  /\ wfFS fs ==>
                   wfFS (openFileFS f fs md k)`,
  CHEAT_TAC);;

let openFileFS_maxFD = prove
 (`IO_fs_maxFD
      (openFileFS f fs md pos) = IO_fs_maxFD fs`,
  CHEAT_TAC);;
add_simp openFileFS_maxFD;;

let openFileFS_fupd_numchars = prove
 (`!s fs k ll. openFileFS s (IO_fs_numchars_fupd (K ll) fs) md k =
               (IO_fs_numchars_fupd (K ll) (openFileFS s fs md k))`,
  CHEAT_TAC);;

let IS_SOME_get_file_content_openFileFS_nextFD = prove
 (`!fs f off md.
   consistentFS fs /\ inFS_fname fs f /\ nextFD fs <= IO_fs_maxFD fs ==>
     IS_SOME (get_file_content (openFileFS f fs md off) (nextFD fs))`,
  CHEAT_TAC);;

let ADELKEY_nextFD_openFileFS = prove
 (`nextFD fs <= IO_fs_maxFD fs ==>
   ADELKEY (nextFD fs) (IO_fs_infds (openFileFS f fs md off)) =
     IO_fs_infds fs`,
  CHEAT_TAC);;
add_simp ADELKEY_nextFD_openFileFS;;

let openFileFS_ADELKEY_nextFD = prove
 (`nextFD fs <= IO_fs_maxFD fs ==> IO_fs_infds_fupd (ADELKEY (nextFD fs))
   (openFileFS f fs md off) = fs`,
  CHEAT_TAC);;

(* forwardFD: like bumpFD but leave numchars *)

let forwardFD_def = new_definition
  `forwardFD fs fd n = IO_fs_infds_fupd (AFUPDKEY fd (I ## I ## (+) n))
     fs`;;

let forwardFD_const = prove
 (`IO_fs_files
      (forwardFD fs fd n) = IO_fs_files fs /\ IO_fs_inode_tbl
      (forwardFD fs fd n) = IO_fs_inode_tbl fs /\ IO_fs_numchars
      (forwardFD fs fd n) = IO_fs_numchars fs /\ IO_fs_maxFD
      (forwardFD fs fd n) = IO_fs_maxFD fs`,
  CHEAT_TAC);;
add_simp forwardFD_const;;

let forwardFD_o = prove
 (`forwardFD (forwardFD fs fd n) fd m = forwardFD fs fd (n + m)`,
  CHEAT_TAC);;

let forwardFD_0 = prove
 (`forwardFD fs fd 0 = fs`,
  CHEAT_TAC);;
add_simp forwardFD_0;;

let forwardFD_numchars = prove
 (`forwardFD (IO_fs_numchars_fupd (K ll) fs) fd n = IO_fs_numchars_fupd (K
  ll) (forwardFD fs fd n)`,
  CHEAT_TAC);;

let liveFS_forwardFD = prove
 (`liveFS (forwardFD fs fd n) = liveFS fs`,
  CHEAT_TAC);;
add_simp liveFS_forwardFD;;

let MAP_FST_forwardFD_infds = prove
 (`MAP FST (IO_fs_infds (forwardFD fs fd n)) = MAP FST (IO_fs_infds fs)`,
  CHEAT_TAC);;
add_simp MAP_FST_forwardFD_infds;;

let validFD_forwardFD = prove
 (`validFD fd (forwardFD fs fd n) = validFD fd fs`,
  CHEAT_TAC);;
add_simp validFD_forwardFD;;

let wfFS_forwardFD = prove
 (`wfFS (forwardFD fs fd n) = wfFS fs`,
  CHEAT_TAC);;
add_simp wfFS_forwardFD;;

let get_file_content_forwardFD = prove
 (`!fs fd c pos n.
    get_file_content (forwardFD fs fd n) fd =
    OPTION_MAP (I ## (+) n) (get_file_content fs fd)`,
  CHEAT_TAC);;
add_simp get_file_content_forwardFD;;

let bumpFD_forwardFD = prove
 (`bumpFD fd fs n = IO_fs_numchars_fupd (K (THE (LTL (IO_fs_numchars fs))))
  (forwardFD fs fd n)`,
  CHEAT_TAC);;

let fastForwardFD_forwardFD = prove
 (`get_file_content fs fd = SOME (content,pos) /\ pos + n <= LENGTH content ==>
   fastForwardFD (forwardFD fs fd n) fd = fastForwardFD fs fd`,
  CHEAT_TAC);;

let forwardFD_ADELKEY_same = prove
 (`IO_fs_infds_fupd (ADELKEY fd)
      (forwardFD fs fd n) = IO_fs_infds_fupd (ADELKEY fd) fs`,
  CHEAT_TAC);;

(* lineFD: the next line *)

let lineFD_def = new_definition
  `lineFD fs fd = OPTION_BIND (get_file_content fs fd) (\(content,pos).
     OPTION_IGNORE_BIND (assert (pos < LENGTH content)) (
     let (l,r) = SPLITP ((=) (CHR 10)) (DROP pos content) in
       SOME (APPEND l "\n")))`;;

(* linesFD: get all the lines *)

let linesFD_def = new_definition
  `linesFD fs fd =
     match get_file_content fs fd with NONE -> []
     | SOME (content,pos) ->
         MAP (\x. APPEND x "\n")
           (splitlines (DROP pos content))`;;

let linesFD_nil_lineFD_NONE = prove
 (`linesFD fs fd = [] <=> lineFD fs fd = NONE`,
  CHEAT_TAC);;


let lines_of_def = new_definition
  `lines_of str =
     MAP (\x. strcat (implode x) (implode "\n"))
           (splitlines (explode str))`;;

(* all_lines_inode: get all the lines based on an inode *)

(* HOL4 fsFFIPropsScript.sml:1034-1035: the overload all_lines_inode, which
   the port expands *)

(* all_lines_file: get all the lines based on filename *)

let all_lines_file_def = new_definition
  `all_lines_file fs fname =
     (\fs ino. lines_of (implode (THE (ALOOKUP (IO_fs_inode_tbl fs)
       ino)))) fs (File (THE (ALOOKUP (IO_fs_files fs) fname)))`;;

let all_lines_stdin_def = new_definition
  `all_lines_stdin fs = (\fs ino. lines_of (implode (THE (ALOOKUP
  (IO_fs_inode_tbl fs) ino)))) fs (UStream (implode "stdin"))`;;

let all_lines_from_def = define_cases
  `(all_lines_from fs NONE = all_lines_stdin fs) /\
   (all_lines_from fs (SOME fname) = all_lines_file fs fname)`;;

let concat_lines_of = prove
 (`!s. mlstring_concat (lines_of s) = s \/
        mlstring_concat (lines_of s) = strcat s (integer_word_toString
          (CHR 10))`,
  CHEAT_TAC);;

let concat_all_lines_file = prove
 (`mlstring_concat (all_lines_file fs fname) = implode (THE (ALOOKUP
  (IO_fs_inode_tbl fs) (File (THE (ALOOKUP (IO_fs_files fs) fname))))) \/
   mlstring_concat (all_lines_file fs fname) = strcat (implode (THE
     (ALOOKUP (IO_fs_inode_tbl fs) (File (THE (ALOOKUP (IO_fs_files fs)
     fname)))))) (integer_word_toString (CHR 10))`,
  CHEAT_TAC);;

let all_lines_file_with_numchars = prove
 (`all_lines_file (IO_fs_numchars_fupd (K ns) fs) = all_lines_file fs`,
  CHEAT_TAC);;

let linesFD_openFileFS_nextFD = prove
 (`consistentFS fs /\ inFS_fname fs f /\ nextFD fs <= IO_fs_maxFD fs ==>
   linesFD (openFileFS f fs md 0) (nextFD fs) = MAP explode
     (all_lines_file fs f)`,
  CHEAT_TAC);;

(* lineForwardFD: seek past the next line *)

let lineForwardFD_def = new_definition
  `fsFFIProps_lineForwardFD fs fd =
     match get_file_content fs fd with NONE -> fs
     | SOME (content,pos) ->
       if pos < LENGTH content then let (l,r) = SPLITP ((=) (CHR 10)) (DROP
         pos content) in
         forwardFD fs fd (LENGTH l + (if NULL r then 0 else 1))
       else fs`;;

let fastForwardFD_lineForwardFD = prove
 (`fastForwardFD (fsFFIProps_lineForwardFD fs fd) fd = fastForwardFD fs fd`,
  CHEAT_TAC);;
add_simp fastForwardFD_lineForwardFD;;

let IS_SOME_get_file_content_lineForwardFD = prove
 (`IS_SOME (get_file_content (fsFFIProps_lineForwardFD fs fd) fd) =
   IS_SOME (get_file_content fs fd)`,
  CHEAT_TAC);;
add_simp IS_SOME_get_file_content_lineForwardFD;;

let lineFD_NONE_lineForwardFD_fastForwardFD = prove
 (`lineFD fs fd = NONE ==>
   fsFFIProps_lineForwardFD fs fd = fastForwardFD fs fd`,
  CHEAT_TAC);;

let linesFD_cons_imp = prove
 (`linesFD fs fd = CONS ln ls ==>
   lineFD fs fd = SOME ln /\
   linesFD (fsFFIProps_lineForwardFD fs fd) fd = ls`,
  CHEAT_TAC);;

let linesFD_lineForwardFD = prove
 (`linesFD (fsFFIProps_lineForwardFD fs fd) fd' =
   if fd = fd' then
     DROP 1 (linesFD fs fd)
   else linesFD fs fd'`,
  CHEAT_TAC);;

let lineForwardFD_forwardFD = prove
 (`!fs fd. ?n. fsFFIProps_lineForwardFD fs fd = forwardFD fs fd n`,
  CHEAT_TAC);;

let get_file_content_lineForwardFD_forwardFD = prove
 (`!fs fd. get_file_content fs fd = SOME (x,pos) ==>
     fsFFIProps_lineForwardFD fs fd = forwardFD fs fd (LENGTH (FST (SPLITP
       ((=) (CHR 10)) (DROP pos x))) +
                              (if NULL (SND (SPLITP ((=) (CHR 10)) (DROP
                                pos x))) then 0 else 1))`,
  CHEAT_TAC);;

(* Property ensuring that standard streams are correctly opened *)
let STD_streams_def = new_definition
  `STD_streams fs = (?inp out err.
     (ALOOKUP (IO_fs_inode_tbl fs) (UStream (implode "stdout")) = SOME out)
       /\
     (ALOOKUP (IO_fs_inode_tbl fs) (UStream (implode "stderr")) = SOME err)
       /\
     (!fd md off. ALOOKUP (IO_fs_infds fs) fd = SOME (UStream (implode
       "stdin"),md,off) <=> fd = 0 /\ md = ReadMode /\ off = inp) /\
     (!fd md off. ALOOKUP (IO_fs_infds fs) fd = SOME (UStream (implode
       "stdout"),md,off) <=> fd = 1 /\ md = WriteMode /\ off = LENGTH out) /\
     (!fd md off. ALOOKUP (IO_fs_infds fs) fd = SOME (UStream (implode
       "stderr"),md,off) <=> fd = 2 /\ md = WriteMode /\ off = LENGTH err))`;;

let STD_streams_fsupdate = prove
 (`!fs fd k pos c.
   ((fd = 1 \/ fd = 2) ==> LENGTH c = pos) /\
    // (fd >= 3 ==> (FST(THE (ALOOKUP fs.infds fd)) <> UStream «stdout» /\
    // FST(THE (ALOOKUP fs.infds fd)) <> UStream «stderr»)) /\
    STD_streams fs ==>
    STD_streams (fsupdate fs fd k pos c)`,
  CHEAT_TAC);;

let STD_streams_openFileFS = prove
 (`!fs s k. STD_streams fs ==> STD_streams (openFileFS s fs md k)`,
  CHEAT_TAC);;

let STD_streams_numchars = prove
 (`!fs ll. STD_streams fs = STD_streams (IO_fs_numchars_fupd (K ll) fs)`,
  CHEAT_TAC);;

(* lemma[local] *)
let fsFFIProps_lemma = prove
 (`~(UStream (implode "stdin") = UStream (implode "stdout")) /\ ~(UStream
  (implode "stdin") = UStream (implode "stderr")) /\ ~(UStream (implode
  "stdout") = UStream (implode "stderr"))`,
  CHEAT_TAC);;

let STD_streams_forwardFD = prove
 (`~(fd = 1) /\ ~(fd = 2) ==>
      (STD_streams (forwardFD fs fd n) = STD_streams fs)`,
  CHEAT_TAC);;

let STD_streams_bumpFD = prove
 (`~(fd = 1) /\ ~(fd = 2) ==>
      (STD_streams (bumpFD fd fs n) = STD_streams fs)`,
  CHEAT_TAC);;

let STD_streams_nextFD = prove
 (`STD_streams fs ==> 3 <= nextFD fs`,
  CHEAT_TAC);;

let STD_streams_lineForwardFD = prove
 (`~(fd = 1) /\ ~(fd = 2) ==>
      (STD_streams (fsFFIProps_lineForwardFD fs fd) <=> STD_streams fs)`,
  CHEAT_TAC);;

let STD_streams_fastForwardFD = prove
 (`~(fd = 1) /\ ~(fd = 2) ==>
      (STD_streams (fastForwardFD fs fd) <=> STD_streams fs)`,
  CHEAT_TAC);;

let get_file_content_stdout = prove
 (`STD_streams fs ==>
   (?content pos. get_file_content fs 1 = SOME (content,pos))`,
  CHEAT_TAC);;

let get_file_content_stderr = prove
 (`STD_streams fs ==>
   (?content pos. get_file_content fs 2 = SOME (content,pos))`,
  CHEAT_TAC);;

let get_mode_def = new_definition
  `get_mode fs fd =
     OPTION_MAP (FST o SND) (ALOOKUP (IO_fs_infds fs) fd)`;;

let get_mode_with_numchars = prove
 (`get_mode (IO_fs_numchars_fupd (K ll) fs) fd = get_mode fs fd`,
  CHEAT_TAC);;

let get_mode_with_files = prove
 (`get_mode (IO_fs_files_fupd (K n) fs) fd = get_mode fs fd`,
  CHEAT_TAC);;

let get_mode_fsupdate = prove
 (`get_mode (fsupdate fs fd' k pos content) fd = get_mode fs fd`,
  CHEAT_TAC);;
add_simp get_mode_fsupdate;;

let get_mode_forwardFD = prove
 (`get_mode (forwardFD fs fd n) fd' = get_mode fs fd'`,
  CHEAT_TAC);;
add_simp get_mode_forwardFD;;

let get_mode_lineForwardFD = prove
 (`get_mode (fsFFIProps_lineForwardFD fs fd) fd' = get_mode fs fd'`,
  CHEAT_TAC);;
add_simp get_mode_lineForwardFD;;

let STD_streams_get_mode = prove
 (`STD_streams fs ==>
   (get_mode fs 0 = SOME ReadMode) /\
   (get_mode fs 1 = SOME WriteMode) /\
   (get_mode fs 2 = SOME WriteMode)`,
  CHEAT_TAC);;

(* HOL4 fsFFIPropsScript.sml:1484-1486: the overload hard_link, which the
   port expands *)

let pipe_def = new_definition
  `pipe fs (fdin,fdout) c =
     (?ino ipos. ALOOKUP (IO_fs_infds fs) fdin = SOME (UStream
       ino,ReadMode,ipos) /\
             ALOOKUP (IO_fs_infds fs) fdout = SOME (UStream
               ino,WriteMode,LENGTH c) /\
             ALOOKUP (IO_fs_inode_tbl fs) (UStream ino) = SOME c)`;;

let validFileFD_forwardFD = prove
 (`validFileFD fd (IO_fs_infds (forwardFD fs x y)) <=> validFileFD fd
  (IO_fs_infds fs)`,
  CHEAT_TAC);;

let validFileFD_nextFD = prove
 (`inFS_fname fs f /\ consistentFS fs /\ nextFD fs <= IO_fs_maxFD fs ==>
   validFileFD (nextFD fs) (IO_fs_infds (openFileFS f fs ReadMode 0))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["stdin"];;

(* and the interface *)
let _ = unhide_overloads ();;
