(* ======================================================== *)
(*  fsFFI: ported from HOL4's
    basis/fsFFIScript.sml
    A definition theory, with 24 definitions, 3 datatypes and 8
    theorems.  Needed by TextIOProof.ml, ag32BootstrapProof.ml,
    ag32_basis_ffiProof.ml, basis_ffi.ml and fsFFIProps.ml.  *)
(* ======================================================== *)

(*
  Logical model of filesystem and I/O streams
*)

needs "basis/Marshalling.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/encoders/asm/asmSem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "fsFFI"
  ["Marshalling"; "cfHeapsBase"; "mlstring"];;

let _ = do_list hide_constant ["decode"];;


(* Logical model of filesystem and I/O streams *)

(* regular files and unnamed streams *)
let inode_INDUCT,inode_RECURSION = define_datatype
  "inode =
     UStream mlstring
   | File mlstring";;

(* HOL4 fsFFIScript.sml:20: the overload isFile, which the port expands *)

let mode_INDUCT,mode_RECURSION = define_datatype
  "mode =
     ReadMode
   | WriteMode";;

(* inode_tbl: maps each existing inode to its content
*  files: maps each filename to its inode identifier
*  infds: descriptor * (filename * mode * position)
*  numchars: stream of num modeling the nondeterministic output of read and
*    write
* maxFD:
* file descriptors are encoded on 8 bytes but there might be OS limits
*  so we define this limit as maxFD
*  ulimit -n has a usual value of 1024
*)

let IO_fs_FIELDS = define_record "IO_fs"
  ["inode_tbl","(inode#char list) list";
   "files","(mlstring#mlstring) list";
   "infds","(num#inode#mode#num) list";
   "numchars","num llist";
   "maxFD","num"];;

(* HOL4 fsFFIScript.sml:46: ML code, not ported *)

let with_same_numchars = prove
 (`IO_fs_numchars_fupd (K (IO_fs_numchars fs))
      fs = fs`,
  CHEAT_TAC);;

let get_file_content_def = new_definition
  `get_file_content fs fd =
     OPTION_BIND (ALOOKUP (IO_fs_infds fs) fd) (\(ino,md,off). OPTION_BIND
       (ALOOKUP (IO_fs_inode_tbl fs) ino) (\c.
       SOME (c,off)))`;;

(* find smallest unused descriptor index *)
let nextFD_def = new_definition
  `nextFD fsys = (minimal n. ~(MEM n (MAP FST (IO_fs_infds fsys))))`;;

(* adds a new file in infds *)
let openFile_def = new_definition
  `openFile fnm fsys md pos =
      (let fd = nextFD fsys in
           OPTION_IGNORE_BIND (assert (fd <= IO_fs_maxFD fsys)) (OPTION_BIND
             (ALOOKUP (IO_fs_files fsys) fnm) (\iname.
           OPTION_IGNORE_BIND (ALOOKUP (IO_fs_inode_tbl fsys) (File iname))
             (
           SOME (fd,IO_fs_infds_fupd (K (CONS (nextFD fsys,(File
             iname,md,pos)) (IO_fs_infds fsys))) fsys)))))`;;

let openFileFS_def = new_definition
  `openFileFS fnm fs md pos =
     match openFile fnm fs md pos with
       NONE -> fs
     | SOME (_,fs') -> fs'`;;

(* adds a new file in infds and truncate it *)
let openFile_truncate_def = new_definition
  `openFile_truncate fnm fsys md =
     (let fd = nextFD fsys in
         OPTION_IGNORE_BIND (assert (fd <= IO_fs_maxFD fsys)) (OPTION_BIND
           (ALOOKUP (IO_fs_files fsys) fnm) (\iname.
         OPTION_IGNORE_BIND (ALOOKUP (IO_fs_inode_tbl fsys) (File iname)) (
         SOME (fd,
                           IO_fs_inode_tbl_fupd (AFUPDKEY (File iname)
                             (\x. "")) (IO_fs_infds_fupd (K (CONS (nextFD
                             fsys,(File iname,md,0)) (IO_fs_infds fsys)))
                             fsys))))))`;;

(* checks if a descriptor index is in infds *)
let validFD_def = new_definition
  `validFD fd fs <=> fd IN FDOM (alist_to_fmap (IO_fs_infds fs))`;;

(* increase by n the position in file descriptor and dump numchar's head *)
let bumpFD_def = new_definition
  `bumpFD fd fs n =
                        IO_fs_numchars_fupd (K (THE (LTL (IO_fs_numchars
                          fs)))) (IO_fs_infds_fupd (AFUPDKEY fd (I ## I ##
                          ((+) n))) fs)`;;

(* reads several chars and update position *)
let fsFFI_read_def = new_definition
  `fsFFI_read fd fs n =
     OPTION_BIND (ALOOKUP (IO_fs_infds fs) fd) (\(ino,md,off).
       OPTION_IGNORE_BIND (assert (md = ReadMode)) (OPTION_BIND (ALOOKUP
         (IO_fs_inode_tbl fs) ino) (\content. OPTION_BIND (LHD (IO_fs_numchars
         fs)) (\strm.
       let k = MIN n (MIN (LENGTH content - off) (SUC strm)) in
       SOME (TAKE k (DROP off content),bumpFD fd fs k)))))`;;

(* replaces the content of the file in fs with filename fnm,
* set the position in the file and skip k fsnumchars elements*)
let fsupdate_def = new_definition
  `fsupdate fs fd k pos content =
     (match ALOOKUP (IO_fs_infds fs) fd with NONE -> fs | SOME (fnm,_) ->
     (IO_fs_infds_fupd (K ((AFUPDKEY fd (I ## I ## (K pos))) (IO_fs_infds
       fs))) (IO_fs_numchars_fupd (K (THE (LDROP k (IO_fs_numchars fs))))
       (IO_fs_inode_tbl_fupd (K (AFUPDKEY fnm (K content) (IO_fs_inode_tbl
       fs))) fs))))`;;

(* "The write function returns the number of bytes successfully written into the
*  array, which may at times be less than the specified nbytes. It returns -1 if
*  an exceptional condition is encountered." *)
(* can it be 0? *)

let fsFFI_write_def = new_definition
  `fsFFI_write fd n chars fs =
     OPTION_BIND (ALOOKUP (IO_fs_infds fs) fd) (\(ino,md,off).
       OPTION_IGNORE_BIND (assert (md = WriteMode)) (OPTION_BIND (ALOOKUP
         (IO_fs_inode_tbl fs) ino) (\content.
       OPTION_IGNORE_BIND (assert (n <= LENGTH chars)) (
       OPTION_IGNORE_BIND (assert (~(IO_fs_numchars fs = LNIL)))
         (OPTION_BIND (LHD (IO_fs_numchars fs)) (\strm.
       let k = MIN n strm in
         // an unspecified error occurred
         SOME (k,fsupdate fs fd 1 (off + k)
                             (APPEND (APPEND (TAKE off content)
                              (TAKE k chars))
                              (DROP (off + k) content)))))))))`;;


(* remove file from infds *)
let closeFD_def = new_definition
  `closeFD fd fsys =
     OPTION_BIND (ALOOKUP (IO_fs_infds fsys) fd) (\(fnm,md,off).
        OPTION_IGNORE_BIND (assert ((\inode. ?fnm. inode = File fnm) fnm)) (
        SOME (one,IO_fs_infds_fupd (K (ADELKEY fd (IO_fs_infds fsys)))
          fsys)))`;;


(* Specification of the FFI functions operating on the above model:
    - open_in
    - open_out
    - read
    - write
    - close
*)

(* truncate byte list after null byte and convert into char list *)
let getNullTermStr_def = new_definition
  `getNullTermStr (bytes:word8 list) =
      let sz = indexedLists_findi (n2w 0) bytes in
        if sz = LENGTH bytes then NONE
        else SOME (MAP (CHR o w2n) (TAKE sz bytes))`;;

(* read file name from the first non null bytes
*  open the file with read access
*  return result code in first byte
*  write its file descriptor index in the second byte *)
let ffi_open_in_def = new_definition
  `ffi_open_in (conf:word8 list) bytes fs = APPEND (
       OPTION_IGNORE_BIND (assert (9 <= LENGTH bytes)) (OPTION_BIND
         (getNullTermStr conf) (\fname. OPTION_BIND (openFile (implode fname)
         fs ReadMode 0) (\(fd,fs').
       SOME (FFIreturn (APPEND (CONS (n2w 0) (n2w8 fd)) (DROP 9 bytes))
         fs')))))
     (
       OPTION_IGNORE_BIND (assert (0 < LENGTH bytes)) (
       SOME (FFIreturn (LUPDATE (n2w 1) 0 bytes) fs)))`;;

(* HOL4 fsFFIScript.sml:205-208: code that the source has in a comment *)

(* open for writing
* position: the beginning of the file.
* The file is truncated to zero length if it already exists.
* TODO: It is created if it does not already exists.*)
let ffi_open_out_def = new_definition
  `ffi_open_out (conf:word8 list) bytes fs = APPEND (
       OPTION_IGNORE_BIND (assert (9 <= LENGTH bytes)) (OPTION_BIND
         (getNullTermStr conf) (\fname. OPTION_BIND (openFile_truncate (implode
         fname) fs WriteMode) (\(fd,fs').
       OPTION_IGNORE_BIND (assert (fd <= 255)) (
       SOME (FFIreturn (APPEND (CONS (n2w 0) (n2w8 fd)) (DROP 9 bytes))
         fs'))))))
     (
       OPTION_IGNORE_BIND (assert (0 < LENGTH bytes)) (
       SOME (FFIreturn (LUPDATE (n2w 1) 0 bytes) fs)))`;;

(*
* [descriptor index (8 bytes); number of char to read (2 bytes); buffer]
*   -> [return code; number of read chars (2 bytes); read chars]
* corresponding system call:
*  ssize_t read(int fd, void *buf, size_t count) *)
let ffi_read_def = new_definition
  `ffi_read (conf:word8 list) bytes fs =
     // the buffer contains at least the number of requested bytes
     match bytes with (CONS n1 (CONS n0 (CONS pad1 (CONS pad2 tll)))) ->
       APPEND (
              OPTION_IGNORE_BIND (assert (LENGTH conf = 8)) (
              OPTION_IGNORE_BIND (assert (LENGTH tll >= w22n [n1; n0]))
                (OPTION_BIND (fsFFI_read (w82n conf) fs (w22n [n1; n0]))
                (\(l,fs').
              // return ok code and list of chars
              // *  the end of the array may remain unchanged
              SOME (FFIreturn
                        (APPEND (APPEND (APPEND (CONS (n2w 0) (n2w2 (LENGTH
                          l))) [pad2])
                         (MAP (n2w o ORD) l))
                         (DROP (LENGTH l) tll))
                        fs'))))) (SOME (FFIreturn (LUPDATE (n2w 1) 0 bytes)
                          fs))
   |
     // inaccurate: "when an error occurs, [...]
     // * it is left unspecified whether the file position (if any) changes.
     _ -> NONE`;;

(* [descriptor index; number of chars to write; chars to write]
*    -> [return code; number of written chars]
* corresponding system call:
* ssize_t write(int fildes, const void *buf, size_t nbytes) *)
let ffi_write_def = new_definition
  `ffi_write (conf:word8 list) bytes fs =
     match bytes with (CONS n1 (CONS n0 (CONS off1 (CONS off0 tll)))) ->
       APPEND (OPTION_IGNORE_BIND
             // the buffer contains at least the number of requested bytes
             (assert (LENGTH conf = 8)) (
             OPTION_IGNORE_BIND (assert (LENGTH tll >= w22n [off1; off0]))
               (OPTION_BIND (fsFFI_write (w82n conf) (w22n [n1; n0])
                              (MAP (CHR o w2n) (DROP (w22n [off1; off0])
                                tll)) fs) (\(nw,fs').
             // return ok code and number of bytes written
             SOME (FFIreturn (APPEND (CONS (n2w 0) (n2w2 nw)) (CONS off0
               tll)) fs'))))) (SOME (FFIreturn (LUPDATE (n2w 1) 0 bytes) fs))
         | _ -> NONE
   // return error code`;;

(* closes a file given its descriptor index *)
let ffi_close_def = new_definition
  `ffi_close (conf:word8 list) (bytes:word8 list) fs =
       OPTION_IGNORE_BIND (assert (LENGTH bytes >= 1)) (
       OPTION_IGNORE_BIND (assert (LENGTH conf = 8)) (APPEND (OPTION_BIND
         (closeFD (w82n conf) fs) (\(_,fs').
         SOME (FFIreturn (LUPDATE (n2w 0) 0 bytes) fs')))
       (SOME (FFIreturn (LUPDATE (n2w 1) 0 bytes) fs))))`;;

(* HOL4 fsFFIScript.sml:291-304: code that the source has in a comment *)
(* -- *)

(* Packaging up the model as an ffi_part *)

let encode_inode_def = define_cases
  `(encode_inode (UStream s) = cfFFIType_Cons (num_of_int (&0))
    (cfFFIType_Str s)) /\
   (encode_inode (File s) = cfFFIType_Cons (num_of_int (&1))
    (cfFFIType_Str s))`;;

let encode_inode_tbl_def = new_definition
  `encode_inode_tbl tbl = encode_list (encode_pair encode_inode
  (cfFFIType_Str o implode)) tbl`;;

let encode_mode_def = define_cases
  `(encode_mode ReadMode = num_of_int (&0)) /\
   (encode_mode WriteMode = num_of_int (&1))`;;

let encode_fds_def = new_definition
  `encode_fds fds =
      encode_list (encode_pair num_of_int (encode_pair encode_inode
        (encode_pair encode_mode num_of_int))) fds`;;

let encode_files_def = new_definition
  `encode_files fs = encode_list (encode_pair cfFFIType_Str cfFFIType_Str)
  fs`;;

let fsFFI_encode_def = new_definition
  `fsFFI_encode fs = cfFFIType_Cons
                (cfFFIType_Cons
                  (cfFFIType_Cons
                   (cfFFIType_Cons
                     (encode_inode_tbl (IO_fs_inode_tbl fs))
                     (encode_fds (IO_fs_infds fs)))
                   (Stream (IO_fs_numchars fs)))
                  (encode_files (IO_fs_files fs)))
                (num_of_int (IO_fs_maxFD fs))`;;

let encode_inode_11 = prove
 (`!x y. encode_inode x = encode_inode y <=> x = y`,
  CHEAT_TAC);;
add_simp encode_inode_11;;

let encode_inode_tbl_11 = prove
 (`!xs ys. encode_inode_tbl xs = encode_inode_tbl ys <=> xs = ys`,
  CHEAT_TAC);;
add_simp encode_inode_tbl_11;;

let encode_mode_11 = prove
 (`!x y. encode_mode x = encode_mode y <=> x = y`,
  CHEAT_TAC);;
add_simp encode_mode_11;;

let encode_fds_11 = prove
 (`!xs ys. encode_fds xs = encode_fds ys <=> xs = ys`,
  CHEAT_TAC);;
add_simp encode_fds_11;;

let encode_files_11 = prove
 (`!xs ys. encode_files xs = encode_files ys <=> xs = ys`,
  CHEAT_TAC);;
add_simp encode_files_11;;

(* encode_11 *)
let fsFFI_encode_11 = prove
 (`!x y. fsFFI_encode x = fsFFI_encode y <=> x = y`,
  CHEAT_TAC);;
add_simp fsFFI_encode_11;;

(* encode_decode_exists[local] *)
let fsFFI_encode_decode_exists = prove
 (`?decode'. !cls. decode' (fsFFI_encode cls) = SOME cls`,
  CHEAT_TAC);;

(* HOL4 fsFFIScript.sml:395-400: ML code, not ported *)

let fs_ffi_part_def = new_definition
  `fs_ffi_part =
     (fsFFI_encode,decode,
       [((implode "open_in"),ffi_open_in);
        ((implode "open_out"),ffi_open_out);
        ((implode "read"),ffi_read);
        ((implode "write"),ffi_write);
        ((implode "close"),ffi_close)])`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["decode"];;

(* and the interface *)
let _ = unhide_overloads ();;
