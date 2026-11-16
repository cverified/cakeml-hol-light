(* ======================================================== *)
(*  CommandLineProof: ported from HOL4's
    basis/CommandLineProofScript.sml
    A proof theory, with 4 definitions and 16 theorems.  Needed by
    ag32BootstrapProof.ml, ag32_basis_ffiProof.ml, basisProg.ml,
    basis_ffi.ml, replProof.ml and x64BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Proof about the command-line module of the CakeML standard basis library.
*)

needs "basis/CommandLineProg.ml";;
needs "basis/Word8ArrayProof.ml";;
needs "basis/clFFI.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfLetAuto.ml";;
needs "characteristic/cfMain.ml";;
needs "semantics/namespace.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/cfMonad.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "CommandLineProof"
  ["CommandLineProg"; "Word8ArrayProof"; "cf"; "cfLetAuto"; "cfMain";
   "cfMonad"; "clFFI"; "ml_prog"; "ml_translator"];;

(* HOL4 CommandLineProofScript.sml:10: ML code, not ported *)

let wfcl_def = new_definition
  `wfcl cl <=> ALL validArg cl /\ LENGTH cl < 256 * 256 /\ ~(cl = [])`;;

let COMMANDLINE_def = new_definition
  `COMMANDLINE cl =
     IOx cl_ffi_part cl * &(wfcl cl)`;;

(* HOL4 CommandLineProofScript.sml:21-29: ML code, not ported *)

(* HOL4 CommandLineProofScript.sml:31-33: a theorem that HOL4 states as the
   value of an ML expression: COMMANDLINE_precond *)

let COMMANDLINE_FFI_part_hprop = prove
 (`FFI_part_hprop (COMMANDLINE x)`,
  CHEAT_TAC);;

(* HOL4 CommandLineProofScript.sml:45-46: ML code, not ported *)

let CommandLine_read16bit = prove
 (`2 <= LENGTH a ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     CommandLine_read16bit_v [av]
     (W8ARRAY av a)
     (POSTv (?_W8ARRAY v) av a * &(NUM (w2n (EL 0 a) + 256 * w2n (EL 1 a))
       v))`,
  CHEAT_TAC);;

let CommandLine_write16bit = prove
 (`NUM n nv /\ 2 <= LENGTH a ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
     CommandLine_write16bit_v [av; nv]
     (W8ARRAY av a)
     (POSTv (?_W8ARRAY v) av (CONS (n2w n) (CONS (n2w (n DIV 256)) (TL (TL
       a)))))`,
  CHEAT_TAC);;

(* [local] *)
let SUC_SUC_MAX2 = prove
 (`SUC (SUC (MAX 2 n - 2)) = (MAX 2 n)`,
  CHEAT_TAC);;

(* [local] *)
let two_byte_sum = prove
 (`k < 65536 ==> k MOD 256 + 256 * ((k DIV 256) MOD 256) = k`,
  CHEAT_TAC);;

(* [local] *)
let LESS_LENGTH_EXISTS = prove
 (`!xs n. n < LENGTH xs ==> (?ys y ts. xs = APPEND ys (CONS y ts) /\ LENGTH
  ys = n)`,
  CHEAT_TAC);;

(* [local] *)
let DROP_SUC_LENGTH_MAP = prove
 (`(DROP (SUC (LENGTH ys)) (APPEND (MAP f ys) (CONS y ts))) = ts`,
  CHEAT_TAC);;

(* HOL4 CommandLineProofScript.sml:120-213: a theorem whose statement the
   port cannot state yet: CommandLine_cloop_spec *)

(* HOL4 CommandLineProofScript.sml:215-263: a theorem whose statement the
   port cannot state yet: CommandLine_cline_spec *)

(* HOL4 CommandLineProofScript.sml:265-266: ML code, not ported *)

(* HOL4 CommandLineProofScript.sml:268-281: a theorem whose statement the
   port cannot state yet: CommandLine_name_spec *)

(* HOL4 CommandLineProofScript.sml:283-284: ML code, not ported *)

let name_def = new_definition
  `CommandLineProof_name one = (\cl. (M_success (HD cl),cl))`;;

let EvalM_name = prove
 (`ast_Eval env exp (UNIT_TYPE u) /\
    (nsLookup (sem_env_v env) (Long (implode "CommandLine") (Short (implode
      "name"))) =
      SOME CommandLine_name_v) ==>
    EvalM F env st (ast_App ast_Opapp [ast_Var (Long (implode "CommandLine")
      (Short (implode "name"))); exp])
      (MONAD STRING_TYPE exc_ty (CommandLineProof_name u))
      (COMMANDLINE,(p:('ffi->(mlstring,ffi)fmap)#(mlstring
        list#(mlstring->word8 list->word8 list->ffi->(ffi
        cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* HOL4 CommandLineProofScript.sml:302-316: a theorem whose statement the
   port cannot state yet: CommandLine_arguments_spec *)

let arguments_def = new_definition
  `arguments one = (\cl. (M_success (TL cl),cl))`;;

let EvalM_arguments = prove
 (`ast_Eval env exp (UNIT_TYPE u) /\
    (nsLookup (sem_env_v env) (Long (implode "CommandLine") (Short (implode
      "arguments"))) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (ast_App ast_Opapp [ast_Var (Long (implode "CommandLine")
      (Short (implode "arguments"))); exp])
      (MONAD (LIST_TYPE STRING_TYPE) exc_ty (arguments u))
      (COMMANDLINE,(p:('ffi->(mlstring,ffi)fmap)#(mlstring
        list#(mlstring->word8 list->word8 list->ffi->(ffi
        cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* HOL4 CommandLineProofScript.sml:334-336: a proof *)

let UNIQUE_COMMANDLINE = prove
 (`!s cl1 cl2 H1 H2. VALID_HEAP s ==>
     (COMMANDLINE cl1 * H1) s /\ (COMMANDLINE cl2 * H2) s ==> cl2 = cl1`,
  CHEAT_TAC);;

(* [hprop_inj] *)
let COMMANDLINE_HPROP_INJ = prove
 (`!cl1 cl2. HPROP_INJ (COMMANDLINE cl1) (COMMANDLINE cl2) (cl2 = cl1)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
