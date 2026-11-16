(* ======================================================== *)
(*  monadic_enc32: ported from HOL4's
    compiler/encoders/monadic_enc/monadic_enc32Script.sml
    A definition theory, with 8 definitions, 2 datatypes and 10
    theorems.  Needed by to_target32Prog.ml.  *)
(* ======================================================== *)

(*
  Implement and prove correct monadic version of encoder
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/monadic_enc/monadic_enc.ml";;
needs "lib/state_transformer.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "monadic_enc32"
  ["asm"; "lab_to_target"; "ml_monadBase"; "monadic_enc"];;

(* Data type for the exceptions *)
let state_exn_32_INDUCT,state_exn_32_RECURSION = define_datatype
  "state_exn_32 =
     monadic_enc32_Fail string
   | monadic_enc32_Subscript";;

(* HOL4 monadic_enc32Script.sml:19-20: the ML values that the definitions
   below antiquote *)

(* HOL4 monadic_enc32Script.sml:22: ML code, not ported *)

(* 32 BIT IMPLEMENTATION *)

(* The state is just an array *)
let enc_state_32_FIELDS = define_record "enc_state_32"
  ["hash_tab_32","((32 asm#word8 list) list) list"];;

(* Monadic functions to handle the exceptions *)
(* HOL4 makes the functions of the exception type state_exn_32 with ML
   code (define_monad_exception_functions of
   ml_monadBaseLib); these are the definitions that it
   makes *)
let monadic_enc32_raise_Fail_def = new_definition
  `monadic_enc32_raise_Fail e1 =
     (\state. (M_failure (monadic_enc32_Fail e1),state))`;;

let monadic_enc32_raise_Subscript_def = new_definition
  `monadic_enc32_raise_Subscript =
     (\state. (M_failure monadic_enc32_Subscript,state))`;;

let monadic_enc32_handle_Fail_def = new_definition
  `monadic_enc32_handle_Fail x f =
     (\state.
       match x state with (res,state) ->
         match res with M_success y -> (M_success y,state)
         | M_failure e ->
           (match e with monadic_enc32_Fail e1 -> f e1 state |
             monadic_enc32_Subscript -> (M_failure
             monadic_enc32_Subscript,state)))`;;

let monadic_enc32_handle_Subscript_def = new_definition
  `monadic_enc32_handle_Subscript x f =
     (\state.
       match x state with (res,state) ->
         match res with M_success y -> (M_success y,state)
         | M_failure e ->
           (match e with monadic_enc32_Fail e1 -> (M_failure
             (monadic_enc32_Fail e1),state) | monadic_enc32_Subscript -> f
             state))`;;

(* HOL4 monadic_enc32Script.sml:35: the overload failwith, which the port
   expands *)

(* HOL4 makes the monadic accessors of enc_state_32 with ML code
   (define_monad_access_funs of ml_monadBaseLib); these are
   the definitions that it makes *)
let get_hash_tab_32_def = new_definition
  `get_hash_tab_32 = (\state. (M_success (enc_state_32_hash_tab_32
  state),state))`;;

let set_hash_tab_32_def = new_definition
  `set_hash_tab_32 x =
     (\state. (M_success one,enc_state_32_hash_tab_32_fupd (K x) state))`;;


(* HOL4 monadic_enc32Script.sml:39-40: ML code, not ported *)

(* Fixed-size array manipulators *)
(* HOL4 makes the manipulators of the fixed size arrays with
   ML code (define_MFarray_manip_funs of ml_monadBaseLib);
   these are the definitions that it makes *)
let hash_tab_32_length_def = new_definition
  `hash_tab_32_length = Marray_length (\state. enc_state_32_hash_tab_32
  state)`;;

let hash_tab_32_sub_def = new_definition
  `hash_tab_32_sub = Marray_sub (\state. enc_state_32_hash_tab_32 state)
  monadic_enc32_Subscript`;;

let update_hash_tab_32_def = new_definition
  `update_hash_tab_32 =
     Marray_update (\state. enc_state_32_hash_tab_32 state)
       (\x state. enc_state_32_hash_tab_32_fupd (K x) state)
         monadic_enc32_Subscript`;;


(* HOL4 monadic_enc32Script.sml:46: ML code, not ported *)

(* HOL4 monadic_enc32Script.sml:48-49: a theorem that HOL4 states as the
   value of an ML expression: hash_tab_32_accessor *)

let lookup_ins_table_32_def = new_definition
  `lookup_ins_table_32 enc n a =
   let v = hash_asm n a MOD n in
   st_ex_bind (hash_tab_32_sub v) (\ls.
     match ALOOKUP ls a with
       NONE ->
       st_ex_bind (st_ex_return (enc a)) (\encode.
         st_ex_ignore_bind (update_hash_tab_32 v (CONS (a,encode) ls)) (
         st_ex_return encode))
     | SOME res ->
       st_ex_return res)`;;

let enc_line_hash_32_def = define_cases
  `(enc_line_hash_32 enc skip_len n (lab_Label n1 n2 n3) =
        st_ex_return (lab_Label n1 n2 skip_len)) /\
   (enc_line_hash_32 enc skip_len n (lab_Asm a _ _) =
        st_ex_bind (lookup_ins_table_32 enc n (cbw_to_asm a)) (\bs.
          st_ex_return (lab_Asm a bs (LENGTH bs)))) /\
   (enc_line_hash_32 enc skip_len n (lab_LabAsm l _ _ _) =
         st_ex_bind (lookup_ins_table_32 enc n (lab_inst (n2w 0) l)) (\bs.
           st_ex_return (lab_LabAsm l (n2w 0) bs (LENGTH bs))))`;;

let enc_line_hash_32_ls_def,enc_line_hash_32_ls_ind = define_guess
  `(enc_line_hash_32_ls enc skip_len n [] = st_ex_return []) /\
   (enc_line_hash_32_ls enc skip_len n (CONS x xs) =
      st_ex_bind (enc_line_hash_32 enc skip_len n x) (\fx. st_ex_bind
          (enc_line_hash_32_ls enc skip_len n xs) (\fxs.
        st_ex_return (CONS fx fxs))))`;;

let enc_sec_hash_32_ls_def,enc_sec_hash_32_ls_ind = define_guess
  `(enc_sec_hash_32_ls enc skip_len n [] = st_ex_return []) /\
   (enc_sec_hash_32_ls enc skip_len n (CONS x xs) =
      match x with Section k ys ->
      st_ex_bind (enc_line_hash_32_ls enc skip_len n ys) (\ls. st_ex_bind
          (enc_sec_hash_32_ls enc skip_len n xs) (\rest.
        st_ex_return (CONS (Section k ls) rest))))`;;

let enc_sec_hash_32_ls_full_def = new_definition
  `enc_sec_hash_32_ls_full enc n xs =
   enc_sec_hash_32_ls enc (LENGTH (enc (asm_Inst asm_Skip))) n xs`;;

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
(* HOL4 makes the record of an initial state of enc_state_32 and the
   run function with ML code (define_run of
   ml_monadBaseLib); an array field of it is the length and
   the initial value of the array *)
let ienc_state_32_FIELDS = define_record "ienc_state_32"
  ["hash_tab_32","num#(32 asm#word8 list) list"];;
let run_ienc_state_32_def = new_definition
  `run_ienc_state_32 x state =
     run x (mk_enc_state_32 (REPLICATE (FST (ienc_state_32_hash_tab_32
       state)) (SND (ienc_state_32_hash_tab_32 state))))`;;


let enc_secs_32_aux_def = new_definition
  `enc_secs_32_aux enc n xs =
     run_ienc_state_32 (enc_sec_hash_32_ls_full enc n xs)
       (mk_enc_state_32 (n,[]))`;;

let enc_secs_32_def = new_definition
  `enc_secs_32 enc n xs =
     match enc_secs_32_aux enc (if n = 0 then 1 else n) xs with
       M_success xs -> xs
     | M_failure _ -> []`;;

(* HOL4 monadic_enc32Script.sml:127: ML code, not ported *)

(* Msub_eqn *)
let msub_eqn = prove
 (`!e n ls v.
   Msub e n ls =
   if n < LENGTH ls then M_success (EL n ls)
                  else M_failure e`,
  CHEAT_TAC);;
add_simp msub_eqn;;

let hash_tab_32_sub_eqn = prove
 (`hash_tab_32_sub n s =
   (if n < LENGTH (enc_state_32_hash_tab_32 s) then
   (M_success (EL n (enc_state_32_hash_tab_32 s)),s)
   else (M_failure (monadic_enc32_Subscript),s))`,
  CHEAT_TAC);;
add_simp hash_tab_32_sub_eqn;;

(* Mupdate_eqn *)
let mupdate_eqn = prove
 (`!e x n ls.
   Mupdate e x n ls =
   if n < LENGTH ls then
   M_success (LUPDATE x n ls)
   else M_failure e`,
  CHEAT_TAC);;
add_simp mupdate_eqn;;

let update_hash_tab_32_eqn = prove
 (`update_hash_tab_32 n t s =
   (if n < LENGTH (enc_state_32_hash_tab_32 s) then
    (M_success one,enc_state_32_hash_tab_32_fupd (K (LUPDATE t n
      (enc_state_32_hash_tab_32 s))) s)
   else (M_failure (monadic_enc32_Subscript),s))`,
  CHEAT_TAC);;
add_simp update_hash_tab_32_eqn;;

let good_table_32_def = new_definition
  `good_table_32 enc n s <=>
   ALL (\ls. ALL (\(x,y). enc x = y) ls) (enc_state_32_hash_tab_32 s) /\
   LENGTH (enc_state_32_hash_tab_32 s) = n`;;

(* [local] *)
let lookup_ins_table_32_correct = prove
 (`good_table_32 enc n s /\
   0 < n ==>
   (?s'.
   lookup_ins_table_32 enc n aa s = (M_success (enc aa),s') /\
   good_table_32 enc n s')`,
  CHEAT_TAC);;

(* [local] *)
let enc_line_hash_32_correct = prove
 (`!line.
     good_table_32 enc n s /\ 0 < n ==>
     (?s'.
      enc_line_hash_32 enc skip_len n line s =
        (M_success (lab_to_target_enc_line enc skip_len line),s') /\
      good_table_32 enc n s')`,
  CHEAT_TAC);;

(* [local] *)
let enc_line_hash_32_ls_correct = prove
 (`!xs s.
   good_table_32 enc n s /\ 0 < n ==>
   (?s'.
   enc_line_hash_32_ls enc skip_len n xs s =
   (M_success (MAP (lab_to_target_enc_line enc skip_len) xs),s') /\
   good_table_32 enc n s')`,
  CHEAT_TAC);;

(* [local] *)
let enc_sec_hash_32_ls_correct = prove
 (`!xs s.
   good_table_32 enc n s /\ 0 < n ==>
   (?s'.
   enc_sec_hash_32_ls enc skip_len n xs s =
   (M_success (MAP (lab_to_target_enc_sec enc skip_len) xs),s') /\
   good_table_32 enc n s')`,
  CHEAT_TAC);;

let enc_secs_32_correct = prove
 (`enc_secs_32 enc n xs =
   (lab_to_target_enc_sec_list enc xs)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
