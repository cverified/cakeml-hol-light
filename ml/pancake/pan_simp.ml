(* ======================================================== *)
(*  pan_simp: ported from HOL4's
    pancake/pan_simpScript.sml
    A definition theory, with 6 definitions and 3 theorems.  Needed
    by from_pancake32Prog.ml, from_pancake64Prog.ml and
    pan_to_word.ml.  *)
(* ======================================================== *)

(*
  Simplification of panLang.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "pancake/panLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_simp"
  ["backend_common"; "panLang"];;

let _ = do_list hide_constant ["pmatch"; "prog"];;

let pan_simp_SmartSeq_def = new_definition
  `pan_simp_SmartSeq p q =
    if p = pan_Skip then q else pan_Seq p q`;;
add_simp pan_simp_SmartSeq_def;;

let pan_simp_seq_assoc_def,pan_simp_seq_assoc_ind = define_guess
  `seq_assoc p q =
     match q with
       pan_Skip -> p
     | pan_Dec v s e q ->
       pan_simp_SmartSeq p (pan_Dec v s e (seq_assoc pan_Skip q))
     | pan_Seq q r -> seq_assoc (seq_assoc p q) r
     | pan_If e q r ->
       pan_simp_SmartSeq p (pan_If e (seq_assoc pan_Skip q) (seq_assoc
         pan_Skip r))
     | pan_While e q ->
      pan_simp_SmartSeq p (pan_While e (seq_assoc pan_Skip q))
     | pan_Call NONE name args ->
       pan_simp_SmartSeq p (pan_Call NONE name args)
     | pan_Call (SOME (rv,exp)) name args ->
       pan_simp_SmartSeq p (pan_Call
                    (match exp with NONE -> SOME (rv,NONE)
                      | SOME (eid,ev,ep) ->
                         SOME (rv,(SOME (eid,ev,(seq_assoc pan_Skip ep)))))
                    name args)
     | pan_DecCall v s e es q ->
       pan_simp_SmartSeq p (pan_DecCall v s e es (seq_assoc pan_Skip q))
     | pan_Annot _ _ -> p
     | q -> pan_simp_SmartSeq p q`;;

let seq_call_ret_def = new_definition
  `seq_call_ret prog =
    match prog with pan_Seq ((\s h. asm_Call (SOME (SOME s,h)))
      (pan_Local,rv1) NONE trgt args) (pan_Return (pan_Var pan_Local
      (rv2:mlstring))) ->
       if rv1 = rv2 then ((asm_Call NONE) trgt args) else prog
     | other -> other`;;

let ret_to_tail_def,ret_to_tail_ind = define_guess
  `ret_to_tail p =
     match p with
       pan_Skip -> pan_Skip
     | pan_Dec v s e q -> pan_Dec v s e (ret_to_tail q)
     | pan_Seq p q ->
       seq_call_ret (pan_Seq (ret_to_tail p) (ret_to_tail q))
     | pan_If e p q -> pan_If e (ret_to_tail p) (ret_to_tail q)
     | pan_While e p -> pan_While e (ret_to_tail p)
     | pan_Call NONE name args -> pan_Call NONE name args
     | pan_Call (SOME (rv,exp)) name args ->
      pan_Call (SOME (rv,(match exp with NONE -> NONE
                       | SOME (eid,ev,ep) ->
                           SOME (eid,ev,(ret_to_tail ep)))))
           name args
     | pan_DecCall v s e es q -> pan_DecCall v s e es (ret_to_tail q)
     | p -> p`;;

let pan_simp_compile_def = new_definition
  `pan_simp_compile p =
    let p = seq_assoc pan_Skip p in
     ret_to_tail p`;;

let pan_simp_compile_prog_def = new_definition
  `pan_simp_compile_prog prog =
     MAP (\decl.
            match decl with
              Function fi ->
                Function (fun_decl_body_fupd (K (pan_simp_compile
                  (fun_decl_body fi))) fi)
            | _ -> decl) prog`;;


(* seq_assoc_pmatch *)
let pan_simp_seq_assoc_pmatch = prove
 (`!p prog.
   seq_assoc p prog =
   match prog with pan_Skip -> p
    | (pan_Dec v s e q) -> pan_simp_SmartSeq p (pan_Dec v s e (seq_assoc
      pan_Skip q))
    | (pan_Seq q r) -> seq_assoc (seq_assoc p q) r
    | (pan_If e q r) ->
      pan_simp_SmartSeq p (pan_If e (seq_assoc pan_Skip q) (seq_assoc
        pan_Skip r))
    | (pan_While e q) ->
      pan_simp_SmartSeq p (pan_While e (seq_assoc pan_Skip q))
    | (pan_Call rtyp name args) ->
       pan_simp_SmartSeq p (pan_Call
                   (match rtyp with NONE -> NONE
                    | SOME (rv,NONE) -> SOME (rv,NONE)
                    | SOME (rv,(SOME (eid,ev,ep))) ->
                        SOME (rv,(SOME (eid,ev,(seq_assoc pan_Skip ep)))))
                   name args)
   | (pan_DecCall v s e es q) -> pan_simp_SmartSeq p (pan_DecCall v s e es
     (seq_assoc pan_Skip q))
   | (pan_Annot _ _) -> p
   | q -> pan_simp_SmartSeq p q`,
  CHEAT_TAC);;

let ret_to_tail_pmatch = prove
 (`!p.
   ret_to_tail p =
   match p with pan_Skip -> pan_Skip
    | (pan_Dec v s e q) -> pan_Dec v s e (ret_to_tail q)
    | (pan_Seq q r) -> seq_call_ret (pan_Seq (ret_to_tail q) (ret_to_tail
      r))
    | (pan_If e q r) ->
       pan_If e (ret_to_tail q) (ret_to_tail r)
    | (pan_While e q) ->
       pan_While e (ret_to_tail q)
    | (pan_Call rtyp name args) ->
       pan_Call
       (match rtyp with NONE -> NONE
                     | SOME (rv,NONE) -> SOME (rv,NONE)
                     | SOME (rv,(SOME (eid,ev,ep))) ->
                        SOME (rv,(SOME (eid,ev,(ret_to_tail ep)))))
       name args
    | (pan_DecCall v s e es q) -> pan_DecCall v s e es (ret_to_tail q)
    | p -> p`,
  CHEAT_TAC);;

let compile_prog_pmatch = prove
 (`pan_simp_compile_prog prog =
     MAP (\decl.
            match decl with
              Function fi ->
                Function (fun_decl_body_fupd (K (pan_simp_compile
                  (fun_decl_body fi))) fi)
            | _ -> decl) prog`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch";
   "prog"];;

(* and the interface *)
let _ = unhide_overloads ();;
