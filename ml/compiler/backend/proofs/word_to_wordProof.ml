(* ======================================================== *)
(*  word_to_wordProof: ported from HOL4's
    compiler/backend/proofs/word_to_wordProofScript.sml
    A proof theory about word_to_word.ml, with 2 definitions and 27
    theorems.  Needed by data_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_to_word
*)

needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_allocProof.ml";;
needs "compiler/backend/proofs/word_copyProof.ml";;
needs "compiler/backend/proofs/word_cseProof.ml";;
needs "compiler/backend/proofs/word_elimProof.ml";;
needs "compiler/backend/proofs/word_instProof.ml";;
needs "compiler/backend/proofs/word_removeProof.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;
needs "compiler/backend/proofs/word_unreachProof.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/ffi/ffi.ml";;

hol4_overload "Call" "wordLang_Call";;

(* HOL4 word_to_wordProofScript.sml:19-23: a proof *)

let FST_compile_single = cake_theorem "FST_compile_single[simp]"
  (fun () ->
    `FST (word_to_word_compile_single a b c d e) = FST (FST e)`)
  CHEAT_TAC;;

(*Chains up compile_single theorems*)
let compile_single_lem = cake_theorem "compile_single_lem"
  (fun () ->
    `!prog n st.
     domain (wordSem_state_locals st) = set_of_list (even_list n)
       /\
     gc_fun_const_ok (wordSem_state_gc_fun st) ==>
     (?perm'.
     let (res,rst) = wordSem_evaluate
       (prog,wordSem_state_permute_fupd (K perm') st) in
     let (_1,_2,cprog) = (word_to_word_compile_single t k a c
       ((name,n,prog),col)) in
     if (res = SOME wordSem_Error) then T else
     let (res',rcst) = wordSem_evaluate (cprog,st) in
       res = res' /\
       word_state_eq_rel rst rcst /\
       (match res with
         NONE -> T | SOME (Break _3) -> T | SOME (Continue _4) ->
           T | SOME _5 -> wordSem_state_locals rst =
           wordSem_state_locals rcst))`)
  CHEAT_TAC;;

let rm_perm = cake_theorem "rm_perm[local]"
  (fun () ->
    `wordSem_state_permute_fupd (K (wordSem_state_permute s))
       s = s`)
  CHEAT_TAC;;

(* HOL4 word_to_wordProofScript.sml:165: ML code, not ported *)

let word_to_wordProof_find_code_thm =
  cake_theorem "find_code_thm[local]"
  (fun () ->
    `(!n v. lookup n (wordSem_state_code st) = SOME v ==>
            (?t k a c col.
            lookup n l = SOME (SND (word_to_word_compile_single t k
              a c ((n,v),col))))) /\
     wordSem_find_code o1 (add_ret_loc o' x) (wordSem_state_code
       st) (wordSem_state_stack_size st) = SOME (args,prog,locsize) ==>
     (?t k a c col n prog'.
     SND (word_to_word_compile_single t k a c ((n,LENGTH
       args,prog),col)) = (LENGTH args,prog') /\
     wordSem_find_code o1 (add_ret_loc o' x) l
       (wordSem_state_stack_size st) = SOME (args,prog',locsize))`)
  CHEAT_TAC;;

let pop_env_termdep = cake_theorem "pop_env_termdep[local]"
  (fun () ->
    `wordSem_pop_env rst = SOME x ==> wordSem_state_termdep x =
  wordSem_state_termdep rst`)
  CHEAT_TAC;;

(* The t k a c parameters don't need to be existentially quantified *)
let code_rel_def = cake_define
  `word_to_wordProof_code_rel stc ttc <=>
   (!n v. lookup n stc = SOME v ==>
          (?col t k a c.
          lookup n ttc = SOME (SND (word_to_word_compile_single t
            k a c ((n,v),col)))))`;;
hol4_overload "code_rel" "word_to_wordProof_code_rel";;

let compile_single_eta = cake_theorem "compile_single_eta[local]"
  (fun () ->
    `word_to_word_compile_single t k a c ((p,x),y) =
     (p,SND (word_to_word_compile_single t k a c ((p,x),y)))`)
  CHEAT_TAC;;


let code_rel_union_fromAList =
  cake_theorem "code_rel_union_fromAList[local]"
  (fun () ->
    `!s l ls.
     code_rel s l /\
     domain s = domain l ==>
     code_rel (union s (fromAList ls)) (union l (fromAList (MAP
       (\p. word_to_word_compile_single t k a c (p,NONE)) ls)))`)
  CHEAT_TAC;;

let compile_single_correct =
  cake_theorem "compile_single_correct[local]"
  (fun () ->
    `!prog (st:('a,'c,'ffi)wordSem_state) l coracle cc.
     code_rel (wordSem_state_code st) l /\
     (domain (wordSem_state_code st) = domain l) /\
     (wordSem_state_compile st = (\conf progs.
       cc conf (MAP (\p. word_to_word_compile_single tt kk aa co
         (p,NONE)) progs))) /\
     (coracle = (I ## MAP (\p. word_to_word_compile_single tt kk aa
       co (p,NONE))) o wordSem_state_compile_oracle st) /\
     gc_fun_const_ok (wordSem_state_gc_fun st) ==>
     (?perm'.
       let (res,rst) = wordSem_evaluate
         (prog,wordSem_state_permute_fupd (K perm') st) in
         if res = SOME wordSem_Error then T else
           let (res1,rst1) = wordSem_evaluate
             (prog,wordSem_state_compile_fupd (K cc)
             (wordSem_state_compile_oracle_fupd (K coracle)
             (wordSem_state_code_fupd (K l)
             st))) in
             res1 = res /\
             code_rel (wordSem_state_code rst) (wordSem_state_code
               rst1) /\
             domain (wordSem_state_code rst) = domain
               (wordSem_state_code rst1) /\
             rst1 = wordSem_state_compile_fupd (K cc)
               (wordSem_state_compile_oracle_fupd (K ((I ## MAP (\p.
               word_to_word_compile_single tt kk aa co (p,NONE))) o
               wordSem_state_compile_oracle rst))
               (wordSem_state_code_fupd (K (wordSem_state_code rst1))
               rst)))
     // todo: rst1.perm?`)
  CHEAT_TAC;;

(* HOL4 word_to_wordProofScript.sml:294-296: a proof *)

(* HOL4 word_to_wordProofScript.sml:298-301: a proof *)

(* HOL4 word_to_wordProofScript.sml:303-306: a proof *)

(* HOL4 word_to_wordProofScript.sml:308-311: a proof *)

(* HOL4 word_to_wordProofScript.sml:313-316: a proof *)

(* HOL4 word_to_wordProofScript.sml:318-321: a proof *)

(* HOL4 word_to_wordProofScript.sml:323-326: a proof *)

(* HOL4 word_to_wordProofScript.sml:328-341: a proof *)

(* Call: dispatch with Tail-call branch closing inline (via
   every_case_tac >> gvs[bad_fun_return_def] for cake-while's
   Break/Continue handling), then suspend "non_tail_call" for
   the more involved non-tail-call branch. *)
(* HOL4 word_to_wordProofScript.sml:347-438: a proof *)
    (*Manual simulation for Result*)
(* HOL4 word_to_wordProofScript.sml:440-507: a proof *)
    (*Manual simulation for Exceptions*)
(* HOL4 word_to_wordProofScript.sml:509-589: a proof *)


(* HOL4 word_to_wordProofScript.sml:592-605: a proof *)
    (* NONE case (first w/o reverse) *)
(* HOL4 word_to_wordProofScript.sml:607-639: a proof *)
  (* SOME case *)
(* HOL4 word_to_wordProofScript.sml:641-642: a proof *)

(* HOL4 word_to_wordProofScript.sml:644-653: a proof *)

(* HOL4 word_to_wordProofScript.sml:655-659: a proof *)
    (* SOME case: cut_state succeeds *)
(* HOL4 word_to_wordProofScript.sml:661-745: a proof *)
  (* NONE case *)
(* HOL4 word_to_wordProofScript.sml:747-748: a proof *)

(* HOL4 word_to_wordProofScript.sml:750-765: a proof *)

(* HOL4 word_to_wordProofScript.sml:767-769: a proof *)

(* HOL4 word_to_wordProofScript.sml:771-773: a proof *)

(* HOL4 word_to_wordProofScript.sml:775-777: a proof *)

(* HOL4 word_to_wordProofScript.sml:779-782: a proof *)

(* HOL4 word_to_wordProofScript.sml:784-787: a proof *)

(* HOL4 word_to_wordProofScript.sml:789-791: a proof *)

(* HOL4 word_to_wordProofScript.sml:793-795: a proof *)

(* HOL4 word_to_wordProofScript.sml:797-799: a proof *)

(* HOL4 word_to_wordProofScript.sml:801-822: a proof *)

(* HOL4 word_to_wordProofScript.sml:824-826: a proof *)

(* HOL4 word_to_wordProofScript.sml:828-830: a proof *)

(* HOL4 word_to_wordProofScript.sml:832-834: a proof *)

(* HOL4 word_to_wordProofScript.sml:836-847: a proof *)

(* HOL4 word_to_wordProofScript.sml:849: a proof *)

let compile_word_to_word_thm = cake_theorem "compile_word_to_word_thm"
  (fun () ->
    `code_rel (wordSem_state_code (st:('a,'c,'ffi)wordSem_state)) l /\
     (domain (wordSem_state_code st) = domain l) /\
     (wordSem_state_compile st = (\conf progs.
     cc conf (MAP (\p. full_compile_single tt kk aa co (p,NONE))
       progs))) /\
     (coracle = (I ## MAP (\p. full_compile_single tt kk aa co
       (p,NONE))) o wordSem_state_compile_oracle st) /\
     gc_fun_const_ok (wordSem_state_gc_fun st) ==>
     (?perm' clk.
     let prog = Call NONE (SOME start) [0] NONE in
     let (res,rst) = wordSem_evaluate
       (prog,wordSem_state_permute_fupd (K perm') st) in
      if res = SOME wordSem_Error then T else
      let (res1,rst1) = wordSem_evaluate
        (prog,wordSem_state_compile_oracle_fupd (K coracle)
        (wordSem_state_compile_fupd (K cc) (wordSem_state_termdep_fupd
        (K 0) (wordSem_state_clock_fupd (K (wordSem_state_clock st +
        clk)) (wordSem_state_code_fupd (K (map (I ##
        remove_must_terminate) l))
        st))))) in
        res1 = res /\ state_clock
        rst1 = state_clock rst /\ state_ffi
        rst1 = state_ffi rst /\ wordSem_state_stack_max
        rst1 = wordSem_state_stack_max rst)`)
  CHEAT_TAC;;

(* HOL4 word_to_wordProofScript.sml:902: ML code, not ported *)

(* HOL4 word_to_wordProofScript.sml:904: ML code, not ported *)

let cond16bit_inst_select_exp' =
  cake_theorem "cond16bit_inst_select_exp'"
  (fun () ->
    `x = inst_select_exp c t1 t2 exp ==>
     (no_share_inst x \/ ~(asm_config_ISA c = Ag32))`)
  CHEAT_TAC;;

(* HOL4 word_to_wordProofScript.sml:917: ML code, not ported *)

let cond16bit_inst_select = cake_theorem "cond16bit_inst_select"
  (fun () ->
    `x = inst_select c n p /\
     (no_share_inst p \/ ~(asm_config_ISA c = Ag32)) ==>
     (no_share_inst x \/ ~(asm_config_ISA c = Ag32))`)
  CHEAT_TAC;;

let remove_must_terminate_no_share_inst =
  cake_theorem "remove_must_terminate_no_share_inst"
  (fun () ->
    `no_share_inst p ==> no_share_inst (remove_must_terminate p)`)
  CHEAT_TAC;;

let full_compile_single_no_share_inst =
  cake_theorem "full_compile_single_no_share_inst"
  (fun () ->
    `no_share_inst (SND (SND (FST prog_info))) ==>
     no_share_inst
       (SND (SND (full_compile_single two_reg_arith reg_count alg
         c prog_info)))`)
  CHEAT_TAC;;

(* syntax going into stackLang *)
let compile_to_word_conventions =
  cake_theorem "compile_to_word_conventions"
  (fun () ->
    `EVERY (\(_6,_7,prg). no_share_inst prg \/ ~(asm_config_ISA ac =
  Ag32)) p ==>
     (let (_8,progs) = word_to_word_compile wc ac p in
     MAP FST progs = MAP FST p /\
     EVERY2 labels_rel (MAP (wordConvs_extract_labels o SND o SND)
       p)
                       (MAP (wordConvs_extract_labels o SND o SND)
                         progs) /\
     EVERY (\(n,m,prog).
       flat_exp_conventions prog /\
       post_alloc_conventions (asm_config_reg_count ac - (5 +
         LENGTH (asm_config_avoid_regs ac))) prog /\
       (EVERY (\(n,m,prog). every_inst (inst_ok_less ac) prog) p /\
        asm_offset_ok 0 (asm_config_addr_offset ac) (n2w 0) /\
          asm_offset_ok 0 (asm_config_hw_offset ac) (n2w 0) /\
          asm_offset_ok 0 (asm_config_byte_offset ac) (n2w 0) ==>
         full_inst_ok_less ac prog) /\
       (asm_config_two_reg_arith ac ==> every_inst two_reg_inst
         prog) /\
       (no_share_inst prog \/ ~(asm_config_ISA ac = Ag32)))
         progs)`)
  CHEAT_TAC;;

(**** more on syntactic form restrictions ****)

let code_rel_not_created_subprogs =
  cake_theorem "code_rel_not_created_subprogs"
  (fun () ->
    `wordSem_find_code op args c1 sz = SOME v /\
     code_rel c1 c2 /\
     not_created_subprogs P (FST (SND v)) /\
     wordSem_find_code op args c2 sz = SOME v' ==>
     not_created_subprogs P (FST (SND v'))`)
  CHEAT_TAC;;

(* HOL4 word_to_wordProofScript.sml:1082: a theorem that HOL4 states
   as the value of an ML expression: code_rel_P *)

(* HOL4 word_to_wordProofScript.sml:1084-1085: a theorem that HOL4
   states as the value of an ML expression: code_rel_no_alloc *)

(* HOL4 word_to_wordProofScript.sml:1087-1088: a theorem that HOL4
   states as the value of an ML expression: code_rel_no_install *)


(***** compile_single correctness for no_alloc & no_install ******)
let no_install_no_alloc_compile_single_correct =
  cake_theorem "no_install_no_alloc_compile_single_correct"
  (fun () ->
    `!prog (st:('a,'c,'ffi)wordSem_state) l.
       code_rel (wordSem_state_code st) l /\
       wordConvs_no_install prog /\ no_alloc prog /\
       no_install_code (wordSem_state_code st) /\ no_alloc_code
         (wordSem_state_code st) /\
       (domain (wordSem_state_code st) = domain l) /\
       gc_fun_const_ok (wordSem_state_gc_fun st) ==>
       (?perm'.
         let (res,rst) = wordSem_evaluate
           (prog,wordSem_state_permute_fupd (K perm') st) in
           if res = SOME wordSem_Error then T else
             let (res1,rst1) = wordSem_evaluate
               (prog,wordSem_state_code_fupd (K l) st) in
               res1 = res /\
               code_rel (wordSem_state_code rst)
                 (wordSem_state_code rst1) /\
               domain (wordSem_state_code rst) = domain
                 (wordSem_state_code rst1) /\
               rst1 = wordSem_state_code_fupd (K
                 (wordSem_state_code rst1)) rst)`)
  CHEAT_TAC;;

(* HOL4 word_to_wordProofScript.sml:1145-1147: a proof *)

(* HOL4 word_to_wordProofScript.sml:1149-1152: a proof *)

(* HOL4 word_to_wordProofScript.sml:1154-1157: a proof *)

(* HOL4 word_to_wordProofScript.sml:1159-1162: a proof *)

(* HOL4 word_to_wordProofScript.sml:1164-1167: a proof *)

(* HOL4 word_to_wordProofScript.sml:1169-1172: a proof *)

(* HOL4 word_to_wordProofScript.sml:1174-1177: a proof *)

(* HOL4 word_to_wordProofScript.sml:1179-1189: a proof *)

(* HOL4 word_to_wordProofScript.sml:1191-1193: a proof *)

(* HOL4 word_to_wordProofScript.sml:1195-1197: a proof *)

(* HOL4 word_to_wordProofScript.sml:1199-1203: a proof *)

(* HOL4 word_to_wordProofScript.sml:1205-1209: a proof *)

(* HOL4 word_to_wordProofScript.sml:1211-1215: a proof *)

(* HOL4 word_to_wordProofScript.sml:1217-1221: a proof *)

(* HOL4 word_to_wordProofScript.sml:1223-1227: a proof *)

(* HOL4 word_to_wordProofScript.sml:1229-1233: a proof *)

(* HOL4 word_to_wordProofScript.sml:1235-1239: a proof *)

(* HOL4 word_to_wordProofScript.sml:1241-1243: a proof *)

(* HOL4 word_to_wordProofScript.sml:1245-1249: a proof *)

(* HOL4 word_to_wordProofScript.sml:1251-1255: a proof *)

(* HOL4 word_to_wordProofScript.sml:1257-1261: a proof *)

(* HOL4 word_to_wordProofScript.sml:1263-1274: a proof *)

(* HOL4 word_to_wordProofScript.sml:1276-1286: a proof *)

(* HOL4 word_to_wordProofScript.sml:1288-1345: a proof *)

(* HOL4 word_to_wordProofScript.sml:1347-1441: a proof *)

(* HOL4 word_to_wordProofScript.sml:1443-1562: a proof *)
   (* Manual simulation for Result *)
(* HOL4 word_to_wordProofScript.sml:1564-1615: a proof *)
   (* Manual simulation for Exceptions *)
(* HOL4 word_to_wordProofScript.sml:1617-1690: a proof *)

(* HOL4 word_to_wordProofScript.sml:1692: a proof *)

(* HOL4 word_to_wordProofScript.sml:1694-2098: code that the source
   has in a comment *)

(******** more on no_mt **********)

let no_mt_remove_must_terminate_const =
  cake_theorem "no_mt_remove_must_terminate_const"
  (fun () ->
    `no_mt prog ==> remove_must_terminate prog = prog`)
  CHEAT_TAC;;

let no_mt_full_compile_single = cake_theorem "no_mt_full_compile_single"
  (fun () ->
    `no_mt (SND (SND (FST x))) ==>
     full_compile_single tt kk aa c x =
     word_to_word_compile_single tt kk aa c x`)
  CHEAT_TAC;;

let no_mt_code_full_compile_single =
  cake_theorem "no_mt_code_full_compile_single"
  (fun () ->
    `no_mt_code (fromAList progs) /\
     ALL_DISTINCT (MAP FST progs) /\
     LENGTH x = LENGTH progs ==>
     MAP (full_compile_single tt kk aa co) (ZIP progs x) =
     MAP (word_to_word_compile_single tt kk aa co) (ZIP progs x)`)
  CHEAT_TAC;;

(*** code_rel_ext ***)

let code_rel_ext_def = cake_define
  `code_rel_ext code l <=>
   (!n p_1 p_2.
      SOME (p_1,p_2) = lookup n code ==>
      (?t' k' a' c' col.
        SOME
        (SND (full_compile_single t' k' a' c' ((n,p_1,p_2),col))) =
        lookup n l))`;;

(* HOL4 word_to_wordProofScript.sml:2154: ML code, not ported *)

let code_rel_ext_word_to_word = cake_theorem "code_rel_ext_word_to_word"
  (fun () ->
    `!code c1 col code'.
       word_to_word_compile c1 c2 code = (col,code') ==>
       code_rel_ext (fromAList code) (fromAList code')`)
  CHEAT_TAC;;

let no_mt_code_rel_ext = cake_theorem "no_mt_code_rel_ext"
  (fun () ->
    `no_mt_code cd1 /\
     code_rel_ext cd1 cd2 ==>
     code_rel cd1 cd2`)
  CHEAT_TAC;;

(**** more on no_share_inst ****)

let code_rel_no_share_inst = cake_theorem "code_rel_no_share_inst"
  (fun () ->
    `wordSem_find_code op args c1 sz = SOME v /\
     code_rel c1 c2 /\
     no_share_inst (FST (SND v)) /\
     wordSem_find_code op args c2 sz = SOME v' ==>
     no_share_inst (FST (SND v'))`)
  CHEAT_TAC;;

(***** word_to_word semantics correctness for Pancake *****)

let panLang_compile_word_to_word_thm =
  cake_theorem "panLang_compile_word_to_word_thm"
  (fun () ->
    `code_rel (wordSem_state_code (st:('a,'c,'ffi)wordSem_state)) l /\
     no_install_code (wordSem_state_code st) /\ no_alloc_code
       (wordSem_state_code st) /\ no_mt_code (wordSem_state_code st) /\
     (domain (wordSem_state_code st) = domain l) /\
     gc_fun_const_ok (wordSem_state_gc_fun st) ==>
     (?perm' clk.
       let prog = Call NONE (SOME start) [0] NONE in
         let (res,rst) = wordSem_evaluate
           (prog,wordSem_state_permute_fupd (K perm') st) in
           if res = SOME wordSem_Error then T else
             let (res1,rst1) = wordSem_evaluate
               (prog,wordSem_state_code_fupd (K l) st) in
               res1 = res /\ state_clock
               rst1 = state_clock rst /\ state_ffi
               rst1 = state_ffi rst /\ wordSem_state_stack_max
               rst1 = wordSem_state_stack_max rst)`)
  CHEAT_TAC;;

let word_to_word_compile_semantics =
  cake_theorem "word_to_word_compile_semantics"
  (fun () ->
    `word_to_word_compile wconf acomf wprog0 = (col,wprog) /\
     gc_fun_const_ok (wordSem_state_gc_fun s) /\
     no_install_code (fromAList wprog0) /\
     no_alloc_code (fromAList wprog0) /\
     no_install_code (wordSem_state_code s) /\ no_alloc_code
       (wordSem_state_code s) /\
     no_mt_code (fromAList wprog0) /\
     ALL_DISTINCT (MAP FST wprog0) /\ wordSem_state_stack s = [] /\
       wordSem_state_code
     // start = lc + first_name ∧
     // EL lc wprog0 = (start, v) ∧
     t = fromAList wprog /\ lookup 0 (wordSem_state_locals t) =
       SOME (Loc 1 0) /\
     t = wordSem_state_code_fupd (K (wordSem_state_code t)) s /\
       wordSem_state_code
     s = fromAList wprog0 /\ ~(wordSem_semantics
       (s:('a,'b,'ffi)wordSem_state) start = Fail) ==>
     wordSem_semantics s start =
     wordSem_semantics (t:('a,'b,'ffi)wordSem_state) start`)
  CHEAT_TAC;;
