(* ======================================================== *)
(*  word_bignum: ported from HOL4's
    compiler/backend/word_bignumScript.sml  *)
(* ======================================================== *)

(*
  The bignum library used by the CakeML compiler. Note that the
  implementation is automatically generated from a shallow embedding
  that is part of the HOL distribution in mc_multiwordTheory.
*)

needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/balanced_map.ml";;
needs "lib/errorMonad.ml";;
needs "lib/mc_multiword.ml";;
needs "lib/multiword.ml";;
needs "lib/peg.ml";;
needs "lib/regexp_compiler.ml";;
needs "lib/sptree.ml";;
needs "lib/term.ml";;
needs "semantics/ast.ml";;

(* syntax of a little language *)

let address_INDUCT,address_RECURSION = define_datatype
  "address = In1 | In2 | Out";;

let mini_INDUCT,mini_RECURSION = define_datatype
  "mini = word_bignum_Skip | word_bignum_Assign (num) ('a \
   wordLang_exp) | word_bignum_Delete (num list) | word_bignum_Seq \
   (mini) (mini) | word_bignum_Load (num) (num) (address) | \
   word_bignum_Store (num) (num) | word_bignum_If (cmp) (num) ('a \
   asm_reg_imm) (mini) (mini) | word_bignum_Swap | word_bignum_Add \
   (num) (num) (num) ('a asm_reg_imm) ('a asm_reg_imm) | \
   word_bignum_Sub (num) (num) (num) ('a asm_reg_imm) ('a \
   asm_reg_imm) | word_bignum_Mul (num) (num) (num) (num) | \
   word_bignum_Div (num) (num) (num) (num) (num) | word_bignum_Loop \
   (bool) (num list) (mini) | word_bignum_Continue | word_bignum_Rec \
   (num list) (num list) | word_bignum_LoopBody (mini)";;
hol4_overload "Skip" "word_bignum_Skip";;
hol4_overload "Assign" "word_bignum_Assign";;
hol4_overload "Delete" "word_bignum_Delete";;
hol4_overload "Seq" "word_bignum_Seq";;
hol4_overload "Load" "word_bignum_Load";;
hol4_overload "Store" "word_bignum_Store";;
hol4_overload "If" "word_bignum_If";;
hol4_overload "Swap" "word_bignum_Swap";;
hol4_overload "Add" "word_bignum_Add";;
hol4_overload "Sub" "word_bignum_Sub";;
hol4_overload "Mul" "word_bignum_Mul";;
hol4_overload "Div" "word_bignum_Div";;
hol4_overload "Loop" "word_bignum_Loop";;
hol4_overload "Continue" "word_bignum_Continue";;
hol4_overload "Rec" "word_bignum_Rec";;
hol4_overload "LoopBody" "word_bignum_LoopBody";;


(* syntax helper funs *)

(* syntax helper funs *)

(* HOL4 builds a term of the deep embedding in a quotation, where
   its typechecker makes the type of the word of every piece the
   same one; the port builds the pieces one by one, so it gives
   each the type variable of the others *)

let at_A tm =
  inst (map (fun v -> `:A`,v) (type_vars_in_term tm)) tm;;

let skip_tm = `word_bignum_Skip:(A)mini`;;
let swap_tm = `word_bignum_Swap:(A)mini`;;
let continue_tm = `word_bignum_Continue:(A)mini`;;

let mk_Delete n = at_A (list_mk_icomb "word_bignum_Delete" [n]);;
let mk_Assign (n,x) =
  at_A (list_mk_icomb "word_bignum_Assign" [n; x]);;
let mk_Rec (xs,ys) =
  at_A (list_mk_icomb "word_bignum_Rec" [xs; ys]);;
let mk_Seq (p1,p2) =
  at_A (list_mk_icomb "word_bignum_Seq" [p1; p2]);;
let mk_Store (n,i) =
  at_A (list_mk_icomb "word_bignum_Store" [n; i]);;
let mk_Loop (b,ns,p) =
  at_A (list_mk_icomb "word_bignum_Loop" [b; ns; p]);;
let mk_Load (n,i,a) =
  at_A (list_mk_icomb "word_bignum_Load" [n; i; a]);;
let mk_Imm w = at_A (list_mk_icomb "Imm" [w]);;
let mk_Reg n = at_A (list_mk_icomb "Reg" [n]);;

let is_Rec tm =
  try fst(dest_const(fst(strip_comb tm))) = "word_bignum_Rec"
  with Failure _ -> false;;

let mk_If (c,r,ri,p1,p2) =
  at_A (list_mk_icomb "word_bignum_If" [c; r; ri; p1; p2]);;

(* generate deep embeddings *)

let my_dest_let tm =
  let bs,b = dest_let tm in
  if length bs = 1 then hd bs,b else failwith "my_dest_let";;

(* a register is a variable r<n> of the type of a machine word *)

let dest_reg v =
  let n,ty = dest_var v in
  if not (is_type ty && fst(dest_type ty) = "word" &&
          n.[0] = 'r')
  then failwith "dest_reg" else
  mk_small_numeral (int_of_string
    (String.sub n 1 (String.length n - 1)));;

let binops =
  [`word_add (v:(A)word) w`,`asm_Add`;
   `word_sub (v:(A)word) w`,`asm_Sub`;
   `word_and (v:(A)word) w`,`asm_And`;
   `word_xor (v:(A)word) w`,`asm_Xor`;
   `word_or (v:(A)word) w`,`asm_Or`];;

let shifts =
  [`word_lsr (v:(A)word) n`,`Lsr`;
   `word_lsl (v:(A)word) n`,`Lsl`;
   `word_asr (v:(A)word) n`,`Asr`];;

(* HOL4 reads these patterns with match_term, which instantiates
   the type of the words and the variables of the pattern *)

let matches pat tm = can (term_match [] pat) tm;;

(* the same constant, at any type (HOL4's same_const) *)

let same_const x y =
  try fst (dest_const x) = fst (dest_const y)
  with Failure _ -> false;;

(* the little of HOL4's wordsSyntax that the translation uses *)

let is_n2w tm = matches `(n2w n):(A)word` tm;;

let dest_word_1comp tm =
  if matches `word_1comp (w:(A)word)` tm then rand tm
  else failwith "dest_word_1comp";;

let word_ty_of tm = hd (snd (dest_type (type_of tm)));;

(* a word of the size of another one, and the Const of wordLang
   that holds it *)

let mk_word tm n =
  inst [word_ty_of tm,`:A`]
       (mk_comb(`n2w:num->(A)word`,mk_small_numeral n));;

let mk_Const_of n =
  mk_comb(`wordLang_Const:(A)word->(A)wordLang_exp`,
          mk_comb(`n2w:num->(A)word`,n));;

let rec get_exp x =
  (* Var *)
  try let n = dest_reg x in at_A (list_mk_icomb "wordLang_Var" [n])
  with Failure _ ->
  (* Const *)
  try if not (is_n2w x) then failwith "get_exp" else
      at_A (list_mk_icomb "wordLang_Const" [x])
  with Failure _ ->
  (* Op *)
  try let _,name = find (fun (pat,_) -> matches pat x) binops in
      let x1 = get_exp (rand (rator x)) in
      let x2 = get_exp (rand x) in
      at_A (list_mk_icomb "wordLang_Op"
              [name; mk_list([x1; x2],type_of x1)])
  with Failure _ ->
  (* Shift *)
  try let _,name = find (fun (pat,_) -> matches pat x) shifts in
      let x1 = get_exp (rand (rator x)) in
      let x2 = rand x in
      at_A (list_mk_icomb "wordLang_Shift"
              [name; x1; mk_Const_of x2])
  with Failure _ ->
  (* ~ *)
  let r = dest_word_1comp x in
  get_exp (list_mk_icomb "word_xor"
             [r; list_mk_icomb "word_sub"
                   [mk_word r 0; mk_word r 1]]);;

let cmps =
  [`word_lo (v:(A)word) w`,`asm_Lower`;
   `word_lt (v:(A)word) w`,`asm_Less`;
   `(v:(A)word) = w`,`asm_Equal`];;

let dest_reg_imm ri =
  try mk_Reg (dest_reg ri) with Failure _ ->
  if is_n2w ri then mk_Imm ri else failwith "dest_reg_imm";;

let get_guard b =
  (* Op *)
  try let _,name = find (fun (pat,_) -> matches pat b) cmps in
      let x1 = dest_reg (rand (rator b)) in
      let x2 = dest_reg_imm (rand b) in
      (name,x1,x2)
  with Failure _ ->
  (* Test *)
  let l,r = dest_eq b in
  if not (is_n2w r && matches `word_and (v:(A)word) w` l)
  then failwith "get_guard" else
  (`asm_Test`,dest_reg (rand (rator l)),dest_reg_imm (rand l));;

let dest_lupdate_let tm =
  let (v,r),body = my_dest_let tm in
  if not (aconv v (rand r) &&
          matches `LUPDATE a (w2n (r:(A)word)) (zs:(B)list)` r)
  then failwith "dest_lupdate_let" else
  let x = rand (rator (rator r)) in
  let y = rand (rand (rator r)) in
  (x,y,body);;

let dest_el_let tm =
  let (v,r),body = my_dest_let tm in
  if not (matches `EL (w2n (r:(A)word)) (zs:(B)list)` r)
  then failwith "dest_el_let"
  else
  let a = fst (dest_var (rand r)) in
  let a = if a = "xs" then `In1` else
          if a = "ys" then `In2` else
          if a = "zs" then `Out` else failwith "dest_el_let" in
  let y = rand (rand (rator r)) in
  (v,y,a,body);;

let dest_single_add_sub_let pat tm =
  let (v,r),body = my_dest_let tm in
  if not (matches pat r) then failwith "dest_single_add_sub_let" else
  let a1,a2 = dest_pair v in
  let a1 = dest_reg a1 and a2 = dest_reg a2 in
  let args = snd (strip_comb r) in
  let r1 = dest_reg (el 0 args) in
  let r2 = dest_reg_imm (el 1 args) in
  let r3 = dest_reg_imm (el 2 args) in
  (a1,a2,r1,r2,r3,body);;

let dest_single_add_let =
  dest_single_add_sub_let
    `single_add_word (r0:(A)word) r1 ri`;;
let dest_single_sub_let =
  dest_single_add_sub_let
    `single_sub_word (r0:(A)word) r1 ri`;;

let dest_single_mul_let tm =
  let (v,r),body = my_dest_let tm in
  if not (matches `single_mul (r0:(A)word) r2 (n2w 0)` r)
  then failwith "dest_single_mul_let" else
  let a1,a2 = dest_pair v in
  let a1 = dest_reg a1 and a2 = dest_reg a2 in
  let args = snd (strip_comb r) in
  let r1 = dest_reg (el 0 args) in
  let r2 = dest_reg (el 1 args) in
  (a1,a2,r1,r2,body);;

let dest_single_div_let tm =
  let (v,r),body = my_dest_let tm in
  if not (matches `single_div (r2:(A)word) r0 r1` r)
  then failwith "dest_single_div_let" else
  let a1,a2 = dest_pair v in
  let a1 = dest_reg a1 and a2 = dest_reg a2 in
  let args = snd (strip_comb r) in
  let r1 = dest_reg (el 0 args) in
  let r2 = dest_reg (el 1 args) in
  let r3 = dest_reg (el 2 args) in
  (a1,a2,r1,r2,r3,body);;

let get_let tm =
  (* Load *)
  try let r,i,a,rest = dest_el_let tm in
      (mk_Load (dest_reg r,dest_reg i,a),rest)
  with Failure _ ->
  (* Store *)
  try let r,i,rest = dest_lupdate_let tm in
      (mk_Store (dest_reg r,dest_reg i),rest)
  with Failure _ ->
  (* Assign *)
  try let (v,x),rest = my_dest_let tm in
      let n = dest_reg v in
      let e = get_exp x in
      (mk_Assign (n,e),rest)
  with Failure _ ->
  (* Swap *)
  try let (v,x),rest = my_dest_let tm in
      if not (is_pair x) then failwith "get_let" else
      let xs = filter (fun c -> fst(dest_const c) <> ",")
                      (find_terms is_const x) in
      if length xs <> 0 then failwith "get_let" else
      (swap_tm,rest)
  with Failure _ ->
  (* Add *)
  try let a1,a2,r1,r2,r3,rest = dest_single_add_let tm in
      (at_A (list_mk_icomb "word_bignum_Add" [a1;a2;r1;r2;r3]),rest)
  with Failure _ ->
  (* Sub *)
  try let a1,a2,r1,r2,r3,rest = dest_single_sub_let tm in
      (at_A (list_mk_icomb "word_bignum_Sub" [a1;a2;r1;r2;r3]),rest)
  with Failure _ ->
  (* Mul *)
  try let a1,a2,r1,r2,rest = dest_single_mul_let tm in
      (at_A (list_mk_icomb "word_bignum_Mul" [a1;a2;r1;r2]),rest)
  with Failure _ ->
  (* Div *)
  let a1,a2,r1,r2,r3,rest = dest_single_div_let tm in
  (at_A (list_mk_icomb "word_bignum_Div" [a1;a2;r1;r2;r3]),rest);;

let code_defs = ref ([]:thm list);;
let prev_trans = ref ([]:(term * term) list);;

(* the name of a function that the translation needs and that is
   not translated yet.  HOL4 raises UnableToTranslate for it, an
   exception of its own, so that the handlers of the translation
   (which catch a HOL_ERR) let it through; the port raises
   Invalid_argument, which its handlers (which catch a Failure)
   let through in the same way *)

let unable_to_translate str =
  invalid_arg ("UnableToTranslate " ^ str);;

let dest_unable e =
  match e with
    Invalid_argument s when String.length s > 18 &&
                            String.sub s 0 18 = "UnableToTranslate " ->
      String.sub s 18 (String.length s - 18)
  | _ -> raise e;;

let rec dest_tuple tm =
  try let x,y = dest_pair tm in dest_tuple x @ dest_tuple y
  with Failure _ -> [tm];;

let get_full_prog inp tm =
  let immediate_deps = ref ([]:term list) in
  let ret_tm = ref skip_tm in
  let cont_tm = ref continue_tm in
  let ret_vars = ref ([]:term list) in
  let cont_vars = ref ([]:term list) in
  (* helpers *)
  let dest_num_let tm =
    let bs,b = dest_let tm in
    if type_of (snd (hd bs)) = `:num` then b
    else failwith "dest_num_let" in
  let dest_num_if tm =
    let x,(_,z) = dest_cond tm in
    let l,_ = dest_eq x in
    if type_of l = `:num` then z else failwith "dest_num_if" in
  let dest_num_let_or_if tm =
    try dest_num_if tm with Failure _ -> dest_num_let tm in
  let dest_rec_let tm =
    let (_,y),rest = my_dest_let tm in
    let saves,call = dest_pair y in
    (saves,call,rest) in
  (* main function *)
  let rec get_prog tm =
    (* return *)
    if is_var tm || is_pair tm
    then (ret_vars := frees tm; !ret_tm)
    else
    (* let *)
    try let x,rest = get_let tm in mk_Seq (x,get_prog rest)
    with Failure _ ->
    (* previous translation *)
    try let (_,x),rest = my_dest_let tm in
        let f = repeat rator x in
        let _,code = find (fun (x,_) -> same_const x f)
                            (!prev_trans) in
        immediate_deps := code :: (!immediate_deps);
        mk_Seq (code,get_prog rest)
    with Failure _ ->
    (* recursive let *)
    try let saves,call,rest = dest_rec_let tm in
        let saves = map dest_reg (dest_tuple saves) in
        let saves = mk_list (saves,`:num`) in
        let dels = mk_list ([],`:num`) in
        cont_vars := frees call;
        mk_Seq (mk_Rec (saves,dels),get_prog rest)
    with Failure _ ->
    (* If *)
    try let b,(t1,t2) = dest_cond tm in
        let x1,x2,x3 = get_guard b in
        mk_If (x1,x2,x3,get_prog t1,get_prog t2)
    with Failure _ ->
    if is_const (rator tm) && (is_var (rand tm) || is_pair (rand tm))
    then (cont_vars := frees tm; !cont_tm) else
    try get_prog (dest_num_let_or_if tm)
    with Failure _ ->
      try let (_,x),_ = my_dest_let tm in
          unable_to_translate (fst (dest_const (repeat rator x)))
      with Failure e ->
        (print_string "Unable to translate\n\n";
         print_string (string_of_term tm);
         print_string "\n\n"; failwith e) in
  (* compute deps *)
  let init_prog = get_prog tm in
  (* compute what vars are deleted or assigned *)
  let x = list_mk_conj
            (mk_eq (init_prog,init_prog) ::
             map concl (filter (fun th -> exists (same_const
                                        (lhs (concl th)))
                                        (!immediate_deps))
                               (!code_defs))) in
  (* the name of the head of a term, so that the patterns below
     are only matched against a term that can match one of them
     (a run of the translation walks every term that it has made
     so far, which is slow enough as it is) *)
  let head_name tm =
    try fst (dest_const (fst (strip_comb tm))) with Failure _ -> "" in
  let is_delete tm =
    head_name tm = "word_bignum_Delete" &&
    can (term_match [] `(word_bignum_Delete n):(A)mini`) tm in
  let is_assign tm =
    mem (head_name tm)
        ["word_bignum_Assign"; "word_bignum_Load"; "word_bignum_Add";
         "word_bignum_Sub"; "word_bignum_Mul"; "word_bignum_Div"] &&
    exists (fun pat -> can (term_match [] pat) tm)
      [`(word_bignum_Assign n):(A)wordLang_exp->(A)mini`;
       `(word_bignum_Load n):num->address->(A)mini`;
       `(word_bignum_Add n1 n2):num->(A)asm_reg_imm->(A)asm_reg_imm
          ->(A)mini`;
       `(word_bignum_Add n1):num->num->(A)asm_reg_imm
          ->(A)asm_reg_imm->(A)mini`;
       `(word_bignum_Sub n1 n2):num->(A)asm_reg_imm->(A)asm_reg_imm
          ->(A)mini`;
       `(word_bignum_Sub n1):num->num->(A)asm_reg_imm
          ->(A)asm_reg_imm->(A)mini`;
       `(word_bignum_Mul n1 n2):num->num->(A)mini`;
       `(word_bignum_Mul n1):num->num->num->(A)mini`;
       `(word_bignum_Div n1 n2):num->num->num->(A)mini`;
       `(word_bignum_Div n1):num->num->num->num->(A)mini`] in
  let f tm = try dest_reg tm with Failure _ -> tm in
  let ds = setify
             (map rand (find_terms is_assign x) @
              itlist (fun t l -> dest_list (rand t) @ l)
                     (find_terms is_delete x) [] @
              filter (fun t -> not (is_var t)) (map f (frees inp))) in
  let add_dels vs tm =
    if vs = [] then tm
    else mk_Seq (mk_Delete (mk_list (vs,type_of (hd vs))),tm) in
  ret_tm := add_dels (subtract ds (map f (!ret_vars))) skip_tm;
  let cont_dels = subtract ds (map f (!cont_vars)) in
  cont_tm := add_dels cont_dels continue_tm;
  (mk_list (cont_dels,`:num`),get_prog tm);;

let rec to_deep def =
  (* produce deep embedding *)
  let f = repeat rator (lhs (concl (SPEC_ALL def))) in
  let tm = rand (concl (SPEC_ALL def)) in
  let inp = rand (rand (rator (concl (SPEC_ALL def)))) in
  let is_rec = can (find_term (aconv f)) tm in
  let rec loop () =
    try get_full_prog inp tm
    with Invalid_argument _ as e ->
      let str = dest_unable e in
      (ignore (to_deep (assoc (str ^ "_def") (!the_tailrec_defs)));
       loop ()) in
  let dels,deep = loop () in
  let rec_flag = if can (find_term is_Rec) deep then `T` else `F` in
  let deep = if is_rec then mk_Loop (rec_flag,dels,deep) else deep in
  (* store deep embedding *)
  let name = (fst (dest_const f)) ^ "_code" in
  let code_def = cake_define (mk_eq (mk_var (name,type_of deep),
                                     deep)) in
  let code_const = lhs (concl code_def) in
  code_defs := code_def :: (!code_defs);
  prev_trans := (f,code_const) :: (!prev_trans);
  code_def;;

let mc_cmp_code_def = to_deep mc_cmp_def;;
let mc_compare_code_def = to_deep mc_compare_def;;
let mc_idiv_code_def = to_deep mc_idiv_def;;
let mc_iadd_code_def = to_deep mc_iadd_def;;
let mc_imul_code_def = to_deep mc_imul_def;;
let mc_iop_code_def = to_deep mc_iop_def;;

(* an example that produces Rec *)

let mc_fac_init_code_def = to_deep mc_fac_init_def;;
let mc_fac_final_code_def = to_deep mc_fac_final_def;;
let mc_fac_code_def = to_deep mc_fac_def;;
let mc_use_fac_code_def = to_deep mc_use_fac_def;;

(* compiler into wordLang *)

let has_compiled_def = cake_define
  `has_compiled code (n,code_list') =
     (match ALOOKUP code_list' code with NONE -> INR (n:num) |
       SOME (index,word_code) -> INL (index:num))`;;

let code_acc_next_def = cake_define
  `code_acc_next (n,code_list') = (n + 1,code_list')`;;

let install_def = cake_define
  `install c (n,code_list') = (n,c :: code_list')`;;

let compile_exp_def = cake_define
  `word_bignum_compile_exp x1 =
      match x1 with
        wordLang_Op b [x1; x2] -> wordLang_Op b
          [word_bignum_compile_exp x1; word_bignum_compile_exp x2]
      | (Var n) -> wordLang_Lookup (Temp (n2w n))
      | (Const w) -> Const w
      | (Shift sh x y) -> Shift sh (word_bignum_compile_exp x)
        (word_bignum_compile_exp y)
      | _1 -> Const (n2w 0)`;;
hol4_overload "compile_exp" "word_bignum_compile_exp";;

let TempIn1_def = cake_define
  `TempIn1 = Temp (n2w 31)`;;
let TempIn2_def = cake_define
  `TempIn2 = Temp (n2w 30)`;;
let TempOut_def = cake_define
  `TempOut = Temp (n2w 29)`;;

let SeqTemp_def = cake_define
  `SeqTemp i r p = Seq (wordLang_Assign i (wordLang_Lookup (Temp (n2w
  r)))) p`;;

let SeqTempImm_def = cake_define_list
  [`SeqTempImm i (Reg r) p = SeqTemp i r p`;
   `SeqTempImm i (Imm w) p = Seq (wordLang_Assign i (wordLang_Const
  w)) p`];;

let SeqTempImmNot_def = cake_define_list
  [`SeqTempImmNot i (Reg r) p =
      SeqTemp i r (Seq (Assign i (wordLang_Op Xor [Var i; Const
        (word_not (n2w 0))])) p)`;
   `SeqTempImmNot i (Imm w) p = Seq (wordLang_Assign i
  (wordLang_Const (word_not w))) p`];;

let SeqIndex_def = cake_define
  `SeqIndex i r arr p =
     (let t = (match arr with Out -> TempOut | In2 -> TempIn2 | In1
       -> TempIn1) in
       Seq (Assign i (wordLang_Op asm_Add [wordLang_Lookup t;
            (\sh e n. Shift sh e (wordLang_Const (n2w n))) Lsl
              (wordLang_Lookup (Temp (n2w r)))
              (backend_common_word_shift (:'a))])) p:'a
              wordLang_prog)`;;

let div_location_def = cake_define
  `div_location = 23`;;

let DivCode_def = cake_define
  `DivCode l1 l2 n1 n2 n3 n4 n5 =
     wordLang_MustTerminate
       (wordLang_Seq (wordLang_Call (SOME ([n1],(LS
         one,LN),Skip,l1,l2)) (SOME div_location) [n3; n4; n5] NONE)
            (wordLang_Assign n2 (wordLang_Lookup (Temp (n2w
              28)))))`;;

let LoadRegs_def = cake_define_list
  [`LoadRegs [] (p:'a wordLang_prog) = (p:'a wordLang_prog)`;
   `LoadRegs (n :: ns) (p:'a wordLang_prog) = ((Seq (Get (n + 2)
  (Temp (n2w n))) (LoadRegs ns p)):'a wordLang_prog)`];;

let SaveRegs_def = cake_define_list
  [`SaveRegs [] = (Skip:'a wordLang_prog)`;
   `SaveRegs (n :: ns) = ((Seq (Set (Temp (n2w n)) (Var (n + 2)))
  (SaveRegs ns)):'a wordLang_prog)`];;

let compile_def = cake_define
  `word_bignum_compile n l i cs x5 =
        match x5 with
          word_bignum_Skip -> (wordLang_Skip,l,i,cs)
        | Continue -> (Call NONE (SOME n) [0] NONE,l,i,cs)
        | (word_bignum_Rec save_regs names) ->
        (LoadRegs save_regs
          (Call (SOME ([1],(LS one,list_insert (MAP (\n. n + 2)
            save_regs) LN),
             SaveRegs save_regs,n,l)) (SOME n) [] NONE),l + 1,i,cs)
        | (Loop rec_calls vs body) ->
        (match has_compiled body cs with INL existing_index ->
            (Call (SOME ([i],(LS one,LN),Skip,n,l)) (SOME
              existing_index) [] NONE,l + 1,i + 1,cs) | INR new_index ->
            (let (new_code,a,b,cs) = word_bignum_compile new_index 2
              1 (code_acc_next cs) body in
              (Call (SOME ([i],(LS one,LN),Skip,n,l)) (SOME
                new_index) [] NONE,l + 1,i + 1,
               install (body,new_index,new_code) cs)))
        | (word_bignum_LoopBody b) -> word_bignum_compile n l i cs b
        | (Seq p1 p2) ->
        (let (p1,l,i,cs) = word_bignum_compile n l i cs p1 in
        let (p2,l,i,cs) = word_bignum_compile n l i cs p2 in
          (Seq p1 p2,l,i,cs))
        | (If t r ri p1 p2) ->
        (let (p1,l,i,cs) = word_bignum_compile n l i cs p1 in
        let (p2,l,i,cs) = word_bignum_compile n l i cs p2 in
          match ri with Reg r2 -> (SeqTemp i r (SeqTemp (i + 1) r2
            (If t i (Reg (i + 1)) p1 p2)),
                       l,i + 2,cs) | Imm im -> (SeqTemp i r (If t i
                         ri p1 p2),l,i + 1,cs))
        | (Assign j e) ->
        (Seq (Assign i (word_bignum_compile_exp e)) (Set (Temp (n2w
          j)) (Var i)),l,i + 1,cs)
        | (word_bignum_Delete _2) -> ((Skip:'a wordLang_prog),l,i,cs)
        | word_bignum_Swap ->
        (Seq (Assign i (wordLang_Lookup (TempIn1)))
        (Seq (Set (TempIn1) (wordLang_Lookup (TempIn2)))
             (Set (TempIn2) (Var i))),l,i + 1,cs)
        | (Store r1 r2) ->
        (SeqTemp i r1
        (SeqIndex (i + 1) r2 Out
           (Store (Var (i + 1)) i)),l,i + 2,cs)
        | (Load r1 r2 arr) ->
        (SeqIndex i r2 arr
        (Seq (Assign (i + 1) (wordLang_Load (Var i)))
             (Set (Temp (n2w r1)) (Var (i + 1)))),l,i + 2,cs)
        | (Add r0 r1 r2 r3 r4) ->
        (SeqTempImm (i + 4) r4 (SeqTempImm (i + 3) r3 (SeqTemp (i +
          2) r2
        (Seq (Inst (Arith (asm_AddCarry (i + 1) (i + 2) (i + 3) (i +
          4))))
        (Seq (Set (Temp (n2w r0)) (Var (i + 1)))
             (Set (Temp (n2w r1)) (Var (i + 4))))))),l,i + 5,cs)
        | (Sub r0 r1 r2 r3 r4) ->
        (SeqTempImm (i + 4) r4 (SeqTempImmNot (i + 3) r3 (SeqTemp (i
          + 2) r2
        (Seq (Inst (Arith (asm_AddCarry (i + 1) (i + 2) (i + 3) (i +
          4))))
        (Seq (Set (Temp (n2w r0)) (Var (i + 1)))
             (Set (Temp (n2w r1)) (Var (i + 4))))))),l,i + 5,cs)
        | (Mul r0 r1 r2 r3) ->
        (SeqTemp (i + 3) r3 (SeqTemp (i + 2) r2
        (Seq (Inst (Arith (asm_LongMul (i + 0) (i + 1) (i + 2) (i +
          3))))
        (Seq (Set (Temp (n2w r1)) (Var (i + 0)))
             (Set (Temp (n2w r0)) (Var (i + 1)))))),l,i + 4,cs)
        | (Div r0 r1 r2 r3 r4) ->
        (SeqTemp (i + 4) r4 (SeqTemp (i + 3) r3 (SeqTemp (i + 2) r2
        (Seq (DivCode n l (i + 0) (i + 1) (i + 2) (i + 3) (i + 4))
        (Seq (Set (Temp (n2w r0)) (Var (i + 0)))
             (Set (Temp (n2w r1)) (Var (i + 1))))))),l + 1,i + 5,cs)
        | _3 -> (Skip,l,i,cs)`;;
hol4_overload "compile" "word_bignum_compile";;

(* HOL4 ML code, not ported:
val _ = (max_print_depth := 25);
*)

let generated_bignum_stubs_def = cake_define
  `generated_bignum_stubs n =
     (let (x1,_4,_5,(_6,cs)) = word_bignum_compile n 2 1 (n + 1,[])
       mc_iop_code in
       (n,1,Seq x1 (Return 0 [0])) :: MAP (\(x,y,z). (y,1,Seq z
         (Return 0 [0]))) cs)`;;
