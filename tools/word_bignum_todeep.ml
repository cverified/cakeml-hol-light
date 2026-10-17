(* syntax helper funs *)

let skip_tm = `word_bignum_Skip:(A)mini`;;
let swap_tm = `word_bignum_Swap:(A)mini`;;
let continue_tm = `word_bignum_Continue:(A)mini`;;

let mk_Delete n = list_mk_icomb "word_bignum_Delete" [n];;
let mk_Assign (n,x) = list_mk_icomb "word_bignum_Assign" [n; x];;
let mk_Rec (xs,ys) = list_mk_icomb "word_bignum_Rec" [xs; ys];;
let mk_Seq (p1,p2) = list_mk_icomb "word_bignum_Seq" [p1; p2];;
let mk_Store (n,i) = list_mk_icomb "word_bignum_Store" [n; i];;
let mk_Loop (b,ns,p) = list_mk_icomb "word_bignum_Loop" [b; ns; p];;
let mk_Load (n,i,a) = list_mk_icomb "word_bignum_Load" [n; i; a];;
let mk_Imm w = list_mk_icomb "Imm" [w];;
let mk_Reg n = list_mk_icomb "Reg" [n];;

let is_Rec tm =
  try fst(dest_const(fst(strip_comb tm))) = "word_bignum_Rec"
  with Failure _ -> false;;

let mk_If (c,r,ri,p1,p2) =
  list_mk_icomb "word_bignum_If" [c; r; ri; p1; p2];;

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
  [`word_add:(A)word->(A)word->(A)word`,`asm_Add`;
   `word_sub:(A)word->(A)word->(A)word`,`asm_Sub`;
   `word_and:(A)word->(A)word->(A)word`,`asm_And`;
   `word_xor:(A)word->(A)word->(A)word`,`asm_Xor`;
   `word_or:(A)word->(A)word->(A)word`,`asm_Or`];;

let shifts =
  [`word_lsr:(A)word->num->(A)word`,`Lsr`;
   `word_lsl:(A)word->num->(A)word`,`Lsl`;
   `word_asr:(A)word->num->(A)word`,`Asr`];;

let head_is f x =
  try aconv (fst(strip_comb x)) f with Failure _ -> false;;

(* the little of HOL4's wordsSyntax that the translation uses *)

let is_n2w tm = is_comb tm && head_is `n2w:num->(A)word` tm;;

let dest_word_1comp tm =
  if head_is `word_1comp:(A)word->(A)word` tm then rand tm
  else failwith "dest_word_1comp";;

let word_ty_of tm = hd (snd (dest_type (type_of tm)));;

(* a word of the size of another one, and the Const of wordLang
   that holds it *)

let mk_word tm n =
  inst [word_ty_of tm,`:A`]
       (mk_comb(`n2w:num->(A)word`,mk_small_numeral n));;

let mk_Const_of ty n =
  inst [ty,`:A`]
       (mk_comb(`wordLang_Const:(A)word->(A)wordLang_exp`,
                mk_comb(`n2w:num->(A)word`,n)));;

let rec get_exp x =
  (* Var *)
  try let n = dest_reg x in list_mk_icomb "wordLang_Var" [n]
  with Failure _ ->
  (* Const *)
  try if not (is_n2w x) then failwith "get_exp" else
      list_mk_icomb "wordLang_Const" [x]
  with Failure _ ->
  (* Op *)
  try let _,name = find (fun (pat,_) -> head_is pat x) binops in
      let x1 = get_exp (rand (rator x)) in
      let x2 = get_exp (rand x) in
      list_mk_icomb "wordLang_Op" [name; mk_list([x1; x2],type_of x1)]
  with Failure _ ->
  (* Shift *)
  try let _,name = find (fun (pat,_) -> head_is pat x) shifts in
      let x1 = get_exp (rand (rator x)) in
      let x2 = rand x in
      list_mk_icomb "wordLang_Shift"
        [name; x1; mk_Const_of (word_ty_of x) x2]
  with Failure _ ->
  (* ~ *)
  let r = dest_word_1comp x in
  get_exp (list_mk_icomb "word_xor"
             [r; list_mk_icomb "word_sub"
                   [mk_word r 0; mk_word r 1]]);;

let cmps =
  [`word_lo:(A)word->(A)word->bool`,`asm_Lower`;
   `word_lt:(A)word->(A)word->bool`,`asm_Less`;
   `(=):(A)word->(A)word->bool`,`asm_Equal`];;

let dest_reg_imm ri =
  try mk_Reg (dest_reg ri) with Failure _ ->
  if is_n2w ri then mk_Imm ri else failwith "dest_reg_imm";;

let get_guard b =
  (* Op *)
  try let _,name = find (fun (pat,_) -> head_is pat b) cmps in
      let x1 = dest_reg (rand (rator b)) in
      let x2 = dest_reg_imm (rand b) in
      (name,x1,x2)
  with Failure _ ->
  (* Test *)
  let l,r = dest_eq b in
  if not (is_n2w r && head_is `word_and:(A)word->(A)word->(A)word` l)
  then failwith "get_guard" else
  (`asm_Test`,dest_reg (rand (rator l)),dest_reg_imm (rand l));;

let dest_lupdate_let tm =
  let (v,r),body = my_dest_let tm in
  if not (aconv v (rand r) &&
          head_is `LUPDATE:A->num->(A)list->(A)list` r)
  then failwith "dest_lupdate_let" else
  let x = rand (rator (rator r)) in
  let y = rand (rator r) in
  (x,y,body);;

let dest_el_let tm =
  let (v,r),body = my_dest_let tm in
  if not (head_is `EL:num->(A)list->A` r) then failwith "dest_el_let"
  else
  let a = fst (dest_var (rand r)) in
  let a = if a = "xs" then `In1` else
          if a = "ys" then `In2` else
          if a = "zs" then `Out` else failwith "dest_el_let" in
  let y = rand (rator r) in
  (v,y,a,body);;

let dest_single_add_sub_let pat tm =
  let (v,r),body = my_dest_let tm in
  if not (head_is pat r) then failwith "dest_single_add_sub_let" else
  let a1,a2 = dest_pair v in
  let a1 = dest_reg a1 and a2 = dest_reg a2 in
  let args = snd (strip_comb r) in
  let r1 = dest_reg (el 0 args) in
  let r2 = dest_reg_imm (el 1 args) in
  let r3 = dest_reg_imm (el 2 args) in
  (a1,a2,r1,r2,r3,body);;

let dest_single_add_let =
  dest_single_add_sub_let
    `single_add_word:(A)word->(A)word->(A)word->(A)word#(A)word`;;
let dest_single_sub_let =
  dest_single_add_sub_let
    `single_sub_word:(A)word->(A)word->(A)word->(A)word#(A)word`;;

let dest_single_mul_let tm =
  let (v,r),body = my_dest_let tm in
  if not (head_is
            `single_mul:(A)word->(A)word->(A)word->(A)word#(A)word` r)
  then failwith "dest_single_mul_let" else
  let a1,a2 = dest_pair v in
  let a1 = dest_reg a1 and a2 = dest_reg a2 in
  let args = snd (strip_comb r) in
  let r1 = dest_reg (el 0 args) in
  let r2 = dest_reg (el 1 args) in
  (a1,a2,r1,r2,body);;

let dest_single_div_let tm =
  let (v,r),body = my_dest_let tm in
  if not (head_is
            `single_div:(A)word->(A)word->(A)word->(A)word#(A)word` r)
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
      (list_mk_icomb "word_bignum_Add" [a1;a2;r1;r2;r3],rest)
  with Failure _ ->
  (* Sub *)
  try let a1,a2,r1,r2,r3,rest = dest_single_sub_let tm in
      (list_mk_icomb "word_bignum_Sub" [a1;a2;r1;r2;r3],rest)
  with Failure _ ->
  (* Mul *)
  try let a1,a2,r1,r2,rest = dest_single_mul_let tm in
      (list_mk_icomb "word_bignum_Mul" [a1;a2;r1;r2],rest)
  with Failure _ ->
  (* Div *)
  let a1,a2,r1,r2,r3,rest = dest_single_div_let tm in
  (list_mk_icomb "word_bignum_Div" [a1;a2;r1;r2;r3],rest);;

let code_defs = ref ([]:thm list);;
let prev_trans = ref ([]:(term * term) list);;

(* the name of a function that the translation needs and that is
   not translated yet (HOL4 raises UnableToTranslate for it) *)

let unable_to_translate str = failwith ("UnableToTranslate " ^ str);;

let dest_unable e =
  match e with
    Failure s when String.length s > 19 &&
                   String.sub s 0 19 = "UnableToTranslate " ^ "" ->
      String.sub s 19 (String.length s - 19)
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
        let _,code = find (fun (x,_) -> aconv x f) (!prev_trans) in
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
      let (_,x),_ = my_dest_let tm in
      unable_to_translate (fst (dest_const (repeat rator x))) in
  (* compute deps *)
  let init_prog = get_prog tm in
  (* compute what vars are deleted or assigned *)
  let x = list_mk_conj
            (init_prog ::
             map concl (filter (fun th -> mem (lhs (concl th))
                                              (!immediate_deps))
                               (!code_defs))) in
  let is_delete tm =
    can (term_match [] `(word_bignum_Delete n):(A)mini`) tm in
  let is_assign tm =
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
  let inp = rand (rator (concl (SPEC_ALL def))) in
  let is_rec = can (find_term (aconv f)) tm in
  let rec loop () =
    try get_full_prog inp tm
    with Failure _ as e ->
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
