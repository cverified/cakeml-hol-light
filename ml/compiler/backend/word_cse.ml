(* ======================================================== *)
(*  word_cse: ported from HOL4's
    compiler/backend/word_cseScript.sml  *)
(* ======================================================== *)

(*
  Defines a common sub-expression elimination pass on a wordLang
    program.
  This pass is to run immediately after the SSA-like renaming.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/balanced_map.ml";;
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: words bool *)


(* DATA

  The to_canonical field maps register name r to a canonical name c
  such that registers r and c hold the same value.

  The to_latest field maps canonical name to latest register name
  that has that value. The latest name should always be emitted to
  generate code with as short live ranges as possible (helps register
  allocation).

  The gets_mem field maps store names to canonical registers.

  The instrs_mem field maps instructions to canonical register holding
  the value of that this instruction produces. Note that instructions
  are stored with canonical names only.

  The loads_mem field maps load instructions (keyed by width, canonical
  address register and offset) to the canonical register holding the
  value last loaded from that address. It is kept separate from
  instrs_mem because memory writes must invalidate exactly the load
  facts: a store clears loads_mem and leaves all register-only facts
  intact.

  Conventions:

   - The domain of to_canonical include all names that are mentioned
     anywhere in the data state.

   - The data must be reset to empty, in case we encounter an
     assignment to a name that's in the main of to_canonical, because
     such assignments can make the optimisers state out-of-date.

   - All names in the domain and range of to_canonical must be ODD, so
     that pre-register-allocated registers aren't touched.

   - Every register mentioned by a stored fact — including registers an
     instruction only reads — must be in the domain of to_canonical, so
     that a later write to it resets the data. Reads are entered as
     self-mappings (registered) when a fact is stored.

*)

let knowledge_FIELDS = define_record "knowledge"
  ["to_canonical","num spt";
   "to_latest","num spt";
   "gets_mem","(store_name#num) list";
   "instrs_mem","(num list,num)balanced_map";
   "loads_mem","(num list,num)balanced_map"];;

(* LIST COMPARISON *)

let listCmp_def = cake_define
  `(listCmp ((hd1:num) :: tl1) ((hd2:num) :: tl2) =
    (if hd1 = hd2 then listCmp tl1 tl2 else if hd1 > hd2 then
      (GREATER) else (LESS))) /\
   (listCmp [] [] = (EQUAL)) /\
   (listCmp (hd1 :: tl1) [] = (GREATER)) /\
   (listCmp [] (hd2 :: tl2) = (LESS))`;;

let empty_data_def = cake_define
  `empty_data = mk_knowledge LN LN [] empty empty`;;

(* Whether we're allowed to keep the data
  after writing to this register *)
let keep_data_def = cake_define
  `keep_data canon (write_to_reg:num) =
     IS_NONE (lookup write_to_reg canon)`;;

let invalidate_data_def = cake_define
  `invalidate_data data (write_to_reg:num) =
   (if keep_data (knowledge_to_canonical data) write_to_reg then
     data else empty_data)`;;

(* Invalidate after writing each register in a list (e.g. multi-output
  instructions); empties the data if any of them is tracked. *)
let invalidate_regs_def = cake_define
  `invalidate_regs data [] = data /\
   invalidate_regs data (r :: rs) = invalidate_regs
     (invalidate_data data r) rs`;;

(* Enter an odd register that a stored fact reads into the tracked set
   as a
  self-mapping, so that a later write to it resets the data. Registers
  already tracked, and pre-allocated (EVEN) registers, are left alone.
    *)
let register_read_def = cake_define
  `register_read data (r:num) =
     (if ~EVEN r /\ keep_data (knowledge_to_canonical data) r then
       knowledge_to_canonical_fupd (K (insert r r
       (knowledge_to_canonical data))) data else data)`;;

let register_reads_def = cake_define
  `register_reads data [] = data /\
   register_reads data (r :: rs) = register_reads (register_read
     data r) rs`;;

(* REGISTER TRANSFORMATIONS *)

let canonicalRegs_def = cake_define
  `canonicalRegs (data:knowledge) (r:num) =
   lookup_any r (knowledge_to_canonical data) r`;;

let canonicalRegs'_def = cake_define
  `canonicalRegs' avoid (data:knowledge) (r:num) =
     (let n = canonicalRegs (data:knowledge) (r:num) in
       if n = avoid then r else n)`;;

let canonicalImmReg_def = cake_define
  `canonicalImmReg data (Reg r) = Reg (canonicalRegs data r) /\
   canonicalImmReg data (Imm w) = Imm w`;;

let canonicalImmReg'_def = cake_define
  `canonicalImmReg' avoid data (Reg r) = Reg (canonicalRegs' avoid data
  r) /\
   canonicalImmReg' avoid data (Imm w) = Imm w`;;

let canonicalMultRegs_def = cake_define
  `canonicalMultRegs (data:knowledge) (regs:num list) = MAP
  (canonicalRegs data) regs`;;

let map_insert_def = cake_define
  `map_insert [] m = m /\
   map_insert ((x,y) :: xs) m =
     insert x y (map_insert xs m)`;;

let canonicalMoveRegs_def = cake_define
  `canonicalMoveRegs data moves =
   (let data = register_reads data (MAP SND moves) in
   if EVERY (keep_data (knowledge_to_canonical data)) (MAP FST moves)
     then
     let xs = FILTER (\(a,b). ~EVEN a /\ ~EVEN b) moves in
     let ys = MAP (\(a,b). (a,canonicalRegs data b)) xs in
     let to_c = map_insert ys (knowledge_to_canonical data) in
     let zs = MAP (\(a,b). (b,a)) ys in
     let to_l = map_insert zs (knowledge_to_latest data) in
       knowledge_to_latest_fupd (K to_l) (knowledge_to_canonical_fupd (K
       to_c)
       data) else empty_data)`;;

let canonicalArith_def = cake_define_list
  [`canonicalArith data (Binop op r1 r2 r3) =
      Binop op r1 (canonicalRegs' r1 data r2) (canonicalImmReg'
        r1 data r3)`;
   `canonicalArith data (Shift s r1 r2 ri) =
      Shift s r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1
        data ri)`;
   `canonicalArith data (Div r1 r2 r3) =
      Div r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalArith data (LongMul r1 r2 r3 r4) =
      LongMul r1 r2 (canonicalRegs data r3) (canonicalRegs data
        r4)`;
   `canonicalArith data (LongDiv r1 r2 r3 r4 r5) =
      LongDiv r1 r2 (canonicalRegs data r3) (canonicalRegs data
        r4) (canonicalRegs data r5)`;
   `canonicalArith data (AddCarry r1 r2 r3 r4) =
      AddCarry r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1
        data r3) r4`;
   `canonicalArith data (AddOverflow r1 r2 r3 r4) =
      AddOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs'
        r1 data r3) r4`;
   `canonicalArith data (SubOverflow r1 r2 r3 r4) =
      SubOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs'
        r1 data r3) r4`];;

let canonicalFp_def = cake_define_list
  [`canonicalFp data (FPLess r1 r2 r3) =
      FPLess r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalFp data (FPLessEqual r1 r2 r3) =
      FPLessEqual r1 (canonicalRegs data r2) (canonicalRegs data
        r3)`;
   `canonicalFp data (FPEqual r1 r2 r3) =
      FPEqual r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalFp data (FPAbs r1 r2) =
      FPAbs r1 (canonicalRegs data r2)`;
   `canonicalFp data (FPNeg r1 r2) =
      FPNeg r1 (canonicalRegs data r2)`;
   `canonicalFp data (FPSqrt r1 r2) =
      FPSqrt r1 (canonicalRegs data r2)`;
   `canonicalFp data (FPAdd r1 r2 r3) =
      FPAdd r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalFp data (FPSub r1 r2 r3) =
      FPSub r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalFp data (FPMul r1 r2 r3) =
      FPMul r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalFp data (FPDiv r1 r2 r3) =
      FPDiv r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalFp data (FPFma r1 r2 r3) =
      FPFma r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalFp data (FPMov r1 r2) =
      FPMov r1 (canonicalRegs data r2)`;
   `canonicalFp data (FPMovToReg r1 r2 r3) =
      FPMovToReg r1 (canonicalRegs data r2) (canonicalRegs data
        r3)`;
   `canonicalFp data (FPMovFromReg r1 r2 r3) =
      FPMovFromReg r1 (canonicalRegs data r2) (canonicalRegs data
        r3)`;
   `canonicalFp data (FPToInt r1 r2) =
      FPToInt r1 (canonicalRegs data r2)`;
   `canonicalFp data (FPFromInt r1 r2) =
      FPFromInt r1 (canonicalRegs data r2)`];;

(* SEEN INSTRUCTIONS MEMORY *)

let wordToNum_def = cake_define
  `wordToNum w = w2n w`;;

let shiftToNum_def = cake_define
  `shiftToNum Lsl = (40:num) /\
   shiftToNum Lsr = 41 /\
   shiftToNum Asr = 42 /\
   shiftToNum Ror = 43`;;

let arithOpToNum_def = cake_define
  `arithOpToNum Add = (35:num) /\
   arithOpToNum Sub = 36 /\
   arithOpToNum And = 37 /\
   arithOpToNum Or = 38 /\
   arithOpToNum Xor = 39`;;

let regImmToNumList_def = cake_define
  `regImmToNumList (Reg r) = [33; r + 100] /\
   regImmToNumList (Imm w) = [34; wordToNum w]`;;

let arithToNumList_def = cake_define
  `arithToNumList (Binop op r1 r2 ri) = [25; arithOpToNum op; r2 + 100]
  ++ regImmToNumList ri /\
   arithToNumList (LongMul r1 r2 r3 r4) = [26; r3 + 100; r4 + 100] /\
   arithToNumList (LongDiv r1 r2 r3 r4 r5) = [27; r3 + 100; r4 + 100;
     r5 + 100] /\
   arithToNumList (Shift s r1 r2 ri) = [28; shiftToNum s; r2 + 100]
     ++ regImmToNumList ri /\
   arithToNumList (Div r1 r2 r3) = [29; r2 + 100; r3 + 100] /\
   arithToNumList (AddCarry r1 r2 r3 r4) = [30; r2 + 100; r3 + 100]
     /\
   arithToNumList (AddOverflow r1 r2 r3 r4) = [31; r2 + 100; r3 +
     100] /\
   arithToNumList (SubOverflow r1 r2 r3 r4) = [32; r2 + 100; r3 +
     100]`;;

let memOpToNum_def = cake_define
  `memOpToNum Load = (21:num) /\
   memOpToNum Load8 = 22 /\
   memOpToNum Load16 = 46 /\
   memOpToNum Load32 = 44 /\
   memOpToNum Store = 23 /\
   memOpToNum Store8 = 47 /\
   memOpToNum Store16 = 24 /\
   memOpToNum Store32 = 45`;;

(* Key for a load fact (kept in the separate loads_mem map): the memop
   head
   distinguishes the load widths; the address register is stored
   canonically. *)
let loadToNumList_def = cake_define
  `loadToNumList op (a:num) ofs = [memOpToNum op; a + 100; wordToNum
  ofs]`;;

let fpToNumList_def = cake_define_list
  [`fpToNumList (FPLess r1 r2 r3) = [5; r2 + 100; r3 + 100]`;
   `fpToNumList (FPLessEqual r1 r2 r3) = [6; r2 + 100; r3 + 100]`;
   `fpToNumList (FPEqual r1 r2 r3) = [7; r2 + 100; r3 + 100]`;
   `fpToNumList (FPAbs r1 r2) = [8; r2 + 100]`;
   `fpToNumList (FPNeg r1 r2) = [9; r2 + 100]`;
   `fpToNumList (FPSqrt r1 r2) = [10; r2 + 100]`;
   `fpToNumList (FPAdd r1 r2 r3) = [11; r2 + 100; r3 + 100]`;
   `fpToNumList (FPSub r1 r2 r3) = [12; r2 + 100; r3 + 100]`;
   `fpToNumList (FPMul r1 r2 r3) = [13; r2 + 100; r3 + 100]`;
   `fpToNumList (FPDiv r1 r2 r3) = [14; r2 + 100; r3 + 100]`;
   `fpToNumList (FPFma r1 r2 r3) = [15; r1 + 100; r2 + 100; r3 + 100]`;
   `fpToNumList (FPMov r1 r2) = [16; r2 + 100]`;
   `fpToNumList (FPMovToReg r1 r2 r3) = [17; r2 + 100; r3 + 100]`;
   `fpToNumList (FPMovFromReg r1 r2 r3) = [18; r2 + 100; r3 + 100]`;
   `fpToNumList (FPToInt r1 r2) = [19; r2 + 100]`;
   `fpToNumList (FPFromInt r1 r2) = [20; r2 + 100]`];;

let instToNumList_def = cake_define
  `instToNumList x1 =
      match x1 with
        (Const r w) -> [2; wordToNum w]
      | (Arith a) -> 3 :: (arithToNumList a)
      | (FP fp) -> 4 :: (fpToNumList fp)
      | _1 -> [1]`;;

(*
Principle:
Each unique instruction is converted to a unique num list.
Numbers between 0 and 99 corresponds to a unique identifier of an
  instruction.
Numbers above 99 corresponds to a register or a word value.
*)
let OpCurrHeapToNumList_def = cake_define
  `OpCurrHeapToNumList op r2 = [0; arithOpToNum op; r2 + 100]`;;

(* WORD CSE FUNCTIONS *)

let firstRegOfArith_def = cake_define
  `firstRegOfArith (Binop _2 r _3 _4) = r /\
   firstRegOfArith (Shift _5 r _6 _7) = r /\
   firstRegOfArith (Div r _8 _9) = r /\
   firstRegOfArith (LongMul r _10 _11 _12) = r /\
   firstRegOfArith (LongDiv r _13 _14 _15 _16) = r /\
   firstRegOfArith (AddCarry r _17 _18 _19) = r /\
   firstRegOfArith (AddOverflow r _20 _21 _22) = r /\
   firstRegOfArith (SubOverflow r _23 _24 _25) = r`;;

(* All registers an arith instruction writes (multi-output ops write
   two), so
  that every written register is invalidated. *)
let arithWrites_def = cake_define
  `arithWrites (Binop _26 r _27 _28) = [r] /\
   arithWrites (Shift _29 r _30 _31) = [r] /\
   arithWrites (Div r _32 _33) = [r] /\
   arithWrites (LongMul r1 r2 _34 _35) = [r1; r2] /\
   arithWrites (LongDiv r1 r2 _36 _37 _38) = [r1; r2] /\
   arithWrites (AddCarry r1 _39 _40 r4) = [r1; r4] /\
   arithWrites (AddOverflow r1 _41 _42 r4) = [r1; r4] /\
   arithWrites (SubOverflow r1 _43 _44 r4) = [r1; r4]`;;

(* All registers an arith instruction reads (AddCarry also reads the
  carry-flag register r4). *)
let arithReads_def = cake_define
  `arithReads x1 =
      match x1 with
        (Binop _45 _46 r2 (Reg r3)) -> [r2; r3]
      | (Binop _47 _48 r2 (Imm _49)) -> [r2]
      | (Shift _50 _51 r2 (Reg r3)) -> [r2; r3]
      | (Shift _52 _53 r2 (Imm _54)) -> [r2]
      | (Div _55 r2 r3) -> [r2; r3]
      | (LongMul _56 _57 r3 r4) -> [r3; r4]
      | (LongDiv _58 _59 r3 r4 r5) -> [r3; r4; r5]
      | (AddCarry _60 r2 r3 r4) -> [r2; r3; r4]
      | (AddOverflow _61 r2 r3 _62) -> [r2; r3]
      | (SubOverflow _63 r2 r3 _64) -> [r2; r3]`;;

(* The general-purpose registers an fp instruction writes. Most write
   only
  fp-registers (disjoint from the tracked state), hence []. *)
let fpWrites_def = cake_define
  `fpWrites x1 =
      match x1 with
        (FPLess r _65 _66) -> [r]
      | (FPLessEqual r _67 _68) -> [r]
      | (FPEqual r _69 _70) -> [r]
      | (FPMovToReg r1 r2 _71) -> [r1; r2]
      | _72 -> []`;;

let add_to_data_aux_def = cake_define
  `add_to_data_aux data r i x =
     (match balanced_map_lookup listCmp i (knowledge_instrs_mem data)
       with SOME r' -> (let k = lookup_any r' (knowledge_to_latest data)
       r' in
                    if EVEN r then
                      (data,Move 0 [(r,k)]) else
                      (knowledge_to_latest_fupd (K (insert r' r
                        (knowledge_to_latest data)))
                        (knowledge_to_canonical_fupd (K (insert r r'
                        (knowledge_to_canonical data))) data),Move 0
                        [(r,k)])) | NONE -> (if EVEN r then
                    (data,x) else
                    (knowledge_to_latest_fupd (K (insert r r
                      (knowledge_to_latest data)))
                      (knowledge_to_canonical_fupd (K (insert r r
                      (knowledge_to_canonical data)))
                      (knowledge_instrs_mem_fupd (K (insert listCmp i
                      r (knowledge_instrs_mem data))) data)),x)))`;;

let add_to_data_def = cake_define
  `add_to_data data r adjusted x =
     (let i = instToNumList adjusted in
       add_to_data_aux data r i (Inst x))`;;

(* As add_to_data, but for constants: a constant is rematerialisable for
   free,
   so a repeated Const is NOT replaced by a Move (which would only
     extend the
   holder's live range). The register equivalence is still recorded, so
     later
   instructions reading r are still canonicalised and can be CSE'd.
     Caller
   guards ODD r. *)
let add_to_data_const_def = cake_define
  `add_to_data_const data r w =
     (let i = instToNumList (Const r w) in
       match balanced_map_lookup listCmp i (knowledge_instrs_mem
         data) with SOME r' -> (knowledge_to_latest_fupd (K (insert r' r
         (knowledge_to_latest data))) (knowledge_to_canonical_fupd (K
         (insert r r' (knowledge_to_canonical data))) data),
                     Inst (Const r w)) | NONE ->
                       (knowledge_to_latest_fupd (K (insert r r
                       (knowledge_to_latest data)))
                       (knowledge_to_canonical_fupd (K (insert r r
                       (knowledge_to_canonical data)))
                       (knowledge_instrs_mem_fupd (K (insert listCmp i r
                       (knowledge_instrs_mem data))) data)),
                     Inst (Const r w)))`;;

(* As add_to_data_aux, but for the load-fact map. *)
let add_to_load_aux_def = cake_define
  `add_to_load_aux data r i x =
     (match balanced_map_lookup listCmp i (knowledge_loads_mem data)
       with SOME r' -> (let k = lookup_any r' (knowledge_to_latest data)
       r' in
                    if EVEN r then
                      (data,Move 0 [(r,k)]) else
                      (knowledge_to_latest_fupd (K (insert r' r
                        (knowledge_to_latest data)))
                        (knowledge_to_canonical_fupd (K (insert r r'
                        (knowledge_to_canonical data))) data),Move 0
                        [(r,k)])) | NONE -> (if EVEN r then
                    (data,x) else
                    (knowledge_to_latest_fupd (K (insert r r
                      (knowledge_to_latest data)))
                      (knowledge_to_canonical_fupd (K (insert r r
                      (knowledge_to_canonical data)))
                      (knowledge_loads_mem_fupd (K (insert listCmp i
                      r (knowledge_loads_mem data))) data)),x)))`;;

let can_mem_arith_def = cake_define
  `can_mem_arith x1 =
      match x1 with
        (Binop _73 _74 r1 (Reg r2)) -> (ODD r1 /\ ODD r2)
      | (Binop _75 _76 r1 (Imm _77)) -> ODD r1
      | (Div _78 r1 r2) -> (ODD r1 /\ ODD r2)
      | (Shift _79 _80 r (Imm _81)) -> ODD r
      | _82 -> F`;;

let is_store_def = cake_define
  `(is_store Load = F) /\
   (is_store Load8 = F) /\
   (is_store Load16 = F) /\
   (is_store Load32 = F) /\
   (is_store Store = T) /\
   (is_store Store8 = T) /\
   (is_store Store16 = T) /\
   (is_store Store32 = T)`;;

let word_cseInst_def = cake_define
  `word_cseInst data x2 =
        match (data,x2) with
          ((data:knowledge),Skip) -> (data,Inst Skip)
        | (data,(Const r w)) ->
        let data = invalidate_data data r in
          if EVEN r then (data,Inst (Const r w)) else
            add_to_data_const data r w
        | (data,(Arith a)) ->
        let r = firstRegOfArith a in
        let data = invalidate_regs data (arithWrites a) in
        let a' = canonicalArith data a in
        let rds = arithReads a' in
          if can_mem_arith a' /\ ~MEM r rds then
            add_to_data (register_reads data rds) r (Arith a') (Arith
              a) else
            (data,Inst (Arith a))
        | (data,(Mem op r (Addr a ofs))) ->
        if is_store op then
          (knowledge_loads_mem_fupd (K empty) data,Inst (Mem op r
            (Addr a ofs))) else
          let data = invalidate_data data r in
            if EVEN r \/ EVEN a \/ a = r then (data,Inst (Mem op r
              (Addr a ofs))) else
              let a' = canonicalRegs' r data a in
                add_to_load_aux (register_read data a') r
                  (loadToNumList op a' ofs)
                              (Inst (Mem op r (Addr a ofs)))
        | (data,(FP fp:'a asm_inst)) ->
        (invalidate_regs data (fpWrites fp),Inst (FP fp))`;;

let dest_Var_def = cake_define
  `dest_Var x1 =
      match x1 with
        (Var v:'a wordLang_exp) -> SOME v
      | _83 -> NONE`;;

(* IF-JOIN MERGE

  Knowledge valid after an If is the set of facts that hold after either
  branch: exactly the entries present with equal value on both sides. *)

(* First-order equality-intersection for the instruction map (written
  without higher-order functions so it can be translated by cv_trans).
    *)
let bm_inter_eq_acc_def = cake_define
  `bm_inter_eq_acc m2 Tip acc = acc /\
   bm_inter_eq_acc m2 (Bin n k v l r) acc =
     bm_inter_eq_acc m2 l
       (bm_inter_eq_acc m2 r
         (if balanced_map_lookup listCmp k m2 = SOME v then
           balanced_map_insert listCmp k v acc else acc))`;;

let bm_inter_eq_def = cake_define
  `bm_inter_eq m1 m2 = bm_inter_eq_acc m2 m1 empty`;;

(* to_latest is reset: its entries must stay within the domain of the
   merged
  to_canonical, and they regenerate as soon as new facts are stored. *)
let merge_data_def = cake_define
  `merge_data d1 d2 =
     mk_knowledge (inter_eq (knowledge_to_canonical d1)
       (knowledge_to_canonical d2)) LN (FILTER (\(x,v). ALOOKUP
       (knowledge_gets_mem d2) x = SOME v) (knowledge_gets_mem d1))
       (bm_inter_eq (knowledge_instrs_mem d1) (knowledge_instrs_mem
       d2)) (bm_inter_eq (knowledge_loads_mem d1)
       (knowledge_loads_mem d2))`;;

(*
Principle:
  We keep track of a map containing all instructions already dealt with,
    and we explore the program to find instructions matching one in the
      map.
  If we find one, we change the instruction by a simple move and we keep
    track
    of the registers equivalence.
  If we don't find any, depending on the instruction, we store it into
    the map
    under the shape of an num list.
Signification of the terms:
    r -> registers or imm_registers
    rs-> multiple registers associations ((num # num) list) (For the
      Move)
    i -> instructions
    e -> expressions
    x -> "store_name"
    p -> programs
    c -> comparisons
    m -> num_set
    b -> binop
    s -> string
*)
let word_cse_def = cake_define_list
  [`word_cse data (Move r rs) =
        (let data' = canonicalMoveRegs data rs in
          (data',Move r rs))`;
   `word_cse data (Inst i) =
        (let (data',p) = word_cseInst data i in
          (data',p))`;
   `word_cse data (Get r x) =
        (let data = invalidate_data data r in
          match ALOOKUP (knowledge_gets_mem data) x with NONE -> (if
            EVEN r then (data,Get r x) else
                      (knowledge_to_latest_fupd (K (insert r r
                        (knowledge_to_latest data)))
                        (knowledge_to_canonical_fupd (K (insert r r
                        (knowledge_to_canonical data)))
                        (knowledge_gets_mem_fupd (K ((x,r) ::
                        knowledge_gets_mem data)) data)),
                       Get r x)) | SOME k -> (if EVEN r then
                         (data,Move 1 [(r,lookup_any k
                         (knowledge_to_latest data) k)]) else
                      (knowledge_to_latest_fupd (K (insert k r
                        (knowledge_to_latest data)))
                        (knowledge_to_canonical_fupd (K (insert r k
                        (knowledge_to_canonical data))) data),
                       Move 1 [(r,lookup_any k
                         (knowledge_to_latest data) k)])))`;
   `word_cse data (Set x e) =
        (if x = CurrHeap then
          (empty_data,Set x e) else
          let new_gets_mem = FILTER (\(m,n). ~(m = x))
            (knowledge_gets_mem data) in
            match dest_Var e with NONE -> (knowledge_gets_mem_fupd
              (K new_gets_mem) data,Set x e) | SOME v -> (if EVEN v then
              (knowledge_gets_mem_fupd (K new_gets_mem) data,Set x e)
              else
                          (knowledge_to_canonical_fupd (K (insert v
                            (lookup_any v (knowledge_to_canonical data)
                            v) (knowledge_to_canonical
                              data))) (knowledge_gets_mem_fupd (K
                                ((x,canonicalRegs data v) ::
                                new_gets_mem)) data),
                           Set x e)))`;
   `word_cse data (MustTerminate p) =
                (let (data',p') = word_cse data p in
                    (data',MustTerminate p'))`;
   `word_cse data (Call ret dest args handler) =
                (empty_data,Call ret dest args handler)`;
   `word_cse data (Seq p1 p2) =
        (let (data1,p1') = word_cse data p1 in
        let (data2,p2') = word_cse data1 p2 in
          (data2,Seq p1' p2'))`;
   `word_cse data (If c r1 r2 p1 p2) =
        (let (data1,p1') = word_cse data p1 in
        let (data2,p2') = word_cse data p2 in
          (merge_data data1 data2,If c r1 r2 p1' p2'))`;
   `word_cse data ((OpCurrHeap b r1 r2):'a wordLang_prog) =
        (let data = invalidate_data data r1 in
          if EVEN r2 \/ r2 = r1 then (data,OpCurrHeap b r1 r2) else
            let r2' = canonicalRegs' r1 data r2 in
            let pL = OpCurrHeapToNumList b r2' in
              add_to_data_aux (register_read data r2') r1 pL
                (OpCurrHeap b r1 r2))`;
   `word_cse data (LocValue r l) =
        (let data = invalidate_data data r in
          add_to_data_aux data r [48; l] (LocValue r l))`;
   `word_cse data (Skip) = (data,Skip)`;
   `word_cse data (Store e r) = (knowledge_loads_mem_fupd (K empty)
  data,Store e r)`;
   `word_cse data (Assign r e) = (data,Assign r e)`;
   `word_cse data (Raise r) = (data,Raise r)`;
   `word_cse data (Return r1 r2) = (data,Return r1 r2)`;
   `word_cse data (Tick) = (data,Tick)`;
   `word_cse data (Alloc r m) = (empty_data,Alloc r m)`;
   `word_cse data (Install p l dp dl m) = (empty_data,Install p l dp
  dl m)`;
   `word_cse data (CodeBufferWrite r1 r2) = (data,CodeBufferWrite r1
  r2)`;
   `word_cse data (DataBufferWrite r1 r2) = (data,DataBufferWrite r1
  r2)`;
   `word_cse data (FFI s p1 l1 p2 l2 m) = (empty_data,FFI s p1 l1 p2
  l2 m)`;
   `word_cse data (StoreConsts r1 r2 r3 r4 payload) =
         (let data = invalidate_regs data [r1; r2; r3; r4] in
            (knowledge_loads_mem_fupd (K empty) data,StoreConsts
              r1 r2 r3 r4 payload))`;
   `word_cse data (ShareInst op r exp) =
         (let data = (if is_store op then data else invalidate_data
           data r) in
           (data,ShareInst op r exp))`;
   `word_cse data (Loop names c exit_names) =
         (let (_84,c') = word_cse empty_data c in
           (empty_data,Loop names c' exit_names))`;
   `word_cse data (Break k) = (data,Break k)`;
   `word_cse data (Continue k) = (data,Continue k)`];;

let word_common_subexp_elim_def = cake_define
  `word_common_subexp_elim prog =
     (let (_85,new_prog) = word_cse empty_data prog in
       new_prog)`;;

(* tests *)

let seqs_def = cake_define
  `word_cse_Seqs x1 =
        match x1 with
          [] -> wordLang_Skip
        | [x] -> x
        | (x :: y :: xs) -> Seq x (word_cse_Seqs (y :: xs))`;;
hol4_overload "Seqs" "word_cse_Seqs";;

(* Concrete word type: the load-fact keys compare distinct offsets,
   which is
   only decidable at a fixed word width. *)

(* Loads from the same canonical address at the same width are CSE'd
   (and a
   chain hanging off the loaded value then CSEs too); a different width
     is a
   different fact; any store invalidates all load facts but no register
   facts. *)

(* Set CurrHeap conservatively resets all knowledge (it is not emitted
   by
   data_to_word, so a finer treatment is not worth its proof cost):
     nothing
   after it is CSE'd. *)

(* A repeated LocValue of the same label is CSE'd to a Move. *)

(* LongMul clobbers both outputs (7 and 9), so the value previously
   stored in
   9 is invalidated and the later Add is NOT replaced by a Move from 9.
     *)

(* An instruction that reads the register it writes is not stored as a
   fact,
   so the second Add (reading the NEW 7) is not replaced by a Move. *)

(* Facts valid after both arms of an If survive the join: the Add fact
   (holder 7) is used both inside the first arm and after the join. *)

(* An arm that clobbers a tracked register resets its branch knowledge,
   so
   nothing survives the join and the trailing Add is not CSE'd. *)

(* HOL4 ML code, not ported:
val _ = Theory.delete_const "Seqs";
*)
