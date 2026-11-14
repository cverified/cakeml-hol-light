(* ======================================================== *)
(*  word_cse: ported from HOL4's
    compiler/backend/word_cseScript.sml
    A definition theory, with 44 definitions, 1 datatype and 10
    theorems.  Needed by backend.ml, backend_passes.ml,
    wordConvsProof.ml, word_cseProof.ml and word_to_word.ml.  *)
(* ======================================================== *)

(*
  Defines a common sub-expression elimination pass on a wordLang program.
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_cse"
  ["wordLang"];;
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

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let listCmp_def,listCmp_ind = define_wf
  `MEASURE (\(x0,x1). list_size (\n. n) x0 + list_size (\n. n) x1)`
  [`(listCmp (CONS (hd1:num) tl1) (CONS (hd2:num) tl2) =
    (if hd1 = hd2 then listCmp tl1 tl2 else if hd1 > hd2 then
      GREATER else LESS)) /\
   (listCmp [] [] = EQUAL) /\
   (listCmp (CONS hd1 tl1) [] = GREATER) /\
   (listCmp [] (CONS hd2 tl2) = LESS)`];;

let empty_data_def = new_definition
  `empty_data = mk_knowledge LN LN [] balanced_map_empty
  balanced_map_empty`;;

(* Whether we're allowed to keep the data
  after writing to this register *)
let keep_data_def = new_definition
  `keep_data canon (write_to_reg:num) =
     IS_NONE (sptree_lookup write_to_reg canon)`;;

let invalidate_data_def = new_definition
  `invalidate_data data (write_to_reg:num) =
   (if keep_data (knowledge_to_canonical data) write_to_reg then
     data else empty_data)`;;

(* Invalidate after writing each register in a list (e.g. multi-output
  instructions); empties the data if any of them is tracked. *)
let invalidate_regs_def,invalidate_regs_ind = define_rec
  [`invalidate_regs data [] = data`;
   `invalidate_regs data (CONS r rs) = invalidate_regs
    (invalidate_data data r) rs`];;

(* Enter an odd register that a stored fact reads into the tracked set as a
  self-mapping, so that a later write to it resets the data. Registers
  already tracked, and pre-allocated (EVEN) registers, are left alone. *)
let register_read_def = new_definition
  `register_read data (r:num) =
     (if ~(EVEN r) /\ keep_data (knowledge_to_canonical data) r
       then knowledge_to_canonical_fupd (K (balanced_map_insert r r
       (knowledge_to_canonical data))) data else data)`;;

let register_reads_def,register_reads_ind = define_rec
  [`register_reads data [] = data`;
   `register_reads data (CONS r rs) = register_reads (register_read
    data r) rs`];;

(* REGISTER TRANSFORMATIONS *)

let canonicalRegs_def = new_definition
  `canonicalRegs (data:knowledge) (r:num) =
   lookup_any r (knowledge_to_canonical data) r`;;

let canonicalRegs'_def = new_definition
  `canonicalRegs' avoid (data:knowledge) (r:num) =
     (let n = canonicalRegs (data:knowledge) (r:num) in
       if n = avoid then r else n)`;;

let canonicalImmReg_def = define_cases
  [`canonicalImmReg data (Reg r) = Reg (canonicalRegs data r)`;
   `canonicalImmReg data (Imm w) = Imm w`];;

let canonicalImmReg'_def = define_cases
  [`canonicalImmReg' avoid data (Reg r) = Reg (canonicalRegs' avoid
    data r)`;
   `canonicalImmReg' avoid data (Imm w) = Imm w`];;

let canonicalMultRegs_def = new_definition
  `canonicalMultRegs (data:knowledge) (regs':num list) = MAP
  (canonicalRegs data) regs'`;;

let map_insert_def,map_insert_ind = define_rec
  [`map_insert [] m = m`;
   `map_insert (CONS (x,y) xs) m =
      balanced_map_insert x y (map_insert xs m)`];;

let canonicalMoveRegs_def = new_definition
  `canonicalMoveRegs data moves =
   // Register the sources first: a register that is both a source and a
   // destination is then tracked and fails the keep_data check below, so
   // no equivalence is recorded across a self-interfering parallel move.
   (let data = register_reads data (MAP SND moves) in
   if ALL (keep_data (knowledge_to_canonical data)) (MAP FST moves)
     then
     let xs = FILTER (\(a,b). ~(EVEN a) /\ ~(EVEN b)) moves in
     let ys = MAP (\(a,b). (a,canonicalRegs data b)) xs in
     let to_c = map_insert ys (knowledge_to_canonical data) in
     let zs = MAP (\(a,b). (b,a)) ys in
     let to_l = map_insert zs (knowledge_to_latest data) in
       knowledge_to_latest_fupd (K to_l) (knowledge_to_canonical_fupd (K
       to_c)
       data) else empty_data)`;;

let canonicalArith_def = define_cases
  [`canonicalArith data (asm_Binop op r1 r2 r3) =
      asm_Binop op r1 (canonicalRegs' r1 data r2)
          (canonicalImmReg' r1 data r3)`;
   `canonicalArith data (asm_Shift s r1 r2 ri) =
      asm_Shift s r1 (canonicalRegs' r1 data r2)
          (canonicalImmReg' r1 data ri)`;
   `canonicalArith data (asm_Div r1 r2 r3) =
      asm_Div r1 (canonicalRegs data r2) (canonicalRegs data r3)`;
   `canonicalArith data (asm_LongMul r1 r2 r3 r4) =
      asm_LongMul r1 r2 (canonicalRegs data r3) (canonicalRegs
          data r4)`;
   `canonicalArith data (asm_LongDiv r1 r2 r3 r4 r5) =
      asm_LongDiv r1 r2 (canonicalRegs data r3) (canonicalRegs
          data r4) (canonicalRegs data r5)`;
   `canonicalArith data (asm_AddCarry r1 r2 r3 r4) =
      asm_AddCarry r1 (canonicalRegs' r1 data r2) (canonicalRegs'
          r1 data r3) r4`;
   `canonicalArith data (asm_AddOverflow r1 r2 r3 r4) =
      asm_AddOverflow r1 (canonicalRegs' r1 data r2)
          (canonicalRegs' r1 data r3) r4`;
   `canonicalArith data (asm_SubOverflow r1 r2 r3 r4) =
      asm_SubOverflow r1 (canonicalRegs' r1 data r2)
          (canonicalRegs' r1 data r3) r4`];;

let canonicalFp_def = define_cases
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

let wordToNum_def = new_definition
  `wordToNum w = w2n w`;;

let shiftToNum_def = define_cases
  [`shiftToNum Lsl = (40:num)`;
   `shiftToNum Lsr = ((41):num)`;
   `shiftToNum Asr = ((42):num)`;
   `shiftToNum Ror = ((43):num)`];;

let arithOpToNum_def = define_cases
  [`arithOpToNum (asm_Add:binop) = (35:num)`;
   `arithOpToNum (asm_Sub:binop) = ((36):num)`;
   `arithOpToNum (asm_And:binop) = ((37):num)`;
   `arithOpToNum (asm_Or:binop) = ((38):num)`;
   `arithOpToNum (asm_Xor:binop) = ((39):num)`];;

let regImmToNumList_def = define_cases
  [`regImmToNumList (Reg r) = [33; r + 100]`;
   `regImmToNumList (Imm w) = [34; wordToNum w]`];;

let arithToNumList_def = define_cases
  [`arithToNumList (asm_Binop op r1 r2 ri) = APPEND [25; arithOpToNum
    op; r2 + 100] (regImmToNumList ri)`;
   `arithToNumList (asm_LongMul r1 r2 r3 r4) = [26; r3 + 100; r4 +
    100]`;
   `arithToNumList (asm_LongDiv r1 r2 r3 r4 r5) = [27; r3 + 100; r4 +
    100; r5 + 100]`;
   `arithToNumList (asm_Shift s r1 r2 ri) = APPEND [28; shiftToNum s;
    r2 + 100] (regImmToNumList ri)`;
   `arithToNumList (asm_Div r1 r2 r3) = [29; r2 + 100; r3 + 100]`;
   `arithToNumList (asm_AddCarry r1 r2 r3 r4) = [30; r2 + 100; r3 +
    100]`;
   `arithToNumList (asm_AddOverflow r1 r2 r3 r4) = [31; r2 + 100; r3
    + 100]`;
   `arithToNumList (asm_SubOverflow r1 r2 r3 r4) = [32; r2 + 100;
    r3 + 100]`];;

let memOpToNum_def = define_cases
  [`memOpToNum (asm_Load:memop) = (21:num)`;
   `memOpToNum asm_Load8 = ((22):num)`;
   `memOpToNum asm_Load16 = ((46):num)`;
   `memOpToNum (asm_Load32:memop) = ((44):num)`;
   `memOpToNum (asm_Store:memop) = ((23):num)`;
   `memOpToNum asm_Store8 = ((47):num)`;
   `memOpToNum asm_Store16 = ((24):num)`;
   `memOpToNum (asm_Store32:memop) = ((45):num)`];;

(* Key for a load fact (kept in the separate loads_mem map): the memop head
   distinguishes the load widths; the address register is stored
   canonically. *)
let loadToNumList_def = new_definition
  `loadToNumList op (a:num) ofs = [memOpToNum op; a + 100; wordToNum
  ofs]`;;

let fpToNumList_def = define_cases
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
   `// List never matched again
    fpToNumList (FPMov r1 r2) = [16; r2 + 100]`;
   `fpToNumList (FPMovToReg r1 r2 r3) = [17; r2 + 100; r3 + 100]`;
   `fpToNumList (FPMovFromReg r1 r2 r3) = [18; r2 + 100; r3 + 100]`;
   `fpToNumList (FPToInt r1 r2) = [19; r2 + 100]`;
   `fpToNumList (FPFromInt r1 r2) = [20; r2 + 100]`];;

let instToNumList_def = new_definition
  `instToNumList x1 =
      match x1 with
        asm_Const r w -> [2; wordToNum w]
      | (asm_Arith a) -> CONS 3 (arithToNumList a)
      | (asm_FP fp) -> CONS 4 (fpToNumList fp)
      | _1 -> [1]`;;

(*
Principle:
Each unique instruction is converted to a unique num list.
Numbers between 0 and 99 corresponds to a unique identifier of an instruction.
Numbers above 99 corresponds to a register or a word value.
*)
let OpCurrHeapToNumList_def = new_definition
  `OpCurrHeapToNumList op r2 = [0; arithOpToNum op; r2 + 100]`;;

(* WORD CSE FUNCTIONS *)

let firstRegOfArith_def = define_cases
  [`firstRegOfArith (asm_Binop _2 r _3 _4) = r`;
   `firstRegOfArith (asm_Shift _8 r _9 _10) = r`;
   `firstRegOfArith (asm_Div r _13 _14) = r`;
   `firstRegOfArith (asm_LongMul r _15 _16 _17) = r`;
   `firstRegOfArith (asm_LongDiv r _18 _19 _20 _21) = r`;
   `firstRegOfArith (asm_AddCarry r _25 _26 _27) = r`;
   `firstRegOfArith (asm_AddOverflow r _28 _29 _30) = r`;
   `firstRegOfArith (asm_SubOverflow r _31 _32 _33) = r`];;

(* All registers an arith instruction writes (multi-output ops write two), so
  that every written register is invalidated. *)
let arithWrites_def = define_cases
  [`arithWrites (asm_Binop _34 r _35 _36) = [r]`;
   `arithWrites (asm_Shift _40 r _41 _42) = [r]`;
   `arithWrites (asm_Div r _45 _46) = [r]`;
   `arithWrites (asm_LongMul r1 r2 _47 _48) = [r1; r2]`;
   `arithWrites (asm_LongDiv r1 r2 _49 _50 _51) = [r1; r2]`;
   `arithWrites (asm_AddCarry r1 _54 _55 r4) = [r1; r4]`;
   `arithWrites (asm_AddOverflow r1 _56 _57 r4) = [r1; r4]`;
   `arithWrites (asm_SubOverflow r1 _58 _59 r4) = [r1; r4]`];;

(* All registers an arith instruction reads (AddCarry also reads the
  carry-flag register r4). *)
let arithReads_def = new_definition
  `arithReads x1 =
      match x1 with
        asm_Binop _60 _61 r2 (Reg r3) -> [r2; r3]
      | (asm_Binop _62 _63 r2 (Imm _64)) -> [r2]
      | (asm_Shift _65 _66 r2 (Reg r3)) -> [r2; r3]
      | (asm_Shift _67 _68 r2 (Imm _69)) -> [r2]
      | (asm_Div _70 r2 r3) -> [r2; r3]
      | (asm_LongMul _71 _72 r3 r4) -> [r3; r4]
      | (asm_LongDiv _73 _74 r3 r4 r5) -> [r3; r4; r5]
      | (asm_AddCarry _75 r2 r3 r4) -> [r2; r3; r4]
      | (asm_AddOverflow _76 r2 r3 _77) -> [r2; r3]
      | (asm_SubOverflow _78 r2 r3 _79) -> [r2; r3]`;;

(* The general-purpose registers an fp instruction writes. Most write only
  fp-registers (disjoint from the tracked state), hence []. *)
let fpWrites_def = new_definition
  `fpWrites x1 =
      match x1 with
        FPLess r _80 _81 -> [r]
      | (FPLessEqual r _82 _83) -> [r]
      | (FPEqual r _84 _85) -> [r]
      | (FPMovToReg r1 r2 _86) -> [r1; r2]
      | _87 -> []`;;

let add_to_data_aux_def = new_definition
  `add_to_data_aux data r i x =
     (match balanced_map_lookup listCmp i (knowledge_instrs_mem data)
       with SOME r' -> (let k = lookup_any r' (knowledge_to_latest data)
       r' in
                    if EVEN r then
                      (data,wordLang_Move 0 [(r,k)]) else
                      (knowledge_to_latest_fupd (K
                        (balanced_map_insert r' r (knowledge_to_latest
                        data))) (knowledge_to_canonical_fupd (K
                        (balanced_map_insert r r'
                        (knowledge_to_canonical data)))
                        data),wordLang_Move 0 [(r,k)])) | NONE -> (if
                        EVEN r then
                    (data,x) else
                    (knowledge_to_latest_fupd (K
                      (balanced_map_insert r r (knowledge_to_latest
                      data))) (knowledge_to_canonical_fupd (K
                      (balanced_map_insert r r
                      (knowledge_to_canonical data)))
                      (knowledge_instrs_mem_fupd (K
                      (balanced_map_insert listCmp i r
                      (knowledge_instrs_mem data))) data)),x)))`;;

let add_to_data_def = new_definition
  `add_to_data data r adjusted x =
     (let i = instToNumList adjusted in
       add_to_data_aux data r i (wordLang_Inst x))`;;

(* As add_to_data, but for constants: a constant is rematerialisable for free,
   so a repeated Const is NOT replaced by a Move (which would only extend the
   holder's live range). The register equivalence is still recorded, so later
   instructions reading r are still canonicalised and can be CSE'd. Caller
   guards ODD r. *)
let add_to_data_const_def = new_definition
  `add_to_data_const data r w =
     (let i = instToNumList (asm_Const r w) in
       match balanced_map_lookup listCmp i (knowledge_instrs_mem
         data) with SOME r' -> (knowledge_to_latest_fupd (K
         (balanced_map_insert r' r (knowledge_to_latest data)))
         (knowledge_to_canonical_fupd (K (balanced_map_insert r r'
         (knowledge_to_canonical data))) data),
                     wordLang_Inst (asm_Const r w)) | NONE ->
                       (knowledge_to_latest_fupd (K (balanced_map_insert
                       r r (knowledge_to_latest data)))
                       (knowledge_to_canonical_fupd (K
                       (balanced_map_insert r r (knowledge_to_canonical
                       data))) (knowledge_instrs_mem_fupd (K
                       (balanced_map_insert listCmp i r
                       (knowledge_instrs_mem data))) data)),
                     wordLang_Inst (asm_Const r w)))`;;

(* As add_to_data_aux, but for the load-fact map. *)
let add_to_load_aux_def = new_definition
  `add_to_load_aux data r i x =
     (match balanced_map_lookup listCmp i (knowledge_loads_mem data)
       with SOME r' -> (let k = lookup_any r' (knowledge_to_latest data)
       r' in
                    if EVEN r then
                      (data,wordLang_Move 0 [(r,k)]) else
                      (knowledge_to_latest_fupd (K
                        (balanced_map_insert r' r (knowledge_to_latest
                        data))) (knowledge_to_canonical_fupd (K
                        (balanced_map_insert r r'
                        (knowledge_to_canonical data)))
                        data),wordLang_Move 0 [(r,k)])) | NONE -> (if
                        EVEN r then
                    (data,x) else
                    (knowledge_to_latest_fupd (K
                      (balanced_map_insert r r (knowledge_to_latest
                      data))) (knowledge_to_canonical_fupd (K
                      (balanced_map_insert r r
                      (knowledge_to_canonical data)))
                      (knowledge_loads_mem_fupd (K
                      (balanced_map_insert listCmp i r
                      (knowledge_loads_mem data))) data)),x)))`;;

let can_mem_arith_def = new_definition
  `can_mem_arith x1 =
      match x1 with
        asm_Binop _88 _89 r1 (Reg r2) -> (ODD r1 /\ ODD r2)
      | (asm_Binop _90 _91 r1 (Imm _92)) -> ODD r1
      | (asm_Div _93 r1 r2) -> (ODD r1 /\ ODD r2)
      | (asm_Shift _94 _95 r (Imm _96)) -> ODD r
      | _97 -> F`;;

let is_store_def = define_cases
  [`is_store (asm_Load:memop) = F`;
   `is_store asm_Load8 = F`;
   `is_store asm_Load16 = F`;
   `is_store (asm_Load32:memop) = F`;
   `is_store (asm_Store:memop) = T`;
   `is_store asm_Store8 = T`;
   `is_store asm_Store16 = T`;
   `is_store (asm_Store32:memop) = T`];;

let word_cseInst_def = new_definition
  `word_cseInst data x2 =
        match (data,x2) with
          ((data:knowledge),asm_Skip) -> (data,asm_Inst asm_Skip)
        | (data,(asm_Const r w)) ->
        (let data = invalidate_data data r in
          if EVEN r then (data,asm_Inst (asm_Const r w)) else
            add_to_data_const data r w)
        | (data,(asm_Arith a)) ->
        (let r = firstRegOfArith a in
        let data = invalidate_regs data (arithWrites a) in
        let a' = canonicalArith data a in
        let rds = arithReads a' in
          // A fact whose reads include the written register would not describe
          // the post-state, so it is not stored.
          if can_mem_arith a' /\ ~(MEM r rds) then
            add_to_data (register_reads data rds) r (asm_Arith a')
              (asm_Arith a) else
            (data,asm_Inst (asm_Arith a)))
        | (data,(asm_Mem op r (Addr a ofs))) ->
        (if is_store op then
          (knowledge_loads_mem_fupd (K balanced_map_empty)
           // A store writes no register, but it writes memory: all load facts
           // are invalidated. Register-only facts survive.
           data,asm_Inst (asm_Mem op r (Addr a ofs))) else
          let data = invalidate_data data r in
            // A load fact whose address is the written register (a = r) would
            // not describe the post-state; EVEN names are never tracked.
            if EVEN r \/ EVEN a \/ a = r then (data,asm_Inst (asm_Mem
              op r (Addr a ofs))) else
              let a' = canonicalRegs' r data a in
                add_to_load_aux (register_read data a') r
                  (loadToNumList op a' ofs)
                              (asm_Inst (asm_Mem op r (Addr a ofs))))
        | (data,(asm_FP fp:'a asm_inst)) ->
        (invalidate_regs data (fpWrites fp),asm_Inst (asm_FP fp))`;;

let dest_Var_def = new_definition
  `dest_Var x1 =
      match x1 with
        (wordLang_Var v:'a wordLang_exp) -> SOME v
      | _98 -> NONE`;;

(* IF-JOIN MERGE

  Knowledge valid after an If is the set of facts that hold after either
  branch: exactly the entries present with equal value on both sides. *)

(* First-order equality-intersection for the instruction map (written
  without higher-order functions so it can be translated by cv_trans). *)
let bm_inter_eq_acc_def,bm_inter_eq_acc_ind = define_rec
  [`bm_inter_eq_acc m2 Tip acc = acc`;
   `bm_inter_eq_acc m2 (Bin n k v l r) acc =
      bm_inter_eq_acc m2 l
        (bm_inter_eq_acc m2 r
          (if balanced_map_lookup listCmp k m2 = SOME v then
              balanced_map_insert listCmp k v acc else acc))`];;

let bm_inter_eq_def = new_definition
  `bm_inter_eq m1 m2 = bm_inter_eq_acc m2 m1 balanced_map_empty`;;

(* to_latest is reset: its entries must stay within the domain of the merged
  to_canonical, and they regenerate as soon as new facts are stored. *)
let merge_data_def = new_definition
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
    and we explore the program to find instructions matching one in the map.
  If we find one, we change the instruction by a simple move and we keep track
    of the registers equivalence.
  If we don't find any, depending on the instruction, we store it into the map
    under the shape of an num list.
Signification of the terms:
    r -> registers or imm_registers
    rs-> multiple registers associations ((num # num) list) (For the Move)
    i -> instructions
    e -> expressions
    x -> "store_name"
    p -> programs
    c -> comparisons
    m -> num_set
    b -> binop
    s -> string
*)
let word_cse_def,word_cse_ind = define_rec
  [`word_cse data (wordLang_Move r rs) =
        (let data' = canonicalMoveRegs data rs in
          (data',(wordLang_Move r rs:'a wordLang_prog)))`;
   `word_cse data (wordLang_Inst i) =
        (let (data',p) = word_cseInst data i in
          (data',p))`;
   `word_cse data (wordLang_Get r x) =
        (let data = invalidate_data data r in
          match ALOOKUP (knowledge_gets_mem data) x with NONE -> (if
              EVEN r then (data,wordLang_Get r x) else
                      (knowledge_to_latest_fupd (K
                          (balanced_map_insert r r (knowledge_to_latest
                          data))) (knowledge_to_canonical_fupd (K
                          (balanced_map_insert r r
                          (knowledge_to_canonical data)))
                          (knowledge_gets_mem_fupd (K (CONS (x,r)
                          (knowledge_gets_mem data))) data)),
                       wordLang_Get r x)) | SOME k -> (if EVEN r
                           then (data,wordLang_Move 1 [(r,lookup_any k
                           (knowledge_to_latest data) k)]) else
                      (knowledge_to_latest_fupd (K
                          (balanced_map_insert k r (knowledge_to_latest
                          data))) (knowledge_to_canonical_fupd (K
                          (balanced_map_insert r k
                          (knowledge_to_canonical data))) data),
                       wordLang_Move 1 [(r,lookup_any k
                           (knowledge_to_latest data) k)])))`;
   `word_cse data (wordLang_Set x e) =
        (if x = CurrHeap then
          (empty_data,wordLang_Set x e) else
          let new_gets_mem = FILTER (\(m,n). ~(m = x))
              (knowledge_gets_mem data) in
            match dest_Var e with NONE -> (knowledge_gets_mem_fupd
                (K new_gets_mem) data,wordLang_Set x e) |
              // Only ODD source registers are tracked; storing a fact about a
              // pre-allocated (EVEN) register would later reset all knowledge on
              // any write to it, for a fact of little value.
              SOME v -> (if EVEN v then (knowledge_gets_mem_fupd (K
                  new_gets_mem) data,wordLang_Set x e) else
                          (knowledge_to_canonical_fupd (K
                              (balanced_map_insert v (lookup_any v
                              (knowledge_to_canonical data) v)
                              (knowledge_to_canonical
                              data))) (knowledge_gets_mem_fupd (K
                                  (CONS (x,canonicalRegs data v)
                                  new_gets_mem)) data),
                           wordLang_Set x e)))`;
   `word_cse data (wordLang_MustTerminate p) =
                (let (data',p') = word_cse data p in
                    (data',wordLang_MustTerminate p'))`;
   `word_cse data (wordLang_Call ret dest args handler) =
                (empty_data,wordLang_Call ret dest args handler)`;
   `word_cse data (wordLang_Seq p1 p2) =
        (let (data1,p1') = word_cse data p1 in
        let (data2,p2') = word_cse data1 p2 in
          (data2,wordLang_Seq p1' p2'))`;
   `word_cse data (wordLang_If c r1 r2 p1 p2) =
        (let (data1,p1') = word_cse data p1 in
        let (data2,p2') = word_cse data p2 in
          (merge_data data1 data2,wordLang_If c r1 r2 p1' p2'))`;
   `word_cse data ((wordLang_OpCurrHeap b r1 r2):'a wordLang_prog) =
        (let data = invalidate_data data r1 in
          // r2 = r1 reads the register the instruction overwrites; such a fact
          // would not describe the post-state, so it is not stored.
          if EVEN r2 \/ r2 = r1 then (data,wordLang_OpCurrHeap b r1
              r2) else
            let r2' = canonicalRegs' r1 data r2 in
            let pL = OpCurrHeapToNumList b r2' in
              add_to_data_aux (register_read data r2') r1 pL
                  (wordLang_OpCurrHeap b r1 r2))`;
   `word_cse data (wordLang_LocValue r l) =
        // Loc l 0 is a constant determined by l, so CSE it like an immediate.
        // Tag 48 is distinct from every other stored hash head (0, 2, 3).
        (let data = invalidate_data data r in
          add_to_data_aux data r [48; l] (wordLang_LocValue r l))`;
   `word_cse data wordLang_Skip = (data,wordLang_Skip)`;
   `// Store cannot occur in flat code, but it writes memory, so be sound:
    // drop the load facts, keep the register-only facts.
    word_cse data (wordLang_Store e r) =
        (knowledge_loads_mem_fupd (K balanced_map_empty)
        data,wordLang_Store e r)`;
   `word_cse data (wordLang_Assign r e) = (data,(wordLang_Assign r
    e:'a wordLang_prog))`;
   `word_cse data (wordLang_Raise r) = (data,wordLang_Raise r)`;
   `word_cse data (wordLang_Return r1 r2) = (data,wordLang_Return r1
    r2)`;
   `word_cse data wordLang_Tick = (data,wordLang_Tick)`;
   `word_cse data (wordLang_Alloc r m) = (empty_data,wordLang_Alloc r
    m)`;
   `word_cse data (wordLang_Install p l dp dl m) =
    (empty_data,wordLang_Install p l dp dl m)`;
   `// Buffer writes touch only the code/data buffers, nothing we track.
    word_cse data (wordLang_CodeBufferWrite r1 r2) =
        (data,wordLang_CodeBufferWrite r1 r2)`;
   `word_cse data (wordLang_DataBufferWrite r1 r2) =
    (data,wordLang_DataBufferWrite r1 r2)`;
   `// FFI cuts the local environment, so all knowledge is stale.
    word_cse data (wordLang_FFI s p1 l1 p2 l2 m) =
        (empty_data,wordLang_FFI s p1 l1 p2 l2 m)`;
   `// StoreConsts writes (or unsets) only its four register args and memory;
    // the memory writes invalidate the load facts.
    word_cse data (wordLang_StoreConsts r1 r2 r3 r4 payload) =
      (let data = invalidate_regs data [r1; r2; r3; r4] in
         (knowledge_loads_mem_fupd (K balanced_map_empty)
             data,wordLang_StoreConsts r1 r2 r3 r4 payload))`;
   `// Shared-memory op: a load writes its var; a store writes no register.
    // Shared memory (sh_mdomain) is disjoint from the heap memory that load
    // facts describe, so loads_mem survives both.
    word_cse data (wordLang_ShareInst op r exp) =
      (let data = (if is_store op then data else invalidate_data
          data r) in
        (data,wordLang_ShareInst op r exp))`;
   `// Conservative: optimise the loop body from empty state.
    word_cse data (wordLang_Loop names c exit_names) =
      (let (_101,c') = word_cse empty_data c in
        (empty_data,wordLang_Loop names c' exit_names))`;
   `word_cse data (wordLang_Break k) = (data,wordLang_Break k)`;
   `word_cse data (wordLang_Continue k) = (data,wordLang_Continue
    k)`];;

let word_common_subexp_elim_def = new_definition
  `word_common_subexp_elim prog =
     (let (_102,new_prog) = word_cse empty_data prog in
       new_prog)`;;

(* tests *)

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let word_cse_Seqs_def,word_cse_Seqs_ind = define_wf
  `MEASURE (\x0. list_size (wordLang_prog_size (\x. 0)) x0)`
  [`word_cse_Seqs [] = wordLang_Skip`;
   `word_cse_Seqs [x] = x`;
   `word_cse_Seqs (CONS x (CONS y xs)) = wordLang_Seq x
    (word_cse_Seqs (CONS y xs))`];;

(* [local] *)
let test_latest_name_used = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1 (Reg 1)));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 11 1 (Reg
             1)));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 13 1 (Reg
             1)))]) =
     word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_Move 0 [(9,7)];
           wordLang_Move 0 [(11,9)];
           wordLang_Move 0 [(13,11)]]`,
  CHEAT_TAC);;

(* [local] *)
let test_get_set = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Get 1 NextFree;
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_Set NextFree (wordLang_Var 7);
           wordLang_Get 9 NextFree;
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 11 1 (Reg
             1)));
           wordLang_Get 33 NextFree;
           wordLang_Get 35 NextFree;
           wordLang_Get 37 NextFree]) =
     word_cse_Seqs [wordLang_Get 1 NextFree;
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_Set NextFree (wordLang_Var 7);
           wordLang_Move 1 [(9,7)];
           wordLang_Move 0 [(11,9)];
           wordLang_Move 1 [(33,11)];
           wordLang_Move 1 [(35,33)];
           wordLang_Move 1 [(37,35)]]`,
  CHEAT_TAC);;

(* Concrete word type: the load-fact keys compare distinct offsets, which is
   only decidable at a fixed word width. *)
(* [local] *)
let test_pattern_match_and_cons = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Arith (asm_Shift Lsr 301 297
       (Imm ((n2w 9):word64))));
           wordLang_OpCurrHeap asm_Add 305 301;
           wordLang_Inst (asm_Mem asm_Load 309 (Addr 305 (n2w 8)));
           wordLang_Move 0 [(313,297)];
           wordLang_Inst (asm_Arith (asm_Shift Lsr 317 313 (Imm (n2w
             9))));
           wordLang_OpCurrHeap asm_Add 321 317;
           wordLang_Inst (asm_Mem asm_Load 325 (Addr 321 (n2w 16)));
           wordLang_Move 0 [(329,313)];
           wordLang_Inst (asm_Arith (asm_Shift Lsr 333 329 (Imm (n2w
             9))));
           wordLang_OpCurrHeap asm_Add 337 333;
           wordLang_Inst (asm_Mem asm_Load 341 (Addr 337 (n2w 24)));
           wordLang_Get 345 NextFree;
           wordLang_Inst (asm_Const 349 (n2w 0x200000003));
           wordLang_Move 0 [(353,345)];
           wordLang_Inst (asm_Mem asm_Store 349 (Addr 353 (n2w 0)));
           wordLang_Move 0 [(357,353)];
           wordLang_Inst (asm_Mem asm_Store 325 (Addr 357 (n2w 8)));
           wordLang_Move 0 [(361,357)];
           wordLang_Inst (asm_Mem asm_Store 341 (Addr 361 (n2w 16)));
           wordLang_Move 0 [(365,361)];
           wordLang_OpCurrHeap asm_Sub 369 365;
           wordLang_Inst (asm_Arith (asm_Shift Lsl 373 369 (Imm (n2w
             9))));
           wordLang_Inst (asm_Arith (asm_Binop asm_Or 377 373 (Imm
             (n2w 5))));
           wordLang_Move 0 [(381,365)];
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 385 381 (Imm
             (n2w 24))));
           wordLang_Set NextFree (wordLang_Var 385);
           wordLang_Get 389 NextFree;
           wordLang_Inst (asm_Const 393 (n2w 0x200000003));
           wordLang_Move 0 [(397,389)];
           wordLang_Inst (asm_Mem asm_Store 393 (Addr 397 (n2w 0)));
           wordLang_Move 0 [(401,397)];
           wordLang_Inst (asm_Mem asm_Store 309 (Addr 401 (n2w 8)));
           wordLang_Move 0 [(405,401)];
           wordLang_Inst (asm_Mem asm_Store 377 (Addr 405 (n2w 16)));
           wordLang_Move 0 [(409,405)];
           wordLang_OpCurrHeap asm_Sub 413 409;
           wordLang_Inst (asm_Arith (asm_Shift Lsl 417 413 (Imm (n2w
             9))));
           wordLang_Inst (asm_Arith (asm_Binop asm_Or 421 417 (Imm
             (n2w 5))));
           wordLang_Move 0 [(425,409)];
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 429 425 (Imm
             (n2w 24))));
           wordLang_Set NextFree (wordLang_Var 429);
           wordLang_Move 0 [(2,421)]; wordLang_Return 273 [2]]) =
     word_cse_Seqs [wordLang_Inst (asm_Arith (asm_Shift Lsr 301 297
       (Imm (n2w 9))));
           wordLang_OpCurrHeap asm_Add 305 301;
           wordLang_Inst (asm_Mem asm_Load 309 (Addr 305 (n2w 8)));
           wordLang_Move 0 [(313,297)];
           wordLang_Move 0 [(317,301)];
           wordLang_Move 0 [(321,305)];
           wordLang_Inst (asm_Mem asm_Load 325 (Addr 321 (n2w 16)));
           wordLang_Move 0 [(329,313)];
           wordLang_Move 0 [(333,317)];
           wordLang_Move 0 [(337,321)];
           wordLang_Inst (asm_Mem asm_Load 341 (Addr 337 (n2w 24)));
           wordLang_Get 345 NextFree;
           wordLang_Inst (asm_Const 349 (n2w 0x200000003));
           wordLang_Move 0 [(353,345)];
           wordLang_Inst (asm_Mem asm_Store 349 (Addr 353 (n2w 0)));
           wordLang_Move 0 [(357,353)];
           wordLang_Inst (asm_Mem asm_Store 325 (Addr 357 (n2w 8)));
           wordLang_Move 0 [(361,357)];
           wordLang_Inst (asm_Mem asm_Store 341 (Addr 361 (n2w 16)));
           wordLang_Move 0 [(365,361)];
           wordLang_OpCurrHeap asm_Sub 369 365;
           wordLang_Inst (asm_Arith (asm_Shift Lsl 373 369 (Imm (n2w
             9))));
           wordLang_Inst (asm_Arith (asm_Binop asm_Or 377 373 (Imm
             (n2w 5))));
           wordLang_Move 0 [(381,365)];
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 385 381 (Imm
             (n2w 24))));
           wordLang_Set NextFree (wordLang_Var 385);
           wordLang_Move 1 [(389,385)];
           wordLang_Inst (asm_Const 393 (n2w 0x200000003));
           wordLang_Move 0 [(397,389)];
           wordLang_Inst (asm_Mem asm_Store 393 (Addr 397 (n2w 0)));
           wordLang_Move 0 [(401,397)];
           wordLang_Inst (asm_Mem asm_Store 309 (Addr 401 (n2w 8)));
           wordLang_Move 0 [(405,401)];
           wordLang_Inst (asm_Mem asm_Store 377 (Addr 405 (n2w 16)));
           wordLang_Move 0 [(409,405)];
           wordLang_OpCurrHeap asm_Sub 413 409;
           wordLang_Inst (asm_Arith (asm_Shift Lsl 417 413 (Imm (n2w
             9))));
           wordLang_Inst (asm_Arith (asm_Binop asm_Or 421 417 (Imm
             (n2w 5))));
           wordLang_Move 0 [(425,409)];
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 429 425 (Imm
             (n2w 24))));
           wordLang_Set NextFree (wordLang_Var 429);
           wordLang_Move 0 [(2,421)];
           wordLang_Return 273 [2]]`,
  CHEAT_TAC);;

(* Loads from the same canonical address at the same width are CSE'd (and a
   chain hanging off the loaded value then CSEs too); a different width is a
   different fact; any store invalidates all load facts but no register
   facts. *)
(* [local] *)
let test_load_cse = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Mem asm_Load 9 (Addr 7 ((n2w
       0):word64)));
           wordLang_Inst (asm_Arith (asm_Shift Lsr 11 9 (Imm (n2w
             29))));
           wordLang_Inst (asm_Mem asm_Load 13 (Addr 7 (n2w 0)));
           wordLang_Inst (asm_Arith (asm_Shift Lsr 15 13 (Imm (n2w
             29))));
           wordLang_Inst (asm_Mem asm_Load8 17 (Addr 7 (n2w 0)));
           wordLang_Inst (asm_Mem asm_Store 15 (Addr 7 (n2w 0)));
           wordLang_Inst (asm_Mem asm_Load 19 (Addr 7 (n2w 0)))]) =
     word_cse_Seqs [wordLang_Inst (asm_Mem asm_Load 9 (Addr 7 (n2w
       0)));
           wordLang_Inst (asm_Arith (asm_Shift Lsr 11 9 (Imm (n2w
             29))));
           wordLang_Move 0 [(13,9)];
           wordLang_Move 0 [(15,11)];
           wordLang_Inst (asm_Mem asm_Load8 17 (Addr 7 (n2w 0)));
           wordLang_Inst (asm_Mem asm_Store 15 (Addr 7 (n2w 0)));
           wordLang_Inst (asm_Mem asm_Load 19 (Addr 7 (n2w 0)))]`,
  CHEAT_TAC);;

(* Set CurrHeap conservatively resets all knowledge (it is not emitted by
   data_to_word, so a finer treatment is not worth its proof cost): nothing
   after it is CSE'd. *)
(* [local] *)
let test_set_currheap = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_OpCurrHeap asm_Add 3 1;
           wordLang_Set CurrHeap (wordLang_Var 7);
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1 (Reg 1)));
           wordLang_OpCurrHeap asm_Add 5 1]) =
     word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_OpCurrHeap asm_Add 3 1;
           wordLang_Set CurrHeap (wordLang_Var 7);
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1 (Reg 1)));
           wordLang_OpCurrHeap asm_Add 5 1]`,
  CHEAT_TAC);;

(* A repeated LocValue of the same label is CSE'd to a Move. *)
(* [local] *)
let test_locvalue = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_LocValue 7 100; wordLang_LocValue 9
       100]) =
     word_cse_Seqs [wordLang_LocValue 7 100; wordLang_Move 0
       [(9,7)]]`,
  CHEAT_TAC);;

(* LongMul clobbers both outputs (7 and 9), so the value previously stored in
   9 is invalidated and the later Add is NOT replaced by a Move from 9. *)
(* [local] *)
let test_multi_output_invalidation = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1
       (Reg 1)));
           wordLang_Inst (asm_Arith (asm_LongMul 7 9 3 5));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 11 1 (Reg
             1)))]) =
     word_cse_Seqs [wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1
       (Reg 1)));
           wordLang_Inst (asm_Arith (asm_LongMul 7 9 3 5));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 11 1 (Reg
             1)))]`,
  CHEAT_TAC);;

(* An instruction that reads the register it writes is not stored as a fact,
   so the second Add (reading the NEW 7) is not replaced by a Move. *)
(* [local] *)
let test_self_read_not_cse = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 7
       (Imm (n2w 1))));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 7 (Imm (n2w
             1))))]) =
     word_cse_Seqs [wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 7
       (Imm (n2w 1))));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 7 (Imm
             (n2w 1))))]`,
  CHEAT_TAC);;

(* Facts valid after both arms of an If survive the join: the Add fact
   (holder 7) is used both inside the first arm and after the join. *)
(* [local] *)
let test_if_merge = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_If EQUAL 1 (Imm (n2w 0))
              (wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1 (Reg
                1))))
              (wordLang_Move 0 [(11,7)]);
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 13 1 (Reg
             1)))]) =
     word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_If EQUAL 1 (Imm (n2w 0)) (wordLang_Move 0
             [(9,7)]) (wordLang_Move 0 [(11,7)]);
           wordLang_Move 0 [(13,7)]]`,
  CHEAT_TAC);;

(* An arm that clobbers a tracked register resets its branch knowledge, so
   nothing survives the join and the trailing Add is not CSE'd. *)
(* [local] *)
let test_if_merge_clobber = prove
 (`word_common_subexp_elim
     (word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_If EQUAL 1 (Imm (n2w 0))
              (wordLang_Move 0 [(7,3)])
              wordLang_Skip;
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1 (Reg
             1)))]) =
     word_cse_Seqs [wordLang_Inst (asm_Const 1 (n2w 0));
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 7 1 (Reg 1)));
           wordLang_If EQUAL 1 (Imm (n2w 0)) (wordLang_Move 0
             [(7,3)]) wordLang_Skip;
           wordLang_Inst (asm_Arith (asm_Binop asm_Add 9 1 (Reg
             1)))]`,
  CHEAT_TAC);;

(* HOL4 word_cseScript.sml:905: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
