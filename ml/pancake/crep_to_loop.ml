(* ======================================================== *)
(*  crep_to_loop: ported from HOL4's
    pancake/crep_to_loopScript.sml
    A definition theory, with 16 definitions, 1 datatype and no
    theorems.  Needed by from_pancake32Prog.ml,
    from_pancake64Prog.ml, pan_passes.ml and pan_to_word.ml.  *)
(* ======================================================== *)

(*
  Compilation from crepLang to loopLang.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/crep_arith.ml";;
needs "pancake/loopLang.ml";;
needs "pancake/loop_live.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "crep_to_loop"
  ["backend_common"; "crepLang"; "crep_arith"; "loopLang"; "loop_live"];;

let crep_to_loop_context_FIELDS = define_record "crep_to_loop_context"
  ["vars","(num,num)fmap";
   "funcs","(mlstring,num#num)fmap";
   (* loc, length args *)
   "vmax","num";
   "target","architecture"];;

let find_var_def = new_definition
  `crep_to_loop_find_var ct v =
    (match FLOOKUP (crep_to_loop_context_vars ct) v with SOME n -> n
     | NONE -> 0)`;;

let crep_to_loop_find_lab_def = new_definition
  `crep_to_loop_find_lab ct f =
    (match FLOOKUP (crep_to_loop_context_funcs ct) f with SOME (n,_) -> n
     | NONE -> 0)`;;

let prog_if_def = new_definition
  `prog_if cmp p q e e' n m l = APPEND (APPEND p q) [
     loop_Assign n e; loop_Assign m e';
     loop_If cmp n (Reg m)
     (loop_Assign n (loop_Const (n2w 1))) (loop_Assign n (loop_Const (n2w
       0))) (list_insert [n; m] l)]`;;

let compile_crepop_def = new_definition
  `(compile_crepop crep_Mul target x y tmp l =
   if target = ARMv7 then
     ([loop_Arith (LLongMul tmp (tmp + 1) x y)],tmp + 1)
   else ([loop_Arith (LLongMul tmp tmp x y)],tmp))`;;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match ISR x with T -> list_size (crep_exp_size ARB) (SND (SND
       (SND (OUTR x))))
                               | F -> crep_exp_size ARB (SND (SND (SND (OUTL
                                 x)))))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 crep_to_loopScript.sml:89-99: the tactic that proves the termination *)
let crep_to_loop_compile_exp_def,crep_to_loop_compile_exp_ind = define_guess
  `(crep_to_loop_compile_exp ctxt tmp l ((crep_BaseAddr):'a crep_exp) =
    ([],crep_BaseAddr,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l ((crep_TopAddr):'a crep_exp) =
    ([],crep_TopAddr,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l ((crep_Const c):'a crep_exp) =
    ([],crep_Const c,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (loop_Var v) = ([],crep_Var
    (crep_to_loop_find_var ctxt v),tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (loop_Load ad) =
       let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l ad in
           (p,crep_Load le,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Load32 ad) =
       let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l ad in
        (APPEND p [crep_Assign tmp le; loop_Load32 tmp tmp],crep_Var
            tmp,tmp + 1,sptree_insert tmp one l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_LoadByte ad) =
       let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l ad in
        (APPEND p [crep_Assign tmp le; loop_LoadByte tmp tmp],crep_Var
            tmp,tmp + 1,sptree_insert tmp one l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_LoadGlob gadr) =
    ([],loop_Lookup gadr,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (loop_Op bop es) =
       let (p,les,tmp,l) = crep_to_loop_compile_exps ctxt tmp l es in
       (p,crep_Op bop les,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp'' l (crep_Crepop cop es) =
       let (p,les,tmp,l) = crep_to_loop_compile_exps ctxt tmp'' l es in let
           (p',tmp') = compile_crepop cop (crep_to_loop_context_target
               ctxt) (tmp) (tmp + 1) (tmp + LENGTH les) (list_insert
               (list_of_seq ((+) tmp) (LENGTH les)) l) in
       (APPEND (APPEND p (MAPi (\n. crep_Assign (tmp + n)) les)) p',
        crep_Var tmp',tmp' + 1,sptree_insert tmp' one (list_insert
            (list_of_seq ((+) tmp) (tmp' - tmp)) l))) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Cmp cmp e e') =
       let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l e in
       let (p',le',tmp',l) = crep_to_loop_compile_exp ctxt tmp l e' in
         (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l,crep_Var (tmp' +
             1),tmp' + 3,
          list_insert [tmp' + 1; tmp' + 2] l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (loop_Shift sh e e') =
       let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l e in
       let (p',le',tmp',l) = crep_to_loop_compile_exp ctxt tmp l e' in
         (APPEND p p',crep_Shift sh le le',tmp',l)) /\
   (crep_to_loop_compile_exps ctxt tmp l cps =
       // to generate ind thm
       match cps with [] -> ([],[],tmp,l)
       | CONS e es ->
         let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l e in
          let (p1,les,tmp,l) = crep_to_loop_compile_exps ctxt tmp l es in
          (APPEND p p1,CONS le les,tmp,l))`;;

let gen_temps_def = new_definition
  `gen_temps n l = list_of_seq (\x. n + x) l`;;

let rt_var_def = define_cases
  `(rt_var fm NONE (n:num) mx = n) /\
   (rt_var fm (SOME v) (n:num) mx =
      match FLOOKUP fm v with NONE -> mx + 1
       |
         // impossible, greater than max to prove a prop later
         SOME m -> m)`;;

let rt_vars_def = new_definition
  `rt_vars fm vs (mx:num) =
     match OPT_MMAP (FLOOKUP fm) vs with NONE -> [mx + 1]
      |
        // impossible, greater than max to prove a prop later
        SOME m -> m`;;

(* the clauses in two quotations: e is ('a exp) and funname, which one
   quotation cannot typecheck *)
let crep_to_loop_compile_def,crep_to_loop_compile_ind = define_guess_clauses
  [`(crep_to_loop_compile _ _ (crep_Skip:'a crep_prog) = (loop_Skip:'a
    loop_prog)) /\
    (crep_to_loop_compile _ _ (loop_Break n) = (((loop_Break n)):'a
    loop_prog)) /\
    (crep_to_loop_compile _ _ (loop_Continue n) = (((loop_Continue n)):'a
    loop_prog)) /\
    (crep_to_loop_compile _ _ loop_Tick = ((loop_Tick):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_Return es) =
        ((let (p,les,ntmp,nl) = crep_to_loop_compile_exps ctxt
            (crep_to_loop_context_vmax ctxt + 1) l es in let
                ntmps = gen_temps ntmp (LENGTH les) in
          loop_nested_seq (APPEND (APPEND p (MAP2 loop_Assign ntmps
              les)) [loop_Return ntmps])):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_Raise eid) =
        ((loop_Seq (loop_Assign (crep_to_loop_context_vmax ctxt + 1)
            (loop_Const eid)) (loop_Raise (crep_to_loop_context_vmax ctxt +
            1))):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_ShMem op r ad) =
        ((match FLOOKUP (crep_to_loop_context_vars ctxt) r with SOME n ->
           let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt
               (crep_to_loop_context_vmax ctxt + 1) l ad in
            loop_nested_seq (APPEND p [loop_ShMem op n le])
         | NONE -> loop_Skip):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_Store dst src) =
        ((let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt
            (crep_to_loop_context_vmax ctxt + 1) l dst in
          let (p',le',tmp,l) = crep_to_loop_compile_exp ctxt tmp l src in
            loop_nested_seq (APPEND (APPEND p p') [loop_Assign tmp le';
                loop_Store le tmp])):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_Store32 dst src) =
        ((let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt
            (crep_to_loop_context_vmax ctxt + 1) l dst in
          let (p',le',tmp,l) = crep_to_loop_compile_exp ctxt tmp l src in
            loop_nested_seq (APPEND (APPEND p p')
                         [loop_Assign tmp le; loop_Assign (tmp + 1) le';
                          loop_Store32 tmp (tmp + 1)])):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_StoreByte dst src) =
        ((let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt
            (crep_to_loop_context_vmax ctxt + 1) l dst in
          let (p',le',tmp,l) = crep_to_loop_compile_exp ctxt tmp l src in
            loop_nested_seq (APPEND (APPEND p p')
                         [loop_Assign tmp le; loop_Assign (tmp + 1) le';
                          loop_StoreByte tmp (tmp + 1)])):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (crep_StoreGlob adr e) =
        ((let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt
            (crep_to_loop_context_vmax ctxt + 1) l e in
            loop_nested_seq (APPEND p [loop_SetGlobal adr le])):'a
                loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_Seq p q) =
        ((loop_Seq (crep_to_loop_compile ctxt l p)
            (crep_to_loop_compile ctxt l q)):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_Assign v e) =
        ((match FLOOKUP (crep_to_loop_context_vars ctxt) v with SOME n ->
           let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt
               (crep_to_loop_context_vmax ctxt + 1) l e in
            loop_nested_seq (APPEND p [loop_Assign n le])
         | NONE -> loop_Skip):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (loop_Primitive lhss pop rhss) =
        ((match (OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) lhss,
              OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) rhss)
                  with (SOME nlhss,SOME nrhss) -> loop_Primitive nlhss pop
                  nrhss
         | _ -> loop_Skip):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (crep_Dec v e prog) =
        ((let (p,le,tmp,nl) = crep_to_loop_compile_exp ctxt
            (crep_to_loop_context_vmax ctxt + 1) l e in let
             nctxt = crep_to_loop_context_vmax_fupd (K tmp)
                 (crep_to_loop_context_vars_fupd (K (crep_to_loop_context_vars
                 ctxt |+ (v,tmp))) ctxt) in let
             fl = sptree_insert tmp one l in let
             lp = crep_to_loop_compile nctxt fl prog in
         loop_Seq (loop_nested_seq p) (loop_Seq (loop_Assign tmp le)
             lp)):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (crep_If e p q) =
        ((let (np,le,tmp,nl) = crep_to_loop_compile_exp ctxt
            (crep_to_loop_context_vmax ctxt + 1) l e in let
            lp = crep_to_loop_compile ctxt l p in let
            lq = crep_to_loop_compile ctxt l q in
        loop_nested_seq (APPEND np [loop_Assign tmp le;
                           loop_If asm_NotEqual tmp (Imm (n2w 0)) lp lq
                               l])):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (crep_While e p) =
        ((let (np,le,tmp,nl) = crep_to_loop_compile_exp ctxt
            (crep_to_loop_context_vmax ctxt + 1) l e in let
            lp = crep_to_loop_compile ctxt l p in
         loop_Loop l (loop_nested_seq (APPEND np [
                    loop_Assign tmp le;
                    loop_If asm_NotEqual tmp (Imm (n2w 0))
                       (loop_Seq lp (loop_Continue 0)) (loop_Break 0) l]))
              l):'a loop_prog)) /\
    (crep_to_loop_compile ctxt l (crep_ExtCall f ptr1 len1 ptr2 len2) =
        ((match (FLOOKUP (crep_to_loop_context_vars ctxt) ptr1,FLOOKUP
            (crep_to_loop_context_vars ctxt) len1,
              FLOOKUP (crep_to_loop_context_vars ctxt) ptr2,FLOOKUP
                  (crep_to_loop_context_vars ctxt) len2) with (SOME pc',SOME
                  lc,SOME pc',SOME lc') ->
             loop_FFI f pc' lc pc' lc' l
         | _ -> loop_Skip):'a loop_prog))`;
   `crep_to_loop_compile ctxt l (crep_Call call_type e es) =
       ((let dest = crep_to_loop_find_lab ctxt e in let
           (p,les,tmp,nl) = crep_to_loop_compile_exps ctxt
               (crep_to_loop_context_vmax ctxt + 1) l es in let
           nargs = gen_temps tmp (LENGTH les) in let
           (rt1,rt2) = (match call_type with NONE -> (NONE,NONE)
             | SOME (rts,hdl) ->
               let rns = rt_vars (crep_to_loop_context_vars ctxt) rts
                   (crep_to_loop_context_vmax ctxt + 1) in let
                   en = crep_to_loop_context_vmax ctxt + 1 in let
                   pe = (match hdl with NONE -> loop_Raise en
                      | SOME (eid,ep) ->
                        let cpe = crep_to_loop_compile ctxt l ep in
                          (loop_If asm_NotEqual en (Imm eid) (loop_Raise
                              en) (loop_Seq loop_Tick cpe) l)) in (SOME
                              (rns,l),SOME (en,pe,loop_Skip,l))) in
          loop_nested_seq (APPEND (APPEND p (MAP2 loop_Assign nargs
              les)) [loop_Call rt1 (SOME dest) nargs rt2])):'a loop_prog)`];;


let ocompile_def = new_definition
  `ocompile ctxt l p = (loop_live_optimise o crep_to_loop_compile ctxt l) p`;;


let mk_ctxt_def = new_definition
  `crep_to_loop_mk_ctxt target vmap fs vmax =
      mk_crep_to_loop_context vmap fs vmax target`;;

let make_vmap_def = new_definition
  `crep_to_loop_make_vmap params' =
     FEMPTY |++ ZIP params' (list_of_seq I (LENGTH params'))`;;

let comp_func_def = new_definition
  `crep_to_loop_comp_func target fs params' body =
     let vmap = crep_to_loop_make_vmap params' in let
         vmax = LENGTH params' - 1 in let
         l = list_to_num_set (list_of_seq I (LENGTH params')) in
     crep_to_loop_compile (crep_to_loop_mk_ctxt target vmap fs vmax) l
       body`;;

let first_name_def = new_definition
  `first_name = (64:num)`;;

let make_funcs_def = new_definition
  `crep_to_loop_make_funcs prog =
   let fnames = MAP FST prog in let
       fnums = list_of_seq (\n. n + first_name) (LENGTH prog) in let
       lens = MAP (LENGTH o FST o SND) prog in let
       fnums_lens = MAP2 (\x y. (x,y)) fnums lens in let
       fs = MAP2 (\x y. (x,y)) fnames fnums_lens in
     alist_to_fmap fs`;;

let crep_to_loop_compile_prog_def = new_definition
  `crep_to_loop_compile_prog target prog =
   let fnums = list_of_seq (\n. n + first_name) (LENGTH prog) in let
       loop_live_comp = crep_to_loop_comp_func target
         (crep_to_loop_make_funcs prog) in
    MAP2 (\n (name,params',body).
          (n,
           (list_of_seq I o LENGTH) params',
           loop_live_optimise (loop_live_comp params' (simp_prog body))))
    fnums prog`;;

(* and the interface *)
let _ = unhide_overloads ();;
