(* ======================================================== *)
(*  pan_to_crep: ported from HOL4's
    pancake/pan_to_crepScript.sml
    A definition theory, with 17 definitions, 1 datatype and no
    theorems.  Needed by from_pancake32Prog.ml,
    from_pancake64Prog.ml, pan_passes.ml and pan_to_word.ml.  *)
(* ======================================================== *)

(*
  Compilation from panLang to crepLang.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "lib/byte.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/crep_inline.ml";;
needs "pancake/panLang.ml";;
needs "pancake/pan_common.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_to_crep"
  ["backend_common"; "crepLang"; "crep_inline"; "panLang"; "pan_common"];;

let pan_to_crep_context_FIELDS = define_record "pan_to_crep_context"
  ["vars","(mlstring,shape#num list)fmap";
   "funcs","(mlstring,(mlstring#shape) list#shape)fmap";
   "eids","(mlstring,'a word)fmap";
   "vmax","num"];;

(* using this style to avoid using HD for code extraction later *)
let cexp_heads_def,cexp_heads_ind = define_guess
  `(cexp_heads [] = SOME []) /\
   (cexp_heads (CONS e es) =
       match (e,cexp_heads es) with [],_ -> NONE
       | _,NONE -> NONE
       | CONS x xs,SOME ys -> SOME (CONS x ys))`;;

let comp_field_def,comp_field_ind = define_guess
  `(comp_field i [] es = ([crep_Const (n2w 0)],pan_One)) /\
   (comp_field i (CONS sh shs) es =
       if i = (0:num) then (TAKE (size_of_shape sh) es,sh)
       else comp_field (i - 1) shs (DROP (size_of_shape sh) es))`;;

let compile_panop_def = new_definition
  `compile_panop pan_Mul = crep_Mul`;;

(* the clauses in two quotations: sh is shape and shift, which one quotation
   cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\e. pan_exp_size ARB (SND e))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pan_to_crepScript.sml:98-104: the tactic that proves the termination *)
let pan_to_crep_compile_exp_def,pan_to_crep_compile_exp_ind =
  define_guess_clauses
  [`(pan_to_crep_compile_exp ctxt ((crep_Const c):'a pan_exp) =
       ([(crep_Const c):'a crep_exp],pan_One)) /\
    (pan_to_crep_compile_exp ctxt (pan_Var pan_Local vname) =
       match FLOOKUP (pan_to_crep_context_vars ctxt) vname with SOME
           (shape,ns) -> (MAP pan_Var ns,shape)
       | NONE -> ([crep_Const (n2w 0)],pan_One)) /\
    (pan_to_crep_compile_exp ctxt (pan_Var pan_Global vname) = ([crep_Const
    (n2w 0)],pan_One)) /\
    // should never happen
    (pan_to_crep_compile_exp ctxt (pan_RStruct es) =
    let cexps = MAP (pan_to_crep_compile_exp ctxt) es in
    (FLAT (MAP FST cexps),pan_Comb (MAP SND cexps))) /\
    (pan_to_crep_compile_exp ctxt (pan_RField index e) =
       let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
       match shape with pan_Comb shapes -> comp_field index shapes cexp
       | _ -> ([crep_Const (n2w 0)],pan_One)) /\
    (pan_to_crep_compile_exp ctxt (pan_NStruct nm flds) = ([crep_Const (n2w
    0)],pan_One)) /\
    // should never happen
    (pan_to_crep_compile_exp ctxt (pan_NField fld e) = ([crep_Const (n2w
        0)],pan_One)) /\
    // should never happen
    (pan_to_crep_compile_exp ctxt (pan_Load sh e) =
    let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
    match cexp with CONS e es -> (load_shape ((n2w 0)) (size_of_shape sh)
        e,sh)
    | _ -> ([crep_Const (n2w 0)],pan_One)) /\
    (pan_to_crep_compile_exp ctxt (crep_Load32 e) =
       let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
       match (cexp,shape) with (CONS e es,pan_One) -> ([pan_Load32
           e],pan_One)
       | (_,_) -> ([crep_Const (n2w 0)],pan_One)) /\
    (pan_to_crep_compile_exp ctxt (crep_LoadByte e) =
       let (cexp,shape) = pan_to_crep_compile_exp ctxt e in
       match (cexp,shape) with (CONS e es,pan_One) -> ([pan_LoadByte
           e],pan_One)
       | (_,_) -> ([crep_Const (n2w 0)],pan_One)) /\
    // have a check here for the shape
    (pan_to_crep_compile_exp ctxt (crep_Op bop es) =
    let cexps = MAP FST (MAP (pan_to_crep_compile_exp ctxt) es) in
    match cexp_heads cexps with SOME es -> ([pan_Op bop es],pan_One)
    | _ -> ([crep_Const (n2w 0)],pan_One)) /\
    (pan_to_crep_compile_exp ctxt (pan_Panop pop es) =
       let cexps = MAP FST (MAP (pan_to_crep_compile_exp ctxt) es) in
       match cexp_heads cexps with SOME es -> ([crep_Crepop (compile_panop
           pop) es],pan_One)
       | _ -> ([crep_Const (n2w 0)],pan_One)) /\
    (pan_to_crep_compile_exp ctxt (crep_Cmp cmp e e') =
       let ce = FST (pan_to_crep_compile_exp ctxt e) in let
           ce' = FST (pan_to_crep_compile_exp ctxt e') in
       match (ce,ce') with (CONS e es,CONS e' es') -> ([pan_Cmp cmp e
           e'],pan_One)
       | (_,_) -> ([crep_Const (n2w 0)],pan_One)) /\
    (pan_to_crep_compile_exp ctxt crep_BaseAddr = ([pan_BaseAddr],pan_One)) /\
    (pan_to_crep_compile_exp ctxt crep_TopAddr = ([pan_TopAddr],pan_One)) /\
    (pan_to_crep_compile_exp ctxt pan_BytesInWord = ([crep_Const
    bytes_in_word],pan_One))`;
   `pan_to_crep_compile_exp ctxt (crep_Shift sh e e') =
       let ce = FST (pan_to_crep_compile_exp ctxt e) in let
           ce' = FST (pan_to_crep_compile_exp ctxt e') in
       match (ce,ce') with (CONS e es,CONS e' es') -> ([crep_Shift sh e
           e'],pan_One)
       | _ -> ([crep_Const (n2w 0)],pan_One)`];;

let exp_hdl_def = new_definition
  `exp_hdl fm v =
   match FLOOKUP fm v with NONE -> crep_Skip
   | SOME (vshp,ns) -> crep_nested_seq
       (MAP2 crep_Assign ns (load_globals (n2w 0) (LENGTH ns)))`;;

(* the clauses in two quotations: sh is (shape list) and stcname, which one
   quotation cannot typecheck *)
let ret_var_def = define_cases_clauses
  [`(ret_var pan_One ns = oHD ns) /\
    (ret_var (pan_Comb sh) ns =
         if size_of_shape ((pan_Comb sh:shape)) = 1 then oHD ns
         else NONE)`;
   `ret_var (pan_Named sh) ns = NONE
    // should never happen`];;

(* the clauses in two quotations: sh is (shape list) and stcname, which one
   quotation cannot typecheck *)
let ret_hdl_def = define_cases_clauses
  [`(ret_hdl pan_One ns = pan_Skip) /\
    (ret_hdl (pan_Comb sh) ns =
         if 1 < size_of_shape ((pan_Comb sh:shape)) then (assign_ret ns)
         else pan_Skip)`;
   `ret_hdl (pan_Named sh) ns = pan_Skip
    // should never happen`];;

(* defining it with inner case to enable rewriting later *)
let wrap_rt_def = new_definition
  `wrap_rt n =
     match n with NONE -> NONE
     | SOME (pan_One,[]) -> NONE
     | m -> m`;;

(* the clauses in two quotations: es is ('a exp list) and (('a exp) list); r
   is ('a exp) and varname; v is varname and ('a exp), which one quotation
   cannot typecheck *)
let pan_to_crep_compile_def,pan_to_crep_compile_ind = define_guess_clauses
  [`(pan_to_crep_compile _ (pan_Skip:'a pan_prog) = (crep_Skip:'a crep_prog))
    /\
    (pan_to_crep_compile ctxt (pan_Dec v s e p) =
       ((let (es,sh) = pan_to_crep_compile_exp ctxt e in let
           vmax = pan_to_crep_context_vmax ctxt in let
           nvars = list_of_seq (\x. vmax + SUC x) (size_of_shape sh) in let
           nctxt = pan_to_crep_context_vmax_fupd (K
               (pan_to_crep_context_vmax ctxt + size_of_shape sh))
               (pan_to_crep_context_vars_fupd (K (pan_to_crep_context_vars ctxt
               |+ (v,(sh,nvars)))) ctxt) in
                if size_of_shape sh = LENGTH es then nested_decs nvars es
                    (pan_to_crep_compile nctxt p)
                else crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (pan_Assign pan_Local v e) =
       ((let (es,sh) = pan_to_crep_compile_exp ctxt e in
       match FLOOKUP (pan_to_crep_context_vars ctxt) v with SOME (vshp,ns)
           ->
          if LENGTH ns = LENGTH es then if distinct_lists ns (FLAT (MAP
              var_cexp es)) then crep_nested_seq (MAP2 crep_Assign ns es)
          else let vmax = pan_to_crep_context_vmax ctxt in let
                   temps = list_of_seq (\x. vmax + SUC x) (LENGTH ns) in
               nested_decs temps es
                           (crep_nested_seq (MAP2 crep_Assign ns (MAP
                               crep_Var temps)))
          else crep_Skip:'a crep_prog
        | NONE -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (pan_Assign pan_Global v e) = ((crep_Skip):'a
    crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_Primitive v pop es) =
       ((let cexps = MAP (pan_to_crep_compile_exp ctxt) es in let
           ces = FLAT (MAP FST cexps) in
       match FLOOKUP (pan_to_crep_context_vars ctxt) v with NONE ->
           crep_Skip
       | SOME (vshp,ns) ->
           let vmax = pan_to_crep_context_vmax ctxt in let
               temps = list_of_seq (\x. vmax + SUC x) (LENGTH ces) in
             nested_decs temps ces
                         (crep_Primitive ns pop temps)):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_Store32 dest src) =
       ((match (pan_to_crep_compile_exp ctxt dest,pan_to_crep_compile_exp
           ctxt src) with (CONS ad ads,_),(CONS e es,_) -> crep_Store32 ad e
        | _ -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_StoreByte dest src) =
       ((match (pan_to_crep_compile_exp ctxt dest,pan_to_crep_compile_exp
           ctxt src) with (CONS ad ads,_),(CONS e es,_) -> crep_StoreByte ad e
        | _ -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_Return rt) =
       ((let (ces,sh) = pan_to_crep_compile_exp ctxt rt in
       if size_of_shape sh = 0 then crep_Return []
       else crep_Return ces):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (pan_Raise eid excp) =
        ((match FLOOKUP (pan_to_crep_context_eids ctxt) eid with SOME n ->
          let (ces,sh) = pan_to_crep_compile_exp ctxt excp in let
              temps = list_of_seq (\x. pan_to_crep_context_vmax ctxt + SUC
                  x) (size_of_shape sh) in
           if size_of_shape sh = LENGTH ces then crep_Seq (nested_decs
               temps ces (crep_nested_seq (store_globals (n2w 0) (MAP crep_Var
               temps))))
                    (crep_Raise n)
           else crep_Skip
        | NONE -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_Seq p p') =
        ((crep_Seq (pan_to_crep_compile ctxt p) (pan_to_crep_compile
            ctxt p')):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_If e p p') =
       ((match pan_to_crep_compile_exp ctxt e with (CONS ce ces,_) ->
          crep_If ce (pan_to_crep_compile ctxt p) (pan_to_crep_compile ctxt
              p')
        | _ -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_While e p) =
       ((match pan_to_crep_compile_exp ctxt e with (CONS ce ces,_) ->
         crep_While ce (pan_to_crep_compile ctxt p)
       | _ -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt pan_Break = ((crep_Break 0):'a crep_prog)) /\
    (pan_to_crep_compile ctxt pan_Continue = ((crep_Continue 0):'a
    crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_Call rtyp ce es) =
       ((let cexps = MAP (pan_to_crep_compile_exp ctxt) es in let
           args = FLAT (MAP FST cexps) in
         match rtyp with NONE -> crep_Call NONE ce args
         | SOME (NONE,hdl) ->
             (let rts =
                (match FLOOKUP (pan_to_crep_context_funcs ctxt) ce with
                    NONE -> []
                   | SOME (args,rshape) -> list_of_seq (\x.
                       pan_to_crep_context_vmax ctxt + SUC x) (size_of_shape
                       rshape)) in
             (match hdl with NONE -> nested_decs rts (REPLICATE (LENGTH
                 rts) (crep_Const (n2w 0))) (crep_Call (SOME (rts,NONE)) ce
                 args)
              | SOME (eid,evar,p) ->
                  (match FLOOKUP (pan_to_crep_context_eids ctxt) eid with
                      NONE -> nested_decs rts (REPLICATE (LENGTH rts)
                      (crep_Const (n2w 0))) (crep_Call (SOME (rts,NONE)) ce
                      args)
                   | SOME neid ->
                       let comp_hdl = pan_to_crep_compile ctxt p in let
                           hndlr = crep_Seq (exp_hdl
                               (pan_to_crep_context_vars ctxt) evar) comp_hdl
                               in
                         nested_decs rts (REPLICATE (LENGTH rts)
                             (crep_Const (n2w 0))) (crep_Call (SOME (rts,(SOME
                             (neid,hndlr)))) ce args))))
         | SOME (SOME (rk,rt),hdl) ->
             (match wrap_rt (FLOOKUP (pan_to_crep_context_vars ctxt) rt)
                 with NONE ->
                  (match hdl with NONE -> crep_Call NONE ce args
                   | SOME (eid,evar,p) ->
                       (match FLOOKUP (pan_to_crep_context_eids ctxt) eid
                           with NONE -> crep_Call NONE ce args
                        | SOME neid ->
                            let comp_hdl = pan_to_crep_compile ctxt p in
                                let
                              hndlr = crep_Seq (exp_hdl
                                  (pan_to_crep_context_vars ctxt) evar)
                                  comp_hdl in
                              crep_Call (SOME ([],(SOME (neid,hndlr)))) ce
                                  args))
              | SOME (sh,ns) ->
                  (match hdl with NONE -> crep_Call (SOME (ns,NONE)) ce
                      args
                   | SOME (eid,evar,p) ->
                       (match FLOOKUP (pan_to_crep_context_eids ctxt) eid
                           with NONE -> crep_Call (SOME (ns,NONE)) ce args
                        | SOME neid ->
                            let comp_hdl = pan_to_crep_compile ctxt p in
                                let
                              hndlr = crep_Seq (exp_hdl
                                  (pan_to_crep_context_vars ctxt) evar)
                                  comp_hdl in
                              crep_Call (SOME (ns,(SOME (neid,hndlr))))
                                  ce args)))):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (pan_DecCall v s ce es p) =
       ((let
         cexps = MAP (pan_to_crep_compile_exp ctxt) es in let
         args = FLAT (MAP FST cexps) in let
         vmax = pan_to_crep_context_vmax ctxt in let
         nvars = list_of_seq (\x. vmax + SUC x) (size_of_shape s) in let
         nctxt = pan_to_crep_context_vmax_fupd (K (pan_to_crep_context_vmax
             ctxt + size_of_shape s)) (pan_to_crep_context_vars_fupd (K
             (pan_to_crep_context_vars ctxt |+ (v,(s,nvars)))) ctxt) in let
         ret_dec = nested_decs nvars (REPLICATE (LENGTH nvars) (crep_Const
             (n2w 0))) in let
         p' = pan_to_crep_compile nctxt p in
       ret_dec (crep_Seq (crep_Call (SOME (nvars,NONE)) ce args)
           p')):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (crep_ExtCall f ptr1 len1 ptr2 len2) =
       ((let
         (ptr1',sh1) = pan_to_crep_compile_exp ctxt ptr1 in let
         (len1',sh2) = pan_to_crep_compile_exp ctxt len1 in let
         (ptr2',sh3) = pan_to_crep_compile_exp ctxt ptr2 in let
         (len2',sh4) = pan_to_crep_compile_exp ctxt len2 in let
         n = ITLIST MAX (FLAT (MAP var_cexp (FLAT [ptr1'; len1'; ptr2';
             len2']))) 0 in
         match ((sh1,ptr1'),(sh2,len1'),(sh3,ptr2'),(sh4,len2')) with
             ((pan_One,CONS pc' pcs),(pan_One,CONS lc lcs),
            (pan_One,CONS pc' pcs'),(pan_One,CONS lc' lcs')) ->
             crep_Dec (n + 1) pc'
             (crep_Dec (n + 2) lc
             (crep_Dec (n + 3) pc'
             (crep_Dec (n + 4) lc' (crep_ExtCall f (n + 1) (n + 2) (n + 3)
                 (n + 4)))))
         | _ -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (pan_ShMemStore op r ad) =
       (((match (pan_to_crep_compile_exp ctxt r,pan_to_crep_compile_exp
           ctxt ad) with
          ((CONS e _,_),(CONS a _,_)) ->
            let n = FOLDR MAX 0 (var_cexp e) in
              crep_Dec (n + 1) a (crep_ShMem (store_op op) (n + 1) e)
        | _ -> crep_Skip)):'a crep_prog)) /\
    (pan_to_crep_compile ctxt crep_Tick = ((crep_Tick):'a crep_prog)) /\
    (pan_to_crep_compile _ (pan_Annot _ _) = ((crep_Skip):'a crep_prog))`;
   `(pan_to_crep_compile ctxt (crep_Store ad v) =
       ((match pan_to_crep_compile_exp ctxt ad with (CONS e es',sh') ->
           let (es,sh) = pan_to_crep_compile_exp ctxt v in let
                adv = pan_to_crep_context_vmax ctxt + 1 in let
                temps = list_of_seq (\x. adv + SUC x) (size_of_shape sh) in
                if size_of_shape sh = LENGTH es then nested_decs (CONS adv
                    temps) (CONS e es)
                     (crep_nested_seq (stores (crep_Var adv) (MAP crep_Var
                         temps) (n2w 0)))
                else crep_Skip
        | (_,_) -> crep_Skip):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (pan_ShMemLoad op pan_Local r ad) =
       (((match pan_to_crep_compile_exp ctxt ad with
          (CONS a _,_) ->
            (match FLOOKUP (pan_to_crep_context_vars ctxt) r with
               SOME (_,CONS r' _) -> crep_ShMem (load_op op) r' a
             | _ -> crep_Skip)
         | _ -> crep_Skip)):'a crep_prog)) /\
    (pan_to_crep_compile ctxt (pan_ShMemLoad op pan_Global r ad) =
    ((crep_Skip):'a crep_prog))`];;

let pan_to_crep_mk_ctxt_def = new_definition
  `pan_to_crep_mk_ctxt vmap fs m (es:(mlstring,'a word)fmap) =
      mk_pan_to_crep_context vmap fs es m`;;

(* HOL4 pan_to_crepScript.sml:318-324: code that the source has in a comment *)

(* params : (varname # shape) list *)
let pan_to_crep_make_vmap_def = new_definition
  `pan_to_crep_make_vmap params' =
    let pvars = MAP FST params' in let
        shs = MAP SND params' in let
        ns = list_of_seq I (size_of_shape (pan_Comb shs)) in let
        // defining in this way to make proof in sync with "with_shape"
        cvars = ZIP shs (with_shape shs ns) in
     FEMPTY |++ ZIP pvars cvars`;;

let pan_to_crep_comp_func_def = new_definition
  `pan_to_crep_comp_func fs eids params' body =
     let vmap = pan_to_crep_make_vmap params' in let
         shapes = MAP SND params' in let
         vmax = size_of_shape (pan_Comb shapes) - 1 in
     pan_to_crep_compile (pan_to_crep_mk_ctxt vmap fs vmax eids) body`;;

(* HOL4 pan_to_crepScript.sml:345-353: code that the source has in a comment *)

(* extract eids from exception declarations *)
let get_eids_from_decls_def = new_definition
  `get_eids_from_decls (decls:('a decl) list) =
     let eids = MAP FST (exceptions decls) in let
         // eids = nub eids;
         ns = list_of_seq (\x. (n2w x):'a word) (LENGTH eids) in let
         es = MAP2 (\x y. (x,y)) eids ns in
       alist_to_fmap es`;;

let pan_to_crep_make_funcs_def = new_definition
  `pan_to_crep_make_funcs prog =
   let fnames = MAP FST prog in let
       params' = MAP (FST o SND) prog in let
       returns = MAP (SND o SND o SND) prog in let
       fs = MAP3 (\x y z. (x,y,z)) fnames params' returns in
     alist_to_fmap fs`;;


let crep_vars_def = new_definition
  `crep_vars params' =
   let shapes = MAP SND params' in let
       len = size_of_shape (pan_Comb shapes) in
       list_of_seq I len`;;

let compile_to_crep_def = new_definition
  `compile_to_crep decls =
   let prog = functions decls in let
       comp = pan_to_crep_comp_func (pan_to_crep_make_funcs prog)
         (get_eids_from_decls decls) in
     MAP (\(name,params',body,return).
           (name,
            crep_vars params',
            comp params' body)) prog`;;

let pan_to_crep_compile_prog_def = new_definition
  `pan_to_crep_compile_prog prog =
   let inl_fs_names = MAP FST (functions (FILTER inlinable prog)) in let
       to_crep = compile_to_crep prog in
     compile_inl_top inl_fs_names to_crep`;;

(* and the interface *)
let _ = unhide_overloads ();;
