(* ======================================================== *)
(*  pan_structs: ported from HOL4's
    pancake/pan_structsScript.sml
    A definition theory, with 8 definitions, 1 datatype and no
    theorems.  Needed by from_pancake32Prog.ml,
    from_pancake64Prog.ml and pan_to_word.ml.  *)
(* ======================================================== *)

(*
  Convert named structs to raw structs
*)

needs "compiler/backend/backend_common.ml";;
needs "pancake/panLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_structs"
  ["backend_common"; "panLang"];;


(* Context of shapes before conversion *)
let pan_structs_context_FIELDS = define_record "pan_structs_context"
  ["structs","(mlstring#(mlstring#shape) list) list";
   "locals","(mlstring#shape) list";
   "globals","(mlstring#shape) list"];;


(* Return index of x in alist *)
let afindi_def,afindi_ind = define_guess
  `(afindi x [] = NONE) /\
   (afindi x (CONS (k,v) t) =
      if x = k then
        SOME 0
      else match afindi x t with NONE -> NONE
        | SOME i -> SOME (1 + i))`;;

(* Replace named struct shapes with raw structs *)
(* the termination relation that HOL4 gives is
     inv_image
              (
               // lexicographic combination of (struct info list size, shape/s size):
               MEASURE LENGTH LEX MEASURE
                (\x. match x with INL x -> shape_size x
                  | INR x -> list_size shape_size x))
              (
               // getting pair from args:
               \x. match x with INL x -> (FST x,INL (SND x))
                | INR x -> (FST x,INR (SND x)))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pan_structsScript.sml:47-67: the tactic that proves the termination *)
let compile_shape_def,compile_shape_ind = define_guess
  `(compile_shape sctxt pan_One = pan_One) /\
   (compile_shape sctxt (pan_Comb shapes) = pan_Comb (compile_shapes sctxt
    shapes)) /\
   (compile_shape sctxt (pan_Named nm) =
        match dropWhile (\(n,fs). ~(n = nm)) sctxt with CONS (nm,flds)
            sctxt' -> pan_Comb (compile_shapes sctxt' (MAP SND flds))
        | _ -> pan_One) /\
   // should never happen
   (compile_shapes sctxt [] = []) /\
   (compile_shapes sctxt (CONS sh shs) = CONS (compile_shape sctxt sh)
    (compile_shapes sctxt shs))`;;

(* Returns unconverted shape of an expression *)
let old_exp_shape_def,old_exp_shape_ind = define_guess
  `(old_exp_shape ctxt (pan_Var pan_Local v) =
        match ALOOKUP (pan_structs_context_locals ctxt) v with NONE ->
            pan_One
        |
          // should never happen
          SOME sh -> sh) /\
   (old_exp_shape ctxt (pan_Var pan_Global v) =
        match ALOOKUP (pan_structs_context_globals ctxt) v with NONE ->
            pan_One
        |
          // should never happen
          SOME sh -> sh) /\
   (old_exp_shape ctxt (pan_RStruct es) =
        pan_Comb (old_exp_shapes ctxt es)) /\
   (old_exp_shape ctxt (pan_RField index e) =
        match old_exp_shape ctxt e with pan_Comb shs ->
          (match (\l n. oEL n l) shs index with SOME sh -> sh
          | NONE -> pan_One)
        |
          // should never happen
          _ -> pan_One) /\
   // should never happen
   (old_exp_shape ctxt (pan_NStruct nm eflds) = pan_Named nm) /\
   (old_exp_shape ctxt (pan_NField fld e) =
        (match old_exp_shape ctxt e with pan_Named nm ->
          (match ALOOKUP (pan_structs_context_structs ctxt) nm with SOME
              flds ->
            (match ALOOKUP flds fld with SOME sh -> sh
            | NONE -> pan_One)
          |
            // should never happen
            NONE -> pan_One)
        |
          // should never happen
          _ -> pan_One)) /\
   // should never happen
   (old_exp_shape ctxt (pan_Load sh e) = sh) /\
   (old_exp_shape ctxt _ = pan_One) /\
   (old_exp_shapes ctxt [] = []) /\
   (old_exp_shapes ctxt (CONS e es) = CONS (old_exp_shape ctxt e)
    (old_exp_shapes ctxt es))`;;

(* Returns converted expression *)
(* the clauses in two quotations: eflds is ((fldname # exp) list), (_)list
   and (_#_)list; es is (exp list) and (_)list; sh is shape and shift, which
   one quotation cannot typecheck *)
let pan_structs_compile_exp_def,pan_structs_compile_exp_ind =
  define_guess_clauses
  [`(pan_structs_compile_exp ctxt (pan_RStruct es) =
        pan_RStruct (pan_structs_compile_exps ctxt es)) /\
    (pan_structs_compile_exp ctxt (pan_RField index e) =
        pan_RField index (pan_structs_compile_exp ctxt e)) /\
    (pan_structs_compile_exp ctxt (pan_NField fld e) =
        let e' = pan_structs_compile_exp ctxt e in
        let index =
          (match old_exp_shape ctxt e with pan_Named nm ->
            (match ALOOKUP (pan_structs_context_structs ctxt) nm with SOME
                flds ->
              (match afindi fld flds with SOME i -> i
              | NONE -> 0)
            |
              // should never happen
              NONE -> 0)
          |
            // should never happen
            _ -> 0) in
        // should never happen
        pan_RField index e') /\
    (pan_structs_compile_exp ctxt (pan_Load sh e) =
        pan_Load (compile_shape (pan_structs_context_structs ctxt) sh)
            (pan_structs_compile_exp ctxt e)) /\
    (pan_structs_compile_exp ctxt (pan_LoadByte e) =
        pan_LoadByte (pan_structs_compile_exp ctxt e)) /\
    (pan_structs_compile_exp ctxt (pan_Load32 e) =
        pan_Load32 (pan_structs_compile_exp ctxt e)) /\
    (pan_structs_compile_exp ctxt (pan_Op bop es) =
        pan_Op bop (pan_structs_compile_exps ctxt es)) /\
    (pan_structs_compile_exp ctxt (pan_Panop pop es) =
        pan_Panop pop (pan_structs_compile_exps ctxt es)) /\
    (pan_structs_compile_exp ctxt (pan_Cmp cmp e1 e2) =
        pan_Cmp cmp (pan_structs_compile_exp ctxt e1)
            (pan_structs_compile_exp ctxt e2)) /\
    (pan_structs_compile_exp ctxt e = e) /\
    (pan_structs_compile_exps ctxt [] = []) /\
    (pan_structs_compile_exps ctxt (CONS e es) = CONS
    (pan_structs_compile_exp ctxt e) (pan_structs_compile_exps ctxt es)) /\
    (compile_fields ctxt [] = [])`;
   `(pan_structs_compile_exp ctxt (pan_NStruct nm eflds) =
        let eflds' = compile_fields ctxt eflds in let
            es' = (match ALOOKUP (pan_structs_context_structs ctxt) nm with
                SOME flds -> FLAT (MAP (\(nm',sh). match ALOOKUP eflds' nm'
                with NONE -> [] | SOME e -> [e]) flds)
          | NONE -> []) in
        // should never happen
        pan_RStruct es') /\
    (pan_structs_compile_exp ctxt (pan_Shift sh e e') =
        pan_Shift sh (pan_structs_compile_exp ctxt e)
            (pan_structs_compile_exp ctxt e')) /\
    (compile_fields ctxt (CONS (fld,exp) eflds) = CONS
    (fld,pan_structs_compile_exp ctxt exp) (compile_fields ctxt eflds))`];;

(* Returns converted statement *)
let pan_structs_compile_def,pan_structs_compile_ind = define_guess
  `pan_structs_compile ctxt p =
     match p with
       pan_Dec v s e p ->
       pan_Dec v
         (compile_shape (pan_structs_context_structs ctxt) s)
         (pan_structs_compile_exp ctxt e)
         (pan_structs_compile (pan_structs_context_locals_fupd (K (CONS
           (v,s) (pan_structs_context_locals ctxt))) ctxt) p)
     | pan_Assign vk v e ->
       pan_Assign vk v (pan_structs_compile_exp ctxt e)
     | pan_Primitive v pop es ->
       pan_Primitive v pop (pan_structs_compile_exps ctxt es)
     | pan_Store ad v ->
       pan_Store (pan_structs_compile_exp ctxt ad) (pan_structs_compile_exp
         ctxt v)
     | pan_Store32 ad v ->
       pan_Store32 (pan_structs_compile_exp ctxt ad)
         (pan_structs_compile_exp ctxt v)
     | pan_StoreByte dest src ->
       pan_StoreByte (pan_structs_compile_exp ctxt dest)
         (pan_structs_compile_exp ctxt src)
     | pan_Seq p p' ->
       pan_Seq (pan_structs_compile ctxt p) (pan_structs_compile ctxt p')
     | pan_If e p p' ->
       pan_If (pan_structs_compile_exp ctxt e) (pan_structs_compile ctxt p)
         (pan_structs_compile ctxt p')
     | pan_While e p ->
       pan_While (pan_structs_compile_exp ctxt e) (pan_structs_compile ctxt
         p)
     | pan_Call rtyp f es ->
       (let cexps = pan_structs_compile_exps ctxt es in
         match rtyp with NONE -> pan_Call NONE f cexps
         | SOME (tl,hdl) ->
           pan_Call (SOME (tl,
               (match hdl with NONE -> NONE
               | SOME (eid,evar,p) ->
                 SOME (eid,evar,pan_structs_compile ctxt p))))
             f cexps)
     | pan_DecCall v s f es p ->
       pan_DecCall v
         (compile_shape (pan_structs_context_structs ctxt) s) f
         (pan_structs_compile_exps ctxt es)
         (pan_structs_compile (pan_structs_context_locals_fupd (K (CONS
           (v,s) (pan_structs_context_locals ctxt))) ctxt) p)
     | pan_ExtCall f ptr1 len1 ptr2 len2 ->
       pan_ExtCall f
         (pan_structs_compile_exp ctxt ptr1)
         (pan_structs_compile_exp ctxt len1)
         (pan_structs_compile_exp ctxt ptr2)
         (pan_structs_compile_exp ctxt len2)
     | pan_Return rt ->
       pan_Return (pan_structs_compile_exp ctxt rt)
     | pan_Raise eid excp ->
       pan_Raise eid (pan_structs_compile_exp ctxt excp)
     | pan_ShMemStore op r ad ->
      pan_ShMemStore op (pan_structs_compile_exp ctxt r)
        (pan_structs_compile_exp ctxt ad)
     | pan_ShMemLoad op vk r ad ->
      pan_ShMemLoad op vk r (pan_structs_compile_exp ctxt ad)
     | p -> p`;;

(* Returns converted declaration - Names are removed *)
(* the clauses in two quotations: nm is stcname and eid, which one quotation
   cannot typecheck *)
let pan_structs_compile_decs_def,pan_structs_compile_decs_ind =
  define_guess_clauses
  [`(pan_structs_compile_decs ctxt [] = ([],ctxt)) /\
    (pan_structs_compile_decs ctxt (CONS (Decl sh v e) ds) =
        let (ds',ctxt') = pan_structs_compile_decs
            (pan_structs_context_globals_fupd (K (CONS (v,sh)
            (pan_structs_context_globals ctxt))) ctxt) ds in
        (CONS (Decl (compile_shape (pan_structs_context_structs ctxt) sh) v
            (pan_structs_compile_exp ctxt e)) ds',
          ctxt')) /\
    (pan_structs_compile_decs ctxt (CONS (Function fi) ds) =
        let (ds',ctxt') = pan_structs_compile_decs ctxt ds in
        let params' = fun_decl_params fi in
        let fi' = fun_decl_return_fupd (compile_shape
            (pan_structs_context_structs ctxt)) (fun_decl_body_fupd
            (pan_structs_compile (pan_structs_context_locals_fupd (K params')
            ctxt')) (fun_decl_params_fupd (MAP (\(p,s). (p,compile_shape
            (pan_structs_context_structs ctxt) s))) fi)) in
        (CONS (Function fi') ds',ctxt')) /\
    (pan_structs_compile_decs ctxt (CONS (Name nm flds) ds) =
        pan_structs_compile_decs ctxt ds)`;
   `pan_structs_compile_decs ctxt (CONS (ExnDecl nm sh) ds) =
        let (ds',ctxt') = pan_structs_compile_decs ctxt ds in
        (CONS (ExnDecl nm (compile_shape (pan_structs_context_structs
            ctxt) sh)) ds',ctxt')`];;

(* Returns struct context *)
let pan_structs_get_names_def,pan_structs_get_names_ind = define_guess
  `pan_structs_get_names ctxt x2 =
     match x2 with
       [] -> ctxt
     | CONS (Name nm flds) ds ->
       pan_structs_get_names (pan_structs_context_structs_fupd (K (CONS
         (nm,flds) (pan_structs_context_structs ctxt))) ctxt) ds
     | CONS _ ds ->
       pan_structs_get_names ctxt ds`;;

(* Returns converted program *)
let pan_structs_compile_top_def = new_definition
  `pan_structs_compile_top decs =
     let ctxt = mk_pan_structs_context [] [] [] in
     FST (pan_structs_compile_decs (pan_structs_get_names ctxt decs)
       decs)`;;

(* and the interface *)
let _ = unhide_overloads ();;
