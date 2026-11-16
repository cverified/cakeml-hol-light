(* ======================================================== *)
(*  crep_inline: ported from HOL4's
    pancake/crep_inlineScript.sml
    A definition theory, with 13 definitions, 1 datatype and no
    theorems.  Needed by from_pancake32Prog.ml,
    from_pancake64Prog.ml, pan_passes.ml and pan_to_crep.ml.  *)
(* ======================================================== *)

(*
  Function inlining pass in crepLang
*)

needs "pancake/crepLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "crep_inline"
  ["crepLang"];;

(* Counting all the variables that appears in a prog *)
let var_prog_def,var_prog_ind = define_guess
  `var_prog x1 =
     match x1 with
       crep_Dec v e p -> APPEND (APPEND [v] (var_cexp e)) (var_prog p)
     | crep_Assign v e -> APPEND [v] (var_cexp e)
     | crep_Store e1 e2 -> APPEND (var_cexp e1) (var_cexp e2)
     | crep_Store32 e1 e2 -> APPEND (var_cexp e1) (var_cexp e2)
     | crep_StoreByte e1 e2 -> APPEND (var_cexp e1) (var_cexp e2)
     | crep_StoreGlob w e -> var_cexp e
     | crep_Seq p1 p2 -> APPEND (var_prog p1) (var_prog p2)
     | crep_If e p1 p2 -> APPEND (APPEND (var_cexp e) (var_prog p1))
       (var_prog p2)
     | crep_While e p -> APPEND (var_cexp e) (var_prog p)
     | crep_Call ctyp e es ->
       let var_ctyp =
         (match ctyp with NONE -> []
           | SOME (vs,NONE) -> vs
           | SOME (vs,SOME (w,hdl)) -> APPEND vs (var_prog hdl)) in APPEND
             (FLAT (MAP var_cexp es)) var_ctyp
     | crep_ExtCall f v1 v2 v3 v4 -> [v1; v2; v3; v4]
     | crep_Return es -> FLAT (MAP var_cexp es)
     | crep_ShMem mop v e -> APPEND [v] (var_cexp e)
     | crep_Primitive lhss pop rhss -> APPEND lhss rhss
     | _ -> []`;;

(* Largest variable of a prog *)
let vmax_prog_def = new_definition
  `vmax_prog p = MAX_LIST (var_prog p)`;;

(* Check if a prog has a return statement or a tail call *)
let has_return_def,has_return_ind = define_guess
  `has_return x1' =
     match x1' with
       crep_Dec v e p -> has_return p
     | crep_Seq p1 p2 -> ((has_return p1) \/ (has_return p2))
     | crep_If e p1 p2 -> ((has_return p1) \/ (has_return p2))
     | crep_While e p -> has_return p
     | crep_Call ctyp e args ->
       (match ctyp with NONE -> T
         | SOME (_,NONE) -> F
         | SOME (_,SOME (w,hdl)) -> has_return hdl)
     | crep_Return e -> T
     | _ -> F`;;

(* This simulate argument loading of a function call.
   Conceptually, only one nested_decs round is needed: "nested_decs args_vname args p", but
   variables in "args" might be shadowed by what are in "args_vname"
 *)
let arg_load_def = new_definition
  `arg_load tmp_vars args args_vname p =
     nested_decs tmp_vars args (nested_decs args_vname (MAP crep_Var
       tmp_vars) p)`;;


(* Whether a function has return in a branching statement, this includes
   Returns inside a While loop
 *)
let not_branch_ret_def,not_branch_ret_ind = define_guess
  `not_branch_ret x1'' =
     match x1'' with
       crep_Dec v e p -> not_branch_ret p
     | crep_Seq p1 p2 -> (not_branch_ret p1 /\ not_branch_ret p2)
     | crep_If e p1 p2 -> (~(has_return p1) /\ ~(has_return p2))
     | crep_While e p -> ~(has_return p)
     | crep_Call ctyp e args ->
       (match ctyp with NONE -> T
          | SOME (_,NONE) -> T
          | SOME (_,SOME (w,hdl)) -> ~(has_return hdl))
     | _ -> T`;;

(* Types of early exit *)
let early_exit_INDUCT,early_exit_RECURSION = define_datatype
  "early_exit =
     crep_inline_Exn
   | crep_inline_Ret
   | crep_inline_Loop_exit";;

(* Eliminate all unreachable code after Return/Raise/Continue/Break
   This treat while loop as a non-stopping statement, as reachability
   of the loop body is not determined at compile time
 *)
let unreach_elim_def,unreach_elim_ind = define_guess
  `unreach_elim p =
     match p with
       crep_Return e -> (crep_Return e,SOME crep_inline_Ret)
     | crep_Raise eid -> (crep_Raise eid,SOME crep_inline_Exn)
     | crep_Break n -> (crep_Break n,SOME crep_inline_Loop_exit)
     | crep_Continue n -> (crep_Continue n,SOME crep_inline_Loop_exit)
     | crep_Seq p1 p2 ->
       let (p1',r1) = unreach_elim p1 in
       (if (~(r1 = NONE)) then (p1',r1) else let (p2',r2) = unreach_elim p2
         in (crep_Seq p1' p2',r2))
     | crep_Dec v e p ->
       let (p',r) = unreach_elim p in (crep_Dec v e p',r)
     | crep_If e p1 p2 ->
       let (p1',r1) = unreach_elim p1 in let
           (p2',r2) = unreach_elim p2 in let
           r3 = (match (r1,r2) with (SOME crep_inline_Ret,e) -> e
                  | (e,SOME crep_inline_Ret) -> e
                  | (SOME crep_inline_Exn,e) -> e
                  | (e,SOME crep_inline_Exn) -> e
                  | (SOME crep_inline_Loop_exit,e) -> e
                  | (e,SOME crep_inline_Loop_exit) -> e
                  | (NONE,NONE) -> NONE) in
           (crep_If e p1' p2',r3)
     | crep_While e p ->
       let (p',r) = unreach_elim p in (crep_While e p',NONE)
     | crep_Call ctyp e args ->
       (match ctyp with NONE -> (crep_Call NONE e args,SOME crep_inline_Ret)
         | SOME (rt,NONE) -> (crep_Call (SOME (rt,NONE)) e args,NONE)
         | SOME (rt,SOME (w,hdl)) ->
             let (hdl',rhdl) = unreach_elim hdl in
               (crep_Call (SOME (rt,SOME (w,hdl'))) e args,NONE))
     | p -> (p,NONE)`;;


(*
  Transformation of Return statements
  rets: variables to be returned to at the call site
*)

(* Transform the callee's body where Returns are not inside any branching statements *)
let transform_eoc_def,transform_eoc_ind = define_guess
  `transform_eoc rets p =
     match p with
       crep_Return es -> crep_nested_seq (MAP2 crep_Assign rets es)
     | crep_Call ctyp e args ->
       (match ctyp with NONE -> crep_Call (SOME (rets,NONE)) e args
         | SOME (rs,NONE) -> crep_Call (SOME (rs,NONE)) e args
         | SOME (rs,SOME (w,hdl)) -> crep_Call (SOME (rs,SOME
           (w,transform_eoc rets hdl))) e args)
     | crep_Dec v e p -> crep_Dec v e (transform_eoc rets p)
     | crep_While e p -> crep_While e (transform_eoc rets p)
     | crep_Seq p1 p2 -> crep_Seq (transform_eoc rets p1) (transform_eoc
       rets p2)
     | crep_If e p1 p2 -> crep_If e (transform_eoc rets p1) (transform_eoc
       rets p2)
     | p -> p`;;

(* Transform the callee's body where are Returns inside branching statments (If/While)
   The implementation is to wrap a While(true) loop around the callee's body and turn
   Returns into multi-level Breaks
 *)
let transform_branch_def,transform_branch_ind = define_guess
  `transform_branch ld rets p =
     match p with
       crep_Return es -> crep_Seq (crep_nested_seq (MAP2 crep_Assign rets
         es)) (crep_Break ld)
     | crep_Call ctyp e args ->
       (match ctyp with NONE -> crep_Seq (crep_Call (SOME (rets,NONE)) e
         args) (crep_Break ld)
         | SOME (rs,NONE) -> crep_Call (SOME (rs,NONE)) e args
         | SOME (rs,SOME (w,hdl)) -> crep_Call (SOME (rs,SOME
           (w,transform_branch ld rets hdl))) e args)
     | crep_Dec v e p -> crep_Dec v e (transform_branch ld rets p)
     | crep_While e p -> crep_While e (transform_branch (ld + 1) rets p)
     | crep_Seq p1 p2 -> crep_Seq (transform_branch ld rets p1)
       (transform_branch ld rets p2)
     | crep_If e p1 p2 -> crep_If e (transform_branch ld rets p1)
       (transform_branch ld rets p2)
     | p -> p`;;

(* Merge the callee body of a tail call into the caller's body, Tick is for clock-synchronization *)
let inline_tail_def = new_definition
  `inline_tail p = crep_Seq crep_Tick p`;;

(* Inline (transformed) function body where the call site is not a tail call
   - p: the transformed callee's body
   - rts: the variables to be returned to, defined at call site
   - temp_rets: temporary variables to avoid shadowing (rts might be shadowed by a variable inside
              the callee's body)
   - tmp_vars: temporary variable to avoid shadowing the function arguments
   - args: expressions to be passed as function arguments
   - args_vname: function arguments original name

   The transformation aims to simulate the behavior of assigning the return results of a call to the variables defined
   at the call site.
   The main transformed body "arg_load _ _ _ _" guarantees to assign the Return values of the call to "temp_rets",
   which means the next "nested_seq _" assigns the Return values of the call back to "rts".
   All the extra treatment of "temp_rets" instead of just storing the results in "rts" is to avoid variables in "rts" shadowing
   a variable appearing in "p".
 *)
let inline_nontail_def = new_definition
  `inline_nontail p rts temp_rets tmp_vars args args_vname =
     nested_decs temp_rets (REPLICATE (LENGTH temp_rets) (crep_Const (n2w
       0)))
       (crep_Seq
           (arg_load tmp_vars args args_vname p)
           (crep_nested_seq (MAP2 crep_Assign rts (MAP crep_Var
             temp_rets))))`;;

(* Perform function inlining over a program's body, with a known inline map.
   This ignores all function calls with a handler.
*)
(* the termination relation that HOL4 gives is
     inv_image (MEASURE I LEX MEASURE (crep_prog_size ARB)) (\(x,y). (CARD
       (FDOM
       x),y))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 crep_inlineScript.sml:250-257: the tactic that proves the
   termination *)
let inline_prog_def,inline_prog_ind = define_guess
  `inline_prog inlineable_fs p =
     match p with
       crep_Call ctyp e args ->
        (let ctyp_inl =
         (match ctyp with NONE -> NONE
            | SOME (x,NONE) -> (SOME (x,NONE))
            | SOME (x,SOME (w,hdl)) -> (SOME (x,SOME (w,inline_prog
              inlineable_fs hdl)))) in
       (if (match ctyp_inl with NONE -> F | SOME (rts,_) -> ~(ALL_DISTINCT
         rts)) then crep_Call ctyp_inl e args else (
        // handling the return vars non distinct case in the semantics
        match FLOOKUP inlineable_fs e with NONE -> crep_Call ctyp_inl e args
          | SOME (args_vname,p) ->
             (let n_inlineable_fs = inlineable_fs \\ e in
             let inlined_callee_unnormalised = inline_prog n_inlineable_fs p
               in
             let (inlined_callee,exit_type) = unreach_elim
               inlined_callee_unnormalised in
             let max_args = MAX_LIST (FLAT (MAP var_cexp args)) in
             let max_args_vname = MAX_LIST args_vname in
             let tmp_vars = list_of_seq (\x. SUC x + MAX max_args
               max_args_vname) (LENGTH args_vname) in
             (match ctyp_inl with NONE -> inline_tail (arg_load tmp_vars
               args args_vname inlined_callee)
                | SOME (rts,hdl) ->
                   (match hdl with NONE ->
                        (let ret_max = MAX_LIST [MAX_LIST rts; vmax_prog
                          inlined_callee; MAX_LIST tmp_vars] in let
                            temp_rets = list_of_seq (\x. SUC x + ret_max)
                              (LENGTH rts) in let
                            // temporary variables to store to in the callee, avoid shadowing with call site
                            n_br = not_branch_ret inlined_callee in let
                            // checks if return statements are inside branching primitives
                            transformed_callee = (if n_br then (crep_Seq
                              crep_Tick (transform_eoc temp_rets
                              inlined_callee))
                              else (crep_While (crep_Const (n2w 1))
                                (transform_branch 0 temp_rets inlined_callee)))
                                in
                         inline_nontail transformed_callee rts temp_rets
                           tmp_vars args args_vname)
                      | SOME w_hdl -> (crep_Call ctyp_inl e args)))))))
     | crep_Dec v e p -> crep_Dec v e (inline_prog inlineable_fs p)
     | crep_Seq p1 p2 ->
       let inline_p1 = inline_prog inlineable_fs p1 in
       let inline_p2 = inline_prog inlineable_fs p2 in
         crep_Seq inline_p1 inline_p2
     | crep_If e p1 p2 ->
       let inline_p1 = inline_prog inlineable_fs p1 in
       let inline_p2 = inline_prog inlineable_fs p2 in
         crep_If e inline_p1 inline_p2
     | crep_While e p -> crep_While e (inline_prog inlineable_fs p)
     | p -> p`;;

let compile_inl_prog_def = new_definition
  `compile_inl_prog inl_fs prog =
       MAP (\(name,params',body). (name,params',inline_prog (inl_fs
         \\ name) body)) prog`;;

let compile_inl_top_def = new_definition
  `compile_inl_top inl_fname prog =
     let inl_fs_alist = FILTER (\(x,y). MEM x inl_fname) prog in let
         inl_fs = alist_to_fmap inl_fs_alist in
     compile_inl_prog inl_fs prog`;;

(* and the interface *)
let _ = unhide_overloads ();;
