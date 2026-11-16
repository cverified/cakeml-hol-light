(* ======================================================== *)
(*  crepLang: ported from HOL4's
    pancake/crepLangScript.sml
    A definition theory, with 11 definitions, 3 datatypes and 1
    theorem.  Needed by 8 files of the port.  *)
(* ======================================================== *)

(*
  Abstract syntax of Crepe language
  Crepe: instructions are similar to that of
  Pancake, but we flatten locals from
  struct-layout to word-layout
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
(* for overloading the shift operation *)
needs "compiler/encoders/asm/asm.ml";;
(* for binop and cmp *)
needs "lib/byte.ml";;
needs "pancake/panLang.ml";;
(* for primop *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "crepLang"
  ["asm"; "backend_common"; "mlstring"; "panLang"];;


new_type_abbrev("crep_shift",`:ast_shift`);;

new_type_abbrev("crep_varname",`:num`);;

new_type_abbrev("crep_funname",`:mlstring`);;

let crepop_INDUCT,crepop_RECURSION = define_datatype
  "crepop =
     // Div |
     crep_Mul
     // | Mod
  ";;

let crep_exp_INDUCT,crep_exp_RECURSION = define_datatype
  "crep_exp =
     crep_Const ('a word)
   | crep_Var crep_varname
   | crep_Load crep_exp
   | crep_Load32 crep_exp
   | crep_LoadByte crep_exp
   | crep_LoadGlob (5 word)
   | crep_Op asm_binop (crep_exp list)
   | crep_Crepop crepop (crep_exp list)
   | crep_Cmp cmp crep_exp crep_exp
   | crep_Shift crep_shift crep_exp crep_exp
   | crep_BaseAddr
   | crep_TopAddr";;

let crep_prog_INDUCT,crep_prog_RECURSION = define_datatype
  "crep_prog =
     crep_Skip
   | crep_Dec crep_varname ('a crep_exp) crep_prog
   | crep_Assign crep_varname ('a crep_exp)
     // dest, source
   | crep_Primitive (crep_varname list) primop (crep_varname list)
     // Since pan_to_crep invents variable names already, we use variables
     // on the RHS (instead of expressions) to piggy-back off of that.
   | crep_Store ('a crep_exp) ('a crep_exp)
     // dest, source
   | crep_Store32 ('a crep_exp) ('a crep_exp)
     // dest, source
   | crep_StoreByte ('a crep_exp) ('a crep_exp)
     // dest, source
   | crep_StoreGlob (5 word) ('a crep_exp)
     // dest, source
   | crep_Seq crep_prog crep_prog
   | crep_If ('a crep_exp) crep_prog crep_prog
   | crep_While ('a crep_exp) crep_prog
   | crep_Break num
   | crep_Continue num
   | crep_Call ((crep_varname list#('a word#crep_prog) option) option)
       crep_funname (('a crep_exp) list)
   | crep_ExtCall crep_funname crep_varname crep_varname crep_varname
       crep_varname
   | crep_Raise ('a word)
   | crep_Return (('a crep_exp) list)
   | crep_ShMem memop crep_varname ('a crep_exp)
   | crep_Tick";;

(* NONE is Tail *)
(* SOME (((varname option) # prog # ((('a word) # prog) option))) is Ret *)
(* (('a word) # prog) is handler *)

(* we can make return varaiable an option, but then might not be able to
   compile to loopLang *)

(* HOL4 crepLangScript.sml:74-80: a theorem whose statement the port cannot
   state yet: MEM_IMP_exp_size *)

let load_shape_def,load_shape_ind = define_guess
  `(load_shape a 0 e = []) /\
   (load_shape a (SUC i) e =
         if a = (n2w 0) then CONS (crep_Load e) (load_shape (a +
             bytes_in_word) i e)
         else CONS (crep_Load (crep_Op asm_Add [e; crep_Const a]))
             (load_shape (a + bytes_in_word) i e))`;;

let crep_nested_seq_def,crep_nested_seq_ind = define_guess
  `(crep_nested_seq [] = crep_Skip) /\
   (crep_nested_seq (CONS e es) = crep_Seq e (crep_nested_seq es))`;;


let stores_def,stores_ind = define_guess
  `(stores ad [] a = []) /\
   (stores ad (CONS e es) a =
         if a = (n2w 0) then CONS (crep_Store ad e) (stores ad es (a +
             bytes_in_word))
         else CONS (crep_Store (crep_Op asm_Add [ad; crep_Const a]) e)
             (stores ad es (a + bytes_in_word)))`;;

let nested_decs_def,nested_decs_ind = define_guess
  `nested_decs x1 x2 p =
     match (x1,x2) with
       ([],[]) -> p
     | (CONS n ns,CONS e es) -> crep_Dec n e (nested_decs ns es p)
     | ([],_) -> crep_Skip
     | (_,[]) -> crep_Skip`;;

let store_globals_def,store_globals_ind = define_guess
  `(store_globals ad [] = []) /\
   (store_globals ad (CONS e es) = CONS (crep_StoreGlob ad e)
    (store_globals (ad + (n2w 1)) es))`;;


let load_globals_def,load_globals_ind = define_guess
  `(load_globals _ 0 = []) /\
   (load_globals ad (SUC n) = CONS (crep_LoadGlob ad) (load_globals (ad +
    (n2w 1)) n))`;;


let assign_ret_def = new_definition
  `assign_ret ns =
     crep_nested_seq (MAP2 crep_Assign ns (load_globals (n2w 0) (LENGTH
       ns)))`;;


(* the termination relation that HOL4 gives is
     MEASURE (\e. crep_exp_size ARB e)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 crepLangScript.sml:141-147: the tactic that proves the termination *)
let var_cexp_def,var_cexp_ind = define_guess
  `var_cexp TopAddrl =
     match TopAddrl with
       crep_Const w -> ([]:num list)
     | crep_Var v -> [v]
     | crep_Load e -> var_cexp e
     | crep_Load32 e -> var_cexp e
     | crep_LoadByte e -> var_cexp e
     | crep_LoadGlob a -> []
     | crep_Op bop es -> FLAT (MAP var_cexp es)
     | crep_Crepop cop es -> FLAT (MAP var_cexp es)
     | crep_Cmp c e1 e2 -> APPEND (var_cexp e1) (var_cexp e2)
     | crep_Shift sh e1 e2 -> APPEND (var_cexp e1) (var_cexp e2)
     | crep_BaseAddr -> []
     | TopAddrl -> []`;;

let assigned_free_vars_def,assigned_free_vars_ind = define_guess
  `assigned_free_vars x1 =
     match x1 with
       crep_Skip -> ([]:num list)
     | crep_Dec n e p -> (FILTER ((\x y. ~(x = y)) n) (assigned_free_vars
       p))
     | crep_Assign n e -> [n]
     | crep_Primitive lhss pop rhss -> lhss
     | crep_Seq p p' -> APPEND (assigned_free_vars p) (assigned_free_vars
       p')
     | crep_If e p p' -> APPEND (assigned_free_vars p) (assigned_free_vars
       p')
     | crep_While e p -> assigned_free_vars p
     | crep_Call (SOME (rts,(SOME (_,p)))) e es -> APPEND rts
       (assigned_free_vars p)
     | crep_Call (SOME (rts,NONE)) e es -> rts
     | crep_ShMem op r ad -> [r]
     | _ -> []`;;

let assigned_vars_def,assigned_vars_ind = define_guess
  `crep_assigned_vars x1' =
     match x1' with
       crep_Skip -> ([]:num list)
     | crep_Dec n e p -> (CONS n (crep_assigned_vars p))
     | crep_Assign n e -> [n]
     | crep_Primitive lhss pop rhss -> lhss
     | crep_Seq p p' -> APPEND (crep_assigned_vars p) (crep_assigned_vars
       p')
     | crep_If e p p' -> APPEND (crep_assigned_vars p) (crep_assigned_vars
       p')
     | crep_While e p -> crep_assigned_vars p
     | crep_Call (SOME (rts,(SOME (_,p)))) e es -> APPEND rts
       (crep_assigned_vars p)
     | crep_Call (SOME (rts,NONE)) e es -> rts
     | crep_ShMem op r ad -> [r]
     | _ -> []`;;

(* HOL4 crepLangScript.sml:179-191: code that the source has in a comment *)

(* the termination relation that HOL4 gives is
     MEASURE (\e. crep_exp_size ARB e)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 crepLangScript.sml:206-212: the tactic that proves the termination *)
let exps_def,exps_ind = define_guess
  `(crepLang_exps (crep_Const w) = [crep_Const w]) /\
   (crepLang_exps (crep_Var v) = [crep_Var v]) /\
   (crepLang_exps (crep_Load e) = crepLang_exps e) /\
   (crepLang_exps (crep_Load32 e) = crepLang_exps e) /\
   (crepLang_exps (crep_LoadByte e) = crepLang_exps e) /\
   (crepLang_exps (crep_LoadGlob a) = [crep_LoadGlob a]) /\
   (crepLang_exps (crep_Op bop es) = FLAT (MAP crepLang_exps es)) /\
   (crepLang_exps (crep_Crepop pop es) = FLAT (MAP crepLang_exps es)) /\
   (crepLang_exps (crep_Cmp c e1 e2) = APPEND (crepLang_exps e1)
    (crepLang_exps e2)) /\
   (crepLang_exps (crep_Shift sh e1 e2) = APPEND (crepLang_exps e1)
    (crepLang_exps e2)) /\
   (crepLang_exps crep_BaseAddr = [crep_BaseAddr]) /\
   (crepLang_exps crep_TopAddr = [crep_TopAddr])`;;

(* HOL4 crepLangScript.sml:214: the overload shift, which the port expands *)

(* and the interface *)
let _ = unhide_overloads ();;
