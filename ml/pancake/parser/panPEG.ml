(* ======================================================== *)
(*  panPEG: ported from HOL4's
    pancake/parser/panPEGScript.sml
    A definition theory, with 23 definitions, 1 datatype and 18
    theorems.  Needed by panPtreeConversion.ml and
    pancake_parseProg.ml.  *)
(* ======================================================== *)

(**
 * The beginnings of a PEG parser for the Pancake language.
 *)

(*
 * We take significant inspiration from the Spark ADA development.
 *)

needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "compiler/backend/word_depth.ml";;
needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexpParse.ml";;
needs "pancake/parser/panLexer.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "panPEG"
  ["panLexer"];;
(* HOL4 ancestors outside the port: combin *)


let pancakeNT_INDUCT,pancakeNT_RECURSION = define_datatype
  "pancakeNT =
     TopDecListNT
   | StructNameNT
   | FieldNameListNT
   | FunNT
   | ProgNT
   | BlockNT
   | StmtNT
   | ExpNT
   | DecNT
   | GlobalDecNT
   | AssignNT
   | StoreNT
   | StoreByteNT
   | Store32NT
   | IfNT
   | WhileNT
   | CallNT
   | RetNT
   | HandleNT
   | ExtCallNT
   | ThrowNT
   | ReturnNT
   | DecCallNT
   | RetCallNT
   | ArgListNT
   | ParamListNT
   | EBoolAndNT
   | EEqNT
   | ECmpNT
   | ELoadNT
   | ELoadByteNT
   | ELoad32NT
   | EXorNT
   | EOrNT
   | EAndNT
   | EShiftNT
   | EAddNT
   | EMulNT
   | ENotNT
   | EFieldNT
   | EBaseNT
   | RawStructNT
   | NmdStructNT
   | NmdFieldListNT
   | NmdFieldNT
   | ShapedIdentNT
   | ShapeNT
   | ShapeCombNT
   | EqOpsNT
   | CmpOpsNT
   | ShiftOpsNT
   | AddOpsNT
   | MulOpsNT
   | SharedLoadNT
   | SharedLoadByteNT
   | SharedLoad16NT
   | SharedLoad32NT
   | SharedStoreNT
   | SharedStoreByteNT
   | SharedStore16NT
   | SharedStore32NT
   | ExnDecNT";;

let mknt_def = new_definition
  `mknt (ntsym:pancakeNT) = peg_nt (INL ntsym) I`;;

let mkleaf_def = new_definition
  `mkleaf t = [Lf (grammar_TOK (FST t),SND t)]`;;

let mknode_def = new_definition
  `mknode x ts = Nd (INL x,ptree_list_loc ts) ts`;;

(** Make a sub-parsetree with a single child *)
let mksubtree_def = new_definition
  `mksubtree x ts = [mknode x ts]`;;

(** Accept a token without storing it. *)
let consume_tok_def = new_definition
  `consume_tok t = peg_tok ((=) t) (\t. [])`;;

(** Accept and store a token in the parse tree. *)
let keep_tok_def = new_definition
  `keep_tok t = peg_tok ((=) t) mkleaf`;;

(** Similar functions for keyword tokens *)
let consume_kw_def = new_definition
  `consume_kw k = consume_tok (panLexer_KeywordT k)`;;

let keep_kw_def = new_definition
  `keep_kw k = keep_tok (panLexer_KeywordT k)`;;

let keep_ident_def = new_definition
  `keep_ident = peg_tok (\t. match t with panLexer_IdentT _ -> T
                        | _ -> F) mkleaf`;;

let keep_annot_def = new_definition
  `keep_annot = peg_tok (\t. match t with panLexer_AnnotCommentT _ -> T
                        | _ -> F) mkleaf`;;

let keep_ffi_ident_def = new_definition
  `keep_ffi_ident = peg_tok (\t. match t with panLexer_ForeignIdent _ -> T
                        | _ -> F) mkleaf`;;

let keep_int_def = new_definition
  `keep_int = peg_tok (\t. match t with panLexer_IntT _ -> T
                        | _ -> F) mkleaf`;;

let keep_nat_def = new_definition
  `keep_nat = peg_tok (\t. match t with
                         panLexer_IntT n -> if n >= (&0) then T else F
                       | _ -> F) mkleaf`;;

let extract_sum_def = define_cases
  `(extract_sum (INL x) = x) /\
   (extract_sum (INR x) = x)`;;

let panPEG_choicel_def,panPEG_choicel_ind = define_guess
  `(panPEG_choicel [] = peg_not (peg_empty []) []) /\
   (panPEG_choicel (CONS h t) = peg_choice h (panPEG_choicel t)
    extract_sum)`;;

let panPEG_pegf_def = new_definition
  `panPEG_pegf s f = peg_seq s (peg_empty []) (\l1 l2. f l1)`;;

let panPEG_seql_def = new_definition
  `panPEG_seql l f = panPEG_pegf (ITLIST (\p acc. peg_seq p acc APPEND) l
  (peg_empty [])) f`;;

let panPEG_try_def = new_definition
  `panPEG_try s = panPEG_choicel [s; peg_empty []]`;;

(* like try, but stores given token without consumption on failure *)
let try_default_def = new_definition
  `try_default s t = panPEG_choicel [s; peg_empty (mkleaf (t,unknown_loc))]`;;

(* add single Skip in place of empty Prog - will generate unnecessary Skips if used without caution *)
let try_ProgNT_def = new_definition
  `try_ProgNT =
     panPEG_choicel [
       panPEG_seql [consume_tok panLexer_RCurT; peg_empty (mkleaf
         (panLexer_KeywordT SkipK,unknown_loc))] (mksubtree ProgNT);
       mknt ProgNT]`;;

let pancake_peg_def = new_definition
  `pancake_peg = mk_peg (mknt TopDecListNT) "Didn't expect an EOF"
  "Failed to see expected token"
  "Failed to see expected token; saw EOF instead" "Not combinator failed"
  (FEMPTY |++ [
         (INL TopDecListNT,panPEG_choicel [peg_not (peg_any (K (mksubtree
           TopDecListNT []))) (mksubtree TopDecListNT []);
                              panPEG_seql [mknt FunNT; mknt TopDecListNT]
                                (mksubtree TopDecListNT);
                              panPEG_seql [mknt GlobalDecNT; mknt
                                TopDecListNT] (mksubtree TopDecListNT);
                              panPEG_seql [mknt ExnDecNT; mknt TopDecListNT]
                                (mksubtree TopDecListNT);
                              panPEG_seql [mknt StructNameNT; mknt
                                TopDecListNT] (mksubtree TopDecListNT);
                              panPEG_seql [keep_annot; mknt TopDecListNT]
                                (mksubtree TopDecListNT)]);
         (INL StructNameNT,panPEG_seql [consume_kw NamedK;
                              keep_ident;
                              consume_tok panLexer_LCurT;
                              mknt FieldNameListNT;
                              consume_tok panLexer_RCurT]
                              (mksubtree StructNameNT));
         (INL FieldNameListNT,panPEG_seql [mknt ShapedIdentNT;
                              peg_rpt (panPEG_seql [consume_tok
                                panLexer_CommaT;
                              mknt ShapedIdentNT] I)
                              FLAT]
                              (mksubtree FieldNameListNT));
         (INL FunNT,panPEG_seql [try_default (keep_kw InlineK)
           panLexer_NoinlineT;
                           try_default (keep_kw ExportK) panLexer_StaticT;
                           consume_kw FunK;
                           mknt ShapedIdentNT;
                           consume_tok panLexer_LParT;
                           panPEG_choicel
                           [mknt ParamListNT;
                            peg_empty (mksubtree ParamListNT [])];
                           consume_tok panLexer_RParT;
                           consume_tok panLexer_LCurT;
                           try_ProgNT]
                           (mksubtree FunNT));
         (INL ParamListNT,panPEG_seql [mknt ShapedIdentNT;
                              peg_rpt (panPEG_seql [consume_tok
                                panLexer_CommaT;
                              mknt ShapedIdentNT] I)
                              FLAT]
                              (mksubtree ParamListNT));
         (INL ProgNT,panPEG_choicel [panPEG_seql [mknt BlockNT; mknt ProgNT]
           (mksubtree ProgNT);
                              panPEG_seql [mknt DecCallNT; try_ProgNT]
                                (mksubtree DecCallNT);
                              panPEG_seql [mknt DecNT; try_ProgNT]
                                (mksubtree DecNT);
                              panPEG_seql [keep_annot; mknt ProgNT]
                                (mksubtree ProgNT);
                              panPEG_seql [mknt StmtNT; consume_tok
                                panLexer_SemiT; mknt ProgNT] (mksubtree
                                ProgNT);
                              consume_tok panLexer_RCurT]);
         (INL BlockNT,panPEG_choicel [mknt HandleNT;
                              mknt IfNT;
                              mknt WhileNT]);
         (INL StmtNT,panPEG_choicel [keep_kw SkipK;
                              mknt CallNT;
                              mknt AssignNT; mknt StoreNT;
                              mknt StoreByteNT;
                              mknt Store32NT;
                              mknt SharedLoadByteNT;
                              mknt SharedLoad16NT;
                              mknt SharedLoad32NT;
                              mknt SharedLoadNT;
                              mknt SharedStoreByteNT;
                              mknt SharedStore16NT;
                              mknt SharedStore32NT;
                              mknt SharedStoreNT;
                              keep_kw BrK; keep_kw ContK;
                              mknt ExtCallNT;
                              mknt ThrowNT; mknt RetCallNT; mknt ReturnNT;
                              keep_kw TicK;
                              panPEG_seql [consume_tok panLexer_LCurT;
                                try_ProgNT] I]);
         (INL DecCallNT,panPEG_seql [consume_kw VarK; mknt ShapedIdentNT;
           consume_tok panLexer_AssignT;
                              keep_ident;
                              consume_tok panLexer_LParT; panPEG_try (mknt
                                ArgListNT);
                              consume_tok panLexer_RParT; consume_tok
                                panLexer_SemiT]
                           (mksubtree DecCallNT));
         (INL DecNT,panPEG_seql [consume_kw VarK; mknt ShapedIdentNT;
                          consume_tok panLexer_AssignT; mknt ExpNT;
                          consume_tok panLexer_SemiT]
                          (mksubtree DecNT));
         (INL GlobalDecNT,panPEG_seql [consume_kw VarK; mknt ShapedIdentNT;
                          consume_tok panLexer_AssignT; mknt ExpNT;
                          consume_tok panLexer_SemiT]
                          (mksubtree GlobalDecNT));
         (INL ExnDecNT,panPEG_seql [consume_kw ExceptionK;
                           keep_ident;
                           consume_tok panLexer_ColonT;
                           mknt ShapeNT;
                           consume_tok panLexer_SemiT]
                           (mksubtree ExnDecNT));
         (INL AssignNT,panPEG_seql [keep_ident; consume_tok
           panLexer_AssignT;
                              mknt ExpNT] (mksubtree AssignNT));
         (INL StoreNT,panPEG_seql [consume_kw StK; mknt ExpNT;
                             consume_tok panLexer_CommaT; mknt ExpNT]
                            (mksubtree StoreNT));
         (INL StoreByteNT,panPEG_seql [consume_kw St8K; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree StoreByteNT));
         (INL Store32NT,panPEG_seql [consume_kw St32K; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree Store32NT));
         (INL IfNT,panPEG_seql [consume_kw IfK; mknt ExpNT; consume_tok
           panLexer_LCurT;
                          try_ProgNT;
                          try_default (panPEG_seql [consume_kw ElseK;
                            consume_tok panLexer_LCurT;
                              try_ProgNT] I) (panLexer_KeywordT SkipK)]
                         (mksubtree IfNT));
         (INL WhileNT,panPEG_seql [consume_kw WhileK; mknt ExpNT;
                             consume_tok panLexer_LCurT; try_ProgNT]
                               (mksubtree WhileNT));
         (INL CallNT,panPEG_seql [try_default (panPEG_choicel [keep_kw RetK;
           mknt RetNT]) panLexer_NotT;
                            keep_ident;
                            consume_tok panLexer_LParT; try_default (mknt
                              ArgListNT) panLexer_NotT;
                            consume_tok panLexer_RParT]
                           (mksubtree CallNT));
         (INL RetNT,panPEG_seql [keep_ident; consume_tok panLexer_AssignT]
                           (mksubtree RetNT));
         (INL HandleNT,panPEG_seql [consume_kw TryK;
                              try_default (mknt RetNT) panLexer_NotT;
                              keep_ident;
                              consume_tok panLexer_LParT; try_default (mknt
                                ArgListNT) panLexer_NotT;
                              consume_tok panLexer_RParT;
                              consume_kw CatchK;
                              keep_ident;
                              consume_tok panLexer_ArrowT;
                              keep_ident;
                              consume_tok panLexer_LCurT; try_ProgNT]
                             (mksubtree HandleNT));
         (INL ExtCallNT,panPEG_seql [keep_ffi_ident;
                              consume_tok panLexer_LParT; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT;
                              consume_tok panLexer_RParT]
                              (mksubtree ExtCallNT));
         (INL ThrowNT,panPEG_seql [consume_kw ThrowK; keep_ident; mknt
           ExpNT]
                            (mksubtree ThrowNT));
         (INL RetCallNT,panPEG_seql [consume_kw RetK;
                              keep_ident;
                              consume_tok panLexer_LParT; panPEG_try (mknt
                                ArgListNT);
                              consume_tok panLexer_RParT]
                             (mksubtree RetCallNT));
         (INL ReturnNT,panPEG_seql [consume_kw RetK; mknt ExpNT]
                             (mksubtree ReturnNT));
         (INL ArgListNT,panPEG_seql [mknt ExpNT;
                              peg_rpt (panPEG_seql [consume_tok
                                panLexer_CommaT;
                              mknt ExpNT] I)
                              FLAT]
                              (mksubtree ArgListNT));
         (INL ExpNT,panPEG_seql [mknt EBoolAndNT;
                           peg_rpt (panPEG_seql [consume_tok
                             panLexer_BoolOrT; mknt EBoolAndNT] I)
                              FLAT]
                          (mksubtree ExpNT));
         (INL EBoolAndNT,panPEG_seql [mknt EEqNT;
                              peg_rpt (panPEG_seql [consume_tok
                                panLexer_BoolAndT; mknt EEqNT] I)
                              FLAT]
                              (mksubtree EBoolAndNT));
         (INL EEqNT,panPEG_seql [mknt ECmpNT;
                           panPEG_try (panPEG_seql [mknt EqOpsNT; mknt
                             ECmpNT] I)]
                          (mksubtree EEqNT));
         (INL ECmpNT,panPEG_seql [mknt ELoadNT;
                            panPEG_try (panPEG_seql [mknt CmpOpsNT; mknt
                              ELoadNT] I)]
                           (mksubtree ECmpNT));
         (INL ELoadNT,panPEG_choicel [panPEG_seql [consume_kw LdsK; mknt
           ShapeNT; mknt ELoadByteNT]
                              (mksubtree ELoadNT);
                              mknt ELoadByteNT]);
         (INL ELoadByteNT,panPEG_choicel [panPEG_seql [consume_kw Ld8K; mknt
           ELoad32NT]
                              (mksubtree ELoadByteNT);
                              mknt ELoad32NT]);
         (INL ELoad32NT,panPEG_choicel [panPEG_seql [consume_kw Ld32K; mknt
           EOrNT]
                              (mksubtree ELoad32NT);
                              mknt EOrNT]);
         (INL EOrNT,panPEG_seql [mknt EXorNT;
                           peg_rpt (panPEG_seql [keep_tok panLexer_OrT; mknt
                             EXorNT] I)
                              FLAT]
                          (mksubtree EOrNT));
         (INL EXorNT,panPEG_seql [mknt EAndNT;
                            peg_rpt (panPEG_seql [keep_tok panLexer_XorT;
                              mknt EAndNT] I)
                              FLAT]
                           (mksubtree EXorNT));
         (INL EAndNT,panPEG_seql [mknt EShiftNT;
                            peg_rpt (panPEG_seql [keep_tok panLexer_AndT;
                              mknt EShiftNT] I)
                              FLAT]
                           (mksubtree EAndNT));
         (INL EShiftNT,panPEG_seql [mknt EAddNT;
                              peg_rpt (panPEG_seql [mknt ShiftOpsNT; mknt
                                EAddNT] I)
                              FLAT]
                             (mksubtree EShiftNT));
         (INL EAddNT,panPEG_seql [mknt EMulNT;
                            peg_rpt (panPEG_seql [mknt AddOpsNT; mknt
                              EMulNT] I)
                              FLAT]
                           (mksubtree EAddNT));
         (INL EMulNT,panPEG_seql [mknt ENotNT;
                            peg_rpt (panPEG_seql [mknt MulOpsNT; mknt
                              ENotNT] I) FLAT]
                           (mksubtree EMulNT));
         (INL ENotNT,panPEG_seql [panPEG_try (keep_tok panLexer_NotT); mknt
           EFieldNT]
                            (mksubtree ENotNT));
         (INL EFieldNT,panPEG_seql [mknt EBaseNT;
                             peg_rpt (panPEG_seql [consume_tok
                               panLexer_DotT;
                              panPEG_choicel [keep_nat; keep_ident]] I)
                              FLAT]
                            (mksubtree EFieldNT));
         (INL EBaseNT,panPEG_choicel [panPEG_seql [consume_tok
           panLexer_LParT;
                              mknt ExpNT;
                              consume_tok panLexer_RParT] I;
                              keep_kw TrueK; keep_kw FalseK;
                              mknt RawStructNT; mknt NmdStructNT;
                              keep_kw BaseK; keep_kw BiwK; keep_kw TopK;
                              keep_int; keep_ident]);
         (INL RawStructNT,panPEG_seql [consume_tok panLexer_LessT; mknt
           ArgListNT;
                              consume_tok panLexer_GreaterT]
                             (mksubtree RawStructNT));
         (INL NmdStructNT,panPEG_seql [keep_ident; consume_tok
           panLexer_LessT; mknt NmdFieldListNT;
                              consume_tok panLexer_GreaterT]
                             (mksubtree NmdStructNT));
         (INL NmdFieldListNT,panPEG_seql [mknt NmdFieldNT;
                              peg_rpt (panPEG_seql [consume_tok
                                panLexer_CommaT;
                              mknt NmdFieldNT] I)
                              FLAT]
                              (mksubtree NmdFieldListNT));
         (INL NmdFieldNT,panPEG_seql [keep_ident;
                              consume_tok panLexer_AssignT;
                              mknt ExpNT]
                              (mksubtree NmdFieldNT));
         (INL ShapedIdentNT,panPEG_choicel [panPEG_seql [mknt ShapeNT;
                              keep_ident] I;
                              panPEG_seql [peg_empty (mkleaf
                                (panLexer_DefaultShT,unknown_loc));
                              keep_ident] I]);
         (INL ShapeNT,panPEG_choicel [keep_int;
                              panPEG_seql [consume_tok panLexer_LCurT;
                              mknt ShapeCombNT;
                              consume_tok panLexer_RCurT] I;
                              keep_ident]);
         (INL ShapeCombNT,panPEG_seql [mknt ShapeNT;
                              peg_rpt (peg_seq (consume_tok panLexer_CommaT)
                              (mknt ShapeNT) (C K)) FLAT]
                              (mksubtree ShapeCombNT));
         (INL EqOpsNT,panPEG_choicel [keep_tok panLexer_EqT; keep_tok
           panLexer_NeqT]);
         (INL CmpOpsNT,panPEG_choicel [keep_tok panLexer_LessT; keep_tok
           panLexer_GeqT; keep_tok panLexer_GreaterT; keep_tok panLexer_LeqT;
                              keep_tok panLexer_LowerT; keep_tok
                                panLexer_HigherT; keep_tok panLexer_HigheqT;
                                keep_tok panLexer_LoweqT]);
         (INL ShiftOpsNT,panPEG_choicel [keep_tok panLexer_LslT; keep_tok
           panLexer_LsrT;
                              keep_tok panLexer_AsrT; keep_tok
                                panLexer_RorT]);
         (INL AddOpsNT,panPEG_choicel [keep_tok panLexer_PlusT; keep_tok
           panLexer_MinusT]);
         (INL MulOpsNT,keep_tok panLexer_StarT);
         (INL SharedLoadNT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw LdwK; keep_ident;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedLoadNT));
         (INL SharedLoadByteNT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw Ld8K; keep_ident;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedLoadByteNT));
         (INL SharedLoad16NT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw Ld16K; keep_ident;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedLoad16NT));
         (INL SharedLoad32NT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw Ld32K; keep_ident;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedLoad32NT));
         (INL SharedStoreNT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw StwK; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedStoreNT));
         (INL SharedStoreByteNT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw St8K; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedStoreByteNT));
         (INL SharedStore16NT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw St16K; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedStore16NT));
         (INL SharedStore32NT,panPEG_seql [consume_tok panLexer_NotT;
           consume_kw St32K; mknt ExpNT;
                              consume_tok panLexer_CommaT; mknt ExpNT]
                              (mksubtree SharedStore32NT))])`;;

(** Compute pancake parser domain lookup function. *)
(* HOL4 panPEGScript.sml:413-418: a theorem that HOL4 states as the value of
   an ML expression: FDOM_pancake_peg *)


(* HOL4 panPEGScript.sml:421-425: ML code, not ported *)

(* HOL4 panPEGScript.sml:427-431: ML code, not ported *)

(* HOL4 panPEGScript.sml:433-438: ML code, not ported *)

(* HOL4 panPEGScript.sml:440-445: a theorem that HOL4 states as the value of
   an ML expression: pancake_peg_applied *)
(* HOL4 panPEGScript.sml:440-445: the ML values that the definitions below
   antiquote *)

(* HOL4 panPEGScript.sml:447-452: a theorem that HOL4 states as the value of
   an ML expression: pancake_peg_applied' *)
(* HOL4 panPEGScript.sml:447-452: the ML values that the definitions below
   antiquote *)

(* HOL4 panPEGScript.sml:454-466: ML code, not ported *)

(* HOL4 panPEGScript.sml:468-473: a theorem that HOL4 states as the value of
   an ML expression: pancake_exec_thm *)

let parse_statement_def = new_definition
  `parse_statement s =
     match peg_exec pancake_peg (mknt ProgNT) s [] NONE [] pegexec_done
       pegexec_failed with pegexec_Result (peg_Success [] [e] _) -> SOME e
     | _ -> NONE`;;

let panPEG_parse_def = new_definition
  `panPEG_parse s =
     match peg_exec pancake_peg (mknt TopDecListNT) s [] NONE []
       pegexec_done pegexec_failed with pegexec_Result (peg_Success [] [e] _)
       -> INL e
     | pegexec_Result (peg_Success toks _ _) -> INR [((implode
       "Parser could not consume all tokens"),unknown_loc)]
     | pegexec_Result (peg_Failure loc msg) -> INR [(implode msg,loc)]
     | pegexec_Looped -> INR [((implode
       "PEG execution looped during parsing"),unknown_loc)]
     | _ -> INR [((implode "Unknown error during parsing"),unknown_loc)]`;;

(** Properties for proving well-formedness of the Pancake grammar. *)

(* frange_image[local] *)
let panPEG_frange_image = prove
 (`FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)`,
  CHEAT_TAC);;

(* HOL4 panPEGScript.sml:501-504: ML code, not ported *)

(* HOL4 panPEGScript.sml:506-507: the ML values that the definitions below
   antiquote *)

(* HOL4 panPEGScript.sml:509-528: ML code, not ported *)

(* HOL4 panPEGScript.sml:530-547: ML code, not ported *)

(* HOL4 panPEGScript.sml:549-553: ML code, not ported *)

(* HOL4 panPEGScript.sml:555-559: ML code, not ported *)

(* HOL4 panPEGScript.sml:561-573: ML code, not ported *)

(* HOL4 panPEGScript.sml:575-588: ML code, not ported *)

(* HOL4 panPEGScript.sml:590-601: the ML values that the definitions below
   antiquote *)

(* HOL4 panPEGScript.sml:603-613: ML code, not ported *)

(* HOL4 panPEGScript.sml:615-620: ML code, not ported *)

(* HOL4 panPEGScript.sml:622-627: ML code, not ported *)

(* peg0_pegf *)
let panPEG_peg0_pegf = prove
 (`peg0 G (panPEG_pegf s f) = peg0 G s`,
  CHEAT_TAC);;
add_simp panPEG_peg0_pegf;;

(* peg0_seql *)
let panPEG_peg0_seql = prove
 (`(peg0 G (panPEG_seql [] f) <=> T) /\
   (peg0 G (panPEG_seql (CONS h t) f) <=> peg0 G h /\ peg0 G (panPEG_seql
     t I))`,
  CHEAT_TAC);;
add_simp panPEG_peg0_seql;;

let peg0_keep_tok = prove
 (`peg0 G (keep_tok t) = F`,
  CHEAT_TAC);;
add_simp peg0_keep_tok;;

let peg0_consume_tok = prove
 (`peg0 G (consume_tok t) = F`,
  CHEAT_TAC);;
add_simp peg0_consume_tok;;

let peg0_keep_kw = prove
 (`peg0 G (keep_kw k) = F`,
  CHEAT_TAC);;
add_simp peg0_keep_kw;;

let peg0_consume_kw = prove
 (`peg0 G (consume_kw k) = F`,
  CHEAT_TAC);;
add_simp peg0_consume_kw;;

let peg0_keep_int = prove
 (`peg0 G keep_int = F`,
  CHEAT_TAC);;
add_simp peg0_keep_int;;

let peg0_keep_nat = prove
 (`peg0 G keep_int = F`,
  CHEAT_TAC);;
add_simp peg0_keep_nat;;

let peg0_keep_ident = prove
 (`peg0 G keep_ident = F`,
  CHEAT_TAC);;
add_simp peg0_keep_ident;;

let peg0_keep_ffi_ident = prove
 (`peg0 G keep_ffi_ident = F`,
  CHEAT_TAC);;
add_simp peg0_keep_ffi_ident;;

(* peg0_choicel *)
let panPEG_peg0_choicel = prove
 (`(peg0 G (panPEG_choicel []) = F) /\
   (peg0 G (panPEG_choicel (CONS h t)) <=>
      peg0 G h \/ pegfail G h /\ peg0 G (panPEG_choicel t))`,
  CHEAT_TAC);;
add_simp panPEG_peg0_choicel;;

(* HOL4 panPEGScript.sml:698-711: a proof *)

(* HOL4 panPEGScript.sml:713-726: the ML values that the definitions below
   antiquote *)

(*  “FunNT”, “TopDecListNT” *)

(** All non-terminals except the top-level
  * program nonterminal always consume input. *)
(* HOL4 panPEGScript.sml:732: the ML values that the definitions below
   antiquote *)

(* HOL4 panPEGScript.sml:734: the ML values that the definitions below
   antiquote *)

(* HOL4 panPEGScript.sml:736-755: a proof *)

(** This time include the top-level program non-terminal which is
  * well-formed. *)
(* HOL4 panPEGScript.sml:759-760: a theorem that HOL4 states as the value of
   an ML expression: pancake_wfpeg_thm *)

(* HOL4 panPEGScript.sml:762-763: a theorem that HOL4 states as the value of
   an ML expression: pancake_wfpeg_FunNT_thm *)

(* [local] *)
let subexprs_mknt = prove
 (`subexprs (mknt n) = {mknt n}`,
  CHEAT_TAC);;

(* PEG_wellformed *)
let panPEG_PEG_wellformed = prove
 (`wfG pancake_peg`,
  CHEAT_TAC);;
add_simp panPEG_PEG_wellformed;;

(* and the interface *)
let _ = unhide_overloads ();;
