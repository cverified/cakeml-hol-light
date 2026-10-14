(* ======================================================== *)
(*  gram: ported from HOL4's
    semantics/gramScript.sml  *)
(* ======================================================== *)

(*
  Definition of CakeML's Context-Free Grammar.
  The grammar specifies how token lists should be converted to syntax
    trees.
*)

needs "lib/grammar.ml";;
needs "lib/location.ml";;
needs "semantics/tokens.ml";;
needs "semantics/typeSystem.ml";;


(* HOL4 ML code, not ported:
val tokmap0 =
    List.foldl (fn ((s,t), acc) => Binarymap.insert(acc,s,t))
               (Binarymap.mkDict String.compare)
               [("(", ``LparT``), (")", ``RparT``), (",", ``CommaT``),
                ("[", ``LbrackT``),
                ("]", ``RbrackT``),
                (";", ``SemicolonT``), (":=", ``SymbolT «:=»``),
                (":>", ``SealT``),
                ("->", ``ArrowT``), ("=>", ``DarrowT``),
                ("*", ``StarT``),
                ("::", “SymbolT «::»”),
                ("|", ``BarT``), ("=", ``EqualsT``), (":", ``ColonT``),
                ("_", ``UnderbarT``),
                ("and", ``AndT``),
                ("andalso", ``AndalsoT``),
                ("as", ``AsT``),
                ("before", ``AlphaT «before»``),
                ("Bind", ``AlphaT «Bind»``),
                ("case", ``CaseT``),
                ("datatype", ``DatatypeT``),
                ("Div", ``AlphaT «Div»``),
                ("else", ``ElseT``),
                ("end", ``EndT``),
                ("exception", ``ExceptionT``),
                ("fn", ``FnT``),
                ("fun", ``FunT``),
                ("handle", ``HandleT``),
                ("if", ``IfT``),
                ("in", ``InT``),
                ("IntError", ``AlphaT «IntError»``),
                ("let", ``LetT``),
                ("local", ``LocalT``),
                ("o", ``AlphaT «o»``),
                ("of", ``OfT``),
                ("op", ``OpT``),
                ("orelse", ``OrelseT``),
                ("raise", ``RaiseT``),
                ("sig", ``SigT``),
                ("struct", ``StructT``),
                ("structure", ``StructureT``),
                ("then", ``ThenT``),
                ("type", ``TypeT``),
                ("val", ``ValT``)]
fun tokmap s =
    case Binarymap.peek(tokmap0, s) of
        NONE => raise Fail ("No token binding for "^s)
      | SOME t => t
*)

(* HOL4 ML code, not ported:
val ginfo = { tokmap = tokmap,
              tokty = ``:token``, nt_tyname = "MMLnonT",
              start = "TopLevelDecs",
              gname = "cmlG", mkntname = (fn s => "n" ^ s) }
*)

let validMultSym_def = cake_define
  `validMultSym s <=> "/" <<= s \/ "*" <<= s \/ "%" <<= s \/ "&" <<=
  s`;;

let validAddSym_def = cake_define
  `validAddSym s <=> ~(s = "") /\ HD s IN {(CHR 43),(CHR 45),(CHR 94)}
  \/
                   2 <= LENGTH s /\ HD s = (CHR 124)`;;

let validRelSym_def = cake_define
  `validRelSym s <=> "<" <<= s \/ ">" <<= s \/ (2 <= LENGTH s /\ ("="
  <<= s \/ "~" <<= s))`;;

let validListSym_def = cake_define
  `validListSym s <=> "@" <<= s \/ (":" <<= s /\ 2 <= LENGTH s /\ ~(s
  = ":="))`;;

let validPrefixSym_def = cake_define
  `validPrefixSym s <=> s = "~" \/ "!" <<= s \/ "?" <<= s`;;

(* HOL4 ML code, not ported:
val cmlG_def = mk_grammar_def ginfo
`(* types *)
 UQTyOp ::= <AlphaT> | <SymbolT> ;
 TyvarN ::= <TyvarT>;
 TyOp ::= UQTyOp | <LongidT>;
 TypeList1 ::= Type | Type "," TypeList1;
 TypeList2 ::= Type "," TypeList1;
 Tbase ::= <TyvarT> | TyOp | "(" TypeList2 ")" TyOp | "(" Type ")";
 DType ::= DType TyOp | Tbase;
 PType ::= DType "*" PType | DType;
 Type ::= PType | PType "->" Type;
 TbaseList ::=  | PTbase TbaseList ;
 PTbase ::= <TyvarT> | TyOp | "(" Type ")" ;
*)

 (* type declarations *)
(* HOL4 ML code, not ported:
 TypeName ::= UQTyOp | "(" TyVarList ")" UQTyOp | <TyvarT> UQTyOp ;
 TyVarList ::= TyvarN | TyVarList "," TyvarN;
 Dconstructor ::= UQConstructorName TbaseList;
 DtypeCons ::= Dconstructor | DtypeCons "|" Dconstructor;
 DtypeDecl ::= TypeName "=" DtypeCons ;
 DtypeDecls ::= DtypeDecl | DtypeDecls "and" DtypeDecl;
 TypeDec ::= "datatype" DtypeDecls;
 TypeAbbrevDec ::= "type" TypeName "=" Type;
*)

 (* expressions - base cases and function applications *)
(* HOL4 ML code, not ported:
 UQConstructorName ::= ^(``{AlphaT s | s ≠ «» ∧ isUpper (strsub s
   0)}``);
 ConstructorName ::=
     UQConstructorName
  | ^(``{LongidT str s | str,s | s ≠ «» ∧ isAlpha (strsub s 0) ∧ isUpper
    (strsub s 0)}``);
 V ::= ^(``{AlphaT s | s ∉ {«before»; «div»; «mod»; «o»} ∧
                       s ≠ «» ∧ ¬isUpper (strsub s 0)}``)
    |  ^(“{SymbolT s | validPrefixSym (explode s)}”);
 FQV ::= V
      |  ^(``{LongidT str s | str,s |
              s ≠ «» ∧ (isAlpha (strsub s 0) ⇒ ¬isUpper (strsub s
                0))}``) ;
 OpID ::= ^(``{LongidT str s | str,s | s ≠ «»}``)
       |  ^(``{AlphaT s | s ≠ «»}``)
       |  ^(``{SymbolT s | s ≠ «»}``)
       |  "*" | "=" ;
*)

(* HOL4 ML code, not ported:
 Eliteral ::= <IntT> | <CharT> | <StringT> | <WordT> | <FFIT> ;
*)

(* HOL4 ML code, not ported:
 Ebase ::= "(" Eseq ")" | Etuple | "(" ")" | FQV | ConstructorName |
   Eliteral
        | "let" LetDecs "in" Eseq "end" | "[" "]"
        | "[" Elist1 "]" | "op" OpID ;
 Eseq ::= E ";" Eseq | E;
 Etuple ::= "(" Elist2 ")";
 Elist2 ::= E "," Elist1;
 Elist1 ::= E | E "," Elist1;
 Eapp ::= Eapp Ebase | Ebase;
*)

 (* expressions - binary operators *)
(* HOL4 ML code, not ported:
 MultOps ::= ^(``{AlphaT «div»; AlphaT «mod»; StarT} ∪
                 {SymbolT s | validMultSym (explode s)}``);
 AddOps ::= ^(``{SymbolT s | validAddSym (explode s)}``);
 RelOps ::= ^(``{SymbolT s | validRelSym (explode s)}``) | "=";
 CompOps ::= "o" | ":=";
 ListOps ::= ^(``{SymbolT s | validListSym (explode s)}``);
 Emult ::= Emult MultOps Eapp | Eapp;
 Eadd ::= Eadd AddOps Emult | Emult;
 Elistop ::= Eadd ListOps Elistop | Eadd;
 Erel ::= Erel RelOps Elistop | Elistop;
 Ecomp ::= Ecomp CompOps Erel | Erel;
 Ebefore ::= Ebefore "before" Ecomp | Ecomp;
 Etyped ::= Ebefore | Ebefore ":" Type;
 ElogicAND ::= ElogicAND "andalso" Etyped | Etyped;
 ElogicOR ::= ElogicOR "orelse" ElogicAND | ElogicAND;
 Ehandle ::= ElogicOR | ElogicOR "handle" PEs ;
 E ::= "if" E "then" E "else" E | "case" E "of" PEs | "fn" Pattern "=>"
   E
    | "raise" E |  Ehandle;
*)

 (* function and value declarations *)
(* HOL4 ML code, not ported:
 FDecl ::= V PbaseList1 "=" E ;
 AndFDecls ::= FDecl | AndFDecls "and" FDecl;
 LetDec ::= "val" Pattern "=" E | "fun" AndFDecls ;
 LetDecs ::= LetDec LetDecs | ";" LetDecs | ;
*)

 (* patterns *)
(* HOL4 ML code, not ported:
 Pbase ::= V | ConstructorName | <IntT> | <StringT> | <CharT> | Ptuple |
   "_"
        |  "[" "]" | "[" PatternList "]" | "op" OpID;
 PConApp ::= ConstructorName | PConApp Pbase ;
 Papp ::= PConApp Pbase | Pbase ;
 Pcons ::= Papp "::" Pcons | Papp ;
 Pas ::= V "as" Pcons | Pcons ;
 Pattern ::= Pas | Pas ":" Type ;
 Ptuple ::= "(" ")" | "(" PatternList ")";
 PatternList ::= Pattern | Pattern "," PatternList ;
 PbaseList1 ::= Pbase | Pbase PbaseList1 ;
 PE ::= "case" E "of" PEs
     |  "if" E "then" E "else" PE
     |  "fn" Pattern "=>" E
     |  "raise" PE
     |  ElogicOR PEsfx ;
 PEsfx ::= | "handle" PEs | "|" PEs;
 PEs ::= Pattern "=>" PE;
*)

 (* modules *)
(* HOL4 ML code, not ported:
 StructName ::= ^(``{AlphaT s | s ≠ «»}``) ;
 SpecLine ::= "val" V ":" Type
           |  "type" TypeName OptTypEqn
           |  "exception" Dconstructor
           |  TypeDec ;
 OptTypEqn ::= "=" Type | ;
 SpecLineList ::= SpecLine SpecLineList | ";" SpecLineList | ;
 SignatureValue ::= "sig" SpecLineList "end" ;
 OptionalSignatureAscription ::= ":>" SignatureValue | ;
 Decl ::= "val" Pattern "=" E  | "fun" AndFDecls |  TypeDec
       |  "exception" Dconstructor
       | TypeAbbrevDec | "local" Decls "in" Decls "end" | Structure;
 Decls ::= Decl Decls | ";" Decls | ;
 Structure ::= "structure" StructName OptionalSignatureAscription "="
   "struct"
               Decls "end";
 TopLevelDecs ::= E ";" TopLevelDecs | Decl NonETopLevelDecs
               |  ";" TopLevelDecs | ;
 NonETopLevelDecs ::= Decl NonETopLevelDecs | ";" TopLevelDecs | ; (*
 REPLCommand ::= <REPLIDT> Ebase ;
 TopLevel ::= REPLCommand | TopLevelDecs ; *)
`;
*)

new_type_abbrev("gram_NT",`: MMLnonT+num`);;

(* HOL4 overload (expanded in the port):
     mkNT = INL : MMLnonT -> NT *)
(* HOL4 overload (expanded in the port):
     NN = \nt. NT (mkNT nt) *)
(* HOL4 overload (expanded in the port):
     TK = TOK : token -> (token,MMLnonT)symbol *)

new_type_abbrev("mlptree",`: (tokens_token,MMLnonT,locs)parsetree`);;

(* HOL4 ML code, not ported:
val nt_distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:MMLnonT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  save_thm("nt_distinct_ths",  LIST_CONJ (recurse ntlist))
end
*)

let ndl_def = cake_define
  `(Ndl n l = Nd (n,unknown_loc) l)`;;

let lfl_def = cake_define
  `(Lfl t = Lf (t,unknown_loc))`;;

(* HOL4 ML code, not ported:
val ast =
  ``let mkI = λn. Ndl (mkNT nEbase) [Ndl (mkNT nEliteral) [Lfl (TK (IntT
    n))]]
    in
      Ndl (mkNT nEmult) [
              Ndl (mkNT nEmult) [
                Ndl (mkNT nEmult) [Ndl (mkNT nEapp) [mkI 3]];
                Ndl (mkNT nMultOps) [Lfl (TK StarT)];
                Ndl (mkNT nEapp) [mkI 4]
              ];
              Ndl (mkNT nMultOps) [Lfl (TK (SymbolT «/»))];
              Ndl (mkNT nEapp) [mkI 5]
            ]``
*)

(* HOL4 ML code, not ported:
val check_results =
    time (SIMP_CONV (srw_ss())
              [valid_ptree_def, cmlG_def,DISJ_IMP_THM, FORALL_AND_THM,
               finite_mapTheory.FAPPLY_FUPDATE_THM,
                 LET_THM,Ndl_def,Lfl_def,
               validMultSym_def])
 ``valid_ptree cmlG ^ast``
*)

(* HOL4 ML code, not ported:
val _ = if aconv (rhs (concl check_results)) T then print
  "valid_ptree: OK\n"
        else raise Fail "valid_ptree: failed"
*)
