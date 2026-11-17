(* ======================================================== *)
(*  gramProps: ported from HOL4's
    semantics/proofs/gramPropsScript.sml
    A proof theory about gram.ml, with 2 definitions and 12
    theorems.  Needed by cmlNTProps.ml, pegComplete.ml and
    pegSound.ml.  *)
(* ======================================================== *)

(*
  Properties of the CakeML CFG, including automatically derived
  nullability results for various non-terminals, and results about
  the grammar’s rules finite map.
*)

needs "lib/NTproperties.ml";;
needs "lib/grammar.ml";;
needs "semantics/gram.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "gramProps"
  ["gram"];;
(* HOL4 ancestors outside the port: pred_set *)

(* HOL4 gramPropsScript.sml:12-13: ML code, not ported *)

(* HOL4 gramPropsScript.sml:15-19: ML code, not ported *)

(* HOL4 gramPropsScript.sml:21-32: ML code, not ported *)

(* HOL4 gramPropsScript.sml:34-36: ML code, not ported *)

let NT_rank_def = new_definition
  `NT_rank N =
     match N with INR _ -> 0
       | INL n ->
         if n = gram_nElist1 then 16
         else if n = gram_nEseq then 16
         else if n = gram_nTopLevelDecs then 16
         else if n = gram_nElist2 then 16
         else if n = gram_nE then 15
         else if n = gram_nEhandle then 14
         else if n = gram_nPE then 14
         else if n = gram_nElogicOR then 13
         else if n = gram_nElogicAND then 12
         else if n = gram_nEtyped then 11
         else if n = gram_nEbefore then 10
         else if n = gram_nEcomp then 9
         else if n = gram_nErel then 8
         else if n = gram_nElistop then 7
         else if n = gram_nEadd then 6
         else if n = gram_nEmult then 5
         else if n = gram_nEapp then 4
         else if n = gram_nEbase then 3
         else if n = gram_nFQV then 2
         else if n = gram_nV then 1
         else if n = gram_nDtypeCons then 3
         else if n = gram_nDconstructor then 2
         else if n = gram_nConstructorName then 2
         else if n = gram_nUQConstructorName then 1
         else if n = gram_nTypeList2 then 8
         else if n = gram_nTypeList1 then 7
         else if n = gram_nType then 6
         else if n = gram_nPType then 5
         else if n = gram_nDType then 4
         else if n = gram_nTbaseList then 4
         else if n = gram_nPTbase then 3
         else if n = gram_nTbase then 3
         else if n = gram_nTyOp then 2
         else if n = gram_nTypeName then 2
         else if n = gram_nUQTyOp then 1
         else if n = gram_nNonETopLevelDecs then 4
         else if n = gram_nDecls then 3
         else if n = gram_nStructure then 1
         else if n = gram_nDecl then 2
         else if n = gram_nTypeDec then 1
         else if n = gram_nSpecLineList then 3
         else if n = gram_nSpecLine then 2
         else if n = gram_nPtuple then 2
         else if n = gram_nPbase then 3
         else if n = gram_nPbaseList1 then 4
         else if n = gram_nPapp then 4
         else if n = gram_nPcons then 5
         else if n = gram_nPas then 6
         else if n = gram_nPattern then 7
         else if n = gram_nPatternList then 8
         else if n = gram_nPEs then 9
         else if n = gram_nLetDecs then 2
         else if n = gram_nLetDec then 1
         else if n = gram_nDtypeDecl then 3
         else if n = gram_nAndFDecls then 3
         else if n = gram_nFDecl then 2
         else if n = gram_nTyVarList then 2
         else if n = gram_nTyvarN then 1
         else 0`;;

(* HOL4 gramPropsScript.sml:104-131: a theorem that HOL4 states as the value
   of an ML expression: cmlG_applied *)
(* HOL4 gramPropsScript.sml:104-131: the ML values that the definitions
   below antiquote *)

let cmlG_FDOM = SIMP_CONV [cmlG_def] `FDOM (grammar_rules cmlG)`;;

(* [local] *)
let paireq = prove
 (`(x,y) = z <=> x = FST z /\ y = SND z`,
  CHEAT_TAC);;

(* [local] *)
let GSPEC_INTER = prove
 (`{x | ?y. (x,T) = f y} INTER Q = {x | ?y. x = FST (f y) /\ SND (f y)
   /\ Q x}`,
  CHEAT_TAC);;

(* [local] *)
let RIGHT_INTER_OVER_UNION = prove
 (`(a UNION b) INTER c = (a INTER c) UNION (b INTER c)`,
  CHEAT_TAC);;

(* [local] *)
let GSPEC_applied = prove
 (`GSPEC f x <=> x IN GSPEC f`,
  CHEAT_TAC);;

(* HOL4 gramPropsScript.sml:162-167: the ML values that the definitions
   below antiquote *)

(* HOL4 gramPropsScript.sml:169-175: ML code, not ported *)

(* HOL4 gramPropsScript.sml:177: ML code, not ported *)

(* HOL4 gramPropsScript.sml:179: ML code, not ported *)

(* [local] *)
let nullloop_th = prove
 (`nullableML G (N INSERT sn) (CONS (grammar_NT N) rest) = F`,
  CHEAT_TAC);;

(* [local] *)
let null2 = prove
 (`nullableML G sn (CONS x (CONS y z)) <=>
       nullableML G sn [x] /\ nullableML G sn [y] /\
       nullableML G sn z`,
  CHEAT_TAC);;


(* HOL4 gramPropsScript.sml:197-243: the ML values that the definitions
   below antiquote *)

(* HOL4 gramPropsScript.sml:245-249: ML code, not ported *)

(* HOL4 gramPropsScript.sml:251-260: ML code, not ported *)

(* HOL4 gramPropsScript.sml:262-274: ML code, not ported *)

(* HOL4 gramPropsScript.sml:276-280: ML code, not ported *)

(* HOL4 gramPropsScript.sml:282-286: ML code, not ported *)

let fringe_lengths_def = new_definition
  `fringe_lengths G sf = {LENGTH i | (\G. RTC (derive G)) G sf (MAP
  grammar_TOK i)}`;;

(* HOL4 gramPropsScript.sml:292: ML code, not ported *)
let fringe_length_ptree = prove
 (`!G i pt. ptree_fringe pt = MAP grammar_TOK i /\ valid_ptree G pt ==>
           LENGTH i IN fringe_lengths G [ptree_head pt]`,
  CHEAT_TAC);;

let fringe_length_not_nullable = prove
 (`!G s. ~(nullable G [s]) ==>
          (!pt. ptree_head pt = s ==> valid_ptree G pt ==>
               0 < LENGTH (ptree_fringe pt))`,
  CHEAT_TAC);;

let derives_singleTOK = prove
 (`(\G. RTC (derive G)) G [grammar_TOK t] l <=> (l = [grammar_TOK t])`,
  CHEAT_TAC);;
add_simp derives_singleTOK;;

let fringe_lengths_V = prove
 (`fringe_lengths cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) gram_nV)] =
  {1}`,
  CHEAT_TAC);;

(* HOL4 gramPropsScript.sml:340-350: a theorem that HOL4 states as the value
   of an ML expression: parsing_ind *)

(* and the interface *)
let _ = unhide_overloads ();;
