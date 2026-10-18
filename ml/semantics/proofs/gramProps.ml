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
(* HOL4 ancestors outside the port: pred_set *)

(* HOL4 gramPropsScript.sml:12-13: ML code, not ported *)

(* HOL4 gramPropsScript.sml:15-19: ML code, not ported *)

(* HOL4 gramPropsScript.sml:21-32: ML code, not ported *)

(* HOL4 gramPropsScript.sml:34-36: ML code, not ported *)

let NT_rank_def = cake_define
  `NT_rank N =
     (match N with INR _1 -> 0 | INL n ->
         (if n = nElist1 then 16 else if n = nEseq then 16 else if
           n = nTopLevelDecs then 16 else if n = nElist2 then 16 else
           if n = nE then 15 else if n = nEhandle then 14 else if n =
           nPE then 14 else if n = nElogicOR then 13 else if n =
           nElogicAND then 12 else if n = nEtyped then 11 else if n =
           nEbefore then 10 else if n = nEcomp then 9 else if n =
           nErel then 8 else if n = nElistop then 7 else if n = nEadd
           then 6 else if n = nEmult then 5 else if n = nEapp then 4
           else if n = nEbase then 3 else if n = nFQV then 2 else if
           n = nV then 1 else if n = nDtypeCons then 3 else if n =
           nDconstructor then 2 else if n = nConstructorName then 2
           else if n = nUQConstructorName then 1 else if n =
           nTypeList2 then 8 else if n = nTypeList1 then 7 else if n
           = nType then 6 else if n = nPType then 5 else if n =
           nDType then 4 else if n = nTbaseList then 4 else if n =
           nPTbase then 3 else if n = nTbase then 3 else if n = nTyOp
           then 2 else if n = nTypeName then 2 else if n = nUQTyOp
           then 1 else if n = nNonETopLevelDecs then 4 else if n =
           nDecls then 3 else if n = nStructure then 1 else if n =
           nDecl then 2 else if n = nTypeDec then 1 else if n =
           nSpecLineList then 3 else if n = nSpecLine then 2 else if
           n = nPtuple then 2 else if n = nPbase then 3 else if n =
           nPbaseList1 then 4 else if n = nPapp then 4 else if n =
           nPcons then 5 else if n = nPas then 6 else if n = nPattern
           then 7 else if n = nPatternList then 8 else if n = nPEs
           then 9 else if n = nLetDecs then 2 else if n = nLetDec
           then 1 else if n = nDtypeDecl then 3 else if n =
           nAndFDecls then 3 else if n = nFDecl then 2 else if n =
           nTyVarList then 2 else if n = nTyvarN then 1 else 0))`;;

(* HOL4 gramPropsScript.sml:104-131: a theorem that HOL4 states as
   the value of an ML expression: cmlG_applied *)
(* HOL4 gramPropsScript.sml:104-131: the ML values that the
   definitions below antiquote *)

(* HOL4 gramPropsScript.sml:133-134: a theorem that HOL4 states as
   the value of an ML expression: cmlG_FDOM *)

let paireq = cake_theorem "paireq[local]"
  (fun () ->
    `(x,y) = z <=> x = FST z /\ y = SND z`)
  CHEAT_TAC;;

let GSPEC_INTER = cake_theorem "GSPEC_INTER[local]"
  (fun () ->
    `GSPEC f INTER Q =
       GSPEC (S ((,) o FST o f) (S ((/\) o SND o f) (Q o FST o
         f)))`)
  CHEAT_TAC;;

let RIGHT_INTER_OVER_UNION =
  cake_theorem "RIGHT_INTER_OVER_UNION[local]"
  (fun () ->
    `(a UNION b) INTER c = (a INTER c) UNION (b INTER c)`)
  CHEAT_TAC;;

let GSPEC_applied = cake_theorem "GSPEC_applied[local]"
  (fun () ->
    `GSPEC f x <=> x IN GSPEC f`)
  CHEAT_TAC;;

(* HOL4 gramPropsScript.sml:162-167: the ML values that the
   definitions below antiquote *)

(* HOL4 gramPropsScript.sml:169-175: ML code, not ported *)

(* HOL4 gramPropsScript.sml:177: ML code, not ported *)

(* HOL4 gramPropsScript.sml:179: ML code, not ported *)

let nullloop_th = cake_theorem "nullloop_th[local]"
  (fun () ->
    `nullableML G (N INSERT sn) (grammar_NT N :: rest) = F`)
  CHEAT_TAC;;

let null2 = cake_theorem "null2[local]"
  (fun () ->
    `nullableML G sn (x :: y :: z) <=>
         nullableML G sn [x] /\ nullableML G sn [y] /\
         nullableML G sn z`)
  CHEAT_TAC;;


(* HOL4 gramPropsScript.sml:197-243: the ML values that the
   definitions below antiquote *)

(* HOL4 gramPropsScript.sml:245-249: ML code, not ported *)

(* HOL4 gramPropsScript.sml:251-260: ML code, not ported *)

(* HOL4 gramPropsScript.sml:262-274: ML code, not ported *)

(* HOL4 gramPropsScript.sml:276-280: ML code, not ported *)

(* HOL4 gramPropsScript.sml:282-286: ML code, not ported *)

let fringe_lengths_def = cake_define
  `fringe_lengths G sf = {LENGTH i | (\G. RTC (derive G)) G sf (MAP
  grammar_TOK i)}`;;

(* HOL4 gramPropsScript.sml:292: ML code, not ported *)
let fringe_length_ptree = cake_theorem "fringe_length_ptree"
  (fun () ->
    `!G i pt. ptree_fringe pt = MAP grammar_TOK i /\ valid_ptree G pt
  ==>
             LENGTH i IN fringe_lengths G [ptree_head pt]`)
  CHEAT_TAC;;

let fringe_length_not_nullable =
  cake_theorem "fringe_length_not_nullable"
  (fun () ->
    `!G s. ~(nullable G [s]) ==>
            (!pt. ptree_head pt = s ==> valid_ptree G pt ==>
                 0 < LENGTH (ptree_fringe pt))`)
  CHEAT_TAC;;

let derives_singleTOK = cake_theorem "derives_singleTOK[simp]"
  (fun () ->
    `(\G. RTC (derive G)) G [grammar_TOK t] l <=> (l = [grammar_TOK
  t])`)
  CHEAT_TAC;;

let fringe_lengths_V = cake_theorem "fringe_lengths_V"
  (fun () ->
    `fringe_lengths cmlG [grammar_NT ((INL:MMLnonT->MMLnonT+num) nV)]
  = {1}`)
  CHEAT_TAC;;

(* HOL4 gramPropsScript.sml:340-350: a theorem that HOL4 states as
   the value of an ML expression: parsing_ind *)
