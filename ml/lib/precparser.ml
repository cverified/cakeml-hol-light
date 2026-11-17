(* ======================================================== *)
(*  precparser: ported from HOL4's
    examples/formal-languages/context-free/precparserScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by camlPtreeConversion.ml.  *)
(* ======================================================== *)

(* this file needs nothing of the port *)

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: option list *)


let tokrel_INDUCT,tokrel_RECURSION = define_datatype
  "tokrel =
     precparser_Reduce
   | precparser_Shift";;

let pMachine_FIELDS = define_record "pMachine"
  ["rules","'tok#'tok->tokrel option";
   (* stk tok , strm tok *)
   "reduce","'trm->'tok->'trm->'trm option";
   "lift","'tok->'trm";
   "isOp","'tok->bool";
   "mkApp","'trm->'trm->'trm option"];;
let precparse1_def = new_definition
  `precparse1 pM (stk,strm) =
      (match strm with
          [] ->
            (match stk with CONS (INR tm2) (CONS (INL opn) (CONS (INR tm1)
              rest)) ->
                  OPTION_MAP (\r. (CONS (INR r) rest,[])) (pMachine_reduce
                    pM tm1 opn tm2)
              | _ -> NONE)
        | CONS tok strm_rest ->
          (if pMachine_isOp pM tok then
            match stk with CONS (INR tm2) (CONS (INL opn) (CONS (INR tm1)
              stk_rest)) ->
                (match pMachine_rules pM (opn,tok) with
                     SOME precparser_Shift -> SOME (CONS (INL tok)
                       stk,strm_rest)
                   | SOME precparser_Reduce ->
                       OPTION_MAP (\r. (CONS (INR r) stk_rest,CONS tok
                         strm_rest))
                              (pMachine_reduce pM tm1 opn tm2)
                   | NONE -> NONE)
              | [INR tm] -> SOME ([INL tok; INR tm],strm_rest)
              | _ -> NONE
          else match stk with
                [] -> SOME ([INR (pMachine_lift pM tok)],strm_rest)
              | CONS (INR ftm) stk_rest ->
                  OPTION_MAP (\r. (CONS (INR r) stk_rest,strm_rest))
                             (pMachine_mkApp pM ftm (pMachine_lift pM tok))
              | CONS (INL _) _ -> SOME (CONS (INR (pMachine_lift pM tok))
                stk,strm_rest)))`;;

(* HOL4 precparserScript.sml:133-136: the definition *)


(* the termination relation that HOL4 gives is
     inv_image (MEASURE LENGTH LEX MEASURE LENGTH) (\(_,y,z). (z,y))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 precparserScript.sml:140-149: the tactic that proves the termination *)
let precparse_def,precparse_ind = define_guess
  `precparse pM (stk0,strm0) =
      if isFinal (stk0,strm0) then SOME (OUTR (HD stk0))
      else match precparse1 pM (stk0,strm0) with
            NONE -> NONE
          | SOME (stk,strm) -> precparse pM (stk,strm)`;;
