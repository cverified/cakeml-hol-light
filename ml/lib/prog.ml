(* ======================================================== *)
(*  prog: ported from HOL4's
    examples/machine-code/hoare-triple/progScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by ag32_prog.ml, misc.ml and
    temporal_state.ml.  *)
(* ======================================================== *)

needs "lib/set_sep.ml";;
needs "lib/tailrec.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: pred_set arithmetic *)

let rel_sequence_def = new_definition
  `rel_sequence R seq state = (
     (seq 0 = state) /\
     (!n. if (?x. R (seq n) x) then R (seq n) (seq (SUC n)) else (seq
       (SUC n) = seq n)))`;;

let SEP_REFINE_def = new_definition
  `SEP_REFINE p less to_set state = (?s. less s state /\ p (to_set s))`;;

let RUN_def = new_definition
  `RUN
  ((to_set,next',instr,less,allow):('a->'b->bool)#('a->'a->bool)#('c->'b->bool)
  #('a->'a->bool)#('a->bool)) p q =
     (!state r. SEP_REFINE (p * r) less to_set state \/ allow state ==>
               (!seq. rel_sequence next' seq state ==>
                     (?i. SEP_REFINE (q * r) less to_set (seq i) \/ allow
                       (seq i))))`;;

let CODE_POOL_def = new_definition
  `CODE_POOL instr c = (\s. s = UNIONS (IMAGE instr c))`;;

let SPEC_def = new_definition
  `SPEC
  ((to_set,next',instr,less,allow):('a->'b->bool)#('a->'a->bool)#('c->'b->bool)
  #('a->'a->bool)#('a->bool)) p c q =
     RUN (to_set,next',instr,less,allow) (CODE_POOL instr c * p)
                              (CODE_POOL instr c * q)`;;
