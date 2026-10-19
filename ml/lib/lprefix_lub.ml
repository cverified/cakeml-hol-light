(* ======================================================== *)
(*  lprefix_lub: ported from HOL4's
    examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml  *)
(* ======================================================== *)

(* this file needs nothing of the port *)
(* HOL4 ancestors outside the port: list rich_list llist pred_set
   option *)

let lprefix_chain_def = cake_define
  `lprefix_chain ls <=>
     (!ll1 ll2. ll1 IN ls /\ ll2 IN ls ==> LPREFIX ll1 ll2 \/
       LPREFIX ll2 ll1)`;;

let lprefix_chain_nth_def = cake_define
  `lprefix_chain_nth n ls =
     some (\x. ?l. l IN ls /\ LNTH n l = SOME x)`;;

let lprefix_lub_def = cake_define
  `lprefix_lub ls lub <=>
     (!ll. ll IN ls ==> LPREFIX ll lub) /\
     (!ub. (!ll. ll IN ls ==> LPREFIX ll ub) ==> LPREFIX lub ub)`;;

let build_lprefix_lub_f_def = cake_define
  `build_lprefix_lub_f ls n =
     OPTION_MAP (\x. (n + 1,x)) (lprefix_chain_nth n ls)`;;

let build_lprefix_lub_def = cake_define
  `build_lprefix_lub ls =
     LUNFOLD (build_lprefix_lub_f ls) 0`;;
