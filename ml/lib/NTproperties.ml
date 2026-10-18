(* ======================================================== *)
(*  NTproperties: ported from HOL4's
    examples/formal-languages/context-free/NTpropertiesScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by cmlNTProps.ml, gramProps.ml,
    pegComplete.ml and pegSound.ml.  *)
(* ======================================================== *)

needs "lib/grammar.ml";;
(* HOL4 ancestors outside the port: list pred_set *)

let nullable_def = cake_define
  `nullable G sf = (\G. RTC (derive G)) G sf []`;;
(* HOL4 NTpropertiesScript.sml:32: the overload nullableNT, which the
   port expands *)
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 NTpropertiesScript.sml:120-132: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let nullableML_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\s. CARD (FDOM (grammar_rules G) DIFF s)) LEX MEASURE
     LENGTH`)
  CHEAT_TAC
  [`nullableML G seen [] = T`;
   `nullableML G seen (grammar_TOK t :: _1) = F`;
   `nullableML G seen (grammar_NT n :: rest) =
        (if n IN FDOM (grammar_rules G) /\ ~(n IN seen) then
          if FAPPLY (grammar_rules G) n INTER {r | nullableML G
            (n INSERT seen) r} = {} then F else nullableML G seen
            rest else F)`];;

let firstSet_def = cake_define
  `firstSet G sf = {t | ?rest. (\G. RTC (derive G)) G sf (grammar_TOK
  t :: rest)}`;;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 NTpropertiesScript.sml:368-380: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let firstSetML_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\s. CARD (FDOM (grammar_rules G) DIFF s)) LEX MEASURE
     LENGTH`)
  CHEAT_TAC
  [`firstSetML G seen [] = {}`;
   `firstSetML G seen (grammar_TOK t :: _2) = {t}`;
   `firstSetML G seen (grammar_NT n :: rest) =
      (if n IN FDOM (grammar_rules G) then
        (if ~(n IN seen) then
          BIGUNION (IMAGE (firstSetML G (n INSERT seen))
                          (FAPPLY (grammar_rules G) n)) else {})
                            UNION
        (if nullable G [grammar_NT n] then firstSetML G seen
          rest else {}) else {})`];;
