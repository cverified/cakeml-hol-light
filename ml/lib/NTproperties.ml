(* ======================================================== *)
(*  NTproperties: ported from HOL4's
    examples/formal-languages/context-free/NTpropertiesScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by cmlNTProps.ml, gramProps.ml,
    pegComplete.ml and pegSound.ml.  *)
(* ======================================================== *)

needs "lib/grammar.ml";;

(* of no theory of the port: what it registers is in the scope of every file *)
let _ = cake_library ();;
(* HOL4 ancestors outside the port: list pred_set *)

let nullable_def = new_definition
  `nullable G sf = (\G. RTC (derive G)) G sf []`;;
(* HOL4 NTpropertiesScript.sml:32: the overload nullableNT, which the
   port expands *)
(* the termination relation that HOL4 gives is
     MEASURE (\s. CARD (FDOM (grammar_rules G) DIFF s)) LEX MEASURE
       LENGTH
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 NTpropertiesScript.sml:120-132: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let nullableML_def,nullableML_ind = define_guess_cheat
  [`nullableML G seen [] = T`;
   `nullableML G seen (CONS (grammar_TOK t) _1) = F`;
   `nullableML G seen (CONS (grammar_NT n) rest) =
        (if n IN FDOM (grammar_rules G) /\ ~(n IN seen) then
          if FAPPLY (grammar_rules G) n INTER {r | nullableML G
              (n INSERT seen) r} = {} then F else nullableML G seen
              rest else F)`];;

let firstSet_def = new_definition
  `firstSet G sf = {t | ?rest. (\G. RTC (derive G)) G sf (CONS
  (grammar_TOK t) rest)}`;;

let firstSetML_def,firstSetML_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`firstSetML G seen [] = {}`;
   `firstSetML G seen (CONS (grammar_TOK t) _2) = {t}`;
   `firstSetML G seen (CONS (grammar_NT n) rest) =
      (if n IN FDOM (grammar_rules G) then
        (if ~(n IN seen) then
          UNIONS (IMAGE (firstSetML G (n INSERT seen))
                          (FAPPLY (grammar_rules G) n)) else {})
                              UNION
        (if nullable G [grammar_NT n] then firstSetML G seen
            rest else {}) else {})`];;
