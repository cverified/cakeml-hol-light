(* ================================================================== *)
(* The end of an abstract.                                            *)
(*                                                                    *)
(* ml/lib/fast.ml takes the name of every way of making a definition  *)
(* and of prove, so that a session loads the port for its side        *)
(* effects only.  This file gives those names back, which is what     *)
(* tools/bin/abstract leaves a session ready for: the port that a     *)
(* file stands on is there in a few minutes, and the file itself is   *)
(* then loaded for real.                                              *)
(*                                                                    *)
(* What was assumed while the abstract was on stays assumed, so       *)
(* length (axioms ()) still says nothing about the port.  What is     *)
(* loaded after this line is proved.                                  *)
(* ================================================================== *)

let cake_abstract = false;;

let new_definition = real_new_definition;;
let define_cases = real_define_cases;;
let define_general = real_define_general;;
let define_general_cheat = real_define_general_cheat;;
let define_shaped = real_define_shaped;;
let assume_definition = real_assume_definition;;
let define_rec = real_define_rec;;
let define_wf = real_define_wf;;
let define_wf_cheat = real_define_wf_cheat;;
let define_wf_tac = real_define_wf_tac;;
let define_guess = real_define_guess;;
let define_guess_cheat = real_define_guess_cheat;;
let define_shaped_rec = real_define_shaped_rec;;
let define_shaped_rec_cheat = real_define_shaped_rec_cheat;;
let define_shaped_rec_tac = real_define_shaped_rec_tac;;
let define_shaped_wf = real_define_shaped_wf;;
let define_shaped_wf_cheat = real_define_shaped_wf_cheat;;
let define_shaped_wf_tac = real_define_shaped_wf_tac;;
let assume_definition_rec = real_assume_definition_rec;;
let prove = real_prove;;

print_string
  "\n*** REAL: what is below this line is proved ***\n\n";;
