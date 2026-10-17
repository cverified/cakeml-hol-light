(* ======================================================== *)
(*  cmlNTProps: ported from HOL4's
    compiler/parsing/proofs/cmlNTPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties (first sets etc) for non-terminals in the CakeML grammar
*)

needs "lib/NTproperties.ml";;
needs "semantics/gram.ml";;
needs "semantics/proofs/gramProps.ml";;
(* HOL4 ML code, not ported:
val _ =
firstSetML_def |> CONJUNCTS |> (fn l => List.take(l,2)) |> rewrites
                                                        |> (fn ss =>
                                                          augment_srw_ss
                                                          [ss])
*)
