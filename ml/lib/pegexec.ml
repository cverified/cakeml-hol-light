(* ======================================================== *)
(*  pegexec: ported from HOL4's
    examples/formal-languages/context-free/pegexecScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/location.ml";;
needs "lib/peg.ml";;
(* HOL4 ancestors outside the port: rich_list *)

let kont_INDUCT,kont_RECURSION = define_datatype
  "kont = pegexec_ksym (('atok,'bnt,'cvalue,'err)pegsym) (kont) \
   (kont) | pegexec_appf1 ('cvalue->'cvalue) (kont) | pegexec_appf2 \
   ('cvalue->'cvalue->'cvalue) (kont) | pegexec_dropErr (kont) | \
   pegexec_addErr (locs) ('err) (kont) | pegexec_cmpErrs (kont) | \
   pegexec_cmpEO ((locs#'err) option) (kont) | pegexec_returnTo \
   (('atok#locs) list) (('cvalue option) list) (kont) | \
   pegexec_restoreEO ((locs#'err) option) (kont) | pegexec_poplist \
   ('cvalue list->'cvalue) (kont) | pegexec_listsym \
   (('atok,'bnt,'cvalue,'err)pegsym) ('cvalue list->'cvalue) (kont) | \
   pegexec_done | pegexec_failed";;
hol4_overload "ksym" "pegexec_ksym";;
hol4_overload "appf1" "pegexec_appf1";;
hol4_overload "appf2" "pegexec_appf2";;
hol4_overload "dropErr" "pegexec_dropErr";;
hol4_overload "addErr" "pegexec_addErr";;
hol4_overload "cmpErrs" "pegexec_cmpErrs";;
hol4_overload "cmpEO" "pegexec_cmpEO";;
hol4_overload "returnTo" "pegexec_returnTo";;
hol4_overload "restoreEO" "pegexec_restoreEO";;
hol4_overload "poplist" "pegexec_poplist";;
hol4_overload "listsym" "pegexec_listsym";;
hol4_overload "done" "pegexec_done";;
hol4_overload "failed" "pegexec_failed";;

let poplist_aux_def = cake_define_list
  [`poplist_aux acc (SOME h :: t) = poplist_aux (h :: acc) t`;
   `poplist_aux acc (NONE :: t) = (acc,t)`;
   `poplist_aux acc [] = (acc,[])`];;

let poplistval_def = cake_define
  `poplistval f l = (let (values,rest) = poplist_aux [] l in
                      SOME (f values) :: rest)`;;

let evalcase_INDUCT,evalcase_RECURSION = define_datatype
  "evalcase = pegexec_EV (('atok,'bnt,'cvalue,'err)pegsym) \
   (('atok#locs) list) (('cvalue option) list) ((locs#'err) option) \
   ((locs#'err) list) (('atok,'bnt,'cvalue,'err)kont) \
   (('atok,'bnt,'cvalue,'err)kont) | pegexec_AP \
   (('atok,'bnt,'cvalue,'err)kont) (('atok#locs) list) (('cvalue \
   option) list) ((locs#'err) option) ((locs#'err) list) | \
   pegexec_Result ((('atok#locs) list,'cvalue,'err)pegresult) | \
   pegexec_Looped";;
hol4_overload "EV" "pegexec_EV";;
hol4_overload "AP" "pegexec_AP";;
hol4_overload "Result" "pegexec_Result";;
hol4_overload "Looped" "pegexec_Looped";;

(* HOL4 pegexecScript.sml:55: the overload OME, which the port
   expands *)
(* HOL4 pegexecScript.sml:56: the overload EOF, which the port
   expands *)

let coreloop_def = cake_define
  `coreloop G =
    OWHILE (\s. match s with pegexec_Result _1 -> F | _2 -> T)
           (\s. match s with
                    pegexec_EV (peg_empty v) i r eo errs k fk ->
                      pegexec_AP k i (SOME v :: r) eo errs | pegexec_EV
                      (peg_any tf) i r eo errs k fk ->
                    (match i with
                         [] -> (let err = ((Locs EOFpt
                           EOFpt),peg_anyEOF G) in
                              pegexec_AP fk i r ((optmax MAXerr) eo
                                (SOME err)) (err :: errs)) | h :: t ->
                                pegexec_AP k t (SOME (tf h) :: r) eo
                                errs) | pegexec_EV (peg_tok P tf2) i r
                                eo errs k fk ->
                    (match i with
                         [] -> (let err = ((Locs EOFpt
                           EOFpt),peg_tokEOF G) in
                              pegexec_AP fk i r ((optmax MAXerr) eo
                                (SOME err)) (err :: errs)) | h :: t ->
                                (if P (FST h) then
                              pegexec_AP k t (SOME (tf2 h) :: r) eo
                                errs else let err = (sloc i,peg_tokFALSE
                                G) in pegexec_AP fk i r ((optmax MAXerr)
                                eo (SOME err))
                              (err :: errs))) | pegexec_EV (peg_nt n
                                tf3) i r eo errs k fk ->
                    (if n IN FDOM (peg_rules G) then
                      pegexec_EV (FAPPLY (peg_rules G) n) i r eo errs
                        (pegexec_appf1 tf3 k) fk else
                      pegexec_Looped) | pegexec_EV (peg_seq e1 e2 f)
                        i r eo errs k fk ->
                      pegexec_EV e1 i r eo errs
                         (pegexec_restoreEO eo
                          (pegexec_ksym e2
                           (pegexec_appf2 f k)
                           (pegexec_cmpEO eo (pegexec_returnTo i r
                             fk))))
                         fk | pegexec_EV (peg_choice e1 e2 cf) i r eo
                           errs k fk ->
                      pegexec_EV e1 i r eo errs
                         (pegexec_appf1 (cf o INL) k)
                         (pegexec_returnTo i r
                          (pegexec_ksym e2
                           (pegexec_dropErr (pegexec_appf1 (cf o INR)
                             k))
                           (pegexec_cmpErrs fk))) | pegexec_EV
                             (peg_rpt e lf) i r eo errs k fk ->
                      pegexec_EV e i (NONE :: r) eo errs
                         (pegexec_restoreEO eo (pegexec_listsym e lf
                           k))
                         (pegexec_poplist lf k) | pegexec_EV (peg_not
                           e v) i r eo errs k fk ->
                      pegexec_EV e i r eo errs
                         (pegexec_restoreEO eo
                            (pegexec_returnTo i r (pegexec_addErr
                              (sloc i) (peg_notFAIL G) fk)))
                         (pegexec_restoreEO eo (pegexec_returnTo i
                           (SOME v :: r) (pegexec_dropErr k))) |
                           pegexec_EV (peg_error err) i r eo errs k fk
                           ->
                      (let err = (sloc i,err) in
                        pegexec_AP fk i r ((optmax MAXerr) eo (SOME
                          err)) (err :: errs)) | pegexec_AP pegexec_done
                          i [] _3 _4 -> pegexec_Looped | pegexec_AP
                          pegexec_done i (NONE :: t) _5 _6 ->
                          pegexec_Looped | pegexec_AP pegexec_done i
                          (SOME rv :: _7) eo _8 -> pegexec_Result
                          (peg_Success i rv eo) | pegexec_AP
                          pegexec_failed i r _9 [] -> pegexec_Looped |
                          pegexec_AP pegexec_failed i r _10 ((l,e) ::
                          _11) -> pegexec_Result (peg_Failure l e) |
                          pegexec_AP (pegexec_dropErr _12) i r _13 [] ->
                          pegexec_Looped | pegexec_AP (pegexec_dropErr
                          k) i r eo (_14 :: t) -> pegexec_AP k i r eo t
                          | pegexec_AP (pegexec_addErr l e k) i r eo
                          errs ->
                      pegexec_AP k i r ((optmax MAXerr) eo (SOME
                        (l,e))) ((l,e) :: errs) | pegexec_AP
                        (pegexec_cmpErrs k) i r _15 [] -> pegexec_Looped
                        | pegexec_AP (pegexec_cmpErrs k) i r _16 [_17]
                        -> pegexec_Looped | pegexec_AP (pegexec_cmpErrs
                        k) i r eo ((l2,er2) :: (l1,er1) :: rest) ->
                      pegexec_AP k i r eo
                         ((if locsle l1 l2 then (l2,er2) else
                           (l1,er1)) :: rest) | pegexec_AP
                           (pegexec_cmpEO eo1 k) i r eo2 [] ->
                           pegexec_Looped | pegexec_AP (pegexec_cmpEO
                           eo1 k) i r eo2 ((l,err) :: rest) ->
                      pegexec_AP k i r ((optmax MAXerr) eo1 (SOME
                        (l,err))) ((l,err) :: rest) | pegexec_AP
                        (pegexec_ksym e k fk) i r eo errs -> pegexec_EV
                        e i r eo errs k fk | pegexec_AP (pegexec_appf1
                        f1 k) i (SOME v :: r) eo errs ->
                      pegexec_AP k i (SOME (f1 v) :: r) eo errs |
                        pegexec_AP (pegexec_appf1 _18 _19) _20 _21 _22
                        _23 -> pegexec_Looped | pegexec_AP
                        (pegexec_appf2 f2 k) i (SOME v1 :: SOME v2 :: r)
                        eo errs ->
                      pegexec_AP k i (SOME (f2 v2 v1) :: r) eo errs |
                        pegexec_AP (pegexec_appf2 _24 _25) _26 _27 _28
                        _29 -> pegexec_Looped | pegexec_AP
                        (pegexec_returnTo i r k) i' r' eo errs ->
                        pegexec_AP k i r eo errs | pegexec_AP
                        (pegexec_restoreEO eo k) i r eo' errs ->
                        pegexec_AP k i r eo errs | pegexec_AP
                        (pegexec_listsym e f k) i r eo errs ->
                      pegexec_EV e i r eo errs (pegexec_restoreEO eo
                        (pegexec_listsym e f k)) (pegexec_poplist f k) |
                        pegexec_AP (pegexec_poplist f k) i r eo [] ->
                        pegexec_Looped | pegexec_AP (pegexec_poplist f
                        k) i r eo (e :: errs) ->
                      pegexec_AP k i (poplistval f r) eo errs |
                        pegexec_Result r -> pegexec_Result r |
                        pegexec_Looped -> pegexec_Looped)`;;

let peg_exec_def = cake_define
  `peg_exec (G:('atok,'bnt,'cvalue,'err)peg) e i r eo errs k fk =
     (match coreloop G (pegexec_EV e i r eo errs k fk) with
         SOME r -> r | NONE -> pegexec_Looped)`;;

let destResult_def = cake_define
  `pegexec_destResult (pegexec_Result r) = r`;;
hol4_overload "destResult" "pegexec_destResult";;

let pegparse_def = cake_define
  `pegparse G s =
     (if wfG G then
       match pegexec_destResult (peg_exec G (start G) s [] NONE []
         pegexec_done pegexec_failed) with
         peg_Success s v eo -> SOME (s,v,eo) | _30 -> NONE else
           NONE)`;;
