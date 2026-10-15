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
  "kont = ksym (('atok,'bnt,'cvalue,'err)pegsym) (kont) (kont) | \
   appf1 ('cvalue->'cvalue) (kont) | appf2 \
   ('cvalue->'cvalue->'cvalue) (kont) | dropErr (kont) | addErr \
   (locs) ('err) (kont) | cmpErrs (kont) | cmpEO ((locs#'err) option) \
   (kont) | returnTo (('atok#locs) list) (('cvalue option) list) \
   (kont) | restoreEO ((locs#'err) option) (kont) | poplist ('cvalue \
   list->'cvalue) (kont) | listsym (('atok,'bnt,'cvalue,'err)pegsym) \
   ('cvalue list->'cvalue) (kont) | done | failed";;

let poplist_aux_def = cake_define
  `poplist_aux acc (SOME h :: t) = poplist_aux (h :: acc) t /\
   poplist_aux acc (NONE :: t) = (acc,t) /\
   poplist_aux acc [] = (acc,[])`;;

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

(* HOL4 overload (expanded in the port):
     OME = optmax MAXerr *)
(* HOL4 overload (expanded in the port):
     EOF = Locs EOFpt EOFpt *)

let coreloop_def = cake_define
  `coreloop G =
    OWHILE (\s. match s with Result _1 -> F | _2 -> T)
           (\s. match s with
                    EV (empty v) i r eo errs k fk -> AP k i (SOME v
                      :: r) eo errs | EV (any tf) i r eo errs k fk ->
                    (match i with
                         [] -> (let err = ((Locs EOFpt
                           EOFpt),peg_anyEOF G) in
                              AP fk i r ((optmax MAXerr) eo (SOME
                                err)) (err :: errs)) | h :: t -> AP k t
                                (SOME (tf h) :: r) eo errs) | EV (tok P
                                tf2) i r eo errs k fk ->
                    (match i with
                         [] -> (let err = ((Locs EOFpt
                           EOFpt),peg_tokEOF G) in
                              AP fk i r ((optmax MAXerr) eo (SOME
                                err)) (err :: errs)) | h :: t -> (if P
                                (FST h) then
                              AP k t (SOME (tf2 h) :: r) eo errs else
                                let err = (sloc i,peg_tokFALSE G) in AP
                                fk i r ((optmax MAXerr) eo (SOME err))
                              (err :: errs))) | EV (nt n tf3) i r eo
                                errs k fk ->
                    (if n IN FDOM (peg_rules G) then
                      EV (FAPPLY (peg_rules G) n) i r eo errs (appf1
                        tf3 k) fk else
                      Looped) | EV (seq e1 e2 f) i r eo errs k fk ->
                      EV e1 i r eo errs
                         (restoreEO eo
                          (ksym e2
                           (appf2 f k)
                           (cmpEO eo (returnTo i r fk))))
                         fk | EV (choice e1 e2 cf) i r eo errs k fk
                           ->
                      EV e1 i r eo errs
                         (appf1 (cf o INL) k)
                         (returnTo i r
                          (ksym e2
                           (dropErr (appf1 (cf o INR) k))
                           (cmpErrs fk))) | EV (rpt e lf) i r eo errs
                             k fk ->
                      EV e i (NONE :: r) eo errs
                         (restoreEO eo (listsym e lf k))
                         (poplist lf k) | EV (not e v) i r eo errs k
                           fk ->
                      EV e i r eo errs
                         (restoreEO eo
                            (returnTo i r (addErr (sloc i)
                              (peg_notFAIL G) fk)))
                         (restoreEO eo (returnTo i (SOME v :: r)
                           (dropErr k))) | EV (error err) i r eo errs k
                           fk ->
                      (let err = (sloc i,err) in
                        AP fk i r ((optmax MAXerr) eo (SOME err))
                          (err :: errs)) | AP done i [] _3 _4 -> Looped
                          | AP done i (NONE :: t) _5 _6 -> Looped | AP
                          done i (SOME rv :: _7) eo _8 -> Result
                          (Success i rv eo) | AP failed i r _9 [] ->
                          Looped | AP failed i r _10 ((l,e) :: _11) ->
                          Result (Failure l e) | AP (dropErr _12) i r
                          _13 [] -> Looped | AP (dropErr k) i r eo (_14
                          :: t) -> AP k i r eo t | AP (addErr l e k) i r
                          eo errs ->
                      AP k i r ((optmax MAXerr) eo (SOME (l,e)))
                        ((l,e) :: errs) | AP (cmpErrs k) i r _15 [] ->
                        Looped | AP (cmpErrs k) i r _16 [_17] -> Looped
                        | AP (cmpErrs k) i r eo ((l2,er2) :: (l1,er1) ::
                        rest) ->
                      AP k i r eo
                         ((if locsle l1 l2 then (l2,er2) else
                           (l1,er1)) :: rest) | AP (cmpEO eo1 k) i r eo2
                           [] -> Looped | AP (cmpEO eo1 k) i r eo2
                           ((l,err) :: rest) ->
                      AP k i r ((optmax MAXerr) eo1 (SOME (l,err)))
                        ((l,err) :: rest) | AP (ksym e k fk) i r eo errs
                        -> EV e i r eo errs k fk | AP (appf1 f1 k) i
                        (SOME v :: r) eo errs ->
                      AP k i (SOME (f1 v) :: r) eo errs | AP (appf1
                        _18 _19) _20 _21 _22 _23 -> Looped | AP (appf2
                        f2 k) i (SOME v1 :: SOME v2 :: r) eo errs ->
                      AP k i (SOME (f2 v2 v1) :: r) eo errs | AP
                        (appf2 _24 _25) _26 _27 _28 _29 -> Looped | AP
                        (returnTo i r k) i' r' eo errs -> AP k i r eo
                        errs | AP (restoreEO eo k) i r eo' errs -> AP k
                        i r eo errs | AP (listsym e f k) i r eo errs ->
                      EV e i r eo errs (restoreEO eo (listsym e f k))
                        (poplist f k) | AP (poplist f k) i r eo [] ->
                        Looped | AP (poplist f k) i r eo (e :: errs) ->
                      AP k i (poplistval f r) eo errs | Result r
                        -> Result r | Looped -> Looped)`;;

let peg_exec_def = cake_define
  `peg_exec (G:('atok,'bnt,'cvalue,'err)peg) e i r eo errs k fk =
     (match coreloop G (EV e i r eo errs k fk) with
         SOME r -> r | NONE -> Looped)`;;

let destResult_def = cake_define
  `pegexec_destResult (Result r) = r`;;
hol4_overload "destResult" "pegexec_destResult";;
