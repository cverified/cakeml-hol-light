(* ======================================================== *)
(*  namespace: ported from HOL4's
    semantics/namespaceScript.sml
    A definition theory, with 19 definitions, 2 datatypes and no
    theorems.  Needed by 31 files of the port.  *)
(* ======================================================== *)

(*
  Defines a datatype for nested namespaces where names can be either
  short (e.g. foo) or long (e.g. ModuleA.InnerB.bar).
*)

(* this file needs nothing of the port *)

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "namespace" [];;
(* HOL4 ancestors outside the port: alist *)

(* HOL4 namespaceScript.sml:11: the type abbreviation alist, which
   the port expands *)

(* Identifiers *)
let namespace_id_INDUCT,namespace_id_RECURSION = define_datatype
  "namespace_id = Short ('n) | Long ('m) (namespace_id)";;

let mk_id_def,mk_id_ind = define_rec
  [`mk_id [] n = Short n`;
   `mk_id (CONS mn mns) n = Long mn (mk_id mns n)`];;

let id_to_n_def,id_to_n_ind = define_rec
  [`id_to_n (Short n) = n`;
   `id_to_n (Long _1 id') = id_to_n id'`];;

let id_to_mods_def,id_to_mods_ind = define_rec
  [`id_to_mods (Short _2) = []`;
   `id_to_mods (Long mn id') = CONS mn (id_to_mods id')`];;

let namespace_INDUCT,namespace_RECURSION = define_datatype
  "namespace = Bind (('n#'v) list) (('m#namespace) list)";;

let _ = size_thms "namespace_id";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let nsLookup_def,nsLookup_ind = define_wf
  `MEASURE (\(x0,x1). namespace_id_size (\x. 0) (\x. 0) x1)`
  [`nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
      ALOOKUP v n`;
   `nsLookup (Bind v m) (Long mn id') =
      (match ALOOKUP m mn with NONE -> NONE | SOME env ->
        nsLookup env id')`];;

let nsLookupMod_def,nsLookupMod_ind = define_guess
  [`nsLookupMod (e:('m,'n,'v)namespace) [] = SOME
  (e:('m,'n,'v)namespace)`;
   `nsLookupMod (Bind v m) (CONS mn path') =
    (match ALOOKUP m mn with NONE -> NONE | SOME env ->
      nsLookupMod env path')`];;

let nsEmpty_def = new_definition
  `nsEmpty = Bind [] []`;;

let nsAppend_def = define_general
  [`nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (APPEND v1 v2) (APPEND
  m1 m2)`];;

let nsLift_def = new_definition
  `nsLift mn env = Bind [] [(mn,env)]`;;

let alist_to_ns_def = new_definition
  `alist_to_ns a = Bind a []`;;

let nsBind_def = define_general
  [`nsBind k x (Bind v m) = Bind (CONS (k,x) v) m`];;

let nsBindList_def = new_definition
  `nsBindList l e = ITLIST (\(x,v) e. nsBind x v e) l e`;;

let nsOptBind_def = new_definition
  `nsOptBind n x env = (match n with NONE -> env | SOME n -> nsBind n
  x env)`;;

let nsSing_def = new_definition
  `nsSing n x = Bind [(n,x)] []`;;

let nsSub_def = new_definition
  `nsSub r env1 env2 <=>
      (!id' v1.
         nsLookup env1 id' = SOME v1 ==>
         (?v2. nsLookup env2 id' = SOME v2 /\ r id' v1 v2)) /\
      (!path'. nsLookupMod env2 path' = NONE ==> nsLookupMod env1
        path' = NONE)`;;

let nsAll_def = new_definition
  `nsAll f env <=> (!id' v. nsLookup env id' = SOME v ==> f id' v)`;;

let nsAll2_def = new_definition
  `nsAll2 r env1 env2 <=>
     nsSub r env1 env2 /\ nsSub (\x y z. r x z y) env2 env1`;;

let nsDom_def = new_definition
  `nsDom (env:('m,'n,'v)namespace) =
      {n | (v,n) | v IN (UNIV:'v->bool) /\ n IN
        (UNIV:('m,'n)namespace_id->bool) /\ nsLookup env n = SOME v}`;;

let nsDomMod_def = new_definition
  `nsDomMod (env:('m,'n,'v)namespace) =
      {n | (v,n) | v IN (UNIV:('m,'n,'v)namespace->bool) /\ n IN
        (UNIV:'m list->bool) /\
                   nsLookupMod env n = SOME v}`;;

let nsMap_def,nsMap_ind = define_shaped_rec
  "nested"
  [`nsMap (f:'v->'w) ((Bind v m):('m,'n,'v)namespace) =
     Bind (MAP (\(n,x). (n,f x)) v) (MAP (\(mn,e). (mn,nsMap f
       e)) m)`];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
