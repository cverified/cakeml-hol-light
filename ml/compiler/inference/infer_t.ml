(* ======================================================== *)
(*  infer_t: ported from HOL4's
    compiler/inference/infer_tScript.sml  *)
(* ======================================================== *)

(*
  The infer_t datatype and various to_string functions.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

let infer_t_INDUCT,infer_t_RECURSION = define_datatype
  "infer_t = Infer_Tvar_db (num) | Infer_Tapp (infer_t list) (num) | \
   Infer_Tuvar (num)";;

let id_to_string_def = cake_define
  `(id_to_string (Short s) = s) /\
   (id_to_string (Long x id') =
     concat [x; implode "."; id_to_string id'])`;;

let get_tyname_def = cake_define
  `get_tyname n (Bind [] []) = NONE /\
   get_tyname n (Bind [] ((m,ys) :: xs)) =
     (match get_tyname n ys with NONE -> get_tyname n (Bind [] xs) |
       SOME x -> SOME (^ (^ m (implode ".")) x)) /\
   get_tyname n (Bind ((tyname,_1,t) :: xs) m) =
     (if (match t with Tapp _2 m -> m = n | _3 -> F) then
       SOME tyname else get_tyname n (Bind xs m))`;;

let type_ident_to_string_def = cake_define
  `type_ident_to_string tys ti =
   (if ti = Tarray_num then
     (implode "Array.array") else if ti = Tbool_num then
     (implode "bool") else if ti = Tchar_num then
     (implode "char") else if ti = Texn_num then
     (implode "exn") else if ti = Tint_num then
     (implode "int") else if ti = Tlist_num then
     (implode "list") else if ti = Tref_num then
     (implode "ref") else if ti = Tstring_num then
     (implode "string") else if ti = Tvector_num then
     (implode "Vector.vector") else if ti = Tword64_num then
     (implode "Word64.word") else if ti = Tword8_num then
     (implode "Word8.word") else if ti = Tword8array_num then
     (implode "byte_array") else if ti = Tdouble_num then
     (implode "Double.double") else
     match get_tyname ti tys with NONE -> mlint_toString (&ti) |
       SOME s -> s)`;;

let ty_var_name_def = cake_define
  `ty_var_name n =
     (if n < 28 then implode ("'" ++ [CHR (n + ORD (CHR 97))]) else
                    concat [implode "'"; mlint_toString (&n)])`;;

let commas_def = cake_define
  `infer_t_commas c x2 =
      match x2 with
        [] -> []
      | [x] -> [x]
      | (x :: ys) -> x :: c :: infer_t_commas c ys`;;
hol4_overload "commas" "infer_t_commas";;

let add_parens_def = cake_define
  `add_parens threshold' (x,n) =
     (if threshold' < (n:num) then concat [(implode "("); x;
       (implode ")")] else x)`;;

let _ = size_thms "infer_t";;
let _ = size_thms "list";;
(* HOL4 termination: *)
let inf_type_to_string_rec_def = cake_define_wf
  `MEASURE (\x. match x with INL (_10,t) -> infer_t_size t | INR
  (_11,ts) -> list_size infer_t_size ts)`
  `(inf_type_to_string_rec tys (Infer_Tuvar n) =
     (concat [(implode "_"); mlint_toString (&n)],0)) /\
   (inf_type_to_string_rec tys (Infer_Tvar_db n) =
     (concat [ty_var_name n],0)) /\
   (inf_type_to_string_rec tys (Infer_Tapp ts ti) =
     (if ti = Tfn_num then
      (match ts with [t1; t2] ->
         (concat [add_parens 2 (inf_type_to_string_rec tys t1);
           (implode " -> ");
                  add_parens 3 (inf_type_to_string_rec tys t2)],3) |
                    _7 -> (implode "<bad function type>",0)) else if ti
                    = Ttup_num then
      (match ts with [] -> ((implode "unit"),0) | [t] ->
        inf_type_to_string_rec tys t | _8 -> (concat (commas (implode
        " * ")
                (MAP (add_parens 1) (inf_type_to_string_rec_list tys
                  ts))),2)) else
       match ts with [] -> (type_ident_to_string tys ti,0) | [t] ->
         (concat [add_parens 1 (inf_type_to_string_rec tys t);
           (implode " ");
                  type_ident_to_string tys ti],1) | _9 ->
         (concat ([(implode "(")] ++
                  commas (implode ", ")
                    (MAP (add_parens 5) (inf_type_to_string_rec_list
                      tys ts)) ++
                  [(implode ") "); type_ident_to_string tys ti]),1)))
                    /\
   inf_type_to_string_rec_list tys [] = [] /\
   inf_type_to_string_rec_list tys (t :: ts) =
     inf_type_to_string_rec tys t ::
     inf_type_to_string_rec_list tys ts`;;

let inf_type_to_string_def = cake_define
  `inf_type_to_string tys t = FST (inf_type_to_string_rec tys t)`;;
