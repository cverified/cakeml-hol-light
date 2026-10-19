(* ======================================================== *)
(*  infer_t: ported from HOL4's
    compiler/inference/infer_tScript.sml
    A definition theory, with 8 definitions, 1 datatype and 1
    theorem.  Needed by 9 files of the port.  *)
(* ======================================================== *)

(*
  The infer_t datatype and various to_string functions.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "lib/regexp_compiler.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

let infer_t_INDUCT,infer_t_RECURSION = define_datatype
  "infer_t = Infer_Tvar_db (num) | Infer_Tapp (infer_t list) (num) | \
   Infer_Tuvar (num)";;

(* HOL4 infer_tScript.sml:19-20: a theorem that HOL4 states as the
   value of an ML expression: infer_t_ind *)

let id_to_string_def = cake_define_list
  [`id_to_string (Short s) = s`;
   `id_to_string (Long x id') =
        mlstring_concat [x; implode "."; id_to_string id']`];;

(* HOL4 infer_tScript.sml: the case constant that its Datatype
   makes *)

let infer_t_CASE = new_recursive_definition infer_t_RECURSION
  `(infer_t_CASE (Infer_Tvar_db n) dbf appf uvf = dbf n) /\
   (infer_t_CASE (Infer_Tapp its n) dbf appf uvf = appf its n) /\
   (infer_t_CASE (Infer_Tuvar n) dbf appf uvf = uvf n)`;;

let get_tyname_def = cake_define_list
  [`get_tyname n (Bind [] []) = NONE`;
   `get_tyname n (Bind [] ((m,ys) :: xs)) =
      (match get_tyname n ys with NONE -> get_tyname n (Bind []
        xs) | SOME x -> SOME ((\x y. strcat x y) ((\x y. strcat x y)
        m (implode ".")) x))`;
   `get_tyname n (Bind ((tyname,_1,t) :: xs) m) =
      (if (match t with Tapp _2 m -> m = n | _3 -> F) then
        SOME tyname else get_tyname n (Bind xs m))`];;

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
                    mlstring_concat [implode "'"; mlint_toString
                      (&n)])`;;

let commas_def = cake_define
  `infer_t_commas c x2 =
      match x2 with
        [] -> []
      | [x] -> [x]
      | (x :: ys) -> x :: c :: infer_t_commas c ys`;;
hol4_overload "commas" "infer_t_commas";;

let add_parens_def = cake_define
  `add_parens threshold' (x,n) =
     (if threshold' < (n:num) then mlstring_concat [(implode "(");
       x; (implode ")")] else x)`;;

let _ = size_thms "infer_t";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let inf_type_to_string_rec_def = cake_define_list_try (fun () ->
  `MEASURE (\x. match x with INL (_7,t) -> infer_t_size t | INR (_8,ts)
     -> list_size infer_t_size ts)`)
  [`inf_type_to_string_rec tys (Infer_Tuvar n) =
        (mlstring_concat [(implode "_"); mlint_toString (&n)],0)`;
   `inf_type_to_string_rec tys (Infer_Tvar_db n) =
        (mlstring_concat [ty_var_name n],0)`;
   `inf_type_to_string_rec tys (Infer_Tapp ts ti) =
        (if ti = Tfn_num then
         (match ts with [t1; t2] ->
            (mlstring_concat [add_parens 2 (inf_type_to_string_rec
              tys t1); (implode " -> ");
                     add_parens 3 (inf_type_to_string_rec tys
                       t2)],3) | _4 -> (implode
                       "<bad function type>",0)) else if ti = Ttup_num
                       then
         (match ts with [] -> ((implode "unit"),0) | [t] ->
           inf_type_to_string_rec tys t | _5 -> (mlstring_concat
           (infer_t_commas (implode " * ")
                   (MAP (add_parens 1) (inf_type_to_string_rec_list
                     tys ts))),2)) else
          match ts with [] -> (type_ident_to_string tys ti,0) | [t]
            ->
            (mlstring_concat [add_parens 1 (inf_type_to_string_rec
              tys t); (implode " ");
                     type_ident_to_string tys ti],1) | _6 ->
            (mlstring_concat ([(implode "(")] ++
                     infer_t_commas (implode ", ")
                       (MAP (add_parens 5)
                         (inf_type_to_string_rec_list tys ts)) ++
                     [(implode ") "); type_ident_to_string tys
                       ti]),1))`;
   `inf_type_to_string_rec_list tys [] = []`;
   `inf_type_to_string_rec_list tys (t :: ts) =
      inf_type_to_string_rec tys t ::
      inf_type_to_string_rec_list tys ts`];;

let inf_type_to_string_def = cake_define
  `inf_type_to_string tys t = FST (inf_type_to_string_rec tys t)`;;
