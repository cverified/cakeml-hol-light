(* ================================================================== *)
(*  A record package for HOL Light, as HOL4's Datatype has one.       *)
(*                                                                    *)
(*    define_record "sem_env"                                         *)
(*      ["v","(A,B,C)namespace"; "c","(A,B,num#stamp)namespace"]      *)
(*                                                                    *)
(*  defines the type with one constructor `mk_sem_env`, the field     *)
(*  accessors `sem_env_v` and `sem_env_c` and the field updates       *)
(*  `sem_env_v_fupd` and `sem_env_c_fupd`. As in HOL4,                *)
(*                                                                    *)
(*    r.v is sem_env_v r                                              *)
(*    r with v := x is sem_env_v_fupd (K x) r                         *)
(*    <|v := x; c := y|> is mk_sem_env x y                            *)
(* ================================================================== *)

let the_records =
  ref ([]:(string * (string * (thm * thm)) list) list);;

let define_record name fields =
  let spec = name ^ " = mk_" ^ name ^
             itlist (fun (_,t) s -> " (" ^ t ^ ")" ^ s) fields "" in
  let _,rth = define_datatype spec in
  let cty = get_const_type ("mk_" ^ name) in
  let argtys,rty = splitlist dest_fun_ty cty in
  let vars = map2 (fun (f,_) ty -> mk_var(f,ty)) fields argtys in
  let con = mk_const("mk_" ^ name,[]) in
  let pat = list_mk_comb(con,vars) in
  let do_field v =
    let fld = fst(dest_var v) in
    let fty = type_of v in
    let acc = mk_var(name ^ "_" ^ fld,mk_fun_ty rty fty) in
    let accth = new_recursive_definition rth
                  (mk_eq(mk_comb(acc,pat),v)) in
    let f = mk_var("f",mk_fun_ty fty fty) in
    let upd = mk_var(name ^ "_" ^ fld ^ "_fupd",
                     mk_fun_ty (type_of f) (mk_fun_ty rty rty)) in
    let vars' = map (fun w -> if w = v then mk_comb(f,w) else w) vars in
    let updth = new_recursive_definition rth
                  (mk_eq(mk_comb(mk_comb(upd,f),pat),
                         list_mk_comb(con,vars'))) in
    fld,(accth,updth) in
  let l = map do_field vars in
  the_records := (name,l)::(!the_records);
  rth,map (fun (_,(a,u)) -> a,u) l;;

(* the accessor and update theorems of a record field *)

let record_accessor name fld =
  fst(assoc fld (assoc name (!the_records)));;

let record_update name fld =
  snd(assoc fld (assoc name (!the_records)));;

(* all accessor and update theorems, for rewriting *)

let record_thms name =
  itlist (fun (_,(a,u)) l -> a::u::l) (assoc name (!the_records)) [];;
