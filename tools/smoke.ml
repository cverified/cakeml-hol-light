(* ================================================================ *)
(*  A smoke test of the machinery that makes the definitions: the   *)
(*  shapes of the port that used to be assumed, and a handful of    *)
(*  ordinary definitions that have to keep working.  Load it in a   *)
(*  clone of the template:                                          *)
(*                                                                  *)
(*    repl-clone hol-template-cakeml smoke                          *)
(*    repl-step smoke '#use ".../tools/smoke.ml";;'                 *)
(*                                                                  *)
(*  Every line it prints has to say 0 cheats.                       *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
let iprog_INDUCT,iprog_RECURSION = define_datatype
  "iprog = ISkip | IMove (num) | ICall ((num # (num#num) # iprog # \
   num # num) option) (num) ((num) list) ((num # iprog # num # \
   num) option) | ISeq (iprog) (iprog)";;
let g2_def = cake_define
  `ge p =
     match p with
       ISkip -> 0
     | IMove n -> n
     | ICall ret dest args h ->
       (let n = MAX_LIST args in
        match ret with
          NONE -> n
        | SOME (v,cutset,ret_handler,l1,l2) ->
          (let cutset_max = MAX n (FST cutset) in
           let ret_max = MAX (MAX v cutset_max) (ge ret_handler) in
           (match h with
              NONE -> ret_max
            | SOME (v,prog,l1,l2) -> MAX v (MAX ret_max (ge prog)))))
     | ISeq s1 s2 -> MAX (ge s1) (ge s2)`;;
print_string ("SMOKE0 cheats " ^
              string_of_int(length(cake_cheats())) ^ "\n");;

(* ---------------------------------------------------------------- *)
(* a smoke test of the strategies: ordinary definitions that
   the port makes, to see that the change does not break them *)
let s_len_def = cake_define_list
  [`s_len ([]:num list) = 0`;
   `s_len (CONS x xs) = 1 + s_len xs`];;
let s_tree_INDUCT,s_tree_RECURSION = define_datatype
  "s_tree = SLeaf | SNode (s_tree) (num) (s_tree)";;
let s_sum_def = cake_define
  `s_sum t =
     match t with SLeaf -> 0 | SNode l n r -> s_sum l + n + s_sum r`;;
let s_map_def = cake_define
  `s_map f t =
     match t with SLeaf -> SLeaf
     | SNode l n r -> SNode (s_map f l) (f n) (s_map f r)`;;
let s_half_def = cake_define
  `s_half n = if n = 0 then 0 else 1 + s_half (n DIV 2)`;;
let s_opt_def = cake_define
  `s_opt t =
     match t with SLeaf -> NONE
     | SNode l n r ->
       (let a = s_opt l in
        match a with NONE -> SOME n | SOME m -> SOME (m + n))`;;
let s_all_def = cake_define
  `s_all ts =
     match ts with [] -> 0
     | (t :: rest) -> s_sum t + s_all rest`;;
let s_fold_def = cake_define
  `s_fold ts = SUM (MAP s_sum ts)`;;
print_string ("SMOKE cheats " ^ string_of_int(length(cake_cheats())) ^
              " axioms " ^ string_of_int(length(axioms())) ^ "\n");;

(* ---------------------------------------------------------------- *)
(* the shape of reg_alloc's st_ex_list_MIN_cost: the recursive
   calls are under a monadic bind and two lambdas *)
let t_bind_def = cake_define
  `t_bind (x:num) (f:num->'a) = f x`;;
let t_min_def = cake_define_list
  [`t_min scost ([]:num list) d k v acc = (k,acc:num list)`;
   `t_min scost (x :: xs) d k v acc =
      (if x < d then
        t_bind (x + 1) (\
          xv. t_bind (xv + 2) (\
          cost.
          if v > cost then t_min scost xs d x cost (k :: acc) else
            t_min scost xs d k v (x :: acc))) else
        t_min scost xs d k v acc)`];;
print_string ("SMOKE2 cheats " ^ string_of_int(length(cake_cheats()))
              ^ "\n");;

(* ---------------------------------------------------------------- *)
(* the shape of clos_known's get_size_aux: a recursive call on
   the MAP SND of a list of pairs of the family *)
let m_exp_INDUCT,m_exp_RECURSION = define_datatype
  "m_exp = MVar (num) | MLetrec ((num # m_exp) list) (m_exp) | \
   MLet ((m_exp) list) (m_exp)";;
let m_aux_def = cake_define_list_try
  (fun () -> `MEASURE (list_size m_exp_size)`)
  [`m_aux [] = 0`;
   `m_aux (x :: y :: xs) = m_aux [x] + m_aux (y :: xs)`;
   `m_aux [(MVar v:m_exp)] = 1`;
   `m_aux [(MLet xs x2:m_exp)] = 1 + m_aux xs + m_aux [x2]`;
   `m_aux [(MLetrec fns x1:m_exp)] =
      1 + m_aux (MAP SND fns) + m_aux [x1]`];;
print_string ("SMOKE4 cheats " ^ string_of_int(length(cake_cheats()))
              ^ "\n");;

(* ---------------------------------------------------------------- *)
(* the shape of mlint's fromChars: the measure goes down by a
   constant without arguments *)
let p_exp_def = cake_define `p_exp = 8`;;
let p_len_def = cake_define `p_len = p_exp`;;
let p_f_def = cake_define
  `p_f n =
     (if n = 0 then 0 else if n <= p_len then 1
      else 1 + p_f (n - p_len))`;;
(* the shape of linear_scan's sort_regs: the bound of the
   recursive call is what a let binds *)
let q_sort_def = cake_define_wf `MEASURE (\(p1,p2). p2 - p1)`
  `q_sort p1 p2 =
     (if p2 <= p1 + 1 then 0
      else let m = (p1 + p2) DIV 2 in
             q_sort p1 (m - 1) + q_sort m p2)`;;
print_string ("SMOKE5 cheats " ^ string_of_int(length(cake_cheats()))
              ^ "\n");;

(* ---------------------------------------------------------------- *)
(* a family of functions, whose measure is a sum_measure *)
let r_exp_INDUCT,r_exp_RECURSION = define_datatype
  "r_exp = RVar (num) | RApp ((r_exp) list)";;
let r_f_def = cake_define_list
  [`r_f (RVar n) = n`;
   `r_f (RApp es) = r_fs es`;
   `r_fs ([]:r_exp list) = 0`;
   `r_fs (e :: es) = r_f e + r_fs es`];;
print_string ("SMOKE6 cheats " ^ string_of_int(length(cake_cheats()))
              ^ "\n");;

(* ---------------------------------------------------------------- *)
(* the shape of word_to_stack's word_list: the list that a DROP
   gives is shorter *)
let w_list_def = cake_define_wf `MEASURE (\(d,xs). LENGTH xs)`
  `w_list d (xs:num list) =
     (if LENGTH xs <= d \/ d = 0 then [xs]
      else TAKE d xs :: w_list d (DROP d xs))`;;
print_string ("SMOKE7 cheats " ^ string_of_int(length(cake_cheats()))
              ^ "\n");;

(* ---------------------------------------------------------------- *)
(* the shape of bvl_handle's dest_handle_If: a destructor that
   gives a sum in an option *)
let s_bexp_INDUCT,s_bexp_RECURSION = define_datatype
  "s_bexp = SBVar (num) | SBIf (s_bexp) (s_bexp) (s_bexp) | \
   SBRaise (s_bexp)";;
let s_dest_if_def = cake_define
  `s_dest_if x1 =
     match x1 with
       (SBIf y1 y2 y3:s_bexp) ->
         (if y1 = SBVar 0 then SOME (INL (y1,y2,y3))
          else SOME (INR (y1,y2,y3)))
     | _1 -> NONE`;;
let s_simp_def = cake_define
  `s_simp x =
     (match s_dest_if x with
        NONE -> 0
      | SOME (INL (b1,b2,b3)) -> 1 + s_simp b1 + s_simp b2
      | SOME (INR (b1,b2,b3)) -> 2 + s_simp b3)`;;
print_string ("SMOKE8 cheats " ^ string_of_int(length(cake_cheats()))
              ^ "\n");;

print_string ("SMOKEALL cheats " ^
              string_of_int(length(cake_cheats())) ^ " axioms " ^
              string_of_int(length(axioms())) ^ "\n");;
