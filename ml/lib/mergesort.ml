(* ======================================================== *)
(*  mergesort: ported from HOL4's
    src/sort/mergesortScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by clos_knownProof.ml,
    clos_knownProps.ml, mllist.ml and regexp_compiler.ml.  *)
(* ======================================================== *)

needs "lib/sorting.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: pred_set arithmetic list
   rich_list option pair relation *)

let sort2_def = new_definition
  `sort2 R x y =
     (if R x y then
       [x; y] else
       [y; x])`;;

let sort3_def = new_definition
  `sort3 R x y z =
     (if R x y then
       if R y z then
         [x; y; z] else if R x z then
         [x; z; y] else
         [z; x; y] else if R y z then
       if R x z then
         [y; x; z] else
         [y; z; x] else
       [z; y; x])`;;

let merge_def,merge_ind = define_guess
  [`mergesort_merge R l x3 =
        match (l,x3) with
          ([],[]) -> []
        | (l,[]) -> l
        | ([],l) -> l
        | ((x :: l1),(y :: l2)) ->
       (if R x y then
         x :: mergesort_merge R l1 (y :: l2) else
         y :: mergesort_merge R (x :: l1) l2)`];;
hol4_overload "merge" "mergesort_merge";;

let mergesortN_def,mergesortN_ind = define_wf
  `MEASURE (\(R,n,l). n)`
  [`mergesortN R n l =
     if n = 0 then [] else
     if n = 1 then (match l with [] -> [] | x :: l -> [x]) else
     if n = 2 then
       (match l with
          [] -> []
        | [x] -> [x]
        | x :: y :: l -> sort2 R x y) else
     if n = 3 then
       (match l with
          [] -> []
        | [x] -> [x]
        | [x; y] -> sort2 R x y
        | x :: y :: z :: l -> sort3 R x y z) else
     let len1 = DIV2 n in
       mergesort_merge R
         (mergesortN R (DIV2 n) l)
         (mergesortN R (n - len1) (DROP len1 l))`];;

let mergesort_def = new_definition
  `mergesort R l = mergesortN R (LENGTH l) l`;;

let sort2_tail_def = new_definition
  `sort2_tail (neg:bool) R x y =
     (if ~(R x y = neg) then
       [x; y] else
       [y; x])`;;

let sort3_tail_def = new_definition
  `sort3_tail (neg:bool) R x y z =
    (if ~(R x y = neg) then
      if ~(R y z = neg) then
        [x; y; z] else if ~(R x z = neg) then
        [x; z; y] else
        [z; x; y] else if ~(R y z = neg) then
      if ~(R x z = neg) then
        [y; x; z] else
        [y; z; x] else
      [z; y; x])`;;

let merge_tail_def,merge_tail_ind = define_guess
  [`merge_tail negate' R l x4 acc =
        match (negate',l,x4) with
          ((negate':bool),[],[]) -> acc
        | (negate',l,[]) -> REV l acc
        | (negate',[],l) -> REV l acc
        | (negate',(x :: l1),(y :: l2)) ->
       (if ~(R x y = negate') then
         merge_tail negate' R l1 (y :: l2) (x :: acc) else
         merge_tail negate' R (x :: l1) l2 (y :: acc))`];;

let mergesortN_tail_def,mergesortN_tail_ind = define_wf
  `MEASURE (\(negate,R,n,l). n)`
  [`mergesortN_tail negate R n l =
     if n = 0 then [] else
     if n = 1 then (match l with [] -> [] | x :: l -> [x]) else
     if n = 2 then
       (match l with
          [] -> []
        | [x] -> [x]
        | x :: y :: l -> sort2_tail negate R x y) else
     if n = 3 then
       (match l with
          [] -> []
        | [x] -> [x]
        | [x; y] -> sort2_tail negate R x y
        | x :: y :: z :: l -> sort3_tail negate R x y z) else
     let len1 = DIV2 n in
     let neg = ~negate in
       merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                        (mergesortN_tail neg R (n - len1)
                                         (DROP len1 l))
                        []`];;

let mergesort_tail_def = new_definition
  `mergesort_tail R l = mergesortN_tail F R (LENGTH l) l`;;
