(* ======================================================== *)
(*  mc_multiword: ported from HOL4's
    examples/machine-code/multiword/mc_multiwordScript.sml
    A HOL4 library theory, of which the port has the definitions
    that CakeML needs.  Needed by data_to_word_bignumProof.ml,
    word_bignum.ml and word_bignumProof.ml.  *)
(* ======================================================== *)

needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
(* HOL4 ancestors outside the port: words address arithmetic list
   address pair rich_list integer *)

needs "lib/mc_tailrec.ml";;

let mc_cmp_def,mc_cmp_pre_def =
  tailrec_define "mc_cmp"
  `(\(l,r10,xs,ys).
     if r10 = (n2w 0x0) then (INR (l,r10,xs,ys),T) else
       (let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH xs) in
        let r8 = EL (w2n r10) xs in
        let cond' = (cond' /\ w2n r10 < LENGTH ys) in
        let r9 = EL (w2n r10) ys in
          if r8 = r9 then (INL (l - 1,r10,xs,ys),(cond' /\ ~(l =
            0))) else if r8 <+ r9 then (let r10 = (n2w 0x1) in (INR
            (l,r10,xs,ys),cond')) else (let r10 = (n2w 0x2) in (INR
            (l,r10,xs,ys),cond')))):num#'a word#('a word) list#('a
            word) list->(num#'a word#('a word) list#('a word)
            list+num#'a word#('a word) list#('a word) list)#bool`;;

let mc_compare_def,mc_compare_pre_def =
  tailrec_define "mc_compare"
  `(\(l,r10,r11,xs,ys).
     if r10 <+ r11 then (let r10 = (n2w 0x1) in (INR
       (l,r10,xs,ys),T)) else if r11 <+ r10 then (let r10 = (n2w 0x2) in
       (INR (l,r10,xs,ys),T)) else
       (let cond' = (mc_cmp_pre (l - 1,r10,xs,ys) /\ ~(l = 0)) in
        let (l,r10,xs,ys) = mc_cmp (l - 1,r10,xs,ys) in
          (INR (l,r10,xs,ys),cond'))):num#'a word#'a word#('a
            word) list#('a word) list->(num#'a word#'a word#('a word)
            list#('a word) list+num#'a word#('a word) list#('a word)
            list)#bool`;;

let mc_header_def = cake_define
  `mc_header (s,(xs:('a word) list)) = n2w (LENGTH xs * 2) + (if s
  then (n2w 1) else (n2w 0):'a word)`;;

let mc_icompare_def,mc_icompare_pre_def =
  tailrec_define "mc_icompare"
  `(\(l,r10,r11,xs,ys).
     if r10 && (n2w 0x1) = (n2w 0x0) then
       if r11 && (n2w 0x1) = (n2w 0x0) then
         (let r10 = r10 >>> 1 in
          let r11 = r11 >>> 1 in
          let cond' = mc_compare_pre (l,r10,r11,xs,ys) in
          let (l,r10,xs,ys) = mc_compare (l,r10,r11,xs,ys) in
            (INR (l,r10,xs,ys),cond')) else (let r10 = (n2w 0x2) in
              (INR (l,r10,xs,ys),T)) else if r11 && (n2w 0x1) = (n2w
              0x0) then
       (let r10 = (n2w 0x1) in (INR (l,r10,xs,ys),T)) else
       (let r10 = r10 >>> 1 in
        let r11 = r11 >>> 1 in
        let cond' = mc_compare_pre (l,r10,r11,xs,ys) in
        let (l,r10,xs,ys) = mc_compare (l,r10,r11,xs,ys) in
          if r10 = (n2w 0x0) then (INR (l,r10,xs,ys),cond') else
            (let r10 = r10 ?? (n2w 0x3) in (INR
            (l,r10,xs,ys),cond')))):num#'a word#'a word#('a word)
            list#('a word) list->(num#'a word#'a word#('a word)
            list#('a word) list+num#'a word#('a word) list#('a word)
            list)#bool`;;

let single_add_word_def = cake_define
  `single_add_word w1 w2 c =
     (let (z,c) = single_add w1 w2 (~(c = ((n2w 0):'a word))) in
       ((z:'a word),((b2w c):'a word)))`;;

let mc_add_loop2_def,mc_add_loop2_pre_def =
  tailrec_define "mc_add_loop2"
  `(\(l,(r1:'a word),(r3:'a word),(r8:'a word),(r9:'a word),(r10:'a
  word),xs,zs).
     if r1 = (n2w 0x1) then
       (let r1 = (n2w 0x0) in
          (INR (l,(r1:'a word),r3,r8,r9,r10,xs,zs),T)) else
       (let r1 = r1 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH xs) in
        let r8 = EL (w2n r10) xs in
        let cond' = (cond' /\ (~(r3 = (n2w 0)) ==> (r3 = (n2w 1))))
          in
        let (r8,r3) = single_add_word r8 r9 r3 in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r8 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INL (l - 1,r1,r3,r8,r9,r10,xs,zs),(cond' /\ ~(l =
            0)))))`;;

let mc_add_loop1_def,mc_add_loop1_pre_def =
  tailrec_define "mc_add_loop1"
  `(\(l,(r1:'a word),(r3:'a word),(r8:'a word),(r9:'a word),(r10:'a
  word),xs,ys,zs).
     if r1 = (n2w 0x1) then
       (let r1 = ((n2w 0x0):'a word) in
          (INR (l,r1,r3,r8,r9,r10,xs,ys,zs),T)) else
       (let r1 = r1 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH xs) in
        let r8 = EL (w2n r10) xs in
        let cond' = (cond' /\ w2n r10 < LENGTH ys) in
        let r9 = EL (w2n r10) ys in
        let cond' = (cond' /\ (~(r3 = (n2w 0)) ==> (r3 = (n2w 1))))
          in
        let (r8,r3) = single_add_word r8 r9 r3 in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r8 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INL (l - 1,r1,r3,r8,r9,r10,xs,ys,zs),(cond' /\ ~(l =
            0)))))`;;

let mc_add_loop_def,mc_add_loop_pre_def =
  tailrec_define "mc_add_loop"
  `(\(l,r1,r2,r8,r9,r10,xs,ys,zs).
     (let r1 = r1 + (n2w 0x1) in
      let r2 = r2 + (n2w 0x1) in
      let r3 = (n2w 0) in
      let cond' = (mc_add_loop1_pre (l - 1,r1,r3,r8,r9,r10,xs,ys,zs)
        /\ ~(l = 0)) in
      let (l,r1,r3,r8,r9,r10,xs,ys,zs) = mc_add_loop1 (l -
        1,r1,r3,r8,r9,r10,xs,ys,zs) in
      let r1 = r2 in
      let r9 = (n2w 0x0) in
      let cond' = (cond' /\ mc_add_loop2_pre (l -
        1,r1,r3,r8,r9,r10,xs,zs) /\ ~(l = 0)) in
      let (l,r1,r3,r8,r9,r10,xs,zs) = mc_add_loop2 (l -
        1,r1,r3,r8,r9,r10,xs,zs) in
        if r3 = (n2w 0) then
          (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond') else
          (let r8 = (n2w 0x1) in
           let cond' = (cond' /\ w2n r10 < LENGTH zs) in
           let zs = LUPDATE r8 (w2n r10) zs in
           let r10 = r10 + (n2w 0x1) in
             (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond')))):num#'a
               word#'a word#'a word#'a word#'a word#('a word)
               list#('a word) list#('a word) list->(num#'a word#'a
               word#'a word#'a word#'a word#('a word) list#('a word)
               list#('a word) list+num#'a word#'a word#'a word#'a
               word#'a word#('a word) list#('a word) list#('a word)
               list)#bool`;;

let mc_add_def,mc_add_pre_def =
  tailrec_define "mc_add"
  `(\(l,r1,r2,r8,r9,r10,xs,ys,zs).
     (let r2 = r2 - r1 in
      let cond' = mc_add_loop_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
      let (l,r1,r2,r8,r9,r10,xs,ys,zs) =
            mc_add_loop (l,r1,r2,r8,r9,r10,xs,ys,zs) in
        (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond'))):num#'a word#'a
          word#'a word#'a word#'a word#('a word) list#('a word)
          list#('a word) list->(num#'a word#'a word#'a word#'a
          word#'a word#('a word) list#('a word) list#('a word)
          list+num#'a word#'a word#'a word#'a word#'a word#('a word)
          list#('a word) list#('a word) list)#bool`;;

let single_sub_word_def = cake_define
  `single_sub_word w1 w2 c =
     (let (z,c) = single_sub w1 w2 (~(c = ((n2w 0):'a word))) in
       ((z:'a word),((b2w c):'a word)))`;;

let mc_sub_loop2_def,mc_sub_loop2_pre_def =
  tailrec_define "mc_sub_loop2"
  `(\(l,(r1:'a word),(r3:'a word),(r8:'a word),(r9:'a word),(r10:'a
  word),xs,zs).
     if r1 = (n2w 0x1) then
       (let r1 = ((n2w 0x0):'a word) in
          (INR (l,r1,r3,r8,r9,r10,xs,zs),T)) else
       (let r1 = r1 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH xs) in
        let r8 = EL (w2n r10) xs in
        let cond' = (cond' /\ (~(r3 = (n2w 0)) ==> (r3 = (n2w 1))))
          in
        let (r8,r3) = single_sub_word r8 r9 r3 in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r8 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INL (l - 1,r1,r3,r8,r9,r10,xs,zs),(cond' /\ ~(l =
            0)))))`;;

let mc_sub_loop1_def,mc_sub_loop1_pre_def =
  tailrec_define "mc_sub_loop1"
  `(\(l,(r1:'a word),(r3:'a word),(r8:'a word),(r9:'a word),(r10:'a
  word),xs,ys,zs).
     if r1 = (n2w 0x1) then
       (let r1 = ((n2w 0x0):'a word) in
          (INR (l,r1,r3,r8,r9,r10,xs,ys,zs),T)) else
       (let r1 = r1 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH xs) in
        let r8 = EL (w2n r10) xs in
        let cond' = (cond' /\ w2n r10 < LENGTH ys) in
        let r9 = EL (w2n r10) ys in
        let cond' = (cond' /\ (~(r3 = (n2w 0)) ==> (r3 = (n2w 1))))
          in
        let (r8,r3) = single_sub_word r8 r9 r3 in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r8 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INL (l - 1,r1,r3,r8,r9,r10,xs,ys,zs),(cond' /\ ~(l =
            0)))))`;;

let mc_sub_loop_def,mc_sub_loop_pre_def =
  tailrec_define "mc_sub_loop"
  `(\(l,r1,r2,r8,r9,r10,xs,ys,zs).
     (let r1 = r1 + (n2w 0x1) in
      let r2 = r2 + (n2w 0x1) in
      let r3 = (n2w 1) in
      let r8 = r8 - (n2w 0x0) in
      let cond' = (mc_sub_loop1_pre (l - 1,r1,r3,r8,r9,r10,xs,ys,zs)
        /\ ~(l = 0)) in
      let (l,r1,r3,r8,r9,r10,xs,ys,zs) = mc_sub_loop1 (l -
        1,r1,r3,r8,r9,r10,xs,ys,zs) in
      let r1 = r2 in
      let r9 = (n2w 0x0) in
      let cond' = (cond' /\ mc_sub_loop2_pre (l -
        1,r1,r3,r8,r9,r10,xs,zs) /\ ~(l = 0)) in
      let (l,r1,r3,r8,r9,r10,xs,zs) = mc_sub_loop2 (l -
        1,r1,r3,r8,r9,r10,xs,zs) in
        (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond'))):num#'a word#'a
          word#'a word#'a word#'a word#('a word) list#('a word)
          list#('a word) list->(num#'a word#'a word#'a word#'a
          word#'a word#('a word) list#('a word) list#('a word)
          list+num#'a word#'a word#'a word#'a word#'a word#('a word)
          list#('a word) list#('a word) list)#bool`;;

let mc_fix_def,mc_fix_pre_def =
  tailrec_define "mc_fix"
  `(\((l:num),(r8:'a word),(r10:'a word),(zs:('a word) list)).
     if r10 = (n2w 0x0) then (INR (l,r8,r10,zs),T) else
       (let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH zs) in
        let r8 = EL (w2n r10) zs in
          if r8 = (n2w 0x0) then (INL (l - 1,r8,r10,zs),(cond' /\
            ~(l = 0))) else (let r10 = r10 + (n2w 0x1) in (INR
            (l,r8,r10,zs),cond'))))`;;

let mc_sub_def,mc_sub_pre_def =
  tailrec_define "mc_sub"
  `(\(l,r1,r2,r8,r9,r10,xs,ys,zs).
     (let r2 = r2 - r1 in
      let cond' = mc_sub_loop_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
      let (l,r1,r2,r8,r9,r10,xs,ys,zs) = mc_sub_loop
        (l,r1,r2,r8,r9,r10,xs,ys,zs) in
      let cond' = (cond' /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l = 0))
        in
      let (l,r8,r10,zs) = mc_fix (l - 1,r8,r10,zs) in
        (INR (l,r1,r2,r8,r9,r10,xs,ys,zs),cond'))):num#'a word#'a
          word#'a word#'a word#'a word#('a word) list#('a word)
          list#('a word) list->(num#'a word#'a word#'a word#'a
          word#'a word#('a word) list#('a word) list#('a word)
          list+num#'a word#'a word#'a word#'a word#'a word#('a word)
          list#('a word) list#('a word) list)#bool`;;

let mc_iadd1_def,mc_iadd1_pre_def =
  tailrec_define "mc_iadd1"
  `(\(r1,r2,xs,ys).
     (let r0 = (n2w 0x0) in
        if r1 <+ r2 then
          (let (xs,ys) = (ys,xs) in
           let r0 = (n2w 0x1) in
             (INR (r1,r2,r0,xs,ys),T)) else
          (let r8 = r1 in
           let r1 = r2 in
           let r2 = r8 in
             (INR (r1,r2,r0,xs,ys),T)))):'a word#'a word#('a word)
               list#('a word) list->('a word#'a word#('a word)
               list#('a word) list+'a word#'a word#'a word#('a word)
               list#('a word) list)#bool`;;

let mc_iadd2_def,mc_iadd2_pre_def =
  tailrec_define "mc_iadd2"
  `(\(r1,r2,r10,r12,xs,ys).
     (let r0 = (n2w 0x0) in
        if r10 = (n2w 0x1) then
          (let (xs,ys) = (ys,xs) in
           let r12 = r12 ?? (n2w 0x1) in
           let r0 = (n2w 0x1) in
             (INR (r1,r2,r0,r12,xs,ys),T)) else
          (let r8 = r1 in
           let r1 = r2 in
           let r2 = r8 in
             (INR (r1,r2,r0,r12,xs,ys),T)))):'a word#'a word#'a
               word#'a word#('a word) list#('a word) list->('a
               word#'a word#'a word#'a word#('a word) list#('a word)
               list+'a word#'a word#'a word#'a word#('a word)
               list#('a word) list)#bool`;;

let mc_iadd3_def,mc_iadd3_pre_def =
  tailrec_define "mc_iadd3"
  `(\(r0,xs,ys).
     if r0 = (n2w 0x0) then (INR (xs,ys),T) else (let (xs,ys) =
       (ys,xs) in (INR (xs,ys),T))):'a word#('a word) list#('a word)
       list->('a word#('a word) list#('a word) list+('a word)
       list#('a word) list)#bool`;;

let mc_iadd_def,mc_iadd_pre_def =
  tailrec_define "mc_iadd"
  `(\(l,r1,r2,xs,ys,zs).
     (let r10 = r1 in
      let r10 = r10 && (n2w 0x1) in
      let r11 = r2 in
      let r11 = r11 && (n2w 0x1) in
        if r10 = r11 then
          (let r1 = r1 >>> 1 in
           let r2 = r2 >>> 1 in
           let (r1,r2,r0,xs,ys) = mc_iadd1 (r1,r2,xs,ys) in
           let r8 = (n2w 0x0) in
           let r9 = r8 in
           let r10 = r8 in
           let cond' = mc_add_pre (l,r1,r2,r8,r9,r10,xs,ys,zs) in
           let (l,r1,r2,r8,r9,r10,xs,ys,zs) =
                 mc_add (l,r1,r2,r8,r9,r10,xs,ys,zs) in
           let (xs,ys) = mc_iadd3 (r0,xs,ys) in
           let r10 = r10 << 1 in
           let r10 = r10 + r11 in
             (INR (l,r10,xs,ys,zs),cond')) else
          (let r12 = r10 in
           let r10 = r1 in
           let r10 = r10 >>> 1 in
           let r11 = r2 in
           let r11 = r11 >>> 1 in
           let cond' = mc_compare_pre (l,r10,r11,xs,ys) in
           let (l,r10,xs,ys) = mc_compare (l,r10,r11,xs,ys) in
             if r10 = (n2w 0x0) then (INR (l,r10,xs,ys,zs),cond')
               else
               (let (r1,r2,r0,r12,xs,ys) =
                      mc_iadd2 (r1,r2,r10,r12,xs,ys) in
                let r8 = (n2w 0x0) in
                let r9 = r8 in
                let r10 = r8 in
                let r1 = r1 >>> 1 in
                let r2 = r2 >>> 1 in
                let cond' = (cond' /\ mc_sub_pre
                  (l,r1,r2,r8,r9,r10,xs,ys,zs)) in
                let (l,r1,r2,r8,r9,r10,xs,ys,zs) =
                      mc_sub (l,r1,r2,r8,r9,r10,xs,ys,zs) in
                let (xs,ys) = mc_iadd3 (r0,xs,ys) in
                let r10 = r10 << 1 in
                let r10 = r10 + r12 in
                  (INR (l,r10,xs,ys,zs),cond'))))):num#'a word#'a
                    word#('a word) list#('a word) list#('a word)
                    list->(num#'a word#'a word#('a word) list#('a
                    word) list#('a word) list+num#'a word#('a word)
                    list#('a word) list#('a word) list)#bool`;;

let mc_single_mul_add_def,mc_single_mul_add_pre_def =
  tailrec_define "mc_single_mul_add"
  `(\(r0,r1,r2,r3).
     (let cond' = T in
      let (r0,r2) = single_mul r0 r2 (n2w 0) in
      let (r0,r4) = single_add_word r0 r1 (n2w 0) in
      let (r2,r4) = single_add_word r2 (n2w 0) r4 in
      let (r0,r4) = single_add_word r0 r3 (n2w 0) in
      let (r2,r4) = single_add_word r2 (n2w 0) r4 in
        (INR (r0,r1,r2,r3),cond'))):'a word#'a word#'a word#'a
          word->('a word#'a word#'a word#'a word+'a word#'a word#'a
          word#'a word)#bool`;;

let mc_mul_pass_def,mc_mul_pass_pre_def =
  tailrec_define "mc_mul_pass"
  `(\(l,r1,r8,r9,r10,r11,ys,zs).
     if r9 = r11 then
       (let cond' = (w2n r10 < LENGTH zs) in
        let zs = LUPDATE r1 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INR (l,r1,r9,r10,ys,zs),cond')) else
       (let cond' = (w2n r10 < LENGTH zs) in
        let r3 = EL (w2n r10) zs in
        let cond' = (cond' /\ w2n r11 < LENGTH ys) in
        let r2 = EL (w2n r11) ys in
        let r0 = r8 in
        let cond' = (cond' /\ mc_single_mul_add_pre (r0,r1,r2,r3)) in
        let (r0,r1,r2,r3) = mc_single_mul_add (r0,r1,r2,r3) in
        let zs = LUPDATE r0 (w2n r10) zs in
        let r1 = r2 in
        let r10 = r10 + (n2w 0x1) in
        let r11 = r11 + (n2w 0x1) in
          (INL (l - 1,r1,r8,r9,r10,r11,ys,zs),(cond' /\ ~(l =
            0))))):num#'a word#'a word#'a word#'a word#'a word#('a
            word) list#('a word) list->(num#'a word#'a word#'a
            word#'a word#'a word#('a word) list#('a word) list+num#'a
            word#'a word#'a word#('a word) list#('a word) list)#bool`;;

let mc_mul_def,mc_mul_pre_def =
  tailrec_define "mc_mul"
  `(\(l,r7,r9,r10,r12,xs,ys,zs).
     if r7 = (n2w 0x0) then (let r10 = r10 + r9 in (INR
       (l,r10,xs,ys,zs),T)) else
       (let r7 = r7 - (n2w 0x1) in
        let cond' = (w2n r12 < LENGTH xs) in
        let r8 = EL (w2n r12) xs in
        let r12 = r12 + (n2w 0x1) in
        let r11 = (n2w 0x0) in
        let r1 = r11 in
        let cond' = (cond' /\ mc_mul_pass_pre (l -
          1,r1,r8,r9,r10,r11,ys,zs) /\ ~(l = 0)) in
        let (l,r1,r9,r10,ys,zs) = mc_mul_pass (l -
          1,r1,r8,r9,r10,r11,ys,zs) in
        let r10 = r10 - r9 in
          (INL (l - 1,r7,r9,r10,r12,xs,ys,zs),(cond' /\ ~(l =
            0))))):num#'a word#'a word#'a word#'a word#('a word)
            list#('a word) list#('a word) list->(num#'a word#'a
            word#'a word#'a word#('a word) list#('a word) list#('a
            word) list+num#'a word#('a word) list#('a word) list#('a
            word) list)#bool`;;

let mc_mul_zero_def,mc_mul_zero_pre_def =
  tailrec_define "mc_mul_zero"
  `(\((l:num),(r0:'a word),(r10:'a word),(zs:('a word) list)).
     if r10 = (n2w 0x0) then (INR (l,r10,zs),T) else
       (let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH zs) in
        let zs = LUPDATE r0 (w2n r10) zs in
          (INL (l - 1,r0,r10,zs),(cond' /\ ~(l = 0)))))`;;

let mc_imul1_def,mc_imul1_pre_def =
  tailrec_define "mc_imul1"
  `(\((r10:'a word),(r11:'a word)).
     if r10 = r11 then let r13 = ((n2w 0):'a word) in (INR
       (r10,r11,r13),T) else let r13 = ((n2w 1):'a word) in (INR
       (r10,r11,r13),T)):'a word#'a word->('a word#'a word+'a word#'a
       word#'a word)#bool`;;

let mc_imul_def,mc_imul_pre_def =
  tailrec_define "mc_imul"
  `(\(l,r1,r2,xs,ys,zs).
     (let r10 = (n2w 0x0) in
        if r1 = (n2w 0x0) then (INR (l,r10,xs,ys,zs),T) else if r2 =
          (n2w 0x0) then (INR (l,r10,xs,ys,zs),T) else
          (let r0 = (n2w 0x0) in
           let r10 = r2 in
           let r10 = r10 >>> 1 in
           let cond' = (mc_mul_zero_pre (l - 1,r0,r10,zs) /\ ~(l =
             0)) in
           let (l,r10,zs) = mc_mul_zero (l - 1,r0,r10,zs) in
           let r10 = r1 in
           let r10 = r10 && (n2w 0x1) in
           let r11 = r2 in
           let r11 = r11 && (n2w 0x1) in
           let (r10,r11,r13) = mc_imul1 (r10,r11) in
           let r7 = r1 in
           let r7 = r7 >>> 1 in
           let r9 = r2 in
           let r9 = r9 >>> 1 in
           let r10 = (n2w 0x0) in
           let r12 = (n2w 0x0) in
           let cond' = (cond' /\ mc_mul_pre (l -
             1,r7,r9,r10,r12,xs,ys,zs) /\ ~(l = 0)) in
           let (l,r10,xs,ys,zs) = mc_mul (l -
             1,r7,r9,r10,r12,xs,ys,zs) in
           let r8 = (n2w 0x0) in
           let cond' = (cond' /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l
             = 0)) in
           let (l,r8,r10,zs) = mc_fix (l - 1,r8,r10,zs) in
           let r10 = r10 << 1 in
           let r10 = r10 + r13 in
             (INR (l,r10,xs,ys,zs),cond')))):num#'a word#'a
               word#('a word) list#('a word) list#('a word)
               list->(num#'a word#'a word#('a word) list#('a word)
               list#('a word) list+num#'a word#('a word) list#('a
               word) list#('a word) list)#bool`;;

let single_div_pre_def = cake_define
  `single_div_pre r2 r0 r9 <=> ~(r9 = ((n2w 0x0):'a word)) /\
     (w2n r2 * dimword (:'a) + w2n r0) DIV w2n r9 < dimword (:'a)`;;

let mc_single_div_def,mc_single_div_pre_def =
  tailrec_define "mc_single_div"
  `(\(r0,r2,r9).
     (let cond' = single_div_pre r2 r0 r9 in
      let (r0,r2) = single_div r2 r0 r9 in
        (INR (r0,r2,r9),cond'))):'a word#'a word#'a word->('a
          word#'a word#'a word+'a word#'a word#'a word)#bool`;;

let mc_simple_div_def,mc_simple_div_pre_def =
  tailrec_define "mc_simple_div"
  `(\(l,r2,r9,r10,xs,zs).
     if r10 = (n2w 0x0) then (INR (l,r2,r9,r10,xs,zs),T) else
       (let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH xs) in
        let r0 = EL (w2n r10) xs in
        let cond' = (cond' /\ mc_single_div_pre (r0,r2,r9)) in
        let (r0,r2,r9) = mc_single_div (r0,r2,r9) in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r0 (w2n r10) zs in
          (INL (l - 1,r2,r9,r10,xs,zs),(cond' /\ ~(l =
            0))))):num#'a word#'a word#'a word#('a word) list#('a
            word) list->(num#'a word#'a word#'a word#('a word)
            list#('a word) list+num#'a word#'a word#'a word#('a word)
            list#('a word) list)#bool`;;

let mc_simple_div1_def,mc_simple_div1_pre_def =
  tailrec_define "mc_simple_div1"
  `(\(l,r2,r9,r10,zs).
     if r10 = (n2w 0x0) then (INR (l,r2,r9,r10,zs),T) else
       (let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH zs) in
        let r0 = EL (w2n r10) zs in
        let cond' = (cond' /\ mc_single_div_pre (r0,r2,r9)) in
        let (r0,r2,r9) = mc_single_div (r0,r2,r9) in
        let zs = LUPDATE r0 (w2n r10) zs in
          (INL (l - 1,r2,r9,r10,zs),(cond' /\ ~(l = 0))))):num#'a
            word#'a word#'a word#('a word) list->(num#'a word#'a
            word#'a word#('a word) list+num#'a word#'a word#'a
            word#('a word) list)#bool`;;

let mc_calc_d_def,mc_calc_d_pre_def =
  tailrec_define "mc_calc_d"
  `(\(l,r1,r2).
     (if r1 < (n2w 0) then (INR (l,r2),T) else
        (let r1 = r1 + r1 in let r2 = r2 + r2 in (INL (l -
          1,r1,r2),~(l = 0))))):num#'a word#'a word->(num#'a word#'a
          word+num#'a word)#bool`;;

let mc_single_mul_def,mc_single_mul_pre_def =
  tailrec_define "mc_single_mul"
  `(\(r0,r1,r2).
     (let cond' = T in
      let (r0,r2) = single_mul r0 r2 (n2w 0) in
      let (r0,r4) = single_add_word r0 r1 (n2w 0) in
      let (r2,r4) = single_add_word r2 (n2w 0) r4 in
        (INR (r0,r1,r2),cond'))):'a word#'a word#'a word->('a
          word#'a word#'a word+'a word#'a word#'a word)#bool`;;

let mc_mul_by_single2_def,mc_mul_by_single2_pre_def =
  tailrec_define "mc_mul_by_single2"
  `(\(r6,r7,r8).
     (let r0 = r6 in
      let r1 = (n2w 0x0) in
      let r2 = r7 in
      let cond' = mc_single_mul_pre (r0,r1,r2) in
      let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
      let r12 = r0 in
      let r0 = r6 in
      let r1 = r2 in
      let r2 = r8 in
      let cond' = (cond' /\ mc_single_mul_pre (r0,r1,r2)) in
      let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
      let r3 = r2 in
      let r2 = r0 in
      let r1 = r12 in
        (INR (r1,r2,r3,r6,r7,r8),cond'))):'a word#'a word#'a
          word->('a word#'a word#'a word+'a word#'a word#'a word#'a
          word#'a word#'a word)#bool`;;

let mc_cmp3_def,mc_cmp3_pre_def =
  tailrec_define "mc_cmp3"
  `(\(r1,r2,r3,r9,r10,r11).
     (let r0 = (n2w 0x1) in
        if r3 = r11 then
          if r2 = r10 then
            if r1 = r9 then
              (let r0 = (n2w 0x0) in (INR
                (r0,r1,r2,r3,r9,r10,r11),T)) else if r9 <+ r1 then
                (INR (r0,r1,r2,r3,r9,r10,r11),T) else (let r0 = (n2w
                0x0) in (INR (r0,r1,r2,r3,r9,r10,r11),T)) else if r10
                <+ r2 then (INR (r0,r1,r2,r3,r9,r10,r11),T) else (let
                r0 = (n2w 0x0) in (INR (r0,r1,r2,r3,r9,r10,r11),T))
                else if r11 <+ r3 then (INR
                (r0,r1,r2,r3,r9,r10,r11),T) else (let r0 = (n2w 0x0)
                in (INR (r0,r1,r2,r3,r9,r10,r11),T)))):'a word#'a
                word#'a word#'a word#'a word#'a word->('a word#'a
                word#'a word#'a word#'a word#'a word+'a word#'a
                word#'a word#'a word#'a word#'a word#'a word)#bool`;;

let mc_cmp_mul2_def,mc_cmp_mul2_pre_def =
  tailrec_define "mc_cmp_mul2"
  `(\(r6,r7,r8,r9,r10,r11).
     (let cond' = mc_mul_by_single2_pre (r6,r7,r8) in
      let (r1,r2,r3,r6,r7,r8) = mc_mul_by_single2 (r6,r7,r8) in
      let (r0,r1,r2,r3,r9,r10,r11) = mc_cmp3 (r1,r2,r3,r9,r10,r11) in
        (INR (r0,r6,r7,r8,r9,r10,r11),cond'))):'a word#'a word#'a
          word#'a word#'a word#'a word->('a word#'a word#'a word#'a
          word#'a word#'a word+'a word#'a word#'a word#'a word#'a
          word#'a word#'a word)#bool`;;

let mc_sub1_def,mc_sub1_pre_def =
  tailrec_define "mc_sub1"
  `(\r6.
     if r6 = (n2w 0x0) then (INR r6,T) else (let r6 = r6 - (n2w
       0x1) in (INR r6,T))):'a word->('a word+'a word)#bool`;;

let mc_cmp2_def,mc_cmp2_pre_def =
  tailrec_define "mc_cmp2"
  `(\(r0,r2,r10,r11).
     (let r1 = (n2w 0x1) in
        if r2 = r11 then
          if r0 = r10 then (let r1 = (n2w 0x0) in (INR
            (r0,r1,r2,r10,r11),T)) else if r10 <+ r0 then (INR
            (r0,r1,r2,r10,r11),T) else (let r1 = (n2w 0x0) in (INR
            (r0,r1,r2,r10,r11),T)) else if r11 <+ r2 then (INR
            (r0,r1,r2,r10,r11),T) else (let r1 = (n2w 0x0) in (INR
            (r0,r1,r2,r10,r11),T)))):'a word#'a word#'a word#'a
            word->('a word#'a word#'a word#'a word+'a word#'a word#'a
            word#'a word#'a word)#bool`;;

let mc_div_test_def,mc_div_test_pre_def =
  tailrec_define "mc_div_test"
  `(\(l,r6,r7,r8,r9,r10,r11).
     (let cond' = mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) in
      let (r0,r6,r7,r8,r9,r10,r11) = mc_cmp_mul2
        (r6,r7,r8,r9,r10,r11) in
        if r0 = (n2w 0x0) then (INR (l,r6,r7,r8,r9,r10,r11),cond')
          else
          (let r6 = mc_sub1 r6 in
           let r0 = r6 in
           let r1 = (n2w 0x0) in
           let r2 = r8 in
           let r3 = r1 in
           let cond' = (cond' /\ mc_single_mul_add_pre (r0,r1,r2,r3))
             in
           let (r0,r1,r2,r3) = mc_single_mul_add (r0,r1,r2,r3) in
           let r2 = r2 + (n2w 0x1) in
           let (r0,r1,r2,r10,r11) = mc_cmp2 (r0,r2,r10,r11) in
             if r1 = (n2w 0x0) then (INR
               (l,r6,r7,r8,r9,r10,r11),cond') else (INL (l -
               1,r6,r7,r8,r9,r10,r11),(cond' /\ ~(l = 0)))))):num#'a
               word#'a word#'a word#'a word#'a word#'a word->(num#'a
               word#'a word#'a word#'a word#'a word#'a word+num#'a
               word#'a word#'a word#'a word#'a word#'a word)#bool`;;

let mc_div_r1_def,mc_div_r1_pre_def =
  tailrec_define "mc_div_r1"
  `(\(r0,r1,r2).
     if r2 <+ r1 then
       (let cond' = single_div_pre r2 r0 r1 in
        let (r0,r2) = single_div r2 r0 r1 in
          (INR (r0,r1,r2),cond')) else (let r0 = (n2w 0x0) in let
            r0 = word_not r0 in (INR (r0,r1,r2),T))):'a word#'a
            word#'a word->('a word#'a word#'a word+'a word#'a word#'a
            word)#bool`;;

let mc_div_guess_def,mc_div_guess_pre_def =
  tailrec_define "mc_div_guess"
  `(\(l,r7,r8,r9,r10,r11).
     (let r0 = r10 in
      let r1 = r8 in
      let r2 = r11 in
      let cond' = mc_div_r1_pre (r0,r1,r2) in
      let (r0,r1,r2) = mc_div_r1 (r0,r1,r2) in
      let r6 = r0 in
      let cond' = (cond' /\ mc_div_test_pre (l -
        1,r6,r7,r8,r9,r10,r11) /\ ~(l = 0)) in
      let (l,r6,r7,r8,r9,r10,r11) = mc_div_test (l -
        1,r6,r7,r8,r9,r10,r11) in
        (INR (l,r6,r7,r8,r9,r10,r11),cond'))):num#'a word#'a
          word#'a word#'a word#'a word->(num#'a word#'a word#'a
          word#'a word#'a word+num#'a word#'a word#'a word#'a word#'a
          word#'a word)#bool`;;

let mc_adj_cmp_def,mc_adj_cmp_pre_def =
  tailrec_define "mc_adj_cmp"
  `(\(r0,r3,r8).
     if r0 = r3 then (INR (r0,r3,r8),T) else
       (let r8 = (n2w 0x1) in
          if r3 <+ r0 then (INR (r0,r3,r8),T) else (let r8 = (n2w
            0x0) in (INR (r0,r3,r8),T)))):'a word#'a word#'a
            word->('a word#'a word#'a word+'a word#'a word#'a
            word)#bool`;;

let mc_adjust_aux_def,mc_adjust_aux_pre_def =
  tailrec_define "mc_adjust_aux"
  `(\(l,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs).
     if r9 = r11 then
       (let r0 = r12 in
        let cond' = (w2n r10 < LENGTH zs) in
        let r3 = EL (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
        let (r0,r3,r8) = mc_adj_cmp (r0,r3,r8) in
          (INR (l,r6,r7,r8,r9,r10,r11,ys,zs),cond')) else
       (let r0 = r6 in
        let cond' = (w2n r11 < LENGTH ys) in
        let r2 = EL (w2n r11) ys in
        let cond' = (cond' /\ mc_single_mul_pre (r0,r1,r2)) in
        let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
        let r1 = r12 in
        let r12 = r2 in
        let r2 = r0 in
        let r0 = r7 in
        let cond' = (cond' /\ mc_single_mul_pre (r0,r1,r2)) in
        let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
        let r1 = r12 in
        let r12 = r2 in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let r3 = EL (w2n r10) zs in
        let (r0,r3,r8) = mc_adj_cmp (r0,r3,r8) in
        let r11 = r11 + (n2w 0x1) in
        let r10 = r10 + (n2w 0x1) in
          (INL (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs),(cond' /\
            ~(l = 0))))):num#'a word#'a word#'a word#'a word#'a
            word#'a word#'a word#'a word#('a word) list#('a word)
            list->(num#'a word#'a word#'a word#'a word#'a word#'a
            word#'a word#'a word#('a word) list#('a word) list+num#'a
            word#'a word#'a word#'a word#'a word#'a word#('a word)
            list#('a word) list)#bool`;;

let mc_div_adjust_def,mc_div_adjust_pre_def =
  tailrec_define "mc_div_adjust"
  `(\(l,r6,r7,r9,r10,ys,zs).
     (let r1 = (n2w 0x0) in
      let r8 = r1 in
      let r11 = r1 in
      let r12 = r1 in
      let cond' = (mc_adjust_aux_pre (l -
        1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) /\ ~(l = 0)) in
      let (l,r6,r7,r8,r9,r10,r11,ys,zs) =
            mc_adjust_aux (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) in
        if r7 = (n2w 0x0) then (INR
          (l,r6,r7,r9,r10,r11,ys,zs),cond') else if r8 = (n2w 0x0)
          then (INR (l,r6,r7,r9,r10,r11,ys,zs),cond') else (let r7 =
          r7 - (n2w 0x1) in (INR
          (l,r6,r7,r9,r10,r11,ys,zs),cond')))):num#'a word#'a word#'a
          word#'a word#('a word) list#('a word) list->(num#'a word#'a
          word#'a word#'a word#('a word) list#('a word) list+num#'a
          word#'a word#'a word#'a word#'a word#('a word) list#('a
          word) list)#bool`;;

let mc_div_sub_def,mc_div_sub_pre_def =
  tailrec_define "mc_div_sub"
  `(\(r0,r3,r8).
     (let cond' = ((~(r8 = (n2w 0))) ==> (r8 = (n2w 1))) in
      let (r3,r8) = single_sub_word r3 r0 r8 in
       (INR (r0,r3,r8),cond'))):'a word#'a word#'a word->('a
         word#'a word#'a word+'a word#'a word#'a word)#bool`;;

let mc_div_sub_loop_def,mc_div_sub_loop_pre_def =
  tailrec_define "mc_div_sub_loop"
  `(\(l,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs).
     if r9 = r11 then
       (let r0 = r12 in
        let cond' = (w2n r10 < LENGTH zs) in
        let r3 = EL (w2n r10) zs in
        let cond' = (cond' /\ mc_div_sub_pre (r0,r3,r8)) in
        let (r0,r3,r8) = mc_div_sub (r0,r3,r8) in
        let r1 = r3 in
        let zs = LUPDATE r1 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INR (l,r6,r7,r9,r10,r11,ys,zs),cond')) else
       (let r0 = r6 in
        let cond' = (w2n r11 < LENGTH ys) in
        let r2 = EL (w2n r11) ys in
        let cond' = (cond' /\ mc_single_mul_pre (r0,r1,r2)) in
        let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
        let r1 = r12 in
        let r12 = r2 in
        let r2 = r0 in
        let r0 = r7 in
        let cond' = (cond' /\ mc_single_mul_pre (r0,r1,r2)) in
        let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
        let r1 = r12 in
        let r12 = r2 in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let r3 = EL (w2n r10) zs in
        let cond' = (cond' /\ mc_div_sub_pre (r0,r3,r8)) in
        let (r0,r3,r8) = mc_div_sub (r0,r3,r8) in
        let r0 = r1 in
        let r1 = r3 in
        let zs = LUPDATE r1 (w2n r10) zs in
        let r1 = r0 in
        let r11 = r11 + (n2w 0x1) in
        let r10 = r10 + (n2w 0x1) in
          (INL (l - 1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs),(cond' /\
            ~(l = 0))))):num#'a word#'a word#'a word#'a word#'a
            word#'a word#'a word#'a word#('a word) list#('a word)
            list->(num#'a word#'a word#'a word#'a word#'a word#'a
            word#'a word#'a word#('a word) list#('a word) list+num#'a
            word#'a word#'a word#'a word#'a word#('a word) list#('a
            word) list)#bool`;;

let mc_div_loop_def,mc_div_loop_pre_def =
  tailrec_define "mc_div_loop"
  `(\(l,(r7:'a word),(r9:'a word),(r10:'a word),(r11:'a word),
      (r14:'a word),(r15:'a word),(ys:('a word) list),(zs:('a word)
        list)).
     if r10 = (n2w 0x0) then (INR (l,r7,r9,r10,r11,r14,r15,ys,zs),T)
       else
       (let r6 = r14 in
        let r3 = r15 in
        let r14 = r7 in
        let r15 = r9 in
        let r16 = r10 in
        let r10 = r10 + r9 in
        let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH zs) in
        let r0 = EL (w2n r10) zs in
        let r10 = r10 - (n2w 0x1) in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let r1 = EL (w2n r10) zs in
        let r10 = r10 - (n2w 0x1) in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let r2 = EL (w2n r10) zs in
        let r11 = r0 in
        let r10 = r1 in
        let r9 = r2 in
        let r7 = r3 in
        let r8 = r6 in
        let cond' = (cond' /\ mc_div_guess_pre (l,r7,r8,r9,r10,r11))
          in
        let (l,r6,r7,r8,r9,r10,r11) = mc_div_guess
          (l,r7,r8,r9,r10,r11) in
        let r0 = r6 in
        let r6 = r14 in
        let r9 = r15 in
        let r10 = r16 in
        let r10 = r10 - (n2w 0x1) in
        let r15 = r7 in
        let r14 = r8 in
        let r7 = r0 in
        let cond' = (cond' /\ mc_div_adjust_pre
          (l,r6,r7,r9,r10,ys,zs)) in
        let (l,r6,r7,r9,r10,r11,ys,zs) = mc_div_adjust
          (l,r6,r7,r9,r10,ys,zs) in
        let r10 = r10 - r9 in
        let r10 = r10 - (n2w 0x1) in
        let r1 = (n2w 0x0) in
        let r8 = r1 in
        let r8 = (n2w 1) in
        let r11 = r1 in
        let r12 = r1 in
        let cond' = (
              cond' /\
              mc_div_sub_loop_pre (l -
                1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) /\ ~(l = 0)) in
        let (l,r6,r7,r9,r10,r11,ys,zs) =
              mc_div_sub_loop (l -
                1,r1,r6,r7,r8,r9,r10,r11,r12,ys,zs) in
        let r10 = r10 - (n2w 0x1) in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r7 (w2n r10) zs in
        let r10 = r10 - r9 in
        let r7 = r6 in
          (INL (l - 1,r7,r9,r10,r11,r14,r15,ys,zs),(cond' /\ ~(l =
            0)))))`;;

let mc_mul_by_single_def,mc_mul_by_single_pre_def =
  tailrec_define "mc_mul_by_single"
  `(\(l,r1,r8,r9,r10,r11,xs,zs).
     if r9 = r11 then
       (let cond' = (w2n r10 < LENGTH zs) in
        let zs = LUPDATE r1 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INR (l,r1,r8,r9,r10,xs,zs),cond')) else
       (let cond' = (w2n r11 < LENGTH xs) in
        let r2 = EL (w2n r11) xs in
        let r0 = r8 in
        let r3 = (n2w 0x0) in
        let cond' = (cond' /\ mc_single_mul_add_pre (r0,r1,r2,r3)) in
        let (r0,r1,r2,r3) = mc_single_mul_add (r0,r1,r2,r3) in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r0 (w2n r10) zs in
        let r1 = r2 in
        let r10 = r10 + (n2w 0x1) in
        let r11 = r11 + (n2w 0x1) in
          (INL (l - 1,r1,r8,r9,r10,r11,xs,zs),(cond' /\ ~(l =
            0))))):num#'a word#'a word#'a word#'a word#'a word#('a
            word) list#('a word) list->(num#'a word#'a word#'a
            word#'a word#'a word#('a word) list#('a word) list+num#'a
            word#'a word#'a word#'a word#('a word) list#('a word)
            list)#bool`;;

let mc_top_two_def,mc_top_two_pre_def =
  tailrec_define "mc_top_two"
  `(\(l,r0,r1,r3,r8,r9,r11,ys).
     if r9 = r11 then (let r1 = r3 in (INR (l,r0,r1,r8,r9,r11,ys),T))
       else
       (let r3 = r0 in
        let cond' = (w2n r11 < LENGTH ys) in
        let r2 = EL (w2n r11) ys in
        let r0 = r8 in
        let cond' = (cond' /\ mc_single_mul_pre (r0,r1,r2)) in
        let (r0,r1,r2) = mc_single_mul (r0,r1,r2) in
        let r1 = r2 in
        let r11 = r11 + (n2w 0x1) in
          (INL (l - 1,r0,r1,r3,r8,r9,r11,ys),(cond' /\ ~(l =
            0))))):num#'a word#'a word#'a word#'a word#'a word#'a
            word#('a word) list->(num#'a word#'a word#'a word#'a
            word#'a word#'a word#('a word) list+num#'a word#'a
            word#'a word#'a word#'a word#('a word) list)#bool`;;

let mc_copy_down_def,mc_copy_down_pre_def =
  tailrec_define "mc_copy_down"
  `(\(l,r8,r10,r11,zs).
     if r8 = (n2w 0x0) then (INR (l,zs),T) else
       (let cond' = (w2n r10 < LENGTH zs) in
        let r0 = EL (w2n r10) zs in
        let r8 = r8 - (n2w 0x1) in
        let r10 = r10 + (n2w 0x1) in
        let cond' = (cond' /\ w2n r11 < LENGTH zs) in
        let zs = LUPDATE r0 (w2n r11) zs in
        let r11 = r11 + (n2w 0x1) in
          (INL (l - 1,r8,r10,r11,zs),(cond' /\ ~(l = 0))))):num#'a
            word#'a word#'a word#('a word) list->(num#'a word#'a
            word#'a word#('a word) list+num#('a word) list)#bool`;;

let mc_copy_over_def,mc_copy_over_pre_def =
  tailrec_define "mc_copy_over"
  `(\(l,r10,xs,zs).
     if r10 = (n2w 0x0) then (INR (l,xs,zs),T) else
       (let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH xs) in
        let r0 = EL (w2n r10) xs in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r0 (w2n r10) zs in
          (INL (l - 1,r10,xs,zs),(cond' /\ ~(l = 0))))):num#'a
            word#('a word) list#('a word) list->(num#'a word#('a
            word) list#('a word) list+num#('a word) list#('a word)
            list)#bool`;;

let mc_div0_def,mc_div0_pre_def =
  tailrec_define "mc_div0"
  `(\(l,r0,r1,r3,xs,ys,zs).
        let r6 = r0 in
          if r3 = (n2w 0x0) then
            (let r0 = (n2w 0x0) in (INR (l,r0,r3,r6,xs,ys,zs),T))
              else
            (let r11 = r0 in
             let r10 = r1 in
             let r0 = (n2w 0x0) in
             let cond' = (mc_mul_zero_pre (l - 1,r0,r10,zs) /\ ~(l =
               0)) in
             let (l,r10,zs) = mc_mul_zero (l - 1,r0,r10,zs) in
             let r10 = r11 in
             let cond' = (cond' /\ mc_copy_over_pre (l - 1,r10,xs,zs)
               /\ ~(l = 0)) in
             let (l,xs,zs) = mc_copy_over (l - 1,r10,xs,zs) in
             let r0 = r1 in
               (INR (l,r0,r3,r6,xs,ys,zs),cond'))):num#'a word#'a
                 word#'a word#('a word) list#('a word) list#('a word)
                 list->(num#'a word#'a word#'a word#('a word)
                 list#('a word) list#('a word) list+num#'a word#'a
                 word#'a word#('a word) list#('a word) list#('a word)
                 list)#bool`;;


let mc_div1_def,mc_div1_pre_def =
  tailrec_define "mc_div1"
  `(\(l,r0,r1,r3,xs,ys,zs).
       (let r14 = r3 in
        let r2 = (n2w 0x0) in
        let r10 = r2 in
        let cond' = (w2n r10 < LENGTH ys) in
        let r9 = EL (w2n r10) ys in
        let r10 = r0 in
        let r8 = r0 in
        let cond' = (cond' /\ mc_simple_div_pre (l -
          1,r2,r9,r10,xs,zs) /\ ~(l = 0)) in
        let (l,r2,r9,r10,xs,zs) = mc_simple_div (l -
          1,r2,r9,r10,xs,zs) in
        let r6 = (n2w 0x0) in
        let r0 = r8 in
        let r3 = r14 in
          if r3 = (n2w 0x0) then
            if r2 = (n2w 0x0) then (INR (l,r0,r3,r6,xs,ys,zs),cond')
              else (let r6 = (n2w 0x1) in (INR
              (l,r0,r3,r6,xs,ys,zs),cond')) else
            (let r0 = (n2w 0x1) in
             let r10 = ((n2w 0x0):'a word) in
             let cond' = (cond' /\ w2n r10 < LENGTH zs) in
             let zs = LUPDATE r2 (w2n r10) zs in
               if r2 = (n2w 0x0) then (INR
                 (l,r0,r3,r6,xs,ys,zs),cond') else (let r6 = (n2w
                 0x1) in (INR (l,r0,r3,r6,xs,ys,zs),cond'))))):num#'a
                 word#'a word#'a word#('a word) list#('a word)
                 list#('a word) list->(num#'a word#'a word#'a
                 word#('a word) list#('a word) list#('a word)
                 list+num#'a word#'a word#'a word#('a word) list#('a
                 word) list#('a word) list)#bool`;;

let mc_div2_def,mc_div2_pre_def =
  tailrec_define "mc_div2"
  `(\(l,r7,r8,r10,r11,r18,xs,ys,zs).
        let r9 = r7 in
        let r2 = (n2w 0x0) in
        let cond' = (mc_simple_div1_pre (l - 1,r2,r9,r10,zs) /\ ~(l =
          0)) in
        let (l,r2,r9,r10,zs) = mc_simple_div1 (l - 1,r2,r9,r10,zs) in
        let r9 = r11 in
        let r10 = r9 in
        let r7 = r8 in
        let cond' = (cond' /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l =
          0)) in
        let (l,r8,r10,zs) = mc_fix (l - 1,r8,r10,zs) in
        let r6 = r10 in
        let r10 = r9 in
        let r3 = r18 in
        let r8 = r7 in
          if r3 = (n2w 0x0) then
            (let r11 = (n2w 0x0) in
             let cond' = (cond' /\ mc_copy_down_pre (l -
               1,r8,r10,r11,zs) /\ ~(l = 0)) in
             let (l,zs) = mc_copy_down (l - 1,r8,r10,r11,zs) in
             let r0 = r7 in
               (INR (l,r0,r3,r6,xs,ys,zs),cond')) else (let r0 =
                 r9 in (INR (l,r0,r3,r6,xs,ys,zs),cond'))):num#'a
                 word#'a word#'a word#'a word#'a word#('a word)
                 list#('a word) list#('a word) list->(num#'a word#'a
                 word#'a word#'a word#'a word#('a word) list#('a
                 word) list#('a word) list+num#'a word#'a word#'a
                 word#('a word) list#('a word) list#('a word)
                 list)#bool`;;

let mc_div3_def,mc_div3_pre_def =
  tailrec_define "mc_div3"
  `(\(l,r2,r7,r9,r18,r19,xs,ys,zs).
        let r1 = (n2w 0x0) in
        let r8 = r2 in
        let r10 = r1 in
        let r11 = r1 in
        let cond' = (mc_mul_by_single_pre (l -
          1,r1,r8,r9,r10,r11,xs,zs) /\ ~(l = 0)) in
        let (l,r1,r8,r9,r10,xs,zs) =
              mc_mul_by_single (l - 1,r1,r8,r9,r10,r11,xs,zs) in
        let r1 = (n2w 0x0) in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let zs = LUPDATE r1 (w2n r10) zs in
        let r0 = (n2w 0x0) in
        let r1 = r0 in
        let r3 = r0 in
        let r11 = r0 in
        let r9 = r7 in
        let cond' = (cond' /\ mc_top_two_pre (l -
          1,r0,r1,r3,r8,r9,r11,ys) /\ ~(l = 0)) in
        let (l,r0,r1,r8,r9,r11,ys) = mc_top_two (l -
          1,r0,r1,r3,r8,r9,r11,ys) in
        let r7 = r8 in
        let r11 = r9 in
        let r10 = r19 in
        let r10 = r10 - r9 in
        let r10 = r10 + (n2w 0x2) in
        let r14 = r0 in
        let r15 = r1 in
        let r17 = r10 in
        let cond' = (cond' /\ mc_div_loop_pre (l -
          1,r7,r9,r10,r11,r14,r15,ys,zs) /\ ~(l = 0)) in
        let (l,r7,r9,r10,r11,r14,r15,ys,zs) =
              mc_div_loop (l - 1,r7,r9,r10,r11,r14,r15,ys,zs) in
        let r8 = r17 in
        let r11 = r9 in
        let r10 = r9 in
        let cond' = (cond' /\ mc_div2_pre
          (l,r7,r8,r10,r11,r18,xs,ys,zs)) in
        let (l,r0,r3,r6,xs,ys,zs) = mc_div2
          (l,r7,r8,r10,r11,r18,xs,ys,zs) in
          (INR (l,r0,r3,r6,xs,ys,zs),cond')):num#'a word#'a
            word#'a word#'a word#'a word#('a word) list#('a word)
            list#('a word) list->(num#'a word#'a word#'a word#'a
            word#'a word#('a word) list#('a word) list#('a word)
            list+num#'a word#'a word#'a word#('a word) list#('a word)
            list#('a word) list)#bool`;;

let mc_div_def,mc_div_pre_def =
  tailrec_define "mc_div"
  `(\(l,r0,r1,r3,xs,ys,zs).
     if r0 <+ r1 then
       (let cond' = mc_div0_pre (l,r0,r1,r3,xs,ys,zs) in
        let (l,r0,r3,r6,xs,ys,zs) = mc_div0 (l,r0,r1,r3,xs,ys,zs) in
          (INR (l,r0,r3,r6,xs,ys,zs),cond')) else if r1 = (n2w 0x1)
            then
       (let cond' = mc_div1_pre (l,r0,r1,r3,xs,ys,zs) in
        let (l,r0,r3,r6,xs,ys,zs) = mc_div1 (l,r0,r1,r3,xs,ys,zs) in
          (INR (l,r0,r3,r6,xs,ys,zs),cond')) else
       (let r18 = r3 in
        let r19 = r0 in
        let r7 = r1 in
        let r9 = r0 in
        let r10 = r1 in
        let r10 = r10 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH ys) in
        let r1 = EL (w2n r10) ys in
        let r2 = (n2w 0x1) in
        let cond' = (cond' /\ mc_calc_d_pre (l - 1,r1,r2) /\ ~(l =
          0)) in
        let (l,r2) = mc_calc_d (l - 1,r1,r2) in
        let cond' = (cond' /\ mc_div3_pre
          (l,r2,r7,r9,r18,r19,xs,ys,zs)) in
        let (l,r0,r3,r6,xs,ys,zs) = mc_div3
          (l,r2,r7,r9,r18,r19,xs,ys,zs) in
          (INR (l,r0,r3,r6,xs,ys,zs),cond'))):num#'a word#'a
            word#'a word#('a word) list#('a word) list#('a word)
            list->(num#'a word#'a word#'a word#('a word) list#('a
            word) list#('a word) list+num#'a word#'a word#'a word#('a
            word) list#('a word) list#('a word) list)#bool`;;

let mc_add1_def,mc_add1_pre_def =
  tailrec_define "mc_add1"
  `(\(l,r2,r10,r11,zs).
     if r10 = r11 then
       (let r0 = (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH zs) in
        let zs = LUPDATE r0 (w2n r10) zs in
        let r11 = r11 + (n2w 0x1) in
          (INR (l,r11,zs),cond')) else
       (let cond' = (w2n r10 < LENGTH zs) in
        let r0 = EL (w2n r10) zs in
          if r0 = r2 then
            (let r0 = (n2w 0x0) in
             let zs = LUPDATE r0 (w2n r10) zs in
             let r10 = r10 + (n2w 0x1) in
               (INL (l - 1,r2,r10,r11,zs),(cond' /\ ~(l = 0)))) else
            (let r0 = r0 + (n2w 0x1) in
             let zs = LUPDATE r0 (w2n r10) zs in
               (INR (l,r11,zs),cond')))):num#'a word#'a word#'a
                 word#('a word) list->(num#'a word#'a word#'a
                 word#('a word) list+num#'a word#('a word) list)#bool`;;

let mc_add1_call_def,mc_add1_call_pre_def =
  tailrec_define "mc_add1_call"
  `(\(l,r2,r6,r11,zs).
     if r2 = (n2w 0x0) then (INR (l,r11,zs),T) else if r6 = (n2w 0x0)
       then (INR (l,r11,zs),T) else
       (let r2 = (n2w 0x0) in
        let r10 = r2 in
        let r2 = word_not r2 in
        let cond' = (mc_add1_pre (l - 1,r2,r10,r11,zs) /\ ~(l = 0))
          in
        let (l,r11,zs) = mc_add1 (l - 1,r2,r10,r11,zs) in
          (INR (l,r11,zs),cond'))):num#'a word#'a word#'a word#('a
            word) list->(num#'a word#'a word#'a word#('a word)
            list+num#'a word#('a word) list)#bool`;;

let mc_div_sub_aux1_def,mc_div_sub_aux1_pre_def =
  tailrec_define "mc_div_sub_aux1"
  `(\(l,(r1:'a word),(r4:'a word),(r8:'a word),(r9:'a word),(r10:'a
  word),ys,zs).
     if r1 = (n2w 0x1) then
       (let r1 = ((n2w 0x0):'a word) in
          (INR (l,r1,r4,r8,r9,r10,ys,zs),T)) else
       (let r1 = r1 - (n2w 0x1) in
        let cond' = (w2n r10 < LENGTH ys) in
        let r8 = EL (w2n r10) ys in
        let cond' = (cond' /\ w2n r10 < LENGTH zs) in
        let r9 = EL (w2n r10) zs in
        let cond' = (cond' /\ ((~(r4 = (n2w 0))) ==> (r4 = (n2w 1))))
          in
        let (r8,r4) = single_sub_word r8 r9 r4 in
        let zs = LUPDATE r8 (w2n r10) zs in
        let r10 = r10 + (n2w 0x1) in
          (INL (l - 1,r1,r4,r8,r9,r10,ys,zs),(cond' /\ ~(l =
            0)))))`;;

let mc_div_sub_aux_def,mc_div_sub_aux_pre_def =
  tailrec_define "mc_div_sub_aux"
  `(\(l,r1,r8,r9,ys,zs).
     (let r10 = (n2w 0x0) in
      let r1 = r1 + (n2w 0x1) in
      let r4 = (n2w 1) in
      let cond' = (mc_div_sub_aux1_pre (l - 1,r1,r4,r8,r9,r10,ys,zs)
        /\ ~(l = 0)) in
      let (l,r1,r4,r8,r9,r10,ys,zs) = mc_div_sub_aux1 (l -
        1,r1,r4,r8,r9,r10,ys,zs) in
        (INR (l,r1,r4,r8,r9,r10,ys,zs),cond'))):num#'a word#'a
          word#'a word#('a word) list#('a word) list->(num#'a word#'a
          word#'a word#('a word) list#('a word) list+num#'a word#'a
          word#'a word#'a word#'a word#('a word) list#('a word)
          list)#bool`;;

let mc_div_sub1_def,mc_div_sub1_pre_def =
  tailrec_define "mc_div_sub1"
  `(\(l,r1,r8,r9,ys,zs).
     (let cond' = mc_div_sub_aux_pre (l,r1,r8,r9,ys,zs) in
      let (l,r1,r4,r8,r9,r10,ys,zs) = mc_div_sub_aux
        (l,r1,r8,r9,ys,zs) in
        (INR (l,r1,r8,r9,r10,ys,zs),cond'))):num#'a word#'a
          word#'a word#('a word) list#('a word) list->(num#'a word#'a
          word#'a word#('a word) list#('a word) list+num#'a word#'a
          word#'a word#'a word#('a word) list#('a word) list)#bool`;;

let mc_div_sub_call_def,mc_div_sub_call_pre_def =
  tailrec_define "mc_div_sub_call"
  `(\(l,r1,r2,r6,ys,zs).
     if r2 = (n2w 0x0) then (INR (l,r6,ys,zs),T) else if r6 = (n2w
       0x0) then (INR (l,r6,ys,zs),T) else
       (let r8 = r6 in
        let r9 = r6 in
        let r3 = r1 in
        let cond' = mc_div_sub1_pre (l,r1,r8,r9,ys,zs) in
        let (l,r1,r8,r9,r10,ys,zs) = mc_div_sub1 (l,r1,r8,r9,ys,zs)
          in
        let r10 = r3 in
        let cond' = (cond' /\ mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l =
          0)) in
        let (l,r8,r10,zs) = mc_fix (l - 1,r8,r10,zs) in
        let r6 = r10 in
          (INR (l,r6,ys,zs),cond'))):num#'a word#'a word#'a
            word#('a word) list#('a word) list->(num#'a word#'a
            word#'a word#('a word) list#('a word) list+num#'a
            word#('a word) list#('a word) list)#bool`;;

let mc_idiv_mod_header_def,mc_idiv_mod_header_pre_def =
  tailrec_define "mc_idiv_mod_header"
  `(\(r6,r11).
     if r6 = (n2w 0x0) then (INR r6,T) else
       (let r6 = r6 << 1 in
          if r11 && (n2w 0x1) = (n2w 0x0) then (INR r6,T) else
            (let r6 = r6 + (n2w 0x1) in (INR r6,T)))):'a word#'a
            word->('a word#'a word+'a word)#bool`;;

let mc_idiv0_def,mc_idiv0_pre_def =
  tailrec_define "mc_idiv0"
  `(\(l,(r0:'a word),(r3:'a word),r6,r11,r20,(xs:('a word) list),ys,zs).
        if r3 = (n2w 0x0) then
          (let r10 = r0 in
           let r8 = r10 in
           let cond' = (mc_fix_pre (l - 1,r8,r10,zs) /\ ~(l = 0)) in
           let (l,r8,r10,zs) = mc_fix (l - 1,r8,r10,zs) in
           let r11 = r10 in
           let r2 = r20 in
           let r3 = r2 in
           let cond' = (cond' /\ mc_add1_call_pre (l,r2,r6,r11,zs))
             in
           let (l,r11,zs) = mc_add1_call (l,r2,r6,r11,zs) in
             if r11 = (n2w 0x0) then (INR (l,r11,xs,ys,zs),cond')
               else
               (let r11 = r11 << 1 in
                let r11 = r11 + r3 in
                  (INR (l,r11,xs,ys,zs),cond'))) else
          (let r2 = r20 in
           let r1 = r11 in
           let r1 = r1 >>> 1 in
           let cond' = mc_div_sub_call_pre (l,r1,r2,r6,ys,zs) in
           let (l,r6,ys,zs) = mc_div_sub_call (l,r1,r2,r6,ys,zs) in
           let r6 = mc_idiv_mod_header (r6,r11) in
           let r11 = r6 in
             (INR (l,r11,xs,ys,zs),cond'))):num#'a word#'a word#'a
               word#'a word#'a word#('a word) list#('a word) list#('a
               word) list->(num#'a word#'a word#'a word#'a word#'a
               word#('a word) list#('a word) list#('a word)
               list+num#'a word#('a word) list#('a word) list#('a
               word) list)#bool`;;

let mc_idiv_def,mc_idiv_pre_def =
  tailrec_define "mc_idiv"
  `(\(l,r3,r10,r11,xs,ys,zs).
     (let r0 = r10 >>> 1 in
      let r1 = r11 >>> 1 in
      let r10 = r10 ?? r11 in
      let r10 = r10 && (n2w 0x1) in
      let r20 = r10 in
      let r21 = r11 in
      let cond' = mc_div_pre (l,r0,r1,r3,xs,ys,zs) in
      let (l,r0,r3,r6,xs,ys,zs) = mc_div (l,r0,r1,r3,xs,ys,zs) in
      let r11 = r21 in
      let cond' = (cond' /\ mc_idiv0_pre
        (l,r0,r3,r6,r11,r20,xs,ys,zs)) in
      let (l,r11,xs,ys,zs) = mc_idiv0 (l,r0,r3,r6,r11,r20,xs,ys,zs)
        in
        (INR (l,r11,xs,ys,zs),cond'))):num#'a word#'a word#'a
          word#('a word) list#('a word) list#('a word) list->(num#'a
          word#'a word#'a word#('a word) list#('a word) list#('a
          word) list+num#'a word#('a word) list#('a word) list#('a
          word) list)#bool`;;

let mc_isub_flip_def,mc_isub_flip_pre_def =
  tailrec_define "mc_isub_flip"
  `(\(r1,r3).
     if r3 = (n2w 0x0) then (INR (r1,r3),T) else (let r1 = r1 ??
       (n2w 0x1) in (INR (r1,r3),T))):'a word#'a word->('a word#'a
       word+'a word#'a word)#bool`;;

let mc_icmp_res_def,mc_icmp_res_pre_def =
  tailrec_define "mc_icmp_res"
  `(\(r10,r3).
     if r3 = (n2w 0x2) then
       if r10 = (n2w 0x1) then (let r10 = (n2w 0x1) in (INR
         r10,T)) else (let r10 = (n2w 0x0) in (INR r10,T)) else if
         r10 = (n2w 0x0) then (let r10 = (n2w 0x1) in (INR r10,T))
         else (let r10 = (n2w 0x0) in (INR r10,T))):'a word#'a
         word->('a word#'a word+'a word)#bool`;;

let mc_full_cmp_def,mc_full_cmp_pre_def =
  tailrec_define "mc_full_cmp"
  `(\(l,r3,r10,r11,xs,ys,zs).
     (let cond' = mc_icompare_pre (l,r10,r11,xs,ys) in
      let (l,r10,xs,ys) = mc_icompare (l,r10,r11,xs,ys) in
      let r10 = mc_icmp_res (r10,r3) in
        if r10 = (n2w 0x0) then (INR (l,r10,xs,ys,zs),cond') else
          (let r0 = (n2w 0x1) in
           let r10 = ((n2w 0x0):'a word) in
           let cond' = (cond' /\ w2n r10 < LENGTH zs) in
           let zs = LUPDATE r0 (w2n r10) zs in
           let r10 = (n2w 0x2) in
             (INR (l,r10,xs,ys,zs),cond')))):num#'a word#'a
               word#'a word#('a word) list#('a word) list#('a word)
               list->(num#'a word#'a word#'a word#('a word) list#('a
               word) list#('a word) list+num#'a word#('a word)
               list#('a word) list#('a word) list)#bool`;;

let mc_iop_def,mc_iop_pre_def =
  tailrec_define "mc_iop"
  `(\(l,r0,r1,r3,xs,ys,zs).
     if r3 <+ (n2w 0x2) then
       (let (r1,r3) = mc_isub_flip (r1,r3) in
        let r2 = r1 in
        let r1 = r0 in
        let cond' = mc_iadd_pre (l,r1,r2,xs,ys,zs) in
        let (l,r10,xs,ys,zs) = mc_iadd (l,r1,r2,xs,ys,zs) in
          (INR (l,r10,xs,ys,zs),cond')) else
      // else if r3 <+ 0x4w then
      // (let r10 = r0 in
      // let r11 = r1 in
      // let cond = mc_full_cmp_pre (r3,r10,r11,xs,ys,zs) in
      // let (r10,xs,ys,zs) = mc_full_cmp (r3,r10,r11,xs,ys,zs)
      // in
      // (INR (r10,xs,ys,zs,ss),cond))
      if r3 = (n2w 0x4) then
       (let r2 = r1 in
        let r1 = r0 in
        let cond' = mc_imul_pre (l,r1,r2,xs,ys,zs) in
        let (l,r10,xs,ys,zs) = mc_imul (l,r1,r2,xs,ys,zs) in
          (INR (l,r10,xs,ys,zs),cond')) else
       (
        // if r3 <+ 0x7w then
        let r3 = r3 - (n2w 0x5) in
        let r10 = r0 in
        let r11 = r1 in
        let cond' = mc_idiv_pre (l,r3,r10,r11,xs,ys,zs) in
        let (l,r11,xs,ys,zs) = mc_idiv (l,r3,r10,r11,xs,ys,zs) in
        let r10 = r11 in
          (INR (l,r10,xs,ys,zs),cond'))):num#'a word#'a word#'a
            word#('a word) list#('a word) list#('a word)
            list->(num#'a word#'a word#'a word#('a word) list#('a
            word) list#('a word) list+num#'a word#('a word) list#('a
            word) list#('a word) list)#bool`;;

let mc_fac_init_def,mc_fac_init_pre_def =
  tailrec_define "mc_fac_init"
  `(\((l:num),r1).
     if r1 <+ (n2w 2) then
       (let r0 = ((n2w 0):'a word) in
        let r2 = ((n2w 0):'a word) in
        let r3 = (n2w 0) in
        let cond' = T in
          (INR (l,r0,r1,r2,r3),cond')) else
       (let r0 = ((n2w 1):'a word) in
        let r2 = r1 - (n2w 1) in
        let r3 = r1 - (n2w 2) in
        let cond' = T in
          (INR (l,r0,r1,r2,r3),cond'))):num#'a word->(num#'a
            word+num#'a word#'a word#'a word#'a word)#bool`;;

let mc_fac_final_def,mc_fac_final_pre_def =
  tailrec_define "mc_fac_final"
  `(\((l:num),r1,r2).
      let r1 = r1 + r2 in
      let cond' = T in
        (INR (l,r1),cond')):num#'a word#'a word->(num#'a word#'a
          word+num#'a word)#bool`;;

(* HOL4 mc_multiwordScript.sml:4196-4212: the tactic that proves the
   termination *)
let mc_fac_def = cake_define_wf
  `MEASURE FST`
  `mc_fac ((l:num),(r1:'a word)) =
     (let l0 = l in
     let (l,r0,r1,r2,r3) = mc_fac_init ((l:num),(r1:'a word)) in
     let l = MIN l l0 in
       if r0 = (n2w 0) then (l,r1) else
         let r1 = r2 in
         if l = 0 then (l,r1) else
         let ((r2,r3),(l,r1)) = ((r2,r3),mc_fac (l - 1,r1)) in
         let l = MIN l l0 in
         let r2 = r1 in
         let r1 = r3 in
         if l = 0 then (l,r1) else
         let (r2,(l,r1)) = (r2,mc_fac (l - 1,r1)) in
         let (l,r1) = mc_fac_final (l,r1,r2) in
           (l,r1))`;;

(* HOL4 mc_multiwordScript.sml:4214-4233: the tactic that proves the
   termination *)
let mc_fac_pre_def = cake_define_wf
  `MEASURE FST`
  `mc_fac_pre ((l:num),(r1:'a word)) =
     (let l0 = l in
     let cond' = mc_fac_init_pre ((l:num),(r1:'a word)) in
     let (l,r0,r1,r2,r3) = mc_fac_init ((l:num),(r1:'a word)) in
     let l = MIN l l0 in
       if r0 = (n2w 0) then F else
         let r1 = r2 in
         if l = 0 then F else
         let cond' = (mc_fac_pre (l - 1,r1) /\ cond') in
         let ((r2,r3),(l,r1)) = ((r2,r3),mc_fac (l - 1,r1)) in
         let l = MIN l l0 in
         let r2 = r1 in
         let r1 = r3 in
         if l = 0 then F else
         let cond' = (mc_fac_pre (l - 1,r1) /\ cond') in
         let cond' = (mc_fac_final_pre (l,r1,r2) /\ cond') in
         let (l,r1) = mc_fac_final (l,r1,r2) in
           cond')`;;

let mc_use_fac_def,mc_use_fac_pre_def =
  tailrec_define "mc_use_fac"
  `(\((l:num),r1).
      let cond' = (mc_fac_pre (l - 1,r1) /\ ~(l = 0)) in
      let (l,r1) = mc_fac (l - 1,r1) in
      let r0 = r1 in
        (INR (l,r0),cond')):num#'a word->(num#'a word+num#'a
          word)#bool`;;
