(* ======================================================== *)
(*  word_gcFunctions: ported from HOL4's
    compiler/backend/proofs/word_gcFunctionsScript.sml  *)
(* ======================================================== *)

(*
  Shallow embedding of garbage collector implementation
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* HOL4 ML code, not ported:
val shift_def = backend_commonTheory.word_shift_def;
*)

(* move candidates *)

(* HOL4 ML code, not ported:
val IMP_EQ_DISJ = METIS_PROVE [] ``(b1 ==> b2) <=> ~b1 \/ b2``
*)

(* -------------------------------------------------------
    definition and verification of GC functions
   ------------------------------------------------------- *)

let ptr_to_addr_def = cake_define
  `ptr_to_addr conf base (w:'a word) =
     base + ((w >>> (shift_length conf)) * bytes_in_word)`;;

let update_addr_def = cake_define
  `update_addr conf fwd_ptr (old_addr:'a word) =
     ((fwd_ptr << (shift_length conf)) ||
      (word_bits (small_shift_length conf - 1) 0) old_addr)`;;

let memcpy_def = cake_define
  `memcpy w a b m dm =
     (if w = (n2w 0) then (b,m,T) else
       let (b1,m1,c1) = memcpy (w - (n2w 1)) (a + bytes_in_word) (b +
         bytes_in_word)
                       ((b =+ m a) m) dm in
         (b1,m1,(c1 /\ a IN dm /\ b IN dm)))`;;

let decode_length_def = cake_define
  `decode_length conf (w:'a word) = w >>> (dimindex (:'a) -
  data_to_word_config_len_size conf)`;;

let word_gc_move_def = cake_define_list
  [`word_gc_move conf (wordLang_Loc l1 l2,i,pa,old,m,dm) = ((Loc l1
  l2:'a word_loc),i,pa,m,(l2 = 0))`;
   `word_gc_move conf (wordLang_Word w,i,pa,old,m,dm) =
         (if (w && (n2w 1)) = (n2w 0) then ((wordLang_Word w:'a
           word_loc),i,pa,m,T) else
           let c = (ptr_to_addr conf old w IN dm) in
           let v = m (ptr_to_addr conf old w) in
             if is_fwd_ptr v then
               (wordLang_Word (update_addr conf (theWord v >>> 2)
                 w),i,pa,m,c) else
               let header_addr = ptr_to_addr conf old w in
               let c = (c /\ header_addr IN dm /\ isWord (m
                 header_addr)) in
               let len = decode_length conf (theWord (m
                 header_addr)) in
               let v = i + len + (n2w 1) in
               let (pa1,m1,c1) = memcpy (len + (n2w 1)) header_addr
                 pa m dm in
               let c = (c /\ header_addr IN dm /\ c1) in
               let m1 = (header_addr =+ wordLang_Word (i << 2)) m1
                 in
                 (wordLang_Word (update_addr conf i
                   w),v,pa1,m1,c))`];;

let word_gen_gc_partial_move_def = cake_define_list
  [`word_gen_gc_partial_move conf (wordLang_Loc l1
  l2,i,pa,old,m,dm,gs,rs) = ((Loc l1 l2:'a word_loc),i,pa,m,(l2 = 0))`;
   `word_gen_gc_partial_move conf (wordLang_Word w,i,pa,old,m,dm,gs,rs)
  =
       (if (w && (n2w 1)) = (n2w 0) then (wordLang_Word w,i,pa,m,T)
         else
         let header_addr = ptr_to_addr conf old w in
         let tmp = header_addr - old in
           if tmp <+ gs \/ rs <=+ tmp then
             (wordLang_Word w,i,pa,m,T) else
             let c = (ptr_to_addr conf old w IN dm) in
             let v = m (ptr_to_addr conf old w) in
               if is_fwd_ptr v then
                 (wordLang_Word (update_addr conf (theWord v >>> 2)
                   w),i,pa,m,c) else
                 let c = (c /\ header_addr IN dm /\ isWord (m
                   header_addr)) in
                 let len = decode_length conf (theWord (m
                   header_addr)) in
                 let v = i + len + (n2w 1) in
                 let (pa1,m1,c1) = memcpy (len + (n2w 1))
                   header_addr pa m dm in
                 let c = (c /\ header_addr IN dm /\ c1) in
                 let m1 = (header_addr =+ wordLang_Word (i << 2)) m1
                   in
                   (wordLang_Word (update_addr conf i
                     w),v,pa1,m1,c))`];;

let word_gc_move_roots_def = cake_define_list
  [`word_gc_move_roots conf ([],i,pa,old,m,dm) = ([],i,pa,m,T)`;
   `word_gc_move_roots conf (w :: ws,i,pa,old,m,dm) =
         (let (w1,i1,pa1,m1,c1) = word_gc_move conf
           (w,i,pa,old,m,dm) in
         let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf
           (ws,i1,pa1,old,m1,dm) in
           (w1 :: ws2,i2,pa2,m2,(c1 /\ c2)))`];;

let word_gc_move_list_def = cake_define
  `word_gc_move_list conf ((a:'a word),(l:'a word),i,(pa:'a
  word),old,m,dm) =
    (if l = (n2w 0) then (a,i,pa,m,T) else
      let w = (m a):'a word_loc in
      let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
      let m1 = (a =+ w1) m1 in
      let (a2,i2,pa2,m2,c2) = word_gc_move_list conf (a +
        bytes_in_word,l - (n2w 1),i1,pa1,old,m1,dm) in
        (a2,i2,pa2,m2,(a IN dm /\ c1 /\ c2)))`;;

let word_gen_gc_partial_move_roots_def = cake_define_list
  [`word_gen_gc_partial_move_roots conf ([],i,pa,old,m,dm,gs,rs) =
  ([],i,pa,m,T)`;
   `word_gen_gc_partial_move_roots conf (w :: ws,i,pa,old,m,dm,gs,rs) =
         (let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf
           (w,i,pa,old,m,dm,gs,rs) in
         let (ws2,i2,pa2,m2,c2) = word_gen_gc_partial_move_roots
           conf (ws,i1,pa1,old,m1,dm,gs,rs) in
           (w1 :: ws2,i2,pa2,m2,(c1 /\ c2)))`];;

let word_gen_gc_partial_move_list_def = cake_define
  `word_gen_gc_partial_move_list conf ((a:'a word),(l:'a word),i,(pa:'a
  word),old,m,dm,gs,rs) =
    (if l = (n2w 0) then (a,i,pa,m,T) else
      let w = (m a):'a word_loc in
      let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf
        (w,i,pa,old,m,dm,gs,rs) in
      let m1 = (a =+ w1) m1 in
      let (a2,i2,pa2,m2,c2) = word_gen_gc_partial_move_list conf (a +
        bytes_in_word,l - (n2w 1),i1,pa1,old,m1,dm,gs,rs) in
        (a2,i2,pa2,m2,(a IN dm /\ c1 /\ c2)))`;;

let word_gc_move_loop_def = cake_define
  `word_gc_move_loop k conf (pb,i,pa,old,m,dm,c) =
     (if pb = pa then (i,pa,m,c) else
     if k = 0 then (i,pa,m,F) else
       let w = m pb in
       let c = (c /\ pb IN dm /\ isWord w) in
       let len = decode_length conf (theWord w) in
         if word_bit 2 (theWord w) then
           let pb = pb + (len + (n2w 1)) * bytes_in_word in
             word_gc_move_loop (k - 1) conf (pb,i,pa,old,m,dm,c) else
           let pb = pb + bytes_in_word in
           let (pb,i1,pa1,m1,c1) = word_gc_move_list conf
             (pb,len,i,pa,old,m,dm) in
             word_gc_move_loop (k - 1) conf
               (pb,i1,pa1,old,m1,dm,(c /\ c1)))`;;

let word_full_gc_def = cake_define
  `word_full_gc conf (all_roots,new,(old:'a word),m,dm) =
     (let (rs,i1,pa1,m1,c1) = word_gc_move_roots conf (all_roots,(n2w
       0),new,old,m,dm) in
     let (i1,pa1,m1,c2) =
           word_gc_move_loop (dimword (:'a)) conf
             (new,i1,pa1,old,m1,dm,c1) in (rs,i1,pa1,m1,c2))`;;

let word_gc_fun_assum_def = cake_define
  `word_gc_fun_assum (conf:data_to_word_config) (s:(store_name,'a
  word_loc)fmap) <=>
     {Globals,CurrHeap,OtherHeap,HeapLength,
      TriggerGC,GenStart,EndOfHeap} SUBSET FDOM s /\
     isWord (FAPPLY s OtherHeap) /\
     isWord (FAPPLY s CurrHeap) /\
     isWord (FAPPLY s TriggerGC) /\
     isWord (FAPPLY s HeapLength) /\
     isWord (FAPPLY s GenStart) /\
     isWord (FAPPLY s EndOfHeap) /\
     isWord (FAPPLY s Globals) /\
     good_dimindex (:'a) /\ ~(data_to_word_config_len_size
     conf = 0) /\ data_to_word_config_len_size
     conf + 2 < dimindex (:'a) /\
     shift_length conf < dimindex (:'a)`;;

let word_gen_gc_can_do_partial_def = cake_define
  `word_gen_gc_can_do_partial gen_sizes (s:(store_name,'a word_loc)fmap)
  <=> ~(
     gen_sizes = []) /\
     (let allo = theWord (FAPPLY s AllocSize) in
     let trig = theWord (FAPPLY s TriggerGC) in
     let endh = theWord (FAPPLY s EndOfHeap) in
       allo <=+ endh - trig)`;;

let new_trig_def = cake_define
  `new_trig (heap_space:'a word) (alloc_pref:'a word) gs =
     (let a = w2n alloc_pref in
     let g = w2n ((get_gen_size gs):'a word) in
     let h = w2n heap_space in
       if a <= g then n2w (MIN h g) else
       if h < a then n2w h else
       if byte_aligned alloc_pref then alloc_pref else n2w h)`;;

let refs_to_addresses_def = cake_define
  `refs_to_addresses x1 =
        match x1 with
          [] -> []
        | (DataElement ptrs _1 _2 :: refs) ->
       ptrs ++ refs_to_addresses refs
        | (_3 :: refs) -> refs_to_addresses refs`;;

let word_gen_gc_partial_move_ref_list_def = cake_define
  `word_gen_gc_partial_move_ref_list k conf
  (pb,i,pa,old,m,dm,c,gs,rs,re) =
     (if pb = re then (i,pa,m,c) else
     if k = 0 then (i,pa,m,F) else
       let w = m pb in
       let c = (c /\ pb IN dm /\ isWord w) in
       let len = decode_length conf (theWord w) in
       let pb = pb + bytes_in_word in
       let (pb,i1,pa1,m1,c1) = word_gen_gc_partial_move_list conf
         (pb,len,i,pa,old,m,dm,gs,rs) in
         word_gen_gc_partial_move_ref_list (k - 1) conf
           (pb,i1,pa1,old,m1,dm,(c /\ c1),gs,rs,re))`;;


let word_gen_gc_partial_move_data_def = cake_define
  `word_gen_gc_partial_move_data conf k ((h2a:'a word),i,(pa:'a
  word),old,m,dm,gs,rs) =
     (if h2a = pa then (i,pa,m,T) else
     if k = 0 then (i,pa,m,F) else
       let c = (h2a IN dm) in
       let v = m h2a in
       let c = (c /\ isWord v) in
       let l = decode_length conf (theWord v) in
         if word_bit 2 (theWord v) then
           let h2a = h2a + (l + (n2w 1)) * bytes_in_word in
           let (i,pa,m,c2) = word_gen_gc_partial_move_data conf (k -
             1)
                         (h2a,i,pa,old,m,dm,gs,rs) in
             (i,pa,m,(c /\ c2)) else
           let (h2a,i,pa,m,c1) = word_gen_gc_partial_move_list conf
                         (h2a + bytes_in_word,l,i,pa,old,m,dm,gs,rs)
                           in
           let (i,pa,m,c2) = word_gen_gc_partial_move_data conf (k -
             1)
                         (h2a,i,pa,old,m,dm,gs,rs) in
             (i,pa,m,(c /\ c1 /\ c2)))`;;


let word_gen_gc_partial_def = cake_define
  `word_gen_gc_partial conf (roots,(curr:'a word),new,len,m,dm,gs,rs) =
     (let refs_end = curr + len in
     let gen_start = gs >>> backend_common_word_shift (:'ga) in
     let (roots,i,pa,m,c1) = word_gen_gc_partial_move_roots conf
                     (roots,gen_start,new,curr,m,dm,gs,rs) in
     let (i,pa,m,c2) = word_gen_gc_partial_move_ref_list (dimword
       (:'a)) conf
                              (curr +
                                rs,i,pa,curr,m,dm,c1,gs,rs,refs_end) in
     let (i,pa,m,c3) = word_gen_gc_partial_move_data conf (dimword
       (:'a))
                              (new,i,pa,curr,m,dm,gs,rs) in
       (roots,i,pa,m,(c2 /\ c3)))`;;

let word_gen_gc_partial_full_def = cake_define
  `word_gen_gc_partial_full conf (roots,(curr:'a
  word),new,len,m,dm,gs,rs) =
     (let (roots,i,pa,m,c1) = word_gen_gc_partial conf
       (roots,curr,new,len,m,dm,gs,rs) in
     let cpy_length = (pa - new) >>> backend_common_word_shift (:'a)
       in
     let (b1,m,c2) = memcpy cpy_length new (curr + gs) m dm in
      (roots,i,b1,m,(c1 /\ c2)))`;;

let is_ref_header_def = cake_define
  `is_ref_header (v:'a word) <=> ((v && (n2w 0b1100)) = (n2w
  0b01000))`;;

let word_gen_gc_move_def = cake_define_list
  [`word_gen_gc_move conf (wordLang_Loc l1 l2,i,pa,ib,pb,old,m,dm) =
         ((Loc l1 l2:'a word_loc),i,pa,ib,pb,m,(l2 = 0))`;
   `word_gen_gc_move conf (wordLang_Word w,i,pa,ib,pb,old,m,dm) =
         (if ((n2w 1) && w) = (n2w 0) then ((wordLang_Word w:'a
           word_loc),i,pa,ib,pb,m,T) else
           let c = (ptr_to_addr conf old w IN dm) in
           let v = m (ptr_to_addr conf old w) in
           let c = (c /\ isWord v) in
             if is_fwd_ptr v then
               (wordLang_Word (update_addr conf (theWord v >>> 2)
                 w),i,pa,ib,pb,m,c) else
               let header_addr = ptr_to_addr conf old w in
               let c = (c /\ header_addr IN dm /\ isWord (m
                 header_addr)) in
               let len = decode_length conf (theWord (m
                 header_addr)) in
                 if is_ref_header (theWord v) then
                   let v = ib - (len + (n2w 1)) in
                   let pb1 = pb - (len + (n2w 1)) * bytes_in_word in
                   let (_7,m1,c1) = memcpy (len + (n2w 1))
                     header_addr pb1 m dm in
                   let c = (c /\ header_addr IN dm /\ c1) in
                   let m1 = (header_addr =+ wordLang_Word (v << 2))
                     m1 in
                     (wordLang_Word (update_addr conf v
                       w),i,pa,v,pb1,m1,c) else
                  let v = i + len + (n2w 1) in
                  let (pa1,m1,c1) = memcpy (len + (n2w 1))
                    header_addr pa m dm in
                  let c = (c /\ header_addr IN dm /\ c1) in
                  let m1 = (header_addr =+ wordLang_Word (i << 2))
                    m1 in
                    (wordLang_Word (update_addr conf i
                      w),v,pa1,ib,pb,m1,c))`];;

let word_gen_gc_move_roots_def = cake_define_list
  [`word_gen_gc_move_roots conf ([],i,pa,ib,pb,old,m,dm) =
  ([],i,pa,ib,pb,m,T)`;
   `word_gen_gc_move_roots conf (w :: ws,i,pa,ib,pb,old,m,dm) =
         (let (w1,i1,pa1,ib,pb,m1,c1) = word_gen_gc_move conf
           (w,i,pa,ib,pb,old,m,dm) in
         let (ws2,i2,pa2,ib,pb,m2,c2) = word_gen_gc_move_roots conf
           (ws,i1,pa1,ib,pb,old,m1,dm) in
           (w1 :: ws2,i2,pa2,ib,pb,m2,(c1 /\ c2)))`];;

let word_gen_gc_move_list_def = cake_define
  `word_gen_gc_move_list conf ((a:'a word),(l:'a word),i,(pa:'a
  word),ib,pb,old,m,dm) =
    (if l = (n2w 0) then (a,i,pa,ib,pb,m,T) else
      let w = (m a):'a word_loc in
      let (w1,i1,pa1,ib,pb,m1,c1) = word_gen_gc_move conf
        (w,i,pa,ib,pb,old,m,dm) in
      let m1 = (a =+ w1) m1 in
      let (a2,i2,pa2,ib,pb,m2,c2) = word_gen_gc_move_list conf (a +
        bytes_in_word,l - (n2w 1),i1,pa1,ib,pb,old,m1,dm) in
        (a2,i2,pa2,ib,pb,m2,(a IN dm /\ c1 /\ c2)))`;;

let word_gen_gc_move_data_def = cake_define
  `word_gen_gc_move_data conf k ((h2a:'a word),i,(pa:'a
  word),ib,pb,old,m,dm) =
     (if h2a = pa then (i,pa,ib,pb,m,T) else
     if k = 0 then (i,pa,ib,pb,m,F) else
       let c = (h2a IN dm) in
       let v = m h2a in
       let c = (c /\ isWord v) in
       let l = decode_length conf (theWord v) in
         if word_bit 2 (theWord v) then
           let h2a = h2a + (l + (n2w 1)) * bytes_in_word in
           let (i,pa,ib,pb,m,c2) = word_gen_gc_move_data conf (k - 1)
                         (h2a,i,pa,ib,pb,old,m,dm) in
             (i,pa,ib,pb,m,(c /\ c2)) else
           let (h2a,i,pa,ib,pb,m,c1) = word_gen_gc_move_list conf
                         (h2a + bytes_in_word,l,i,pa,ib,pb,old,m,dm)
                           in
           let (i,pa,ib,pb,m,c2) = word_gen_gc_move_data conf (k - 1)
                         (h2a,i,pa,ib,pb,old,m,dm) in
             (i,pa,ib,pb,m,(c /\ c1 /\ c2)))`;;

let word_gen_gc_move_refs_def = cake_define
  `word_gen_gc_move_refs conf k ((r2a:'a word),(r1a:'a word),i,(pa:'a
  word),ib,pb,old,(m:'a word->'a word_loc),dm) =
     (if r2a = r1a then (r2a,i,pa,ib,pb,m,T) else
     if k = 0 then (r2a,i,pa,ib,pb,m,F) else
       let c = (r2a IN dm) in
       let v = m r2a in
       let c = (c /\ isWord v) in
       let l = decode_length conf (theWord v) in
       let (r2a,i,pa,ib,pb,m,c1) = word_gen_gc_move_list conf
                              (r2a +
                                bytes_in_word,l,i,pa,ib,pb,old,m,dm) in
       let (r2a,i,pa,ib,pb,m,c2) = word_gen_gc_move_refs conf (k - 1)
                              (r2a,r1a,i,pa,ib,pb,old,m,dm) in
         (r2a,i,pa,ib,pb,m,(c /\ c1 /\ c2)))`;;

let word_gen_gc_move_loop_def = cake_define
  `word_gen_gc_move_loop conf k ((pax:'a word),i,(pa:'a
  word),ib,pb,pbx,old,m,dm) =
     (if pbx = pb then
       if pax = pa then
         (i,pa,ib,pb,m,T) else
         let (i,pa,ib,pb,m,c1) = word_gen_gc_move_data conf (dimword
           (:'a))
                              (pax,i,pa,ib,pb,old,m,dm) in
           if k = 0 then (i,pa,ib,pb,m,F) else
             let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (k -
               1)
                            (pa,i,pa,ib,pb,pbx,old,m,dm) in
               (i,pa,ib,pb,m,(c1 /\ c2)) else
         let (pbx,i,pa,ib,pb',m,c1) = word_gen_gc_move_refs conf
           (dimword (:'a))
                              (pb,pbx,i,pa,ib,pb,old,m,dm) in
           if k = 0 then (i,pa,ib,pb,m,F) else
             let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (k -
               1)
                            (pax,i,pa,ib,pb',pb,old,m,dm) in
               (i,pa,ib,pb,m,(c1 /\ c2)))`;;

let word_gen_gc_def = cake_define
  `word_gen_gc conf (roots,curr,new,(len:'a word),m,dm) =
     (let new_end = new + len in
     let len = len >>> backend_common_word_shift (:'a) in
     let (roots,i,pa,ib,pb,m,c1) = word_gen_gc_move_roots conf
                     (roots,(n2w 0),new,len,new_end,curr,m,dm) in
     let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (w2n len)
                              (new,i,pa,ib,pb,new_end,curr,m,dm) in
       (roots,i,pa,ib,pb,m,(c1 /\ c2)))`;;

let glob_real_def = cake_define
  `glob_real c curr w =
        match w with
          wordLang_Word (w:'a word) ->
        wordLang_Word (curr + (w >>> (shift_length c) <<
          backend_common_word_shift (:'ga)))
        | w -> w`;;

let word_gc_fun_def = cake_define
  `((word_gc_fun (conf:data_to_word_config)):('a word_loc) list#('a
  word->'a word_loc)#('a word->bool)#(store_name,'a word_loc)fmap->(('a
  word_loc) list#('a word->'a word_loc)#(store_name,'a word_loc)fmap)
  option) = (\(roots,m,dm,s).
      let c1 = word_gc_fun_assum conf s in
      let new = theWord (FAPPLY s OtherHeap) in
      let old = theWord (FAPPLY s CurrHeap) in
      let len = theWord (FAPPLY s HeapLength) in
      let all_roots = FAPPLY s Globals :: roots in
        match data_to_word_config_gc_kind conf with None ->
         (let s1 = s |++ [(NextFree,wordLang_Word old);
                          (TriggerGC,wordLang_Word old);
                          (EndOfHeap,wordLang_Word old)] in
            if c1 then SOME (roots,m,s1) else NONE) | Simple ->
         (let (roots1,i1,pa1,m1,c2) =
            word_full_gc conf (all_roots,new,old,m,dm) in
          let s1 = s |++ [(CurrHeap,wordLang_Word new);
                          (OtherHeap,wordLang_Word old);
                          (NextFree,wordLang_Word pa1);
                          (TriggerGC,wordLang_Word (new + len));
                          (EndOfHeap,wordLang_Word (new + len));
                          (Globals,HD roots1);
                          (GlobReal,glob_real conf new (HD roots1))]
                            in
            if c1 /\ c2 then SOME (TL roots1,m1,s1) else NONE) |
              data_to_word_Generational gen_sizes ->
         (if ~c1 then NONE else
         if word_gen_gc_can_do_partial gen_sizes s then
           (let gs = theWord (FAPPLY s GenStart) in
            let rs = theWord (FAPPLY s EndOfHeap) - theWord (FAPPLY s
              CurrHeap) in
            let len = theWord (FAPPLY s HeapLength) in
            let endh = theWord (FAPPLY s EndOfHeap) in
            let (roots1,i1,pa1,m1,c2) =
              word_gen_gc_partial_full conf
                (all_roots,old,new,len,m,dm,gs,rs) in
            let a = theWord (FAPPLY s AllocSize) in
            let s1 = s |++ [(CurrHeap,wordLang_Word old);
                            (OtherHeap,wordLang_Word new);
                            (NextFree,wordLang_Word pa1);
                            (GenStart,wordLang_Word (pa1 - old));
                            (TriggerGC,wordLang_Word (pa1 + new_trig
                              (endh - pa1) a gen_sizes));
                            (Globals,HD roots1);
                            (GlobReal,glob_real conf old (HD
                              roots1));
                            (Temp (n2w 0),wordLang_Word (n2w 0));
                            (Temp (n2w 1),wordLang_Word (n2w 0))] in
            let c3 = (a <=+ endh - pa1 /\ a <=+ new_trig (endh - pa1)
              a gen_sizes) in
              if c2 /\ c3 then SOME (TL roots1,m1,s1) else NONE) else
           (let (roots1,i1,pa1,ib1,pb1,m1,c2) =
              word_gen_gc conf (all_roots,old,new,len,m,dm) in
            let a = theWord (FAPPLY s AllocSize) in
            let s1 = s |++ [(CurrHeap,wordLang_Word new);
                            (OtherHeap,wordLang_Word old);
                            (NextFree,wordLang_Word pa1);
                            (GenStart,wordLang_Word (pa1 - new));
                            (TriggerGC,wordLang_Word (pa1 + new_trig
                              (pb1 - pa1) a gen_sizes));
                            (EndOfHeap,wordLang_Word pb1);
                            (Globals,HD roots1);
                            (GlobReal,glob_real conf new (HD
                              roots1));
                            (Temp (n2w 0),wordLang_Word (n2w 0));
                            (Temp (n2w 1),wordLang_Word (n2w 0));
                            (Temp (n2w 2),wordLang_Word (n2w 0));
                            (Temp (n2w 3),wordLang_Word (n2w 0));
                            (Temp (n2w 4),wordLang_Word (n2w 0));
                            (Temp (n2w 5),wordLang_Word (n2w 0));
                            (Temp (n2w 6),wordLang_Word (n2w 0))] in
              if c2 then SOME (TL roots1,m1,s1) else NONE)))`;;

(* lemmas about has_fp_ops *)
