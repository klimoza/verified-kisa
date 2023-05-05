
Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import Coq.Strings.Ascii.
Require Import format_specs.
Require Import format_std_proof.
Require Import format_proof.
Require Import list_specs.
Require Import format_combinator_proof.

Lemma body_clear_to_text : semax_body Vprog Gprog f_clear_to_text clear_to_text_spec.
Proof.
  start_function.
  forward_if(p <> nullval).
  { forward; destruct l.
    { unff listrep; entailer!. }
    unnw; desf.
    assert (p :: l = []) by auto; vauto. }
  { forward; entailer!. }

  destruct l.
  { unff listrep; Intros; unnw; vauto. }

  unff listrep; Intros.
  destruct p0 as (fst_shift, fst_line).
  Intros fst_tail_ptr fst_line_ptr.

  forward.
  { entailer!; unnw; desf; entailer!. }
  forward_call(l, fst_tail_ptr, gv).
  forward. unfold cstring.
  forward_if(
    PROP()
    LOCAL(temp _t'1 fst_line_ptr; temp _t'3 fst_tail_ptr; gvars gv; temp _l p)
    SEP (mem_mgr gv; malloc_token Ews t_list p; data_at Ews t_list
      (Vptrofs (Ptrofs.repr fst_shift), (fst_line_ptr, fst_tail_ptr)) p)).
  { forward.
    forward_call(tarray tschar (Zlength fst_line + 1), fst_line_ptr, gv).
    { desf; entailer!. }
    entailer!. }
  { forward; entailer!. }
  forward_call(t_list, p, gv).
  { desf; entailer!. }
  entailer!.
Qed.

Lemma body_clear_format_list : semax_body Vprog Gprog f_clear_format_list clear_format_list_spec.
Proof.
  start_function.
  forward_if(p <> nullval).
  { forward.
    destruct fs.
    { unff listrepf; entailer!. }
    unnw; desf.
    assert (t :: fs = []) by auto; vauto. }
  { forward; entailer!. }
  
  Intros; destruct fs; unff listrepf.
  { Intros; unnw; vauto. }
  Intros fst_tail_ptr fst_format_ptr.
  forward.
  { entailer!; unnw; desf; entailer!. }

  forward_call(fs, fst_tail_ptr, gv).
  forward.
  { unfold mformat; Intros sigmaG pG.
    unfold concrete_mformat; do 2 entailer. }
  
  unfold mformat; Intros sigmaG pG; unfold concrete_mformat.
  forward_if(
    PROP()
    LOCAL(temp _t'1 fst_format_ptr; temp _t'5 fst_tail_ptr; gvars gv; temp _fs p)
    SEP (mem_mgr gv; malloc_token Ews t_flist p;
    data_at Ews t_flist (fst_format_ptr, fst_tail_ptr) p)).
  2: { forward; do 2 entailer!. }
  2: { forward_call(t_flist, p, gv).
       { desf; entailer!. }
       entailer!. }

  forward.
  forward.
  { entailer; unnw; desf; entailer!. }

  forward_call(sigmaG, pG, gv).
  forward.
  forward_call(t_format, fst_format_ptr, gv).
  { desf; entailer!. }
  entailer!.
Qed.

Lemma lsegf_lsegf: forall (s1 s2: list t) (x y z: val),
  lsegf s1 x y * lsegf s2 y z |-- lsegf (s1 ++ s2) x z.
Proof.
  intros s1. induction s1.
  { intros. unff lsegf. simpl. entailer!. unnw. subst. entailer. }
  intros. unff lsegf. Intros h y0. simpl.
  unff lsegf.
  Exists h y0.
  entailer!.
  apply IHs1.
Qed.

Lemma lsegf_listf (s1 s2: list t) (x y: val) :
  lsegf s1 x y * listrepf s2 y |-- listrepf (s1 ++ s2) x.
Proof.
  generalize dependent x.
  induction s1; ins; unfold lsegf.
  { entailer!; unnw; subst; entailer. }
  unff lsegf; destruct a.
  Intros h y0.
  unff listrepf; Exists h y0.
  entailer!; apply IHs1.
Qed.

Lemma lsegf_null_listrepf (sigma : list t) (p : val):
  lsegf sigma p nullval |-- listrepf sigma p.
Proof.
  revert p.
  induction sigma.
  { unfold lsegf; unfold listrepf; entailer!. }
  unff lsegf; destruct a.
  intros p.
  Intros h y.
  unff listrepf.
  Exists h y.
  entailer!.
Qed.


Lemma concat_map_nil (l : list t): concat (map (fun x => ([] : list t)) l) = [].
Proof.
  induction l; vauto.
Qed.

Instance t_Inhabitant : Inhabitant t := {
  default := empty;
}.

Lemma beside_doc_forall_height (l : list t) (h : Z):
  Forall (fun G => (height G <= Z.to_nat h)%nat)
    (filter (fun G => (height G <=? Z.to_nat h)%nat) l).
Proof.
  induction l; ins.
  desf.
  { apply Forall_cons; vauto. }
  vauto.
Qed.

Lemma beside_doc_forall_width (l : list t) (h w : Z):
  Forall (fun G : t => (total_width G <= Z.to_nat w)%nat)
    (filter (fun G : t => (height G <=? Z.to_nat h)%nat)
      (filter (fun G : t => (total_width G <=? Z.to_nat w)%nat) l)).
Proof.
  induction l; ins.
  desf.
  { ins; desf.
    { apply Forall_cons; vauto. }
    vauto. }
  vauto.
Qed.

Lemma beside_doc_app (fs l1 l2 : list t) (w : Z):
  FormatTrivial.besideDoc (Z.to_nat w) fs l1 ++
    FormatTrivial.besideDoc (Z.to_nat w) fs l2 =
      FormatTrivial.besideDoc (Z.to_nat w) fs (l1 ++ l2).
Proof.
  unfold FormatTrivial.besideDoc.
  unfold FormatTrivial.cross_general.
  rewrite <- filter_app.
  rewrite <- concat_app.
  rewrite <- map_app.
  vauto.
Qed.


Lemma body_beside_doc : semax_body Vprog Gprog f_beside_doc beside_doc_spec.
Proof.
  start_function.
  forward_if(p1 <> nullval).
  { forward_if(
    PROP ( )
    LOCAL (gvars gv; temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h)); temp _fs1 p1; temp _fs2 p2)
    SEP (listrepf fs1 p1; mem_mgr gv)).
    { forward_call(fs2, p2, gv); entailer!. }
    { forward; entailer!. 
      unnw; desf.
      assert (fs2 = []) by auto; subst.
      unff listrepf; entailer!. }
    forward.
    unnw; desf.
    assert (fs1 = []) by auto; subst.
    Exists nullval ([] : list t); entailer!.
    unfold FormatTrivial.besideDoc.
    unfold FormatTrivial.cross_general; ins.
    rewrite concat_map_nil; list_solve. }
  { forward; entailer!. }

  forward_if(p2 <> nullval).
  { forward_call(fs1, p1, gv).
    forward.
    unnw; desf.
    assert (fs2 = []) by auto; subst.
    Exists nullval ([] : list t); entailer!. }
  { forward; entailer!. }
  forward_call(t_flist, gv).
  Intros result_ptr.
  dest_ptr result_ptr.
  forward_call(gv).
  Intros cur_empty_ptr.
  do 3 forward.
  desf.
  do 2 forward.
  

  remember (
      EX i : Z, EX head_ptr : val, EX result_tail_ptr : val, EX res_part : list t,
      PROP(0 <= i <= Zlength fs2;
            res_part = filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 (sublist 0 i fs2)))
      LOCAL(temp _fs2_tail head_ptr;
            temp _has_item (Val.of_bool (0 <? Zlength res_part)); temp _result result_ptr; gvars gv; 
            temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
            temp _fs1 p1; temp _fs2 p2; temp _result_tail result_tail_ptr)
      SEP (mem_mgr gv; listrepf fs1 p1; lsegf (sublist 0 i fs2) p2 head_ptr; 
          listrepf (sublist i (Zlength fs2) fs2) head_ptr; lsegf res_part result_ptr result_tail_ptr;
          listrepf [empty] result_tail_ptr)) as loop_invariant eqn:eqn_loop.
  remember (
      EX result_tail_ptr : val, EX res_part : list t,
      PROP(res_part = filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))
      LOCAL(temp _has_item (Val.of_bool (0 <? Zlength res_part)); temp _result result_ptr; gvars gv;
            temp _result_tail result_tail_ptr;
            temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
            temp _fs1 p1; temp _fs2 p2)
      SEP (mem_mgr gv; listrepf fs1 p1; listrepf fs2 p2; lsegf res_part result_ptr result_tail_ptr;
          listrepf [empty] result_tail_ptr)) as break_invariant eqn:eqn_break.
  forward_loop(loop_invariant) break: (break_invariant).
  { subst.
    Exists 0 p2 result_ptr ([] : list t).
    entailer!.
    replace (sublist 0 0 fs2) with ([] : list t) by list_solve.
    assert (sublist 0 (Zlength fs2) fs2 = fs2) as K.
    { rewrite sublist_skip; vauto. }
    rewrite K.
    unff lsegf; entailer!; ins.
    unff listrepf.
    Exists nullval cur_empty_ptr.
    entailer!. }
  2: { subst.
      Intros result_tail_ptr res_part.
      forward_call(fs1, p1, gv).
      forward_call(fs2, p2, gv).
      forward_if (
        Zlength res_part <> 0
      ).
      { destruct (0 <? Zlength res_part) eqn:E; vauto.
        forward_call([empty], result_ptr, gv).
        { desf; entailer!.
          replace ((filter (fun G : t => (height G <=? Z.to_nat h)%nat)
          (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))) with ([] : list t) by list_solve.
          unff lsegf; unff listrepf.
          entailer!; subst; unnw; entailer!.
          Exists nullval y; entailer!. }
        forward.
        Exists nullval ([] : list t); entailer!.
        2: { unff listrepf; entailer!. }
        split.
        { unfold good_format_list; vauto. }
        list_solve. }
      { forward; entailer!; ins.
        assert (Zlength (filter (fun G : t => (height G <=? Z.to_nat h)%nat)
           (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)) = 0) as K by vauto.
        rewrite K in *; vauto. }
      forward.
      forward_loop(
        EX i : Z, EX new_result_tail : val,
        PROP(0 <= i < Zlength res_part)
        LOCAL(temp _new_result_tail new_result_tail; temp _fs1 p1; temp _fs2 p2; 
              temp _result_tail result_tail_ptr; gvars gv; temp _result result_ptr)
        SEP(mem_mgr gv; lsegf (sublist 0 i res_part) result_ptr new_result_tail; 
            listrepf (sublist i (Zlength res_part) res_part ++ [empty]) new_result_tail)
      ) break: (
        EX new_result_tail : val,
        PROP()
        LOCAL(temp _new_result_tail new_result_tail; temp _fs1 p1; temp _fs2 p2; 
              temp _result_tail result_tail_ptr; gvars gv; temp _result result_ptr)
        SEP(mem_mgr gv; lsegf (sublist 0 (Zlength res_part - 1) res_part) result_ptr new_result_tail; 
            listrepf (sublist (Zlength res_part - 1) (Zlength res_part) res_part ++ [empty]) new_result_tail)).
      { Exists 0 result_ptr.
        entailer!.
        autorewrite with sublist.
        unff lsegf; entailer!.
        apply lsegf_listf. }
      { Intros i new_result_tail_ptr.
        replace (sublist i (Zlength res_part) res_part) with (Znth i res_part :: sublist (i + 1) (Zlength res_part) res_part)
          by list_solve.
        autorewrite with sublist norm.
        replace ((Znth i res_part
            :: sublist (i + 1) (Zlength res_part) res_part) ++ [empty]) with
            (Znth i res_part :: (sublist (i + 1) (Zlength res_part) res_part ++ [empty])) by list_solve.
        unff listrepf.
        Intros ith_tail_ptr ith_format_ptr.
        forward.
        { entailer!; getnw; desf. }
        assert (i + 1 = Zlength res_part \/ i + 1 < Zlength res_part) as K by lia.
        destruct K.
        { replace (sublist (i + 1) (Zlength res_part) res_part) with ([] : list t) by list_solve.
          autorewrite with sublist.
          unff listrepf.
          Intros nullval_tail_ptr empty_ptr.
          forward.
          { unnw; subst; entailer!. }
          getnw; rewrite LIST_NULL_PTR.
          forward_if.
          { vauto. }
          forward.  
          Exists new_result_tail_ptr.
          entailer!.
          remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))
            as res_part.
          replace i with (Zlength res_part - 1) by lia.
          replace (sublist (Zlength res_part - 1) (Zlength res_part) res_part ++ [empty])
            with [Znth (Zlength res_part - 1) res_part; empty] by list_solve.
          unff listrepf.
          Exists ith_tail_ptr ith_format_ptr.
          Exists nullval empty_ptr.
          entailer!.
        }
        replace (sublist (i + 1) (Zlength res_part) res_part)
          with (Znth (i + 1) res_part :: sublist (i + 2) (Zlength res_part) res_part) by list_solve.
        replace ((Znth (i + 1) res_part :: sublist (i + 2) (Zlength res_part) res_part) ++ [empty]) with
            (Znth (i + 1) res_part :: ((sublist (i + 2) (Zlength res_part) res_part ++ [empty]))) by list_solve.
        unff listrepf.
        Intros ithplus_tail_ptr ithplus_format_ptr.
        forward.
        { entailer!; unnw; desf.  }
        forward_if.
        { forward; entailer!.
          remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)).
          Exists (i + 1) ith_tail_ptr.
          replace (sublist (i + 1) (Zlength l) l) with
              (Znth (i + 1) l :: sublist (i + 2) (Zlength l) l) by list_solve.
          replace ((Znth (i + 1) l :: sublist (i + 2) (Zlength l) l) ++ [empty]) with 
              (Znth (i + 1) l :: (sublist (i + 2) (Zlength l) l ++ [empty])) by list_solve.
          unff listrepf.
          Exists ithplus_tail_ptr ithplus_format_ptr.
          entailer!.
          remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)).
          assert (
            lsegf (sublist 0 i l) result_ptr new_result_tail_ptr *
            lsegf [Znth i l] new_result_tail_ptr ith_tail_ptr |--
            lsegf (sublist 0 (i + 1) l) result_ptr ith_tail_ptr) as K.
          { replace (sublist 0 (i + 1) l) with (sublist 0 i l ++ [Znth i l]) by list_solve.
            eapply lsegf_lsegf. }
          eapply derives_trans.
          2: eauto.
          entailer!.
          unff lsegf; Exists ith_tail_ptr ith_format_ptr.
          entailer!. }
        forward.
        replace ithplus_tail_ptr with nullval by vauto.
        destruct (sublist (i + 2) (Zlength res_part) res_part).
        { autorewrite with sublist norm.
          unff listrepf.
          Intros x y.
          entailer!. }
        replace (((t :: l) ++ [empty])) with (t :: (l ++ [empty])) by list_solve.
        unff listrepf.
        Intros x y.
        entailer!. }
    Intros new_result_tail.
    replace (sublist (Zlength res_part - 1) (Zlength res_part) res_part ++ [empty]) with 
        [Znth (Zlength res_part - 1) res_part; empty] by list_solve.
    unff listrepf.
    Intros empty_list_ptr last_format_ptr nullval_ptr empty_format_ptr.
    forward.
    forward_call([empty], empty_list_ptr, gv).
    { getnw; subst.
      unff listrepf.
      Exists nullval empty_format_ptr.
      entailer!. }
    do 2 forward.
    Exists result_ptr (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)).
    entailer!.
    2: {
      remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)).
      assert (
        lsegf (sublist 0 (Zlength l - 1) l) result_ptr new_result_tail *
        listrepf [Znth (Zlength l - 1) l] new_result_tail |--
        listrepf l result_ptr
      ) as K.
      { assert(l = (sublist 0 (Zlength l - 1) l ++ [Znth (Zlength l - 1) l])) as KK by list_solve.
        rewrite KK at 5.
        apply lsegf_listf. }
      eapply derives_trans.
      2: eauto.
      unff listrepf.
      Exists nullval last_format_ptr.
      entailer!. }
    unfold good_format_list.
    unfold good_format.
    eapply Forall_and.
    2: { apply beside_doc_forall_height. }
    unfold FormatTrivial.besideDoc.
    unfold FormatTrivial.cross_general.
    apply beside_doc_forall_width. }
subst.
Intros i head_ptr result_tail_ptr res_part.
forward_if.
2: {
  forward.
  Exists result_tail_ptr res_part.
  assert(i < Zlength fs2 \/ i = Zlength fs2) as K by lia.
  destruct K.
  { replace (sublist i (Zlength fs2) fs2) with 
      (Znth i fs2 :: sublist (i + 1) (Zlength fs2) fs2) by list_solve.
    unff listrepf.
    Intros x1 y1 x2 y2.
    subst.
    entailer!. }
  entailer!.
  { autorewrite with sublist norm; vauto. }
  autorewrite with sublist norm.
  unff listrepf.
  entailer!.
  apply lsegf_null_listrepf. }
forward.
remember (
    EX j : Z, EX head_ptr2 : val, EX result_tail_ptr_new : val, EX res_part_new : list t,
    PROP(0 <= j <= Zlength fs1;
          res_part_new = res_part ++ filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) (sublist 0 j fs1) [Znth i fs2]))
    LOCAL(temp _fs2_tail head_ptr; temp _fs1_tail head_ptr2;
          temp _has_item (Val.of_bool (0 <? Zlength res_part_new)); 
          temp _result result_ptr; gvars gv; 
          temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
          temp _fs1 p1; temp _fs2 p2; temp _result_tail result_tail_ptr_new)
    SEP (mem_mgr gv; 
        lsegf (sublist 0 j fs1) p1 head_ptr2;
        listrepf (sublist j (Zlength fs1) fs1) head_ptr2;
        lsegf (sublist 0 i fs2) p2 head_ptr; 
        listrepf (sublist i (Zlength fs2) fs2) head_ptr; 
        lsegf res_part_new result_ptr result_tail_ptr_new;
        listrepf [empty] result_tail_ptr_new)) as loop_invariant eqn:eqn_loop.
remember (
    EX result_tail_ptr_new : val, EX res_part_new : list t,
    PROP(res_part_new = filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 (sublist 0 (i + 1) fs2)))
    LOCAL(temp _has_item (Val.of_bool (0 <? Zlength res_part_new)); 
          temp _result result_ptr; 
          gvars gv;
          temp _result_tail result_tail_ptr_new;
          temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
          temp _fs1 p1; temp _fs2 p2;
          temp _fs2_tail head_ptr)
    SEP (mem_mgr gv; 
        listrepf fs1 p1; 
        lsegf (sublist 0 i fs2) p2 head_ptr; 
        listrepf (sublist i (Zlength fs2) fs2) head_ptr; 
        lsegf res_part_new result_ptr result_tail_ptr_new;
        listrepf [empty] result_tail_ptr_new)) as break_invariant eqn:eqn_break.
forward_loop(loop_invariant) break: (break_invariant).
{ rewrite eqn_loop.
  Exists 0 p1 result_tail_ptr res_part.
  entailer!.
  { autorewrite with sublist norm; vauto. }
  autorewrite with sublist norm.
  unff lsegf; entailer!. }
2: {
  rewrite eqn_break.
  Intros result_tail_ptr_new res_part_new.
  assert(i = Zlength fs2 \/ i < Zlength fs2) as K by lia.
  destruct K.
  { subst.
    autorewrite with sublist norm.
    unff listrepf.
    Intros; unnw; vauto. }
  replace (sublist i (Zlength fs2) fs2) 
    with (Znth i fs2 :: (sublist (i + 1) (Zlength fs2) fs2)) by list_solve.
  unff listrepf.
  Intros ith_tail_ptr ith_format_ptr.
  Intros nullval_ptr empty_ptr.
  getnw; rewrite LIST_NULL_PTR.
  forward.
  { entailer!; unnw; desf. }
  Exists (i + 1) ith_tail_ptr result_tail_ptr_new res_part_new.
  entailer!.
  unff listrepf.
  Exists nullval empty_ptr.
  entailer!.
  assert (
    lsegf (sublist 0 i fs2) p2 head_ptr *
    lsegf [Znth i fs2] head_ptr ith_tail_ptr |--
    lsegf (sublist 0 (i + 1) fs2) p2 ith_tail_ptr
  ) as K.
  { replace (sublist 0 (i + 1) fs2) with
      (sublist 0 i fs2 ++ [Znth i fs2]) by list_solve.
    apply lsegf_lsegf. }
  eapply derives_trans.
  2: eauto.
  entailer!.
  unff lsegf; entailer!.
  Exists ith_tail_ptr ith_format_ptr.
  entailer!. }
rewrite eqn_loop.
Intros j head_ptr2 result_tail_ptr_new res_part_new.
forward_if.
2: { 
  forward.
  rewrite eqn_break.
  Exists result_tail_ptr_new 
    (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 (sublist 0 (i + 1) fs2))).
  assert (j < Zlength fs1 \/ j = Zlength fs1) as K by lia.
  destruct K.
  { replace (sublist j (Zlength fs1) fs1) with
      (Znth j fs1 :: sublist (j + 1) (Zlength fs1) fs1) by list_solve.
    unff listrepf.
    subst.
    Intros x y x1 y1.
    entailer!. }
  replace j with (Zlength fs1) by lia.
  assert (i = Zlength fs2 \/ i < Zlength fs2) as K by lia.
  destruct K.
  { subst.
    autorewrite with sublist norm.
    unff listrepf.
    Intros x y.
    unnw; vauto. }
  entailer!.
  { rewrite <- filter_app.
    replace (sublist 0 (Zlength fs1) fs1) with fs1 by list_solve.
    rewrite beside_doc_app.
    replace (sublist 0 (i + 1) fs2) with
      (sublist 0 i fs2 ++ [Znth i fs2]) by list_solve.
    vauto. }
  autorewrite with sublist norm.
  unff listrepf.
  rewrite <- filter_app.
  rewrite beside_doc_app.
  replace (sublist 0 (i + 1) fs2) with
    (sublist 0 i fs2 ++ [Znth i fs2]) by list_solve.
  entailer!.
  apply lsegf_null_listrepf. }
assert (j = Zlength fs1 \/ j < Zlength fs1) as K by lia.
destruct K.
{ subst.
  autorewrite with sublist norm.
  unff listrepf.
  Intros x y.
  unnw; vauto. }
assert (i = Zlength fs2 \/ i < Zlength fs2) as K by lia.
destruct K.
{ subst.
  autorewrite with sublist norm.
  unff listrepf.
  Intros x y.
  unnw; vauto. }
replace (sublist i (Zlength fs2) fs2) with
  (Znth i fs2 :: (sublist (i + 1) (Zlength fs2) fs2)) by list_solve.
replace (sublist j (Zlength fs1) fs1) with
  (Znth j fs1 :: (sublist (j + 1) (Zlength fs1) fs1)) by list_solve.
unff listrepf.
Intros ith_tail_fs1_ptr ith_format_fs1_ptr.
Intros ith_tail_fs2_ptr ith_format_fs2_ptr.
Intros nullval_ptr empty_ptr.
getnw; rewrite LIST_NULL_PTR.
forward.
{ entailer.
  unfold mformat.
  unfold concrete_mformat.
  Intros x y x1 y1 x2 y2.
  entailer!. }
forward.
{ entailer.
  unfold mformat.
  unfold concrete_mformat.
  Intros x y x1 y1 x2 y2.
  entailer!. }
unfold mformat.
Intros sigmaG pG sigmaF pF sigmaEmpty pEmpty.
unfold concrete_mformat.
Intros.
forward_call(Znth j fs1, Znth i fs2, 
    ith_format_fs1_ptr, ith_format_fs2_ptr, sigmaG, sigmaF, pG, pF, gv).
{ unfold concrete_mformat; entailer!. }
{ split.
  { getnw; inv FMT_MP.
    getnw; inv FMT_MP.
    getnw; inv FMT_MP.
    unfold good_format_list in *.
    assert (good_format (Znth j fs1) w h) as GF1.
    { list_solve. }
    assert (good_format (Znth i fs2) w h) as GF2.
    { list_solve. }
    unfold good_format in GF1.
    unfold good_format in GF2.
    desc.
    unfold total_width in *; ins.
    destruct (Znth j fs1).
    destruct (Znth i fs2).
    apply mk_format_comb; ins; try lia.
    unfold Int.max_unsigned in *; ins; lia. }
  split.
  { getnw

  }
}


Admitted.