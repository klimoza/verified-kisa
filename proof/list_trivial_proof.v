
Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import printer.verified_printer.FormatTrivial.
Require Import Coq.Strings.Ascii.
Require Import format_specs.
Require Import list_specs.

Lemma zmax_natmax_eq (a b : nat):
  0 <= Z.of_nat a <= Int.max_unsigned ->
  0 <= Z.of_nat b <= Int.max_unsigned ->
  Z.max (Z.of_nat a) (Z.of_nat b) = Z.of_nat (max a b).
Proof.
  lia.
Qed.

Lemma body_total_width : semax_body Vprog Gprog f_total_width total_width_spec.
Proof.
  start_function.
  unfold concrete_mformat.
  Intros.
  getnw; inv FMT_MP.
  do 2 forward.
  forward_call(Z.of_nat (middle_width G), Z.of_nat (last_line_width G)).
  Intros vret.
  forward.
  forward_call(Z.of_nat (first_line_width G), vret).
  Intros vret0.
  forward.
  entailer!.
  { unfold total_width.
    destruct G.
    ins.
    rewrite zmax_natmax_eq; try lia.
    rewrite zmax_natmax_eq; try lia.
    auto. } 
  unfold concrete_mformat.
  entailer!.
Qed.

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
  Intros fst_tail_ptr fst_format_ptr format_sigma sigma_pt.
  forward.
  { entailer!; unnw; desf; entailer!. }

  forward_call(fs, fst_tail_ptr, w, h, gv).
  forward.
  { entailer; unfold concrete_mformat; entailer. }

  unfold concrete_mformat.
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

  forward_call(format_sigma, sigma_pt, gv).
  forward.
  forward_call(t_format, fst_format_ptr, gv).
  { desf; entailer!. }
  entailer!.
Qed.

Lemma lsegf_lsegf: forall (s1 s2: list t) (x y z: val) (w h : Z),
  lsegf s1 x y w h * lsegf s2 y z w h |-- lsegf (s1 ++ s2) x z w h.
Proof.
  intros s1. induction s1.
  { intros; unff lsegf; simpl; entailer!; unnw; subst; entailer. }
  intros. 
  unff lsegf. 
  Intros h0 y0 format_sigma sigma_pt. 
  simpl.
  unff lsegf.
  Exists h0 y0 format_sigma sigma_pt.
  entailer!.
  apply IHs1.
Qed.

Lemma lsegf_listf (s1 s2: list t) (x y: val) (w h : Z):
  lsegf s1 x y w h * listrepf s2 y w h |-- listrepf (s1 ++ s2) x w h.
Proof.
  generalize dependent x.
  induction s1; ins; unfold lsegf.
  { entailer!; unnw; subst; entailer. }
  unff lsegf; destruct a.
  Intros h0 y0 format_sigma sigma_pt.
  unff listrepf.
  Exists h0 y0 format_sigma sigma_pt.
  entailer!; apply IHs1.
Qed.

Lemma lsegf_null_listrepf (sigma : list t) (p : val) (w h : Z):
  lsegf sigma p nullval w h |-- listrepf sigma p w h.
Proof.
  revert p.
  induction sigma.
  { unfold lsegf; unfold listrepf; entailer!. }
  unff lsegf; destruct a.
  intros p.
  Intros h0 y format_sigma sigma_pt.
  unff listrepf.
  Exists h0 y format_sigma sigma_pt.
  entailer!.
Qed.

 Definition format_without_to_text (G : t) (x p : val) : mpred :=
  sepcon (malloc_token Ews t_format x)
  (data_at Ews t_format (Vint (Int.repr (Z.of_nat G.(height))),
                        (Vint (Int.repr (Z.of_nat G.(first_line_width))),
                         (Vint (Int.repr (Z.of_nat G.(middle_width))),
                          (Vint (Int.repr (Z.of_nat G.(last_line_width))), p)))) x)
.

Lemma body_max_width_check : semax_body Vprog Gprog f_max_width_check max_width_check_spec.
Proof.
  start_function.
  unfold concrete_mformat.
  Intros.
  getnw; inv FMT_MP.
  assert (0 <= Z.of_nat (total_width G) <= Int.max_unsigned) as K.
  { unfold total_width.
    desf; ins; lia. }
  forward_call(G, p, sigma, sigma_pt).
  { unfold concrete_mformat; entailer!. }
  forward_if.
  { forward.
    Exists false.
    entailer!. }
  forward.
  forward_if.
  { forward.
    Exists false.
    unfold concrete_mformat; entailer!. }
  forward.
  Exists true.
  unfold concrete_mformat.
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

Lemma beside_doc_app_l (l1 l2: list t) (w : Z) (G : t):
  FormatTrivial.besideDoc (Z.to_nat w) l1 [G] ++
    FormatTrivial.besideDoc (Z.to_nat w) l2 [G] =
      FormatTrivial.besideDoc (Z.to_nat w) (l1 ++ l2) [G].
Proof.
  unfold FormatTrivial.besideDoc.
  unfold FormatTrivial.cross_general.
  repeat rewrite <- filter_app.
  repeat rewrite <- concat_app.
  repeat rewrite map_cons.
  repeat rewrite map_nil.
  repeat rewrite concat_app.
  repeat rewrite concat_cons.
  repeat rewrite concat_nil.
  autorewrite with sublist norm.
  repeat rewrite filter_app.
  repeat rewrite map_app.
  repeat rewrite filter_app.
  vauto.
Qed.

Lemma beside_doc_llw_add (fs : list (Z * list byte)) (llw w : Z):
  0 <= 8 * w <= Int.max_unsigned - 1 ->
  Forall (fun x => 0 <= 4 * (fst x) <= Int.max_unsigned - 1) fs ->
  Forall (fun x => 0 <= 4 * (Zlength (snd x)) + 1 <= Int.max_unsigned) fs ->
  Forall (fun x => 0 <= fst x + Zlength (snd x) <= w) fs ->
  0 <= llw <= w ->
  Forall (fun x => 0 <= 4 * (fst x + llw) <= Int.max_unsigned - 1) fs.
Proof.
  ins.
  induction fs.
  { apply Forall_nil. }
  apply Forall_cons_iff in H0.
  destruct H0.
  apply Forall_cons_iff in H1.
  destruct H1.
  apply Forall_cons_iff in H2.
  destruct H2.
  apply Forall_cons.
  2: apply (IHfs H4 H5 H6 ).
  lia.
Qed.

Lemma beside_doc_ab_pred (G F : t) (fs1 fs2 : list (Z * list byte)) (w : Z):
  0 <= 8 * w <= Int.max_unsigned - 1 ->
  list_mp fs1 ->
  Forall (fun x => 0 <= fst x + Zlength (snd x) <= w) fs2 ->
  Forall (fun x => 0 <= fst x + Zlength (snd x) <= w) fs1 ->
  to_text_add_beside_pred G F fs1 fs2.
Proof.
  ins.
  unfold to_text_add_beside_pred.
  desf.
  induction fs1.
  { apply Forall_nil. }
  inv H1.
  inv H0.
  inv H2.
  apply Forall_cons_iff in  list_mp_forall_fst.
  apply Forall_cons_iff in  list_mp_forall_snd.
  desf.
  apply Forall_cons.
  2: { apply IHfs1; vauto. 
       apply mk_list_mp; vauto.
       list_solve. }
  unfold Int.max_unsigned; ins.
  lia.
Qed.

Lemma total_width_eq (G : t) (sigma : list (Z * list byte)):
  << FMT_MP : format_mp G sigma >> ->
  total_width G = list_max (map (fun x => Z.to_nat (fst x + Zlength (snd x))) sigma).
Proof.
  ins.
  getnw; inv FMT_MP.
  unfold first_line_width_pred in *.
  unfold middle_width_pred in *.
  unfold last_line_width_pred in *.
  desf; ins; unfold total_width; desf; ins.
  all: rewrite format_mp_flw_eq.
  all: rewrite format_mp_mw_eq.
  all: rewrite format_mp_llw_eq.
  { replace sigma with ([] : list (Z * list byte)) by list_solve.
    list_solve. }
  { replace sigma with [Znth 0 sigma] by list_solve.
    rewrite map_cons.
    rewrite map_nil.
    rewrite list_max_cons.
    rewrite list_max_nil.
    autorewrite with sublist norm.
    lia. }
  { replace (Zlength sigma) with 2%Z by lia.
    replace (2 - 1) with 1 by lia.
    replace sigma with [Znth 0 sigma; Znth 1 sigma] by list_solve.
    repeat rewrite map_cons.
    rewrite map_nil.
    repeat rewrite list_max_cons.
    rewrite list_max_nil.
    autorewrite with sublist norm.
    replace (Znth 1 [Znth 0 sigma;  Znth 1 sigma]) with (Znth 1 sigma) by list_solve.
    lia. }
  assert (sigma = [Znth 0 sigma] ++ sublist 1 (Zlength sigma - 1) sigma ++ [Znth (Zlength sigma - 1) sigma]) as K by list_solve.
  rewrite K at 9.
  repeat rewrite map_app.
  repeat rewrite map_cons.
  repeat rewrite map_nil.
  repeat rewrite list_max_app.
  repeat rewrite list_max_cons.
  repeat rewrite list_max_nil.
  lia.
Qed.

Lemma list_max_impl_forall (l : list (Z * list byte)) (w : Z):
  0 <= 8 * w <= Int.max_unsigned - 1 ->
  list_mp l ->
  (list_max (map (fun x => Z.to_nat (fst x + Zlength (snd x))) l) <= Z.to_nat w)%nat ->
  Forall (fun x => 0 <= fst x + Zlength (snd x) <= w) l.
Proof.
  ins.
  revert dependent w.
  induction l; ins.
  inv H0.
  apply Forall_cons_iff in list_mp_forall_fst.
  apply Forall_cons_iff in list_mp_forall_snd.
  desf.
  apply Forall_cons_iff; split.
  { lia. }
  remember  ((list_max (map (fun x : Z * list byte => Z.to_nat (fst x + Zlength (snd x))) l))) as local_max.
  enough (
    Forall (fun x => 0 <= fst x + Zlength (snd x) <= Z.of_nat local_max) l
  ) as FF.
  { assert (Z.of_nat local_max <= w) as K by lia.
    list_solve. }
  apply IHl.
  { apply mk_list_mp; list_solve. }
  { lia. }
  lia.
Qed.

Lemma body_format_list_copy : semax_body Vprog Gprog f_format_list_copy format_list_copy_spec.
Proof.
  start_function.
  forward_if.
  { forward.
    Exists nullval.
    entailer!.
    unnw; desf.
    assert (fs = []) by auto; subst.
    unff listrepf.
    entailer!. }
  forward_call(t_flist, gv).
  Intros result_ptr.
  dest_ptr result_ptr.
  destruct fs.
  { unff listrepf.
    Intros; ins. }
  unff listrepf.
  Intros x y format_sigma sigma_pt.
  forward.
  { unfold concrete_mformat.
    do 2 entailer. }
  forward_call(t, y, format_sigma, sigma_pt, gv).
  Intros new_format_pt.
  do 2 forward.
  { entailer!; unnw; desf. }
  forward_call(fs, x, w, h, gv).
  Intros tail_ptr.
  do 2 forward.
  Exists result_ptr.
  entailer!.
  unff listrepf.
  Exists x y format_sigma sigma_pt.
  unfold mformat.
  Intros new_sigma new_pt.
  Exists tail_ptr new_format_pt new_sigma new_pt.
  entailer!.
Qed.

Lemma body_get_format_list_tail : semax_body Vprog Gprog f_get_format_list_tail get_format_list_tail_spec.
Proof.
  start_function.
  forward.
  forward_loop(
    EX i : Z, EX cur_tail : val,
    PROP(0 <= i < Zlength fs)
    LOCAL(temp _cur cur_tail; temp _fs p)
    SEP(
      lsegf (sublist 0 i fs) p cur_tail w h;
      listrepf (sublist i (Zlength fs) fs) cur_tail w h
    )
  ) break: (
    EX cur_tail : val,
    PROP()
    LOCAL(temp _cur cur_tail; temp _fs p)
    SEP(
      lsegf (sublist 0 (Zlength fs - 1) fs) p cur_tail w h;
      listrepf (sublist (Zlength fs - 1) (Zlength fs) fs) cur_tail w h
    )
  ).
  { Exists 0 p.
    entailer!.
    { destruct fs; list_solve. }
    autorewrite with sublist norm.
    unff lsegf.
    entailer!. }
  2: { 
    Intros cur_tail.
    forward.
    Exists cur_tail.
    entailer!. }
  Intros i cur_tail.
  replace (sublist i (Zlength fs) fs) with
    (Znth i fs :: sublist (i + 1) (Zlength fs) fs) by list_solve.
  unff listrepf.
  Intros x y format_sigma sigma_pt.
  forward.
  { entailer!; unnw; desf. }
  forward_if.
  2: {
    forward.
    Exists cur_tail.
    entailer!.
    unnw; desf.
    assert (sublist (i + 1) (Zlength fs) fs = []) as K by auto.
    assert (i = Zlength fs - 1) as F by list_solve.
    subst.
    replace (sublist (Zlength fs - 1) (Zlength fs) fs) with
      [Znth (Zlength fs - 1) fs] by list_solve.
    unff listrepf.
    Exists nullval y format_sigma sigma_pt.
    entailer!.
    replace (Zlength fs - 1 + 1) with (Zlength fs) by lia.
    autorewrite with sublist.
    unff listrepf; entailer!. }
  forward.
  Exists (i + 1) x.
  entailer!.
  { assert (i + 1 = Zlength fs \/ i + 1 < Zlength fs) as K by lia; desf.
    2: { lia. }
    unnw; desf.
    replace (i + 1) with (Zlength fs) in *.
    autorewrite with sublist in *.
    assert (x = nullval) by auto; ins. }
  assert(
    lsegf (sublist 0 i fs) p cur_tail w h *
    lsegf [Znth i fs] cur_tail x w h |--
    lsegf (sublist 0 (i + 1) fs) p x w h
  ) as K.
  { replace (sublist 0 (i + 1) fs) 
      with (sublist 0 i fs ++ [Znth i fs]) by list_solve.
    apply lsegf_lsegf. }
  eapply derives_trans.
  2: eauto.
  entailer!.
  unff lsegf.
  Exists x y format_sigma sigma_pt.
  entailer!.
Qed.

Lemma filter_good_format (fs : list t) (w h : Z):
  good_format_list fs w h ->
  filter (fun G => (height G <=? Z.to_nat h)%nat) fs = fs.
Proof.
  ins.
  revert dependent w.
  revert dependent h.
  induction fs; ins.
  desf.
  { f_equal.
    unfold good_format_list in H.
    apply (IHfs h w).
    apply Forall_cons_iff in H; desf. }
  unfold good_format_list in H.
  apply Forall_cons_iff in H.
  desf.
  unfold good_format in H.
  desf.
Qed.

Lemma good_format_app (fs1 fs2 : list t) (w h : Z):
  good_format_list fs1 w h ->
  good_format_list fs2 w h ->
  good_format_list (fs1 ++ fs2) w h.
Proof.
  ins.
  unfold good_format_list in *.
  apply Forall_app; auto.
Qed.

Lemma choice_doc_spec : semax_body Vprog Gprog f_choice_doc choice_doc_spec.
Proof.
  start_function.
  getnw.
  forward_if.
  { forward_call(fs2, p2, w, h, gv).
    Intros result_ptr.
    forward_call(fs2, p2, w, h, gv).
    forward.
    Exists result_ptr fs2.
    entailer!; unnw; desf.
    all: assert (fs1 = []) by auto.
    all: subst.
    2: { unff listrepf; entailer!. }
    unfold choiceDoc.
    autorewrite with sublist.
    rewrite (filter_good_format fs2 w h); vauto. }
  forward_if.
  { forward_call(fs1, p1, w, h, gv).
    Intros result_ptr.
    forward_call(fs1, p1, w, h, gv).
    forward.
    Exists result_ptr fs1.
    entailer!; unnw; desf.
    all: assert (fs2 = []) by auto.
    all: subst.
    2: { unff listrepf; entailer!. }
    unfold choiceDoc.
    autorewrite with sublist.
    rewrite (filter_good_format fs1 w h); vauto. }
  forward_call(fs1, p1, w, h, gv).
  Intros result_ptr.
  destruct fs1.
  { unff listrepf.
    Intros; desf. }
  forward_call((t :: fs1), w, h, result_ptr).
  remember (t :: fs1) as fs3.
  assert (0 < Zlength fs3) as K by list_solve.
  clear Heqfs3.
  clear fs1.
  remember fs3 as fs1.
  clear Heqfs1.
  clear fs3.
  Intros result_tail_ptr.
  forward_call(fs2, p2, w, h, gv).
  Intros fs2_new_ptr.
  replace ((sublist (Zlength fs1 - 1) (Zlength fs1) fs1)) 
    with [Znth (Zlength fs1 - 1) fs1] by list_solve.
  forward.
  forward_call(fs1, p1, w, h, gv).
  forward_call(fs2, p2, w, h, gv).
  forward.
  Exists result_ptr (fs1 ++ fs2).
  entailer!.
  2: {
    assert (
      lsegf fs1 result_ptr fs2_new_ptr w h *
      listrepf fs2 fs2_new_ptr w h |--
      listrepf (fs1 ++ fs2) result_ptr w h
    ) as F.
    { apply lsegf_listf. }
    eapply derives_trans.
    2: eauto.
    entailer!.
    assert(
      lsegf (sublist 0 (Zlength fs1 - 1) fs1) result_ptr result_tail_ptr w h *
      lsegf [Znth (Zlength fs1 - 1) fs1] result_tail_ptr fs2_new_ptr w h |--
      lsegf fs1 result_ptr fs2_new_ptr w h
    ) as G.
    { assert (fs1 = sublist 0 (Zlength fs1 - 1) fs1 ++ [Znth (Zlength fs1 - 1) fs1]) as GG by list_solve.
      rewrite GG at 5.
      apply lsegf_lsegf. }
    eapply derives_trans.
    2: eauto.
    entailer!.
    unff lsegf.
    Exists fs2_new_ptr y format_sigma sigma_pt.
    entailer!. }
  unfold choiceDoc.
  rewrite (filter_good_format (fs1 ++ fs2) w h); vauto.
  apply good_format_app; vauto.
Qed.


Lemma body_beside_doc : semax_body Vprog Gprog f_beside_doc beside_doc_spec.
Proof.
  start_function.
  forward_if(p1 <> nullval).
  { forward_if(
    PROP ( )
    LOCAL (gvars gv; temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h)); temp _fs1 p1; temp _fs2 p2)
    SEP (listrepf fs1 p1 w h; mem_mgr gv)).
    { forward_call(fs2, p2, w, h, gv); entailer!. }
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
  { forward_call(fs1, p1, w, h, gv).
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
      SEP (mem_mgr gv; listrepf fs1 p1 w h; lsegf (sublist 0 i fs2) p2 head_ptr w h; 
          listrepf (sublist i (Zlength fs2) fs2) head_ptr w h; lsegf res_part result_ptr result_tail_ptr w h;
          listrepf [empty] result_tail_ptr w h)) as loop_invariant eqn:eqn_loop.
  remember (
      EX result_tail_ptr : val, EX res_part : list t,
      PROP(res_part = filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))
      LOCAL(temp _has_item (Val.of_bool (0 <? Zlength res_part)); temp _result result_ptr; gvars gv;
            temp _result_tail result_tail_ptr;
            temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
            temp _fs1 p1; temp _fs2 p2)
      SEP (mem_mgr gv; listrepf fs1 p1 w h; listrepf fs2 p2 w h; lsegf res_part result_ptr result_tail_ptr w h;
          listrepf [empty] result_tail_ptr w h)) as break_invariant eqn:eqn_break.
  forward_loop(loop_invariant) break: (break_invariant).
  { subst.
    Exists 0 p2 result_ptr ([] : list t).
    entailer!.
    replace (sublist 0 0 fs2) with ([] : list t) by list_solve.
    assert (sublist 0 (Zlength fs2) fs2 = fs2) as K.
    { rewrite sublist_skip; vauto. }
    rewrite K.
    unff lsegf; entailer!; ins.
    unfold mformat.
    Intros sigma_list sigma_pt.
    unff listrepf.
    Exists nullval cur_empty_ptr sigma_list sigma_pt.
    unfold concrete_mformat.
    entailer!.
    getnw.
    inv FMT_MP.
    unfold empty in *; ins.
    unnw; unfold good_format; ins.
    assert (sigma_list = []) by list_solve; subst.
    list_solve. }
  2: { subst.
      Intros result_tail_ptr res_part.
      forward_call(fs1, p1, w, h, gv).
      forward_call(fs2, p2, w, h, gv).
      forward_if (
        Zlength res_part <> 0
      ).
      { destruct (0 <? Zlength res_part) eqn:E; vauto.
        forward_call([empty], result_ptr, w, h, gv).
        { desf; entailer!.
          replace ((filter (fun G : t => (height G <=? Z.to_nat h)%nat)
          (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))) with ([] : list t) by list_solve.
          unff lsegf; unff listrepf.
          entailer!; subst; unnw; entailer!.
          Exists nullval y format_sigma sigma_pt; entailer!. }
        forward.
        Exists nullval ([] : list t); entailer!.
        2: { unff listrepf; entailer!. }
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
        SEP(mem_mgr gv; lsegf (sublist 0 i res_part) result_ptr new_result_tail w h; 
            listrepf (sublist i (Zlength res_part) res_part ++ [empty]) new_result_tail w h)
      ) break: (
        EX new_result_tail : val,
        PROP()
        LOCAL(temp _new_result_tail new_result_tail; temp _fs1 p1; temp _fs2 p2; 
              temp _result_tail result_tail_ptr; gvars gv; temp _result result_ptr)
        SEP(mem_mgr gv; lsegf (sublist 0 (Zlength res_part - 1) res_part) result_ptr new_result_tail w h; 
            listrepf (sublist (Zlength res_part - 1) (Zlength res_part) res_part ++ [empty]) new_result_tail w h)).
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
        Intros ith_tail_ptr ith_format_ptr format_sigma sigma_pt.
        forward.
        { entailer!; getnw; desf. }
        assert (i + 1 = Zlength res_part \/ i + 1 < Zlength res_part) as K by lia.
        destruct K.
        { replace (sublist (i + 1) (Zlength res_part) res_part) with ([] : list t) by list_solve.
          autorewrite with sublist.
          unff listrepf.
          Intros nullval_tail_ptr empty_ptr format_sigma_empty sigma_pt_empty.
          forward.
          { unnw; subst; entailer!. }
          getnw; rewrite LIST_NULL_PTR.
          forward_if.
          { vauto. }
          forward.  
          entailer!.
          Exists new_result_tail_ptr.
          remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))
            as res_part.
          replace i with (Zlength res_part - 1) by lia.
          replace (sublist (Zlength res_part - 1) (Zlength res_part) res_part ++ [empty])
            with [Znth (Zlength res_part - 1) res_part; empty] by list_solve.
          unff listrepf.
          Exists ith_tail_ptr ith_format_ptr format_sigma sigma_pt.
          Exists nullval empty_ptr format_sigma_empty sigma_pt_empty.
          entailer!.
          unnw.
          list_solve. }
        replace (sublist (i + 1) (Zlength res_part) res_part)
          with (Znth (i + 1) res_part :: sublist (i + 2) (Zlength res_part) res_part) by list_solve.
        replace ((Znth (i + 1) res_part :: sublist (i + 2) (Zlength res_part) res_part) ++ [empty]) with
            (Znth (i + 1) res_part :: ((sublist (i + 2) (Zlength res_part) res_part ++ [empty]))) by list_solve.
        unff listrepf.
        Intros ithplus_tail_ptr ithplus_format_ptr ith_plus_sigma ith_plus_sigma_pt.
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
          Exists ithplus_tail_ptr ithplus_format_ptr ith_plus_sigma ith_plus_sigma_pt.
          entailer!.
          remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)).
          assert (
            lsegf (sublist 0 i l) result_ptr new_result_tail_ptr w h *
            lsegf [Znth i l] new_result_tail_ptr ith_tail_ptr w h |--
            lsegf (sublist 0 (i + 1) l) result_ptr ith_tail_ptr w h) as K.
          { replace (sublist 0 (i + 1) l) with (sublist 0 i l ++ [Znth i l]) by list_solve.
            eapply lsegf_lsegf. }
          eapply derives_trans.
          2: eauto.
          entailer!.
          unff lsegf; Exists ith_tail_ptr ith_format_ptr format_sigma sigma_pt.
          entailer!. }
        forward.
        replace ithplus_tail_ptr with nullval by vauto.
        destruct (sublist (i + 2) (Zlength res_part) res_part).
        { autorewrite with sublist norm.
          unff listrepf.
          Intros x y format_sigma0 sigma_pt0.
          entailer!. }
        replace (((t :: l) ++ [empty])) with (t :: (l ++ [empty])) by list_solve.
        unff listrepf.
        Intros x y format_sigma0 sigma_pt0.
        entailer!. }
    Intros new_result_tail.
    replace (sublist (Zlength res_part - 1) (Zlength res_part) res_part ++ [empty]) with 
        [Znth (Zlength res_part - 1) res_part; empty] by list_solve.
    unff listrepf.
    Intros empty_list_ptr last_format_ptr empty_sigma empty_sigma_ptr.
    Intros nullval_ptr empty_format_ptr format_sigma0 sigma_pt0.
    forward.
    forward_call([empty], empty_list_ptr, w, h, gv).
    { getnw; subst.
      unff listrepf.
      Exists nullval empty_format_ptr format_sigma0 sigma_pt0.
      entailer!. }
    do 2 forward.
    Exists result_ptr (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)).
    entailer!.
    remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)).
    assert (
      lsegf (sublist 0 (Zlength l - 1) l) result_ptr new_result_tail w h *
      listrepf [Znth (Zlength l - 1) l] new_result_tail w h |--
      listrepf l result_ptr w h
    ) as K.
    { assert(l = (sublist 0 (Zlength l - 1) l ++ [Znth (Zlength l - 1) l])) as KK by list_solve.
      rewrite KK at 5.
      apply lsegf_listf. }
    eapply derives_trans.
    2: eauto.
    unff listrepf.
    Exists nullval last_format_ptr empty_sigma empty_sigma_ptr.
    entailer!. }
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
        lsegf (sublist 0 j fs1) p1 head_ptr2 w h;
        listrepf (sublist j (Zlength fs1) fs1) head_ptr2 w h;
        lsegf (sublist 0 i fs2) p2 head_ptr w h; 
        listrepf (sublist i (Zlength fs2) fs2) head_ptr w h; 
        lsegf res_part_new result_ptr result_tail_ptr_new w h;
        listrepf [empty] result_tail_ptr_new w h)) as loop_invariant eqn:eqn_loop.
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
        listrepf fs1 p1 w h; 
        lsegf (sublist 0 i fs2) p2 head_ptr w h; 
        listrepf (sublist i (Zlength fs2) fs2) head_ptr w h; 
        lsegf res_part_new result_ptr result_tail_ptr_new w h;
        listrepf [empty] result_tail_ptr_new w h)) as break_invariant eqn:eqn_break.
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
  Intros ith_tail_ptr ith_format_ptr ith_sigma ith_sigma_pt.
  Intros nullval_ptr empty_ptr empty_sigma empty_sigma_pt.
  getnw; rewrite LIST_NULL_PTR.
  forward.
  { entailer!; unnw; desf. }
  Exists (i + 1) ith_tail_ptr result_tail_ptr_new res_part_new.
  entailer!.
  unff listrepf.
  Exists nullval empty_ptr empty_sigma empty_sigma_pt.
  entailer!.
  assert (
    lsegf (sublist 0 i fs2) p2 head_ptr w h *
    lsegf [Znth i fs2] head_ptr ith_tail_ptr w h |--
    lsegf (sublist 0 (i + 1) fs2) p2 ith_tail_ptr w h
  ) as K.
  { replace (sublist 0 (i + 1) fs2) with
      (sublist 0 i fs2 ++ [Znth i fs2]) by list_solve.
    apply lsegf_lsegf. }
  eapply derives_trans.
  2: eauto.
  entailer!.
  unff lsegf; entailer!.
  Exists ith_tail_ptr ith_format_ptr ith_sigma ith_sigma_pt.
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
Intros ith_tail_fs1_ptr ith_format_fs1_ptr fs1_sigma fs1_sigma_pt.
Intros ith_tail_fs2_ptr ith_format_fs2_ptr fs2_sigma fs2_sigma_pt.
Intros nullval_ptr empty_ptr empty_sigma empty_sigma_pt.
getnw; rewrite LIST_NULL_PTR.
forward.
{ entailer.
  unfold concrete_mformat.
  entailer!. }
forward.
{ entailer.
  unfold concrete_mformat.
  entailer!. }
unfold concrete_mformat.
Intros.
forward_call(Znth j fs1, Znth i fs2, 
    ith_format_fs1_ptr, ith_format_fs2_ptr, fs1_sigma, fs2_sigma, fs1_sigma_pt, fs2_sigma_pt, gv).
{ unfold concrete_mformat; entailer!. }
{ getnw; inv FMT_MP; inv GOOD_FORMAT.
  getnw; inv FMT_MP; inv GOOD_FORMAT.
  getnw; inv FMT_MP; inv GOOD_FORMAT.  
  split.
  { destruct (Znth j fs1); ins.
    destruct (Znth i fs2); ins.
    apply mk_format_comb; ins.
    all: unfold Int.max_unsigned in *.
    all: ins.
    all: lia. }
  assert (Forall (fun x => 0 <= fst x + Zlength (snd x) <= w) fs2_sigma) as FORALL2.
      { enough (list_max (map (fun x => Z.to_nat (fst x + Zlength (snd x))) fs2_sigma) <= Z.to_nat w)%nat.
        { apply list_max_impl_forall; vauto. }
        rewrite <- (total_width_eq (Znth i fs2)); vauto. }
  assert (Forall (fun x => 0 <= fst x + Zlength (snd x) <= w) fs1_sigma) as FORALL1.
      { enough (list_max (map (fun x => Z.to_nat (fst x + Zlength (snd x))) fs1_sigma) <= Z.to_nat w)%nat.
        { apply list_max_impl_forall; vauto. }
        rewrite <- (total_width_eq (Znth j fs1)); vauto. }
  split.
  { eapply beside_doc_llw_add.
    4: eauto.
    { lia. }
    3: {
      unfold total_width in *.
      desf; ins; lia. }
    all: inv format_mp_list_mp0.
    all: vauto. }
  eapply beside_doc_ab_pred.
  4: eauto.
  { lia. }
  all: vauto. }
Intros vret.
destruct vret as (vret_sigma, result_sigma_pt).
destruct vret_sigma as (result_format_ptr, result_sigma).
forward.
unfold concrete_mformat.
Intros.
forward_call(add_beside (Znth j fs1) (Znth i fs2), result_format_ptr, result_sigma, result_sigma_pt, w, h).
{ unfold concrete_mformat.
  entailer!.
  entailer!. }
Intros width_check_result.
forward_if(
  EX res_part_new : list t, EX result_tail_ptr_new : val,
  PROP(0 <= j <= Zlength fs1;
        res_part_new = res_part ++ filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) (sublist 0 (j + 1) fs1) [Znth i fs2]))
  LOCAL(temp _fs2_tail head_ptr; temp _fs1_tail head_ptr2;
        temp _has_item (Val.of_bool (0 <? Zlength res_part_new)); 
        temp _result result_ptr; gvars gv; 
        temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
        temp _fs1 p1; temp _fs2 p2; temp _result_tail result_tail_ptr_new)
  SEP (mem_mgr gv; 
      lsegf (sublist 0 j fs1) p1 head_ptr2 w h;
      listrepf (sublist j (Zlength fs1) fs1) head_ptr2 w h;
      lsegf (sublist 0 i fs2) p2 head_ptr w h; 
      listrepf (sublist i (Zlength fs2) fs2) head_ptr w h; 
      lsegf res_part_new result_ptr result_tail_ptr_new w h;
      listrepf [empty] result_tail_ptr_new w h)).
2: { forward.
     { entailer!; unnw; desf. }
     forward_call(result_sigma, result_sigma_pt, gv).
     forward_call(t_format, result_format_ptr, gv).
     { prove_ptr.
       entailer!. }
     Exists ((filter (fun G : t => (height G <=? Z.to_nat h)%nat)
              (besideDoc (Z.to_nat w) fs1 (sublist 0 i fs2)) ++
              filter (fun G : t => (height G <=? Z.to_nat h)%nat)
              (besideDoc (Z.to_nat w) (sublist 0 j fs1) [Znth i fs2]))) result_tail_ptr_new.
    entailer!.
     2: {
        unff listrepf.
        Exists nullval empty_ptr empty_sigma empty_sigma_pt.
        entailer!.  
        unff concrete_mformat.
        entailer!.
        replace (sublist j (Zlength fs1) fs1) with 
          (Znth j fs1 :: sublist (j + 1) (Zlength fs1) fs1) by list_solve.
        unff listrepf.
        Exists ith_tail_fs1_ptr ith_format_fs1_ptr fs1_sigma fs1_sigma_pt.
        unfold concrete_mformat.
        entailer!.
        replace (sublist i (Zlength fs2) fs2) with 
          (Znth i fs2 :: sublist (i + 1) (Zlength fs2) fs2) by list_solve.
        unff listrepf.
        Exists ith_tail_fs2_ptr ith_format_fs2_ptr fs2_sigma fs2_sigma_pt.
        unfold concrete_mformat.
        entailer!. }
    replace (sublist 0 (j + 1) fs1) with (sublist 0 j fs1 ++ [Znth j fs1]) by list_solve.
    rewrite <- beside_doc_app_l.
    apply app_inv_head_iff.
    rewrite filter_app.
    enough(
      filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) [Znth j fs1] [Znth i fs2]) = []
    ) as K.
    { rewrite K; list_solve. }
    unfold FormatTrivial.besideDoc.
    unfold FormatTrivial.cross_general.
    rewrite map_cons.
    rewrite concat_cons.
    rewrite map_nil.
    rewrite concat_nil.
    autorewrite with sublist norm.
    unfold filter.
    desf; vauto.
    lia. }
2: {
  Intros res_part_new0 result_tail_ptr_new0.
  replace (sublist j (Zlength fs1) fs1) with 
    (Znth j fs1 :: sublist (j + 1) (Zlength fs1) fs1) by list_solve.  
  unff listrepf.
  Intros ith_tail_fs1_ptr_new ith_format_fs1_ptr_new fs1_sigma_new fs1_sigma_pt_new.
  Intros empty_ptr_new empty_format_ptr_new empty_sigma_new empty_sigma_pt_new.
  forward.
  { entailer!; unnw; desf. }
  rewrite eqn_loop.
  Exists (j + 1) ith_tail_fs1_ptr_new result_tail_ptr_new0 res_part_new0.
  entailer!.
  unff listrepf.
  Exists empty_ptr_new empty_format_ptr_new empty_sigma_new empty_sigma_pt_new.
  unfold concrete_mformat.
  entailer!.
  assert (
    lsegf (sublist 0 j fs1) p1 head_ptr2 w h *
    lsegf [Znth j fs1] head_ptr2 ith_tail_fs1_ptr_new w h |--
    lsegf (sublist 0 (j + 1) fs1) p1 ith_tail_fs1_ptr_new w h
  ) as K.
  { replace (sublist 0 (j + 1) fs1) with
      (sublist 0 j fs1 ++ [Znth j fs1]) by list_solve.
    apply lsegf_lsegf. }
  eapply derives_trans.
  2: eauto.
  entailer!.
  unff lsegf.
  Exists ith_tail_fs1_ptr_new ith_format_fs1_ptr_new fs1_sigma_new fs1_sigma_pt_new.
  entailer!.
  unfold concrete_mformat.
  entailer!. } 
do 2 forward.
{ entailer!; unnw; desf. }
forward_call(empty_sigma, empty_sigma_pt, gv).
forward.
forward_call(t_format, empty_ptr, gv).
{ prove_ptr; entailer!. }
forward.
forward_call(t_flist, gv).
Intros new_result_tail_ptr.
do 2 forward.
dest_ptr new_result_tail_ptr.
forward_call(gv).
Intros new_empty_ptr.
do 6 forward.
Exists (filter (fun G : t => (height G <=? Z.to_nat h)%nat)
        (besideDoc (Z.to_nat w) fs1 (sublist 0 i fs2)) ++
        filter (fun G : t => (height G <=? Z.to_nat h)%nat)
        (besideDoc (Z.to_nat w) (sublist 0 (j + 1) fs1) [Znth i fs2])) new_result_tail_ptr.
entailer!.
2: { 
  unfold mformat.
  Intros sigma0 sigma_pt0.
  unff listrepf.
  Exists nullval new_empty_ptr sigma0 sigma_pt0.
  unfold concrete_mformat.
  entailer!.
  remember ((filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) fs1 (sublist 0 i fs2)))) as part1.
  remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) (sublist 0 j fs1) [Znth i fs2])) as part2.
  remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) (sublist 0 (j + 1) fs1) [Znth i fs2])) as part3.
  remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) [Znth j fs1] [Znth i fs2])) as part4.
  assert (part1 ++ part3 = (part1 ++ part2) ++ part4) as K.
  { rewrite <- app_assoc.
    apply app_inv_head_iff.
    vauto.
    replace (sublist 0 (j + 1) fs1) with (sublist 0 j fs1 ++ [Znth j fs1]) by list_solve.
    rewrite <- beside_doc_app_l.
    rewrite filter_app; vauto. }
  rewrite K.
  assert(
    listrepf (sublist j (Zlength fs1) fs1) head_ptr2 w h
    * listrepf (sublist i (Zlength fs2) fs2) head_ptr w h
    * lsegf (part1 ++ part2) result_ptr result_tail_ptr_new w h
    * lsegf part4 result_tail_ptr_new new_result_tail_ptr w h |--
    listrepf (sublist j (Zlength fs1) fs1) head_ptr2 w h
      * listrepf (sublist i (Zlength fs2) fs2) head_ptr w h
      * lsegf ((part1 ++ part2) ++ part4) result_ptr new_result_tail_ptr w h
  ) as FF.
  { entailer!.
    apply lsegf_lsegf. }
  eapply derives_trans.
  2: eauto.
  entailer!.
  unfold FormatTrivial.besideDoc.
  unfold FormatTrivial.cross_general.
  rewrite map_cons.
  rewrite map_nil.
  rewrite map_cons.
  rewrite map_nil.
  rewrite concat_cons.
  rewrite concat_nil.
  autorewrite with sublist.
  unfold filter.
  desf;
  assert (
    (total_width (add_beside (Znth j fs1) (Znth i fs2)) <= Z.to_nat w)%nat /\
      (height (add_beside (Znth j fs1) (Znth i fs2)) <= Z.to_nat h)%nat
  ) as GG by auto; desf.
  unff lsegf.
  Exists new_result_tail_ptr result_format_ptr result_sigma result_sigma_pt.
  entailer!.
  { unfold good_format; split; vauto. }
  unfold concrete_mformat; entailer!.
  assert (
    listrepf (sublist j (Zlength fs1) fs1) head_ptr2 w h
    * lsegf [Znth i fs2] head_ptr ith_tail_fs2_ptr w h
    * listrepf (sublist (i + 1) (Zlength fs2) fs2) ith_tail_fs2_ptr w h |--
    listrepf (sublist j (Zlength fs1) fs1) head_ptr2 w h
    * listrepf (sublist i (Zlength fs2) fs2) head_ptr w h
  ) as KK.
  { entailer!.
    replace (sublist i (Zlength fs2) fs2) 
      with ([Znth i fs2] ++ sublist (i + 1) (Zlength fs2) fs2) by list_solve.
    apply lsegf_listf. }
  eapply derives_trans.
  2: eauto.
  entailer!.
  unff lsegf.
  Exists ith_tail_fs2_ptr ith_format_fs2_ptr fs2_sigma fs2_sigma_pt.
  unfold concrete_mformat.
  entailer!.
  assert(
    lsegf [Znth j fs1] head_ptr2 ith_tail_fs1_ptr w h
    * listrepf (sublist (j + 1) (Zlength fs1) fs1) ith_tail_fs1_ptr w h |--
    listrepf (sublist j (Zlength fs1) fs1) head_ptr2 w h
  ) as KKK.
  { replace (sublist j (Zlength fs1) fs1) with
      ([Znth j fs1] ++ sublist (j + 1) (Zlength fs1) fs1) by list_solve.
    apply lsegf_listf. }
  eapply derives_trans.
  2: eauto.
  entailer!.
  unff lsegf.
  Exists ith_tail_fs1_ptr ith_format_fs1_ptr fs1_sigma fs1_sigma_pt.
  unfold concrete_mformat.
  entailer!. }
autorewrite with sublist norm.
desf.
remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) (sublist 0 j fs1) [Znth i fs2])) as part2.
remember ((filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) fs1 (sublist 0 i fs2)))) as part1.
remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) (sublist 0 (j + 1) fs1) [Znth i fs2])) as part3.
remember (filter (fun G : t => (height G <=? Z.to_nat h)%nat) (besideDoc (Z.to_nat w) [Znth j fs1] [Znth i fs2])) as part4.
assert (part3 = part2 ++ part4) as K.
{ vauto.
  replace (sublist 0 (j + 1) fs1) with (sublist 0 j fs1 ++ [Znth j fs1]) by list_solve.
  rewrite <- beside_doc_app_l.
  rewrite filter_app; vauto. }
rewrite K.
rewrite Zlength_app.
enough (Zlength part4 = 1) as KK. 
{ rewrite KK.
  assert(Zlength part1 + Zlength part2 + 1 > 0) as FF.
  { list_solve. }
  assert (0 <? Zlength part1 + (Zlength part2 + 1) = true) as GG.
  { lia. }
  rewrite GG.
  list_solve. }
vauto.
unfold besideDoc.
unfold cross_general.
rewrite map_cons.
rewrite map_nil.
rewrite map_cons.
rewrite map_nil.
rewrite concat_cons.
rewrite concat_nil.
autorewrite with sublist.
unfold filter.
desf;
assert (
  (total_width (add_beside (Znth j fs1) (Znth i fs2)) <= Z.to_nat w)%nat /\
    (height (add_beside (Znth j fs1) (Znth i fs2)) <= Z.to_nat h)%nat
) as GG by auto; desf.
Qed.