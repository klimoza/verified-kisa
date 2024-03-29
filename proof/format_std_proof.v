Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import Coq.Strings.Ascii.
Require Import format_specs.
Require Import list_specs.

Lemma body_max: semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function. 
  forward_if; forward.
  { Exists b; entailer!. }
  Exists a; entailer!.
Qed.

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
  start_function.
  unfold cstring in *; Intros.
  forward.

  forward_loop(
    EX i : Z,
    PROP (0 <= i < Zlength s + 1)
    LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
    SEP (cstring sh s str)
  ).
  { Exists 0; unfold cstring; entailer. }
  Intros i. 
  unfold cstring; Intros.
  forward; forward_if; forward; entailer!. 
  { list_solve. }
  Exists (i + 1).
  unfold cstring; entailer!.
  list_solve.
Qed.

Lemma body_strcpy : semax_body Vprog Gprog f_strcpy strcpy_spec.
Proof.
  start_function.
  unfold cstring.
  forward.
  forward_loop (EX i : Z,
    PROP (0 <= i < Zlength s + 1)
    LOCAL (temp _i (Vptrofs (Ptrofs.repr i)); temp _dest dest; temp _src src)
    SEP (data_at wsh (tarray tschar n) (map Vbyte (sublist 0 i s) ++ Zrepeat Vundef (n - i)) dest;
         cstring rsh s src)).
  { Exists 0; unfold cstring; entailer. }
  Intros i; unfold cstring; Intros.
  do 3 forward; forward_if.
  { forward. 
    unfold cstring, cstringn; entailer!.
    apply derives_refl'; f_equal.
    list_solve. }
  unfold cstring; forward.
  Exists (i + 1); entailer!.
  2: { rewrite upd_Znth_app2.
       all: list_solve. }
  list_solve.
Qed.

Lemma body_strcat: semax_body Vprog Gprog f_strcat strcat_spec.
Proof.
  leaf_function.
  start_function.
  unfold cstringn, cstring in *.
  forward.
  forward_loop(
    EX i : Z,
    PROP (0 <= i < Zlength b + 1)
    LOCAL (temp _i (Vptrofs (Ptrofs.repr i)); temp _dest dest; temp _src src)
    SEP (cstringn wsh b n dest; cstring rsh s src)) 
    break: (
    PROP ()
    LOCAL (temp _i (Vptrofs (Ptrofs.repr (Zlength b))); temp _dest dest; temp _src src)
    SEP (cstringn wsh b n dest; cstring rsh s src)).
  { Exists 0. 
    unfold cstringn, cstring; entailer!. }
  { unfold cstringn, cstring.
    Intros i; forward.
    { entailer!. }
    { entailer!; list_solve. }
    autorewrite with sublist norm.
    forward; forward_if; forward.
    { unfold cstringn, cstring; entailer!.
       do 2 f_equal; list_solve. }
    Exists (i + 1).
    unfold cstringn, cstring; entailer!; list_solve. }
  unfold cstringn, cstring.
  forward.
  autorewrite with sublist norm in *.
  forward_loop(
    EX j : Z,
    PROP (0 <= j < Zlength s + 1)
    LOCAL (temp _i (Vptrofs (Ptrofs.repr (Zlength b)));
           temp _j (Vptrofs (Ptrofs.repr j));
           temp _dest dest; temp _src src)
    SEP (data_at wsh (tarray tschar n) (map Vbyte (b ++ sublist 0 j s) ++  Zrepeat Vundef (n - (Zlength b + j))) dest; 
         cstring rsh s src)).
  { Exists 0. 
    unfold cstring, cstringn. 
    autorewrite with sublist norm; entailer!; list_solve. }
  Intros j.
  unfold cstringn, cstring.
  autorewrite with sublist norm in *.
  do 3 forward.
  { entailer!. }
  forward_if.
  { forward; entailer!.
    { assert (In Byte.zero b \/ In Byte.zero s) as K.
      { apply in_app_or; ins. }
      desf. }
    list_solve. }
  forward.
  Exists (j + 1).
  entailer!.
  { list_solve. }
  unfold cstringn, cstring.
  entailer!; list_solve.
Qed.

Lemma list_copy_length_fact:
  forall (A : Type) (t : list A),
  Z.to_nat (Zlength t) = Datatypes.length t.
Proof.
  intros.
  induction t.
  { list_solve. }
  rewrite Zlength_cons. simpl. 
  rewrite <- IHt. list_solve.
Qed.

Definition list_copy_loop_invariant 
  (l new_pointer : val)
  (sigma : list (Z * list byte))
  (gv: globals) : environ -> mpred :=
  EX i : Z, EX cur : val, EX l_cur : val,
          PROP(0 <= i < Zlength sigma + 1;
               cur <> nullval;
               l_cur <> nullval)
            LOCAL(temp _new new_pointer; 
                  temp _l l;
                  temp _cur cur; 
                  temp _l_cur l_cur; 
                  gvars gv)
            SEP(malloc_token Ews t_list cur;
                data_at_ Ews t_list cur;
                lseg (sublist 0 i sigma) new_pointer cur; 
                lseg (sublist 0 i sigma) l l_cur;
                listrep (sublist i (Zlength sigma) sigma) l_cur;
                mem_mgr gv).


Lemma body_list_copy: semax_body Vprog Gprog f_list_copy list_copy_spec.
Proof.
  start_function.
  forward_if(l <> nullval). 
  { forward. Exists nullval. entailer!. getnw.
    desc. assert (nullval = nullval) as Trivial by auto.
    apply LIST_PTR_FACT0 in Trivial.
    subst.
    unfold listrep. entailer!. }
  { forward. entailer!. }

  forward_call(t_list, gv).
  Intros new_pointer.
  destruct (eq_dec new_pointer nullval). 
  { forward_if(new_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    forward. contradiction. }

  forward_if(new_pointer <> nullval).
  { forward_call. entailer!. }
  { forward. entailer!. }

  Intros. do 2 forward.
  
  forward_loop (
    list_copy_loop_invariant l new_pointer sigma gv
  ) break: (
    PROP()
    LOCAL(temp _new new_pointer; gvars gv)
    SEP(listrep sigma new_pointer; listrep sigma l; mem_mgr gv)
  ).
  3: { forward. Exists new_pointer. entailer!. }
  { Exists 0 new_pointer l.
    entailer!.
    replace (sublist 0 0 sigma) with ([] : list (Z * list byte)) by list_solve.
    unfold lseg.
    replace (sublist 0 (Zlength sigma) sigma) with sigma by list_solve.
    entailer!.
  }
  
  unfold list_copy_loop_invariant.
  Intros i cur l_cur.
  destruct (eq_dec i (Zlength sigma)) as [ | I_is_not_zlength]. 
  { subst.
    replace ((sublist (Zlength sigma) (Zlength sigma) sigma)) with ([] : list (Z * list byte)) by list_solve.
    unfold listrep; fold listrep. 
    Intros. contradiction.
  }

replace (sublist i (Zlength sigma) sigma) with 
  (Znth i sigma :: sublist (i + 1) (Zlength sigma) sigma) by list_solve.
unfold listrep; fold listrep.
remember (Znth i sigma) as ith_element eqn:eqn_ith_element.
destruct ith_element as (shift_i, line_i).

Intros l_cur_tail line_i_pointer.

do 3 forward.
forward_call(Ews, line_i, line_i_pointer).
forward_call((Tarray tschar (Zlength line_i + 1) noattr), gv). {
  assert (In (shift_i, line_i) sigma) as In_fact. 
  { rewrite eqn_ith_element. apply Znth_In. lia. }

  assert (Zlength line_i + 1 <= Int.max_unsigned) as Zlength_fact. {
    remember (fun x : Z * list byte =>
    0 <= fst x <= Int.max_unsigned /\
    0 <= Zlength (snd x) + 1 <= Int.max_unsigned) as List_condition.
    assert (List_condition (shift_i, line_i)) as Ith_condition. 
    { apply (computable_theorems.Forall_forall1 _ sigma); auto. }
    rewrite HeqList_condition in Ith_condition.
    destruct Ith_condition as [shift_condition].
    simpl in *. lia. }

  unfold sizeof. unfold Ctypes.sizeof.
  unfold Int.max_unsigned in Zlength_fact. simpl in Zlength_fact.
  unfold Ptrofs.max_unsigned. simpl.
  lia. }

Intros cur_line_i_pointer.
destruct (eq_dec cur_line_i_pointer nullval). 
{ do 2 forward.
  forward_if(cur_line_i_pointer <> nullval).
  { forward_call. entailer!. }
  { forward. entailer!. }
  forward. contradiction. }

Intros. do 2 forward.
forward_if(cur_line_i_pointer <> nullval).
{ forward_call. entailer!. }
{ forward. entailer!. }

do 2 forward.
forward_call(Ews, Ews, cur_line_i_pointer, Zlength line_i + 1, line_i_pointer, line_i).
do 2 forward.
{ entailer!. getnw. desf. }

forward_if(l_cur_tail <> nullval). 
{ do 2 forward.
  entailer!.
  rewrite <- cstringn_equiv.
  assert (i + 1 = Zlength sigma) as AA.
  { assert (i + 1 < Zlength sigma \/ i + 1 = Zlength sigma) as BB
        by lia.
    destruct BB as [BB|BB]; auto.
    replace (sublist (i + 1) (Zlength sigma) sigma) 
      with (Znth (i + 1) sigma :: (sublist (i + 2) (Zlength sigma) sigma)) in * by list_solve.
    unnw.
    desf.
    assert(Znth (i + 1) sigma :: sublist (i + 2) (Zlength sigma) sigma = []) as CC by auto.
    inversion CC. }
  rewrite AA.
  replace (sublist (Zlength sigma) (Zlength sigma) sigma) with ([] : list (Z * list byte)) by list_solve.
  unfold listrep; fold listrep.
  
  entailer!.

  assert (
    cstring Ews line_i cur_line_i_pointer 
      * cstring Ews line_i line_i_pointer
      * malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
      * malloc_token Ews t_list cur
      * data_at Ews t_list (Vlong (Int64.repr shift_i), (cur_line_i_pointer, Vlong (Int64.repr 0))) cur
      * lseg (sublist 0 i sigma) new_pointer cur
      * lseg (sublist 0 i sigma) l l_cur
      * malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer
      * malloc_token Ews t_list l_cur
      * data_at Ews t_list (Vlong (Int64.repr shift_i), (line_i_pointer, nullval)) l_cur
    |-- 
    (lseg (sublist 0 i sigma) new_pointer cur *
    (
      malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
      * cstring Ews line_i cur_line_i_pointer 
      * malloc_token Ews t_list cur
      * data_at Ews t_list (Vlong (Int64.repr shift_i), (cur_line_i_pointer, Vlong (Int64.repr 0))) cur
    )) * (
      lseg (sublist 0 i sigma) l l_cur *
      (
      malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer
      * cstring Ews line_i line_i_pointer
      * malloc_token Ews t_list l_cur
      * data_at Ews t_list (Vlong (Int64.repr shift_i), (line_i_pointer, nullval)) l_cur
      )
    )
  ) as Trans_step1. 
  { entailer!. }

  eapply derives_trans; eauto. 
  apply sepcon_derives. 
  { assert (sigma = sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) as FF by list_solve.
    rewrite FF.
    assert (
      lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) new_pointer cur
       * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
       * cstring Ews line_i cur_line_i_pointer
       * malloc_token Ews t_list cur
       * data_at Ews t_list (Vlong (Int64.repr shift_i), (cur_line_i_pointer, Vlong (Int64.repr 0))) cur)
       |-- 
      lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) new_pointer cur *
      listrep [(shift_i, line_i)] cur
    ) as Trans_step2. {
      unfold listrep; fold listrep.
      Exists nullval cur_line_i_pointer.
      entailer!. }

    eapply derives_trans; eauto.
    rewrite eqn_ith_element.
    replace [Znth i sigma] with (sublist i (Zlength sigma) sigma) by list_solve.
    replace (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) with sigma at 1 by list_solve.
    apply lseg_list. }
  assert (sigma = sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) as FF by list_solve.
  rewrite FF.
  assert (
      lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) l l_cur
      * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer
         * cstring Ews line_i line_i_pointer
         * malloc_token Ews t_list l_cur
         * data_at Ews t_list (Vlong (Int64.repr shift_i), (line_i_pointer, nullval)) l_cur)
          |-- 
          lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) l l_cur *
        listrep [(shift_i, line_i)] l_cur
    ) as Trans_step2.
  { unfold listrep; fold listrep.
    Exists nullval line_i_pointer.
    entailer!. }

  eapply derives_trans; eauto.
  rewrite eqn_ith_element.
  replace [Znth i sigma] with (sublist i (Zlength sigma) sigma) by list_solve.
  replace (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) with sigma at 1 by list_solve.
  apply lseg_list. }
  { forward. entailer!. }
  Intros.
  forward_call(t_list, gv).
  Intros cur_tail.
  do 2 forward.
  destruct (eq_dec cur_tail nullval). 
  { forward_if(cur_tail <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    forward. contradiction. }
  forward_if(cur_tail <> nullval). 
  { forward_call. entailer!. }
  { forward. entailer!. }
  Intros.

  do 2 forward.
  Exists (i + 1) cur_tail l_cur_tail.
  entailer!.
  rewrite <- cstringn_equiv.

  assert (
    cstring Ews line_i cur_line_i_pointer * cstring Ews line_i line_i_pointer
    * malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
    * malloc_token Ews t_list cur
    * data_at Ews t_list (Vlong (Int64.repr shift_i), (cur_line_i_pointer, cur_tail)) cur
    * lseg (sublist 0 i sigma) new_pointer cur
    * lseg (sublist 0 i sigma) l l_cur
    * malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer
    * malloc_token Ews t_list l_cur
    * data_at Ews t_list (Vlong (Int64.repr shift_i), (line_i_pointer, l_cur_tail)) l_cur
    |--
    (lseg (sublist 0 i sigma) new_pointer cur
    * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
    * cstring Ews line_i cur_line_i_pointer
    * malloc_token Ews t_list cur
    * data_at Ews t_list (Vlong (Int64.repr shift_i), (cur_line_i_pointer, cur_tail)) cur))
    * (lseg (sublist 0 i sigma) l l_cur
    * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer
    * cstring Ews line_i line_i_pointer
    * malloc_token Ews t_list l_cur
    * data_at Ews t_list (Vlong (Int64.repr shift_i), (line_i_pointer, l_cur_tail)) l_cur))
  ) as AA by entailer!.
  
  eapply derives_trans; eauto.
  apply sepcon_derives. {
    clear AA.
    assert (
      lseg (sublist 0 i sigma) new_pointer cur
       * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
       * cstring Ews line_i cur_line_i_pointer
       * malloc_token Ews t_list cur
       * data_at Ews t_list (Vlong (Int64.repr shift_i), (cur_line_i_pointer, cur_tail)) cur)
      |-- 
      lseg (sublist 0 i sigma) new_pointer cur * 
      lseg (sublist i (i + 1) sigma) cur cur_tail
    ). 
    { apply sepcon_derives. entailer.
      replace (sublist i (i + 1) sigma) with [Znth i sigma] by list_solve.
      unfold lseg.
      rewrite <- eqn_ith_element.
      Exists cur_tail cur_line_i_pointer.
      entailer!. }
    eapply derives_trans; eauto.
    replace (sublist 0 (i + 1) sigma) with (sublist 0 i sigma ++ sublist i (i + 1) sigma) by list_solve.
    apply lseg_lseg. }
  clear AA.
  assert (
      lseg (sublist 0 i sigma) l l_cur
      * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer
         * cstring Ews line_i line_i_pointer
         * malloc_token Ews t_list l_cur
         * data_at Ews t_list (Vlong (Int64.repr shift_i), (line_i_pointer, l_cur_tail)) l_cur)
          |-- 
          lseg (sublist 0 i sigma) l l_cur * 
        lseg (sublist i (i + 1) sigma) l_cur l_cur_tail
    ).
  { apply sepcon_derives. entailer.
    replace (sublist i (i + 1) sigma) with [Znth i sigma] by list_solve.
    unfold lseg.
    rewrite <- eqn_ith_element.
    Exists l_cur_tail line_i_pointer.
    entailer!. }
  eapply derives_trans; eauto.
  replace (sublist 0 (i + 1) sigma) with (sublist 0 i sigma ++ sublist i (i + 1) sigma) by list_solve.
  apply lseg_lseg.
Qed.

Lemma body_list_concat: semax_body Vprog Gprog f_list_concat list_concat_spec.
Proof.
  start_function.
  forward_call(p1, l1).
  Intros l1_tail.
  replace (sublist (Zlength l1 - 1) (Zlength l1) l1) with 
    ([Znth (Zlength l1 - 1) l1]).
  2: {
    rewrite sublist_next.
    3: lia.
    2: { destruct l1; list_solve. }
    list_solve. }
  unff listrep.
  remember (Znth (Zlength l1 - 1) l1) as l1_last.
  destruct l1_last as (l1_shift_last, l1_line_last).
  Intros l1_tail_ptr l1_line_ptr.
  do 2 forward.
  remember (lseg_list l1 l2 p1 p2).
  eapply derives_trans.
  2: eauto.
  entailer!.
  remember (lseg_lseg (sublist 0 (Zlength l1 - 1) l1) [Znth (Zlength l1 - 1) l1] p1 l1_tail p2).
  assert (Zlength l1 > 0).
  { destruct l1; list_solve. }
  assert (l1 = (sublist 0 (Zlength l1 - 1) l1 ++ [Znth (Zlength l1 - 1) l1])) as I by list_solve.
  rewrite I at 3.
  eapply derives_trans.
  2: eauto.
  entailer!.
  unff lseg.
  rewrite <- Heql1_last.
  Exists p2 l1_line_ptr.
  entailer!.
Qed.

Lemma body_get_list_tail: semax_body Vprog Gprog f_get_list_tail get_list_tail_spec.
Proof.
  start_function.
  forward.
  forward_loop(
    EX i : Z, EX q : val,
    PROP (0 <= i < Zlength sigma)
    LOCAL (temp _cur q; temp _l p)
    SEP(
      lseg (sublist 0 i sigma) p q;
      listrep (sublist i (Zlength sigma) sigma) q
    )
  ) break: (
    EX q : val,
    PROP()
    LOCAL(temp _cur q; temp _l p)
    SEP(lseg (sublist 0 (Zlength sigma - 1) sigma) p q;
        listrep (sublist (Zlength sigma - 1) (Zlength sigma) sigma) q)
  ).
  { Exists 0 p. 
    destruct sigma.
    { vauto. }
    entailer!.
    { list_solve. }
    replace ((sublist 0 0 (p0 :: sigma))) with ([] : list (Z * list byte)) by list_solve.
    unff lseg.
    replace (sublist 0 (Zlength (p0 :: sigma)) (p0 :: sigma)) with
        (p0 :: sigma) by list_solve.
    entailer!. }
  2: {
    Intros q.
    forward.
    Exists q.
    entailer!. }
  Intros i q.
  replace (sublist i (Zlength sigma) sigma) with (Znth i sigma :: sublist (i + 1) (Zlength sigma) sigma)
    by list_solve.
  unff listrep.
  remember (Znth i sigma) as ith_element.
  destruct ith_element as (ith_shift, ith_line).
  Intros ith_tail ith_line_ptr.
  forward.
  prove_ptr.
  forward_if.
  { forward.
    Exists (i + 1) ith_tail.
    assert(i + 1 = Zlength sigma \/ i + 1 < Zlength sigma) as F by lia.
    destruct F.
    { replace (sublist (i + 1) (Zlength sigma) sigma) with ([] : list (Z * list byte))
          by list_solve.
      unff listrep.
      entailer!. }
    entailer!.
    assert(
      lseg (sublist 0 i sigma) p q *
      lseg (sublist i (i + 1) sigma) q ith_tail
      |--
      lseg (sublist 0 (i + 1) sigma) p ith_tail
    ) as K.
    { replace (sublist 0 (i + 1) sigma) with (sublist 0 i sigma ++ sublist i (i + 1) sigma)
        by list_solve.
      apply lseg_lseg. }
    eapply derives_trans.
    2: eauto.
    replace (sublist i (i + 1) sigma) with [Znth i sigma] by list_solve.
    unff lseg.
    rewrite <- Heqith_element.
    Exists ith_tail ith_line_ptr.
    entailer!. }
  forward.
  Exists q.
  entailer!.
  assert(i + 1 < Zlength sigma \/ i + 1 = Zlength sigma) as F by lia.
  destruct F.
  { unnw; desf.
    assert (sublist (i + 1) (Zlength sigma) sigma = []) as K by auto.
    replace (sublist (i + 1) (Zlength sigma) sigma) with 
      (Znth (i + 1) sigma :: sublist (i + 2) (Zlength sigma) sigma) in K by list_solve.
    vauto. }
  replace i with (Zlength sigma - 1) in * by lia.
  entailer!.
  replace (sublist (Zlength sigma - 1) (Zlength sigma) sigma) with [Znth (Zlength sigma - 1) sigma]
    by list_solve.
  replace (sublist (Zlength sigma - 1 + 1) (Zlength sigma) sigma) with ([] : list (Z * list byte))
    by list_solve.
  unff listrep.
  rewrite <- Heqith_element.
  Exists nullval ith_line_ptr.
  entailer!.
Qed.