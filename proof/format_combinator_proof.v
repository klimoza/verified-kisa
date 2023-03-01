Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import Coq.Strings.Ascii.
Require Import format_specs.
Require Import format_std_proof.
Require Import format_proof.

Lemma eq_and_true_impl (n a m b : nat):
  ((n =? a)%nat && (m =? b)%nat)%bool = true ->
  n = a /\ m = b.
Proof.
  intros AA.
  apply andb_true_iff in AA.
  destruct AA.
  split; apply Nat.eqb_eq; auto.
Qed.

Lemma int_repr_eq (n m : nat):
  0 <= Z.of_nat n <= Int.max_unsigned ->
  0 <= Z.of_nat m <= Int.max_unsigned ->
  Int.repr (Z.of_nat n) = Int.repr (Z.of_nat m) ->
  m = n.
Proof.
  intros.
  assert(Z.of_nat n = Z.of_nat m).
  { apply mapsto_memory_block.repr_inj_unsigned; list_solve. }
  list_solve.
Qed.

Lemma body_mdw_add_above: semax_body Vprog Gprog f_mdw_add_above mdw_add_above_spec.
Proof.
  start_function.
  forward.
  getnw; destruct FMT_MP.
  forward_if(height G <> 0%nat).
  { do 2 forward.
    unfold concrete_mformat.
    entailer!.
    unfold add_above.
    replace (height G) with 0%nat by list_solve.
    split.
    2: { split; auto; apply mk_format_mp; auto. }
    getnw; destruct FMT_MP.
    lia. }
  { forward; entailer!. }
  forward.
  getnw; destruct FMT_MP.
  forward_if(height F <> 0%nat).
  { do 2 forward.
    unfold concrete_mformat.
    entailer!.
    unfold add_above.
    destruct (height G) eqn:E.
    { lia. }
    replace (height F) with 0%nat by list_solve.
    split.
    { lia. }
    split; auto.
    split; apply mk_format_mp; try rewrite E; auto. }
  { forward; entailer!. }

  forward.
  remember (fun (tr: ident) (b: bool) =>
    PROP()
    LOCAL(temp tr (Val.of_bool b); temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF))
  as if_invariant eqn:eqn_if_invariant.
    
  forward_if(
    if_invariant _t'12 ((height G =? 1)%nat && (height F =? 1)%nat)%bool
  ).
  { do 2 forward.
    rewrite eqn_if_invariant.
    entailer!.
    { replace (height G) with 1%nat.
      { ins; f_equal.
        apply nat_eq_iff_int_eq; list_solve. }
      list_solve.
    }
    unfold concrete_mformat.
    entailer!.
    split; apply mk_format_mp; auto.
  }
  { forward. rewrite eqn_if_invariant.
    entailer!.
    { assert (height G <> 1)%nat by list_solve.
      replace (height G =? 1)%nat with false.
      { list_solve. }
      symmetry. apply Nat.eqb_neq. auto.
     }
     unfold concrete_mformat.
     entailer!.
    split; apply mk_format_mp; auto.
  }

  remember (
    PROP(0 <= Z.of_nat (middle_width (add_above G F)) <= Int.max_unsigned)
    LOCAL(temp _middle_width_new (Vint (Int.repr (Z.of_nat (middle_width (add_above G F))))); 
          temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  ) as middle_invariant eqn:eqn_middle_invariant.
  rewrite eqn_if_invariant.
  forward_if(middle_invariant).
  { forward.
    rewrite eqn_middle_invariant.
    entailer!.
    2: now unfold concrete_mformat; entailer!. 
    do 3 f_equal.
    assert(AA: (height G = 1)%nat /\ (height F = 1)%nat).
    { apply eq_and_true_impl; auto. }
    destruct AA.
    unfold add_above.
    destruct (height G) as [ | hG].
    { lia. }
    destruct (height F) as [ | hF].
    { lia. }
    destruct hG.
    2: now lia.
    destruct hF.
    2: now lia.
    auto.
  }
  { forward.
    getnw. destruct FMT_MP.

    forward_if(
      if_invariant _t'11 ((height G =? 1)%nat && negb (height F =? 1)%nat)%bool
    ).
    { do 2 forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      f_equal.
      replace (height G) with 1%nat.
      { simpl. f_equal.
        apply nat_eq_iff_int_eq; list_solve.
      }
      apply int_repr_eq; list_solve.
    }
    { forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      assert (height G <> 1)%nat by list_solve.
      replace (height G =? 1)%nat with false.
      { list_solve. }
      symmetry. apply Nat.eqb_neq; auto.
    }
    rewrite eqn_if_invariant.

    forward_if(middle_invariant).
    { do 2 forward.
      forward_call(Z.of_nat (first_line_width F), Z.of_nat (middle_width F)).
      Intros max.
      forward.
      rewrite eqn_middle_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      do 3 f_equal.
      unfold add_above.
      destruct (height G) as [| hG].
      { lia. }
      destruct (height F) as [| hF].
      { lia. }
      destruct hG as [| hG].
      2: { simpl in *. lia. }
      destruct hF as [| hF].
      { simpl in *. lia. }
      simpl. list_solve.
    }

    forward.
    forward_if(
      if_invariant _t'10 ((height G =? 2)%nat && ((height F) =? 1)%nat)%bool
    ).
    { do 2 forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      f_equal.
      replace (height G) with 2%nat by list_solve.
      simpl.
      apply nat_eq_iff_int_eq; list_solve.
    }
    { forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      replace (height G =? 2)%nat with false.
      { simpl. list_solve. }
      symmetry. apply Nat.eqb_neq; list_solve.
    }

    rewrite eqn_if_invariant.
    forward_if(middle_invariant).
    { forward.
      rewrite eqn_middle_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      do 3 f_equal.
      unfold add_above.
      destruct (height G) as [| hG].
      { lia. }
      destruct (height F) as [| hF].
      { lia. }
      destruct hG as [| hG].
      { simpl in *. lia. }
      destruct hG.
      2: { simpl in *. lia. }
      destruct hF; ins. }

    forward.
    forward_if(
      if_invariant _t'9 ((height F =? 1)%nat && negb ((height G) =? 1)%nat)%bool
    ).
    { do 2 forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      f_equal.
      replace (height G =? 1)%nat with false.
      { simpl. ring_simplify. 
        apply nat_eq_iff_int_eq; list_solve.
      }
      symmetry. apply Nat.eqb_neq; list_solve.
    }
    { forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      replace (height G) with 1%nat by list_solve.
      simpl.
      assert ((height F =? 1)%nat && false = false)%bool as E.
      { ring_simplify. auto. }
      rewrite E. list_solve.
    }
    rewrite eqn_if_invariant.

    forward_if(middle_invariant).
    { do 2 forward.
      forward_call(Z.of_nat (last_line_width G), Z.of_nat (middle_width G)).
      Intros max.
      forward.
      rewrite eqn_middle_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      do 2 f_equal.
      unfold add_above.
      destruct (height G) as [| hG].
      { lia. }
      destruct (height F) as [| hF].
      { lia. }
      destruct hG as [| hG].
      { simpl in *. lia. }
      destruct hF as [| hF].
      2: { simpl in *. lia. }
      destruct hG; ins; split; try lia; list_solve. }
    
    forward.
    forward_if(
      if_invariant _t'8 ((height G =? 2)%nat && negb ((height F) =? 1)%nat)%bool
    ).
    { do 2 forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      f_equal.
      replace (height G) with 2%nat by list_solve.
      simpl. f_equal.
      apply nat_eq_iff_int_eq; list_solve.
    }
    { forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      replace (height G =? 2)%nat with false.
      { simpl. list_solve. }
      symmetry. apply Nat.eqb_neq; list_solve.
    }
    rewrite eqn_if_invariant.
    
    forward_if(middle_invariant).
    { do 2 forward.
      forward_call(Z.of_nat (first_line_width F), Z.of_nat (middle_width F)).
      Intros max1.
      forward.
      forward_call(Z.of_nat (last_line_width G), max1).
      Intros max2.
      forward.
      rewrite eqn_middle_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      do 2 f_equal.
      unfold add_above.
      destruct (height G) as [| hG]; vauto.
      destruct (height F) as [| hF]; vauto.
      destruct hG as [| hG]; vauto.
      destruct hF as [| hF]; vauto.
      destruct hG as [| hG]; vauto; ins; list_solve. }
    do 2 forward.
    forward_call(Z.of_nat (first_line_width F), Z.of_nat (middle_width F)).
    Intros max1.
    forward.
    forward_call(Z.of_nat (last_line_width G), max1).
    Intros max2.
    forward.
    forward_call(Z.of_nat (middle_width G), max2).
    Intros max.
    forward.
    rewrite eqn_middle_invariant.
    entailer!.
    2: now unfold concrete_mformat; entailer!.
    do 2 f_equal.
    unfold add_above.
    destruct (height G) as [| hG]; vauto.
    destruct (height F) as [| hF]; vauto.
    destruct hG as [| hG].
    { ins; replace (hF =? 0)%nat with false in *; lia. }
    destruct hG as [| hG].
    { ins; replace (hF =? 0)%nat with false in *; lia. }
    destruct hF as [| hF]; vauto.
    ins; list_solve. }
  
  rewrite eqn_middle_invariant.
  forward.
Qed.


Lemma text_from_concat_add_above (sigmaG sigmaF : list (Z * list byte)) (G F : t) (shift : nat) (line : string):
  sigmaG <> [] -> sigmaF <> [] ->
  to_text_eq (to_text G) sigmaG -> to_text_eq (to_text F) sigmaF ->
  string_to_list_byte
  (to_text G shift
     (String (ascii_of_pos 10) (sp shift ++ to_text F shift line))) = 
  text_from (sigmaG ++ sigmaF) shift line.
Proof.
  intros G_not_nil F_not_nil EQG EQF.
  unfold to_text_eq in *.
  rewrite EQG. 
  clear EQG G.
  rewrite text_from_line; auto.
  rewrite text_from_concat; auto.
  assert (string_to_list_byte (String (ascii_of_pos 10) (sp shift ++ to_text F shift line)) =
    [Byte.repr 10] ++ string_to_list_byte (sp shift) ++ string_to_list_byte (to_text F shift line)
  ) as K.
  { simpl.
    rewrite string_to_list_byte_app.
    auto. }
  rewrite K.
  rewrite EQF.
  do 2 apply app_inv_head_iff.
  rewrite text_from_line; auto.
  rewrite sp_eq_sp_byte.
  rewrite <- text_from_shifted_text_from_iff; auto; list_solve.
Qed.
  
Lemma body_to_text_add_above: semax_body Vprog Gprog f_to_text_add_above to_text_add_above_spec.
Proof.
  start_function.
  forward.
  getnw; destruct FMT_MP.
  forward_if(height G <> 0%nat).
  { forward.
    prove_ptr.
    getnw; destruct FMT_MP.
    forward_call(Ews, pF, sigmaF, gv).
    { destruct format_mp_list_mp0; list_solve. }
    Intros new_format_ptr.
    forward.
    Exists new_format_ptr sigmaF.
    entailer!.
    2: { unfold concrete_mformat; entailer!.
      split; apply mk_format_mp; auto. }
    unfold add_above.
    replace (height G) with 0%nat in * by lia.
    split; auto.
    ins; desf; assert (sigmaG = []) by auto; subst; list_solve. }
  { forward; entailer!. }

  forward.
  getnw; destruct FMT_MP.
  forward_if(height F <> 0%nat).
  { forward.
    prove_ptr.
    forward_call(Ews, pG, sigmaG, gv).
    { destruct format_mp_list_mp; list_solve. }
    Intros new_format_ptr.
    forward.
    Exists new_format_ptr sigmaG.
    entailer!.
    2: { unfold concrete_mformat; entailer!.
      split; apply mk_format_mp; auto. }
    unfold add_above.
    replace (height F) with 0%nat by lia.
    destruct (height G).
    { lia. }
    split; auto.
    ins; desf; assert (sigmaF = []) by auto; subst; list_solve. }
  { forward; entailer!. }

  forward.
  prove_ptr.
  forward_call(Ews, pG, sigmaG, gv).
  { destruct format_mp_list_mp; list_solve. }
  Intros new_G_ptr.
  forward.
  prove_ptr.
  forward_call(Ews, pF, sigmaF, gv).
  { destruct format_mp_list_mp0; list_solve. }
  Intros new_F_ptr.
  forward_call(sigmaG, new_G_ptr, sigmaF, new_F_ptr).
  { split.
    { destruct sigmaG.
      2: vauto.
      desf.
      assert (0 = Z.of_nat (height G)) by auto; lia.
    }
    destruct sigmaF.
    2: vauto.
    desf.
    assert (0 = Z.of_nat (height F)) by auto; lia. }
  do 2 forward.

  Exists new_G_ptr (sigmaG ++ sigmaF).
  entailer!.
  2: { unfold concrete_mformat; entailer!.
    split; apply mk_format_mp; auto. }
  split.
  { unfold add_above.
    destruct (height G).
    { lia. }
    destruct (height F).
    { lia. }
    simpl.
    unfold to_text_eq.
    intros shift line.
    apply text_from_concat_add_above; auto.
    { destruct sigmaG; desf.
      assert (0 = Z.of_nat (S n)) by auto; lia. }
    destruct sigmaF; desf.
    assert (0 = Z.of_nat (S n0)) by auto; lia. }
  destruct format_mp_list_mp.
  destruct format_mp_list_mp0.
  apply mk_list_mp; list_solve.
Qed.

Lemma body_add_above: semax_body Vprog Gprog f_add_above add_above_spec.
Proof.
  start_function.
  unfold mformat.
  forward.
  getnw; destruct COMB.
  forward_if(height G <> 0%nat).
  { forward_call(F, pointer_F, sigmaF, pF, gv).
    Intros new_format_ptr.
    forward.
    Exists new_format_ptr.
    entailer!.
    unfold mformat.
    Intros sigmaF1 pF1.
    Exists sigmaF1 pF1.
    unfold concrete_mformat. unfold add_above.
    replace (height G) with 0%nat.
    { entailer!. }
    getnw. destruct FMT_MP.
    apply int_repr_eq; simpl; list_solve. }
  { forward; entailer!. }
  forward.
  forward_if(height F <> 0%nat).
  { forward_call(G, pointer_G, sigmaG, pG, gv).
    { unfold concrete_mformat; entailer!. }
    Intros new_format_ptr.
    forward.
    Exists new_format_ptr.
    entailer!.
    unfold mformat.
    Intros sigmaG1 pG1.
    Exists sigmaG1 pG1.
    unfold concrete_mformat. unfold add_above.
    destruct (height G) eqn:E.
    { lia. }
    replace (height F) with 0%nat.
    { rewrite E. entailer!. }
    getnw. destruct FMT_MP.
    apply int_repr_eq; list_solve.
  }
  { forward; entailer!. }
  forward_call(t_format, gv).

  Intros result_ptr.
  dest_ptr result_ptr.
  
  forward_call(G, F, pointer_G, pointer_F, sigmaG, sigmaF, pG, pF, gv).
  { unfold concrete_mformat; entailer!. }
  { apply mk_format_comb; auto. }

  forward_call(G, F, pointer_G, pointer_F, sigmaG, sigmaF, pG, pF, gv).
  Intros p.
  destruct p as (to_text_ptr, to_text).
  unfold concrete_mformat.
  Intros.
  do 10 forward.
  Exists result_ptr.
  entailer!.
  unfold mformat.
  Exists to_text to_text_ptr.
  unfold concrete_mformat.
  assert ((Z.of_nat (height G) + Z.of_nat (height F)) = Z.of_nat (height (add_above G F))) as K1.
  { unfold add_above.
    destruct (height G); try lia.
    destruct (height F); try lia.
    simpl; lia. }
  assert (first_line_width G = first_line_width (add_above G F)) as K2.
  { unfold add_above.
    destruct (height G); try lia.
    destruct (height F); try lia.
    simpl; lia. }
  assert (last_line_width F = last_line_width (add_above G F)) as K3.
  { unfold add_above.
    destruct (height G); try lia.
    destruct (height F); try lia.
    simpl; lia. }
  entailer!.
  2: {
    rewrite K1; rewrite K2; rewrite K3.
    entailer!. }
  simpl in *.
  getnw; destruct FMT_MP.
  getnw; destruct FMT_MP.
  apply mk_format_mp; auto.
  { rewrite <- K1; lia. }
  { rewrite <- K2; lia. }
  { rewrite <- K3; lia. }
  rewrite <- K1.
  split; ins.
  { assert (height G = 0%nat) by lia; lia. }
  subst.
  destruct sigmaG.
  2: vauto.
  desf.
  assert (0 = Z.of_nat (height G)) by auto.
  lia.
Qed.

Lemma body_mdw_add_beside: semax_body Vprog Gprog f_mdw_add_beside mdw_add_beside_spec.
Proof.
  start_function.
  forward.
  getnw; destruct FMT_MP.
  forward_if(height G <> 0%nat).
  { do 2 forward.
    unfold concrete_mformat.
    entailer!.
    unfold add_beside.
    replace (height G) with 0%nat by lia.
    getnw; destruct FMT_MP.
    split; try split; ins.
    lia. }
  { forward; entailer!. }
  forward.
  getnw; destruct FMT_MP.
  forward_if(height F <> 0%nat).
  { do 2 forward.
    unfold concrete_mformat.
    entailer!.
    unfold add_beside.
    destruct (height G) eqn:E.
    { lia. }
    replace (height F) with 0%nat by lia.
    split; try split; try split; ins.
    { lia. }
    apply mk_format_mp; try rewrite E; auto. }
  { forward; entailer!. }
  forward.

  remember (fun (tr: ident) (b: bool) =>
    PROP()
    LOCAL(temp tr (Val.of_bool b); temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF))
  as if_invariant eqn:eqn_if_invariant.
    
  forward_if(
    if_invariant _t'5 ((height G =? 1)%nat && (height F =? 1)%nat)%bool
  ).
  { do 2 forward.
    rewrite eqn_if_invariant.
    unfold concrete_mformat.
    entailer!.
    split; try split; try apply mk_format_mp; auto.
    replace (height G) with 1%nat by lia.
    ins; f_equal; apply nat_eq_iff_int_eq; lia. }
  { forward.
    rewrite eqn_if_invariant.
    unfold concrete_mformat.
    entailer!.
    split; try split; try apply mk_format_mp; auto.
    assert (height G <> 1%nat) by list_solve.
    replace (height G =? 1)%nat with false; ins.
    symmetry; rewrite Nat.eqb_neq; auto. }
  rewrite eqn_if_invariant.
  
  getnw; destruct COMB.
  remember (
    PROP(0 <= Z.of_nat (middle_width (add_beside G F)) <= Int.max_unsigned)
    LOCAL(temp _middle_width_new (Vint (Int.repr (Z.of_nat (middle_width (add_beside G F))))); 
          temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  ) as middle_invariant eqn:eqn_middle_invariant.
  forward_if(middle_invariant).
  { do 3 forward.
    rewrite eqn_middle_invariant.
    unfold concrete_mformat.
    entailer!.
    do 2 f_equal.
    unfold add_beside.
    desf; ins. 
    split; try lia; list_solve. }
  2: {
    rewrite eqn_middle_invariant.
    forward. }
  forward.
  forward_if(
    if_invariant _t'4 ((height G =? 1)%nat && (height F =? 2)%nat)%bool
  ).
  { do 2 forward.
    rewrite eqn_if_invariant.
    unfold concrete_mformat.
    entailer!.
    replace (height G) with 1%nat by lia.
    ins; f_equal; apply nat_eq_iff_int_eq; ins. }
  { forward.
    rewrite eqn_if_invariant.
    unfold concrete_mformat; entailer!.
    assert (height G <> 1)%nat by lia.
    replace (height G =? 1)%nat with false; ins.
    symmetry; rewrite Nat.eqb_neq; auto. }
  rewrite eqn_if_invariant.
  forward_if(middle_invariant).
  { do 3 forward.
    rewrite eqn_middle_invariant.
    unfold concrete_mformat; entailer!.
    do 2 f_equal.
    unfold add_beside.
    desf; ins; list_solve. }
  forward.
  forward_if(middle_invariant).
  { forward.
    rewrite eqn_middle_invariant.
    unfold concrete_mformat; entailer!.
    unfold add_beside.
    destruct (height G); vauto.
    destruct (height F); vauto.
    desf; ins; try lia. }
  forward.
  forward_if(middle_invariant).
  { do 3 forward.
    rewrite eqn_middle_invariant.
    unfold concrete_mformat; entailer!.
    unfold add_beside.
    destruct (height G); vauto.
    destruct (height F); vauto.
    destruct n; try lia.
    destruct n0; vauto.
    destruct n0; vauto.
    ins; list_solve. }
  forward.
  forward_if(middle_invariant).
  { do 4 forward.
    forward_call(Z.of_nat (last_line_width G) + Z.of_nat (first_line_width F),
      Z.of_nat (last_line_width G) + Z.of_nat (middle_width F)).
    Intros max1.
    forward.
    rewrite eqn_middle_invariant.
    unfold concrete_mformat; entailer!.
    unfold add_beside.
    destruct (height G); vauto.
    destruct (height F); vauto.
    destruct n; vauto.
    destruct n; try lia.
    destruct n0; vauto.
    ins; list_solve. }
  do 4 forward.
  forward_call(Z.of_nat (last_line_width G) + Z.of_nat (first_line_width F),
    Z.of_nat (last_line_width G) + Z.of_nat (middle_width F)).
  Intros max1.
  forward.
  forward_call(Z.of_nat (middle_width G), max1).
  Intros max2.
  forward.
  rewrite eqn_middle_invariant.
  unfold concrete_mformat; entailer!.
  unfold add_beside.
  destruct (height G); vauto.
  destruct (height F); vauto.
  destruct n; vauto.
  destruct n; try lia.
  destruct n0; vauto.
  ins; list_solve.
Qed.
  