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
    split; apply mk_format_mp; auto. }
  { forward. rewrite eqn_if_invariant.
    entailer!.
    { assert (height G <> 1)%nat by list_solve.
      replace (height G =? 1)%nat with false.
      { list_solve. }
      symmetry. apply Nat.eqb_neq. auto.
     }
     unfold concrete_mformat.
     entailer!.
    split; apply mk_format_mp; auto. }

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
    destruct hF; vauto. }
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
      apply int_repr_eq; list_solve. }
    { forward.
      rewrite eqn_if_invariant.
      entailer!.
      2: now unfold concrete_mformat; entailer!.
      assert (height G <> 1)%nat by list_solve.
      replace (height G =? 1)%nat with false.
      { list_solve. }
      symmetry. apply Nat.eqb_neq; auto. }
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
      apply nat_eq_iff_int_eq; list_solve. }
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
    apply int_repr_eq; list_solve. }
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
  
Lemma body_flw_add_beside: semax_body Vprog Gprog f_flw_add_beside flw_add_beside_spec.
Proof.
  start_function.
  forward.
  getnw; destruct COMB.
  forward_if(height G <> 0%nat).
  { do 2 forward.
    unfold concrete_mformat; entailer!.
    unfold add_beside.
    replace (height G) with 0%nat by lia.
    list_solve. }
  { forward. entailer!.  }
  forward.
  forward_if(height F <> 0%nat).
  { do 2 forward.
    unfold concrete_mformat; entailer!.
    unfold add_beside.
    destruct (height G); vauto.
    replace (height F) with 0%nat by lia.
    list_solve. }
  { forward. entailer!.  }
  forward.
  forward_if(
    PROP(0 <= Z.of_nat (first_line_width (add_beside G F)) <= Int.max_unsigned)
    LOCAL(temp _first_line_width_new (Vint (Int.repr (Z.of_nat (first_line_width (add_beside G F))))); 
          temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)).
  3: { forward. }
  { do 3 forward.
    unfold concrete_mformat; entailer!.
    unfold add_beside.
    desf; ins; list_solve. }
  forward.
  unfold concrete_mformat; entailer!.
  unfold add_beside.
  desf; ins; list_solve.
Qed.

Lemma Zrepeat_cons: forall {A: Type} (a: A) (n: Z),
  0 <= n ->
  a :: Zrepeat a n = Zrepeat a (n + 1).
Proof.
  ins.
  repeat rewrite <- repeat_Zrepeat.
  remember (Z.to_nat n) as k.
  replace (Z.to_nat (n + 1)) with (k + 1)%nat by lia.
  clear dependent n.
  replace (k + 1)%nat with (S k) by lia.
  ins.
Qed.
  

Lemma body_line_concats: semax_body Vprog Gprog f_line_concats line_concats_spec.
Proof.
  start_function.
  forward_call(Ews, l1, p1).
  forward_call(Ews, l2, p2).
  forward_call((tarray tschar (Zlength l1 + shift + Zlength l2 + 1)), gv).
  { unfold Ptrofs.max_unsigned.
    unfold Int.max_unsigned in *; ins; lia. }
  Intros result_ptr.
  destruct (eq_dec result_ptr nullval).
  { forward.
    forward_if(result_ptr <> nullval).
    { forward_call; entailer!. }
    { forward; entailer!. }
    now Intros. }
  Intros.
  forward.
  forward_if(result_ptr <> nullval).
  { forward_call; entailer!. }
  { forward; entailer!. }
  Intros.
  rewrite data_at__tarray.
  replace (Zrepeat (default_val tschar) (Zlength l1 + shift + Zlength l2 + 1)) 
    with (default_val tschar :: Zrepeat (default_val tschar) (Zlength l1 + shift + Zlength l2)).
  2: { apply Zrepeat_cons; list_solve. }
  forward.
  { entailer!. }
  rewrite upd_Znth0.
  forward_call(shift, gv).
  Intros shifted_ptr.
  forward_call(Ews, Ews, result_ptr, Zlength l1 + shift + Zlength l2 + 1, p1, [] : list byte, l1).
  2: list_solve.
  { unfold cstringn.
    autorewrite with sublist norm.
    entailer!. }
  forward_call(Ews, Ews, result_ptr, Zlength l1 + shift + Zlength l2 + 1, shifted_ptr, l1, sp_byte (Z.to_nat shift)).
  { autorewrite with sublist norm.
    entailer!. }
  { rewrite sp_byte_length; list_solve. }
  forward_call(Ews, Ews, result_ptr, Zlength l1 + shift + Zlength l2 + 1, p2, l1 ++ sp_byte (Z.to_nat shift), l2).
  { autorewrite with sublist norm.
    rewrite sp_byte_length; list_solve. }
  forward_call(tarray tschar (Zlength l1 + 1), p1, gv).
  { destruct (eq_dec p1 nullval).
    { entailer!. }
    unfold cstring; entailer!. }
  forward_call(tarray tschar (shift + 1), shifted_ptr, gv).
  { destruct (eq_dec shifted_ptr nullval); entailer!.
    rewrite sp_byte_length. 
    replace (Z.of_nat (Z.to_nat shift)) with shift by list_solve.
    entailer!. }
  forward_call(tarray tschar (Zlength l2 + 1), p2, gv).
  { destruct (eq_dec p2 nullval).
    { entailer!. }
    unfold cstring; entailer!. }
  forward.
  Exists (l1 ++ sp_byte (Z.to_nat shift) ++ l2) result_ptr.
  entailer!.
  { autorewrite with sublist norm.
    rewrite sp_byte_length; list_solve. }
  rewrite cstringn_equiv.
  autorewrite with sublist norm.
  rewrite sp_byte_length.
  replace (Z.of_nat (Z.to_nat shift)) with shift by list_solve.
  replace (((l1 ++ sp_byte (Z.to_nat shift)) ++ l2)) with
    (l1 ++ sp_byte (Z.to_nat shift) ++ l2) by list_solve.
  replace (Zlength l1 + (shift + Zlength l2) + 1) with
    (Zlength l1 + shift + Zlength l2 + 1) by list_solve.
  entailer!.
Qed.

Lemma body_shift_list: semax_body Vprog Gprog f_shift_list shift_list_spec.
Proof.
  start_function.
  forward.
  forward_loop(
    EX i : Z, 
    EX q : val,
    PROP(0 <= i <= Zlength sigma)
    LOCAL(temp _cur_sigma q; temp _sigma p; temp _n (Vptrofs (Ptrofs.repr shift)))
    SEP(lseg (map (fun x => (fst x + shift, snd x)) (sublist 0 i sigma)) p q; 
        listrep (sublist i (Zlength sigma) sigma) q)
  ).
  2: {entailer!. }
  { Exists 0 p.
    entailer!.
    replace (sublist 0 0 sigma) with ([] : list (Z * list byte)) by list_solve.
    unff lseg.
    replace (sublist 0 (Zlength sigma) sigma) with sigma by list_solve.
    entailer!. }
  { assert ((i = Zlength sigma) \/ (i < Zlength sigma)) as K by lia.
    destruct K.
    { subst.
      replace (sublist (Zlength sigma) (Zlength sigma) sigma) with ([] : list (Z * list byte)) by list_solve.
      unff listrep.
      Intros; vauto. }
    replace (sublist i (Zlength sigma) sigma) 
      with (Znth i sigma :: sublist (i + 1) (Zlength sigma) sigma) by list_solve.
    unff listrep.
    remember (Znth i sigma) as ith_element.
    destruct ith_element as (ith_shift, ith_line).
    Intros ith_tail ith_line_ptr.
    do 3 forward.
    prove_ptr.
    Exists ((i + 1), ith_tail).
    entailer!.
    { list_solve. }
    entailer!.
    replace (sublist 0 (i + 1) sigma) with (sublist 0 i sigma ++ [Znth i sigma]) by list_solve.
    rewrite map_app.
    remember (fun x : Z * list byte => (fst x + shift, snd x)) as f.
    assert (
      lseg (map f (sublist 0 i sigma)) p q *
      lseg (map f [Znth i sigma]) q ith_tail
      |--
      lseg (map f (sublist 0 i sigma) ++ map f [Znth i sigma]) p ith_tail
    ) as K.
    { apply lseg_lseg. }
    eapply derives_trans.
    2: eauto.
    entailer!.
    rewrite <- Heqith_element.
    simpl.
    unfold lseg.
    Exists ith_tail ith_line_ptr.
    entailer!. }
  forward.
  unnw; desf.
  assert (sublist i (Zlength sigma) sigma = []) as K by auto.
  assert (i < Zlength sigma \/ i = Zlength sigma) as K2 by lia.
  destruct K2.
  { replace (sublist i (Zlength sigma) sigma) with
      (Znth i sigma :: sublist (i + 1) (Zlength sigma) sigma) in K by list_solve.
    vauto. }
  subst.
  replace (sublist 0 (Zlength sigma) sigma) with sigma by list_solve.
  replace (sublist (Zlength sigma) (Zlength sigma) sigma) with ([] : list (Z * list byte)) by list_solve.
  unff listrep.
  entailer!.
  apply lseg_null_listrep.
Qed.

Lemma sp_byte_eq (n m : nat) :
  sp_byte n = sp_byte m <-> n = m.
Proof.
  split; ins; vauto.
  revert dependent m.
  induction n.
  { ins; destruct m; ins. }
  intros m F.
  destruct m; ins.
  inv F. unfold sp_byte in *.
  apply eq_S.
  apply IHn; auto.
Qed.

Lemma shifted_text_addb_eq p0 p sigmaF_tail l shift n:
  Forall (fun x : Z * list byte => 0 <= fst x <= Int.max_unsigned) (p0 :: sigmaF_tail) ->
  0 <= Z.of_nat n ->
  0 <= Z.of_nat shift ->
  p :: l = map (fun x : Z * list byte => (fst x + (Z.of_nat n), snd x)) (p0 :: sigmaF_tail) ->
  shifted_text_from (p0 :: sigmaF_tail) (shift + n) =
    shifted_text_from (p :: l) shift.
Proof.
  intros K1 K2 K3.
  intros F.
  inv F.
  revert dependent n.
  revert dependent shift.
  revert dependent p0.
  induction sigmaF_tail.
  { ins.
    unfold shifted_text_from.
    desf; ins.
    replace (Z.to_nat z + (shift + n))%nat with (Z.to_nat (z + Z.of_nat n) + shift)%nat; vauto.
    inv K1; ins.
    rewrite Z2Nat.inj_add; lia. }
  ins.
  replace (shifted_text_from (p0 :: a :: sigmaF_tail) (shift + n)) with
    (sp_byte (Z.to_nat (fst p0) + shift + n) ++ snd p0 ++ newline_byte ++ (shifted_text_from (a :: sigmaF_tail) (shift + n))).
  2: { unff shifted_text_from; desf; ins; rewrite <- Nat.add_assoc; vauto.  }
  replace (shifted_text_from ((fst p0 + Z.of_nat n, snd p0) :: (fst a + Z.of_nat n, snd a)
            :: map (fun x : Z * list byte => (fst x + Z.of_nat n, snd x)) sigmaF_tail) shift) with
  (sp_byte (Z.to_nat (fst p0 + Z.of_nat n) + shift) ++ snd p0 ++ newline_byte ++ 
      shifted_text_from((fst a + Z.of_nat n, snd a) :: map (fun x : Z * list byte => (fst x + Z.of_nat n, snd x)) sigmaF_tail) shift).
  2: { unff shifted_text_from; desf. }
  rewrite IHsigmaF_tail; vauto; ins.
  { inv K1.
    rewrite Z2Nat.inj_add; try lia.
    replace (Z.to_nat (Z.of_nat n)) with n by lia.
    replace (Z.to_nat (fst p0) + shift + n)%nat with (Z.to_nat (fst p0) + n + shift)%nat by lia.
    list_solve. }
  inv K1; vauto.
Qed.

Lemma body_to_text_add_beside: semax_body Vprog Gprog f_to_text_add_beside to_text_add_beside_spec.
Proof.
  start_function.
  forward.
  getnw; destruct FMT_MP.
  forward_if(height G <> 0%nat).
  { forward.
    prove_ptr.
    getnw; destruct FMT_MP.
    forward_call(Ews, pF, sigmaF, gv).
    { destruct format_mp_list_mp0; list_solve.  }
    Intros result_ptr.
    forward.
    Exists result_ptr sigmaF.
    unfold concrete_mformat; entailer!.
    desf; assert (sigmaG = []).
    { list_solve. }
    split.
    { unfold add_beside; desf. }
    split.
    { subst; list_solve. }
    split; apply mk_format_mp; vauto. }
  { forward; entailer!. }
  forward.
  getnw; destruct FMT_MP.
  forward_if(height F <> 0%nat).
  { forward.
    prove_ptr.
    forward_call(Ews, pG, sigmaG, gv).
    { destruct format_mp_list_mp; list_solve.  }
    Intros result_ptr.
    forward.
    Exists result_ptr sigmaG.
    unfold concrete_mformat; entailer!.
    split.
    { unfold add_beside; desf. }
    split; apply mk_format_mp; vauto. }
  { forward; entailer!. }
  forward.
  prove_ptr.
  forward_call(Ews, pG, sigmaG, gv).
  { destruct format_mp_list_mp; list_solve. }
  Intros head_ptr.
  forward.
  forward_call(head_ptr, sigmaG).
  { desf; assert (0 = Z.of_nat (height G)) by auto; lia. }
  Intros tail_ptr.
  assert (Zlength sigmaG = 0 \/ Zlength sigmaG > 0) as K by list_solve.
  destruct K.
  { destruct (sigmaG); try list_solve.
    desf; assert (0 = Z.of_nat (height G)) by auto; lia. }
  replace (sublist (Zlength sigmaG - 1) (Zlength sigmaG) sigmaG) with 
    [Znth (Zlength sigmaG - 1) sigmaG] by list_solve.
  unff listrep.
  remember (Znth (Zlength sigmaG - 1) sigmaG) as tail_el.
  destruct tail_el as (tail_shift, tail_line).
  Intros tail_nullptr tail_line_ptr.
  forward.
  prove_ptr.
  forward_call(Ews, pF, sigmaF, gv).
  { destruct format_mp_list_mp0; list_solve. }
  Intros pF_new.
  forward.
  destruct sigmaF as [| f_fst_el sigmaF_tail].
  { desf; assert (0 = Z.of_nat (height F)) by auto; lia. }
  unff listrep.
  destruct f_fst_el as (f_fst_shift, f_fst_line).
  Intros f_fst_tail_ptr_old f_fst_line_ptr_old.
  Intros f_fst_tail_ptr f_fst_line_ptr.
  do 3 forward.
  unfold to_text_add_beside_pred in AB_PRED.
  forward_call(tail_line, tail_line_ptr, f_fst_line, f_fst_line_ptr, f_fst_shift, gv).
  { ins. split.
    { assert (In (tail_shift, tail_line) sigmaG) as K.
      { rewrite Heqtail_el; apply Znth_In; list_solve. }
      replace (tail_line) with (snd (tail_shift, tail_line)) by auto.
      remember (fun x : Z * list byte => 
      0 <= Zlength (snd x) + f_fst_shift + Zlength f_fst_line + 1 <= Int.max_unsigned
      ) as PP.
      remember (computable_theorems.Forall_forall1 PP sigmaG).
      assert (PP (tail_shift, tail_line)) as K2.
      { list_solve. }
      rewrite HeqPP in K2; auto. }
    destruct format_mp_list_mp0.
    assert(
      0 <= fst (f_fst_shift, f_fst_line) <= Int.max_unsigned - 1
    ) as KK. {
      remember (fun x : Z * list byte =>
        0 <= fst x <= Int.max_unsigned - 1)  as PP.
      enough (PP (f_fst_shift, f_fst_line)) as KK.
      { rewrite HeqPP in KK; auto. }
      eapply (Forall_inv _). Unshelve.
      { apply []. }
      list_solve. }
    simpl in KK; auto. }
  Intros line_concats.
  destruct line_concats as (line_con, line_con_ptr).
  do 2 forward.
  prove_ptr.
  forward.
  forward_call(sigmaF_tail, f_fst_tail_ptr, Z.of_nat (last_line_width G)).
  { split.
    { list_solve. }
    remember (fun x : Z * list byte =>
      0 <= fst x + Z.of_nat (last_line_width G) <= Int.max_unsigned - 1) as PP.
    remember (fun x : Z * list byte =>
      0 <= fst x + Z.of_nat (last_line_width G) <= Int.max_unsigned) as FF.
    inversion STMT as [| tmp4 tmp3 tmp2 FACT tmp1].
    eapply (Forall_impl FF).
    2: eauto.
    rewrite HeqPP.
    rewrite HeqFF.
    intros; lia. }
  do 2 forward.
  forward_call(t_list, pF_new, gv).
  { desf; entailer!. }
  forward.
  remember  
    (map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
      as new_sigmaF_tail.
  Exists head_ptr (sublist 0 (Zlength sigmaG - 1) sigmaG ++ [(tail_shift, line_con)] ++ new_sigmaF_tail).
  destruct format_mp_list_mp.
  destruct format_mp_list_mp0.
  entailer!.
  { split.
    2: { split.
      { apply mk_list_mp. 
        { list_solve. }
        { apply Forall_app; split.
          { list_solve. }
          apply Forall_app; split.
          { enough (0 <= tail_shift <= Int.max_unsigned - 1) by list_solve.
            replace tail_shift with (fst (tail_shift, tail_line)) by list_solve.
            rewrite Heqtail_el; list_solve. }
          apply List.Forall_map; simpl.
          eapply _. Unshelve.
          inv STMT.
          simpl in *; auto. }
        apply Forall_app; split.
        { list_solve. }
        apply Forall_app; split.
        2: { apply List.Forall_map; simpl.
          inv list_mp_forall_snd0; auto. }
        enough (0 <= Zlength line_con + 1 <= Int.max_unsigned) by list_solve; vauto. }
      list_solve. }
    unfold to_text_eq.
    ins.
    unfold add_beside.
    destruct (height G); vauto.
    destruct (height F); vauto; ins.
    rewrite format_mp_text_eq.
    rewrite text_from_line.
    2: { 
      destruct sigmaG.
      2: easy.
      desf; assert (0 = Z.of_nat (height G)) by auto; lia. }
    rewrite format_mp_text_eq0.
    rewrite (text_from_line _ (shift + last_line_width G) _).
    2: easy.
    remember (map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
      as new_sigmaF.
    rewrite (text_from_line 
      (sublist 0 (Zlength sigmaG - 1) sigmaG ++ (tail_shift, line_con) :: new_sigmaF) _ _).
    2: { destruct (sublist 0 (Zlength sigmaG - 1) sigmaG); vauto. }
    rewrite app_assoc.
    rewrite app_inv_tail_iff.
    assert (Zlength sigmaG = 0 \/ Zlength sigmaG = 1 \/ Zlength sigmaG > 1) by lia; desf.
    { assert (sigmaG = []) by list_solve; desf. }
    { replace (sublist 0 (Zlength sigmaG - 1) sigmaG) 
          with ([] : list (Z * list byte)) by list_solve.
      remember (map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
        as new_sigmaF.
      replace sigmaG with [(tail_shift, tail_line)] by list_solve.
      autorewrite with sublist norm.
      replace ((f_fst_shift, f_fst_line) :: sigmaF_tail) 
        with ([(f_fst_shift, f_fst_line)] ++ sigmaF_tail) by list_solve.
      replace ((tail_shift, line_con) :: new_sigmaF) 
        with ([(tail_shift, line_con)] ++ new_sigmaF) by list_solve.
      destruct (new_sigmaF).
      { autorewrite with sublist norm.
        unfold text_from.
        getnw; desf.
        2: list_solve.
        inv Heq; list_solve. }
      destruct sigmaF_tail; vauto.
      rewrite text_from_concat; vauto.
      rewrite text_from_concat; vauto.
      getnw; desf.
      unff text_from.
      autorewrite with sublist norm.
      repeat rewrite <- app_assoc.
      repeat apply app_inv_head_iff.
      apply shifted_text_addb_eq; vauto.
      2: lia.
      inv list_mp_forall_fst0.
      remember (fun x : Z * list byte => 0 <= fst x <= Int.max_unsigned) as PP.
      remember (fun x : Z * list byte => 0 <= fst x <= 4294967294) as FF.
      eapply Forall_impl.
      2: eauto.
      rewrite HeqFF; rewrite HeqPP.
      intros.
      unfold Int.max_unsigned; simpl; lia. }
    assert (sigmaG = (sublist 0 (Zlength sigmaG - 1) sigmaG) ++ [(tail_shift, tail_line)]) as K.
    { rewrite Heqtail_el; list_solve. }
    rewrite K at 1.
    repeat rewrite text_from_concat; vauto.
    2: { replace (sublist 0 (Zlength sigmaG - 1) sigmaG) with 
          (Znth 0 sigmaG :: sublist 1 (Zlength sigmaG - 1) sigmaG) by list_solve; vauto. }
    2: { replace (sublist 0 (Zlength sigmaG - 1) sigmaG) with 
          (Znth 0 sigmaG :: sublist 1 (Zlength sigmaG - 1) sigmaG) by list_solve; vauto. }
    repeat rewrite <- app_assoc.
    repeat apply app_inv_head_iff.
    autorewrite with sublist norm.
    remember (map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
      as new_sigmaF.
    replace ((f_fst_shift, f_fst_line) :: sigmaF_tail) 
      with ([(f_fst_shift, f_fst_line)] ++ sigmaF_tail) by list_solve.
    replace ((tail_shift, line_con) :: new_sigmaF) 
      with ([(tail_shift, line_con)] ++ new_sigmaF) by list_solve.
    destruct (new_sigmaF).
    { autorewrite with sublist norm.
      unfold text_from.
      getnw; desf.
      2: list_solve.
      inv Heq. 
      unfold shifted_text_from.
      list_solve. }
    destruct sigmaF_tail; vauto.
    rewrite text_from_concat; vauto.
    getnw; desf.
    unff text_from.
    autorewrite with sublist norm.
    repeat rewrite <- app_assoc.
    replace (shifted_text_from
        ([(tail_shift, tail_line ++ sp_byte (Z.to_nat f_fst_shift) ++ f_fst_line)] ++ p :: l) shift)
      with (
        sp_byte (Z.to_nat tail_shift + shift) ++ 
        (tail_line ++ sp_byte (Z.to_nat f_fst_shift) ++ f_fst_line) ++ newline_byte ++
        shifted_text_from (p :: l) shift
      ).
    2: desf.
    remember (shifted_text_from [(tail_shift, tail_line)] shift) as J.
    unfold shifted_text_from in HeqJ.
    rewrite HeqJ.
    repeat rewrite <- app_assoc.
    repeat apply app_inv_head_iff.
    apply shifted_text_addb_eq; vauto.
    2: lia.
    inv list_mp_forall_fst0.
    remember (fun x : Z * list byte => 0 <= fst x <= Int.max_unsigned) as PP.
    remember (fun x : Z * list byte => 0 <= fst x <= 4294967294) as FF.
    eapply Forall_impl.
    2: eauto.
    rewrite HeqFF; rewrite HeqPP.
    intros.
    unfold Int.max_unsigned; simpl; lia. }
  unfold concrete_mformat; entailer!.
  { split; apply mk_format_mp; vauto. }
  unff listrep.
  Exists f_fst_tail_ptr_old f_fst_line_ptr_old.
  entailer!.
  assert (
    lseg (sublist 0 (Zlength sigmaG - 1) sigmaG) head_ptr tail_ptr *
    lseg [(tail_shift, line_con)] tail_ptr f_fst_tail_ptr *
    listrep
    (map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
    f_fst_tail_ptr |--
    listrep
      (sublist 0 (Zlength sigmaG - 1) sigmaG ++
       [(tail_shift, line_con)] ++
       map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
      head_ptr
  ) as K.
  { assert (
    lseg (sublist 0 (Zlength sigmaG - 1) sigmaG) head_ptr tail_ptr *
    lseg [(tail_shift, line_con)] tail_ptr f_fst_tail_ptr *
    listrep
    (map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
    f_fst_tail_ptr |--
    lseg (sublist 0 (Zlength sigmaG - 1) sigmaG) head_ptr tail_ptr *
    listrep ( [(tail_shift, line_con)] ++
      (map (fun x : Z * list byte => (fst x + Z.of_nat (last_line_width G), snd x)) sigmaF_tail)
    ) tail_ptr ) as KK.
    { entailer!. 
      apply lseg_list. }
    eapply derives_trans; eauto.
    apply lseg_list. }
  eapply derives_trans.
  2: eauto.
  unff lseg.
  Exists f_fst_tail_ptr line_con_ptr.
  entailer!.
  getnw; ins; subst.
  autorewrite with sublist norm.
  rewrite sp_byte_length.
  inv list_mp_forall_fst0; ins. 
  replace (Z.of_nat (Z.to_nat f_fst_shift)) with f_fst_shift by list_solve.
  rewrite Z.add_assoc.
  entailer!.
Qed.
  
Lemma add_beside_spec: semax_body Vprog Gprog f_add_beside add_beside_spec.
Proof.
  start_function.
  forward.
  getnw; destruct FMT_MP.
  forward_if(height G <> 0%nat).
  { forward_call(F, pointer_F, sigmaF, pF, gv).
    Intros result_ptr.
    forward.
    Exists result_ptr.
    unfold concrete_mformat; entailer!.
    { apply mk_format_mp; vauto. }
    unfold mformat.
    Intros sigma p.
    Exists sigma p.
    unfold add_beside.
    replace (height G) with 0%nat by lia.
    entailer!. }
  { forward; entailer!. }
  forward.
  getnw; destruct FMT_MP.
  forward_if(height F <> 0%nat).
  { forward_call(G, pointer_G, sigmaG, pG, gv).
    { unfold concrete_mformat; entailer!.
      apply mk_format_mp; vauto. }
    Intros result_ptr.
    forward.
    Exists result_ptr.
    unfold concrete_mformat; entailer!.
    { apply mk_format_mp; vauto. }
    unfold mformat.
    Intros sigma p.
    Exists sigma p.
    unfold add_beside.
    destruct (height G).
    { lia. }
    replace (height F) with 0%nat by lia.
    entailer!. }
  { forward; entailer!. }

  forward_call(t_format, gv).
  Intros result_ptr.
  dest_ptr result_ptr.
  forward_call(G, F, pointer_G, pointer_F, sigmaG, sigmaF, pG, pF).
  { unfold concrete_mformat; entailer!.
    split; apply mk_format_mp; vauto. }
  forward_call(G, F, pointer_G, pointer_F, sigmaG, sigmaF, pG, pF).
  Intros flw_ptr.
  destruct COMB.
  forward_call(G, F, pointer_G, pointer_F, sigmaG, sigmaF, pG, pF, gv).
  Intros to_text.
  destruct to_text as (to_text_ptr, to_text_list).
  do 10 forward.
  Exists result_ptr.
  unfold concrete_mformat; entailer!.
  unfold mformat.
  Exists to_text_list to_text_ptr.
  unfold concrete_mformat.
  assert (height (add_beside G F) = height G + height F - 1)%nat as K1. 
  { unfold add_beside.
    destruct (height G).
    { lia. }
    destruct (height F).
    { lia. }
    simpl; lia. }
  assert (last_line_width (add_beside G F) = last_line_width G + last_line_width F)%nat as K2.
  { unfold add_beside.
    destruct (height G).
    { lia. }
    destruct (height F).
    { lia. }
    simpl; lia. }

  entailer!.
  { apply mk_format_mp; vauto.
    { rewrite K1; lia. }
    { rewrite K2; lia. }
    split.
    { lia. }
    ins; desf.
    destruct (sigmaG).
    { assert(0 = Z.of_nat (height G)) by auto; lia. }
    list_solve. }
  rewrite K1.
  rewrite K2.
  repeat rewrite Nat2Z.inj_add.
  replace (Z.of_nat (height G + height F - 1)) with 
    (Z.of_nat (height G) + Z.of_nat (height F) - 1) by list_solve.
  entailer!.
Qed.