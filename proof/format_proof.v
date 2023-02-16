Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import Coq.Strings.Ascii.
Require Import format_specs.
Require Import format_std_proof.

Lemma less_components_fact1: 
  forall (x y : nat), 
    (0 <= (Z.of_nat x) <= Int.max_unsigned) ->
    (0 <= (Z.of_nat y) <= Int.max_unsigned) ->
    Val.of_bool (Z.of_nat x <=? Z.of_nat y) =
    Val.of_bool (negb (Int.ltu (Int.repr (Z.of_nat y)) (Int.repr (Z.of_nat x)))).
Proof.
  intros.
  f_equal.
  remember (Z.of_nat x <=? Z.of_nat y) as comp.
  destruct comp.
  { remember (Z.of_nat y) as Y.
    remember (Z.of_nat x) as X.
    assert (X <= Y \/  X > Y) as AA. lia.
    destruct AA. 
    { remember (Int.ltu (Int.repr Y) (Int.repr X)) as b eqn:AA.
      destruct b.
      symmetry in AA.
      apply ltu_inv in AA.
      repeat rewrite Int.unsigned_repr in AA by auto.
      all: lia.
    } 
    remember (Int.ltu (Int.repr Y) (Int.repr X)).
    destruct b.
    2: now lia.
    destruct (Z.leb_spec0 X Y); lia.
    
  }
  remember (Z.of_nat y) as Y.
  remember (Z.of_nat x) as X.
  assert (X <= Y \/  X > Y) as AA. lia.
  destruct AA. 
  { remember (Int.ltu (Int.repr Y) (Int.repr X)) as b eqn:AA.
    destruct b. lia.
    symmetry in AA.
    apply ltu_false_inv in AA.
    repeat rewrite Int.unsigned_repr in AA by auto.
    destruct (Z.leb_spec0 X Y); lia.
  } 
  remember (Int.ltu (Int.repr Y) (Int.repr X)) as b eqn:AA.
  destruct b. lia.
  symmetry in AA.
  apply ltu_false_inv in AA.
  repeat rewrite Int.unsigned_repr in AA by auto.
  lia.
Qed.
  
Lemma less_components_fact2:
  forall (x y : nat),
  ((Z.of_nat x)) <=? (Z.of_nat y) = (Nat.leb x y).
Proof.
  intros.
  destruct (Nat.leb_spec0 x y).
  { apply inj_le in l.
    destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)); auto.
  }
  destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)); auto.
  apply Nat2Z.inj_le in l. lia.
Qed.

Lemma body_less_components: semax_body Vprog Gprog f_less_components less_components_spec.
Proof.
  start_function.
  unfold mformat.
  Intros sigmaG pG sigmaG' pG'.
  do 2 forward. 
  getnw. rename FMT_MP into FMT_MP'. getnw.
  destruct FMT_MP, FMT_MP'.
  forward_if(
    EX t1: bool,
    PROP(<< first_comp_eq : t1 = andb 
      ((Z.of_nat (height G)) <=? Z.of_nat (height G'))
      ((Z.of_nat (first_line_width G)) <=? Z.of_nat (first_line_width G')) >> 
    )
    LOCAL(temp _t'1 (Val.of_bool t1); temp _G p; temp _F q)
    SEP(
      concrete_mformat G p sigmaG pG;
      concrete_mformat G' q sigmaG' pG'
    )
  ). 

  { do 3 forward.
    Exists ((Z.of_nat (first_line_width G)) <=? (Z.of_nat (first_line_width G'))).
    unfold concrete_mformat. 
    unnw. entailer!. split.
    { apply less_components_fact1; auto. }
    { split; apply mk_format_mp; auto. }
  }
  { forward.
    Exists false.
    unfold concrete_mformat. unnw.
    entailer!.
    { split; apply mk_format_mp; auto. }
  }

  Intros first_comp.
  forward_if(
    EX t2: bool,
    PROP(<< second_comp_eq : t2 = andb first_comp 
      (((Z.of_nat (middle_width G))) <=?
      (Z.of_nat (middle_width G'))) >>)
    LOCAL(temp _t'2 (Val.of_bool t2); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ).
  { do 3 forward.
    Exists (first_comp && ((Z.of_nat (middle_width G)) <=? (Z.of_nat (middle_width G'))))%bool.
    getnw. 
    unfold concrete_mformat. unnw. subst. entailer!.
    remember ((Z.of_nat (height G) <=? Z.of_nat (height G')) &&
    (Z.of_nat (first_line_width G) <=? Z.of_nat (first_line_width G')))%bool as comp eqn:AA.
    clear AA. subst.
    simpl. apply less_components_fact1; auto.
  } 
  { forward.
    Exists false.
    entailer!.
  }

  Intros second_comp.
  forward_if(
    EX t3: bool,
    PROP(<< third_comp_eq : t3 = andb second_comp
      (((Z.of_nat (last_line_width G))) <=?
       (Z.of_nat (last_line_width G'))) >>)
    LOCAL(temp _t'3 (Val.of_bool t3); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ). 
  { do 3 forward.
    Exists (second_comp && (((Z.of_nat (last_line_width G))) <=? (Z.of_nat (last_line_width G'))))%bool.
    unfold concrete_mformat. entailer!. simpl.
    apply less_components_fact1; auto.
  } 
  {
    forward.
    Exists false.
    entailer!.
  }

  Intros third_comp.
  forward.
  Exists (less_components G G').
  entailer!.
  { f_equal. unfold less_components. getnw. subst. repeat rewrite less_components_fact2. auto. }
  unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!.
Qed.

Lemma is_less_than_fact1 x y :
    (x <> y)%nat <-> (x =? y)%nat = false.
Proof.
  remember (Nat.eqb_spec x y) eqn:AA. clear AA. split.
  { intros. destruct r. contradiction. auto. }
  intros. destruct r. lia. auto.
Qed.

Lemma is_less_than_fact2 x y
    (XBOUND : 0 <= (Z.of_nat x) <= Int.max_unsigned)
    (YBOUND : 0 <= (Z.of_nat y) <= Int.max_unsigned) :
    (x =? y)%nat = Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y)).
Proof.
  destruct (Nat.eqb_spec x y).
  { subst. rewrite Int.eq_true. auto. }
  remember(Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y))) as b eqn:AA.
  destruct b.
  2: lia.
  symmetry in AA. apply Int.same_if_eq in AA. apply repr_inj_unsigned in AA; auto. lia.
Qed.
    
Lemma body_is_less_than: semax_body Vprog Gprog f_is_less_than is_less_than_spec.
Proof.
  start_function.
  unfold mformat.
  Intros sigmaG pG sigmaG' pG'.
  forward.
  getnw. destruct FMT_MP.
  forward_if(
    EX t1: bool,
    PROP(t1 = andb (negb (Nat.eqb (height G) 1%nat)) (Nat.eqb (height G') 1))
    LOCAL(temp _t'2 (Val.of_bool t1); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ). 
  { do 2 forward.
    Exists (negb (height G =? 1)%nat && (height G' =? 1)%nat)%bool.
    entailer!.
    2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
    f_equal. 
    assert ((Nat.eqb (height G) 1) = false) as AA. 
    { destruct (eq_dec (height G) 1%nat).
      { rewrite e in *. simpl in *. list_solve. }
      apply is_less_than_fact1. auto. 
    }
    rewrite AA. simpl. apply is_less_than_fact2.
    { getnw. destruct FMT_MP. auto. }
    unfold Int.max_unsigned; simpl. lia.
  } 
  { forward.
    Exists false.
    entailer!.
    2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
    replace (height G) with 1%nat by lia. simpl. auto.
  }

  unfold concrete_mformat.
  Intros first_comp.
  getnw. destruct FMT_MP.
  forward_if(
    EX t2: bool,
    PROP(t2 = orb first_comp (andb (Nat.eqb (height G) 1%nat) (negb (Nat.eqb (height G') 1%nat))))
    LOCAL(temp _t'3 (Val.of_bool t2); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ). 
  { forward.
    Exists (first_comp || (height G =? 1)%nat && negb (height G' =? 1)%nat)%bool.
    entailer!.
    2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
    remember (negb (height G =? 1)%nat && (height G' =? 1)%nat)%bool as comp eqn:AA.
    clear AA. subst. 
    list_solve.
  } 
  { forward.
    forward_if(
      EX t3: bool,
      PROP(t3 = andb (Nat.eqb (height G) 1%nat) (negb (Nat.eqb (height G') 1%nat)))
      LOCAL(temp _t'3 (Val.of_bool t3); temp _G p; temp _F q)
      SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
    ). 
    { do 3 forward.
      Exists ((height G =? 1)%nat && negb (height G' =? 1)%nat)%bool.
      entailer!.
      2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
      - f_equal. replace (height G) with 1%nat by list_solve. simpl. f_equal.
        apply is_less_than_fact2; auto. simpl. unfold Int.max_unsigned. simpl. lia.
    } 
    { forward.
      Exists false.
      entailer!.
      2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
      assert (height G <> 1%nat). list_solve.
      destruct (Nat.eqb_spec (height G) 1%nat).
      { contradiction. }
      auto.
    }
    Intros second_comp.
    Exists (first_comp || second_comp)%bool.
    entailer!.
    replace (negb (height G =? 1)%nat && (height G' =? 1)%nat)%bool with false.
    auto.
  }
  Intros all_comp.
  forward_if. 
  { forward.
    Exists false.
    unfold is_less_than.
    destruct (height G) eqn:AA.
    { destruct (height G') eqn:BB.
      { entailer!. 
        2: { unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!. }
        simpl in *. lia.
      }
      entailer!.
      2: { unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!. }
      destruct n.
      { auto. }
      simpl in *. lia.
    }
    entailer!.
    2: { unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!. }
    destruct n.
    { destruct (height G').
      { auto. }
      destruct n.  
      2: now auto.
      simpl in *. lia.
    }
    destruct (height G').
    { simpl in *. lia. }
    destruct n0.
    { auto. }
    simpl in *. lia.
  }

  forward_call(p, G, q, G').
  { unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!. }
  Intros ans. forward.
  Exists (less_components G G').
  entailer!.
  unfold is_less_than. 
  destruct (height G).
  { destruct (height G').
    { auto. }
    destruct n.
    2: now auto.
    simpl in *. lia.
  }
  destruct n.
  { destruct (height G').
    { simpl in *. lia. }
    destruct n.
    { auto. }
    simpl in *. lia.
  }
  destruct (height G').
  { auto. }
  destruct n0.
  2: now auto.
  simpl in *. lia.
Qed.

Lemma body_empty: semax_body Vprog Gprog f_empty empty_spec.
Proof.
  start_function.
  forward_call(t_format, gv).
  Intros empty_pointer.
  destruct (eq_dec empty_pointer nullval).
  { forward_if(empty_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    { now Intros. }
  }

  forward_if(empty_pointer <> nullval). 
  { forward_call. entailer!. }
  { forward. entailer!. }

  Intros.
  do 6 forward.

  Exists empty_pointer.
  entailer!.
  unfold mformat.
  Exists ([] : (list (Z * list byte))) (Vlong (Int64.repr 0)).
  unfold concrete_mformat.
  entailer!.
  { apply mk_format_mp. 
    { unfold to_text_eq. auto. }
    { apply mk_list_mp; auto. simpl. unfold Int.max_unsigned. simpl. lia. }
    all: now unfold empty.
  }
  unfold listrep. entailer!.
Qed.

Lemma list_byte_to_string_length:
  forall (s : list byte),
    Z.of_nat (String.length (list_byte_to_string s)) = Zlength s.
Proof.
  intros.
  induction s.
  - list_solve.
  - unfold list_byte_to_string; fold list_byte_to_string.
    simpl. list_solve.
Qed.

Lemma list_byte_to_list_byte_eq:
  forall (s : list byte),
    string_to_list_byte (list_byte_to_string s) = s.
Proof.
  intros.
  induction s.
  - list_solve.
  - unfold list_byte_to_string; fold list_byte_to_string.
    unfold string_to_list_byte; fold string_to_list_byte.
    rewrite IHs.
    assert (Byte.unsigned a < 256). {
      remember (Byte.unsigned_range a).
      unfold Byte.modulus in a0.
      assert(two_power_nat Byte.wordsize = 256 ). list_solve.
      lia.
    }
    assert ((Z.to_N (Byte.unsigned a) < 256)%N). {
      list_solve.
    }
    assert ((N_of_ascii (ascii_of_N (Z.to_N (Byte.unsigned a)))) = Z.to_N (Byte.unsigned a)) as AA. {
      apply N_ascii_embedding.
      auto.
    }
    rewrite AA.
    rewrite Z2N.id.
    rewrite Byte.repr_unsigned.
    auto.
    apply Byte.unsigned_range.
Qed.

Lemma empty_string_app:
  forall (s : string),
    (s ++ "")%string = s.
Proof.
  intros.
  induction s.
  - simpl. reflexivity.
  - unfold append; fold append. rewrite IHs. reflexivity.
Qed.

Lemma body_line: semax_body Vprog Gprog f_line line_spec.
Proof.
  start_function.
  forward_call(t_format, gv).
  Intros format_pointer.
  destruct (eq_dec format_pointer nullval). 
  { forward_if(format_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    { Intros. contradiction. }
  }

  forward_if(format_pointer <> nullval). 
  { forward_call. entailer!. } 
  { forward. entailer!. }
  Intros.

  forward.
  forward_call(Ews, sigma, p).
  forward.
  forward_call(Ews, sigma, p).
  forward.
  forward_call(Ews, sigma, p).
  forward.

  forward_call(t_list, gv).
  Intros to_text_pointer.
  destruct (eq_dec to_text_pointer nullval). 
  { do 2 forward.
    forward_if(to_text_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    { Intros. contradiction. }
  }

  Intros.
  do 2 forward.
  forward_if(to_text_pointer <> nullval). 
  { forward_call. entailer!. } 
  { forward. entailer. }

  do 7 forward.
  Exists format_pointer.
  unfold mformat. unfold cstring.
  Exists ([(0, sigma)]) to_text_pointer.
  entailer!. unfold concrete_mformat.
  entailer!.
  { 
    unnw. apply mk_format_mp.
    { unfold to_text_eq. unfold to_text. simpl.
      replace (sigma ++ []) with sigma by list_solve.
      rewrite empty_string_app.
      apply list_byte_to_list_byte_eq.
    }
    { apply mk_list_mp; auto.
      { simpl. unfold Int.max_unsigned. simpl. lia. }
      list_simplify. simpl. lia.
    }
    all: unfold line; simpl.
    { unfold Int.max_unsigned. simpl. lia. }
    all: rewrite list_byte_to_string_length; list_solve.
  }
  unfold listrep.
  unfold cstring.
  Exists (Vlong (Int64.repr 0)) p.
  entailer!.
  unfold line; simpl.
  repeat rewrite list_byte_to_string_length.
  entailer!.
  apply orp_right1.
  entailer.
Qed.

Lemma sp_fact1 (n : Z):
  Zrepeat (Byte.repr 32) n = string_to_list_byte (sp (Z.to_nat n)).
Proof.
  unfold Zrepeat.
  remember (Z.to_nat n) as m.
  clear Heqm. clear n.
  induction m.
  - auto.
  - simpl. f_equal. apply IHm.
Qed.

Lemma sp_fact2 (n : nat):
  ~In Byte.zero (string_to_list_byte (sp n)).
Proof.
  induction n.
  - list_solve.
  - unfold not in *. unfold sp; fold sp. simpl.
    intros. destruct H.
    + inversion H.
    + auto.
Qed.

Lemma body_sp : semax_body Vprog Gprog f_sp sp_spec.
Proof.
  start_function.
  forward_call((Tarray tschar (n + 1) noattr), gv).
  { unfold Int.max_unsigned in H. unfold Ptrofs.max_unsigned. simpl in *. lia. }
  Intros result_pointer.
  destruct (eq_dec result_pointer nullval). {
    forward_if(result_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    { forward. contradiction. }
  }
  forward_if(result_pointer <> nullval).
  { forward_call. entailer!. }
  { forward. entailer. }
  Intros.
  forward.
  forward_loop (
    EX i : Z,
    PROP(0 <= i <= n)
    LOCAL(temp _i (Vptrofs (Ptrofs.repr i)); temp _space (Vint (Int.repr 32));
          temp _result result_pointer; temp _n (Vptrofs (Ptrofs.repr n)))
    SEP(data_at Ews (Tarray tschar (n + 1) noattr) (map Vbyte (Zrepeat (Byte.repr 32) i) ++ Zrepeat Vundef (n + 1 - i)) result_pointer;
        malloc_token Ews (Tarray tschar (n + 1) noattr) result_pointer;
        mem_mgr gv)
  ) break: (
    PROP()
    LOCAL(temp _result result_pointer; temp _n (Vptrofs (Ptrofs.repr n)))
    SEP(data_at Ews (Tarray tschar (n + 1) noattr) (map Vbyte (Zrepeat (Byte.repr 32) n) ++ [Vundef]) result_pointer;
        malloc_token Ews (Tarray tschar (n + 1) noattr) result_pointer;
        mem_mgr gv)
  ).
  { 
    forward. Exists 0. entailer!. 
    autorewrite with sublist norm.
    unfold data_at_, data_at, field_at_. entailer!.
  }
  { 
    Intros i. 
    forward_if.
    { forward. forward. Exists (i + 1). entailer!. list_solve. } 
    forward.
    entailer!.
    unfold cstring.
    entailer!.
    replace i with n by list_solve.
    autorewrite with sublist norm.
    list_solve.
  }
  forward.
  forward.
  Exists result_pointer.
  unfold cstring.
  entailer!.
  { remember (sp_fact2 (Z.to_nat n)) as H5. auto. }
  repeat rewrite <- sp_fact1.
  autorewrite with sublist norm.
  list_solve.
Qed.

Lemma add_above_fact (n : nat):
  Z.of_nat n <> 0 ->
  Z.of_nat n <> 1 ->
  (n =? 1)%nat = false.
Proof.
  intros.
  destruct n.
  - contradiction.
  - destruct n.
    + contradiction.
    + auto.
Qed.

Lemma add_above_fact2 (n a m b : nat):
  ((n =? a)%nat && (m =? b)%nat)%bool = false ->
  n <> a \/ m <> b.
Proof.
  intros.
  apply andb_false_iff in H.
  destruct H.
  - left. intuition. rewrite H0 in H. 
    rewrite Nat.eqb_refl in H. lia.
  - right. intuition. rewrite H0 in H.
    rewrite Nat.eqb_refl in H. lia.
Qed.
  
Lemma add_above_fact3 (n a m b : nat):
  ((n =? a)%nat && negb (m =? b)%nat)%bool = true ->
  n = a /\ m <> b.
Proof.
  intros.
  apply andb_true_iff in H.
  destruct H.
  split.
  - apply Nat.eqb_eq; auto.
  - intuition. subst. 
    rewrite Nat.eqb_refl in H0. lia.
Qed.

Lemma add_above_fact4 (n a m b : nat):
  ((n =? a)%nat && negb (m =? b)%nat)%bool = false ->
  n <> a \/ m = b.
Proof.
  intros.
  apply andb_false_iff in H.
  destruct H.
  - left. intuition. subst. rewrite Nat.eqb_refl in H. lia.
  - right. rewrite negb_false_iff in H. apply Nat.eqb_eq; auto.
Qed.

Lemma add_above_fact5 (n a m b : nat):
  ((n =? a)%nat && (m =? b)%nat)%bool = true ->
  n = a /\ m = b.
Proof.
  intros.
  apply andb_true_iff in H.
  destruct H.
  split; apply Nat.eqb_eq; auto.
Qed.

Lemma body_add_above: semax_body Vprog Gprog f_add_above add_above_spec.
Proof.
  start_function.
  forward_call(t_format, gv).
  Intros result_pointer.
  destruct(eq_dec result_pointer nullval).
  {  forward_if(result_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    forward. contradiction. }
  
  forward_if(result_pointer <> nullval).
  { forward_call. entailer!. }
  { forward. entailer!. }
  Intros.
  forward.
  (* getnw. *)

  unfold mformat.
  Intros sigma0 p0.
  forward_if(
    PROP()
    LOCAL(temp _result result_pointer; gvars gv)
    SEP(concrete_mformat G pointer_G sigma p; 
        concrete_mformat F pointer_F sigma0 p0;
       mformat (add_above G F) result_pointer;
        mem_mgr gv)
  ).
  {
    do 9 forward.
    simpl.
    unfold list_mp in *.
    destruct H10. 
    destruct H4.
    forward_call(Ews, p0, sigma0, gv).                                                                              
    Intros result_to_text_pointer.
    forward.
    entailer!.
    unfold add_above.
    replace (height G) with 0%nat by list_solve.
    unfold concrete_mformat.
    unfold mformat.
    unfold list_mp.
    Exists sigma0 result_to_text_pointer.
    entailer!.
    replace (height G) with 0%nat by list_solve.
    entailer.
  }
  2: {
    forward.
    Exists result_pointer.
    unfold concrete_mformat, mformat.
    Intros result_sigma result_p.
    Exists sigma p.
    Exists sigma0 p0.
    Exists result_sigma result_p.
    entailer!.
  }

  forward.
  forward_if(
    PROP()
    LOCAL(temp _result result_pointer; gvars gv)
    SEP(concrete_mformat G pointer_G sigma p; 
        concrete_mformat F pointer_F sigma0 p0;
       mformat (add_above G F) result_pointer;
        mem_mgr gv)
  ).
  {
    do 9 forward.
    simpl.
    unfold list_mp in *.
    destruct H10. 
    destruct H4.
    forward_call(Ews, p, sigma, gv).                                                                              
    Intros result_to_text_pointer.
    forward.
    unfold add_above.
    assert (HG: exists (k : nat), (height G) = S k). 
    { exists ((height G) - 1)%nat. lia. }
    destruct HG.
    replace (height F) with 0%nat by list_solve.
    rewrite H15.
    unfold concrete_mformat, mformat.
    Exists sigma result_to_text_pointer.
    unfold list_mp in *.
    entailer!.
    rewrite H15.
    replace (height F) with 0%nat by list_solve.
    entailer!.
  }
  forward.
  forward_if(
    PROP()
    LOCAL(temp _t'15 (Val.of_bool (((height G) =? 1)%nat && ((height F) =? 1)%nat)%bool);
          temp _G pointer_G; temp _F pointer_F; gvars gv)
    SEP(malloc_token Ews t_format result_pointer;
        data_at_ Ews t_format result_pointer;
        mem_mgr gv;
        concrete_mformat G pointer_G sigma p;
        concrete_mformat F pointer_F sigma0 p0)
  ).
  {
    forward.
    forward.
    unfold concrete_mformat.
    entailer!.
    replace (height G) with 1%nat by list_solve.
    simpl.
    f_equal.
    apply is_less_than_fact2; auto; list_solve.
  }
  {
    forward.
    unfold concrete_mformat.
    entailer!.
    assert ((height G =? 1)%nat = false) as AA.
    { apply is_less_than_fact1. list_solve. }
    rewrite AA.
    simpl.
    list_solve.
  }
  forward_if(
    PROP()
    LOCAL(temp _middle_width_new (Vint (Int.repr (Z.of_nat (middle_width (add_above G F)))));
          temp _G pointer_G; temp _F pointer_F; gvars gv)
    SEP(malloc_token Ews t_format result_pointer;
        data_at_ Ews t_format result_pointer;
        mem_mgr gv;
        concrete_mformat G pointer_G sigma p;
        concrete_mformat F pointer_F sigma0 p0)
  ).
  {
    unfold concrete_mformat.
    forward.
    unfold concrete_mformat.
    entailer!.
    unfold add_above.
    assert(exists (k : nat), (height G) = S k) as A1.
    { exists (height G - 1)%nat. lia. }
    assert(exists (k : nat), (height F) = S k) as A2.
    { exists (height F - 1)%nat. lia. }
    destruct A1. destruct A2.
    rewrite H25. rewrite H26.
    simpl.
    symmetry in H13.
    apply andb_true_eq in H13.
    destruct H13.
    symmetry in H13, H27.
    apply Nat.eqb_eq in H13.
    rewrite H13 in H25.
    replace x with 0%nat by lia.
    apply Nat.eqb_eq in H27.
    rewrite H27 in H26.
    replace x0 with 0%nat by lia.
    auto.
  }
  {
    forward.
    forward_if(
      PROP()
      LOCAL(temp _t'14 (Val.of_bool (((height G) =? 1)%nat && negb ((height F) =? 1)%nat)%bool);
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      forward.
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      f_equal.
      replace (height G) with 1%nat by list_solve.
      simpl.
      f_equal.
      apply is_less_than_fact2; list_solve.
    }
    {
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      rewrite add_above_fact; auto.
    }
    apply add_above_fact2 in H13.
    forward_if(
      PROP()
      LOCAL(temp _middle_width_new (Vint (Int.repr (Z.of_nat (middle_width (add_above G F)))));
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      do 2 forward.
      forward_call(Z.of_nat (first_line_width F) ,Z.of_nat (middle_width F)).
      Intros max.
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      do 2 f_equal.
      apply add_above_fact3 in H14.
      destruct H14.
      unfold add_above. 
      destruct (height G); try contradiction.
      destruct (height F); try contradiction.
      replace n0 with 0%nat by lia.
      destruct n1.
      { contradiction. }
      simpl.
      list_solve.
    }
    forward.
    forward_if(
      PROP()
      LOCAL(temp _t'13 (Val.of_bool (((height G) =? 2)%nat && ((height F) =? 1)%nat)%bool);
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      do 2 forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      replace (height G) with 2%nat by list_solve.
      simpl.
      f_equal.
      apply is_less_than_fact2; list_solve.
    }
    {
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      replace ((height G) =? 2)%nat with false.
      2: { symmetry. apply Nat.eqb_neq. list_solve. }
      list_solve.
    }

    apply add_above_fact4 in H14.
    forward_if(
      PROP()
      LOCAL(temp _middle_width_new (Vint (Int.repr (Z.of_nat (middle_width (add_above G F)))));
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      apply add_above_fact5 in H15.
      destruct H15.
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      do 3 f_equal.
      unfold add_above.
      destruct (height G).
      { contradiction. }
      destruct (height F).
      { contradiction. }
      destruct n0.
      { lia. }
      destruct n1.
      2: now lia.
      destruct n0.
      2: now lia.
      simpl.
      auto.
    }

    forward.
    forward_if(
      PROP()
      LOCAL(temp _t'12 (Val.of_bool (((height F) =? 1)%nat && negb ((height G) =? 1)%nat)%bool);
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      do 2 forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      f_equal.
      replace (height G =? 1)%nat with false.
      2: { symmetry. apply Nat.eqb_neq. list_solve. }
      ring_simplify. apply is_less_than_fact2.
      all: list_solve.
    }
    {
      forward.
      unfold concrete_mformat; entailer!.
    }

    apply add_above_fact2 in H15.
    forward_if(
      PROP()
      LOCAL(temp _middle_width_new (Vint (Int.repr (Z.of_nat (middle_width (add_above G F)))));
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      apply add_above_fact3 in H16.
      destruct H16.
      do 2 forward.
      forward_call(Z.of_nat (last_line_width G), Z.of_nat (middle_width G)).
      Intros max.
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      do 2 f_equal.
      unfold add_above.
      destruct (height G); try contradiction.
      destruct (height F); try contradiction.
      destruct n0; try contradiction.
      destruct n0.
      { destruct H15; lia. }
      destruct n1.
      2: { lia. }
      simpl. list_solve.
    }
    
    apply add_above_fact4 in H16.
    forward.
    forward_if(
      PROP()
      LOCAL(temp _t'11 (Val.of_bool (((height G) =? 2)%nat && negb ((height F) =? 1)%nat)%bool);
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      do 2 forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      f_equal.
      replace (height G) with 2%nat by list_solve.
      ring_simplify.
      f_equal.
      apply is_less_than_fact2; list_solve.
    }
    {
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      replace (height G =? 2)%nat with false.
      2: { symmetry. apply Nat.eqb_neq. list_solve. }
      list_solve.
    }


    forward_if(
      PROP()
      LOCAL(temp _middle_width_new (Vint (Int.repr (Z.of_nat (middle_width (add_above G F)))));
            temp _G pointer_G; temp _F pointer_F; gvars gv)
      SEP(malloc_token Ews t_format result_pointer;
          data_at_ Ews t_format result_pointer;
          mem_mgr gv;
          concrete_mformat G pointer_G sigma p;
          concrete_mformat F pointer_F sigma0 p0)
    ).
    {
      apply add_above_fact3 in H17.
      destruct H17.
      do 2 forward.
      forward_call(Z.of_nat (first_line_width F), Z.of_nat (middle_width F)).
      Intros max1.
      forward.
      forward_call(Z.of_nat (last_line_width G), max1).
      Intros max2.
      forward.
      entailer!.
      2: { unfold concrete_mformat; entailer!. }
      do 2 f_equal.
      unfold add_above.
      destruct (height G); try contradiction.
      destruct (height F); try contradiction.
      destruct n0.
      { lia. }
      destruct n0.
      2: { lia. }
      destruct n1.
      { lia. }
      simpl.
      list_solve.
    }

    apply add_above_fact4 in H17.
    do 2 forward.
    forward_call(Z.of_nat (first_line_width F), Z.of_nat (middle_width F)).
    Intros max1.
    forward.
    forward_call(Z.of_nat (last_line_width G), max1).
    Intros max2.
    forward.
    forward_call(Z.of_nat (middle_width G), max2).
    Intros max3.
    forward.
    entailer!.
    2: { unfold concrete_mformat; entailer!. }
    do 2 f_equal.
    unfold add_above.
    destruct (height G); try contradiction.
    destruct (height F); try contradiction.
    destruct n0.
    { lia. }
    destruct n0.
    { lia. }
    destruct n1.
    { lia. }
    simpl.
    list_solve.
  }

  forward.
  unfold list_mp in *. destruct H10. destruct H4.
  forward_call(Ews, p, sigma, gv).
  Intros result_to_text.
  forward.
  forward_if(
    EX new_result_pointer : val, EX result_sigma: list (Z * list byte),
    PROP(to_text_eq (to_text (add_above G F)) result_sigma)
    LOCAL(temp _to_text_new new_result_pointer; temp _G pointer_G; temp _F pointer_F; gvars gv)
    SEP(listrep result_sigma new_result_pointer;
        malloc_token Ews t_format result_pointer;
        data_at_ Ews t_format result_pointer;
        mem_mgr gv;
        concrete_mformat G pointer_G sigma p;
        concrete_mformat F pointer_F sigma0 p0)

  ).
  { forward.
    forward_call(Ews, p0, sigma0, gv).
    Intros to_text_tail_pointer.
    forward.
    Exists to_text_tail_pointer sigma0.
    unfold list_mp in *.
    destruct H16.
    entailer!.
    2: { assert(sigma = ([] : list (Z * list byte))).
         { assert(nullval = nullval) as AA.
           { reflexivity. }
           apply H21 in AA.
           auto. }
      subst.
      unfold concrete_mformat. unfold list_mp in *. entailer!.
      unfold listrep.
      entailer!.
    }
    unfold add_above.
    destruct (height G).
    { contradiction. }
    destruct (height F).
    { contradiction. }
    simpl.
    unfold to_text_eq.
    simpl.
    admit.
  }
Admitted.
