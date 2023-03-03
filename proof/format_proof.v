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
    destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)); auto. }
  destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)); auto.
  apply Nat2Z.inj_le in l. lia.
Qed.

Lemma body_less_components: semax_body Vprog Gprog f_less_components less_components_spec.
Proof.
  start_function.
  do 2 forward. 
  getnw. rename FMT_MP into FMT_MP'. getnw.
  destruct FMT_MP, FMT_MP'.
  forward_if(
    EX t1: bool,
    PROP(<< first_comp_eq : t1 = andb 
      ((Z.of_nat (height G)) <=? Z.of_nat (height F))
      ((Z.of_nat (first_line_width G)) <=? Z.of_nat (first_line_width F)) >> 
    )
    LOCAL(temp _t'1 (Val.of_bool t1); temp _G pointer_G; temp _F pointer_F)
    SEP(
      concrete_mformat G pointer_G sigmaG pG;
      concrete_mformat F pointer_F sigmaF pF
    )
  ). 

  { do 3 forward.
    Exists ((Z.of_nat (first_line_width G)) <=? (Z.of_nat (first_line_width F))).
    unfold concrete_mformat. 
    unnw. entailer!. split.
    { apply less_components_fact1; lia. }
    split; apply mk_format_mp; auto. }
  { forward.
    Exists false.
    unfold concrete_mformat; unnw.
    entailer!.
    split; apply mk_format_mp; auto. }

  Intros first_comp.
  forward_if(
    EX t2: bool,
    PROP(<< second_comp_eq : t2 = andb first_comp 
      (((Z.of_nat (middle_width G))) <=?
      (Z.of_nat (middle_width F))) >>)
    LOCAL(temp _t'2 (Val.of_bool t2); temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  ).
  { do 3 forward.
    Exists (first_comp && ((Z.of_nat (middle_width G)) <=? (Z.of_nat (middle_width F))))%bool.
    getnw. 
    unfold concrete_mformat. unnw. subst. entailer!.
    remember ((Z.of_nat (height G) <=? Z.of_nat (height F)) &&
    (Z.of_nat (first_line_width G) <=? Z.of_nat (first_line_width F)))%bool as comp eqn:AA.
    clear AA. subst.
    simpl. apply less_components_fact1; lia. } 
  { forward.
    Exists false.
    entailer!. }

  Intros second_comp.
  forward_if(
    EX t3: bool,
    PROP(<< third_comp_eq : t3 = andb second_comp
      (((Z.of_nat (last_line_width G))) <=?
       (Z.of_nat (last_line_width F))) >>)
    LOCAL(temp _t'3 (Val.of_bool t3); temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  ). 
  { do 3 forward.
    Exists (second_comp && (((Z.of_nat (last_line_width G))) <=? (Z.of_nat (last_line_width F))))%bool.
    unfold concrete_mformat. entailer!. simpl.
    apply less_components_fact1; lia. } 
  { forward.
    Exists false.
    entailer!. }
  Intros third_comp.
  forward.
  Exists (less_components G F).
  entailer!.
  f_equal; unfold less_components; getnw; subst.
  repeat rewrite less_components_fact2; auto.
Qed.

Lemma is_less_than_fact1 x y :
    (x <> y)%nat <-> (x =? y)%nat = false.
Proof.
  remember (Nat.eqb_spec x y) eqn:AA. clear AA. split.
  { intros. destruct r; easy. }
  intros. destruct r; auto. lia.
Qed.

Lemma nat_eq_iff_int_eq x y
    (XBOUND : 0 <= (Z.of_nat x) <= Int.max_unsigned)
    (YBOUND : 0 <= (Z.of_nat y) <= Int.max_unsigned) :
    (x =? y)%nat = Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y)).
Proof.
  destruct (Nat.eqb_spec x y).
  { subst. rewrite Int.eq_true. auto. }
  remember(Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y))) as b eqn:AA.
  destruct b.
  2: lia.
  symmetry in AA. apply Int.same_if_eq in AA.
  apply repr_inj_unsigned in AA; auto. lia.
Qed.
    
Lemma body_is_less_than: semax_body Vprog Gprog f_is_less_than is_less_than_spec.
Proof.
  start_function.
  forward.
  getnw. destruct FMT_MP.
  forward_if(
    EX t1: bool,
    PROP(t1 = andb (negb (Nat.eqb (height G) 1%nat)) (Nat.eqb (height F) 1))
    LOCAL(temp _t'2 (Val.of_bool t1); temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  ). 
  { do 2 forward.
    Exists (negb (height G =? 1)%nat && (height F =? 1)%nat)%bool.
    entailer!.
    2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
    f_equal. 
    assert ((Nat.eqb (height G) 1) = false) as AA. 
    { destruct (eq_dec (height G) 1%nat).
      { rewrite e in *. simpl in *. list_solve. }
      apply is_less_than_fact1. auto. 
    }
    rewrite AA. simpl. apply nat_eq_iff_int_eq.
    { getnw; destruct FMT_MP; lia. }
    unfold Int.max_unsigned; ins; lia. } 
  { forward.
    Exists false.
    entailer!.
    2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
    replace (height G) with 1%nat by lia; ins. }

  unfold concrete_mformat.
  Intros first_comp.
  getnw. destruct FMT_MP.
  forward_if(
    EX t2: bool,
    PROP(t2 = orb first_comp (andb (Nat.eqb (height G) 1%nat) (negb (Nat.eqb (height F) 1%nat))))
    LOCAL(temp _t'3 (Val.of_bool t2); temp _G pointer_G; temp _F pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  ). 
  { forward.
    Exists (first_comp || (height G =? 1)%nat && negb (height F =? 1)%nat)%bool.
    entailer!.
    2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
    remember (negb (height G =? 1)%nat && (height F =? 1)%nat)%bool as comp eqn:AA.
    clear AA. subst. 
    list_solve. } 
  { forward.
    forward_if(
      EX t3: bool,
      PROP(t3 = andb (Nat.eqb (height G) 1%nat) (negb (Nat.eqb (height F) 1%nat)))
      LOCAL(temp _t'3 (Val.of_bool t3); temp _G pointer_G; temp _F pointer_F)
      SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
    ). 
    { do 3 forward.
      Exists ((height G =? 1)%nat && negb (height F =? 1)%nat)%bool.
      entailer!.
      2: { unfold concrete_mformat. entailer!. unnw. apply mk_format_mp; auto. }
      f_equal. replace (height G) with 1%nat by list_solve.
      simpl. f_equal.
      apply nat_eq_iff_int_eq; lia. }
    { forward.
      Exists false.
      entailer!.
      2: { unfold concrete_mformat. entailer!. unnw.
           apply mk_format_mp; auto. }
      assert (height G <> 1%nat). list_solve.
      destruct (Nat.eqb_spec (height G) 1%nat); easy. }
    Intros second_comp.
    Exists (first_comp || second_comp)%bool.
    entailer!.
    replace (negb (height G =? 1)%nat && (height F =? 1)%nat)%bool
      with false; auto. }
  Intros all_comp.
  forward_if. 
  { forward.
    Exists false.
    unfold is_less_than.
    destruct (height G) eqn:AA.
    { destruct (height F) eqn:BB.
      { entailer!; ins. }
      entailer!.
      destruct n; ins. }
    entailer!.
    desf. }

  forward_call(G, F, pointer_G, pointer_F, sigmaG, sigmaF, pG, pF).
  Intros ans; forward.
  Exists (less_components G F).
  entailer!.
  unfold is_less_than; desf.
Qed.

Lemma body_empty: semax_body Vprog Gprog f_empty empty_spec.
Proof.
  start_function.
  forward_call(t_format, gv).
  Intros empty_pointer.
  dest_ptr empty_pointer.
  do 6 forward.

  Exists empty_pointer.
  entailer!.
  unfold mformat.
  Exists ([] : (list (Z * list byte))) (Vlong (Int64.repr 0)).
  unfold concrete_mformat.
  entailer!.
  { now apply mk_format_mp. }
  unfold listrep. entailer!.
Qed.

Lemma list_byte_to_string_length:
  forall (s : list byte),
    Z.of_nat (String.length (list_byte_to_string s)) = Zlength s.
Proof.
  ins.
  induction s.
  { list_solve. }
  unff list_byte_to_string.
  ins. list_solve.
Qed.

Lemma list_byte_to_list_byte_eq:
  forall (s : list byte),
    string_to_list_byte (list_byte_to_string s) = s.
Proof.
  intros.
  induction s.
  { list_solve. }
  unfold list_byte_to_string; fold list_byte_to_string.
  unfold string_to_list_byte; fold string_to_list_byte.
  rewrite IHs.
  assert (Byte.unsigned a < 256).
  { remember (Byte.unsigned_range a).
    unfold Byte.modulus in a0.
    assert(two_power_nat Byte.wordsize = 256 ). list_solve.
    lia. }
  assert ((Z.to_N (Byte.unsigned a) < 256)%N) by list_solve.
  assert ((N_of_ascii (ascii_of_N (Z.to_N (Byte.unsigned a)))) = Z.to_N (Byte.unsigned a)) as AA.
  { now apply N_ascii_embedding. }
  rewrite AA.
  rewrite Z2N.id.
  rewrite Byte.repr_unsigned; auto.
  apply Byte.unsigned_range.
Qed.

Lemma empty_string_app:
  forall (s : string),
    (s ++ "")%string = s.
Proof.
  ins. induction s; ins.
  unfold append; fold append. now rewrite IHs.
Qed.

Lemma string_to_list_byte_app (l1 l2 : string) :
  string_to_list_byte (l1 ++ l2) =
    string_to_list_byte l1 ++ string_to_list_byte l2.
Proof.
  induction l1; ins.
  now rewrite IHl1.
Qed.

Lemma body_line: semax_body Vprog Gprog f_line line_spec.
Proof.
  start_function.
  forward_call(t_format, gv).
  Intros format_pointer.
  dest_ptr format_pointer.
  forward. forward_call(Ews, sigma, p).
  forward. forward_call(Ews, sigma, p).
  forward. forward_call(Ews, sigma, p).
  forward. forward_call(t_list, gv).
  Intros to_text_pointer.
  destruct (eq_dec to_text_pointer nullval). 
  { do 2 forward.
    forward_if(to_text_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    now Intros. }
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
      intros x line.
      rewrite string_to_list_byte_app.
      rewrite list_byte_to_list_byte_eq.
      auto.
    }
    { apply mk_list_mp; auto.
      { simpl. unfold Int.max_unsigned. simpl. lia. }
      list_simplify; simpl; lia. 
    }
    all: unfold line; simpl.
    { unfold Int.max_unsigned. simpl. lia. }
    4: ins.
    all: rewrite list_byte_to_string_length; list_solve.
  }
  unfold listrep.
  unfold cstring.
  Exists (Vlong (Int64.repr 0)) p.
  entailer!.
  unfold line; simpl.
  repeat rewrite list_byte_to_string_length.
  entailer!.
Qed.

Lemma sp_fact1 (n : Z):
  Zrepeat (Byte.repr 32) n = sp_byte (Z.to_nat n).
Proof.
  unfold Zrepeat.
  remember (Z.to_nat n) as m eqn:AA.
  clear AA. clear n.
  induction m; ins.
Qed.

Lemma sp_fact2 (n : nat):
  ~In Byte.zero (sp_byte n).
Proof.
  induction n.
  { list_solve. }
  unfold not in *. unfold sp; fold sp. simpl.
  intros AA. destruct AA as [AA | AA]; auto.
  inv AA.
Qed.

Lemma body_sp : semax_body Vprog Gprog f_sp sp_spec.
Proof.
  start_function.
  forward_call((Tarray tschar (n + 1) noattr), gv).
  { unfold Int.max_unsigned, Ptrofs.max_unsigned in *.
    ins. lia. }
  Intros result_pointer.
  dest_ptr result_pointer.
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
  { forward. Exists 0. entailer!. 
    autorewrite with sublist norm.
    unfold data_at_, data_at, field_at_. entailer!. }
  { Intros i. 
    forward_if.
    { forward. forward. Exists (i + 1). entailer!. list_solve. } 
    forward.
    entailer!.
    autorewrite with sublist norm.
    list_solve.
  }
  do 2 forward.
  Exists result_pointer.
  unfold cstring.
  entailer!.
  { remember (sp_fact2 (Z.to_nat n)) as AA. auto. }
  repeat rewrite <- sp_fact1.
  autorewrite with sublist norm.
  list_solve.
Qed.

Lemma sp_byte_length (n : nat) :
  Zlength (sp_byte n) = Z.of_nat n.
Proof.
  induction n; unfold sp_byte; ins.
  autorewrite with sublist. 
  unfold sp_byte in *; ins. lia.
Qed.

Lemma shifted_text_from_length_element_relation (sigma : list (Z * list byte)) (p : (Z * list byte)) (shift : Z) :
  (<<LIST_MP : list_mp sigma>>) ->
  0 <= fst p <= Int.max_unsigned ->
  0 <= Zlength (snd p) + 1 <= Int.max_unsigned ->
  0 <= shift ->
  Zlength sigma = 0 \/ Zlength sigma = 1 \/
  Zlength (shifted_text_from (sigma ++ [p]) (Z.to_nat shift)) =
  Zlength (shifted_text_from sigma (Z.to_nat shift)) +
  (1 + (fst p) + shift + Zlength (snd p)).
Proof.
  intros.
  induction sigma.
  { list_solve. }
  right; ins.
  destruct a.
  assert (list_mp sigma) as AA.
  { getnw.
    destruct LIST_MP.
    apply mk_list_mp; list_solve. }
  apply IHsigma in AA.
  destruct AA as [AA | AA].
  { left. list_solve. }
  destruct AA as [AA | AA].
  { destruct sigma. 
    { list_solve. }
    right.
    replace (sigma) with ([] : list (Z * list byte)) by list_solve.
    simpl.
    unfold shifted_text_from.
    destruct p0. destruct p.
    autorewrite with sublist norm.
    repeat rewrite sp_byte_length.
    simpl in *.
    getnw. destruct LIST_MP.
    unfold newline_byte.
    list_solve. }
  right; ins.
  unfold shifted_text_from; fold shifted_text_from; ins.
  destruct sigma; ins.
  { unfold shifted_text_from.
    destruct p; ins.
    autorewrite with sublist norm.
    repeat rewrite sp_byte_length.
    list_solve. }
  autorewrite with sublist norm.
  rewrite AA.
  list_solve.
Qed.

Lemma text_from_length_element_relation (sigma : list (Z * list byte)) (p : (Z * list byte)) (shift : Z) (line : list byte) :
  (<<LIST_MP : list_mp sigma>>) ->
  0 <= fst p <= Int.max_unsigned ->
  0 <= Zlength (snd p) + 1 <= Int.max_unsigned ->
  0 <= shift ->
  sigma = [] \/
  Zlength (text_from (sigma ++ [p]) (Z.to_nat shift) (list_byte_to_string line)) =
  Zlength (text_from sigma (Z.to_nat shift) (list_byte_to_string line)) +
  (1 + (fst p) + shift + Zlength (snd p)).
Proof.
  intros.
  getnw. destruct LIST_MP.
  destruct sigma; [left|right]; auto.
  unfold text_from; ins.
  destruct p0.
  destruct sigma; ins.
  { unfold shifted_text_from.
    destruct p.
    autorewrite with sublist norm.
    repeat rewrite list_byte_to_list_byte_eq.
    repeat rewrite sp_byte_length.
    ins. list_solve. }
  destruct sigma; ins.
  { simpl. unfold shifted_text_from.
    destruct p0. destruct p.
    autorewrite with sublist norm.
    simpl in *.
    repeat rewrite sp_byte_length.
    repeat rewrite list_byte_to_list_byte_eq.
    unfold newline_byte.
    list_solve.
  }
  autorewrite with sublist norm.
  simpl in *.
  assert (
    Zlength (shifted_text_from (p0 :: p1 :: sigma ++ [p]) (Z.to_nat shift)) =
    Zlength (shifted_text_from (p0 :: p1 :: sigma) (Z.to_nat shift)) +
    (1 + fst p + shift + Zlength (snd p))
  ) as AA.
  { 
    remember (shifted_text_from_length_element_relation (p0 :: p1 :: sigma) p shift).
    assert (list_mp (p0 :: p1 :: sigma)) as AA. 
    { apply mk_list_mp.
      { list_solve. }
      { inversion list_mp_forall_fst. auto. }
      inversion list_mp_forall_snd. auto.
    }
    assert (0 <= fst p <= Int.max_unsigned) by lia.
    assert (0 <= Zlength (snd p) + 1 <= Int.max_unsigned) by lia.
    assert (0 <= shift) by lia.
    apply o in AA; auto.
    destruct AA as [AA | AA]; [list_solve|]; auto.
    destruct AA as [AA | AA]; [list_solve|]; auto. }
  rewrite AA.
  repeat rewrite sp_byte_length.
  repeat rewrite list_byte_to_list_byte_eq.
  list_solve.
Qed.
  

Lemma text_from_length_relation (sigma : list (Z * list byte)) (i : Z) (shift : Z) (line : list byte) :
  0 <= i < Zlength sigma ->
  (<<LIST_MP : list_mp sigma>>) ->
  0 <= shift ->
  i = 0 \/
  Zlength (text_from (sublist 0 (i + 1) sigma) (Z.to_nat shift) (list_byte_to_string line)) = 
  Zlength (text_from (sublist 0 i sigma) (Z.to_nat shift) (list_byte_to_string line)) + 
  (1 + (fst (Znth i sigma)) + shift + Zlength (snd (Znth i sigma))).
Proof.
  intros.
  getnw.
  destruct LIST_MP.
  remember (Z.to_nat i) as n.
  replace i with (Z.of_nat n) in * by lia .
  clear Heqn.
  destruct n.
  { left. auto. }
  right.
  replace ((sublist 0 (Z.of_nat (S n) + 1) sigma) ) with 
    ((sublist 0 (Z.of_nat (S n)) sigma) ++ [Znth (Z.of_nat (S n)) sigma]) by list_solve.
  enough (
    Zlength (text_from
     (sublist 0 (Z.of_nat (S n)) sigma ++ [Znth (Z.of_nat (S n)) sigma])
     (Z.to_nat shift) (list_byte_to_string line)) =
    Zlength (text_from (sublist 0 (Z.of_nat (S n)) sigma) (Z.to_nat shift) (list_byte_to_string line)) +
    (1 + (fst (Znth (Z.of_nat (S n)) sigma)) + shift + Zlength (snd (Znth (Z.of_nat (S n)) sigma)))) as AA.
  { now rewrite AA. }
  remember (text_from_length_element_relation (sublist 0 (Z.of_nat (S n)) sigma) (Znth (Z.of_nat (S n)) sigma) shift line).
  assert (list_mp (sublist 0 (Z.of_nat (S n)) sigma)) as AA.
  { apply mk_list_mp; list_solve. }
  apply o in AA.
  all: try destruct AA; auto.
  all: list_solve.
Qed.
  

Lemma body_get_applied_length: semax_body Vprog Gprog f_get_applied_length get_applied_length_spec.
Proof.
  start_function. getnw. destruct LIST_MP.
  forward_if (p <> nullval).
  { forward_call(Ews, line, q). forward. 
    getnw. desf. 
    assert (sigma = []) as AA. 
    { list_solve. }
    subst.
    Exists (Zlength line). entailer!.
    unfold text_from.
    rewrite list_byte_to_list_byte_eq. auto.
  }
  { forward. entailer!. }

  destruct sigma. 
  { unfold listrep. Intros. contradiction. }

  Intros.
  unfold listrep; fold listrep.
  destruct p0 as (first_el_shift, first_el_line).
  inversion list_mp_forall_fst as [tmp | tmp1 tmp2 first_el_shift_cond shift_sigma_cond tmp3 ].
  simpl in first_el_shift_cond.
  inversion list_mp_forall_snd as [tmp | tmp10 tmp20 first_el_line_cond line_sigma_cond tmp30].
  simpl in first_el_line_cond.
  Intros to_text_tail_ptr first_el_line_ptr.
  forward.
  forward_call(Ews, first_el_line, first_el_line_ptr). 
  do 3 forward. 
  { entailer!. getnw. desf. }
  remember ((first_el_shift, first_el_line)::sigma) as big_sigma eqn:eqn_big_sigma.
  forward_call(Ews, line, q). 
  forward. 

  forward_loop (
    EX i : Z, EX cur_to_text_ptr : val,
    PROP (1 <= i < Zlength big_sigma + 1)
    LOCAL (temp _total_length (Vptrofs (Ptrofs.repr (Zlength (text_from (sublist 0 i big_sigma) (Z.to_nat shift) (list_byte_to_string line)))));
          temp _to_text_cpy cur_to_text_ptr;
          temp _shift (Vptrofs (Ptrofs.repr shift)))
    SEP( listrep (sublist i (Zlength big_sigma) big_sigma) cur_to_text_ptr;
        lseg (sublist 0 i big_sigma) p cur_to_text_ptr; cstring Ews line q
    )).
  { Exists 1 to_text_tail_ptr.
    entailer!.
    { split.
      { list_solve. }
      do 3 f_equal.
      replace (sublist 0 1 ((first_el_shift, first_el_line) :: sigma)) with
        [(first_el_shift, first_el_line)] by list_solve.
      unfold text_from. rewrite list_byte_to_list_byte_eq.
      autorewrite with sublist. rewrite sp_byte_length.
      list_solve.
    }
    replace ((sublist 1 (Zlength ((first_el_shift, first_el_line) :: sigma)) ((first_el_shift, first_el_line) :: sigma))) with
      sigma by list_solve.
    replace (sublist 0 1 ((first_el_shift, first_el_line) :: sigma)) with
      [(first_el_shift, first_el_line)] by list_solve.
    entailer!.
    unfold lseg.
    Exists to_text_tail_ptr first_el_line_ptr.
    entailer!.
  }
  { entailer!. }
  { assert (i = Zlength big_sigma \/ i < Zlength big_sigma) as AA by lia.
    destruct AA as [AA | AA].
    { subst i.
      replace (sublist (Zlength big_sigma) (Zlength big_sigma) big_sigma) with ([] : list (Z * list byte)) by list_solve.
      unfold listrep. Intros.
      contradiction.
    } 
    replace (sublist i (Zlength big_sigma) big_sigma) with (Znth i big_sigma :: (sublist (i + 1) (Zlength big_sigma) big_sigma)) by list_solve.
    unfold listrep; fold listrep.
    destruct (Znth i big_sigma) as (ith_shift, ith_line) eqn:eqn_ith_element.
    Intros ith_tail_ptr ith_line_ptr.
    forward.
    forward_call(Ews, ith_line, ith_line_ptr).
    do 3 forward.
    { entailer!. unnw. desf. }
    Exists (i + 1, ith_tail_ptr).
    entailer!.
    { split.
      { list_solve. }
      do 2 f_equal.
      remember ((first_el_shift, first_el_line) :: sigma) as big_sigma.
      remember (text_from_length_relation big_sigma i shift line).
      assert (0 <= i < Zlength big_sigma) as AE1 by list_solve.
      apply o in AE1.
      3: now lia.
      2: { apply mk_list_mp; try list_solve. }
      destruct AE1 as [AE | AE].
      { list_solve. }
      rewrite AE. rewrite eqn_ith_element.
      simpl.
      list_solve.
    }
    entailer!.
    assert (
      cstring Ews ith_line ith_line_ptr
      * malloc_token Ews (Tarray tschar (Zlength ith_line + 1) noattr) ith_line_ptr
      * malloc_token Ews t_list cur_to_text_ptr
      * data_at Ews t_list (Vlong (Int64.repr ith_shift), (ith_line_ptr, ith_tail_ptr)) cur_to_text_ptr
      * lseg (sublist 0 i ((first_el_shift, first_el_line) :: sigma)) p cur_to_text_ptr
      |--
      lseg (sublist 0 i ((first_el_shift, first_el_line) :: sigma)) p cur_to_text_ptr
      * (malloc_token Ews (Tarray tschar (Zlength ith_line + 1) noattr) ith_line_ptr
      * cstring Ews ith_line ith_line_ptr
      * malloc_token Ews t_list cur_to_text_ptr
      * data_at Ews t_list (Vlong (Int64.repr ith_shift), (ith_line_ptr, ith_tail_ptr)) cur_to_text_ptr )
    ).
    { entailer!. }
    eapply (derives_trans _ _ _); eauto. 
    assert  (
      lseg (sublist 0 i ((first_el_shift, first_el_line) :: sigma)) p cur_to_text_ptr
      * lseg (sublist i (i + 1) ((first_el_shift, first_el_line) :: sigma)) cur_to_text_ptr ith_tail_ptr
      |-- lseg (sublist 0 (i + 1) ((first_el_shift, first_el_line) :: sigma)) p ith_tail_ptr
    ).
    { remember (lseg_lseg (sublist 0 i ((first_el_shift, first_el_line) :: sigma)) 
      (sublist i (i + 1) ((first_el_shift, first_el_line) :: sigma)) p cur_to_text_ptr ith_tail_ptr) as BB. 
      replace ((sublist 0 (i + 1) ((first_el_shift, first_el_line) :: sigma))) with 
      ((sublist 0 i ((first_el_shift, first_el_line) :: sigma)) ++ (sublist i (i + 1) ((first_el_shift, first_el_line) :: sigma)))
      by list_solve.
      apply BB.
    }
    eapply (derives_trans _ _ _). 2: eauto.
    entailer!.
    replace (sublist i (i + 1) ((first_el_shift, first_el_line) :: sigma)) 
      with [Znth i ((first_el_shift, first_el_line) :: sigma)] by list_solve.
      
    unfold lseg.
    rewrite eqn_ith_element.
    Exists ith_tail_ptr ith_line_ptr.
    entailer!.
  }
  forward.
  remember ((first_el_shift, first_el_line) :: sigma) as big_sigma.
  assert (i < Zlength big_sigma \/ i = Zlength big_sigma) as BB by lia.
  destruct BB.
  { replace ((sublist i (Zlength big_sigma) big_sigma)) with
      (Znth i big_sigma :: ((sublist (i + 1) (Zlength big_sigma) big_sigma))) 
        by list_solve.
    unfold listrep; fold listrep.
    destruct (Znth i big_sigma).
    Intros x y.
    entailer!.
  }
  subst i.
  replace (sublist (Zlength big_sigma) (Zlength big_sigma) big_sigma) 
    with ([] : list (Z * list byte)) by list_solve.
  replace (sublist 0 (Zlength big_sigma) big_sigma)
    with big_sigma by list_solve.
  unfold listrep; fold listrep.
  Intros.
  Exists (Zlength (text_from big_sigma (Z.to_nat shift) (list_byte_to_string line))).
  entailer!.
  apply lseg_null_listrep.
Qed.


Lemma body_format_copy: semax_body Vprog Gprog f_format_copy format_copy_spec.
Proof.
  start_function.
  forward_call(t_format, gv).
  Intros new_format_ptr.
  destruct(eq_dec new_format_ptr nullval). 
  { forward_if(new_format_ptr <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    now Intros.
  }
  forward_if(new_format_ptr <> nullval).
  { forward_call. entailer!. }
  { forward. entailer!. }

  Intros.
  do 9 forward.
  prove_ptr.

  getnw. destruct FMT_MP. destruct format_mp_list_mp.
  forward_call(Ews, pG, sigmaG, gv).
  { list_solve. }

  Intros new_list_ptr.
  do 2 forward.
  Exists new_format_ptr.
  entailer!.
  unfold mformat.
  unfold concrete_mformat.
  Exists sigmaG new_list_ptr; entailer!.
  split; apply mk_format_mp; auto; apply mk_list_mp; auto.
Qed.

Lemma text_from_concat (s1 s2 : list (Z * list byte)) (shift : nat) (line : string):
  s1 <> [] -> s2 <> [] ->
  text_from (s1 ++ s2) shift line = 
  text_from s1 shift EmptyString ++ [Byte.repr 10] ++ shifted_text_from s2 shift ++ string_to_list_byte line.
Proof.
  ins.
  induction s1.
  { ins. }
  ins.
  desf.
  { autorewrite with sublist.
    replace s2 with (p :: l0) by list_solve.
    list_solve. }
  autorewrite with sublist.
  assert (p0 :: l1 <> []) as I by vauto.
  apply IHs1 in I.
  unfold text_from in I.
  desf.
  { inversion Heq. subst.
    replace (shifted_text_from [] shift ) with ([] : list  byte).
    2: { unfold shifted_text_from; auto. }
    autorewrite with sublist.
    list_solve. }
  { autorewrite with sublist in *.
    inversion Heq.
    subst.
    assert (shifted_text_from [(z0, l2)] shift = 
      sp_byte (Z.to_nat z0 + shift) ++ l2) as F.
    { unfold shifted_text_from; auto. }
    rewrite F.
    assert (shifted_text_from ((z0, l2) :: p :: l3) shift =
      sp_byte (Z.to_nat z0 + shift) ++ l2 ++ [Byte.repr 10] ++ (shifted_text_from (p :: l3) shift)) as G.
    { reflexivity. }
    rewrite G.
    list_solve. }
  inversion Heq.
  subst.
  autorewrite with sublist norm in *.
  rewrite <- app_assoc in I; apply app_inv_head in I.
  rewrite <- app_assoc in I; apply app_inv_head in I.
  rewrite <- app_assoc in I; apply app_inv_head in I.
  assert (
    shifted_text_from (p :: l4) shift ++ Byte.repr 10 :: shifted_text_from s2 shift ++ string_to_list_byte line =
    (shifted_text_from (p :: l4) shift ++ Byte.repr 10 :: shifted_text_from s2 shift) ++ string_to_list_byte line
  ) as K.
  { apply (app_assoc 
  (shifted_text_from (p :: l4) shift)
  (Byte.repr 10 :: shifted_text_from s2 shift )
  (string_to_list_byte line)
  ). }
  rewrite K in I.
  apply app_inv_tail in I.
  clear K IHs1 Heq H.
  rewrite <- app_assoc; apply app_inv_head_iff.
  rewrite <- app_assoc; apply app_inv_head_iff.
  assert (
    (Byte.repr 10 :: shifted_text_from ((z0, l2) :: p :: l4) shift) ++ 
    Byte.repr 10 :: shifted_text_from s2 shift ++ string_to_list_byte line = 
    ((Byte.repr 10 :: shifted_text_from ((z0, l2) :: p :: l4) shift) ++ 
    Byte.repr 10 :: shifted_text_from s2 shift) ++ string_to_list_byte line
  ) as K.
  { apply (app_assoc
      (Byte.repr 10 :: shifted_text_from ((z0, l2) :: p :: l4) shift)
      (Byte.repr 10 :: shifted_text_from s2 shift)
      (string_to_list_byte line)
    ). }
  rewrite K.
  clear K.
  assert (Byte.repr 10 :: shifted_text_from ((z0, l2) :: p :: l4 ++ s2) shift ++
     string_to_list_byte line = 
     (Byte.repr 10 :: shifted_text_from ((z0, l2) :: p :: l4 ++ s2) shift ) ++
     string_to_list_byte line) as K.
  { list_solve. }
  rewrite K.
  apply app_inv_tail_iff.
  clear K.
  replace (shifted_text_from ((z0, l2) :: p :: l4 ++ s2) shift)
    with (sp_byte (Z.to_nat z0 + shift) ++ l2 ++ [Byte.repr 10] ++ shifted_text_from (p :: l4 ++ s2) shift)
   by reflexivity.
  replace (shifted_text_from ((z0, l2) :: p :: l4) shift)
    with (sp_byte (Z.to_nat z0 + shift) ++ l2 ++ [Byte.repr 10] ++ shifted_text_from (p :: l4) shift)
    by reflexivity.
  rewrite I.
  list_solve.
Qed.
  
Lemma text_from_line (s : list (Z * list byte)) (shift : nat) (line : string):
  s <> [] ->
  text_from s shift line = text_from s shift EmptyString ++ string_to_list_byte line.
Proof.
  destruct s.
  { ins. }
  ins.
  desf.
  { autorewrite with sublist; list_solve. }
  list_solve.
Qed.

Lemma sp_eq_sp_byte (n : nat):
  string_to_list_byte (sp n) = sp_byte n.
Proof.
  induction n.
  { reflexivity. }
  unfold sp_byte; ins.
  rewrite IHn.
  unfold sp_byte; auto.
Qed.

Lemma sp_byte_app (n m : nat):
  sp_byte (n + m) = sp_byte n ++ sp_byte m.
Proof.
  unfold sp_byte.
  apply repeat_app.
Qed.

Lemma text_from_shifted_text_from_iff (s : list (Z * list byte)) (shift : nat):
  s <> [] ->
  sp_byte shift ++ text_from s shift EmptyString = shifted_text_from s shift.
Proof.
  destruct s.
  { ins. }
  ins; desf.
  { unfold shifted_text_from.
    autorewrite with sublist.
    rewrite app_assoc.
    apply app_inv_tail_iff.
    rewrite <- sp_byte_app.
    f_equal; lia. }
  autorewrite with sublist.
  replace (shifted_text_from ((z, l) :: p :: l0) shift) with 
    (sp_byte (Z.to_nat z + shift) ++ l ++ [Byte.repr 10] ++ shifted_text_from (p :: l0) shift) by auto.
  rewrite Nat.add_comm.
  rewrite sp_byte_app.
  list_solve.
Qed.
  