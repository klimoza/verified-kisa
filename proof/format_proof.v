Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import Coq.Strings.Ascii.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition max_spec : ident * funspec := 
DECLARE _max
  WITH a : Z, b : Z
  PRE [ tuint, tuint ]
    PROP (
      0 <= a <= Int.max_unsigned;
      0 <= b <= Int.max_unsigned
    )
    PARAMS (Vint (Int.repr a); Vint (Int.repr b))
    SEP ()
  POST [ tuint ] EX q : Z,
    PROP (q = Z.max a b) 
    RETURN (Vint (Int.repr q)) 
    SEP().
    
Definition strlen_spec :=
 DECLARE _strlen
  WITH sh: share, s : list byte, str: val
  PRE [ tptr tschar ]
    PROP (readable_share sh)
    PARAMS (str)
    SEP (cstring sh s str)
  POST [ size_t ]
    PROP ()
    RETURN (Vptrofs (Ptrofs.repr (Zlength s)))
    SEP (cstring sh s str).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH wsh: share, rsh: share, dest : val, n : Z, src : val, s : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (writable_share wsh; readable_share rsh; Zlength s < n)
    PARAMS (dest; src)
    SEP (data_at_ wsh (tarray tschar n) dest; cstring rsh s src)
  POST [ tptr tschar ]
    PROP ()
    RETURN (dest)
    SEP (cstringn wsh s n dest; cstring rsh s src).

Definition t_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list (Z * (list byte))) (p: val) : mpred :=
 match sigma with
 | (a, b)::hs =>
    EX x:val, EX y: val,
    cstring Ews b y *
    data_at Ews t_list ((Vint (Int.repr a), (y, x)) : @reptype CompSpecs t_list) p *
    listrep hs x
 | nil =>
    !! (p = nullval) && emp
 end.

Fixpoint lseg (sigma: list (Z * (list byte))) (x z: val) : mpred :=
  match sigma with
  | nil => !! (x = z) && emp
  | (a, b)::hs => EX h: val, EX y:val, 
        cstring Ews b y *
        data_at Ews t_list ((Vint (Int.repr a)), (y, h)) x * 
        lseg hs h z
  end.

Arguments lseg sigma x z : simpl never.

Definition list_copy_spec : ident * funspec :=
DECLARE _list_copy
  WITH sh : share, p : val, s : list (Z * (list byte)), gv: globals
  PRE [ tptr t_list ]
    PROP(0 <= Zlength s <= Ptrofs.max_unsigned;
         Forall (fun x => 0 <= (fst x) <= Int.max_unsigned /\ 0 <= Zlength (snd x) + 1 <= Ptrofs.max_unsigned) s)
    PARAMS(p) GLOBALS(gv)
    SEP(listrep s p; mem_mgr gv)
  POST [ tptr t_list ] 
    EX q: val,
    PROP(p <> nullval -> p <> q)
    RETURN(q)
    SEP(listrep s q; listrep s p; mem_mgr gv).


Definition t_format := Tstruct _t noattr.

Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a))
                                      :: string_to_list_byte s'
  end.

Fixpoint text_from (sigma : list (Z * list byte)) : list byte :=
  match sigma with 
  | nil => nil
  | (s, l)::hs => (repeat (Byte.repr (Z.of_N 32)) (Z.to_nat s) ) ++ l ++ text_from hs
end.

Definition to_text_eq (to_text : nat -> string -> string) (sigma : list (Z * list byte)) :=
  string_to_list_byte (to_text (Z.to_nat 0) EmptyString) = text_from sigma.


Definition mformat (G : t) (x : val) : mpred := 
  EX sigma : list (Z * list byte),
  EX p : val,
  !! (to_text_eq G.(to_text) sigma) &&
  !! (0 <= Z.of_nat (height G) <= Int.max_unsigned) &&
  !! (0 <= Z.of_nat (first_line_width G) <= Int.max_unsigned) &&
  !! (0 <= Z.of_nat (middle_width G) <= Int.max_unsigned) &&
  !! (0 <= Z.of_nat (last_line_width G) <= Int.max_unsigned) &&
  data_at Ews t_format (Vint (Int.repr (Z.of_nat G.(height))),
                        (Vint (Int.repr (Z.of_nat G.(first_line_width))),
                         (Vint (Int.repr (Z.of_nat G.(middle_width))),
                          (Vint (Int.repr (Z.of_nat G.(last_line_width))), p)))) x *
  listrep sigma p
 .

 Definition concrete_mformat (G : t) (x : val) (sigma : list (Z * list byte)) (p : val) : mpred :=
  !! (to_text_eq G.(to_text) sigma) &&
  !! (to_text_eq G.(to_text) sigma) &&
  !! (0 <= Z.of_nat (height G) <= Int.max_unsigned) &&
  !! (0 <= Z.of_nat (first_line_width G) <= Int.max_unsigned) &&
  !! (0 <= Z.of_nat (middle_width G) <= Int.max_unsigned) &&
  !! (0 <= Z.of_nat (last_line_width G) <= Int.max_unsigned) &&
  sepcon 
  (data_at Ews t_format (Vint (Int.repr (Z.of_nat G.(height))),
                        (Vint (Int.repr (Z.of_nat G.(first_line_width))),
                         (Vint (Int.repr (Z.of_nat G.(middle_width))),
                          (Vint (Int.repr (Z.of_nat G.(last_line_width))), p)))) x)
  (listrep sigma p)
.


 Definition less_components_spec : ident * funspec :=
 DECLARE _less_components
  WITH p : val, G : t, q : val, G' : t
  PRE [ tptr t_format, tptr t_format]
    PROP()
    PARAMS(p; q)
    SEP(mformat G p; mformat G' q)
  POST [ tbool ]
    EX a : bool,
    PROP(a = less_components G G')
    RETURN(Val.of_bool a)
    SEP(mformat G p; mformat G' q).


Definition is_less_than_spec : ident * funspec :=
DECLARE _is_less_than
  WITH p : val, G : t, q : val, G' : t
  PRE [ tptr t_format, tptr t_format]
    PROP()
    PARAMS(p; q)
    SEP(mformat G p; mformat G' q)
  POST [ tbool ]
    EX a : bool,
    PROP(a = is_less_than G G')
    RETURN(Val.of_bool a)
    SEP(mformat G p; mformat G' q).

(* ================================================================= *)


Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   max_spec; strlen_spec; strcpy_spec; list_copy_spec;
                   less_components_spec; is_less_than_spec
 ]).

(* ================================================================= *)

Lemma body_max: semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function. 
  forward_if.
  - forward. Exists b. entailer!.
  - forward. Exists a. entailer!.
Qed.

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
Intros.
forward.

forward_loop  (EX i : Z,
  PROP (0 <= i < Zlength s + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength s + 1))
          (map Vbyte (s ++ [Byte.zero])) str)).

assert (Example: Archi.ptr64=false -> 
          forall n, Vptrofs (Ptrofs.repr n) = Vint (Int.repr n)). {
 intro Hx; try discriminate Hx.
 
all:  intros.
all:  hint.
all:  autorewrite with norm.
all:  auto.
} clear Example.

* Exists 0. entailer.
* Intros i. forward. forward_if. forward. entailer!. 
  repeat f_equal. cstring.
  forward. entailer. Exists (i + 1). entailer!.
  assert(0 <= i + 1 < Zlength (s ++ [Byte.zero])).
  assert (i < Zlength s) by cstring.
  autorewrite with sublist.
  cstring.
  autorewrite with sublist in H6. simpl in H6.
  apply H6.
Qed.

Lemma body_strcpy: semax_body Vprog Gprog f_strcpy strcpy_spec.
Proof.
start_function.

unfold cstring,cstringn in *.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength s + 1)
  LOCAL (temp _i (Vptrofs (Ptrofs.repr i)); temp _dest dest; temp _src src)
  SEP (data_at wsh (tarray tschar n)
        (map Vbyte (sublist 0 i s) ++ Zrepeat Vundef (n - i)) dest;
       data_at rsh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) src)).
+ Exists 0. entailer.
+ Intros i. forward. forward. forward. forward_if.
  * forward. entailer!. apply derives_refl'. f_equal.
    rewrite upd_Znth_app2. {
      assert (i - Zlength (map Vbyte (sublist 0 i s)) = 0). list_solve.
      rewrite H12. unfold Zrepeat.
      remember (Z.to_nat (n - i)). destruct n0. lia.
      simpl. 
      assert (i = Zlength s). cstring.
      replace (Z.to_nat (n - (Zlength s + 1))) with n0 by lia.
      list_solve.
    } {
      list_solve.
    }
  * forward. Exists (i + 1). entailer!. 
    assert (0 <= i + 1 < (Zlength (s ++ [Byte.zero]))).
    assert (i < Zlength s) by cstring.
    autorewrite with sublist.
    cstring.
    autorewrite with sublist in H11. simpl in H11.
    apply H11. rewrite upd_Znth_app2. list_solve.
    list_solve.
Qed.

Arguments listrep sigma p : simpl never.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
  intros.

  revert p; induction sigma; intros p.
  - unfold listrep. entailer!. split; auto.
  - unfold listrep; fold listrep. destruct a. entailer. entailer!. split; intro.
    + subst p. eapply field_compatible_nullval; eauto.
    + inversion H3.
Qed.
#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 intros.
 unfold listrep. destruct sigma; simpl.
  - entailer!.
  - destruct p0. Intros x y. auto with valid_pointer.
Qed.
#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

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
  + remember (Z.of_nat y) as Y.
    remember (Z.of_nat x) as X.
    assert (X <= Y \/  X > Y). lia.
    destruct H1. {
      remember (Int.ltu (Int.repr Y) (Int.repr X)).
      destruct b.
      symmetry in Heqb.
      apply ltu_inv in Heqb.
      repeat rewrite Int.unsigned_repr in Heqb by auto.
      lia. lia.
    } {
      remember (Int.ltu (Int.repr Y) (Int.repr X)).
      destruct b.
      - destruct (Z.leb_spec0 X Y).
        + lia.
        + lia.
      - lia.
    }
  + remember (Z.of_nat y) as Y.
    remember (Z.of_nat x) as X.
    assert (X <= Y \/  X > Y). lia.
    destruct H1. {
      remember (Int.ltu (Int.repr Y) (Int.repr X)).
      destruct b. lia.
      symmetry in Heqb.
      apply ltu_false_inv in Heqb.
      repeat rewrite Int.unsigned_repr in Heqb by auto.
      destruct (Z.leb_spec0 X Y).
      lia. lia.
    } {
      remember (Int.ltu (Int.repr Y) (Int.repr X)).
      destruct b. lia.
      symmetry in Heqb.
      apply ltu_false_inv in Heqb.
      repeat rewrite Int.unsigned_repr in Heqb by auto.
      lia.
    }
Qed.
  
Lemma less_components_fact2:
  forall (x y : nat),
  ((Z.of_nat x)) <=? (Z.of_nat y) = (Nat.leb x y).
Proof.
  intros.
  destruct (Nat.leb_spec0 x y).
  - apply inj_le in l.
    destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)).
    + auto.
    + auto.
  - destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)).
    + apply Nat2Z.inj_le in l. lia.
    + auto.
Qed.

Lemma body_less_components: semax_body Vprog Gprog f_less_components less_components_spec.
Proof.
  start_function.
  unfold mformat.
  Intros sigmaG pG.
  Intros sigmaG' pG'.
  forward.
  forward.
  forward_if(
    EX t1: bool,
    PROP(t1 = andb 
    ((Z.of_nat (height G)) <=? Z.of_nat (height G'))
    ((Z.of_nat (first_line_width G)) <=? Z.of_nat (first_line_width G'))
    )
    LOCAL(temp _t'1 (Val.of_bool t1); temp _G p; temp _F q)
    SEP(
          concrete_mformat G p sigmaG pG;
          concrete_mformat G' q sigmaG' pG'
    )
  ). {
  forward.
  forward.
  forward.
  Exists ((Z.of_nat (first_line_width G)) <=? (Z.of_nat (first_line_width G'))).
  unfold mformat.
  entailer!.
  + apply less_components_fact1; auto.
  + unfold concrete_mformat. entailer!.
  } {
  forward.
  Exists false.
  entailer.
  unfold concrete_mformat.
  entailer!.
  }

  Intros first_two_comp.
  forward_if(
    EX t2: bool,
    PROP(t2 = andb first_two_comp 
      (((Z.of_nat (middle_width G))) <=?
      (Z.of_nat (middle_width G'))))
    LOCAL(temp _t'2 (Val.of_bool t2); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ). {
    unfold concrete_mformat.
    Intros.
    forward.
    forward.
    forward.
    Exists (first_two_comp && ((Z.of_nat (middle_width G)) <=? (Z.of_nat (middle_width G'))))%bool.
    entailer!.
    + rewrite H10. simpl. apply less_components_fact1; auto.
    + unfold concrete_mformat. entailer!.
  } {
    forward.
    Exists false.
    entailer!.
  }

  Intros first_three_comp.
  forward_if(
    EX t3: bool,
    PROP(t3 = andb first_three_comp
      (((Z.of_nat (last_line_width G))) <=?
       (Z.of_nat (last_line_width G'))))
    LOCAL(temp _t'3 (Val.of_bool t3); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ). {
    unfold concrete_mformat.
    Intros.
    forward.
    forward.
    forward.
    Exists (first_three_comp && (((Z.of_nat (last_line_width G))) <=? (Z.of_nat (last_line_width G'))))%bool.
    entailer!.
    + rewrite H11. simpl. apply less_components_fact1; auto.
    + unfold concrete_mformat. entailer!.
  } {
    forward.
    Exists false.
    entailer!.
  }

  Intros comparison.
  forward.
  Exists (less_components G G').
  entailer!.

  + f_equal. unfold less_components. repeat rewrite less_components_fact2. auto.
  + unfold concrete_mformat. unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!.
Qed.

Lemma is_less_than_fact1:
  forall (x y : nat),
    (x <> y)%nat <-> (x =? y)%nat = false.
Proof.
  intros.
  remember (Nat.eqb_spec x y).
  clear Heqr.
  split.
  - intros. destruct r. contradiction. auto.
  - intros. destruct r. lia. auto.
Qed.

Lemma is_less_than_fact2:
  forall (x y : nat),
    (0 <= (Z.of_nat x) <= Int.max_unsigned) ->
    (0 <= (Z.of_nat y) <= Int.max_unsigned) ->
    (x =? y)%nat = Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y)).
Proof.
  intros.
  destruct (Nat.eqb_spec x y).
  - subst. rewrite Int.eq_true. auto.
  - remember(Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y))).
    destruct b.
    + symmetry in Heqb. apply Int.same_if_eq in Heqb. apply repr_inj_unsigned in Heqb; auto. lia.
    + lia.
Qed.
    
Lemma body_is_less_than: semax_body Vprog Gprog f_is_less_than is_less_than_spec.
Proof.
  start_function.
  unfold mformat.
  Intros sigmaG pG sigmaG' pG'.
  forward.
  forward_if(
    EX t1: bool,
    PROP(t1 = andb (negb (Nat.eqb (height G) 1%nat)) (Nat.eqb (height G') 1))
    LOCAL(temp _t'2 (Val.of_bool t1); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ). {
    forward.
    forward.
    Exists (negb (height G =? 1)%nat && (height G' =? 1)%nat)%bool.
    entailer!.
    - f_equal. 
      assert ((Nat.eqb (height G) 1) = false). destruct (eq_dec (height G) 1%nat).
      + rewrite e in H9. simpl in H9. list_solve.
      + apply is_less_than_fact1. auto.
      + rewrite H17. simpl. apply is_less_than_fact2; auto. simpl. 
        unfold Int.max_unsigned. simpl. lia.
    - unfold concrete_mformat. entailer!.
  } {
    forward.
    Exists false.
    entailer!.
    - assert (height G = 1%nat). lia. rewrite H16. simpl. auto.
    - unfold concrete_mformat. entailer!.
  }

  Intros first_comp.
  forward_if(
    EX t2: bool,
    PROP(t2 = orb first_comp (andb (Nat.eqb (height G) 1%nat) (negb (Nat.eqb (height G') 1%nat))))
    LOCAL(temp _t'3 (Val.of_bool t2); temp _G p; temp _F q)
    SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
  ). {
    forward.
    Exists (first_comp || (height G =? 1)%nat && negb (height G' =? 1)%nat)%bool.
    entailer!.
    rewrite H10. list_solve.
  } {
    forward.
    forward_if(
      EX t3: bool,
      PROP(t3 = andb (Nat.eqb (height G) 1%nat) (negb (Nat.eqb (height G') 1%nat)))
      LOCAL(temp _t'3 (Val.of_bool t3); temp _G p; temp _F q)
      SEP(concrete_mformat G p sigmaG pG; concrete_mformat G' q sigmaG' pG')
    ). {
      forward.
      forward.
      forward.
      Exists ((height G =? 1)%nat && negb (height G' =? 1)%nat)%bool.
      entailer!.
      - f_equal. replace (height G) with 1%nat by list_solve. simpl. f_equal.
        apply is_less_than_fact2; auto. simpl. unfold Int.max_unsigned. simpl. lia.
      - unfold concrete_mformat. entailer!.
    } {
      forward.
      Exists false.
      entailer!.
      assert (height G <> 1%nat). list_solve.
      destruct (Nat.eqb_spec (height G) 1%nat).
      + contradiction.
      + auto.
      + unfold concrete_mformat. entailer!.
    }
    Intros second_comp.
    Exists (first_comp || second_comp)%bool.
    entailer!.
    rewrite H10.
    simpl.
    f_equal.
  }
  Intros all_comp.
  forward_if. {
    forward.
    Exists false.
    unfold is_less_than.
    destruct (height G).
    - destruct (height G').
      + simpl. simpl in H11. lia.
      + destruct n.
        * unfold concrete_mformat. unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!.
        * simpl in H11. lia.
    - destruct n.
      + destruct (height G').
        * unfold concrete_mformat. unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!.
        * destruct n.  
          { simpl in H11. lia. }
          { unfold concrete_mformat. unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!. }
      + destruct (height G').
        * simpl in H11. lia.
        * destruct n0.
          { unfold concrete_mformat. unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!. }
          { simpl in H11. lia. }
  }

  forward_call(p, G, q, G').
  - unfold concrete_mformat. unfold mformat. Exists sigmaG pG sigmaG' pG'. entailer!.
  - Intros ans. forward.
    Exists (less_components G G').
    entailer!.
    unfold is_less_than. {
      destruct (height G).
      - destruct (height G').
        + auto.
        + destruct n.
          * simpl in H11. lia.
          * auto.
      - destruct n.
        + destruct (height G').
          * simpl in H11. lia.
          * destruct n.
            { auto. }
            { simpl in H11. lia. }
        + destruct (height G').
          * auto.
          * destruct n0.
            { simpl in H11. lia. }
            { auto. }
    }
Qed.

Lemma list_copy_length_fact:
  forall (A : Type) (t : list A),
  Z.to_nat (Zlength t) = Datatypes.length t.
Proof.
  intros.
  induction t.
  - list_solve.
  - rewrite Zlength_cons. simpl. 
    rewrite <- IHt. list_solve.
Qed.

Lemma list_copy_fact1:
  forall (A : Type) (i : Z) (t : list A),
    0 <= i ->
    skipn (Z.to_nat i) t = sublist i (Zlength t) t.
Proof.
  intros. 
  unfold sublist.
  f_equal.
  rewrite list_copy_length_fact.
  symmetry.
  apply firstn_exact_length.
Qed.

Lemma list_copy_fact2:
  forall (A : Type) (t : list A),
  Z.to_nat (Zlength t) =  Datatypes.length (firstn (Z.to_nat (Zlength t + 1)) t).
Proof.
  intros.
  induction t.
  - list_solve.
  - replace (Zlength (a :: t)) with (Zlength t + 1) by list_solve.
    replace (Z.to_nat (Zlength t + 1 + 1)) with (S (Z.to_nat (Zlength t + 1))) by list_solve.
    rewrite firstn_cons.
    simpl.
    rewrite <- IHt.
    list_solve.
Qed.



Lemma body_list_copy: semax_body Vprog Gprog f_list_copy list_copy_spec.
Proof.
  start_function.

  forward_if. { 
    forward. destruct s.
      - unfold listrep. Exists nullval. entailer!.
      - unfold listrep; fold listrep. destruct p. 
        destruct H2. assert (nullval = nullval). auto.
        apply H1 in H3. inversion H3. 
  }

  forward_call(t_list, gv).
  Intros vret. destruct (eq_dec vret nullval). {
    forward_if (vret <> nullval).
      - forward_call; entailer.
      - forward; entailer.
      - Intros. contradiction.
  }
  
  forward_if (vret <> nullval).
  { forward_call; entailer. }
  { forward; entailer. }

  Intros. destruct s. 
  { unfold listrep. Intros. contradiction. }
  unfold listrep; fold listrep.
  destruct p0.
  Intros x y.
  forward.
  forward.
  forward.
  forward_call(Ews, l, y).
  inversion H0. simpl in H4.
  destruct H4.
  forward_call((Tarray (Tint I8 Signed noattr) (Zlength l + 1) noattr), gv). {
    unfold sizeof.
    unfold Ctypes.sizeof.
    list_solve.
  }
  Intros vret0.
  forward.
  forward.
  destruct (eq_dec vret0 nullval). {
    forward_if (vret0 <> nullval).
    - forward_call. entailer.
    - forward. entailer.
    - forward. contradiction.
  }
  forward_if(vret0 <> nullval). 
  { forward_call. entailer. }
  { forward. entailer. }
  
  Intros.
  forward.
  forward.
  forward_call(Ews, Ews, vret0, (Zlength l + 1), y, l).
  forward.
  forward.
  forward. subst. clear H5 H6 H4. 
  remember ((z, l) :: s) as t.
  forward_while(
    EX i : Z, EX cur_tail : val, EX l_tail : val,
    PROP(0 <= i < Zlength t + 1;
         cur_tail <> nullval)
    LOCAL(temp _l l_tail; gvars gv; temp _cur_tail cur_tail) 
    SEP(mem_mgr gv; 
        malloc_token Ews (Tarray (Tint I8 Signed noattr) (Zlength l + 1) noattr) vret0;
        malloc_token Ews t_list cur_tail;
        lseg (sublist 0 i t) cur_tail vret;
        listrep (sublist i (i + 1) t) cur_tail;
        lseg (sublist 0 (i + 1) t) p l_tail;
        listrep (sublist (i + 1) (Zlength s + 1) t) l_tail)).
  - Exists 0 vret x. entailer.
    replace (sublist 1 (Zlength s + 1) ((z, l) :: s)) with s by list_solve.
    replace (sublist 0 1 ((z, l) :: s)) with [(z, l)] by list_solve.
    unfold lseg; fold lseg.
    Exists x y.
    unfold cstringn.
    unfold cstring.
    entailer!; try list_solve.
    replace (Zrepeat Vundef (Zlength l + 1 - (Zlength l + 1))) with ([] : (list val)) by list_solve.
    replace ((map Vbyte (l ++ [Byte.zero]) ++ [])) with ((map Vbyte (l ++ [Byte.zero]))) by list_solve.
    simpl.
    rewrite sublist_nil'; try lia.
    replace (sublist 0 1 ((z, l) :: s)) with [(z, l)] by list_solve.
    unfold lseg.
    unfold listrep.
    Exists (Vlong (Int64.repr 0)) vret0.
    unfold cstring.
    entailer!.
  - entailer!.
  - forward_call(t_list, gv).
    Intros cur_tail_tail.
    remember (sublist 0 (i + 1) t) as processed_part.
    
    destruct processed_part as [ |first_element processed_part]. {
      destruct t. 
      - replace (sublist i (i + 1) []) with ([] : list (Z * list byte)) by list_solve.
        unfold listrep; fold listrep.
        Intros. 
        contradiction.
      - destruct (eq_dec i 0).
        + subst. replace (sublist 0 (0 + 1) (p0 :: t)) with [p0] in Heqprocessed_part by list_solve.
          inversion Heqprocessed_part.
        + unfold sublist in Heqprocessed_part.
          unfold skipn in Heqprocessed_part. simpl in Heqprocessed_part.
          replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Heqprocessed_part by list_solve.
          rewrite firstn_cons in Heqprocessed_part.
          inversion Heqprocessed_part.
    }

    destruct (eq_dec cur_tail_tail nullval). {
      destruct (sublist i (i + 1) t).
      + unfold listrep; fold listrep. Intros. contradiction.
      + unfold listrep; fold listrep.
        destruct p0. Intros x0 y0.
        forward.
        forward.
        forward_if(cur_tail_tail <> nullval). 
        - forward_call. entailer.
        - forward. entailer.
        - forward. contradiction.
    }
    Intros.

    remember (sublist i (i + 1) t) as current_processed.
    destruct (current_processed) as [| current_processed_element empty_proccessed]. {
      unfold listrep; fold listrep. Intros. contradiction.
    }
    unfold listrep; fold listrep. destruct current_processed_element as (current_shift, current_line).
    Intros empty_proccessed_address current_line_address.
    forward.
    forward.
    forward_if(cur_tail_tail <> nullval). 
    { forward_call. entailer. }
    { forward. entailer. }
    forward.

    remember (sublist (i + 1) (Zlength s + 1) t) as not_processed.
    destruct not_processed as [| not_processed_element  not_processed]. {
      unfold listrep; fold listrep. Intros. contradiction.
    }
    unfold listrep; fold listrep. destruct not_processed_element as (not_processed_shift, not_processed_line).
    Intros not_processed_address not_processed_line_address.
    forward.
    forward.
    forward.
    
    forward_call(Ews, not_processed_line, not_processed_line_address).
    forward_call((Tarray (Tint I8 Signed noattr) (Zlength not_processed_line + 1) noattr), gv). {
      unfold sizeof.
      unfold Ctypes.sizeof.
      assert (In (not_processed_shift, not_processed_line) t).
      assert (skipn (Z.to_nat (i + 1)) t = sublist (i + 1) (Zlength s + 1) t). 
      replace (Zlength s + 1) with (Zlength t) by list_solve.
      apply list_copy_fact1. lia.
      rewrite <- H4 in Heqnot_processed.
      assert (In (not_processed_shift, not_processed_line) (skipn (Z.to_nat (i + 1)) t)). 
      rewrite <- Heqnot_processed. simpl. auto.
      apply initialize.In_skipn in H5. auto.
      split; try lia.
      remember (computable_theorems.Forall_forall1 _ _ H0 (not_processed_shift, not_processed_line) H4).
      simpl in a. list_solve.
    }
    
    Intros current_tail_line_address.
    destruct (eq_dec current_tail_line_address nullval). {
      forward.
      forward.
      forward_if(current_tail_line_address <> nullval).
      - forward_call. entailer.
      - forward. entailer.
      - forward. contradiction.
    }
    Intros.
    forward.
    forward.
    forward_if (current_tail_line_address <> nullval).
    { forward_call. entailer. }
    { forward. entailer. }
    forward. forward.

    forward_call(Ews, Ews, current_tail_line_address, (Zlength not_processed_line + 1), not_processed_line_address, not_processed_line).
    forward.
    forward.

    Exists (i + 1, cur_tail_tail, not_processed_address).
    entailer.
    
    unfold cstring.
    unfold cstringn.
    entailer.

    entailer!.
    + assert(i = Zlength ((z, l) :: s) \/ i < Zlength ((z, l) :: s)).
      lia.
      destruct H31. subst. 
      assert (sublist (Zlength ((z, l) :: s)) (Zlength ((z, l) :: s) + 1) 
      ((z, l) :: s) = []). 
      unfold sublist.
      
      assert ((Z.to_nat (Zlength ((z, l) :: s))) = Datatypes.length (firstn (Z.to_nat (Zlength ((z, l) :: s) + 1)) ((z, l) :: s))).
      apply list_copy_fact2.
      rewrite H31.
      apply (skipn_exact_length (firstn (Z.to_nat (Zlength ((z, l) :: s) + 1)) ((z, l) :: s))).
      rewrite H31 in Heqcurrent_processed.
      inversion Heqcurrent_processed.
      list_solve.
    + assert (not_processed = sublist (i + 1 + 1) (Zlength s + 1) ((z, l) :: s)).
      remember Heqnot_processed as Heqnot_processed2.
      clear HeqHeqnot_processed2.
      rewrite sublist_next in Heqnot_processed2; try list_solve.
      inversion Heqnot_processed2; try list_solve.
      assert(i = Zlength ((z, l) :: s) \/ i < Zlength ((z, l) :: s)). lia.
      destruct H31. subst. assert (sublist (Zlength ((z, l) :: s)) (Zlength ((z, l) :: s) + 1)  ((z, l) :: s) = []). 
      unfold sublist.
      assert ((Z.to_nat (Zlength ((z, l) :: s))) = Datatypes.length (firstn (Z.to_nat (Zlength ((z, l) :: s) + 1)) ((z, l) :: s))).
      apply list_copy_fact2.
      rewrite H31.
      apply (skipn_exact_length (firstn (Z.to_nat (Zlength ((z, l) :: s) + 1)) ((z, l) :: s))).
      rewrite H31 in Heqcurrent_processed.
      inversion Heqcurrent_processed.
      list_solve.
      
      rewrite <- H31.
      entailer!.

      remember (sublist (i + 1) (i + 1 + 1) ((z, l) :: s)) as cur_tail_tail_list.

      assert (i < Zlength s ). {
        assert (i >= Zlength s \/ i < Zlength s). lia.
        destruct H31.
        - assert(sublist (i + 1) (Zlength s + 1) ((z, l) :: s) = []). 
          assert (i + 1 >= Zlength s + 1). lia.
          assert (i < Zlength s + 2). list_solve.
          apply sublist_nil_gen. lia.
          rewrite H32 in Heqnot_processed.
          inversion Heqnot_processed.
        - apply H31.
      }

      rewrite sublist_next in Heqcur_tail_tail_list.
      2: lia.
      2: list_solve.

      rewrite Heqcur_tail_tail_list.
      unfold listrep; fold listrep.
      destruct (Znth (i + 1) ((z, l) :: s)).
      
Admitted.
      
