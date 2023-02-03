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

Definition strcat_spec :=
 DECLARE _strcat
  WITH wsh: share, rsh: share, dest : val, n : Z, src : val, b : list byte, s : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (writable_share wsh; readable_share rsh; Zlength b + Zlength s < n)
    PARAMS (dest; src)
    SEP (cstringn wsh b n dest; cstring rsh s src)
  POST [ tptr tschar]
    PROP ()
    RETURN (dest)
    SEP (cstringn wsh (b ++ s) n dest; cstring rsh s src).

Definition t_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list (Z * (list byte))) (p: val) : mpred :=
 match sigma with
 | (a, b)::hs =>
    EX x:val, EX y: val,
    (emp || malloc_token Ews (Tarray tschar (Zlength b + 1) noattr) y) *
    cstring Ews b y *
    malloc_token Ews t_list p * 
    data_at Ews t_list ((Vint (Int.repr a), (y, x)) : @reptype CompSpecs t_list) p *
    listrep hs x
 | nil =>
    !! (p = nullval) && emp
 end.

Fixpoint lseg (sigma: list (Z * (list byte))) (x z: val) : mpred :=
  match sigma with
  | nil => !! (x = z) && emp
  | (a, b)::hs => EX h: val, EX y:val, 
        (emp || malloc_token Ews (Tarray tschar (Zlength b + 1) noattr) y) *
        cstring Ews b y *
        malloc_token Ews t_list x * 
        data_at Ews t_list ((Vint (Int.repr a)), (y, h)) x * 
        lseg hs h z
  end.

Arguments lseg sigma x z : simpl never.

Definition list_copy_spec : ident * funspec :=
DECLARE _list_copy
  WITH sh : share, l : val, sigma : list (Z * (list byte)), gv: globals
  PRE [ tptr t_list ]
    PROP(0 <= Zlength sigma <= Int.max_unsigned;
         Forall (fun x => 0 <= (fst x) <= Int.max_unsigned /\ 0 <= Zlength (snd x) + 1 <= Int.max_unsigned) sigma)
    PARAMS(l) GLOBALS(gv)
    SEP(listrep sigma l; mem_mgr gv)
  POST [ tptr t_list ] 
    EX q: val,
    PROP()
    RETURN(q)
    SEP(listrep sigma l; listrep sigma q; mem_mgr gv).


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
  malloc_token Ews t_format x * 
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
  sepcon (malloc_token Ews t_format x)
  (sepcon 
  (data_at Ews t_format (Vint (Int.repr (Z.of_nat G.(height))),
                        (Vint (Int.repr (Z.of_nat G.(first_line_width))),
                         (Vint (Int.repr (Z.of_nat G.(middle_width))),
                          (Vint (Int.repr (Z.of_nat G.(last_line_width))), p)))) x)
  (listrep sigma p))
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


Definition empty_spec : ident * funspec :=
DECLARE _empty 
  WITH gv : globals
  PRE []
    PROP()
    PARAMS() GLOBALS(gv)
    SEP(mem_mgr gv)
  POST [ tptr t_format ]
    EX p : val,
    PROP()
    RETURN(p)
    SEP(mem_mgr gv; mformat empty p).


Fixpoint list_byte_to_string (sigma: list byte) : string :=
  match sigma with 
  | nil => EmptyString
  | (h :: hs) => String (Ascii.ascii_of_N (Z.to_N (Byte.unsigned h))) (list_byte_to_string hs)
end.


Definition line_spec : ident * funspec :=
DECLARE _line
  WITH p : val, sigma : list byte, gv : globals
  PRE [ tptr tschar ]
    PROP(0 <= Zlength sigma <= Int.max_unsigned)
    PARAMS(p) GLOBALS(gv)
    SEP(mem_mgr gv; cstring Ews sigma p)
  POST [ tptr t_format ]
    EX q : val,
    PROP()
    RETURN(q)
    SEP(mem_mgr gv; mformat (line (list_byte_to_string sigma)) q).
    

Definition sp_spec : ident * funspec :=
DECLARE _sp
  WITH n : Z, gv : globals
  PRE [ size_t ]
    PROP (0 <= n <= Int.max_unsigned)
    PARAMS(Vptrofs (Ptrofs.repr n)) GLOBALS(gv)
    SEP(mem_mgr gv)
  POST [ tptr tschar ]
    EX p : val,
    PROP()
    RETURN(p)
    SEP(cstring Ews (string_to_list_byte (sp (Z.to_nat n))) p;
         malloc_token Ews (tptr tschar) p; mem_mgr gv).

(* ================================================================= *)


Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   max_spec; strlen_spec; strcpy_spec; strcat_spec;
                   list_copy_spec; less_components_spec; is_less_than_spec; 
                   empty_spec; line_spec
 ]).

(* ================================================================= *)

Lemma body_max: semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function. 
  forward_if.
  { forward. Exists b. entailer!. }
  forward. Exists a. entailer!.
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

{ Exists 0. entailer. }
Intros i. forward. forward_if. forward. entailer!. 
repeat f_equal. cstring.
forward. entailer. Exists (i + 1). entailer!.
assert(0 <= i + 1 < Zlength (s ++ [Byte.zero])).
{ assert (i < Zlength s) by cstring.
  autorewrite with sublist.
  cstring. }
autorewrite with sublist in H6. simpl in H6.
apply H6.
Qed.

Lemma body_strcpy : semax_body Vprog Gprog f_strcpy strcpy_spec.
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
{ Exists 0. entailer. }
Intros i. forward. forward. forward. forward_if.
{ forward. entailer!. apply derives_refl'. f_equal.
  rewrite upd_Znth_app2.
  2: { list_solve. }
  assert (i - Zlength (map Vbyte (sublist 0 i s)) = 0) as AA by list_solve.
  rewrite AA. unfold Zrepeat.
  remember (Z.to_nat (n - i)). destruct n0.
  { lia. }
  simpl. 
  assert (i = Zlength s) by cstring.
  replace (Z.to_nat (n - (Zlength s + 1))) with n0 by lia.
  list_solve. }
forward. Exists (i + 1). entailer!. 
2: { rewrite upd_Znth_app2.
     all: list_solve. }
assert (0 <= i + 1 < (Zlength (s ++ [Byte.zero]))) as AA.
{ assert (i < Zlength s) as LT by cstring.
  autorewrite with sublist.
  cstring. }
autorewrite with sublist in AA. simpl in AA.
apply AA.
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
  break:
  (
    PROP ()
    LOCAL (temp _i (Vptrofs (Ptrofs.repr (Zlength b))); temp _dest dest; temp _src src)
    SEP (cstringn wsh b n dest; cstring rsh s src)).
  { Exists 0. unfold cstringn, cstring. entailer!. }
  {
    unfold cstringn, cstring.
    Intros i.
    forward. 
    { entailer!. }
    { entailer!. list_solve. }
    autorewrite with sublist norm.
    forward.
    forward_if.
    { forward. unfold cstringn, cstring. entailer!. do 2 f_equal. list_solve. }
    forward.
    Exists (i + 1).
    unfold cstringn, cstring.
    entailer!.
    list_solve.
  }
  unfold cstringn, cstring.
  forward.
  autorewrite with sublist norm in *.
  forward_loop(
    EX j : Z,
    PROP (0 <= j < Zlength s + 1)
    LOCAL (temp _i (Vptrofs (Ptrofs.repr (Zlength b)));
            temp _j (Vptrofs (Ptrofs.repr j));
            temp _dest dest; temp _src src)
    SEP ( data_at wsh (tarray tschar n) (map Vbyte (b ++ sublist 0 j s) ++ 
    Zrepeat Vundef (n - (Zlength b + j))) dest;
        cstring rsh s src)
  ).
  { Exists 0. unfold cstring, cstringn. autorewrite with sublist norm. entailer!. list_solve. }
  { 
    Intros j.
    unfold cstringn, cstring.
    autorewrite with sublist norm in *.
    Intros.
    do 3 forward.
    { entailer!. }
    forward_if.
    { forward. autorewrite with sublist norm. entailer!; list_solve. }
    forward.
    Exists (j + 1).
    entailer!.
    { list_solve. }
    unfold cstringn, cstring.
    autorewrite with sublist norm.
    entailer!.
    list_solve.
  }
Qed.

Arguments listrep sigma p : simpl never.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
  intros.

  revert p; induction sigma; intros p.
  { unfold listrep. entailer!. split; auto. }
  unfold listrep; fold listrep. destruct a. entailer. entailer!. split; intro.
  2: now inversion H4.
  subst p. eapply field_compatible_nullval; eauto.
Qed.
#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
intros.
unfold listrep. destruct sigma; simpl.
{ entailer!. }
destruct p0. Intros x y. auto with valid_pointer.
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
      all: lia.
    } {
      remember (Int.ltu (Int.repr Y) (Int.repr X)).
      destruct b.
      - destruct (Z.leb_spec0 X Y); lia.
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
    destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)); auto.
  - destruct (Z.leb_spec0 (Z.of_nat x) (Z.of_nat y)); auto.
    apply Nat2Z.inj_le in l. lia.
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
  do 3 forward.
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

Lemma is_less_than_fact1 x y :
    (x <> y)%nat <-> (x =? y)%nat = false.
Proof.
  remember (Nat.eqb_spec x y).
  clear Heqr.
  split.
  - intros. destruct r. contradiction. auto.
  - intros. destruct r. lia. auto.
Qed.

Lemma is_less_than_fact2 x y
    (XBOUND : 0 <= (Z.of_nat x) <= Int.max_unsigned)
    (YBOUND : 0 <= (Z.of_nat y) <= Int.max_unsigned) :
    (x =? y)%nat = Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y)).
Proof.
  destruct (Nat.eqb_spec x y).
  { subst. rewrite Int.eq_true. auto. }
  remember(Int.eq (Int.repr (Z.of_nat x)) (Int.repr (Z.of_nat y))).
  destruct b.
  2: lia.
  symmetry in Heqb. apply Int.same_if_eq in Heqb. apply repr_inj_unsigned in Heqb; auto. lia.
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
      + rewrite H19. simpl. apply is_less_than_fact2; auto. simpl. 
        unfold Int.max_unsigned. simpl. lia.
    - unfold concrete_mformat. entailer!.
  } {
    forward.
    Exists false.
    entailer!.
    - assert (height G = 1%nat). lia. rewrite H18. simpl. auto.
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

Lemma body_empty: semax_body Vprog Gprog f_empty empty_spec.
Proof.
  start_function.
  forward_call(t_format, gv).
  Intros empty_pointer.
  destruct (eq_dec empty_pointer nullval). {
    forward_if(empty_pointer <> nullval).
    - forward_call. entailer!.
    - forward. entailer!.
    - now Intros.
  }

  forward_if(empty_pointer <> nullval). {
    forward_call.
    entailer!.
  } {
    forward.
    entailer!.
  }

  Intros.
  do 6 forward.

  Exists empty_pointer.
  entailer!.
  unfold mformat.
  Exists ([] : (list (Z * list byte))) (Vlong (Int64.repr 0)).
  entailer!.
  - unfold empty. simpl. unfold Int.max_unsigned. simpl. lia.
  - unfold listrep. entailer!.
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
    assert ((N_of_ascii (ascii_of_N (Z.to_N (Byte.unsigned a)))) = Z.to_N (Byte.unsigned a)). {
      apply N_ascii_embedding.
      auto.
    }
    rewrite H1.
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
  destruct (eq_dec format_pointer nullval). {
    forward_if(format_pointer <> nullval).
    - forward_call. entailer!.
    - forward. entailer!.
    - Intros. contradiction.
  }

  forward_if(format_pointer <> nullval). {
    forward_call. entailer!.
  } {
    forward. entailer!.
  }
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
  destruct (eq_dec to_text_pointer nullval). {
    forward.
    forward.
    forward_if(to_text_pointer <> nullval).
    - forward_call. entailer!.
    - forward. entailer!.
    - Intros. contradiction.
  }

  Intros.
  forward.
  forward.
  forward_if(to_text_pointer <> nullval). {
    forward_call. entailer!.
  } {
    forward. entailer.
  }

  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  Exists format_pointer.
  unfold mformat.
  unfold cstring.
  Exists ([(0, sigma)]) to_text_pointer.
  entailer!.
  - unfold line. simpl. split.
    + repeat rewrite list_byte_to_string_length. list_solve.
    + unfold to_text_eq. simpl. split.
      * replace (sigma ++ []) with sigma by list_solve.
        rewrite empty_string_app.
        apply list_byte_to_list_byte_eq.
      * unfold Int.max_unsigned.
        simpl. lia.
  - unfold listrep.
    Exists (Vlong (Int64.repr 0)) p.
    unfold cstring.
    entailer!.
    unfold line. simpl.
    repeat rewrite list_byte_to_string_length.
    entailer!.
    apply orp_right1.
    entailer.
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

Lemma singleton_listrep: forall (a : Z) (b : list byte) (h : val) (x: val),
  cstring Ews b h *
  malloc_token Ews t_list x *
  data_at Ews t_list ((Vint (Int.repr a)), (h, nullval)) x
   |-- listrep [(a, b)] x.
Proof.
  intros.
  unfold listrep.
  Exists nullval h.
  entailer!.
  apply orp_right1.
  entailer.
Qed.

Lemma singleton_lseg: forall (a : Z) (b : list byte) (h : val) (x y: val),
  cstring Ews b h *
  malloc_token Ews t_list x *
  data_at Ews t_list ((Vint (Int.repr a)), (h, y)) x
   |-- lseg [(a, b)] x y.
Proof.
  intros.
  unfold lseg. 
  Exists y h.
  entailer!.
  apply orp_right1.
  entailer.
Qed.

Lemma lseg_list: forall (s1 s2: list (Z * list byte)) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  induction s1.
  - intros. simpl. unfold lseg. entailer!.
  - intros. simpl. unfold lseg; fold lseg. destruct a.
    Intros h y0.
    unfold listrep; fold listrep. Exists h y0.
    entailer!. apply IHs1.
Qed.

Lemma lseg_lseg: forall (s1 s2: list (Z * list byte)) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros s1. induction s1.
  - intros. unfold lseg; fold lseg. simpl. entailer!.
  - intros. unfold lseg; fold lseg. destruct a. Intros h y0. simpl.
    unfold lseg; fold lseg.
    Exists h y0.
    assert (
      (emp || malloc_token Ews (Tarray tschar (Zlength l + 1) noattr) y0)
        * cstring Ews l y0
        * malloc_token Ews t_list x
        * data_at Ews t_list (Vint (Int.repr z0), (y0, h)) x
        * lseg s1 h y
        * lseg s2 y z
        |-- 
      (emp || malloc_token Ews (Tarray tschar (Zlength l + 1) noattr) y0)
        * cstring Ews l y0
        * malloc_token Ews t_list x
        * data_at Ews t_list (Vint (Int.repr z0), (y0, h)) x
        * (lseg s1 h y
        * lseg s2 y z)
    ) as H by entailer!.
    eapply (derives_trans _ _ _); eauto.
    apply sepcon_derives; entailer.
Qed.

Lemma body_list_copy: semax_body Vprog Gprog f_list_copy list_copy_spec.
Proof.
  start_function.
  forward_if(l <> nullval). {
    forward. Exists nullval. entailer!.
    destruct H2. assert (nullval = nullval) as Trivial by auto.
    apply H1 in Trivial as sigma_fact.
    rewrite sigma_fact.
    unfold listrep.
    entailer!.
  }
  { forward. entailer!. }

  forward_call(t_list, gv).
  Intros new_pointer.
  destruct (eq_dec new_pointer nullval). {
    forward_if(new_pointer <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. } 
    { forward. contradiction. }
  }

  forward_if(new_pointer <> nullval).
  { forward_call. entailer!. }
  { forward. entailer!. }

  Intros. do 2 forward.
  
  forward_loop (
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
        mem_mgr gv)
  ) break: (
    PROP()
    LOCAL(temp _new new_pointer; gvars gv)
    SEP(listrep sigma new_pointer; listrep sigma l; mem_mgr gv)
  ).
  3: { forward. Exists new_pointer. entailer!. }
  {
    Exists 0 new_pointer l.
    entailer!.
    replace (sublist 0 0 sigma) with ([] : list (Z * list byte)) by list_solve.
    unfold lseg.
    replace (sublist 0 (Zlength sigma) sigma) with sigma by list_solve.
    entailer!.
  }
  
  Intros i cur l_cur.
  rename H2 into I_Boundaries.
  rename H1 into L_not_null.
  rename n into New_pointer_not_null.
  rename H3 into Cur_not_null.
  rename H4 into L_cur_not_null.
  destruct (eq_dec i (Zlength sigma)) as [ | I_is_not_zlength]. {
    subst.
    replace ((sublist (Zlength sigma) (Zlength sigma) sigma)) with ([] : list (Z * list byte)) by list_solve.
    unfold listrep; fold listrep. 
    Intros. contradiction.
  }

replace (sublist i (Zlength sigma) sigma) with 
  (Znth i sigma :: sublist (i + 1) (Zlength sigma) sigma) by list_solve.
unfold listrep; fold listrep.
remember (Znth i sigma) as ith_element.
destruct ith_element as (shift_i, line_i).

Intros l_cur_tail line_i_pointer.
do 3 forward.
forward_call(Ews, line_i, line_i_pointer).
forward_call((Tarray tschar (Zlength line_i + 1) noattr), gv). {
  assert (In (shift_i, line_i) sigma) as In_fact. 
  { rewrite Heqith_element. apply Znth_In. lia. }

  assert (Zlength line_i + 1 <= Int.max_unsigned) as Zlength_fact. {
    remember (fun x : Z * list byte =>
    0 <= fst x <= Int.max_unsigned /\
    0 <= Zlength (snd x) + 1 <= Int.max_unsigned) as List_condition.
    assert (List_condition (shift_i, line_i)) as Ith_condition. 
    { apply (computable_theorems.Forall_forall1 _ sigma); auto. }
    rewrite HeqList_condition in Ith_condition.
    destruct Ith_condition as [shift_condition].
    simpl in H1. lia.
  }

  unfold sizeof. unfold Ctypes.sizeof.
  unfold Int.max_unsigned in Zlength_fact. simpl in Zlength_fact.
  unfold Ptrofs.max_unsigned. simpl.
  lia.
}

Intros cur_line_i_pointer.
destruct (eq_dec cur_line_i_pointer nullval). {
  do 2 forward.
  forward_if(cur_line_i_pointer <> nullval).
  { forward_call. entailer!. }
  { forward. entailer!. }
  { forward. contradiction. }
}

Intros. do 2 forward.
forward_if(cur_line_i_pointer <> nullval).
{ forward_call. entailer!. }
{ forward. entailer!. }

do 2 forward.
forward_call(Ews, Ews, cur_line_i_pointer, Zlength line_i + 1, line_i_pointer, line_i).
do 2 forward.

forward_if(l_cur_tail <> nullval). {
  do 2 forward.
  entailer!.
  rewrite <- cstringn_equiv.
  assert (i + 1 = Zlength sigma) as AA. {
    assert (i + 1 < Zlength sigma \/ i + 1 = Zlength sigma) as BB. lia.
    destruct BB. {
      replace (sublist (i + 1) (Zlength sigma) sigma) 
        with (Znth (i + 1) sigma :: (sublist (i + 2) (Zlength sigma) sigma)) in H12 by list_solve.
        destruct H12.
      assert( Znth (i + 1) sigma :: sublist (i + 2) (Zlength sigma) sigma = []) as CC by auto.
      inversion CC.
    }
    auto.
  }
  rewrite AA.
  replace (sublist (Zlength sigma) (Zlength sigma) sigma) with ([] : list (Z * list byte)) by list_solve.
  unfold listrep; fold listrep.
  
  entailer!.

  assert (
    cstring Ews line_i cur_line_i_pointer 
      * cstring Ews line_i line_i_pointer
      * malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
      * malloc_token Ews t_list cur
      * data_at Ews t_list (Vint (Int.repr shift_i), (cur_line_i_pointer, Vlong (Int64.repr 0))) cur
      * lseg (sublist 0 i sigma) new_pointer cur
      * lseg (sublist 0 i sigma) l l_cur
      * (emp || malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer)
      * malloc_token Ews t_list l_cur
      * data_at Ews t_list (Vint (Int.repr shift_i), (line_i_pointer, nullval)) l_cur
    |-- 
    (lseg (sublist 0 i sigma) new_pointer cur *
    (
      malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
      * cstring Ews line_i cur_line_i_pointer 
      * malloc_token Ews t_list cur
      * data_at Ews t_list (Vint (Int.repr shift_i), (cur_line_i_pointer, Vlong (Int64.repr 0))) cur
    )) * (
      lseg (sublist 0 i sigma) l l_cur *
      (
      (emp || malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer)
      * cstring Ews line_i line_i_pointer
      * malloc_token Ews t_list l_cur
      * data_at Ews t_list (Vint (Int.repr shift_i), (line_i_pointer, nullval)) l_cur
      )
    )
  ) as Trans_step1. 
  { entailer!. }

  eapply (derives_trans _ _ _); eauto. 
  apply sepcon_derives. 
  {
    assert (sigma = sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) as FF by list_solve.
    rewrite FF.
    assert (
      lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) new_pointer cur
       * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
       * cstring Ews line_i cur_line_i_pointer
       * malloc_token Ews t_list cur
       * data_at Ews t_list (Vint (Int.repr shift_i), (cur_line_i_pointer, Vlong (Int64.repr 0))) cur)
       |-- 
      lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) new_pointer cur *
      listrep [(shift_i, line_i)] cur
    ) as Trans_step2. {
      unfold listrep; fold listrep.
      Exists nullval cur_line_i_pointer.
      entailer!. apply orp_right2. entailer.
    }

    eapply (derives_trans _ _ _); eauto.
    rewrite Heqith_element.
    replace [Znth i sigma] with (sublist i (Zlength sigma) sigma) by list_solve.
    replace (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) with sigma at 1 by list_solve.
    apply lseg_list.
  }
  {
    assert (sigma = sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) as FF by list_solve.
    rewrite FF.
    assert (
      lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) l l_cur
        * ((emp || malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer)
          * cstring Ews line_i line_i_pointer
          * malloc_token Ews t_list l_cur
          * data_at Ews t_list (Vint (Int.repr shift_i), (line_i_pointer, nullval)) l_cur)
      |-- 
      lseg (sublist 0 i (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma)) l l_cur *
      listrep [(shift_i, line_i)] l_cur
    ) as Trans_step2. {
      unfold listrep; fold listrep.
      Exists nullval line_i_pointer.
      entailer!.
    }

    eapply (derives_trans _ _ _); eauto.
    rewrite Heqith_element.
    replace [Znth i sigma] with (sublist i (Zlength sigma) sigma) by list_solve.
    replace (sublist 0 i sigma ++ sublist i (Zlength sigma) sigma) with sigma at 1 by list_solve.
    apply lseg_list.
  }
  }
  { forward. entailer!. }
  Intros.
  forward_call(t_list, gv).
  Intros cur_tail.
  do 2 forward.
  destruct (eq_dec cur_tail nullval). {
    forward_if(cur_tail <> nullval).
    { forward_call. entailer!. }
    { forward. entailer!. }
    { forward. contradiction. }
  }
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
    * data_at Ews t_list (Vint (Int.repr shift_i), (cur_line_i_pointer, cur_tail)) cur
    * lseg (sublist 0 i sigma) new_pointer cur
    * lseg (sublist 0 i sigma) l l_cur
    * (emp || malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer)
    * malloc_token Ews t_list l_cur
    * data_at Ews t_list (Vint (Int.repr shift_i), (line_i_pointer, l_cur_tail)) l_cur
    |--
    (lseg (sublist 0 i sigma) new_pointer cur
    * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
    * cstring Ews line_i cur_line_i_pointer
    * malloc_token Ews t_list cur
    * data_at Ews t_list (Vint (Int.repr shift_i), (cur_line_i_pointer, cur_tail)) cur))
    * (lseg (sublist 0 i sigma) l l_cur
    * ((emp || malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer)
    * cstring Ews line_i line_i_pointer
    * malloc_token Ews t_list l_cur
    * data_at Ews t_list (Vint (Int.repr shift_i), (line_i_pointer, l_cur_tail)) l_cur))
  ) as AA by entailer!.
  
  eapply (derives_trans _ _ _); eauto.
  apply sepcon_derives. {
    clear AA.
    assert (
      lseg (sublist 0 i sigma) new_pointer cur
       * (malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) cur_line_i_pointer
       * cstring Ews line_i cur_line_i_pointer
       * malloc_token Ews t_list cur
       * data_at Ews t_list (Vint (Int.repr shift_i), (cur_line_i_pointer, cur_tail)) cur)
      |-- 
      lseg (sublist 0 i sigma) new_pointer cur * 
      lseg (sublist i (i + 1) sigma) cur cur_tail
    ). {
      apply sepcon_derives. entailer.
      replace (sublist i (i + 1) sigma) with [Znth i sigma] by list_solve.
      unfold lseg.
      rewrite <- Heqith_element.
      Exists cur_tail cur_line_i_pointer.
      entailer!.
      apply orp_right2. entailer.
    }
    eapply (derives_trans _ _ _); eauto.
    replace (sublist 0 (i + 1) sigma) with (sublist 0 i sigma ++ sublist i (i + 1) sigma) by list_solve.
    apply lseg_lseg.
  }
  {
    clear AA.
    assert (
      lseg (sublist 0 i sigma) l l_cur
      * ((emp || malloc_token Ews (Tarray tschar (Zlength line_i + 1) noattr) line_i_pointer)
      * cstring Ews line_i line_i_pointer
      * malloc_token Ews t_list l_cur
      * data_at Ews t_list (Vint (Int.repr shift_i), (line_i_pointer, l_cur_tail)) l_cur)
      |-- 
      lseg (sublist 0 i sigma) l l_cur * 
      lseg (sublist i (i + 1) sigma) l_cur l_cur_tail
    ). {
      apply sepcon_derives. entailer.
      replace (sublist i (i + 1) sigma) with [Znth i sigma] by list_solve.
      unfold lseg.
      rewrite <- Heqith_element.
      Exists l_cur_tail line_i_pointer.
      entailer!.
    }
    eapply (derives_trans _ _ _); eauto.
    replace (sublist 0 (i + 1) sigma) with (sublist 0 i sigma ++ sublist i (i + 1) sigma) by list_solve.
    apply lseg_lseg.
  }
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
    LOCAL(temp _i (Vint (Int.repr i)); temp _result result_pointer; temp _n (Vptrofs (Ptrofs.repr n)))
    SEP(data_at Ews (Tarray tschar (n + 1) noattr) (map Vbyte (Zrepeat (Byte.repr 32) i) ++ Zrepeat Vundef (n + 1 - i)) result_pointer;
        malloc_token Ews (Tarray tschar (n + 1) noattr) result_pointer;
        mem_mgr gv)
  ) break: (
    PROP()
    LOCAL(temp _result result_pointer)
    SEP(cstring Ews (string_to_list_byte (sp (Z.to_nat n))) result_pointer;
        malloc_token Ews (Tarray tschar (n + 1) noattr) result_pointer;
        mem_mgr gv)
  ).
  { forward. Exists 0. entailer!. autorewrite with sublist norm. unfold data_at_.
    unfold data_at. unfold field_at_. entailer!. }
  { 
    Intros i. 
    forward_if.
    { forward. } 
  }
  