Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer_files.compiled_format.
Require Import printer_files.verified_printer.Format.
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

(* ================================================================= *)


Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   max_spec; strlen_spec; strcpy_spec; list_copy_spec
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
  - Exists 1 vret x. entailer.
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
    Intros vret1.
    remember (sublist 0 i t) as f.
    
    destruct f. {
      destruct t. 
      - replace (sublist (i - 1) i []) with ([] : list (Z * list byte)) by list_solve.
        unfold listrep; fold listrep.
        Intros. 
        contradiction.
      - destruct (eq_dec i 0).
        + subst. replace (sublist (0 - 1) 0 (p0 :: t)) with ([] : list (Z * list byte)) by list_solve.
          unfold listrep; fold listrep.
          Intros.
          contradiction.
        + unfold sublist in Heqf.
          unfold skipn in Heqf. simpl in Heqf.
          Search firstn.
          replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) in Heqf by list_solve.
          rewrite firstn_cons in Heqf.
          inversion Heqf.
    }

    destruct (eq_dec vret1 nullval). {
      forward.
      forward.
      forward_if(vret1 <> nullval). 
      - forward_call. entailer.
      - forward. entailer.
      - forward. contradiction.
    }
    Intros.
    forward.
    forward.
    forward_if(vret1 <> nullval). 
    { forward_call. entailer. }
    { forward. entailer. }
    forward.
    unfold lseg; fold lseg.
    Intros h y1.
    remember (sublist i (Zlength s + 1) t) as x_list.
    destruct x_list. {
      unfold listrep; fold listrep.
      Intros.
      contradiction.
    }
    unfold listrep; fold listrep.
    destruct p0.
    Intros x1 y2.
    forward.
    forward.
    forward.
    forward_call(Ews, l1, y2).
    forward_call((Tarray (Tint I8 Signed noattr) (Zlength l1 + 1) noattr), gv). {
      unfold sizeof.
      unfold Ctypes.sizeof.
      assert (In (z1, l1) t). 
      assert (skipn (Z.to_nat i) t = sublist i (Zlength s + 1) t). 
      replace (Zlength s + 1) with (Zlength t) by list_solve.
      apply list_copy_fact1. lia.
      rewrite <- H3 in Heqx_list.
      assert (In (z1, l1) (skipn (Z.to_nat i) t)). 
      rewrite <- Heqx_list. simpl. auto.
      apply initialize.In_skipn in H4. auto.
      split; try lia.
      remember (computable_theorems.Forall_forall1 _ _ H0 (z1, l1) H3).
      simpl in a. list_solve.
    }
    
    Intros vret2.
    destruct (eq_dec vret2 nullval). {
      forward.
      forward.
      forward_if(vret2 <> nullval).
      - forward_call. entailer.
      - forward. entailer.
      - forward. contradiction.
    }
    Intros.
    forward.
    forward.
    forward_if (vret2 <> nullval).
    { forward_call. entailer. }
    { forward. entailer. }
    forward. forward.

    forward_call(Ews, Ews, vret2, (Zlength l1 + 1), y2, l1).
    forward.
    Exists ((i + 1), vret1, x1 ).
    simpl.
    entailer.
    unfold cstring.
    unfold cstringn.
    entailer!; try list_solve.
    assert (x_list = sublist (i + 1) (Zlength s + 1) ((z, l) :: s)). admit.
    rewrite <- H33.
    autorewrite with sublist.
    assert ((sublist 0 (i + 1) ((z, l) :: s)) = ((z, l) :: (sublist 0 i ( s)))). admit.
    rewrite H34.
    unfold listrep; fold listrep.
    Exists 
    unfold lseg; fold lseg.
    
    
    
    
    
Admitted.
      
  