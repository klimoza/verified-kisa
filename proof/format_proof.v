Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer_files.compiled_format.
Require Import printer_files.verified_printer.Format.

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

Definition t_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list (val * val)) (p: val) : mpred :=
 match sigma with
 | (a, b)::hs =>
    EX x:val,
    !! (is_int I32 Unsigned a) &&
    data_at Tsh t_list ((a, (b, x)) : @reptype CompSpecs t_list) p *
    listrep hs x
 | nil =>
    !! (p = nullval) && emp
 end.

Definition list_copy_spec : ident * funspec :=
DECLARE _list_copy
  WITH p : val, s : list (val * val), gv: globals
  PRE [ tptr t_list ]
    PROP()
    PARAMS(p) GLOBALS(gv)
    SEP(listrep s p; mem_mgr gv)
  POST [ tptr t_list ] 
    EX q: val,
    PROP(p <> nullval -> p <> q)
    RETURN(q)
    SEP(listrep s q; listrep s p; mem_mgr gv).

Definition t_format := Tstruct _t noattr.

(* ================================================================= *)


Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   max_spec; list_copy_spec
 ]).

(* ================================================================= *)

Lemma body_max: semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function. 
  forward_if.
  - forward. Exists b. entailer!.
  - forward. Exists a. entailer!.
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
    + clear - H H2. subst p. eapply field_compatible_nullval; eauto.
    + inversion H2.
Qed.
#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 intros.
 unfold listrep. destruct sigma; simpl.
  - entailer!.
  - destruct p0. Intros y. auto with valid_pointer.
Qed.
#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

Print malloc_spec'.

Lemma body_list_copy: semax_body Vprog Gprog f_list_copy list_copy_spec.
Proof.
  start_function.

  forward_if. { 
    forward. destruct s.
      - unfold listrep. Exists nullval. entailer!.
      - unfold listrep; fold listrep. destruct p. 
        destruct H0. assert (nullval = nullval). auto.
        apply H in H1. inversion H1. 
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
  Intros x.
  repeat forward.
Admitted.
      
  