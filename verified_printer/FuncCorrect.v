From hahn Require Import Hahn.
Require Import Format.

Require Import String.
Require Import ZArith Int.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.ssr.ssrbool.
Require Import Lia.

Ltac andb_split :=
  repeat match goal with
         | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
         end.

Definition is_less_than'  (G:t) (G':t): bool :=
  match G.(height) with
  | 2 => (G.(height) <=? G'.(height)) &&
         (G.(first_line_width) <=? G'.(first_line_width)) &&
         (G.(last_line_width) <=? G'.(last_line_width))
  | _ => is_less_than G G'
  end.

Definition format_correct1 a := height a = 1 ->
                                first_line_width a = middle_width a /\
                                middle_width a = last_line_width a.

Definition format_correct2 a := height a > 0.

Definition format_correct3 a := height a = 2 -> first_line_width a = middle_width a.

Definition format_correct a := << F1: format_correct1 a >> /\
                               << F2: format_correct2 a >> /\
                               << F3: format_correct3 a >>.

Definition quad_correct a b c d := << Q1: format_correct a >> /\
                                   << Q2: format_correct b >> /\
                                   << Q3: format_correct c >> /\
                                   << Q4: format_correct d >>.

Definition triple_correct a b c := << Q1: format_correct a >> /\
                                   << Q2: format_correct b >> /\
                                   << Q3: format_correct c >>.

Definition list_correct lst := forall a, In a lst -> format_correct a.

Lemma list_correct_add_b lst a :
      list_correct (a::lst) <-> list_correct lst /\ format_correct a.
Proof.
  unfold list_correct in *.
  split.
  { ins.
    split.
    { ins.
      apply H; auto. }
    apply H.
    simpls.
    auto. }
  ins.
  desf.
  apply H; auto.
Qed.

Lemma list_correct_incl lst lst'
      (H: incl lst lst')
      (R: list_correct lst') : list_correct lst.
Proof.
  induction lst; simpls.
  apply list_correct_add_b.
  assert (In a lst' /\ incl lst lst').
  { unfold incl in *.
    split.
    { apply H.
      apply in_eq. }
    ins.
    apply H; auto. }
  desf.
  split; auto.
Qed.

Lemma list_correct_add_e lst a
      (H: list_correct (lst ++ a :: nil)) :
  list_correct lst /\ format_correct a.
Proof.
  unfold list_correct in *.
  split.
  { ins.
    apply H.
    apply in_app_l; auto. }
  apply H.
  apply in_app_r.
  simpls.
  auto.
Qed.

Hint Unfold
  triple_correct
  format_correct
  format_correct1
  format_correct2
  format_correct3
  is_less_than'
  is_less_than
  less_components
  : unfoldCorrectDb.

Ltac zgz :=
  match goal with
  | H : 0 > 0 |- _ => inv H 
  end.
  (* all: repeat match goal with *)
  (* | H : (1 = 2 -> _) |- _ => clear H *)
  (* | H : 1 > 0 |- _ => clear H *)
  (* | H : (1 = 1 -> ?X) |- _ => specialize (H eq_refl); desf *)
  (* end. *)

Ltac leb_simpl :=
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply leb_complete in H
  end.

Ltac zauto := auto; try by zgz.

Lemma is_less_than'_trans a b c
      (H  : triple_correct a b c)
      (AB : is_less_than' a b = true)
      (BC : is_less_than' b c = true) :
    is_less_than' a c = true.
Proof.
  repeat autounfold with unfoldCorrectDb in *.
  desf.
  all: andb_split.
  all: leb_simpl.
  all: zauto.
  all: repeat (apply andb_true_iff; split).
  all: apply Nat.leb_le; auto.
  all: etransitivity; eauto.
Qed.

Definition save_correct (f: t -> t -> t) :=
  forall a b (FCA : format_correct a) (FCB : format_correct b),
    format_correct (f a b).

Definition save_width (f: t -> t -> t) :=
  forall a b w (FCA : format_correct a)
               (FCB : format_correct b)
               (TWF : total_width (f a b) <= w),
    total_width a <= w /\ total_width b <= w.

Definition save_less (f: t -> t -> t) :=
  forall a b c d
         (QC   : quad_correct a b c d)
         (LTAB : is_less_than' a b)
         (LTCD : is_less_than' c d),
    is_less_than' (f a c) (f b d).

Definition fun_correct (f: t -> t -> t) :=
  << SVC : save_correct f >> /\
  << SWH : save_width   f >> /\
  << SL  : save_less    f >>.

Hint Unfold
     format_correct
     format_correct1
     format_correct2
     format_correct3
  : unfoldCorrectDb.

Hint Unfold
     indent'
     add_beside
     add_fill
     add_above
  : unfoldAddDb.

Ltac add_solver := 
  repeat autounfold with unfoldCorrectDb in *;
  desf; splits; ins;
  repeat autounfold with unfoldAddDb in *;
  desf; ins; zauto; lia.

Lemma beside_format a b
      (FCA : format_correct a)
      (FCB : format_correct b) :
  format_correct (add_beside a b). 
Proof. add_solver. Qed.

Lemma fill_format a b n
      (H1: format_correct a)
      (H2: format_correct b) : format_correct (add_fill a b n).
Proof. add_solver. Qed.

Lemma above_format a b
      (H1: format_correct a)
      (H2: format_correct b) : format_correct (add_above a b).
Proof. add_solver. Qed.

Lemma indent_format a n (H1: format_correct a) :
  format_correct (indent' n a).
Proof. add_solver. Qed.

(* TODO: move to Format module. *)
Lemma format_split_length_non_zero s :
  length (Format.split s) > 0.
Proof.
  induction s; ins.
  desf; ins; lia.
Qed.

Lemma of_string_correct s : format_correct (of_string s).
Proof.
  ins. unfold of_string.
  assert (length (map line (Format.split s)) > 0) as NN.
  { rewrite length_map. apply format_split_length_non_zero. }
  remember (Format.split s) as ss eqn:HH. clear HH.

  assert (forall a (IN : In a (map line ss)), format_correct a) as AA.
  { clear NN.
    ins. induction ss; simpls.
    desf.
    { repeat autounfold with unfoldCorrectDb in *.
      unfold line. splits; auto. }
    apply IHss; auto. }

  generalize dependent NN.
  generalize dependent AA.
  generalize (map line ss).
  ins.
  destruct l; simpls.
  assert (format_correct (add_above empty t)).
  { eapply AA.
    unfold add_above.
    simpls.
    eauto. }
  generalize dependent t.
  clear NN.
  induction l; ins.
  assert (add_above (add_above empty t) a = add_above empty (add_above t a)) as BB by simpls.
  rewrite BB.
  apply IHl.
  { ins.
    desf.
    { apply above_format; auto. }
    apply AA; auto. }
  unfold add_above at 1.
  simpls.
  apply above_format; auto.
Qed.

Ltac line_indent_solver :=
  match goal with
  | |- (_ = ?X) =>
    destruct X eqn:E1;
      [apply leb_complete in E1; apply Nat.leb_le; unfold indent'; desf; ins; lia|];
      apply leb_iff_conv; apply leb_iff_conv in E1; unfold indent';
        desf; ins; lia
  end.

Lemma middle_line_indent sh a b:
  (middle_width (indent' sh a) <=? middle_width (indent' sh b)) =
  (middle_width a <=? middle_width b).
Proof. line_indent_solver. Qed.

Lemma first_line_indent sh a b:
  (first_line_width (indent' sh a) <=? first_line_width (indent' sh b)) =
  (first_line_width a <=? first_line_width b).
Proof. line_indent_solver. Qed.

Lemma last_line_indent sh a b:
  (last_line_width (indent' sh a) <=? last_line_width (indent' sh b)) =
  (last_line_width a <=? last_line_width b).
Proof. line_indent_solver. Qed.

Lemma indent'_comp_helper sh a b :
  less_components a b = less_components (indent' sh a) (indent' sh b).
Proof.
  assert (forall c, height c = height (indent' sh c)) as HH.
  { ins.
    unfold indent'.
    desf. }
  unfold less_components.
  rewrite first_line_indent.
  rewrite last_line_indent.
  rewrite middle_line_indent.
  repeat rewrite <- HH.
  auto.
Qed.  

Lemma indent_width b sh a w
      (F1 : format_correct a)
      (F2 : format_correct b)
      (LT : is_less_than a b = true)
      (TW : total_width (indent' sh b) <= w) :
  total_width (indent' sh a) <= w.
Proof.
  assert (height a > 0 /\ height b > 0) as [HA HB].
  { split.
    { apply F1. }
    apply F2. }
  unfold is_less_than in LT.
  rewrite (indent'_comp_helper sh) in LT. 
  desf; zauto.
  all: unfold less_components in LT.
  all: andb_split; leb_simpl.
  all: unfold total_width in *.
  all: desf; ins; lia.
Qed.  
    
Lemma indent_width' b sh a w
      (F1: format_correct a)
      (F2: format_correct b)
      (H1: is_less_than' a b = true)
      (H2: total_width (indent' sh b) <= w) : total_width (indent' sh a) <= w.
Proof.
  assert (height a > 0 /\ height b > 0).
  { split.
    { apply F1. }
    apply F2. }
  assert (height (indent' sh a) > 0 /\ height (indent' sh b) > 0).
  { apply (indent_format _ sh) in F1.
    apply (indent_format _ sh) in F2.
    split.
    { apply F1. }
    apply F2. }
  unfold is_less_than' in H1.
  desf.
  all: try lia.
  { apply (indent_width b); auto. }
  { andb_split.
    apply leb_complete in H6.
    apply leb_complete in H5.
    assert (first_line_width a = middle_width a).
    { apply F1; auto. }
    unfold total_width in *.
    unfold indent' in *.
    desf; ins.
    lia. }
  apply (indent_width b); auto.
Qed.

Lemma indent'_components sh a b
      (H1: format_correct a)
      (H2: format_correct b)
      (T: height a <> 1) :
  is_less_than a b = less_components (indent' sh a) (indent' sh b).
Proof.
  assert (height a > 0 /\ height b > 0).
  { split.
    { apply H1. }
    apply H2. }
  desf.
  unfold is_less_than.
  rewrite <- indent'_comp_helper.
  unfold less_components.
  desf.
  assert (height a > 0).
  { apply H1. }
  lia.
Qed.

Lemma indent'_linear sh a b
      (H1: format_correct a)
      (H2: format_correct b) :
  is_less_than a b = is_less_than (indent' sh a) (indent' sh b).
Proof.
  assert (height a > 0 /\ height b > 0).
  { split.
    { apply H1. }
    apply H2. }
  desf.
  assert (L: forall c, height (indent' sh c) = height c).
  { ins.
    unfold indent'.
    desf. }
  destruct (height a <=? 1) eqn:T.
  { assert (height a = 1).
    { apply leb_complete in T.
      lia. }
    clear T.
    unfold is_less_than.
    repeat rewrite L.
    desf.
    apply indent'_comp_helper. }
  apply Nat.leb_gt in T.
  rewrite (indent'_components sh); auto.
  2: lia.
  unfold is_less_than.
  repeat rewrite L.
  desf.
  all: try lia.
  assert (height a <=? height b = false).
  { apply Nat.leb_gt.
    lia. }
  unfold less_components.
  repeat rewrite L.
  rewrite H3.
  auto.
Qed.

Lemma indent'_linear' sh a b
      (H1: format_correct a)
      (H2: format_correct b) :
  is_less_than' a b = is_less_than' (indent' sh a) (indent' sh b).
Proof.
  assert (L: forall c, height (indent' sh c) = height c).
  { ins.
    unfold indent'.
    desf. }
  unfold is_less_than'.
  rewrite (indent'_linear sh); auto.
  rewrite L.
  rewrite first_line_indent.
  rewrite last_line_indent.
  rewrite L; auto.
Qed.

Lemma beside_correct : fun_correct add_beside.
Proof.
  unfold fun_correct.
  split.
  { unfold save_correct.
    red.
    ins.
    apply beside_format; auto. }
  split.
  red.
  { unfold save_width.
    ins.
    unfold format_correct in *.
    unfold format_correct1 in *.
    unfold format_correct2 in *.
    unfold format_correct3 in *.
    desf.
    split.
    all: unfold add_beside in *.
    all: unfold total_width in *.
    all: desf; ins.
    all: try lia. }
  unfold save_less.
  red.
  ins.
  desf.
  unfold quad_correct in *.
  desf.
  assert (triple_correct (add_beside a c) (add_beside b c) (add_beside b d)).
  { unfold triple_correct.
    split.
    { red.
      apply beside_format; auto. }
    split.
    { red.
      apply beside_format; auto. }
    red.
    apply beside_format; auto. }
  unfold format_correct in *.
  unfold format_correct1 in *.
  unfold format_correct2 in *.
  unfold format_correct3 in *.
  desf.
  apply (is_less_than'_trans _ (add_beside b c)); auto.
  { unfold is_less_than' in *.
    unfold is_less_than in *.
    unfold less_components in *.
    unfold add_beside in *.
    desf; ins.
    all: desf.
    all: try andb_split.   
    all: try apply leb_complete in LTAB.
    all: try apply leb_complete in LTAB0.
    all: try apply leb_complete in LTAB1.
    all: try apply leb_complete in LTCD.
    all: try apply leb_complete in LTCD0.
    all: try apply leb_complete in LTCD1.
    all: try lia.
    all: repeat (apply andb_true_iff; split).
    all: try apply Nat.leb_le.
    all: try lia.
    all: try auto.
    all: apply leb_complete in LTAB2.
    all: lia. }
  unfold is_less_than' in *.
  unfold is_less_than in *.
  unfold less_components in *.
  unfold add_beside in *.
  desf; ins.
  all: desf.
  all: try andb_split.
  all: try apply leb_complete in LTAB.
  all: try apply leb_complete in LTAB0.
  all: try apply leb_complete in LTAB1.
  all: try apply leb_complete in LTCD.
  all: try apply leb_complete in LTCD0.
  all: try apply leb_complete in LTCD1.
  all: repeat (apply andb_true_iff; split).
  all: try apply Nat.leb_le.
  all: try lia.
  all: try auto.                          
  all: try apply leb_complete in LTCD2.
  all: try lia.                      
Qed.

Lemma above_correct : fun_correct add_above.
Proof.
  unfold fun_correct.
  split.
  { red.
    unfold save_correct.
    ins.
    desf.
    apply above_format; auto. }
  split.
  { red.
    unfold save_width.
    ins.
    unfold format_correct in *.
    unfold format_correct1 in *.
    unfold format_correct2 in *.
    unfold format_correct3 in *.
    desf.
    split.
    all: unfold add_above in *.
    all: unfold total_width in *.
    all: desf; ins.
    all: lia. }
  red.
  unfold save_less.
  ins.
  desf.
  unfold quad_correct in QC.
  desf.
  assert (triple_correct (add_above a c) (add_above b c) (add_above b d)).
  { unfold triple_correct.
    split.
    { red.
      apply above_format; auto. }
    split.
    { red.
      apply above_format; auto. }
    red.
    apply above_format; auto. }
  unfold format_correct in *.
  unfold format_correct1 in *.
  unfold format_correct2 in *.
  unfold format_correct3 in *.
  desf.
  apply (is_less_than'_trans _ (add_above b c)); auto.
  { unfold is_less_than' in *.
    unfold is_less_than in *.
    unfold less_components in *.
    unfold add_above in *.
    desf; ins. 
    all: desf.
    all: try andb_split.   
    all: try apply leb_complete in LTAB.
    all: try apply leb_complete in LTAB0.
    all: try apply leb_complete in LTAB1.
    all: try apply leb_complete in LTCD.
    all: try apply leb_complete in LTCD0.
    all: try apply leb_complete in LTCD1.
    all: try lia.
    all: repeat (apply andb_true_iff; split).
    all: try apply Nat.leb_le.
    all: try lia.
    all: try auto.
    all: try apply leb_complete in LTAB2.
    all: lia. }
  unfold is_less_than' in *.
  unfold is_less_than in *.
  unfold less_components in *.
  unfold add_above in *.
  desf; ins.
  all: desf.
  all: try andb_split.
  all: try apply leb_complete in LTAB.
  all: try apply leb_complete in LTAB0.
  all: try apply leb_complete in LTAB1.
  all: try apply leb_complete in LTCD.
  all: try apply leb_complete in LTCD0.
  all: try apply leb_complete in LTCD1.
  all: repeat (apply andb_true_iff; split).
  all: try apply Nat.leb_le.
  all: try lia.
  all: try auto.
  all: apply leb_complete in LTCD2.
  all: lia.
Qed.

Lemma fill_correct n: fun_correct (fun fs f : t => add_fill fs f n).
Proof.
  unfold fun_correct.
  split.
  { red.
    unfold save_correct.
    ins.
    apply fill_format; auto. }
  split.
  { red.
    unfold save_width.
    ins.
    unfold format_correct in *.
    unfold format_correct1 in *.
    unfold format_correct2 in *.
    unfold format_correct3 in *.
    desf.
    split.
    all: unfold add_fill in *.
    all: unfold total_width in *.
    all: desf; ins.
    all: try lia. }
  unfold save_less.
  red.
  ins.
  unfold quad_correct in *.
  desf.
  assert (triple_correct (add_fill a c n) (add_fill b c n) (add_fill b d n)).
  { unfold triple_correct.
    split.
    { red.
      apply fill_format; auto. }
    split.
    { red.
      apply fill_format; auto. }
    red.
    apply fill_format; auto. }
  unfold format_correct in *.
  unfold format_correct1 in *.
  unfold format_correct2 in *.
  unfold format_correct3 in *.
  desf.
  apply (is_less_than'_trans _ (add_fill b c n)); auto.
  { unfold is_less_than' in *.
    unfold is_less_than in *.
    unfold less_components in *.
    unfold add_fill in *.
    desf; ins.
    all: desf.
    all: try andb_split.   
    all: try apply leb_complete in LTAB.
    all: try apply leb_complete in LTAB0.
    all: try apply leb_complete in LTAB1.
    all: try apply leb_complete in LTCD.
    all: try apply leb_complete in LTCD0.
    all: try apply leb_complete in LTCD1.
    all: try lia.
    all: repeat (apply andb_true_iff; split).
    all: try apply Nat.leb_le.
    all: try lia.
    all: try auto.
    all: apply leb_complete in LTAB2.
    all: lia. }
  unfold is_less_than' in *.
  unfold is_less_than in *.
  unfold less_components in *.
  unfold add_fill in *.
  desf; ins.
  all: desf.
  all: try andb_split.
  all: try apply leb_complete in LTAB.
  all: try apply leb_complete in LTAB0.
  all: try apply leb_complete in LTAB1.
  all: try apply leb_complete in LTCD.
  all: try apply leb_complete in LTCD0.
  all: try apply leb_complete in LTCD1.
  all: repeat (apply andb_true_iff; split).
  all: try apply Nat.leb_le.
  all: try lia.
  all: try auto.                          
  all: try apply leb_complete in LTCD2.
  all: try lia.
Qed.
