Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import printer.verified_printer.FormatTrivial.
Require Import Coq.Strings.Ascii.
Require Import format_specs.

Definition t_flist := Tstruct _format_list noattr.

Lemma list_max_cons (x : nat) (l : list nat):
  list_max (x :: l) = max x (list_max l).
Proof.
  unfold list_max.
  unfold fold_right.
  lia.
Qed.

Lemma list_max_nil:
  list_max [] = 0%nat.
Proof.
  unfold list_max.
  unfold fold_right.
  lia.
Qed.

Definition good_format (G : t) (w h : Z) : Prop :=
   (total_width G <= Z.to_nat w)%nat /\
   (G.(height) <= Z.to_nat h)%nat.

Fixpoint listrepf (sigma: list t) (p: val) (wd ht : Z) : mpred :=
 match sigma with
 | G::hs =>
    EX x:val, EX y: val, EX format_sigma : list (Z * list byte), EX sigma_pt : val,
    !! (<< GOOD_FORMAT : good_format G wd ht >>) &&
    concrete_mformat G y format_sigma sigma_pt *
    malloc_token Ews t_flist p * 
    data_at Ews t_flist ((y, x) : @reptype CompSpecs t_flist) p *
    listrepf hs x wd ht
 | nil =>
    !! (<< LIST_NULL_PTR : p = nullval >> ) && emp
 end.

Arguments listrepf sigma p wd ht : simpl never.

Lemma listrepf_local_facts sigma p w h:
   listrepf sigma p w h |--
   !! (<< LIST_PTR_FACT : is_pointer_or_null p /\ (p=nullval <-> sigma=nil) >>).
Proof.
  intros.
  revert p; induction sigma; intros p.
  { unfold listrepf. unnw. entailer!. split; auto. }
  unff listrepf.
  destruct a. entailer. unnw. entailer!.
  split; ins.
  subst. eapply field_compatible_nullval; eauto.
Qed.
#[export] Hint Resolve listrepf_local_facts : saturate_local.

Lemma listrepf_valid_pointer sigma p w h :
   listrepf sigma p w h |-- valid_pointer p.
Proof.
  intros.
  unfold listrepf. destruct sigma; simpl; unnw.
  { entailer!. }
  Intros x y sigma0 sigma_pt. auto with valid_pointer.
Qed.
#[export] Hint Resolve listrepf_valid_pointer : valid_pointer.

Fixpoint lsegf (sigma: list t) (x z: val) (wd ht : Z) : mpred :=
  match sigma with
  | nil => !! (<< LSEG_PTR_FACT : x = z >>) && emp
  | G::hs => EX h: val, EX y:val, EX format_sigma : list (Z * list byte), EX sigma_pt : val,
      !! (<< GOOD_FORMAT : good_format G wd ht >>) &&
      concrete_mformat G y format_sigma sigma_pt *
      malloc_token Ews t_flist x * 
      data_at Ews t_flist ((y, h) : @reptype CompSpecs t_flist) x *
      lsegf hs h z wd ht
  end.

Arguments lsegf sigma x z wd ht : simpl never.

Definition total_width_spec : ident * funspec :=
DECLARE _total_width
   WITH G : t, p : val, sigma : list (Z * list byte), sigma_pt : val
   PRE [ tptr t_format ]
      PROP(format_mp G sigma)
      PARAMS(p)
      SEP (concrete_mformat G p sigma sigma_pt)
   POST [ tuint ]
      PROP() RETURN (Vint (Int.repr (Z.of_nat (total_width G))))
      SEP(concrete_mformat G p sigma sigma_pt).

Definition max_width_check_spec : ident * funspec :=
DECLARE _max_width_check
   WITH G : t, p : val, sigma : list (Z * list byte), sigma_pt : val, w : Z, h : Z
   PRE [ tptr t_format, tuint, tuint ]
      PROP(0 <= 8 * w <= Int.max_unsigned;
           0 <= 8 * h <= Int.max_unsigned;
           format_mp G sigma)
      PARAMS(p; Vint (Int.repr w); Vint (Int.repr h))
      SEP (concrete_mformat G p sigma sigma_pt)
   POST [ tbool ]
      EX a : bool,
      PROP(a = true <-> ((total_width G <= (Z.to_nat w))%nat /\
                         (G.(height) <= (Z.to_nat h))%nat))
      RETURN (Val.of_bool a)
      SEP(concrete_mformat G p sigma sigma_pt).

Definition clear_to_text_spec : ident * funspec :=
DECLARE _clear_to_text
   WITH l : list (Z * list byte), p : val, gv : globals
   PRE [ tptr t_list ]
      PROP() PARAMS(p) GLOBALS(gv)
      SEP (listrep l p; mem_mgr gv)
   POST [ tvoid ]
      PROP() RETURN() SEP(mem_mgr gv).

Definition clear_format_list_spec : ident * funspec :=
DECLARE _clear_format_list
   WITH fs : list t, p : val, w : Z, h : Z, gv : globals
   PRE [ tptr t_flist ]
      PROP() PARAMS(p) GLOBALS(gv)
      SEP (listrepf fs p w h; mem_mgr gv)
   POST [ tvoid ]
      PROP() RETURN() SEP(mem_mgr gv).

Definition beside_doc_spec : ident * funspec :=
DECLARE _beside_doc
   WITH fs1 : list t, fs2 : list t, p1 : val, p2 : val, w : Z, h : Z, gv : globals
   PRE [ tuint, tuint, tptr t_flist, tptr t_flist ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p1; p2) GLOBALS(gv)
      SEP (listrepf fs1 p1 w h; listrepf fs2 p2 w h; mem_mgr gv)
   POST [ tptr t_flist ]
      EX p: val, EX sigma: list t,
      PROP (sigma = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (besideDoc (Z.to_nat w) fs1 fs2))
      RETURN(p)
      SEP (listrepf sigma p w h; mem_mgr gv).

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   max_spec; strlen_spec; strcpy_spec; strcat_spec;
                   list_copy_spec; less_components_spec; is_less_than_spec; 
                   empty_spec; line_spec; sp_spec; 
                   get_applied_length_spec; format_copy_spec; get_list_tail_spec;
                   mdw_add_above_spec; list_concat_spec; to_text_add_above_spec;
                   new_list_spec; add_above_spec;
                   flw_add_beside_spec; shift_list_spec; add_beside_spec; line_concats_spec;
                   mdw_add_beside_spec; to_text_add_beside_spec;
                   mdw_add_fill_spec; flw_add_fill_spec; to_text_add_fill_spec;
                   llw_add_fill_spec; add_fill_spec; beside_doc_spec; clear_format_list_spec; clear_to_text_spec;
                   max_width_check_spec; total_width_spec
 ]).