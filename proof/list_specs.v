Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import printer.verified_printer.FormatTrivial.
Require Import Coq.Strings.Ascii.
Require Import format_specs.

Definition t_flist := Tstruct _format_list noattr.

Fixpoint listrepf (sigma: list t) (p: val) : mpred :=
 match sigma with
 | G::hs =>
    EX x:val, EX y: val,
    mformat G y *
    malloc_token Ews t_flist p * 
    data_at Ews t_flist ((y, x) : @reptype CompSpecs t_flist) p *
    listrepf hs x
 | nil =>
    !! (<< LIST_NULL_PTR : p = nullval >> ) && emp
 end.

Arguments listrepf sigma p : simpl never.

Lemma listrepf_local_facts sigma p :
   listrepf sigma p |--
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

Lemma listrepf_valid_pointer sigma p :
   listrepf sigma p |-- valid_pointer p.
Proof.
  intros.
  unfold listrepf. destruct sigma; simpl; unnw.
  { entailer!. }
  Intros x y. auto with valid_pointer.
Qed.
#[export] Hint Resolve listrepf_valid_pointer : valid_pointer.

Fixpoint lsegf (sigma: list t) (x z: val) : mpred :=
  match sigma with
  | nil => !! (<< LSEG_PTR_FACT : x = z >>) && emp
  | G::hs => EX h: val, EX y:val, 
      mformat G y *
      malloc_token Ews t_flist x * 
      data_at Ews t_flist ((y, h) : @reptype CompSpecs t_flist) x *
      lsegf hs h z
  end.

Arguments lsegf sigma x z : simpl never.

Definition good_format (G : t) (w h : Z) : Prop :=
   (total_width G <= Z.to_nat w)%nat /\ (G.(height) <= Z.to_nat h)%nat.

Definition good_format_list (sigma : list t) (w h : Z) : Prop :=
  Forall (fun G => good_format G w h) sigma.

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
   WITH fs : list t, p : val, gv : globals
   PRE [ tptr t_flist ]
      PROP() PARAMS(p) GLOBALS(gv)
      SEP (listrepf fs p; mem_mgr gv)
   POST [ tvoid ]
      PROP() RETURN() SEP(mem_mgr gv).

Definition beside_doc_spec : ident * funspec :=
DECLARE _beside_doc
   WITH fs1 : list t, fs2 : list t, p1 : val, p2 : val, w : Z, h : Z, gv : globals
   PRE [ tuint, tuint, tptr t_flist, tptr t_flist ]
      PROP (good_format_list fs1 w h; good_format_list fs2 w h;
            0 <= 4 * w <= Int.max_unsigned;
            0 <= 4 * h <= Int.max_unsigned)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p1; p2) GLOBALS(gv)
      SEP (listrepf fs1 p1; listrepf fs2 p2; mem_mgr gv)
   POST [ tptr t_flist ]
      EX p: val, EX sigma: list t,
      PROP (good_format_list sigma w h;
            sigma = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (besideDoc (Z.to_nat w) fs1 fs2))
      RETURN(p)
      SEP (listrepf sigma p; mem_mgr gv).

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
                   llw_add_fill_spec; add_fill_spec; beside_doc_spec; clear_format_list_spec; clear_to_text_spec
 ]).