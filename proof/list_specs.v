Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import printer.verified_printer.FormatTrivial.
Require Import printer.verified_printer.Doc.
Require Import printer.verified_printer.FuncCorrect.
Require Import Coq.Strings.Ascii.
Require Import format_specs.

Definition t_flist := Tstruct _format_list noattr.
Definition t_slist := Tstruct _string_list noattr.

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
   (G.(height) <= Z.to_nat h)%nat /\
   (format_correct G).

Definition good_format_list (fs : list t) (w h : Z) : Prop :=
  Forall (fun G => good_format G w h) fs.

Fixpoint listrepf (sigma: list t) (p: val) (wd ht : Z) : mpred :=
 match sigma with
 | G::hs =>
    EX x:val, EX y: val, EX format_sigma : list (Z * list byte), EX sigma_pt : val,
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
   !! (<< LIST_PTR_FACT : is_pointer_or_null p /\ (p=nullval <-> sigma=nil)>>).
Proof.
  intros.
  revert p; induction sigma; intros p.
  { unfold listrepf; unnw.
    entailer!.
    repeat split; unnw; auto; ins. }
  unff listrepf.
  destruct a. entailer. unnw. entailer!.
  repeat split; ins; unfold good_format_list in *.
  subst; eapply field_compatible_nullval; eauto.
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
      concrete_mformat G y format_sigma sigma_pt *
      malloc_token Ews t_flist x * 
      data_at Ews t_flist ((y, h) : @reptype CompSpecs t_flist) x *
      lsegf hs h z wd ht
  end.

Arguments lsegf sigma x z wd ht : simpl never.

Lemma lsegf_null_listrepf sigma p w h:
  lsegf sigma p nullval w h |-- listrepf sigma p w h.
Proof.
  revert p.
  induction sigma.
  { unff lsegf; unff listrepf; entailer!. }
  intros p.
  unff lsegf.
  Intros h0 y format_sigma sigma_pt.
  unff listrepf.
  Exists h0 y format_sigma sigma_pt.
  entailer!.
Qed.

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

Definition above_doc_spec : ident * funspec :=
DECLARE _above_doc
   WITH fs1 : list t, fs2 : list t, p1 : val, p2 : val, w : Z, h : Z, gv : globals
   PRE [ tuint, tuint, tptr t_flist, tptr t_flist ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned;
            << GOOD_FMT1: good_format_list fs1 w h>>;
            << GOOD_FMT2: good_format_list fs2 w h>>)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p1; p2) GLOBALS(gv)
      SEP (listrepf fs1 p1 w h; listrepf fs2 p2 w h; mem_mgr gv)
   POST [ tptr t_flist ]
      EX p: val, EX sigma: list t,
      PROP (sigma = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (aboveDoc (Z.to_nat w) fs1 fs2);
            << GOOD_FMT: good_format_list sigma w h >>)
      RETURN(p)
      SEP (listrepf sigma p w h; mem_mgr gv).

Definition beside_doc_spec : ident * funspec :=
DECLARE _beside_doc
   WITH fs1 : list t, fs2 : list t, p1 : val, p2 : val, w : Z, h : Z, gv : globals
   PRE [ tuint, tuint, tptr t_flist, tptr t_flist ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned;
            << GOOD_FMT1: good_format_list fs1 w h>>;
            << GOOD_FMT2: good_format_list fs2 w h>>)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p1; p2) GLOBALS(gv)
      SEP (listrepf fs1 p1 w h; listrepf fs2 p2 w h; mem_mgr gv)
   POST [ tptr t_flist ]
      EX p: val, EX sigma: list t,
      PROP (sigma = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (besideDoc (Z.to_nat w) fs1 fs2);
            << GOOD_FMT: good_format_list sigma w h>>)
      RETURN(p)
      SEP (listrepf sigma p w h; mem_mgr gv).

Definition fill_doc_spec : ident * funspec :=
DECLARE _fill_doc
   WITH fs1 : list t, fs2 : list t, p1 : val, p2 : val, w : Z, h : Z, shift : Z, gv : globals
   PRE [ tuint, tuint, tptr t_flist, tptr t_flist, size_t ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned;
            0 <= shift <= w;
            << GOOD_FMT1: good_format_list fs1 w h>>;
            << GOOD_FMT2: good_format_list fs2 w h>>)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p1; p2; Vptrofs (Ptrofs.repr shift)) GLOBALS(gv)
      SEP (listrepf fs1 p1 w h; listrepf fs2 p2 w h; mem_mgr gv)
   POST [ tptr t_flist ]
      EX p: val, EX sigma: list t,
      PROP (sigma = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (fillDoc (Z.to_nat w) fs1 fs2 (Z.to_nat shift));
            << GOOD_FMT: good_format_list sigma w h >>)
      RETURN(p)
      SEP (listrepf sigma p w h; mem_mgr gv).

Definition get_format_list_tail_spec : ident * funspec :=
DECLARE _get_format_list_tail
   WITH fs : list t, w : Z, h : Z, p : val
   PRE [ tptr t_flist ]
      PROP(fs <> nil) PARAMS(p) SEP (listrepf fs p w h)
   POST [ tptr t_flist ]
      EX q : val,
      PROP()
      RETURN(q)
      SEP(listrepf (sublist (Zlength fs - 1) (Zlength fs) fs) q w h; 
          lsegf (sublist 0 (Zlength fs - 1) fs) p q w h).

Definition format_list_copy_spec : ident * funspec :=
DECLARE _format_list_copy
  WITH fs : list t, p : val, w : Z, h : Z, gv: globals
  PRE [ tptr t_flist ]
    PROP()
    PARAMS(p) GLOBALS(gv)
    SEP(listrepf fs p w h; mem_mgr gv)
  POST [ tptr t_flist ] 
    EX q: val,
    PROP()
    RETURN(q)
    SEP(listrepf fs p w h; listrepf fs q w h; mem_mgr gv).

Definition choice_doc_spec : ident * funspec :=
DECLARE _choice_doc
   WITH fs1 : list t, fs2 : list t, p1 : val, p2 : val, w : Z, h : Z, gv : globals
   PRE [ tptr t_flist, tptr t_flist ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned;
            << GOOD_FMT1: good_format_list fs1 w h >>;
            << GOOD_FMT2: good_format_list fs2 w h >>)
      PARAMS(p1; p2) GLOBALS(gv)
      SEP (listrepf fs1 p1 w h; listrepf fs2 p2 w h; mem_mgr gv)
   POST [ tptr t_flist ]
      EX p: val, EX sigma: list t,
      PROP (sigma = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (choiceDoc fs1 fs2);
            << GOOD_FMT: good_format_list sigma w h >>)
      RETURN(p)
      SEP (listrepf sigma p w h; mem_mgr gv).

Definition indent_spec : ident * funspec :=
DECLARE _indent
   WITH G : t, p : val, sigma : list (Z * list byte), sigma_pt : val, shift : Z, w : Z, h : Z, gv : globals
   PRE [ tptr t_format, size_t ]
      PROP (
         0 <= 8 * w <= Int.max_unsigned - 1;
         0 <= 8 * h <= Int.max_unsigned;
         0 <= shift <= w;
         << GOOD_FMT: good_format G w h >>)
      PARAMS(p; Vptrofs (Ptrofs.repr shift)) GLOBALS(gv)
      SEP (concrete_mformat G p sigma sigma_pt; mem_mgr gv)
   POST [ tptr t_format ]
      EX new_p : val, EX new_sigma : list (Z * list byte), EX new_sigma_pt : val,
      PROP ()
      RETURN (new_p)
      SEP (concrete_mformat G p sigma sigma_pt; concrete_mformat (indent' (Z.to_nat shift) G) new_p new_sigma new_sigma_pt; mem_mgr gv).

Definition indent_doc_spec : ident * funspec :=
DECLARE _indent_doc
   WITH fs : list t, p : val, w : Z, h : Z, shift : Z, gv : globals
   PRE [ tuint, tuint, tptr t_flist, size_t ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned;
            0 <= shift <= w;
            << GOOD_FMT: good_format_list fs w h >>)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p; Vptrofs (Ptrofs.repr shift)) GLOBALS(gv)
      SEP (listrepf fs p w h; mem_mgr gv)
   POST [ tptr t_flist ]
      EX p: val, EX sigma: list t,
      PROP (sigma = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (indentDoc (Z.to_nat w) (Z.to_nat shift) fs);
            << GOOD_FMT: good_format_list sigma w h >>)
      RETURN(p)
      SEP (listrepf sigma p w h; mem_mgr gv).

Definition clear_last_format_element_spec : ident * funspec :=
DECLARE _clear_last_format_element
   WITH fs : list t, p : val, w : Z, h : Z, gv : globals
   PRE [ tptr t_flist ]
      PROP (Zlength fs >= 2)
      PARAMS(p) GLOBALS(gv)
      SEP (listrepf fs p w h; mem_mgr gv)
   POST [ tptr t_flist ]
      PROP()
      RETURN(p)
      SEP(listrepf (sublist 0 (Zlength fs - 1) fs) p w h; mem_mgr gv).

Definition construct_doc_spec : ident * funspec :=
DECLARE _construct_doc
   WITH sigma : list byte, p : val, w : Z, h : Z, gv : globals
   PRE [ tuint, tuint, tptr tschar]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p) GLOBALS(gv)
      SEP (cstring Ews sigma p; mem_mgr gv)
   POST [ tptr t_flist ]
      EX q: val, EX res: list t,
      PROP (res = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (constructDoc (Z.to_nat w) (list_byte_to_string sigma));
            << GOOD_FMT: good_format_list res w h >>)
      RETURN(q)
      SEP (listrepf res q w h; cstring Ews sigma p; mem_mgr gv).

Definition t_doc := Tstruct _doc noattr.

Fixpoint mdoc (doc : Doc) (x : val) (w h : Z) : mpred :=
  match doc with
  | Text s     => 
      EX p : val,
      !! (0 <= Zlength (string_to_list_byte s) <= w) &&
      data_at Ews t_doc (Vint (Int.repr 0), (Vptrofs (Ptrofs.repr 0), (p, nullval))) x *
      cstring Ews (string_to_list_byte s) p
  | Indent n d => 
      EX p : val,
      !! (<< SHIFT_RANGE: 0 <= Z.of_nat n <= w >>) &&
      data_at Ews t_doc (Vint (Int.repr 1), (Vptrofs (Ptrofs.repr (Z.of_nat n)), (p, nullval))) x *
      mdoc d p w h
  | Beside a b => 
      EX p, EX q : val,
      data_at Ews t_doc (Vint (Int.repr 2), (Vptrofs (Ptrofs.repr 0), (p, q))) x *
      mdoc a p w h *
      mdoc b q w h
  | Above a b  => 
      EX p, EX q : val,
      data_at Ews t_doc (Vint (Int.repr 3), (Vptrofs (Ptrofs.repr 0), (p, q))) x *
      mdoc a p w h *
      mdoc b q w h
  | Choice a b =>
      EX p, EX q : val,
      data_at Ews t_doc (Vint (Int.repr 4), (Vptrofs (Ptrofs.repr 0), (p, q))) x *
      mdoc a p w h *
      mdoc b q w h
  | Fill a b n =>
      EX p, EX q : val,
      !! (<< SHIFT_RANGE: 0 <= Z.of_nat n <= w >>) &&
      data_at Ews t_doc (Vint (Int.repr 5), (Vptrofs (Ptrofs.repr (Z.of_nat n)), (p, q))) x *
      mdoc a p w h *
      mdoc b q w h
  end.

Lemma doc_local_facts d x w h :
   mdoc d x w h |-- !! (<< DOC_PTR_FACT : is_pointer_or_null x >>).
Proof.
  revert x; induction d; ins.
  { Intros p; entailer!. }
  { Intros p; entailer!. }
  { Intros p q; entailer!. }
  { Intros p q; entailer!. }
  { Intros p q; entailer!. }
  Intros p q; entailer!.
Qed.
#[export] Hint Resolve doc_local_facts : saturate_local.

Definition evaluator_trivial_spec : ident * funspec :=
DECLARE _evaluator_trivial
   WITH d : Doc, p : val, w : Z, h : Z, gv : globals
   PRE [ tuint, tuint, tptr t_doc ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned)
      PARAMS(Vint (Int.repr w); Vint (Int.repr h); p) GLOBALS(gv)
      SEP(mdoc d p w h; mem_mgr gv)
   POST [ tptr t_flist ]
      EX q: val, EX res: list t,
      PROP (res = filter (fun G => (G.(height) <=? (Z.to_nat h))%nat) (evaluatorTrivial (Z.to_nat w) d);
            << GOOD_FMT: good_format_list res w h >>)
      RETURN(q)
      SEP (mdoc d p w h; listrepf res q w h; mem_mgr gv).


Fixpoint listreps (sigma: list (list byte)) (p: val) : mpred :=
 match sigma with
 | h::hs =>
    EX x:val, EX y: val,
    !! (0 <= 4 * Zlength h + 1 <= Int.max_unsigned) &&
    malloc_token Ews (Tarray tschar (Zlength h + 1) noattr) y *
    cstring Ews h y *
    malloc_token Ews t_slist p * 
    data_at Ews t_slist ((y, x) : @reptype CompSpecs t_slist) p *
    listreps hs x
 | nil =>
    !! (<< LIST_NULL_PTR : p = nullval >> ) && emp
 end.

Arguments listreps sigma p : simpl never.

Lemma listreps_local_facts sigma p :
   listreps sigma p |--
   !! (<< LIST_PTR_FACT : is_pointer_or_null p /\ (p=nullval <-> sigma=nil) >>).
Proof.
  intros.
  revert p; induction sigma; intros p.
  { unfold listreps. unnw. entailer!. split; auto. }
  unff listreps.
  entailer. unnw. entailer!.
  split; ins.
  subst. eapply field_compatible_nullval; eauto.
Qed.
#[export] Hint Resolve listreps_local_facts : saturate_local.

Lemma listreps_valid_pointer sigma p :
   listreps sigma p |-- valid_pointer p.
Proof.
  intros.
  unfold listreps. destruct sigma; simpl; unnw.
  { entailer!. }
  Intros x y. auto with valid_pointer.
Qed.
#[export] Hint Resolve listreps_valid_pointer : valid_pointer.

Fixpoint lsegs (sigma: list (list byte)) (x z: val) : mpred :=
  match sigma with
  | nil => !! (<< LSEG_PTR_FACT : x = z >>) && emp
  | b::hs => EX h: val, EX y:val, 
        !! (0 <= 4 * Zlength b + 1 <= Int.max_unsigned) &&
        malloc_token Ews (Tarray tschar (Zlength b + 1) noattr) y *
        cstring Ews b y *
        malloc_token Ews t_slist x * 
        data_at Ews t_slist ((y, h)) x * 
        lsegs hs h z
  end.

Arguments lsegs sigma x z : simpl never.

Definition new_string_list_spec : ident * funspec :=
DECLARE _new_string_list
   WITH gv: globals
   2: PRE []
      PROP ()
      PARAMS() GLOBALS(gv)
      SEP (mem_mgr gv)
   POST [ tptr t_slist ]
      EX q: val,
      PROP ()
      RETURN(q)
      SEP (listreps [[]] q; mem_mgr gv).

Definition split_spec : ident * funspec :=
DECLARE _split
   WITH s : list byte, p : val, gv : globals
   PRE [ tptr tschar ]
      PROP (0 <= 4 * Zlength s + 1 <= Int.max_unsigned)
      PARAMS (p) GLOBALS(gv)
      SEP (cstring Ews s p; mem_mgr gv)
   POST [ tptr t_slist ]
      EX q : val,
      PROP ()
      RETURN (q)
      SEP (listreps (map (fun x => string_to_list_byte x) (split (list_byte_to_string s))) q;
           cstring Ews s p; mem_mgr gv).

Definition clear_string_list_spec : ident * funspec :=
DECLARE _clear_string_list
   WITH sl : list (list byte), p : val, gv : globals
   PRE [ tptr t_slist ]
      PROP () 
      PARAMS (p) GLOBALS(gv)
      SEP (listreps sl p; mem_mgr gv)
   POST [ tvoid ]
      PROP () 
      RETURN () 
      SEP (mem_mgr gv).

Definition fl_from_sl_spec : ident * funspec :=
DECLARE _fl_from_sl
   WITH sl : list (list byte), p : val, w : Z, h : Z, gv : globals
   PRE [ tptr t_slist, tuint, tuint ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned)
      PARAMS (p; Vint (Int.repr w); Vint (Int.repr h)) GLOBALS(gv)
      SEP (listreps sl p; mem_mgr gv)
   POST [ tptr t_flist ]
      EX q : val,
      PROP ()
      RETURN (q)
      SEP (listrepf (filter (fun x => (((total_width x) <=? Z.to_nat w)%nat && (x.(height) <=? Z.to_nat h)%nat)%bool) (map (fun x => line (list_byte_to_string x)) sl)) q w h; 
             listreps sl p; mem_mgr gv).

Definition fold_above_spec : ident * funspec :=
DECLARE _fold_above
   WITH fl : list t, p : val, w : Z, h : Z, gv : globals
   PRE [ tptr t_flist, tuint, tuint ]
      PROP (0 <= 8 * w <= Int.max_unsigned - 1;
            0 <= 8 * h <= Int.max_unsigned)
      PARAMS (p; Vint (Int.repr w); Vint (Int.repr h)) GLOBALS(gv)
      SEP (listrepf fl p w h; mem_mgr gv) 
   POST [ tptr t_format ]
      EX res : t, EX q : val,
      PROP (res = fold_left add_above fl empty)
      RETURN (q)
      SEP (
         if ((Nat.ltb (Z.to_nat h) res.(height)) || (Nat.ltb (Z.to_nat w) (total_width res)))%bool 
         then ((listrepf fl p w h) * (mem_mgr gv))
         else ((listrepf fl p w h) * (mformat res q) * (mem_mgr gv))).
      

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
                   llw_add_fill_spec; add_fill_spec; clear_format_list_spec; clear_to_text_spec;
                   max_width_check_spec; total_width_spec; get_format_list_tail_spec; format_list_copy_spec;
                   choice_doc_spec; beside_doc_spec; above_doc_spec; fill_doc_spec; indent_spec;
                   clear_last_format_element_spec; indent_doc_spec; construct_doc_spec;
                   evaluator_trivial_spec; new_string_list_spec; split_spec; clear_string_list_spec;
                   fl_from_sl_spec
 ]).