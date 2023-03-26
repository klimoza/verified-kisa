
Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import Coq.Strings.Ascii.
Require Import format_specs.
Require Import format_std_proof.
Require Import format_proof.
Require Import list_specs.
Require Import format_combinator_proof.

Lemma body_clear_to_text : semax_body Vprog Gprog f_clear_to_text clear_to_text_spec.
Proof.
  start_function.
  forward_if(p <> nullval).
  { forward; destruct l.
    { unff listrep; entailer!. }
    unnw; desf.
    assert (p :: l = []) by auto; vauto. }
  { forward; entailer!. }

  destruct l.
  { unff listrep; Intros; unnw; vauto. }

  unff listrep; Intros.
  destruct p0 as (fst_shift, fst_line).
  Intros fst_tail_ptr fst_line_ptr.

  forward.
  { entailer!; unnw; desf; entailer!. }
  forward_call(l, fst_tail_ptr, gv).
  forward. unfold cstring.
  forward_if(
    PROP()
    LOCAL(temp _t'1 fst_line_ptr; temp _t'3 fst_tail_ptr; gvars gv; temp _l p)
    SEP (mem_mgr gv; malloc_token Ews t_list p; data_at Ews t_list
      (Vptrofs (Ptrofs.repr fst_shift), (fst_line_ptr, fst_tail_ptr)) p)).
  { forward.
    forward_call(tarray tschar (Zlength fst_line + 1), fst_line_ptr, gv).
    { desf; entailer!. }
    entailer!. }
  { forward; entailer!. }
  forward_call(t_list, p, gv).
  { desf; entailer!. }
  entailer!.
Qed.

Lemma body_clear_format_list : semax_body Vprog Gprog f_clear_format_list clear_format_list_spec.
Proof.
  start_function.
  forward_if(p <> nullval).
  { forward.
    destruct fs.
    { unff listrepf; entailer!. }
    unnw; desf.
    assert (t :: fs = []) by auto; vauto. }
  { forward; entailer!. }
  
  Intros; destruct fs; unff listrepf.
  { Intros; unnw; vauto. }
  Intros fst_tail_ptr fst_format_ptr.
  forward.
  { entailer!; unnw; desf; entailer!. }

  forward_call(fs, fst_tail_ptr, gv).
  forward.
  { unfold mformat; Intros sigmaG pG.
    unfold concrete_mformat; do 2 entailer. }
  
  unfold mformat; Intros sigmaG pG; unfold concrete_mformat.
  forward_if(
    PROP()
    LOCAL(temp _t'1 fst_format_ptr; temp _t'5 fst_tail_ptr; gvars gv; temp _fs p)
    SEP (mem_mgr gv; malloc_token Ews t_flist p;
    data_at Ews t_flist (fst_format_ptr, fst_tail_ptr) p)).
  2: { forward; do 2 entailer!. }
  2: { forward_call(t_flist, p, gv).
       { desf; entailer!. }
       entailer!. }

  forward.
  forward.
  { entailer; unnw; desf; entailer!. }

  forward_call(sigmaG, pG, gv).
  forward.
  forward_call(t_format, fst_format_ptr, gv).
  { desf; entailer!. }
  entailer!.
Qed.

Lemma lsegf_listf (s1 s2: list t) (x y: val) :
  lsegf s1 x y * listrepf s2 y |-- listrepf (s1 ++ s2) x.
Proof.
  generalize dependent x.
  induction s1; ins; unfold lsegf.
  { entailer!; unnw; subst; entailer. }
  unff lsegf; destruct a.
  Intros h y0.
  unff listrepf; Exists h y0.
  entailer!; apply IHs1.
Qed.

Lemma lsegf_null_listrepf (sigma : list t) (p : val):
  lsegf sigma p nullval |-- listrepf sigma p.
Proof.
  revert p.
  induction sigma.
  { unfold lsegf; unfold listrepf; entailer!. }
  unff lsegf; destruct a.
  intros p.
  Intros h y.
  unff listrepf.
  Exists h y.
  entailer!.
Qed.

Lemma concat_map_nil (l : list t): concat (map (fun x => ([] : list t)) l) = [].
Proof.
  induction l; vauto.
Qed.

Instance t_Inhabitant : Inhabitant t := {
  default := empty;
}.


Lemma body_beside_doc : semax_body Vprog Gprog f_beside_doc beside_doc_spec.
Proof.
  start_function.
  forward_if(p1 <> nullval).
  { forward_if(
    PROP ( )
    LOCAL (gvars gv; temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h)); temp _fs1 p1; temp _fs2 p2)
    SEP (listrepf fs1 p1; mem_mgr gv)).
    { forward_call(fs2, p2, gv); entailer!. }
    { forward; entailer!. 
      unnw; desf.
      assert (fs2 = []) by auto; subst.
      unff listrepf; entailer!. }
    forward.
    unnw; desf.
    assert (fs1 = []) by auto; subst.
    Exists nullval ([] : list t); entailer!.
    unfold FormatTrivial.besideDoc.
    unfold FormatTrivial.cross_general; ins.
    rewrite concat_map_nil; list_solve. }
  { forward; entailer!. }

  forward_if(p2 <> nullval).
  { forward_call(fs1, p1, gv).
    forward.
    unnw; desf.
    assert (fs2 = []) by auto; subst.
    Exists nullval ([] : list t); entailer!. }
  { forward; entailer!. }
  forward_call(t_flist, gv).
  Intros result_ptr.
  dest_ptr result_ptr.
  do 3 forward.
  desf.
  

  remember (
      EX i : Z, EX head_ptr : val, EX result_tail_ptr : val, EX res_part : list t,
      PROP(0 <= i <= Zlength fs2;
            res_part = filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 (sublist 0 i fs2)))
      LOCAL(temp _fs2_tail head_ptr;
            temp _has_item (Val.of_bool (0 <? Zlength res_part)); temp _result result_ptr; gvars gv; 
            temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
            temp _fs1 p1; temp _fs2 p2)
      SEP (mem_mgr gv; listrepf fs1 p1; lsegf (sublist 0 i fs2) p2 head_ptr; 
          listrepf (sublist i (Zlength fs2) fs2) head_ptr; lsegf res_part result_ptr result_tail_ptr;
          malloc_token Ews t_flist result_tail_ptr; data_at_ Ews t_flist result_ptr)) as loop_invariant eqn:eqn_loop.
  remember (
      EX result_tail_ptr : val, EX res_part : list t,
      PROP(res_part = filter (fun G => (G.(height) <=? Z.to_nat h)%nat) (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))
      LOCAL(temp _has_item (Val.of_bool (0 <? Zlength res_part)); temp _result result_ptr; gvars gv; 
            temp _width (Vint (Int.repr w)); temp _height (Vint (Int.repr h));
            temp _fs1 p1; temp _fs2 p2)
      SEP (mem_mgr gv; listrepf fs1 p1; listrepf fs2 p2; lsegf res_part result_ptr result_tail_ptr;
          malloc_token Ews t_flist result_tail_ptr; data_at_ Ews t_flist result_ptr)) as break_invariant eqn:eqn_break.
  forward_loop(loop_invariant) break: (break_invariant).
  { subst.
    Exists 0 p2 result_ptr ([] : list t).
    entailer!.
    replace (sublist 0 0 fs2) with ([] : list t) by list_solve.
    assert (sublist 0 (Zlength fs2) fs2 = fs2) as K.
    { rewrite sublist_skip; vauto. }
    rewrite K.
    unff lsegf; entailer!; ins. }
  2: { subst.
      Intros result_tail_ptr res_part.
      forward_call(fs1, p1, gv).
      forward_call(fs2, p2, gv).
      forward_if (
        Zlength res_part <> 0
      ).
      { destruct (0 <? Zlength res_part) eqn:E; vauto.
        forward_call(t_flist, result_ptr, gv).
        { desf; entailer!.
          replace ((filter (fun G : t => (height G <=? Z.to_nat h)%nat)
          (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2))) with ([] : list t) by list_solve.
          unff lsegf.
          entailer!; subst; unnw; entailer!. }
        forward.
        Exists nullval ([] : list t); entailer!.
        2: { unff listrepf; entailer!. }
        split.
        { unfold good_format_list; vauto. }
        list_solve. }
      { forward; entailer!; ins.
        assert (Zlength (filter (fun G : t => (height G <=? Z.to_nat h)%nat)
           (FormatTrivial.besideDoc (Z.to_nat w) fs1 fs2)) = 0) as K by vauto.
        rewrite K in *; vauto. }
      forward.
}

Admitted.