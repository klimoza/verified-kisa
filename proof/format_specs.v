Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
Require Import printer.verified_printer.FuncCorrect.
Require Import Coq.Strings.Ascii.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_list := Tstruct _list noattr.
Definition t_format := Tstruct _t noattr.

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
  POST [ tuint ] 
    EX q : Z,
    PROP (q = Z.max a b; 0 <= q <= a \/ 0 <= q <= b) 
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

Fixpoint listrep (sigma: list (Z * (list byte))) (p: val) : mpred :=
 match sigma with
 | (a, b)::hs =>
    EX x:val, EX y: val,
    malloc_token Ews (Tarray tschar (Zlength b + 1) noattr) y *
    cstring Ews b y *
    malloc_token Ews t_list p * 
    data_at Ews t_list ((Vptrofs (Ptrofs.repr a), (y, x)) : @reptype CompSpecs t_list) p *
    listrep hs x
 | nil =>
    !! (<< LIST_NULL_PTR : p = nullval >> ) && emp
 end.

Arguments listrep sigma p : simpl never.

Lemma listrep_local_facts sigma p :
   listrep sigma p |--
   !! (<< LIST_PTR_FACT : is_pointer_or_null p /\ (p=nullval <-> sigma=nil) >>).
Proof.
  intros.
  revert p; induction sigma; intros p.
  { unfold listrep. unnw. entailer!. split; auto. }
  unfold listrep; fold listrep.
  destruct a. entailer. unnw. entailer!.
  split; ins.
  subst. eapply field_compatible_nullval; eauto.
Qed.
#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer sigma p :
   listrep sigma p |-- valid_pointer p.
Proof.
  intros.
  unfold listrep. destruct sigma; simpl; unnw.
  { entailer!. }
  destruct p0. Intros x y. auto with valid_pointer.
Qed.
#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

Fixpoint lseg (sigma: list (Z * (list byte))) (x z: val) : mpred :=
  match sigma with
  | nil => !! (<< LSEG_PTR_FACT : x = z >>) && emp
  | (a, b)::hs => EX h: val, EX y:val, 
        malloc_token Ews (Tarray tschar (Zlength b + 1) noattr) y *
        cstring Ews b y *
        malloc_token Ews t_list x * 
        data_at Ews t_list ((Vptrofs (Ptrofs.repr a)), (y, h)) x * 
        lseg hs h z
  end.

Arguments lseg sigma x z : simpl never.

Lemma singleton_listrep (a : Z) (b : list byte) (h : val) (x: val) :
  cstring Ews b h *
  malloc_token Ews (Tarray tschar (Zlength b + 1) noattr) h *
  malloc_token Ews t_list x *
  data_at Ews t_list ((Vptrofs (Ptrofs.repr a)), (h, nullval)) x
   |-- listrep [(a, b)] x.
Proof.
  intros.
  unfold listrep.
  Exists nullval h.
  entailer!.
Qed.

Lemma singleton_lseg (a : Z) (b : list byte) (h : val) (x y: val) :
  cstring Ews b h *
  malloc_token Ews (Tarray tschar (Zlength b + 1) noattr) h *
  malloc_token Ews t_list x *
  data_at Ews t_list ((Vptrofs (Ptrofs.repr a)), (h, y)) x
   |-- lseg [(a, b)] x y.
Proof.
  intros.
  unfold lseg. 
  Exists y h.
  entailer!.
Qed.

Lemma lseg_list (s1 s2: list (Z * list byte)) (x y: val) :
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  generalize dependent x.
  induction s1; ins; unfold lseg.
  { entailer!. unnw. subst. entailer. }
  unfold lseg; fold lseg. destruct a.
  Intros h y0.
  unfold listrep; fold listrep. Exists h y0.
  entailer!. apply IHs1.
Qed.

Lemma lseg_lseg: forall (s1 s2: list (Z * list byte)) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros s1. induction s1.
  { intros. unfold lseg; fold lseg. simpl. entailer!. unnw. subst. entailer. }
  intros. unfold lseg; fold lseg. destruct a. Intros h y0. simpl.
  unfold lseg; fold lseg.
  Exists h y0.
  assert (
    malloc_token Ews (Tarray tschar (Zlength l + 1) noattr) y0
      * cstring Ews l y0
      * malloc_token Ews t_list x
      * data_at Ews t_list (Vptrofs (Ptrofs.repr z0), (y0, h)) x
      * lseg s1 h y
      * lseg s2 y z
      |-- 
    malloc_token Ews (Tarray tschar (Zlength l + 1) noattr) y0
      * cstring Ews l y0
      * malloc_token Ews t_list x
      * data_at Ews t_list (Vptrofs (Ptrofs.repr z0), (y0, h)) x
      * (lseg s1 h y
      * lseg s2 y z)
  ) as H by entailer!.
  eapply (derives_trans _ _ _); eauto.
  apply sepcon_derives; entailer.
Qed.

Lemma lseg_null_listrep (sigma : list (Z * list byte)) (p : val):
  lseg sigma p nullval |-- listrep sigma p.
Proof.
  revert p.
  induction sigma.
  { unfold lseg. unfold listrep. entailer!. }
  unfold lseg; fold lseg. destruct a.
  intros p.
  Intros h y.
  unfold listrep; fold listrep.
  Exists h y.
  entailer!.
Qed.


Definition list_copy_spec : ident * funspec :=
DECLARE _list_copy
  WITH sh : share, l : val, sigma : list (Z * (list byte)), gv: globals
  PRE [ tptr t_list ]
    PROP(0 <= Zlength sigma <= Int.max_unsigned;
         Forall (fun x => 0 <= fst x <= Int.max_unsigned /\ 0 <= Zlength (snd x) + 1 <= Int.max_unsigned) sigma)
    PARAMS(l) GLOBALS(gv)
    SEP(listrep sigma l; mem_mgr gv)
  POST [ tptr t_list ] 
    EX q: val,
    PROP()
    RETURN(q)
    SEP(listrep sigma l; listrep sigma q; mem_mgr gv).

Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a))
                                      :: string_to_list_byte s'
  end.

Definition sp_byte (n : nat) : list byte := repeat (Byte.repr 32) n.
Definition newline_byte : list byte := [Byte.repr 10].

Fixpoint shifted_text_from (sigma : list (Z * list byte)) (shift : nat) : list byte :=
  match sigma with
  | nil => nil
  | (s, l)::nil => sp_byte (Z.to_nat s + shift) ++ l
  | (s, l)::hs => sp_byte (Z.to_nat s + shift)
                    ++ l ++ newline_byte
                    ++ (shifted_text_from hs shift)
end.

Arguments shifted_text_from sigma shift : simpl never.

Definition text_from (sigma : list (Z * list byte))
  (shift : nat) (line : string)  : list byte :=
  let line_byte := string_to_list_byte line 
  in
    match sigma with 
    | nil => line_byte
    | (s, l)::nil => sp_byte (Z.to_nat s) ++ l ++ line_byte
    | (s, l)::hs  => sp_byte (Z.to_nat s)
                       ++ l ++ newline_byte
                       ++ shifted_text_from hs shift ++ line_byte
end.

Definition to_text_eq (to_text : nat -> string -> string)
  (sigma : list (Z * list byte)) := 
  forall (shift : nat) (line : string),
    string_to_list_byte (to_text shift line)
    = text_from sigma shift line.

Record list_mp (sigma : list (Z * list byte)) : Prop :=
  mk_list_mp {
    list_mp_length     : 0 <= Zlength sigma + 1 <= Int.max_unsigned;
    list_mp_forall_fst :
      Forall (fun x => 0 <= 4 * (fst x) <= Int.max_unsigned - 1) sigma;
    list_mp_forall_snd :
      Forall (fun x => 0 <= 4 * (Zlength (snd x)) + 1 <= Int.max_unsigned) sigma;
  }.

Definition first_line_width_pred (G : t) (sigma : list (Z * list byte)) : Prop :=
  match G.(height) with
  | 0%nat => G.(first_line_width) = 0%nat
  | _ => let fst_elem := Znth 0 sigma in
      G.(first_line_width) = Z.to_nat (fst fst_elem + Zlength (snd fst_elem))
  end.

Definition middle_width_pred (G : t) (sigma : list (Z * list byte)) : Prop :=
  match G.(height) with
  | 0%nat => G.(middle_width) = 0%nat
  | 1%nat|2%nat => let fst_elem := Znth 0 sigma in
      G.(middle_width) = Z.to_nat (fst fst_elem + Zlength (snd fst_elem))
  | _ => G.(middle_width) = list_max (map (fun x => Z.to_nat (fst x + Zlength (snd x))) (sublist 1 (Zlength sigma - 1) sigma))
  end.

Definition last_line_width_pred (G : t) (sigma : list (Z * list byte)) : Prop :=
  match G.(height) with
  | 0%nat => G.(last_line_width) = 0%nat
  | _ => let last_elem := Znth (Zlength sigma - 1) sigma in
      G.(last_line_width) = Z.to_nat (fst last_elem + Zlength (snd last_elem))
  end.

Record format_mp (G : t) (sigma : list (Z * list byte)) : Prop :=
  mk_format_mp {
    format_mp_text_eq : to_text_eq G.(to_text) sigma;
    format_mp_list_mp : list_mp sigma;
    format_mp_hg : 0 <= Z.of_nat (height G) <= Int.max_unsigned;
    format_mp_flw : 0 <= Z.of_nat (first_line_width G) <= Int.max_unsigned;
    format_mp_mw : 0 <= Z.of_nat (middle_width G) <= Int.max_unsigned;
    format_mp_llw : 0 <= Z.of_nat (last_line_width G) <= Int.max_unsigned;
    format_mp_zero_hg: Z.of_nat (height G) = Zlength sigma;
    format_mp_flw_eq : first_line_width_pred G sigma;
    format_mp_mw_eq : middle_width_pred G sigma;
    format_mp_llw_eq : last_line_width_pred G sigma;
  }.

Record format_comb_pred (G F : t) (sigmaG sigmaF : list (Z * list byte)) : Prop :=
  mk_format_comb {
    comb_hg_G : 0 <= 4 * Z.of_nat (height G) <= Int.max_unsigned;
    comb_flw_G : 0 <= 4 * Z.of_nat (first_line_width G) <= Int.max_unsigned;
    comb_mw_G : 0 <= 4 * Z.of_nat (middle_width G) <= Int.max_unsigned;
    comb_llw_G : 0 <= 4 * Z.of_nat (last_line_width G) <= Int.max_unsigned;
    comb_hg_F : 0 <= 4 * Z.of_nat (height F) <= Int.max_unsigned;
    comb_flw_F : 0 <= 4 * Z.of_nat (first_line_width F) <= Int.max_unsigned;
    comb_mw_F : 0 <= 4 * Z.of_nat (middle_width F) <= Int.max_unsigned;
    comb_llw_F : 0 <= 4 * Z.of_nat (last_line_width F) <= Int.max_unsigned;
    comb_ln : 0 <= Zlength sigmaG + Zlength sigmaF + 1 <= Int.max_unsigned;
  }.

 Definition concrete_mformat (G : t) (x : val) (sigma : list (Z * list byte)) (p : val) : mpred :=
  !! (<< FMT_MP : format_mp G sigma >> ) &&
  sepcon (malloc_token Ews t_format x)
  (sepcon 
  (data_at Ews t_format (Vint (Int.repr (Z.of_nat G.(height))),
                        (Vint (Int.repr (Z.of_nat G.(first_line_width))),
                         (Vint (Int.repr (Z.of_nat G.(middle_width))),
                          (Vint (Int.repr (Z.of_nat G.(last_line_width))), p)))) x)
  (listrep sigma p))
.

Definition mformat (G : t) (x : val) : mpred := 
  EX sigma : list (Z * list byte), 
  EX p : val,
  concrete_mformat G x sigma p
 .

 Definition less_components_spec : ident * funspec :=
 DECLARE _less_components
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val
  PRE [ tptr t_format, tptr t_format]
    PROP()
    PARAMS(pointer_G; pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG;
        concrete_mformat F pointer_F sigmaF pF)
  POST [ tbool ]
    EX a : bool,
    PROP(a = less_components G F)
    RETURN(Val.of_bool a)
    SEP(concrete_mformat G pointer_G sigmaG pG;
        concrete_mformat F pointer_F sigmaF pF).


Definition is_less_than_spec : ident * funspec :=
DECLARE _is_less_than
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val
  PRE [ tptr t_format, tptr t_format]
    PROP()
    PARAMS(pointer_G; pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG;
        concrete_mformat F pointer_F sigmaF pF)
  POST [ tbool ]
    EX a : bool,
    PROP(a = is_less_than G F)
    RETURN(Val.of_bool a)
    SEP(concrete_mformat G pointer_G sigmaG pG;
        concrete_mformat F pointer_F sigmaF pF).


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
    PROP(0 <= 4 * Zlength sigma + 1 <= Int.max_unsigned)
    PARAMS(p) GLOBALS(gv)
    SEP(mem_mgr gv; cstring Ews sigma p)
  POST [ tptr t_format ]
    EX q : val,
    PROP()
    RETURN(q)
    SEP(mem_mgr gv; mformat (line (list_byte_to_string sigma)) q; cstring Ews sigma p).
    

Definition sp_spec : ident * funspec :=
DECLARE _sp
  WITH n : Z, gv : globals
  PRE [ size_t ]
    PROP (0 <= n <= Int.max_unsigned - 1)
    PARAMS(Vptrofs (Ptrofs.repr n)) GLOBALS(gv)
    SEP(mem_mgr gv)
  POST [ tptr tschar ]
    EX p : val,
    PROP()
    RETURN(p)
    SEP(cstring Ews (sp_byte (Z.to_nat n)) p;
         malloc_token Ews (Tarray tschar (n + 1) noattr) p; mem_mgr gv).
        
Definition get_applied_length_spec : ident * funspec :=
DECLARE _get_applied_length
  WITH p : val, sigma : list (Z * list byte), shift : Z, q : val, line : list byte
  PRE [ tptr t_list, size_t, tptr tschar ]
    PROP ( << LIST_MP: list_mp sigma >>;
           0 <= Zlength line + 1 <= Int.max_unsigned; 
           0 <= shift <= Int.max_unsigned )
    PARAMS (p; Vptrofs (Ptrofs.repr shift); q)
    SEP (cstring Ews line q; listrep sigma p)
  POST [ size_t ]
    EX n : Z,
    PROP (n = Zlength (text_from sigma (Z.to_nat shift) (list_byte_to_string line)))
    RETURN (Vptrofs (Ptrofs.repr n))
    SEP(cstring Ews line q; listrep sigma p).

Definition format_copy_spec : ident * funspec := 
DECLARE _format_copy
  WITH G : t, p : val, sigmaG : list(Z * list byte), pG : val, gv : globals
  PRE [ tptr t_format ]
    PROP()
    PARAMS(p) GLOBALS(gv)
    SEP(concrete_mformat G p sigmaG pG; mem_mgr gv)
  POST [ tptr t_format ]
    EX q : val,
    PROP()
    RETURN(q)
    SEP(concrete_mformat G p sigmaG pG; mformat G q; mem_mgr gv).

Definition get_list_tail_spec : ident * funspec :=
DECLARE _get_list_tail
  WITH p : val, sigma : list (Z * list byte)
  PRE [ tptr t_list ]
    PROP(sigma <> nil)
    PARAMS(p)
    SEP(listrep sigma p)
  POST [ tptr t_list ]
    EX q : val,
    PROP()
    RETURN(q)
    SEP(listrep (sublist (Zlength sigma - 1) (Zlength sigma) sigma) q; 
        lseg (sublist 0 (Zlength sigma - 1) sigma) p q).
  
Definition list_concat_spec : ident * funspec :=
DECLARE _list_concat
  WITH l1 : list (Z * list byte), p1 : val, l2 : list (Z * list byte), p2 : val
  PRE [ tptr t_list, tptr t_list ]
    PROP(l1 <> []; l2 <> [])
    PARAMS(p1; p2)
    SEP(listrep l1 p1; listrep l2 p2)
  POST [ tptr t_list ]
    PROP()
    RETURN(p1)
    SEP(listrep (l1 ++ l2) p1).

Definition new_list_spec : ident * funspec :=
DECLARE _new_list
  WITH gv : globals
  PRE []
    PROP()
    PARAMS() GLOBALS(gv)
    SEP()
  POST [ tptr t_list ]
    EX p : val,
    PROP()
    RETURN(p)
    SEP(listrep [(0, [])] p).
  
Definition mdw_add_above_spec : ident * funspec :=
DECLARE _mdw_add_above
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
      sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
      pG : val, pF : val, gv : globals
  PRE [ tptr t_format, tptr t_format ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  POST [ tuint ]
    PROP(0 <= Z.of_nat (middle_width (add_above G F)) <= Int.max_unsigned)
    RETURN(Vint (Int.repr (Z.of_nat (middle_width (add_above G F)))))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF).

Definition to_text_add_above_spec : ident * funspec :=
DECLARE _to_text_add_above
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val, gv : globals
  PRE [ tptr t_format, tptr t_format ]
    PROP (0 <= Zlength sigmaG + Zlength sigmaF + 1 <= Int.max_unsigned)
    PARAMS(pointer_G; pointer_F) GLOBALS(gv)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
      concrete_mformat F pointer_F sigmaF pF; mem_mgr gv)
  POST [ tptr t_list ]
    EX q : val, EX sigma : list (Z * list byte),
    PROP(to_text_eq (to_text (add_above G F)) sigma; list_mp sigma;
          sigma = sigmaG ++ sigmaF)
    RETURN(q)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
        concrete_mformat F pointer_F sigmaF pF;
        mem_mgr gv;
        listrep sigma q).

Definition add_above_spec : ident * funspec :=
DECLARE _add_above
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val, gv : globals
  PRE [ tptr t_format, tptr t_format ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF>>)
    PARAMS(pointer_G; pointer_F) GLOBALS(gv)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
        concrete_mformat F pointer_F sigmaF pF; 
        mem_mgr gv)
  POST [ tptr t_format ]
    EX p : val, EX sigma : list (Z * list byte), EX sigma_pt : val,
    PROP()
    RETURN(p)
    SEP(!! (Forall (fun x => 0 <= (fst x) + (Zlength (snd x)) <= Int.max_unsigned) sigma) &&
        concrete_mformat G pointer_G sigmaG pG; 
        concrete_mformat F pointer_F sigmaF pF; 
        concrete_mformat (add_above G F) p sigma sigma_pt;
        mem_mgr gv).

Definition line_concats_spec : ident * funspec :=
DECLARE _line_concats
  WITH l1 : list byte, p1 : val, l2 : list byte, p2 : val, shift : Z, gv : globals
  PRE [ tptr tschar, size_t, tptr tschar ]
    PROP(0 <= 4 * (Zlength l1 + shift + Zlength l2) + 1 <= Int.max_unsigned;
          0 <= shift <= Int.max_unsigned - 1)
    PARAMS(p1; Vptrofs (Ptrofs.repr shift); p2) GLOBALS(gv)
    SEP(mem_mgr gv; cstring Ews l1 p1; cstring Ews l2 p2;
        malloc_token Ews (Tarray tschar (Zlength l1 + 1) noattr) p1;
        malloc_token Ews (Tarray tschar (Zlength l2 + 1) noattr) p2)
  POST [ tptr tschar ]
    EX sigma : list byte, EX p : val,
    PROP(<< LINE_CON_EQ: sigma = l1 ++ sp_byte (Z.to_nat shift) ++ l2 >>;
          0 <= 4 * Zlength sigma + 1 <= Int.max_unsigned)
    RETURN(p)
    SEP(mem_mgr gv; cstring Ews sigma p;
        malloc_token Ews (Tarray tschar (Zlength l1 + shift + Zlength l2 + 1) noattr) p).

Definition shift_list_spec : ident * funspec :=
DECLARE _shift_list
  WITH sigma : list (Z * list byte), p : val, shift : Z
  PRE [ tptr t_list, size_t ]
    PROP(0 <= Zlength sigma + 1 <= Int.max_unsigned;
          Forall (fun x => 0 <= fst x + shift <= Int.max_unsigned) sigma)
    PARAMS(p; Vptrofs (Ptrofs.repr shift))
    SEP(listrep sigma p)
  POST [ tptr t_list ]
    PROP(0 <= Zlength sigma + 1 <= Int.max_unsigned;
          Forall (fun x => 0 <= fst x + shift <= Int.max_unsigned) sigma)
    RETURN(p)
    SEP(listrep (map (fun x => (fst x + shift, snd x)) sigma) p).

  
Definition to_text_add_beside_pred (G F : t) (sigmaG sigmaF : list (Z * list byte)) : Prop :=
  match sigmaF with
  | nil => True
  | h::hs => Forall (fun x => 0 <= 4 * (Zlength (snd x) + (fst h) + Zlength (snd h)) + 1 <= Int.max_unsigned) sigmaG
end.

Definition mdw_add_beside_spec : ident * funspec :=
DECLARE _mdw_add_beside
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
      sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
      pG : val, pF : val
  PRE [ tptr t_format, tptr t_format ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  POST [ tuint ]
    PROP(0 <= Z.of_nat (middle_width (add_beside G F)) <= Int.max_unsigned)
    RETURN(Vint (Int.repr (Z.of_nat (middle_width (add_beside G F)))))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF).

Definition flw_add_beside_spec : ident * funspec :=
DECLARE _flw_add_beside
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
      sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
      pG : val, pF : val
  PRE [ tptr t_format, tptr t_format ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  POST [ tuint ]
    PROP(0 <= Z.of_nat (first_line_width (add_beside G F)) <= Int.max_unsigned)
    RETURN(Vint (Int.repr (Z.of_nat (first_line_width (add_beside G F)))))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF).

Definition list_add_beside_length (sigmaG sigmaF : list (Z * list byte)) :=
  match sigmaG, sigmaF with
  | nil, _ => Zlength sigmaF
  | _, nil => Zlength sigmaG
  | _, _ => Zlength sigmaG + Zlength sigmaF - 1
  end.

Definition to_text_add_beside_spec : ident * funspec :=
DECLARE _to_text_add_beside
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val, gv : globals
  PRE [ tptr t_format, tptr t_format ]
    PROP (0 <= Zlength sigmaG + Zlength sigmaF + 1 <= Int.max_unsigned;
          << STMT: Forall (fun x => 0 <= 4 * (fst x + (Z.of_nat (last_line_width G))) <= Int.max_unsigned - 1) sigmaF>>;
          << AB_PRED: to_text_add_beside_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F) GLOBALS(gv)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
      concrete_mformat F pointer_F sigmaF pF; mem_mgr gv)
  POST [ tptr t_list ]
    EX q : val, EX sigma : list (Z * list byte),
    PROP(to_text_eq (to_text (add_beside G F)) sigma; list_mp sigma;
          0 <= Zlength sigma + 1 <= Int.max_unsigned;
          Zlength sigma = list_add_beside_length sigmaG sigmaF;
          first_line_width_pred (add_beside G F) sigma;
          middle_width_pred (add_beside G F) sigma;
          last_line_width_pred (add_beside G F) sigma)
    RETURN(q)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
        concrete_mformat F pointer_F sigmaF pF;
        mem_mgr gv;
        listrep sigma q).

Definition add_beside_spec : ident * funspec :=
DECLARE _add_beside
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val, gv : globals
  PRE [ tptr t_format, tptr t_format ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF>>;
          << STMT: Forall (fun x => 0 <= 4 * (fst x + (Z.of_nat (last_line_width G))) <= Int.max_unsigned - 1) sigmaF>>;
          << AB_PRED: to_text_add_beside_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F) GLOBALS(gv)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
      concrete_mformat F pointer_F sigmaF pF; mem_mgr gv)
  POST [ tptr t_format ]
    EX p : val, EX sigma : list (Z * list byte), EX sigma_pt : val,
    PROP()
    RETURN(p)
    SEP(!! (Forall (fun x => 0 <= (fst x) + (Zlength (snd x)) <= Int.max_unsigned) sigma) &&
        concrete_mformat G pointer_G sigmaG pG; 
        concrete_mformat F pointer_F sigmaF pF; 
        concrete_mformat (add_beside G F) p sigma sigma_pt; mem_mgr gv).

Definition mdw_add_fill_spec : ident * funspec :=
DECLARE _mdw_add_fill
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
      sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
      pG : val, pF : val, shift : Z
  PRE [ tptr t_format, tptr t_format, size_t ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF >>;
          0 <= 4 * shift <= Int.max_unsigned)
    PARAMS(pointer_G; pointer_F; Vptrofs (Ptrofs.repr shift))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  POST [ tuint ]
    PROP(0 <= Z.of_nat (middle_width (add_fill G F (Z.to_nat shift))) <= Int.max_unsigned)
    RETURN(Vint (Int.repr (Z.of_nat (middle_width (add_fill G F (Z.to_nat shift))))))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF).

Definition llw_add_fill_spec : ident * funspec :=
DECLARE _llw_add_fill
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
      sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
      pG : val, pF : val, shift : Z
  PRE [ tptr t_format, tptr t_format, size_t ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF >>;
          0 <= 4 * shift <= Int.max_unsigned)
    PARAMS(pointer_G; pointer_F; Vptrofs (Ptrofs.repr shift))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  POST [ tuint ]
    PROP(0 <= Z.of_nat (last_line_width (add_fill G F (Z.to_nat shift))) <= Int.max_unsigned)
    RETURN(Vint (Int.repr (Z.of_nat (last_line_width (add_fill G F (Z.to_nat shift))))))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF).

Definition flw_add_fill_spec : ident * funspec :=
DECLARE _flw_add_fill
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
      sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
      pG : val, pF : val, shift : Z
  PRE [ tptr t_format, tptr t_format ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F)
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF)
  POST [ tuint ]
    PROP(0 <= Z.of_nat (first_line_width (add_fill G F (Z.to_nat shift))) <= Int.max_unsigned)
    RETURN(Vint (Int.repr (Z.of_nat (first_line_width (add_fill G F (Z.to_nat shift))))))
    SEP(concrete_mformat G pointer_G sigmaG pG; concrete_mformat F pointer_F sigmaF pF).

Definition to_text_add_fill_spec : ident * funspec :=
DECLARE _to_text_add_fill
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val, shift : Z, gv : globals
  PRE [ tptr t_format, tptr t_format, size_t ]
    PROP (0 <= Zlength sigmaG + Zlength sigmaF + 1 <= Int.max_unsigned;
          << STMT: Forall (fun x => 0 <= 4 * (fst x + shift) <= Int.max_unsigned - 1) sigmaF>>;
          0 <= shift <= Int.max_unsigned;
          << AB_PRED: to_text_add_beside_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F; Vptrofs (Ptrofs.repr shift)) GLOBALS(gv)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
      concrete_mformat F pointer_F sigmaF pF; mem_mgr gv)
  POST [ tptr t_list ]
    EX q : val, EX sigma : list (Z * list byte),
    PROP(to_text_eq (to_text (add_fill G F (Z.to_nat shift))) sigma; list_mp sigma;
          0 <= Zlength sigma + 1 <= Int.max_unsigned;
          Zlength sigma = list_add_beside_length sigmaG sigmaF;
          first_line_width_pred (add_fill G F (Z.to_nat shift)) sigma;
          middle_width_pred (add_fill G F (Z.to_nat shift)) sigma;
          last_line_width_pred (add_fill G F (Z.to_nat shift)) sigma)
    RETURN(q)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
        concrete_mformat F pointer_F sigmaF pF;
        mem_mgr gv;
        listrep sigma q).

Definition add_fill_spec : ident * funspec :=
DECLARE _add_fill
  WITH G : t, F : t, pointer_G : val, pointer_F : val,
    sigmaG : list (Z * list byte), sigmaF : (list (Z * list byte)),
    pG : val, pF : val, shift : Z, gv : globals
  PRE [ tptr t_format, tptr t_format, size_t ]
    PROP (<< COMB: format_comb_pred G F sigmaG sigmaF>>;
          << STMT: Forall (fun x => 0 <= 4 * (fst x + shift) <= Int.max_unsigned - 1) sigmaF>>;
          0 <= 4 * shift <= Int.max_unsigned;
          << AB_PRED: to_text_add_beside_pred G F sigmaG sigmaF >>)
    PARAMS(pointer_G; pointer_F; Vptrofs (Ptrofs.repr shift)) GLOBALS(gv)
    SEP(concrete_mformat G pointer_G sigmaG pG; 
      concrete_mformat F pointer_F sigmaF pF; mem_mgr gv)
  POST [ tptr t_format ]
    EX p : val, EX sigma : list (Z * list byte), EX sigma_pt : val,
    PROP()
    RETURN(p)
    SEP(!! (Forall (fun x => 0 <= (fst x) + (Zlength (snd x)) <= Int.max_unsigned) sigma) &&
        concrete_mformat G pointer_G sigmaG pG; 
        concrete_mformat F pointer_F sigmaF pF; 
        concrete_mformat (add_fill G F (Z.to_nat shift)) p sigma sigma_pt; mem_mgr gv).
      
(* ----------------------- *)
(* ----------------------- *)
(* ----------------------- *)

Ltac dest_ptr ptr := 
  destruct (eq_dec ptr nullval);
  [ forward_if(ptr <> nullval);
    [ forward_call; entailer | forward; entailer! | now Intros] |
    forward_if(ptr <> nullval);
    [ forward_call; entailer | forward; entailer! | ]
  ]; Intros.

Ltac unff def := unfold def; fold def.

Ltac prove_ptr := entailer!; unnw; desf.

(* ----------------------- *)
(* ----------------------- *)
(* ----------------------- *)

Lemma string_to_list_byte_app (l1 l2 : string) :
  string_to_list_byte (l1 ++ l2) =
    string_to_list_byte l1 ++ string_to_list_byte l2.
Proof.
  induction l1; ins.
  now rewrite IHl1.
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

Lemma string_to_string_eq (s : string):
  list_byte_to_string (string_to_list_byte s) = s.
Proof.
  induction s.
  { list_solve. }
  unff string_to_list_byte.
  unff list_byte_to_string.
  rewrite IHs.
  rewrite Byte.unsigned_repr.
  2: { 
    assert (N_of_ascii a < 256)%N as K.
    { apply N_ascii_bounded. }
    unfold Byte.max_unsigned.
    ins; lia. }
  rewrite N2Z.id.
  rewrite ascii_N_embedding; ins.
Qed.