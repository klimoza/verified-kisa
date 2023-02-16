Require Import HahnBase.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import printer.printer_files.compiled_format.
Require Import printer.verified_printer.Format.
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
    !! (<< LIST_NULL_PTR : p = nullval >> ) && emp
 end.

Arguments listrep sigma p : simpl never.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (<< LIST_PTR_FACT : is_pointer_or_null p /\ (p=nullval <-> sigma=nil) >>).
Proof.
  intros.

  revert p; induction sigma; intros p.
  { unfold listrep. unnw. entailer!. split; auto. }
  unfold listrep; fold listrep. destruct a. entailer. unnw. entailer!. split; intro.
  2: now auto.
  subst. eapply field_compatible_nullval; eauto.
Qed.
#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
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

Record list_mp (sigma : list (Z * list byte)) : Prop :=
  mk_list_mp {
    list_mp_length     : 0 <= Zlength sigma + 1 <= Int.max_unsigned;
    list_mp_forall_fst :
      Forall (fun x => 0 <= (fst x) <= Int.max_unsigned) sigma;
    list_mp_forall_snd :
      Forall (fun x => 0 <= Zlength (snd x) + 1 <= Int.max_unsigned) sigma;
  }.

Record format_mp (G : t) (sigma : list (Z * list byte)) : Prop :=
  mk_format_mp {
    format_mp_text_eq : to_text_eq G.(to_text) sigma;
    format_mp_list_mp : list_mp sigma;
    format_mp_hg : 0 <= Z.of_nat (height G) <= Int.max_unsigned;
    format_mp_flw : 0 <= Z.of_nat (first_line_width G) <= Int.max_unsigned;
    format_mp_mw : 0 <= Z.of_nat (middle_width G) <= Int.max_unsigned;
    format_mp_llw : 0 <= Z.of_nat (last_line_width G) <= Int.max_unsigned;
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
    PROP(0 <= Zlength sigma + 1 <= Int.max_unsigned)
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
         malloc_token Ews (Tarray tschar (n + 1) noattr) p; mem_mgr gv).

Definition add_above_spec : ident * funspec :=
DECLARE _add_above
  WITH G : t, F : t, pointer_G : val, pointer_F : val, gv : globals
  PRE [ tptr t_format, tptr t_format ]
    PROP ()
    PARAMS(pointer_G; pointer_F) GLOBALS(gv)
    SEP(mformat G pointer_G; mformat F pointer_F; mem_mgr gv)
  POST [ tptr t_format ]
    EX p : val,
    PROP()
    RETURN(p)
    SEP(mformat G pointer_G; mformat F pointer_F; 
        mformat (add_above G F) p; mem_mgr gv).


Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   max_spec; strlen_spec; strcpy_spec; strcat_spec;
                   list_copy_spec; less_components_spec; is_less_than_spec; 
                   empty_spec; line_spec; sp_spec
 ]).
