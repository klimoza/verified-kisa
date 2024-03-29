From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.11".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "code/format.c".
  Definition normalized := true.
End Info.

Definition _F : ident := $"F".
Definition _G : ident := $"G".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition _a : ident := $"a".
Definition _above_doc : ident := $"above_doc".
Definition _add_above : ident := $"add_above".
Definition _add_beside : ident := $"add_beside".
Definition _add_fill : ident := $"add_fill".
Definition _b : ident := $"b".
Definition _beside_doc : ident := $"beside_doc".
Definition _child1 : ident := $"child1".
Definition _child2 : ident := $"child2".
Definition _choice_doc : ident := $"choice_doc".
Definition _clear_format_list : ident := $"clear_format_list".
Definition _clear_last_format_element : ident := $"clear_last_format_element".
Definition _clear_to_text : ident := $"clear_to_text".
Definition _construct_doc : ident := $"construct_doc".
Definition _copy_F : ident := $"copy_F".
Definition _cur : ident := $"cur".
Definition _cur_sigma : ident := $"cur_sigma".
Definition _d : ident := $"d".
Definition _d__1 : ident := $"d__1".
Definition _dest : ident := $"dest".
Definition _doc : ident := $"doc".
Definition _empty : ident := $"empty".
Definition _evaluator_trivial : ident := $"evaluator_trivial".
Definition _exit : ident := $"exit".
Definition _f : ident := $"f".
Definition _fill_doc : ident := $"fill_doc".
Definition _first_line_width : ident := $"first_line_width".
Definition _first_line_width_new : ident := $"first_line_width_new".
Definition _flw_add_beside : ident := $"flw_add_beside".
Definition _flw_add_fill : ident := $"flw_add_fill".
Definition _format_copy : ident := $"format_copy".
Definition _format_list : ident := $"format_list".
Definition _format_list_copy : ident := $"format_list_copy".
Definition _format_tail : ident := $"format_tail".
Definition _free : ident := $"free".
Definition _fs : ident := $"fs".
Definition _fs1 : ident := $"fs1".
Definition _fs1_tail : ident := $"fs1_tail".
Definition _fs2 : ident := $"fs2".
Definition _fs2_tail : ident := $"fs2_tail".
Definition _fs_tail : ident := $"fs_tail".
Definition _get_applied_length : ident := $"get_applied_length".
Definition _get_format_list_tail : ident := $"get_format_list_tail".
Definition _get_list_tail : ident := $"get_list_tail".
Definition _has_item : ident := $"has_item".
Definition _head : ident := $"head".
Definition _height : ident := $"height".
Definition _i : ident := $"i".
Definition _indent : ident := $"indent".
Definition _indent_doc : ident := $"indent_doc".
Definition _is_less_than : ident := $"is_less_than".
Definition _j : ident := $"j".
Definition _l : ident := $"l".
Definition _l1 : ident := $"l1".
Definition _l1_tail : ident := $"l1_tail".
Definition _l2 : ident := $"l2".
Definition _l_cur : ident := $"l_cur".
Definition _last_line_width : ident := $"last_line_width".
Definition _last_line_width_new : ident := $"last_line_width_new".
Definition _less_components : ident := $"less_components".
Definition _line : ident := $"line".
Definition _line__1 : ident := $"line__1".
Definition _line_concats : ident := $"line_concats".
Definition _list : ident := $"list".
Definition _list_concat : ident := $"list_concat".
Definition _list_copy : ident := $"list_copy".
Definition _llw_add_fill : ident := $"llw_add_fill".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _max : ident := $"max".
Definition _max_width_check : ident := $"max_width_check".
Definition _mdw_add_above : ident := $"mdw_add_above".
Definition _mdw_add_beside : ident := $"mdw_add_beside".
Definition _mdw_add_fill : ident := $"mdw_add_fill".
Definition _middle_width : ident := $"middle_width".
Definition _middle_width_new : ident := $"middle_width_new".
Definition _n : ident := $"n".
Definition _new : ident := $"new".
Definition _new_line : ident := $"new_line".
Definition _new_list : ident := $"new_list".
Definition _new_result_tail : ident := $"new_result_tail".
Definition _new_string : ident := $"new_string".
Definition _new_string_list : ident := $"new_string_list".
Definition _newline : ident := $"newline".
Definition _nt : ident := $"nt".
Definition _result : ident := $"result".
Definition _result__1 : ident := $"result__1".
Definition _result__2 : ident := $"result__2".
Definition _result_tail : ident := $"result_tail".
Definition _s : ident := $"s".
Definition _shift : ident := $"shift".
Definition _shift_list : ident := $"shift_list".
Definition _shifted : ident := $"shifted".
Definition _sigma : ident := $"sigma".
Definition _sp : ident := $"sp".
Definition _space : ident := $"space".
Definition _split : ident := $"split".
Definition _src : ident := $"src".
Definition _str : ident := $"str".
Definition _strcat : ident := $"strcat".
Definition _strcpy : ident := $"strcpy".
Definition _string_list : ident := $"string_list".
Definition _strlen : ident := $"strlen".
Definition _t : ident := $"t".
Definition _tail : ident := $"tail".
Definition _to_string : ident := $"to_string".
Definition _to_text : ident := $"to_text".
Definition _to_text_add_above : ident := $"to_text_add_above".
Definition _to_text_add_beside : ident := $"to_text_add_beside".
Definition _to_text_add_fill : ident := $"to_text_add_fill".
Definition _to_text_apply : ident := $"to_text_apply".
Definition _to_text_cpy : ident := $"to_text_cpy".
Definition _to_text_head : ident := $"to_text_head".
Definition _to_text_new : ident := $"to_text_new".
Definition _total_length : ident := $"total_length".
Definition _total_width : ident := $"total_width".
Definition _type : ident := $"type".
Definition _width : ident := $"width".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_strlen := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _str (tptr tschar)) (Etempvar _i tulong)
              (tptr tschar)) tschar))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tschar)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Etempvar _i tulong)))
          Sskip)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_strcpy := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tschar)) :: (_src, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_d, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _src (tptr tschar)) (Etempvar _i tulong)
                (tptr tschar)) tschar))
          (Sset _d (Ecast (Etempvar _t'1 tschar) tschar)))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _dest (tptr tschar))
                (Etempvar _i tulong) (tptr tschar)) tschar)
            (Etempvar _d tschar))
          (Sifthenelse (Ebinop Oeq (Etempvar _d tschar)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Etempvar _dest (tptr tschar))))
            Sskip))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_strcat := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tschar)) :: (_src, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_j, tulong) :: (_d, tschar) ::
               (_d__1, tschar) :: (_t'2, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        Sskip
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _dest (tptr tschar))
                  (Etempvar _i tulong) (tptr tschar)) tschar))
            (Sset _d (Ecast (Etempvar _t'2 tschar) tschar)))
          (Sifthenelse (Ebinop Oeq (Etempvar _d tschar)
                         (Econst_int (Int.repr 0) tint) tint)
            Sbreak
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Ssequence
    (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        Sskip
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _src (tptr tschar))
                  (Etempvar _j tulong) (tptr tschar)) tschar))
            (Sset _d__1 (Ecast (Etempvar _t'1 tschar) tschar)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _dest (tptr tschar))
                  (Ebinop Oadd (Etempvar _i tulong) (Etempvar _j tulong)
                    tulong) (tptr tschar)) tschar) (Etempvar _d__1 tschar))
            (Sifthenelse (Ebinop Oeq (Etempvar _d__1 tschar)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sreturn (Some (Etempvar _dest (tptr tschar))))
              Sskip))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tulong) (Econst_int (Int.repr 1) tint)
          tulong)))))
|}.

Definition f_max := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_a, tuint) :: (_b, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _a tuint) (Etempvar _b tuint) tint)
    (Sreturn (Some (Etempvar _b tuint)))
    Sskip)
  (Sreturn (Some (Etempvar _a tuint))))
|}.

Definition f_list_copy := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_new, (tptr (Tstruct _list noattr))) ::
               (_cur, (tptr (Tstruct _list noattr))) ::
               (_l_cur, (tptr (Tstruct _list noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tulong) :: (_t'1, (tptr tvoid)) :: (_t'11, tulong) ::
               (_t'10, (tptr tschar)) :: (_t'9, (tptr tschar)) ::
               (_t'8, (tptr tschar)) :: (_t'7, (tptr tschar)) ::
               (_t'6, (tptr (Tstruct _list noattr))) ::
               (_t'5, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _l (tptr (Tstruct _list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _list noattr) tulong) :: nil))
      (Sset _new (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _new (tptr (Tstruct _list noattr))) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Sset _cur (Etempvar _new (tptr (Tstruct _list noattr))))
        (Ssequence
          (Sset _l_cur (Etempvar _l (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sloop
              (Ssequence
                Sskip
                (Ssequence
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef
                          (Etempvar _l_cur (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _shift tulong))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _cur (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _shift tulong)
                      (Etempvar _t'11 tulong)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'10
                            (Efield
                              (Ederef
                                (Etempvar _l_cur (tptr (Tstruct _list noattr)))
                                (Tstruct _list noattr)) _line (tptr tschar)))
                          (Scall (Some _t'2)
                            (Evar _strlen (Tfunction
                                            (Tcons (tptr tschar) Tnil) tulong
                                            cc_default))
                            ((Etempvar _t'10 (tptr tschar)) :: nil)))
                        (Scall (Some _t'3)
                          (Evar _malloc (Tfunction (Tcons tulong Tnil)
                                          (tptr tvoid) cc_default))
                          ((Ebinop Oadd (Etempvar _t'2 tulong)
                             (Econst_int (Int.repr 1) tint) tulong) :: nil)))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _cur (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _line (tptr tschar))
                        (Etempvar _t'3 (tptr tvoid))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Etempvar _cur (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _line (tptr tschar)))
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _t'9 (tptr tschar)) tint)
                          (Scall None
                            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                          cc_default))
                            ((Econst_int (Int.repr 1) tint) :: nil))
                          Sskip))
                      (Ssequence
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Ederef
                                (Etempvar _cur (tptr (Tstruct _list noattr)))
                                (Tstruct _list noattr)) _line (tptr tschar)))
                          (Ssequence
                            (Sset _t'8
                              (Efield
                                (Ederef
                                  (Etempvar _l_cur (tptr (Tstruct _list noattr)))
                                  (Tstruct _list noattr)) _line
                                (tptr tschar)))
                            (Scall None
                              (Evar _strcpy (Tfunction
                                              (Tcons (tptr tschar)
                                                (Tcons (tptr tschar) Tnil))
                                              (tptr tschar) cc_default))
                              ((Etempvar _t'7 (tptr tschar)) ::
                               (Etempvar _t'8 (tptr tschar)) :: nil))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _cur (tptr (Tstruct _list noattr)))
                                (Tstruct _list noattr)) _tail
                              (tptr (Tstruct _list noattr)))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'6
                                (Efield
                                  (Ederef
                                    (Etempvar _l_cur (tptr (Tstruct _list noattr)))
                                    (Tstruct _list noattr)) _tail
                                  (tptr (Tstruct _list noattr))))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _t'6 (tptr (Tstruct _list noattr)))
                                             (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)) tint)
                                (Ssequence
                                  (Sset _cur
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)))
                                  Sbreak)
                                Sskip))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'4)
                                  (Evar _malloc (Tfunction
                                                  (Tcons tulong Tnil)
                                                  (tptr tvoid) cc_default))
                                  ((Esizeof (Tstruct _list noattr) tulong) ::
                                   nil))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _cur (tptr (Tstruct _list noattr)))
                                      (Tstruct _list noattr)) _tail
                                    (tptr (Tstruct _list noattr)))
                                  (Etempvar _t'4 (tptr tvoid))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'5
                                    (Efield
                                      (Ederef
                                        (Etempvar _cur (tptr (Tstruct _list noattr)))
                                        (Tstruct _list noattr)) _tail
                                      (tptr (Tstruct _list noattr))))
                                  (Sifthenelse (Eunop Onotbool
                                                 (Etempvar _t'5 (tptr (Tstruct _list noattr)))
                                                 tint)
                                    (Scall None
                                      (Evar _exit (Tfunction
                                                    (Tcons tint Tnil) tvoid
                                                    cc_default))
                                      ((Econst_int (Int.repr 1) tint) :: nil))
                                    Sskip))
                                (Ssequence
                                  (Sset _cur
                                    (Efield
                                      (Ederef
                                        (Etempvar _cur (tptr (Tstruct _list noattr)))
                                        (Tstruct _list noattr)) _tail
                                      (tptr (Tstruct _list noattr))))
                                  (Sset _l_cur
                                    (Efield
                                      (Ederef
                                        (Etempvar _l_cur (tptr (Tstruct _list noattr)))
                                        (Tstruct _list noattr)) _tail
                                      (tptr (Tstruct _list noattr))))))))))))))
              Sskip)
            (Sreturn (Some (Etempvar _new (tptr (Tstruct _list noattr)))))))))))
|}.

Definition f_new_list := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _list noattr) tulong) :: nil))
    (Sset _result (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _result (tptr (Tstruct _list noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _shift tulong)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _line (tptr tschar))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Sreturn (Some (Etempvar _result (tptr (Tstruct _list noattr))))))))))
|}.

Definition f_sp := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr tschar)) :: (_space, tschar) ::
               (_i, tulong) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Ebinop Oadd (Etempvar _n tulong) (Econst_int (Int.repr 1) tint)
         tulong) :: nil))
    (Sset _result (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _result (tptr tschar)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sset _space (Ecast (Econst_int (Int.repr 32) tint) tschar))
      (Ssequence
        (Ssequence
          (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                             (Etempvar _n tulong) tint)
                Sskip
                Sbreak)
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _result (tptr tschar))
                    (Etempvar _i tulong) (tptr tschar)) tschar)
                (Etempvar _space tschar)))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tulong)
                (Econst_int (Int.repr 1) tint) tulong))))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _result (tptr tschar))
                (Etempvar _n tulong) (tptr tschar)) tschar)
            (Econst_int (Int.repr 0) tint))
          (Sreturn (Some (Etempvar _result (tptr tschar)))))))))
|}.

Definition f_get_applied_length := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_to_text, (tptr (Tstruct _list noattr))) ::
                (_shift, tulong) :: (_line__1, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_total_length, tulong) ::
               (_to_text_cpy, (tptr (Tstruct _list noattr))) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: (_t'8, (tptr tschar)) :: (_t'7, tulong) ::
               (_t'6, (tptr tschar)) :: (_t'5, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _to_text (tptr (Tstruct _list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                        cc_default))
        ((Etempvar _line__1 (tptr tschar)) :: nil))
      (Sreturn (Some (Etempvar _t'1 tulong))))
    Sskip)
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _line (tptr tschar)))
        (Scall (Some _t'2)
          (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                          cc_default))
          ((Etempvar _t'8 (tptr tschar)) :: nil)))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _shift tulong))
        (Sset _total_length
          (Ebinop Oadd (Etempvar _t'7 tulong) (Etempvar _t'2 tulong) tulong))))
    (Ssequence
      (Sset _to_text_cpy
        (Efield
          (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                            cc_default))
            ((Etempvar _line__1 (tptr tschar)) :: nil))
          (Sset _total_length
            (Ebinop Oadd (Etempvar _total_length tulong)
              (Etempvar _t'3 tulong) tulong)))
        (Ssequence
          (Swhile
            (Ebinop One (Etempvar _to_text_cpy (tptr (Tstruct _list noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _to_text_cpy (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _line (tptr tschar)))
                  (Scall (Some _t'4)
                    (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil)
                                    tulong cc_default))
                    ((Etempvar _t'6 (tptr tschar)) :: nil)))
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef
                        (Etempvar _to_text_cpy (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _shift tulong))
                  (Sset _total_length
                    (Ebinop Oadd (Etempvar _total_length tulong)
                      (Ebinop Oadd
                        (Ebinop Oadd
                          (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                            (Etempvar _t'5 tulong) tulong)
                          (Etempvar _shift tulong) tulong)
                        (Etempvar _t'4 tulong) tulong) tulong))))
              (Sset _to_text_cpy
                (Efield
                  (Ederef
                    (Etempvar _to_text_cpy (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _tail
                  (tptr (Tstruct _list noattr))))))
          (Sreturn (Some (Etempvar _total_length tulong))))))))
|}.

Definition f_to_text_apply := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_to_text, (tptr (Tstruct _list noattr))) ::
                (_shift, tulong) :: (_line__1, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_total_length, tulong) :: (_result, (tptr tschar)) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tulong) :: (_t'6, (tptr tschar)) :: (_t'5, tulong) ::
               (_t'4, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _to_text (tptr (Tstruct _list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Etempvar _line__1 (tptr tschar))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_applied_length (Tfunction
                                    (Tcons (tptr (Tstruct _list noattr))
                                      (Tcons tulong
                                        (Tcons (tptr tschar) Tnil))) tulong
                                    cc_default))
        ((Etempvar _to_text (tptr (Tstruct _list noattr))) ::
         (Etempvar _shift tulong) :: (Etempvar _line__1 (tptr tschar)) ::
         nil))
      (Sset _total_length (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Ebinop Oadd (Etempvar _total_length tulong)
             (Econst_int (Int.repr 1) tint) tulong) :: nil))
        (Sset _result (Etempvar _t'2 (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _line (tptr tschar)))
          (Scall None
            (Evar _strcpy (Tfunction
                            (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil))
                            (tptr tschar) cc_default))
            ((Etempvar _result (tptr tschar)) ::
             (Etempvar _t'6 (tptr tschar)) :: nil)))
        (Ssequence
          (Swhile
            (Ebinop One (Etempvar _to_text (tptr (Tstruct _list noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef
                        (Etempvar _to_text (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _shift tulong))
                  (Scall (Some _t'3)
                    (Evar _sp (Tfunction (Tcons tulong Tnil) (tptr tschar)
                                cc_default))
                    ((Ebinop Oadd (Etempvar _t'5 tulong)
                       (Etempvar _shift tulong) tulong) :: nil)))
                (Scall None
                  (Evar _strcat (Tfunction
                                  (Tcons (tptr tschar)
                                    (Tcons (tptr tschar) Tnil)) (tptr tschar)
                                  cc_default))
                  ((Etempvar _result (tptr tschar)) ::
                   (Etempvar _t'3 (tptr tschar)) :: nil)))
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _to_text (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _line (tptr tschar)))
                  (Scall None
                    (Evar _strcat (Tfunction
                                    (Tcons (tptr tschar)
                                      (Tcons (tptr tschar) Tnil))
                                    (tptr tschar) cc_default))
                    ((Etempvar _result (tptr tschar)) ::
                     (Etempvar _t'4 (tptr tschar)) :: nil)))
                (Sset _to_text
                  (Efield
                    (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _list noattr)))))))
          (Sreturn (Some (Etempvar _result (tptr tschar)))))))))
|}.

Definition f_less_components := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _height tuint))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _height tuint))
          (Sifthenelse (Ebinop Ole (Etempvar _t'8 tuint)
                         (Etempvar _t'9 tuint) tint)
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _first_line_width tuint))
              (Ssequence
                (Sset _t'11
                  (Efield
                    (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _first_line_width tuint))
                (Sset _t'1
                  (Ecast
                    (Ebinop Ole (Etempvar _t'10 tuint) (Etempvar _t'11 tuint)
                      tint) tbool))))
            (Sset _t'1 (Econst_int (Int.repr 0) tint)))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _middle_width tuint))
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _middle_width tuint))
            (Sset _t'2
              (Ecast
                (Ebinop Ole (Etempvar _t'6 tuint) (Etempvar _t'7 tuint) tint)
                tbool))))
        (Sset _t'2 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _last_line_width tuint))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _last_line_width tuint))
          (Sset _t'3
            (Ecast
              (Ebinop Ole (Etempvar _t'4 tuint) (Etempvar _t'5 tuint) tint)
              tbool))))
      (Sset _t'3 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'3 tint))))
|}.

Definition f_is_less_than := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tbool) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop One (Etempvar _t'6 tuint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _height tuint))
          (Sset _t'2
            (Ecast
              (Ebinop Oeq (Etempvar _t'7 tuint)
                (Econst_int (Int.repr 1) tint) tint) tbool)))
        (Sset _t'2 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Sset _t'3 (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _height tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _height tuint))
              (Sset _t'3
                (Ecast
                  (Ebinop One (Etempvar _t'5 tuint)
                    (Econst_int (Int.repr 1) tint) tint) tbool)))
            (Sset _t'3 (Ecast (Etempvar _t'3 tint) tbool)))
          (Sset _t'3 (Ecast (Econst_int (Int.repr 0) tint) tbool))))))
  (Sifthenelse (Etempvar _t'3 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar _less_components (Tfunction
                                 (Tcons (tptr (Tstruct _t noattr))
                                   (Tcons (tptr (Tstruct _t noattr)) Tnil))
                                 tbool cc_default))
        ((Etempvar _G (tptr (Tstruct _t noattr))) ::
         (Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
      (Sreturn (Some (Etempvar _t'1 tbool))))))
|}.

Definition f_empty := {|
  fn_return := (tptr (Tstruct _t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _t noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _t noattr) tulong) :: nil))
    (Sset _result (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _result (tptr (Tstruct _t noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _first_line_width tuint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _middle_width tuint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _last_line_width tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _to_text
                  (tptr (Tstruct _list noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (Sreturn (Some (Etempvar _result (tptr (Tstruct _t noattr))))))))))))
|}.

Definition f_line := {|
  fn_return := (tptr (Tstruct _t noattr));
  fn_callconv := cc_default;
  fn_params := ((_nt, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _t noattr))) ::
               (_t'5, (tptr tvoid)) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, (tptr tvoid)) ::
               (_t'9, (tptr (Tstruct _list noattr))) ::
               (_t'8, (tptr (Tstruct _list noattr))) ::
               (_t'7, (tptr (Tstruct _list noattr))) ::
               (_t'6, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _t noattr) tulong) :: nil))
    (Sset _result (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _result (tptr (Tstruct _t noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint)
        (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                            cc_default))
            ((Etempvar _nt (tptr tschar)) :: nil))
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint)
            (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                              cc_default))
              ((Etempvar _nt (tptr tschar)) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _middle_width tuint)
              (Etempvar _t'3 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                                cc_default))
                ((Etempvar _nt (tptr tschar)) :: nil))
              (Sassign
                (Efield
                  (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _last_line_width tuint)
                (Etempvar _t'4 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                  cc_default))
                  ((Esizeof (Tstruct _list noattr) tulong) :: nil))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _to_text
                    (tptr (Tstruct _list noattr)))
                  (Etempvar _t'5 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _to_text
                      (tptr (Tstruct _list noattr))))
                  (Sifthenelse (Eunop Onotbool
                                 (Etempvar _t'9 (tptr (Tstruct _list noattr)))
                                 tint)
                    (Scall None
                      (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                    cc_default))
                      ((Econst_int (Int.repr 1) tint) :: nil))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _to_text
                        (tptr (Tstruct _list noattr))))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _t'8 (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _shift tulong)
                      (Econst_int (Int.repr 0) tint)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _to_text
                          (tptr (Tstruct _list noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _t'7 (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _line (tptr tschar))
                        (Etempvar _nt (tptr tschar))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Efield
                            (Ederef
                              (Etempvar _result (tptr (Tstruct _t noattr)))
                              (Tstruct _t noattr)) _to_text
                            (tptr (Tstruct _list noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _t'6 (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _tail
                            (tptr (Tstruct _list noattr)))
                          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
                      (Sreturn (Some (Etempvar _result (tptr (Tstruct _t noattr))))))))))))))))
|}.

Definition v_newline := {|
  gvar_info := (tptr tschar);
  gvar_init := (Init_addrof ___stringlit_1 (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_format_copy := {|
  fn_return := (tptr (Tstruct _t noattr));
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _t noattr))) ::
               (_t'2, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr tvoid)) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _t noattr) tulong) :: nil))
    (Sset _result (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _result (tptr (Tstruct _t noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _height tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _height tuint) (Etempvar _t'7 tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint)
            (Etempvar _t'6 tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _middle_width tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _middle_width tuint)
              (Etempvar _t'5 tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _last_line_width tuint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _last_line_width tuint)
                (Etempvar _t'4 tuint)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _to_text
                      (tptr (Tstruct _list noattr))))
                  (Scall (Some _t'2)
                    (Evar _list_copy (Tfunction
                                       (Tcons (tptr (Tstruct _list noattr))
                                         Tnil) (tptr (Tstruct _list noattr))
                                       cc_default))
                    ((Etempvar _t'3 (tptr (Tstruct _list noattr))) :: nil)))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _to_text
                    (tptr (Tstruct _list noattr)))
                  (Etempvar _t'2 (tptr (Tstruct _list noattr)))))
              (Sreturn (Some (Etempvar _result (tptr (Tstruct _t noattr))))))))))))
|}.

Definition f_get_list_tail := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_cur, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _cur (Etempvar _l (tptr (Tstruct _list noattr))))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _cur (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Sifthenelse (Ebinop One
                         (Etempvar _t'1 (tptr (Tstruct _list noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            Sskip
            Sbreak))
        (Sset _cur
          (Efield
            (Ederef (Etempvar _cur (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))))
      Sskip)
    (Sreturn (Some (Etempvar _cur (tptr (Tstruct _list noattr)))))))
|}.

Definition f_list_concat := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_l1, (tptr (Tstruct _list noattr))) ::
                (_l2, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l1_tail, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_list_tail (Tfunction
                             (Tcons (tptr (Tstruct _list noattr)) Tnil)
                             (tptr (Tstruct _list noattr)) cc_default))
      ((Etempvar _l1 (tptr (Tstruct _list noattr))) :: nil))
    (Sset _l1_tail (Etempvar _t'1 (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _l1_tail (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
      (Etempvar _l2 (tptr (Tstruct _list noattr))))
    (Sreturn (Some (Etempvar _l1 (tptr (Tstruct _list noattr)))))))
|}.

Definition f_mdw_add_above := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_middle_width_new, tuint) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: (_t'37, tuint) ::
               (_t'36, tuint) :: (_t'35, tuint) :: (_t'34, tuint) ::
               (_t'33, tuint) :: (_t'32, tuint) :: (_t'31, tuint) ::
               (_t'30, tuint) :: (_t'29, tuint) :: (_t'28, tuint) ::
               (_t'27, tuint) :: (_t'26, tuint) :: (_t'25, tuint) ::
               (_t'24, tuint) :: (_t'23, tuint) :: (_t'22, tuint) ::
               (_t'21, tuint) :: (_t'20, tuint) :: (_t'19, tuint) ::
               (_t'18, tuint) :: (_t'17, tuint) :: (_t'16, tuint) ::
               (_t'15, tuint) :: (_t'14, tuint) :: (_t'13, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'36
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'36 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _t'37
          (Efield
            (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _middle_width tuint))
        (Sreturn (Some (Etempvar _t'37 tuint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'34
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'34 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sset _t'35
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _middle_width tuint))
          (Sreturn (Some (Etempvar _t'35 tuint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'32
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _height tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'32 tuint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Ssequence
              (Sset _t'33
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _height tuint))
              (Sset _t'12
                (Ecast
                  (Ebinop Oeq (Etempvar _t'33 tuint)
                    (Econst_int (Int.repr 1) tint) tint) tbool)))
            (Sset _t'12 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'12 tint)
          (Sset _middle_width_new
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint))
          (Ssequence
            (Ssequence
              (Sset _t'30
                (Efield
                  (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _height tuint))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'30 tuint)
                             (Econst_int (Int.repr 1) tint) tint)
                (Ssequence
                  (Sset _t'31
                    (Efield
                      (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _height tuint))
                  (Sset _t'11
                    (Ecast
                      (Ebinop One (Etempvar _t'31 tuint)
                        (Econst_int (Int.repr 1) tint) tint) tbool)))
                (Sset _t'11 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'11 tint)
              (Ssequence
                (Ssequence
                  (Sset _t'28
                    (Efield
                      (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _first_line_width tuint))
                  (Ssequence
                    (Sset _t'29
                      (Efield
                        (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _middle_width tuint))
                    (Scall (Some _t'1)
                      (Evar _max (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                   tuint cc_default))
                      ((Etempvar _t'28 tuint) :: (Etempvar _t'29 tuint) ::
                       nil))))
                (Sset _middle_width_new (Etempvar _t'1 tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'26
                    (Efield
                      (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _height tuint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'26 tuint)
                                 (Econst_int (Int.repr 2) tint) tint)
                    (Ssequence
                      (Sset _t'27
                        (Efield
                          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _height tuint))
                      (Sset _t'10
                        (Ecast
                          (Ebinop Oeq (Etempvar _t'27 tuint)
                            (Econst_int (Int.repr 1) tint) tint) tbool)))
                    (Sset _t'10 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'10 tint)
                  (Sset _middle_width_new
                    (Efield
                      (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _last_line_width tuint))
                  (Ssequence
                    (Ssequence
                      (Sset _t'24
                        (Efield
                          (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _height tuint))
                      (Sifthenelse (Ebinop One (Etempvar _t'24 tuint)
                                     (Econst_int (Int.repr 1) tint) tint)
                        (Ssequence
                          (Sset _t'25
                            (Efield
                              (Ederef
                                (Etempvar _F (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _height tuint))
                          (Sset _t'9
                            (Ecast
                              (Ebinop Oeq (Etempvar _t'25 tuint)
                                (Econst_int (Int.repr 1) tint) tint) tbool)))
                        (Sset _t'9 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'9 tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'22
                            (Efield
                              (Ederef
                                (Etempvar _G (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _last_line_width tuint))
                          (Ssequence
                            (Sset _t'23
                              (Efield
                                (Ederef
                                  (Etempvar _G (tptr (Tstruct _t noattr)))
                                  (Tstruct _t noattr)) _middle_width tuint))
                            (Scall (Some _t'2)
                              (Evar _max (Tfunction
                                           (Tcons tuint (Tcons tuint Tnil))
                                           tuint cc_default))
                              ((Etempvar _t'22 tuint) ::
                               (Etempvar _t'23 tuint) :: nil))))
                        (Sset _middle_width_new (Etempvar _t'2 tuint)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'20
                            (Efield
                              (Ederef
                                (Etempvar _G (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _height tuint))
                          (Sifthenelse (Ebinop Oeq (Etempvar _t'20 tuint)
                                         (Econst_int (Int.repr 2) tint) tint)
                            (Ssequence
                              (Sset _t'21
                                (Efield
                                  (Ederef
                                    (Etempvar _F (tptr (Tstruct _t noattr)))
                                    (Tstruct _t noattr)) _height tuint))
                              (Sset _t'8
                                (Ecast
                                  (Ebinop One (Etempvar _t'21 tuint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tbool)))
                            (Sset _t'8 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'8 tint)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'18
                                  (Efield
                                    (Ederef
                                      (Etempvar _F (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _first_line_width
                                    tuint))
                                (Ssequence
                                  (Sset _t'19
                                    (Efield
                                      (Ederef
                                        (Etempvar _F (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr)) _middle_width
                                      tuint))
                                  (Scall (Some _t'3)
                                    (Evar _max (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil)) tuint
                                                 cc_default))
                                    ((Etempvar _t'18 tuint) ::
                                     (Etempvar _t'19 tuint) :: nil))))
                              (Ssequence
                                (Sset _t'17
                                  (Efield
                                    (Ederef
                                      (Etempvar _G (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _last_line_width
                                    tuint))
                                (Scall (Some _t'4)
                                  (Evar _max (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint Tnil)) tuint
                                               cc_default))
                                  ((Etempvar _t'17 tuint) ::
                                   (Etempvar _t'3 tuint) :: nil))))
                            (Sset _middle_width_new (Etempvar _t'4 tuint)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'15
                                    (Efield
                                      (Ederef
                                        (Etempvar _F (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr))
                                      _first_line_width tuint))
                                  (Ssequence
                                    (Sset _t'16
                                      (Efield
                                        (Ederef
                                          (Etempvar _F (tptr (Tstruct _t noattr)))
                                          (Tstruct _t noattr)) _middle_width
                                        tuint))
                                    (Scall (Some _t'5)
                                      (Evar _max (Tfunction
                                                   (Tcons tuint
                                                     (Tcons tuint Tnil))
                                                   tuint cc_default))
                                      ((Etempvar _t'15 tuint) ::
                                       (Etempvar _t'16 tuint) :: nil))))
                                (Ssequence
                                  (Sset _t'14
                                    (Efield
                                      (Ederef
                                        (Etempvar _G (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr)) _last_line_width
                                      tuint))
                                  (Scall (Some _t'6)
                                    (Evar _max (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil)) tuint
                                                 cc_default))
                                    ((Etempvar _t'14 tuint) ::
                                     (Etempvar _t'5 tuint) :: nil))))
                              (Ssequence
                                (Sset _t'13
                                  (Efield
                                    (Ederef
                                      (Etempvar _G (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _middle_width
                                    tuint))
                                (Scall (Some _t'7)
                                  (Evar _max (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint Tnil)) tuint
                                               cc_default))
                                  ((Etempvar _t'13 tuint) ::
                                   (Etempvar _t'6 tuint) :: nil))))
                            (Sset _middle_width_new (Etempvar _t'7 tuint)))))))))))))
      (Sreturn (Some (Etempvar _middle_width_new tuint))))))
|}.

Definition f_to_text_add_above := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_to_text_head, (tptr (Tstruct _list noattr))) ::
               (_t'5, (tptr (Tstruct _list noattr))) ::
               (_t'4, (tptr (Tstruct _list noattr))) ::
               (_t'3, (tptr (Tstruct _list noattr))) ::
               (_t'2, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) ::
               (_t'11, (tptr (Tstruct _list noattr))) :: (_t'10, tuint) ::
               (_t'9, (tptr (Tstruct _list noattr))) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct _list noattr))) ::
               (_t'6, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'10
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _to_text (tptr (Tstruct _list noattr))))
          (Scall (Some _t'1)
            (Evar _list_copy (Tfunction
                               (Tcons (tptr (Tstruct _list noattr)) Tnil)
                               (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _t'11 (tptr (Tstruct _list noattr))) :: nil)))
        (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _list noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _to_text
                (tptr (Tstruct _list noattr))))
            (Scall (Some _t'2)
              (Evar _list_copy (Tfunction
                                 (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                 (tptr (Tstruct _list noattr)) cc_default))
              ((Etempvar _t'9 (tptr (Tstruct _list noattr))) :: nil)))
          (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _list noattr))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _to_text
                  (tptr (Tstruct _list noattr))))
              (Scall (Some _t'3)
                (Evar _list_copy (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                   (tptr (Tstruct _list noattr)) cc_default))
                ((Etempvar _t'7 (tptr (Tstruct _list noattr))) :: nil)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _to_text
                  (tptr (Tstruct _list noattr))))
              (Scall (Some _t'4)
                (Evar _list_copy (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                   (tptr (Tstruct _list noattr)) cc_default))
                ((Etempvar _t'6 (tptr (Tstruct _list noattr))) :: nil))))
          (Scall (Some _t'5)
            (Evar _list_concat (Tfunction
                                 (Tcons (tptr (Tstruct _list noattr))
                                   (Tcons (tptr (Tstruct _list noattr)) Tnil))
                                 (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _t'3 (tptr (Tstruct _list noattr))) ::
             (Etempvar _t'4 (tptr (Tstruct _list noattr))) :: nil)))
        (Sset _to_text_head (Etempvar _t'5 (tptr (Tstruct _list noattr)))))
      (Sreturn (Some (Etempvar _to_text_head (tptr (Tstruct _list noattr))))))))
|}.

Definition f_add_above := {|
  fn_return := (tptr (Tstruct _t noattr));
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _t noattr))) ::
               (_middle_width_new, tuint) ::
               (_to_text_new, (tptr (Tstruct _list noattr))) ::
               (_t'5, (tptr (Tstruct _list noattr))) :: (_t'4, tuint) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr (Tstruct _t noattr))) ::
               (_t'1, (tptr (Tstruct _t noattr))) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'11
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'11 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _format_copy (Tfunction
                               (Tcons (tptr (Tstruct _t noattr)) Tnil)
                               (tptr (Tstruct _t noattr)) cc_default))
          ((Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
        (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _t noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _format_copy (Tfunction
                                 (Tcons (tptr (Tstruct _t noattr)) Tnil)
                                 (tptr (Tstruct _t noattr)) cc_default))
            ((Etempvar _G (tptr (Tstruct _t noattr))) :: nil))
          (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _t noattr))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _t noattr) tulong) :: nil))
        (Sset _result (Etempvar _t'3 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Eunop Onotbool
                       (Etempvar _result (tptr (Tstruct _t noattr))) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _mdw_add_above (Tfunction
                                     (Tcons (tptr (Tstruct _t noattr))
                                       (Tcons (tptr (Tstruct _t noattr))
                                         Tnil)) tuint cc_default))
              ((Etempvar _G (tptr (Tstruct _t noattr))) ::
               (Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
            (Sset _middle_width_new (Etempvar _t'4 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _to_text_add_above (Tfunction
                                           (Tcons (tptr (Tstruct _t noattr))
                                             (Tcons
                                               (tptr (Tstruct _t noattr))
                                               Tnil))
                                           (tptr (Tstruct _list noattr))
                                           cc_default))
                ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                 (Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
              (Sset _to_text_new
                (Etempvar _t'5 (tptr (Tstruct _list noattr)))))
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _height tuint))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _height tuint))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _height tuint)
                    (Ebinop Oadd (Etempvar _t'8 tuint) (Etempvar _t'9 tuint)
                      tuint))))
              (Ssequence
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _first_line_width tuint))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _first_line_width tuint)
                    (Etempvar _t'7 tuint)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _middle_width tuint)
                    (Etempvar _middle_width_new tuint))
                  (Ssequence
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _last_line_width tuint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _last_line_width tuint)
                        (Etempvar _t'6 tuint)))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _to_text
                          (tptr (Tstruct _list noattr)))
                        (Etempvar _to_text_new (tptr (Tstruct _list noattr))))
                      (Sreturn (Some (Etempvar _result (tptr (Tstruct _t noattr))))))))))))))))
|}.

Definition f_mdw_add_beside := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_middle_width_new, tuint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               (_t'31, tuint) :: (_t'30, tuint) :: (_t'29, tuint) ::
               (_t'28, tuint) :: (_t'27, tuint) :: (_t'26, tuint) ::
               (_t'25, tuint) :: (_t'24, tuint) :: (_t'23, tuint) ::
               (_t'22, tuint) :: (_t'21, tuint) :: (_t'20, tuint) ::
               (_t'19, tuint) :: (_t'18, tuint) :: (_t'17, tuint) ::
               (_t'16, tuint) :: (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, tuint) :: (_t'12, tuint) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'30
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'30 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _t'31
          (Efield
            (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _middle_width tuint))
        (Sreturn (Some (Etempvar _t'31 tuint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'28
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'28 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sset _t'29
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _middle_width tuint))
          (Sreturn (Some (Etempvar _t'29 tuint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'26
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _height tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'26 tuint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Ssequence
              (Sset _t'27
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _height tuint))
              (Sset _t'5
                (Ecast
                  (Ebinop Oeq (Etempvar _t'27 tuint)
                    (Econst_int (Int.repr 1) tint) tint) tbool)))
            (Sset _t'5 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'5 tint)
          (Ssequence
            (Sset _t'24
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _first_line_width tuint))
            (Ssequence
              (Sset _t'25
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _first_line_width tuint))
              (Sset _middle_width_new
                (Ebinop Oadd (Etempvar _t'24 tuint) (Etempvar _t'25 tuint)
                  tuint))))
          (Ssequence
            (Ssequence
              (Sset _t'22
                (Efield
                  (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _height tuint))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'22 tuint)
                             (Econst_int (Int.repr 1) tint) tint)
                (Ssequence
                  (Sset _t'23
                    (Efield
                      (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _height tuint))
                  (Sset _t'4
                    (Ecast
                      (Ebinop Oeq (Etempvar _t'23 tuint)
                        (Econst_int (Int.repr 2) tint) tint) tbool)))
                (Sset _t'4 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Sset _t'20
                  (Efield
                    (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _first_line_width tuint))
                (Ssequence
                  (Sset _t'21
                    (Efield
                      (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _first_line_width tuint))
                  (Sset _middle_width_new
                    (Ebinop Oadd (Etempvar _t'20 tuint)
                      (Etempvar _t'21 tuint) tuint))))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _height tuint))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                               (Econst_int (Int.repr 1) tint) tint)
                  (Sset _middle_width_new
                    (Efield
                      (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _middle_width tuint))
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _height tuint))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      (Ssequence
                        (Sset _t'18
                          (Efield
                            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                              (Tstruct _t noattr)) _last_line_width tuint))
                        (Ssequence
                          (Sset _t'19
                            (Efield
                              (Ederef
                                (Etempvar _F (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _middle_width tuint))
                          (Sset _middle_width_new
                            (Ebinop Oadd (Etempvar _t'18 tuint)
                              (Etempvar _t'19 tuint) tuint))))
                      (Ssequence
                        (Sset _t'8
                          (Efield
                            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                              (Tstruct _t noattr)) _height tuint))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                                       (Econst_int (Int.repr 2) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'14
                                (Efield
                                  (Ederef
                                    (Etempvar _G (tptr (Tstruct _t noattr)))
                                    (Tstruct _t noattr)) _last_line_width
                                  tuint))
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _F (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _first_line_width
                                    tuint))
                                (Ssequence
                                  (Sset _t'16
                                    (Efield
                                      (Ederef
                                        (Etempvar _G (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr)) _last_line_width
                                      tuint))
                                  (Ssequence
                                    (Sset _t'17
                                      (Efield
                                        (Ederef
                                          (Etempvar _F (tptr (Tstruct _t noattr)))
                                          (Tstruct _t noattr)) _middle_width
                                        tuint))
                                    (Scall (Some _t'1)
                                      (Evar _max (Tfunction
                                                   (Tcons tuint
                                                     (Tcons tuint Tnil))
                                                   tuint cc_default))
                                      ((Ebinop Oadd (Etempvar _t'14 tuint)
                                         (Etempvar _t'15 tuint) tuint) ::
                                       (Ebinop Oadd (Etempvar _t'16 tuint)
                                         (Etempvar _t'17 tuint) tuint) ::
                                       nil))))))
                            (Sset _middle_width_new (Etempvar _t'1 tuint)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Ederef
                                      (Etempvar _G (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _last_line_width
                                    tuint))
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _F (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr))
                                      _first_line_width tuint))
                                  (Ssequence
                                    (Sset _t'12
                                      (Efield
                                        (Ederef
                                          (Etempvar _G (tptr (Tstruct _t noattr)))
                                          (Tstruct _t noattr))
                                        _last_line_width tuint))
                                    (Ssequence
                                      (Sset _t'13
                                        (Efield
                                          (Ederef
                                            (Etempvar _F (tptr (Tstruct _t noattr)))
                                            (Tstruct _t noattr))
                                          _middle_width tuint))
                                      (Scall (Some _t'2)
                                        (Evar _max (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tuint Tnil))
                                                     tuint cc_default))
                                        ((Ebinop Oadd (Etempvar _t'10 tuint)
                                           (Etempvar _t'11 tuint) tuint) ::
                                         (Ebinop Oadd (Etempvar _t'12 tuint)
                                           (Etempvar _t'13 tuint) tuint) ::
                                         nil))))))
                              (Ssequence
                                (Sset _t'9
                                  (Efield
                                    (Ederef
                                      (Etempvar _G (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _middle_width
                                    tuint))
                                (Scall (Some _t'3)
                                  (Evar _max (Tfunction
                                               (Tcons tuint
                                                 (Tcons tuint Tnil)) tuint
                                               cc_default))
                                  ((Etempvar _t'9 tuint) ::
                                   (Etempvar _t'2 tuint) :: nil))))
                            (Sset _middle_width_new (Etempvar _t'3 tuint)))))))))))))
      (Sreturn (Some (Etempvar _middle_width_new tuint))))))
|}.

Definition f_flw_add_beside := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_first_line_width_new, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _first_line_width tuint))
        (Sreturn (Some (Etempvar _t'7 tuint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint))
          (Sreturn (Some (Etempvar _t'5 tuint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _height tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _first_line_width tuint))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _first_line_width tuint))
              (Sset _first_line_width_new
                (Ebinop Oadd (Etempvar _t'2 tuint) (Etempvar _t'3 tuint)
                  tuint))))
          (Sset _first_line_width_new
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint))))
      (Sreturn (Some (Etempvar _first_line_width_new tuint))))))
|}.

Definition f_line_concats := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_l1, (tptr tschar)) :: (_n, tulong) ::
                (_l2, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_line, (tptr tschar)) :: (_shifted, (tptr tschar)) ::
               (_t'7, (tptr tschar)) :: (_t'6, (tptr tschar)) ::
               (_t'5, (tptr tschar)) :: (_t'4, (tptr tschar)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, tulong) :: (_t'1, tulong) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                          cc_default)) ((Etempvar _l1 (tptr tschar)) :: nil))
        (Scall (Some _t'2)
          (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                          cc_default)) ((Etempvar _l2 (tptr tschar)) :: nil)))
      (Scall (Some _t'3)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Ebinop Oadd
           (Ebinop Oadd
             (Ebinop Oadd (Etempvar _t'1 tulong) (Etempvar _n tulong) tulong)
             (Etempvar _t'2 tulong) tulong) (Econst_int (Int.repr 1) tint)
           tulong) :: nil)))
    (Sset _new_line (Etempvar _t'3 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _new_line (tptr tschar)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _new_line (tptr tschar))
            (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _sp (Tfunction (Tcons tulong Tnil) (tptr tschar)
                        cc_default)) ((Etempvar _n tulong) :: nil))
          (Sset _shifted (Etempvar _t'4 (tptr tschar))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _strcat (Tfunction
                              (Tcons (tptr tschar)
                                (Tcons (tptr tschar) Tnil)) (tptr tschar)
                              cc_default))
              ((Etempvar _new_line (tptr tschar)) ::
               (Etempvar _l1 (tptr tschar)) :: nil))
            (Sset _new_line (Etempvar _t'5 (tptr tschar))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _strcat (Tfunction
                                (Tcons (tptr tschar)
                                  (Tcons (tptr tschar) Tnil)) (tptr tschar)
                                cc_default))
                ((Etempvar _new_line (tptr tschar)) ::
                 (Etempvar _shifted (tptr tschar)) :: nil))
              (Sset _new_line (Etempvar _t'6 (tptr tschar))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _strcat (Tfunction
                                  (Tcons (tptr tschar)
                                    (Tcons (tptr tschar) Tnil)) (tptr tschar)
                                  cc_default))
                  ((Etempvar _new_line (tptr tschar)) ::
                   (Etempvar _l2 (tptr tschar)) :: nil))
                (Sset _new_line (Etempvar _t'7 (tptr tschar))))
              (Ssequence
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _l1 (tptr tschar)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _shifted (tptr tschar)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                      ((Etempvar _l2 (tptr tschar)) :: nil))
                    (Sreturn (Some (Etempvar _new_line (tptr tschar))))))))))))))
|}.

Definition f_shift_list := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_sigma, (tptr (Tstruct _list noattr))) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_cur_sigma, (tptr (Tstruct _list noattr))) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _cur_sigma (Etempvar _sigma (tptr (Tstruct _list noattr))))
  (Ssequence
    (Swhile
      (Ebinop One (Etempvar _cur_sigma (tptr (Tstruct _list noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _cur_sigma (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _shift tulong))
          (Sassign
            (Efield
              (Ederef (Etempvar _cur_sigma (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _shift tulong)
            (Ebinop Oadd (Etempvar _t'1 tulong) (Etempvar _n tulong) tulong)))
        (Sset _cur_sigma
          (Efield
            (Ederef (Etempvar _cur_sigma (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))))
    (Sreturn (Some (Etempvar _sigma (tptr (Tstruct _list noattr)))))))
|}.

Definition f_to_text_add_beside := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_head, (tptr (Tstruct _list noattr))) ::
               (_tail, (tptr (Tstruct _list noattr))) ::
               (_copy_F, (tptr (Tstruct _list noattr))) ::
               (_t'6, (tptr tschar)) ::
               (_t'5, (tptr (Tstruct _list noattr))) ::
               (_t'4, (tptr (Tstruct _list noattr))) ::
               (_t'3, (tptr (Tstruct _list noattr))) ::
               (_t'2, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) ::
               (_t'18, (tptr (Tstruct _list noattr))) :: (_t'17, tuint) ::
               (_t'16, (tptr (Tstruct _list noattr))) :: (_t'15, tuint) ::
               (_t'14, (tptr (Tstruct _list noattr))) ::
               (_t'13, (tptr (Tstruct _list noattr))) ::
               (_t'12, (tptr tschar)) :: (_t'11, tulong) ::
               (_t'10, (tptr tschar)) :: (_t'9, tuint) ::
               (_t'8, (tptr (Tstruct _list noattr))) ::
               (_t'7, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'17
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'17 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'18
            (Efield
              (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _to_text (tptr (Tstruct _list noattr))))
          (Scall (Some _t'1)
            (Evar _list_copy (Tfunction
                               (Tcons (tptr (Tstruct _list noattr)) Tnil)
                               (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _t'18 (tptr (Tstruct _list noattr))) :: nil)))
        (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _list noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'15
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'15 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'16
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _to_text
                (tptr (Tstruct _list noattr))))
            (Scall (Some _t'2)
              (Evar _list_copy (Tfunction
                                 (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                 (tptr (Tstruct _list noattr)) cc_default))
              ((Etempvar _t'16 (tptr (Tstruct _list noattr))) :: nil)))
          (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _list noattr))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'14
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _to_text (tptr (Tstruct _list noattr))))
          (Scall (Some _t'3)
            (Evar _list_copy (Tfunction
                               (Tcons (tptr (Tstruct _list noattr)) Tnil)
                               (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _t'14 (tptr (Tstruct _list noattr))) :: nil)))
        (Sset _head (Etempvar _t'3 (tptr (Tstruct _list noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_list_tail (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                   (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _head (tptr (Tstruct _list noattr))) :: nil))
          (Sset _tail (Etempvar _t'4 (tptr (Tstruct _list noattr)))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'13
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _to_text
                  (tptr (Tstruct _list noattr))))
              (Scall (Some _t'5)
                (Evar _list_copy (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                   (tptr (Tstruct _list noattr)) cc_default))
                ((Etempvar _t'13 (tptr (Tstruct _list noattr))) :: nil)))
            (Sset _copy_F (Etempvar _t'5 (tptr (Tstruct _list noattr)))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef (Etempvar _tail (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _line (tptr tschar)))
                (Ssequence
                  (Sset _t'11
                    (Efield
                      (Ederef
                        (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _shift tulong))
                  (Ssequence
                    (Sset _t'12
                      (Efield
                        (Ederef
                          (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _line (tptr tschar)))
                    (Scall (Some _t'6)
                      (Evar _line_concats (Tfunction
                                            (Tcons (tptr tschar)
                                              (Tcons tulong
                                                (Tcons (tptr tschar) Tnil)))
                                            (tptr tschar) cc_default))
                      ((Etempvar _t'10 (tptr tschar)) ::
                       (Etempvar _t'11 tulong) ::
                       (Etempvar _t'12 (tptr tschar)) :: nil)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _tail (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _line (tptr tschar))
                (Etempvar _t'6 (tptr tschar))))
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _list noattr))))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _last_line_width tuint))
                  (Scall None
                    (Evar _shift_list (Tfunction
                                        (Tcons (tptr (Tstruct _list noattr))
                                          (Tcons tulong Tnil))
                                        (tptr (Tstruct _list noattr))
                                        cc_default))
                    ((Etempvar _t'8 (tptr (Tstruct _list noattr))) ::
                     (Etempvar _t'9 tuint) :: nil))))
              (Ssequence
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _tail
                      (tptr (Tstruct _list noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _tail (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _tail
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _t'7 (tptr (Tstruct _list noattr)))))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _copy_F (tptr (Tstruct _list noattr))) :: nil))
                  (Sreturn (Some (Etempvar _head (tptr (Tstruct _list noattr))))))))))))))
|}.

Definition f_add_beside := {|
  fn_return := (tptr (Tstruct _t noattr));
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _t noattr))) ::
               (_middle_width_new, tuint) ::
               (_first_line_width_new, tuint) ::
               (_to_text_new, (tptr (Tstruct _list noattr))) ::
               (_t'6, (tptr (Tstruct _list noattr))) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _t noattr))) ::
               (_t'1, (tptr (Tstruct _t noattr))) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'12
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'12 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _format_copy (Tfunction
                               (Tcons (tptr (Tstruct _t noattr)) Tnil)
                               (tptr (Tstruct _t noattr)) cc_default))
          ((Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
        (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _t noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'11 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _format_copy (Tfunction
                                 (Tcons (tptr (Tstruct _t noattr)) Tnil)
                                 (tptr (Tstruct _t noattr)) cc_default))
            ((Etempvar _G (tptr (Tstruct _t noattr))) :: nil))
          (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _t noattr))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _t noattr) tulong) :: nil))
        (Sset _result (Etempvar _t'3 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Eunop Onotbool
                       (Etempvar _result (tptr (Tstruct _t noattr))) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _mdw_add_beside (Tfunction
                                      (Tcons (tptr (Tstruct _t noattr))
                                        (Tcons (tptr (Tstruct _t noattr))
                                          Tnil)) tuint cc_default))
              ((Etempvar _G (tptr (Tstruct _t noattr))) ::
               (Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
            (Sset _middle_width_new (Etempvar _t'4 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _flw_add_beside (Tfunction
                                        (Tcons (tptr (Tstruct _t noattr))
                                          (Tcons (tptr (Tstruct _t noattr))
                                            Tnil)) tuint cc_default))
                ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                 (Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
              (Sset _first_line_width_new (Etempvar _t'5 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _to_text_add_beside (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _t noattr))
                                                (Tcons
                                                  (tptr (Tstruct _t noattr))
                                                  Tnil))
                                              (tptr (Tstruct _list noattr))
                                              cc_default))
                  ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                   (Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
                (Sset _to_text_new
                  (Etempvar _t'6 (tptr (Tstruct _list noattr)))))
              (Ssequence
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _height tuint))
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _height tuint))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _height tuint)
                      (Ebinop Osub
                        (Ebinop Oadd (Etempvar _t'9 tuint)
                          (Etempvar _t'10 tuint) tuint)
                        (Econst_int (Int.repr 1) tint) tuint))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _first_line_width tuint)
                    (Etempvar _first_line_width_new tuint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _middle_width tuint)
                      (Etempvar _middle_width_new tuint))
                    (Ssequence
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                              (Tstruct _t noattr)) _last_line_width tuint))
                        (Ssequence
                          (Sset _t'8
                            (Efield
                              (Ederef
                                (Etempvar _F (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _last_line_width tuint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _result (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _last_line_width tuint)
                            (Ebinop Oadd (Etempvar _t'7 tuint)
                              (Etempvar _t'8 tuint) tuint))))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _result (tptr (Tstruct _t noattr)))
                              (Tstruct _t noattr)) _to_text
                            (tptr (Tstruct _list noattr)))
                          (Etempvar _to_text_new (tptr (Tstruct _list noattr))))
                        (Sreturn (Some (Etempvar _result (tptr (Tstruct _t noattr)))))))))))))))))
|}.

Definition f_mdw_add_fill := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: (_shift, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_middle_width_new, tuint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               (_t'41, tuint) :: (_t'40, tuint) :: (_t'39, tuint) ::
               (_t'38, tuint) :: (_t'37, tuint) :: (_t'36, tuint) ::
               (_t'35, tuint) :: (_t'34, tuint) :: (_t'33, tuint) ::
               (_t'32, tuint) :: (_t'31, tuint) :: (_t'30, tuint) ::
               (_t'29, tuint) :: (_t'28, tuint) :: (_t'27, tuint) ::
               (_t'26, tuint) :: (_t'25, tuint) :: (_t'24, tuint) ::
               (_t'23, tuint) :: (_t'22, tuint) :: (_t'21, tuint) ::
               (_t'20, tuint) :: (_t'19, tuint) :: (_t'18, tuint) ::
               (_t'17, tuint) :: (_t'16, tuint) :: (_t'15, tuint) ::
               (_t'14, tuint) :: (_t'13, tuint) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'40
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'40 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _t'41
          (Efield
            (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _middle_width tuint))
        (Sreturn (Some (Etempvar _t'41 tuint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'38
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'38 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sset _t'39
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _middle_width tuint))
          (Sreturn (Some (Etempvar _t'39 tuint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'36
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _height tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'36 tuint)
                         (Econst_int (Int.repr 1) tint) tint)
            (Ssequence
              (Sset _t'37
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _height tuint))
              (Sset _t'8
                (Ecast
                  (Ebinop Oeq (Etempvar _t'37 tuint)
                    (Econst_int (Int.repr 1) tint) tint) tbool)))
            (Sset _t'8 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'8 tint)
          (Ssequence
            (Sset _t'34
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _first_line_width tuint))
            (Ssequence
              (Sset _t'35
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _first_line_width tuint))
              (Sset _middle_width_new
                (Ebinop Oadd (Etempvar _t'34 tuint) (Etempvar _t'35 tuint)
                  tuint))))
          (Ssequence
            (Ssequence
              (Sset _t'32
                (Efield
                  (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _height tuint))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'32 tuint)
                             (Econst_int (Int.repr 1) tint) tint)
                (Ssequence
                  (Sset _t'33
                    (Efield
                      (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _height tuint))
                  (Sset _t'7
                    (Ecast
                      (Ebinop Oeq (Etempvar _t'33 tuint)
                        (Econst_int (Int.repr 2) tint) tint) tbool)))
                (Sset _t'7 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'7 tint)
              (Ssequence
                (Sset _t'30
                  (Efield
                    (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _first_line_width tuint))
                (Ssequence
                  (Sset _t'31
                    (Efield
                      (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _first_line_width tuint))
                  (Sset _middle_width_new
                    (Ebinop Oadd (Etempvar _t'30 tuint)
                      (Etempvar _t'31 tuint) tuint))))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _height tuint))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'9 tuint)
                               (Econst_int (Int.repr 1) tint) tint)
                  (Ssequence
                    (Sset _t'29
                      (Efield
                        (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _middle_width tuint))
                    (Sset _middle_width_new
                      (Ecast
                        (Ebinop Oadd (Etempvar _shift tulong)
                          (Etempvar _t'29 tuint) tulong) tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'27
                        (Efield
                          (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _height tuint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'27 tuint)
                                     (Econst_int (Int.repr 2) tint) tint)
                        (Ssequence
                          (Sset _t'28
                            (Efield
                              (Ederef
                                (Etempvar _F (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _height tuint))
                          (Sset _t'6
                            (Ecast
                              (Ebinop Oeq (Etempvar _t'28 tuint)
                                (Econst_int (Int.repr 1) tint) tint) tbool)))
                        (Sset _t'6 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'6 tint)
                      (Sset _middle_width_new
                        (Efield
                          (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _first_line_width tuint))
                      (Ssequence
                        (Ssequence
                          (Sset _t'25
                            (Efield
                              (Ederef
                                (Etempvar _G (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _height tuint))
                          (Sifthenelse (Ebinop Oeq (Etempvar _t'25 tuint)
                                         (Econst_int (Int.repr 2) tint) tint)
                            (Ssequence
                              (Sset _t'26
                                (Efield
                                  (Ederef
                                    (Etempvar _F (tptr (Tstruct _t noattr)))
                                    (Tstruct _t noattr)) _height tuint))
                              (Sset _t'5
                                (Ecast
                                  (Ebinop Oeq (Etempvar _t'26 tuint)
                                    (Econst_int (Int.repr 2) tint) tint)
                                  tbool)))
                            (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Ssequence
                            (Sset _t'23
                              (Efield
                                (Ederef
                                  (Etempvar _G (tptr (Tstruct _t noattr)))
                                  (Tstruct _t noattr)) _last_line_width
                                tuint))
                            (Ssequence
                              (Sset _t'24
                                (Efield
                                  (Ederef
                                    (Etempvar _F (tptr (Tstruct _t noattr)))
                                    (Tstruct _t noattr)) _first_line_width
                                  tuint))
                              (Sset _middle_width_new
                                (Ebinop Oadd (Etempvar _t'23 tuint)
                                  (Etempvar _t'24 tuint) tuint))))
                          (Ssequence
                            (Sset _t'10
                              (Efield
                                (Ederef
                                  (Etempvar _G (tptr (Tstruct _t noattr)))
                                  (Tstruct _t noattr)) _height tuint))
                            (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tuint)
                                           (Econst_int (Int.repr 2) tint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'20
                                    (Efield
                                      (Ederef
                                        (Etempvar _G (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr)) _last_line_width
                                      tuint))
                                  (Ssequence
                                    (Sset _t'21
                                      (Efield
                                        (Ederef
                                          (Etempvar _F (tptr (Tstruct _t noattr)))
                                          (Tstruct _t noattr))
                                        _first_line_width tuint))
                                    (Ssequence
                                      (Sset _t'22
                                        (Efield
                                          (Ederef
                                            (Etempvar _F (tptr (Tstruct _t noattr)))
                                            (Tstruct _t noattr))
                                          _middle_width tuint))
                                      (Scall (Some _t'1)
                                        (Evar _max (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tuint Tnil))
                                                     tuint cc_default))
                                        ((Ebinop Oadd (Etempvar _t'20 tuint)
                                           (Etempvar _t'21 tuint) tuint) ::
                                         (Ebinop Oadd
                                           (Etempvar _shift tulong)
                                           (Etempvar _t'22 tuint) tulong) ::
                                         nil)))))
                                (Sset _middle_width_new
                                  (Etempvar _t'1 tuint)))
                              (Ssequence
                                (Sset _t'11
                                  (Efield
                                    (Ederef
                                      (Etempvar _F (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _height tuint))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'11 tuint)
                                               (Econst_int (Int.repr 1) tint)
                                               tint)
                                  (Sset _middle_width_new
                                    (Efield
                                      (Ederef
                                        (Etempvar _G (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr)) _middle_width
                                      tuint))
                                  (Ssequence
                                    (Sset _t'12
                                      (Efield
                                        (Ederef
                                          (Etempvar _F (tptr (Tstruct _t noattr)))
                                          (Tstruct _t noattr)) _height tuint))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'12 tuint)
                                                   (Econst_int (Int.repr 2) tint)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'17
                                            (Efield
                                              (Ederef
                                                (Etempvar _G (tptr (Tstruct _t noattr)))
                                                (Tstruct _t noattr))
                                              _middle_width tuint))
                                          (Ssequence
                                            (Sset _t'18
                                              (Efield
                                                (Ederef
                                                  (Etempvar _G (tptr (Tstruct _t noattr)))
                                                  (Tstruct _t noattr))
                                                _last_line_width tuint))
                                            (Ssequence
                                              (Sset _t'19
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _F (tptr (Tstruct _t noattr)))
                                                    (Tstruct _t noattr))
                                                  _first_line_width tuint))
                                              (Scall (Some _t'2)
                                                (Evar _max (Tfunction
                                                             (Tcons tuint
                                                               (Tcons tuint
                                                                 Tnil)) tuint
                                                             cc_default))
                                                ((Etempvar _t'17 tuint) ::
                                                 (Ebinop Oadd
                                                   (Etempvar _t'18 tuint)
                                                   (Etempvar _t'19 tuint)
                                                   tuint) :: nil)))))
                                        (Sset _middle_width_new
                                          (Etempvar _t'2 tuint)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'14
                                              (Efield
                                                (Ederef
                                                  (Etempvar _G (tptr (Tstruct _t noattr)))
                                                  (Tstruct _t noattr))
                                                _last_line_width tuint))
                                            (Ssequence
                                              (Sset _t'15
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _F (tptr (Tstruct _t noattr)))
                                                    (Tstruct _t noattr))
                                                  _first_line_width tuint))
                                              (Ssequence
                                                (Sset _t'16
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _F (tptr (Tstruct _t noattr)))
                                                      (Tstruct _t noattr))
                                                    _middle_width tuint))
                                                (Scall (Some _t'3)
                                                  (Evar _max (Tfunction
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   Tnil))
                                                               tuint
                                                               cc_default))
                                                  ((Ebinop Oadd
                                                     (Etempvar _t'14 tuint)
                                                     (Etempvar _t'15 tuint)
                                                     tuint) ::
                                                   (Ebinop Oadd
                                                     (Etempvar _shift tulong)
                                                     (Etempvar _t'16 tuint)
                                                     tulong) :: nil)))))
                                          (Ssequence
                                            (Sset _t'13
                                              (Efield
                                                (Ederef
                                                  (Etempvar _G (tptr (Tstruct _t noattr)))
                                                  (Tstruct _t noattr))
                                                _middle_width tuint))
                                            (Scall (Some _t'4)
                                              (Evar _max (Tfunction
                                                           (Tcons tuint
                                                             (Tcons tuint
                                                               Tnil)) tuint
                                                           cc_default))
                                              ((Etempvar _t'13 tuint) ::
                                               (Etempvar _t'3 tuint) :: nil))))
                                        (Sset _middle_width_new
                                          (Etempvar _t'4 tuint)))))))))))))))))))
      (Sreturn (Some (Etempvar _middle_width_new tuint))))))
|}.

Definition f_llw_add_fill := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: (_shift, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_last_line_width_new, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'7
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _last_line_width tuint))
        (Sreturn (Some (Etempvar _t'8 tuint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _last_line_width tuint))
          (Sreturn (Some (Etempvar _t'6 tuint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _height tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _last_line_width tuint))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _last_line_width tuint))
              (Sset _last_line_width_new
                (Ebinop Oadd (Etempvar _t'3 tuint) (Etempvar _t'4 tuint)
                  tuint))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _last_line_width tuint))
            (Sset _last_line_width_new
              (Ecast
                (Ebinop Oadd (Etempvar _t'2 tuint) (Etempvar _shift tulong)
                  tulong) tuint)))))
      (Sreturn (Some (Etempvar _last_line_width_new tuint))))))
|}.

Definition f_flw_add_fill := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_first_line_width_new, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _first_line_width tuint))
        (Sreturn (Some (Etempvar _t'7 tuint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint))
          (Sreturn (Some (Etempvar _t'5 tuint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _height tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _first_line_width tuint))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _first_line_width tuint))
              (Sset _first_line_width_new
                (Ebinop Oadd (Etempvar _t'2 tuint) (Etempvar _t'3 tuint)
                  tuint))))
          (Sset _first_line_width_new
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _first_line_width tuint))))
      (Sreturn (Some (Etempvar _first_line_width_new tuint))))))
|}.

Definition f_to_text_add_fill := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: (_shift, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_head, (tptr (Tstruct _list noattr))) ::
               (_tail, (tptr (Tstruct _list noattr))) ::
               (_copy_F, (tptr (Tstruct _list noattr))) ::
               (_t'6, (tptr tschar)) ::
               (_t'5, (tptr (Tstruct _list noattr))) ::
               (_t'4, (tptr (Tstruct _list noattr))) ::
               (_t'3, (tptr (Tstruct _list noattr))) ::
               (_t'2, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) ::
               (_t'17, (tptr (Tstruct _list noattr))) :: (_t'16, tuint) ::
               (_t'15, (tptr (Tstruct _list noattr))) :: (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct _list noattr))) ::
               (_t'12, (tptr (Tstruct _list noattr))) ::
               (_t'11, (tptr tschar)) :: (_t'10, tulong) ::
               (_t'9, (tptr tschar)) ::
               (_t'8, (tptr (Tstruct _list noattr))) ::
               (_t'7, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'16
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'16 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'17
            (Efield
              (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _to_text (tptr (Tstruct _list noattr))))
          (Scall (Some _t'1)
            (Evar _list_copy (Tfunction
                               (Tcons (tptr (Tstruct _list noattr)) Tnil)
                               (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _t'17 (tptr (Tstruct _list noattr))) :: nil)))
        (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _list noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'14
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'14 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'15
              (Efield
                (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _to_text
                (tptr (Tstruct _list noattr))))
            (Scall (Some _t'2)
              (Evar _list_copy (Tfunction
                                 (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                 (tptr (Tstruct _list noattr)) cc_default))
              ((Etempvar _t'15 (tptr (Tstruct _list noattr))) :: nil)))
          (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _list noattr))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _to_text (tptr (Tstruct _list noattr))))
          (Scall (Some _t'3)
            (Evar _list_copy (Tfunction
                               (Tcons (tptr (Tstruct _list noattr)) Tnil)
                               (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _t'13 (tptr (Tstruct _list noattr))) :: nil)))
        (Sset _head (Etempvar _t'3 (tptr (Tstruct _list noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_list_tail (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                   (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _head (tptr (Tstruct _list noattr))) :: nil))
          (Sset _tail (Etempvar _t'4 (tptr (Tstruct _list noattr)))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'12
                (Efield
                  (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _to_text
                  (tptr (Tstruct _list noattr))))
              (Scall (Some _t'5)
                (Evar _list_copy (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr)) Tnil)
                                   (tptr (Tstruct _list noattr)) cc_default))
                ((Etempvar _t'12 (tptr (Tstruct _list noattr))) :: nil)))
            (Sset _copy_F (Etempvar _t'5 (tptr (Tstruct _list noattr)))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef (Etempvar _tail (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _line (tptr tschar)))
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Ederef
                        (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _shift tulong))
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef
                          (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _line (tptr tschar)))
                    (Scall (Some _t'6)
                      (Evar _line_concats (Tfunction
                                            (Tcons (tptr tschar)
                                              (Tcons tulong
                                                (Tcons (tptr tschar) Tnil)))
                                            (tptr tschar) cc_default))
                      ((Etempvar _t'9 (tptr tschar)) ::
                       (Etempvar _t'10 tulong) ::
                       (Etempvar _t'11 (tptr tschar)) :: nil)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _tail (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _line (tptr tschar))
                (Etempvar _t'6 (tptr tschar))))
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _list noattr))))
                (Scall None
                  (Evar _shift_list (Tfunction
                                      (Tcons (tptr (Tstruct _list noattr))
                                        (Tcons tulong Tnil))
                                      (tptr (Tstruct _list noattr))
                                      cc_default))
                  ((Etempvar _t'8 (tptr (Tstruct _list noattr))) ::
                   (Etempvar _shift tulong) :: nil)))
              (Ssequence
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _copy_F (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _tail
                      (tptr (Tstruct _list noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _tail (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _tail
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _t'7 (tptr (Tstruct _list noattr)))))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _copy_F (tptr (Tstruct _list noattr))) :: nil))
                  (Sreturn (Some (Etempvar _head (tptr (Tstruct _list noattr))))))))))))))
|}.

Definition f_add_fill := {|
  fn_return := (tptr (Tstruct _t noattr));
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) ::
                (_F, (tptr (Tstruct _t noattr))) :: (_shift, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _t noattr))) ::
               (_middle_width_new, tuint) ::
               (_first_line_width_new, tuint) ::
               (_last_line_width_new, tuint) ::
               (_to_text_new, (tptr (Tstruct _list noattr))) ::
               (_t'7, (tptr (Tstruct _list noattr))) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _t noattr))) ::
               (_t'1, (tptr (Tstruct _t noattr))) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'11
      (Efield
        (Ederef (Etempvar _G (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'11 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _format_copy (Tfunction
                               (Tcons (tptr (Tstruct _t noattr)) Tnil)
                               (tptr (Tstruct _t noattr)) cc_default))
          ((Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
        (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _t noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _format_copy (Tfunction
                                 (Tcons (tptr (Tstruct _t noattr)) Tnil)
                                 (tptr (Tstruct _t noattr)) cc_default))
            ((Etempvar _G (tptr (Tstruct _t noattr))) :: nil))
          (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _t noattr))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _t noattr) tulong) :: nil))
        (Sset _result (Etempvar _t'3 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Eunop Onotbool
                       (Etempvar _result (tptr (Tstruct _t noattr))) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _mdw_add_fill (Tfunction
                                    (Tcons (tptr (Tstruct _t noattr))
                                      (Tcons (tptr (Tstruct _t noattr))
                                        (Tcons tulong Tnil))) tuint
                                    cc_default))
              ((Etempvar _G (tptr (Tstruct _t noattr))) ::
               (Etempvar _F (tptr (Tstruct _t noattr))) ::
               (Etempvar _shift tulong) :: nil))
            (Sset _middle_width_new (Etempvar _t'4 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _flw_add_fill (Tfunction
                                      (Tcons (tptr (Tstruct _t noattr))
                                        (Tcons (tptr (Tstruct _t noattr))
                                          Tnil)) tuint cc_default))
                ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                 (Etempvar _F (tptr (Tstruct _t noattr))) :: nil))
              (Sset _first_line_width_new (Etempvar _t'5 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _llw_add_fill (Tfunction
                                        (Tcons (tptr (Tstruct _t noattr))
                                          (Tcons (tptr (Tstruct _t noattr))
                                            (Tcons tulong Tnil))) tuint
                                        cc_default))
                  ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                   (Etempvar _F (tptr (Tstruct _t noattr))) ::
                   (Etempvar _shift tulong) :: nil))
                (Sset _last_line_width_new (Etempvar _t'6 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _to_text_add_fill (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _t noattr))
                                                (Tcons
                                                  (tptr (Tstruct _t noattr))
                                                  (Tcons tulong Tnil)))
                                              (tptr (Tstruct _list noattr))
                                              cc_default))
                    ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                     (Etempvar _F (tptr (Tstruct _t noattr))) ::
                     (Etempvar _shift tulong) :: nil))
                  (Sset _to_text_new
                    (Etempvar _t'7 (tptr (Tstruct _list noattr)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _height tuint))
                    (Ssequence
                      (Sset _t'9
                        (Efield
                          (Ederef (Etempvar _F (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _height tuint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _height tuint)
                        (Ebinop Osub
                          (Ebinop Oadd (Etempvar _t'8 tuint)
                            (Etempvar _t'9 tuint) tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _first_line_width tuint)
                      (Etempvar _first_line_width_new tuint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct _t noattr)))
                            (Tstruct _t noattr)) _middle_width tuint)
                        (Etempvar _middle_width_new tuint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _result (tptr (Tstruct _t noattr)))
                              (Tstruct _t noattr)) _last_line_width tuint)
                          (Etempvar _last_line_width_new tuint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _result (tptr (Tstruct _t noattr)))
                                (Tstruct _t noattr)) _to_text
                              (tptr (Tstruct _list noattr)))
                            (Etempvar _to_text_new (tptr (Tstruct _list noattr))))
                          (Sreturn (Some (Etempvar _result (tptr (Tstruct _t noattr))))))))))))))))))
|}.

Definition f_to_string := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_total_length, tuint) ::
               (_to_text, (tptr (Tstruct _list noattr))) ::
               (_result, (tptr tschar)) :: (_t'6, (tptr tschar)) ::
               (_t'5, (tptr tschar)) :: (_t'4, (tptr tschar)) ::
               (_t'3, (tptr tschar)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tulong) :: (_t'12, (tptr tschar)) :: (_t'11, tulong) ::
               (_t'10, tulong) :: (_t'9, (tptr tschar)) ::
               (_t'8, (tptr tschar)) ::
               (_t'7, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _total_length (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _to_text
      (Efield
        (Ederef (Etempvar _f (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _to_text (tptr (Tstruct _list noattr))))
    (Ssequence
      (Swhile
        (Ebinop One (Etempvar _to_text (tptr (Tstruct _list noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'12
                (Efield
                  (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _line (tptr tschar)))
              (Scall (Some _t'1)
                (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                                cc_default))
                ((Etempvar _t'12 (tptr tschar)) :: nil)))
            (Sset _total_length
              (Ecast
                (Ebinop Oadd (Etempvar _total_length tuint)
                  (Etempvar _t'1 tulong) tulong) tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _shift tulong))
              (Sset _total_length
                (Ecast
                  (Ebinop Oadd (Etempvar _total_length tuint)
                    (Etempvar _t'11 tulong) tulong) tuint)))
            (Sset _to_text
              (Efield
                (Ederef (Etempvar _to_text (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                            cc_default))
            ((Ebinop Oadd (Etempvar _total_length tuint)
               (Econst_int (Int.repr 1) tint) tuint) :: nil))
          (Sset _result (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Sifthenelse (Eunop Onotbool (Etempvar _result (tptr tschar)) tint)
            (Scall None
              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
              ((Econst_int (Int.repr 1) tint) :: nil))
            Sskip)
          (Ssequence
            (Sset _to_text
              (Efield
                (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _to_text
                (tptr (Tstruct _list noattr))))
            (Ssequence
              (Swhile
                (Ebinop One (Etempvar _to_text (tptr (Tstruct _list noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'10
                          (Efield
                            (Ederef
                              (Etempvar _to_text (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _shift tulong))
                        (Scall (Some _t'3)
                          (Evar _sp (Tfunction (Tcons tulong Tnil)
                                      (tptr tschar) cc_default))
                          ((Etempvar _t'10 tulong) :: nil)))
                      (Scall (Some _t'4)
                        (Evar _strcat (Tfunction
                                        (Tcons (tptr tschar)
                                          (Tcons (tptr tschar) Tnil))
                                        (tptr tschar) cc_default))
                        ((Etempvar _result (tptr tschar)) ::
                         (Etempvar _t'3 (tptr tschar)) :: nil)))
                    (Sset _result (Etempvar _t'4 (tptr tschar))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Etempvar _to_text (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _line (tptr tschar)))
                        (Scall (Some _t'5)
                          (Evar _strcat (Tfunction
                                          (Tcons (tptr tschar)
                                            (Tcons (tptr tschar) Tnil))
                                          (tptr tschar) cc_default))
                          ((Etempvar _result (tptr tschar)) ::
                           (Etempvar _t'9 (tptr tschar)) :: nil)))
                      (Sset _result (Etempvar _t'5 (tptr tschar))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _to_text (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _tail
                            (tptr (Tstruct _list noattr))))
                        (Sifthenelse (Ebinop One
                                       (Etempvar _t'7 (tptr (Tstruct _list noattr)))
                                       (Ecast (Econst_int (Int.repr 0) tint)
                                         (tptr tvoid)) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'8 (Evar _newline (tptr tschar)))
                              (Scall (Some _t'6)
                                (Evar _strcat (Tfunction
                                                (Tcons (tptr tschar)
                                                  (Tcons (tptr tschar) Tnil))
                                                (tptr tschar) cc_default))
                                ((Etempvar _result (tptr tschar)) ::
                                 (Etempvar _t'8 (tptr tschar)) :: nil)))
                            (Sset _result (Etempvar _t'6 (tptr tschar))))
                          Sskip))
                      (Sset _to_text
                        (Efield
                          (Ederef
                            (Etempvar _to_text (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _tail
                          (tptr (Tstruct _list noattr))))))))
              (Sreturn (Some (Etempvar _result (tptr tschar)))))))))))
|}.

Definition f_total_width := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _middle_width tuint))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
              (Tstruct _t noattr)) _last_line_width tuint))
        (Scall (Some _t'1)
          (Evar _max (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                       cc_default))
          ((Etempvar _t'4 tuint) :: (Etempvar _t'5 tuint) :: nil))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _first_line_width tuint))
      (Scall (Some _t'2)
        (Evar _max (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                     cc_default))
        ((Etempvar _t'3 tuint) :: (Etempvar _t'1 tuint) :: nil))))
  (Sreturn (Some (Etempvar _t'2 tuint))))
|}.

Definition f_new_string_list := {|
  fn_return := (tptr (Tstruct _string_list noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _string_list noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'4, (tptr tschar)) :: (_t'3, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _string_list noattr) tulong) :: nil))
    (Sset _result (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _result (tptr (Tstruct _string_list noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct _string_list noattr)))
              (Tstruct _string_list noattr)) _line (tptr tschar))
          (Etempvar _t'2 (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _string_list noattr)))
                (Tstruct _string_list noattr)) _line (tptr tschar)))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'4 (tptr tschar)) tint)
            (Scall None
              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
              ((Econst_int (Int.repr 1) tint) :: nil))
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _string_list noattr)))
                  (Tstruct _string_list noattr)) _line (tptr tschar)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'3 (tptr tschar))
                  (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
              (Econst_int (Int.repr 0) tint)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _string_list noattr)))
                  (Tstruct _string_list noattr)) _tail
                (tptr (Tstruct _string_list noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Sreturn (Some (Etempvar _result (tptr (Tstruct _string_list noattr)))))))))))
|}.

Definition f_split := {|
  fn_return := (tptr (Tstruct _string_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_tail, (tptr (Tstruct _string_list noattr))) ::
               (_result, (tptr (Tstruct _string_list noattr))) ::
               (_new_string, (tptr tschar)) :: (_t'5, (tptr tvoid)) ::
               (_t'4, tulong) ::
               (_t'3, (tptr (Tstruct _string_list noattr))) ::
               (_t'2, (tptr (Tstruct _string_list noattr))) ::
               (_t'1, (tptr (Tstruct _string_list noattr))) ::
               (_t'11, tschar) :: (_t'10, (tptr tschar)) :: (_t'9, tschar) ::
               (_t'8, (tptr tschar)) :: (_t'7, (tptr tschar)) ::
               (_t'6, tschar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'11
      (Ederef
        (Ebinop Oadd (Etempvar _s (tptr tschar))
          (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'11 tschar)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _new_string_list (Tfunction Tnil
                                   (tptr (Tstruct _string_list noattr))
                                   cc_default)) nil)
        (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _string_list noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _split (Tfunction (Tcons (tptr tschar) Tnil)
                       (tptr (Tstruct _string_list noattr)) cc_default))
        ((Ebinop Oadd (Etempvar _s (tptr tschar))
           (Econst_int (Int.repr 1) tint) (tptr tschar)) :: nil))
      (Sset _tail (Etempvar _t'2 (tptr (Tstruct _string_list noattr)))))
    (Ssequence
      (Sset _t'6
        (Ederef
          (Ebinop Oadd (Etempvar _s (tptr tschar))
            (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tschar)
                     (Econst_int (Int.repr 10) tint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _new_string_list (Tfunction Tnil
                                       (tptr (Tstruct _string_list noattr))
                                       cc_default)) nil)
            (Sset _result
              (Etempvar _t'3 (tptr (Tstruct _string_list noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _string_list noattr)))
                  (Tstruct _string_list noattr)) _tail
                (tptr (Tstruct _string_list noattr)))
              (Etempvar _tail (tptr (Tstruct _string_list noattr))))
            (Sreturn (Some (Etempvar _result (tptr (Tstruct _string_list noattr)))))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Etempvar _tail (tptr (Tstruct _string_list noattr)))
                      (Tstruct _string_list noattr)) _line (tptr tschar)))
                (Scall (Some _t'4)
                  (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                                  cc_default))
                  ((Etempvar _t'10 (tptr tschar)) :: nil)))
              (Scall (Some _t'5)
                (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                cc_default))
                ((Ebinop Oadd (Etempvar _t'4 tulong)
                   (Econst_int (Int.repr 2) tint) tulong) :: nil)))
            (Sset _new_string (Etempvar _t'5 (tptr tvoid))))
          (Ssequence
            (Sifthenelse (Eunop Onotbool (Etempvar _new_string (tptr tschar))
                           tint)
              (Scall None
                (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
                ((Econst_int (Int.repr 1) tint) :: nil))
              Sskip)
            (Ssequence
              (Ssequence
                (Sset _t'9
                  (Ederef
                    (Ebinop Oadd (Etempvar _s (tptr tschar))
                      (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _new_string (tptr tschar))
                      (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar)
                  (Etempvar _t'9 tschar)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _new_string (tptr tschar))
                      (Econst_int (Int.repr 1) tint) (tptr tschar)) tschar)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _tail (tptr (Tstruct _string_list noattr)))
                          (Tstruct _string_list noattr)) _line (tptr tschar)))
                    (Scall None
                      (Evar _strcat (Tfunction
                                      (Tcons (tptr tschar)
                                        (Tcons (tptr tschar) Tnil))
                                      (tptr tschar) cc_default))
                      ((Etempvar _new_string (tptr tschar)) ::
                       (Etempvar _t'8 (tptr tschar)) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _tail (tptr (Tstruct _string_list noattr)))
                            (Tstruct _string_list noattr)) _line
                          (tptr tschar)))
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Etempvar _t'7 (tptr tschar)) :: nil)))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _tail (tptr (Tstruct _string_list noattr)))
                            (Tstruct _string_list noattr)) _line
                          (tptr tschar))
                        (Etempvar _new_string (tptr tschar)))
                      (Sreturn (Some (Etempvar _tail (tptr (Tstruct _string_list noattr))))))))))))))))
|}.

Definition f_indent := {|
  fn_return := (tptr (Tstruct _t noattr));
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _t noattr))) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _t noattr))) ::
               (_t'2, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr tvoid)) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _list noattr))) ::
               (_t'3, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'9
      (Efield
        (Ederef (Etempvar _f (tptr (Tstruct _t noattr))) (Tstruct _t noattr))
        _height tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'9 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _t noattr) tulong) :: nil))
      (Sset _result (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _result (tptr (Tstruct _t noattr))) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _height tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                (Tstruct _t noattr)) _height tuint) (Etempvar _t'8 tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _first_line_width tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                  (Tstruct _t noattr)) _first_line_width tuint)
              (Ebinop Oadd (Etempvar _t'7 tuint) (Etempvar _n tulong) tulong)))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _middle_width tuint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                    (Tstruct _t noattr)) _middle_width tuint)
                (Ebinop Oadd (Etempvar _t'6 tuint) (Etempvar _n tulong)
                  tulong)))
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _last_line_width tuint))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _last_line_width tuint)
                  (Ebinop Oadd (Etempvar _t'5 tuint) (Etempvar _n tulong)
                    tulong)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Efield
                        (Ederef (Etempvar _f (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _to_text
                        (tptr (Tstruct _list noattr))))
                    (Scall (Some _t'2)
                      (Evar _list_copy (Tfunction
                                         (Tcons (tptr (Tstruct _list noattr))
                                           Tnil)
                                         (tptr (Tstruct _list noattr))
                                         cc_default))
                      ((Etempvar _t'4 (tptr (Tstruct _list noattr))) :: nil)))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                        (Tstruct _t noattr)) _to_text
                      (tptr (Tstruct _list noattr)))
                    (Etempvar _t'2 (tptr (Tstruct _list noattr)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef (Etempvar _result (tptr (Tstruct _t noattr)))
                          (Tstruct _t noattr)) _to_text
                        (tptr (Tstruct _list noattr))))
                    (Scall None
                      (Evar _shift_list (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _list noattr))
                                            (Tcons tulong Tnil))
                                          (tptr (Tstruct _list noattr))
                                          cc_default))
                      ((Etempvar _t'3 (tptr (Tstruct _list noattr))) ::
                       (Etempvar _n tulong) :: nil)))
                  (Sreturn (Some (Etempvar _result (tptr (Tstruct _t noattr))))))))))))))
|}.

Definition f_clear_to_text := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct _list noattr))) ::
               (_t'2, (tptr tschar)) :: (_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _l (tptr (Tstruct _list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
      (Scall None
        (Evar _clear_to_text (Tfunction
                               (Tcons (tptr (Tstruct _list noattr)) Tnil)
                               tvoid cc_default))
        ((Etempvar _t'3 (tptr (Tstruct _list noattr))) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _line (tptr tschar)))
        (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr tschar))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _line (tptr tschar)))
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _t'2 (tptr tschar)) :: nil)))
          Sskip))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _l (tptr (Tstruct _list noattr))) :: nil)))))
|}.

Definition f_clear_format_list := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fs, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, (tptr (Tstruct _format_list noattr))) ::
               (_t'4, (tptr (Tstruct _list noattr))) ::
               (_t'3, (tptr (Tstruct _t noattr))) ::
               (_t'2, (tptr (Tstruct _t noattr))) ::
               (_t'1, (tptr (Tstruct _t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _fs (tptr (Tstruct _format_list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _fs (tptr (Tstruct _format_list noattr)))
            (Tstruct _format_list noattr)) _tail
          (tptr (Tstruct _format_list noattr))))
      (Scall None
        (Evar _clear_format_list (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _format_list noattr))
                                     Tnil) tvoid cc_default))
        ((Etempvar _t'5 (tptr (Tstruct _format_list noattr))) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _fs (tptr (Tstruct _format_list noattr)))
              (Tstruct _format_list noattr)) _G (tptr (Tstruct _t noattr))))
        (Sifthenelse (Ebinop One (Etempvar _t'1 (tptr (Tstruct _t noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _fs (tptr (Tstruct _format_list noattr)))
                    (Tstruct _format_list noattr)) _G
                  (tptr (Tstruct _t noattr))))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _t'3 (tptr (Tstruct _t noattr)))
                      (Tstruct _t noattr)) _to_text
                    (tptr (Tstruct _list noattr))))
                (Scall None
                  (Evar _clear_to_text (Tfunction
                                         (Tcons (tptr (Tstruct _list noattr))
                                           Tnil) tvoid cc_default))
                  ((Etempvar _t'4 (tptr (Tstruct _list noattr))) :: nil))))
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _fs (tptr (Tstruct _format_list noattr)))
                    (Tstruct _format_list noattr)) _G
                  (tptr (Tstruct _t noattr))))
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _t'2 (tptr (Tstruct _t noattr))) :: nil))))
          Sskip))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _fs (tptr (Tstruct _format_list noattr))) :: nil)))))
|}.

Definition f_max_width_check := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_G, (tptr (Tstruct _t noattr))) :: (_width, tuint) ::
                (_height, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _total_width (Tfunction (Tcons (tptr (Tstruct _t noattr)) Tnil)
                           tuint cc_default))
      ((Etempvar _G (tptr (Tstruct _t noattr))) :: nil))
    (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tuint) (Etempvar _width tuint)
                   tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _G (tptr (Tstruct _t noattr)))
            (Tstruct _t noattr)) _height tuint))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'2 tuint) (Etempvar _height tuint)
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_clear_last_format_element := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_fs, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_t'3, (tptr (Tstruct _format_list noattr))) ::
               (_t'2, (tptr (Tstruct _format_list noattr))) ::
               (_t'1, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _new_result_tail (Etempvar _fs (tptr (Tstruct _format_list noattr))))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                (Tstruct _format_list noattr)) _tail
              (tptr (Tstruct _format_list noattr))))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _t'2 (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _tail
                (tptr (Tstruct _format_list noattr))))
            (Sifthenelse (Ebinop One
                           (Etempvar _t'3 (tptr (Tstruct _format_list noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              Sskip
              Sbreak)))
        (Sset _new_result_tail
          (Efield
            (Ederef
              (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
              (Tstruct _format_list noattr)) _tail
            (tptr (Tstruct _format_list noattr)))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef
              (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
              (Tstruct _format_list noattr)) _tail
            (tptr (Tstruct _format_list noattr))))
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _t'1 (tptr (Tstruct _format_list noattr))) :: nil)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
              (Tstruct _format_list noattr)) _tail
            (tptr (Tstruct _format_list noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Sreturn (Some (Etempvar _fs (tptr (Tstruct _format_list noattr)))))))))
|}.

Definition f_indent_doc := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_width, tuint) :: (_height, tuint) ::
                (_fs, (tptr (Tstruct _format_list noattr))) ::
                (_shift, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _format_list noattr))) ::
               (_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_fs_tail, (tptr (Tstruct _format_list noattr))) ::
               (_has_item, tbool) :: (_G, (tptr (Tstruct _t noattr))) ::
               (_t'6, tbool) :: (_t'5, (tptr (Tstruct _t noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr (Tstruct _t noattr))) ::
               (_t'2, (tptr (Tstruct _t noattr))) :: (_t'1, (tptr tvoid)) ::
               (_t'14, (tptr (Tstruct _t noattr))) ::
               (_t'13, (tptr (Tstruct _list noattr))) ::
               (_t'12, (tptr (Tstruct _t noattr))) ::
               (_t'11, (tptr (Tstruct _t noattr))) ::
               (_t'10, (tptr (Tstruct _format_list noattr))) ::
               (_t'9, (tptr (Tstruct _format_list noattr))) ::
               (_t'8, (tptr (Tstruct _format_list noattr))) ::
               (_t'7, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _fs (tptr (Tstruct _format_list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _format_list noattr) tulong) :: nil))
      (Sset _result (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _result (tptr (Tstruct _format_list noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _empty (Tfunction Tnil (tptr (Tstruct _t noattr))
                           cc_default)) nil)
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _format_list noattr)))
                (Tstruct _format_list noattr)) _G (tptr (Tstruct _t noattr)))
            (Etempvar _t'2 (tptr (Tstruct _t noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _format_list noattr)))
                (Tstruct _format_list noattr)) _tail
              (tptr (Tstruct _format_list noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Sset _result_tail
              (Etempvar _result (tptr (Tstruct _format_list noattr))))
            (Ssequence
              (Sset _fs_tail
                (Etempvar _fs (tptr (Tstruct _format_list noattr))))
              (Ssequence
                (Sset _has_item (Ecast (Econst_int (Int.repr 0) tint) tbool))
                (Ssequence
                  (Swhile
                    (Ebinop One
                      (Etempvar _fs_tail (tptr (Tstruct _format_list noattr)))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                      tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'14
                            (Efield
                              (Ederef
                                (Etempvar _fs_tail (tptr (Tstruct _format_list noattr)))
                                (Tstruct _format_list noattr)) _G
                              (tptr (Tstruct _t noattr))))
                          (Scall (Some _t'3)
                            (Evar _indent (Tfunction
                                            (Tcons (tptr (Tstruct _t noattr))
                                              (Tcons tulong Tnil))
                                            (tptr (Tstruct _t noattr))
                                            cc_default))
                            ((Etempvar _t'14 (tptr (Tstruct _t noattr))) ::
                             (Etempvar _shift tulong) :: nil)))
                        (Sset _G (Etempvar _t'3 (tptr (Tstruct _t noattr)))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _max_width_check (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _t noattr))
                                                       (Tcons tuint
                                                         (Tcons tuint Tnil)))
                                                     tbool cc_default))
                            ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                             (Etempvar _width tuint) ::
                             (Etempvar _height tuint) :: nil))
                          (Sifthenelse (Etempvar _t'6 tbool)
                            (Ssequence
                              (Ssequence
                                (Sset _t'12
                                  (Efield
                                    (Ederef
                                      (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                      (Tstruct _format_list noattr)) _G
                                    (tptr (Tstruct _t noattr))))
                                (Ssequence
                                  (Sset _t'13
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'12 (tptr (Tstruct _t noattr)))
                                        (Tstruct _t noattr)) _to_text
                                      (tptr (Tstruct _list noattr))))
                                  (Scall None
                                    (Evar _clear_to_text (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _list noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                    ((Etempvar _t'13 (tptr (Tstruct _list noattr))) ::
                                     nil))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _G
                                      (tptr (Tstruct _t noattr))))
                                  (Scall None
                                    (Evar _free (Tfunction
                                                  (Tcons (tptr tvoid) Tnil)
                                                  tvoid cc_default))
                                    ((Etempvar _t'11 (tptr (Tstruct _t noattr))) ::
                                     nil)))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _G
                                      (tptr (Tstruct _t noattr)))
                                    (Etempvar _G (tptr (Tstruct _t noattr))))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'4)
                                        (Evar _malloc (Tfunction
                                                        (Tcons tulong Tnil)
                                                        (tptr tvoid)
                                                        cc_default))
                                        ((Esizeof (Tstruct _format_list noattr) tulong) ::
                                         nil))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                            (Tstruct _format_list noattr))
                                          _tail
                                          (tptr (Tstruct _format_list noattr)))
                                        (Etempvar _t'4 (tptr tvoid))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                              (Tstruct _format_list noattr))
                                            _tail
                                            (tptr (Tstruct _format_list noattr))))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _t'10 (tptr (Tstruct _format_list noattr)))
                                                       (Ecast
                                                         (Econst_int (Int.repr 0) tint)
                                                         (tptr tvoid)) tint)
                                          (Scall None
                                            (Evar _exit (Tfunction
                                                          (Tcons tint Tnil)
                                                          tvoid cc_default))
                                            ((Econst_int (Int.repr 1) tint) ::
                                             nil))
                                          Sskip))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'5)
                                            (Evar _empty (Tfunction Tnil
                                                           (tptr (Tstruct _t noattr))
                                                           cc_default)) nil)
                                          (Ssequence
                                            (Sset _t'9
                                              (Efield
                                                (Ederef
                                                  (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                  (Tstruct _format_list noattr))
                                                _tail
                                                (tptr (Tstruct _format_list noattr))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'9 (tptr (Tstruct _format_list noattr)))
                                                  (Tstruct _format_list noattr))
                                                _G
                                                (tptr (Tstruct _t noattr)))
                                              (Etempvar _t'5 (tptr (Tstruct _t noattr))))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'8
                                              (Efield
                                                (Ederef
                                                  (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                  (Tstruct _format_list noattr))
                                                _tail
                                                (tptr (Tstruct _format_list noattr))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'8 (tptr (Tstruct _format_list noattr)))
                                                  (Tstruct _format_list noattr))
                                                _tail
                                                (tptr (Tstruct _format_list noattr)))
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tvoid))))
                                          (Ssequence
                                            (Sset _result_tail
                                              (Efield
                                                (Ederef
                                                  (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                  (Tstruct _format_list noattr))
                                                _tail
                                                (tptr (Tstruct _format_list noattr))))
                                            (Sset _has_item
                                              (Ecast
                                                (Econst_int (Int.repr 1) tint)
                                                tbool))))))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _G (tptr (Tstruct _t noattr)))
                                      (Tstruct _t noattr)) _to_text
                                    (tptr (Tstruct _list noattr))))
                                (Scall None
                                  (Evar _clear_to_text (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _list noattr))
                                                           Tnil) tvoid
                                                         cc_default))
                                  ((Etempvar _t'7 (tptr (Tstruct _list noattr))) ::
                                   nil)))
                              (Scall None
                                (Evar _free (Tfunction
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                                ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                                 nil)))))
                        (Sset _fs_tail
                          (Efield
                            (Ederef
                              (Etempvar _fs_tail (tptr (Tstruct _format_list noattr)))
                              (Tstruct _format_list noattr)) _tail
                            (tptr (Tstruct _format_list noattr)))))))
                  (Ssequence
                    (Scall None
                      (Evar _clear_format_list (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _format_list noattr))
                                                   Tnil) tvoid cc_default))
                      ((Etempvar _fs (tptr (Tstruct _format_list noattr))) ::
                       nil))
                    (Ssequence
                      (Sifthenelse (Eunop Onotbool (Etempvar _has_item tbool)
                                     tint)
                        (Ssequence
                          (Scall None
                            (Evar _clear_format_list (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _format_list noattr))
                                                         Tnil) tvoid
                                                       cc_default))
                            ((Etempvar _result (tptr (Tstruct _format_list noattr))) ::
                             nil))
                          (Sreturn (Some (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)))))
                        Sskip)
                      (Ssequence
                        (Scall None
                          (Evar _clear_last_format_element (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _format_list noattr))
                                                               Tnil)
                                                             (tptr (Tstruct _format_list noattr))
                                                             cc_default))
                          ((Etempvar _result (tptr (Tstruct _format_list noattr))) ::
                           nil))
                        (Sreturn (Some (Etempvar _result (tptr (Tstruct _format_list noattr)))))))))))))))))
|}.

Definition f_above_doc := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_width, tuint) :: (_height, tuint) ::
                (_fs1, (tptr (Tstruct _format_list noattr))) ::
                (_fs2, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _format_list noattr))) ::
               (_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_has_item, tbool) ::
               (_fs2_tail, (tptr (Tstruct _format_list noattr))) ::
               (_fs1_tail, (tptr (Tstruct _format_list noattr))) ::
               (_G, (tptr (Tstruct _t noattr))) ::
               (_new_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_t'6, tbool) :: (_t'5, (tptr (Tstruct _t noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr (Tstruct _t noattr))) ::
               (_t'2, (tptr (Tstruct _t noattr))) :: (_t'1, (tptr tvoid)) ::
               (_t'18, (tptr (Tstruct _t noattr))) ::
               (_t'17, (tptr (Tstruct _t noattr))) ::
               (_t'16, (tptr (Tstruct _list noattr))) ::
               (_t'15, (tptr (Tstruct _t noattr))) ::
               (_t'14, (tptr (Tstruct _t noattr))) ::
               (_t'13, (tptr (Tstruct _format_list noattr))) ::
               (_t'12, (tptr (Tstruct _format_list noattr))) ::
               (_t'11, (tptr (Tstruct _format_list noattr))) ::
               (_t'10, (tptr (Tstruct _list noattr))) ::
               (_t'9, (tptr (Tstruct _format_list noattr))) ::
               (_t'8, (tptr (Tstruct _format_list noattr))) ::
               (_t'7, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _fs1 (tptr (Tstruct _format_list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Sifthenelse (Ebinop One
                     (Etempvar _fs2 (tptr (Tstruct _format_list noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) :: nil))
        Sskip)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _fs2 (tptr (Tstruct _format_list noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) :: nil))
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _format_list noattr) tulong) :: nil))
        (Sset _result (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _result (tptr (Tstruct _format_list noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _empty (Tfunction Tnil (tptr (Tstruct _t noattr))
                             cc_default)) nil)
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _G
                (tptr (Tstruct _t noattr)))
              (Etempvar _t'2 (tptr (Tstruct _t noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _tail
                (tptr (Tstruct _format_list noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Ssequence
              (Sset _result_tail
                (Etempvar _result (tptr (Tstruct _format_list noattr))))
              (Ssequence
                (Sset _has_item (Ecast (Econst_int (Int.repr 0) tint) tbool))
                (Ssequence
                  (Sset _fs2_tail
                    (Etempvar _fs2 (tptr (Tstruct _format_list noattr))))
                  (Ssequence
                    (Swhile
                      (Ebinop One
                        (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                        tint)
                      (Ssequence
                        (Sset _fs1_tail
                          (Etempvar _fs1 (tptr (Tstruct _format_list noattr))))
                        (Ssequence
                          (Swhile
                            (Ebinop One
                              (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'17
                                    (Efield
                                      (Ederef
                                        (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _G
                                      (tptr (Tstruct _t noattr))))
                                  (Ssequence
                                    (Sset _t'18
                                      (Efield
                                        (Ederef
                                          (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                                          (Tstruct _format_list noattr)) _G
                                        (tptr (Tstruct _t noattr))))
                                    (Scall (Some _t'3)
                                      (Evar _add_above (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _t noattr))
                                                           (Tcons
                                                             (tptr (Tstruct _t noattr))
                                                             Tnil))
                                                         (tptr (Tstruct _t noattr))
                                                         cc_default))
                                      ((Etempvar _t'17 (tptr (Tstruct _t noattr))) ::
                                       (Etempvar _t'18 (tptr (Tstruct _t noattr))) ::
                                       nil))))
                                (Sset _G
                                  (Etempvar _t'3 (tptr (Tstruct _t noattr)))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'6)
                                    (Evar _max_width_check (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _t noattr))
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   Tnil)))
                                                             tbool
                                                             cc_default))
                                    ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                                     (Etempvar _width tuint) ::
                                     (Etempvar _height tuint) :: nil))
                                  (Sifthenelse (Etempvar _t'6 tbool)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'15
                                          (Efield
                                            (Ederef
                                              (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                              (Tstruct _format_list noattr))
                                            _G (tptr (Tstruct _t noattr))))
                                        (Ssequence
                                          (Sset _t'16
                                            (Efield
                                              (Ederef
                                                (Etempvar _t'15 (tptr (Tstruct _t noattr)))
                                                (Tstruct _t noattr)) _to_text
                                              (tptr (Tstruct _list noattr))))
                                          (Scall None
                                            (Evar _clear_to_text (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _list noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                            ((Etempvar _t'16 (tptr (Tstruct _list noattr))) ::
                                             nil))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'14
                                            (Efield
                                              (Ederef
                                                (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                (Tstruct _format_list noattr))
                                              _G (tptr (Tstruct _t noattr))))
                                          (Scall None
                                            (Evar _free (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                            ((Etempvar _t'14 (tptr (Tstruct _t noattr))) ::
                                             nil)))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                (Tstruct _format_list noattr))
                                              _G (tptr (Tstruct _t noattr)))
                                            (Etempvar _G (tptr (Tstruct _t noattr))))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'4)
                                                (Evar _malloc (Tfunction
                                                                (Tcons tulong
                                                                  Tnil)
                                                                (tptr tvoid)
                                                                cc_default))
                                                ((Esizeof (Tstruct _format_list noattr) tulong) ::
                                                 nil))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                    (Tstruct _format_list noattr))
                                                  _tail
                                                  (tptr (Tstruct _format_list noattr)))
                                                (Etempvar _t'4 (tptr tvoid))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'13
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                      (Tstruct _format_list noattr))
                                                    _tail
                                                    (tptr (Tstruct _format_list noattr))))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _t'13 (tptr (Tstruct _format_list noattr)))
                                                               (Ecast
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 (tptr tvoid))
                                                               tint)
                                                  (Scall None
                                                    (Evar _exit (Tfunction
                                                                  (Tcons tint
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                    ((Econst_int (Int.repr 1) tint) ::
                                                     nil))
                                                  Sskip))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'5)
                                                    (Evar _empty (Tfunction
                                                                   Tnil
                                                                   (tptr (Tstruct _t noattr))
                                                                   cc_default))
                                                    nil)
                                                  (Ssequence
                                                    (Sset _t'12
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'12 (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _G
                                                        (tptr (Tstruct _t noattr)))
                                                      (Etempvar _t'5 (tptr (Tstruct _t noattr))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'11 (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr)))
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tvoid))))
                                                  (Ssequence
                                                    (Sset _result_tail
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sset _has_item
                                                      (Ecast
                                                        (Econst_int (Int.repr 1) tint)
                                                        tbool))))))))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _G (tptr (Tstruct _t noattr)))
                                              (Tstruct _t noattr)) _to_text
                                            (tptr (Tstruct _list noattr))))
                                        (Scall None
                                          (Evar _clear_to_text (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _list noattr))
                                                                   Tnil)
                                                                 tvoid
                                                                 cc_default))
                                          ((Etempvar _t'10 (tptr (Tstruct _list noattr))) ::
                                           nil)))
                                      (Scall None
                                        (Evar _free (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        Tnil) tvoid
                                                      cc_default))
                                        ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                                         nil)))))
                                (Sset _fs1_tail
                                  (Efield
                                    (Ederef
                                      (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                                      (Tstruct _format_list noattr)) _tail
                                    (tptr (Tstruct _format_list noattr)))))))
                          (Sset _fs2_tail
                            (Efield
                              (Ederef
                                (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                                (Tstruct _format_list noattr)) _tail
                              (tptr (Tstruct _format_list noattr)))))))
                    (Ssequence
                      (Scall None
                        (Evar _clear_format_list (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _format_list noattr))
                                                     Tnil) tvoid cc_default))
                        ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar _clear_format_list (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _format_list noattr))
                                                       Tnil) tvoid
                                                     cc_default))
                          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) ::
                           nil))
                        (Ssequence
                          (Sifthenelse (Eunop Onotbool
                                         (Etempvar _has_item tbool) tint)
                            (Ssequence
                              (Scall None
                                (Evar _clear_format_list (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _format_list noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                ((Etempvar _result (tptr (Tstruct _format_list noattr))) ::
                                 nil))
                              (Sreturn (Some (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)))))
                            Sskip)
                          (Ssequence
                            (Sset _new_result_tail
                              (Etempvar _result (tptr (Tstruct _format_list noattr))))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Ederef
                                          (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                          (Tstruct _format_list noattr))
                                        _tail
                                        (tptr (Tstruct _format_list noattr))))
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'8 (tptr (Tstruct _format_list noattr)))
                                            (Tstruct _format_list noattr))
                                          _tail
                                          (tptr (Tstruct _format_list noattr))))
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar _t'9 (tptr (Tstruct _format_list noattr)))
                                                     (Ecast
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr tvoid)) tint)
                                        Sskip
                                        Sbreak)))
                                  (Sset _new_result_tail
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr)))))
                                Sskip)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr))))
                                  (Scall None
                                    (Evar _clear_format_list (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _format_list noattr))
                                                                 Tnil) tvoid
                                                               cc_default))
                                    ((Etempvar _t'7 (tptr (Tstruct _format_list noattr))) ::
                                     nil)))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr)))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)))
                                  (Sreturn (Some (Etempvar _result (tptr (Tstruct _format_list noattr))))))))))))))))))))))
|}.

Definition f_fill_doc := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_width, tuint) :: (_height, tuint) ::
                (_fs1, (tptr (Tstruct _format_list noattr))) ::
                (_fs2, (tptr (Tstruct _format_list noattr))) ::
                (_shift, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _format_list noattr))) ::
               (_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_has_item, tbool) ::
               (_fs2_tail, (tptr (Tstruct _format_list noattr))) ::
               (_fs1_tail, (tptr (Tstruct _format_list noattr))) ::
               (_G, (tptr (Tstruct _t noattr))) ::
               (_new_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_t'6, tbool) :: (_t'5, (tptr (Tstruct _t noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr (Tstruct _t noattr))) ::
               (_t'2, (tptr (Tstruct _t noattr))) :: (_t'1, (tptr tvoid)) ::
               (_t'18, (tptr (Tstruct _t noattr))) ::
               (_t'17, (tptr (Tstruct _t noattr))) ::
               (_t'16, (tptr (Tstruct _list noattr))) ::
               (_t'15, (tptr (Tstruct _t noattr))) ::
               (_t'14, (tptr (Tstruct _t noattr))) ::
               (_t'13, (tptr (Tstruct _format_list noattr))) ::
               (_t'12, (tptr (Tstruct _format_list noattr))) ::
               (_t'11, (tptr (Tstruct _format_list noattr))) ::
               (_t'10, (tptr (Tstruct _list noattr))) ::
               (_t'9, (tptr (Tstruct _format_list noattr))) ::
               (_t'8, (tptr (Tstruct _format_list noattr))) ::
               (_t'7, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _fs1 (tptr (Tstruct _format_list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Sifthenelse (Ebinop One
                     (Etempvar _fs2 (tptr (Tstruct _format_list noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) :: nil))
        Sskip)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _fs2 (tptr (Tstruct _format_list noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) :: nil))
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _format_list noattr) tulong) :: nil))
        (Sset _result (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _result (tptr (Tstruct _format_list noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _empty (Tfunction Tnil (tptr (Tstruct _t noattr))
                             cc_default)) nil)
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _G
                (tptr (Tstruct _t noattr)))
              (Etempvar _t'2 (tptr (Tstruct _t noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _tail
                (tptr (Tstruct _format_list noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Ssequence
              (Sset _result_tail
                (Etempvar _result (tptr (Tstruct _format_list noattr))))
              (Ssequence
                (Sset _has_item (Ecast (Econst_int (Int.repr 0) tint) tbool))
                (Ssequence
                  (Sset _fs2_tail
                    (Etempvar _fs2 (tptr (Tstruct _format_list noattr))))
                  (Ssequence
                    (Swhile
                      (Ebinop One
                        (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                        tint)
                      (Ssequence
                        (Sset _fs1_tail
                          (Etempvar _fs1 (tptr (Tstruct _format_list noattr))))
                        (Ssequence
                          (Swhile
                            (Ebinop One
                              (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'17
                                    (Efield
                                      (Ederef
                                        (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _G
                                      (tptr (Tstruct _t noattr))))
                                  (Ssequence
                                    (Sset _t'18
                                      (Efield
                                        (Ederef
                                          (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                                          (Tstruct _format_list noattr)) _G
                                        (tptr (Tstruct _t noattr))))
                                    (Scall (Some _t'3)
                                      (Evar _add_fill (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _t noattr))
                                                          (Tcons
                                                            (tptr (Tstruct _t noattr))
                                                            (Tcons tulong
                                                              Tnil)))
                                                        (tptr (Tstruct _t noattr))
                                                        cc_default))
                                      ((Etempvar _t'17 (tptr (Tstruct _t noattr))) ::
                                       (Etempvar _t'18 (tptr (Tstruct _t noattr))) ::
                                       (Etempvar _shift tulong) :: nil))))
                                (Sset _G
                                  (Etempvar _t'3 (tptr (Tstruct _t noattr)))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'6)
                                    (Evar _max_width_check (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _t noattr))
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   Tnil)))
                                                             tbool
                                                             cc_default))
                                    ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                                     (Etempvar _width tuint) ::
                                     (Etempvar _height tuint) :: nil))
                                  (Sifthenelse (Etempvar _t'6 tbool)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'15
                                          (Efield
                                            (Ederef
                                              (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                              (Tstruct _format_list noattr))
                                            _G (tptr (Tstruct _t noattr))))
                                        (Ssequence
                                          (Sset _t'16
                                            (Efield
                                              (Ederef
                                                (Etempvar _t'15 (tptr (Tstruct _t noattr)))
                                                (Tstruct _t noattr)) _to_text
                                              (tptr (Tstruct _list noattr))))
                                          (Scall None
                                            (Evar _clear_to_text (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _list noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                            ((Etempvar _t'16 (tptr (Tstruct _list noattr))) ::
                                             nil))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'14
                                            (Efield
                                              (Ederef
                                                (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                (Tstruct _format_list noattr))
                                              _G (tptr (Tstruct _t noattr))))
                                          (Scall None
                                            (Evar _free (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                            ((Etempvar _t'14 (tptr (Tstruct _t noattr))) ::
                                             nil)))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                (Tstruct _format_list noattr))
                                              _G (tptr (Tstruct _t noattr)))
                                            (Etempvar _G (tptr (Tstruct _t noattr))))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'4)
                                                (Evar _malloc (Tfunction
                                                                (Tcons tulong
                                                                  Tnil)
                                                                (tptr tvoid)
                                                                cc_default))
                                                ((Esizeof (Tstruct _format_list noattr) tulong) ::
                                                 nil))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                    (Tstruct _format_list noattr))
                                                  _tail
                                                  (tptr (Tstruct _format_list noattr)))
                                                (Etempvar _t'4 (tptr tvoid))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'13
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                      (Tstruct _format_list noattr))
                                                    _tail
                                                    (tptr (Tstruct _format_list noattr))))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _t'13 (tptr (Tstruct _format_list noattr)))
                                                               (Ecast
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 (tptr tvoid))
                                                               tint)
                                                  (Scall None
                                                    (Evar _exit (Tfunction
                                                                  (Tcons tint
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                    ((Econst_int (Int.repr 1) tint) ::
                                                     nil))
                                                  Sskip))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'5)
                                                    (Evar _empty (Tfunction
                                                                   Tnil
                                                                   (tptr (Tstruct _t noattr))
                                                                   cc_default))
                                                    nil)
                                                  (Ssequence
                                                    (Sset _t'12
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'12 (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _G
                                                        (tptr (Tstruct _t noattr)))
                                                      (Etempvar _t'5 (tptr (Tstruct _t noattr))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'11 (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr)))
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tvoid))))
                                                  (Ssequence
                                                    (Sset _result_tail
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sset _has_item
                                                      (Ecast
                                                        (Econst_int (Int.repr 1) tint)
                                                        tbool))))))))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _G (tptr (Tstruct _t noattr)))
                                              (Tstruct _t noattr)) _to_text
                                            (tptr (Tstruct _list noattr))))
                                        (Scall None
                                          (Evar _clear_to_text (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _list noattr))
                                                                   Tnil)
                                                                 tvoid
                                                                 cc_default))
                                          ((Etempvar _t'10 (tptr (Tstruct _list noattr))) ::
                                           nil)))
                                      (Scall None
                                        (Evar _free (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        Tnil) tvoid
                                                      cc_default))
                                        ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                                         nil)))))
                                (Sset _fs1_tail
                                  (Efield
                                    (Ederef
                                      (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                                      (Tstruct _format_list noattr)) _tail
                                    (tptr (Tstruct _format_list noattr)))))))
                          (Sset _fs2_tail
                            (Efield
                              (Ederef
                                (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                                (Tstruct _format_list noattr)) _tail
                              (tptr (Tstruct _format_list noattr)))))))
                    (Ssequence
                      (Scall None
                        (Evar _clear_format_list (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _format_list noattr))
                                                     Tnil) tvoid cc_default))
                        ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar _clear_format_list (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _format_list noattr))
                                                       Tnil) tvoid
                                                     cc_default))
                          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) ::
                           nil))
                        (Ssequence
                          (Sifthenelse (Eunop Onotbool
                                         (Etempvar _has_item tbool) tint)
                            (Ssequence
                              (Scall None
                                (Evar _clear_format_list (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _format_list noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                ((Etempvar _result (tptr (Tstruct _format_list noattr))) ::
                                 nil))
                              (Sreturn (Some (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)))))
                            Sskip)
                          (Ssequence
                            (Sset _new_result_tail
                              (Etempvar _result (tptr (Tstruct _format_list noattr))))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Ederef
                                          (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                          (Tstruct _format_list noattr))
                                        _tail
                                        (tptr (Tstruct _format_list noattr))))
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'8 (tptr (Tstruct _format_list noattr)))
                                            (Tstruct _format_list noattr))
                                          _tail
                                          (tptr (Tstruct _format_list noattr))))
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar _t'9 (tptr (Tstruct _format_list noattr)))
                                                     (Ecast
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr tvoid)) tint)
                                        Sskip
                                        Sbreak)))
                                  (Sset _new_result_tail
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr)))))
                                Sskip)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr))))
                                  (Scall None
                                    (Evar _clear_format_list (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _format_list noattr))
                                                                 Tnil) tvoid
                                                               cc_default))
                                    ((Etempvar _t'7 (tptr (Tstruct _format_list noattr))) ::
                                     nil)))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr)))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)))
                                  (Sreturn (Some (Etempvar _result (tptr (Tstruct _format_list noattr))))))))))))))))))))))
|}.

Definition f_beside_doc := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_width, tuint) :: (_height, tuint) ::
                (_fs1, (tptr (Tstruct _format_list noattr))) ::
                (_fs2, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _format_list noattr))) ::
               (_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_has_item, tbool) ::
               (_fs2_tail, (tptr (Tstruct _format_list noattr))) ::
               (_fs1_tail, (tptr (Tstruct _format_list noattr))) ::
               (_G, (tptr (Tstruct _t noattr))) ::
               (_new_result_tail, (tptr (Tstruct _format_list noattr))) ::
               (_t'6, tbool) :: (_t'5, (tptr (Tstruct _t noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr (Tstruct _t noattr))) ::
               (_t'2, (tptr (Tstruct _t noattr))) :: (_t'1, (tptr tvoid)) ::
               (_t'18, (tptr (Tstruct _t noattr))) ::
               (_t'17, (tptr (Tstruct _t noattr))) ::
               (_t'16, (tptr (Tstruct _list noattr))) ::
               (_t'15, (tptr (Tstruct _t noattr))) ::
               (_t'14, (tptr (Tstruct _t noattr))) ::
               (_t'13, (tptr (Tstruct _format_list noattr))) ::
               (_t'12, (tptr (Tstruct _format_list noattr))) ::
               (_t'11, (tptr (Tstruct _format_list noattr))) ::
               (_t'10, (tptr (Tstruct _list noattr))) ::
               (_t'9, (tptr (Tstruct _format_list noattr))) ::
               (_t'8, (tptr (Tstruct _format_list noattr))) ::
               (_t'7, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _fs1 (tptr (Tstruct _format_list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Sifthenelse (Ebinop One
                     (Etempvar _fs2 (tptr (Tstruct _format_list noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) :: nil))
        Sskip)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _fs2 (tptr (Tstruct _format_list noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) :: nil))
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _format_list noattr) tulong) :: nil))
        (Sset _result (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _result (tptr (Tstruct _format_list noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _empty (Tfunction Tnil (tptr (Tstruct _t noattr))
                             cc_default)) nil)
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _G
                (tptr (Tstruct _t noattr)))
              (Etempvar _t'2 (tptr (Tstruct _t noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _tail
                (tptr (Tstruct _format_list noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Ssequence
              (Sset _result_tail
                (Etempvar _result (tptr (Tstruct _format_list noattr))))
              (Ssequence
                (Sset _has_item (Ecast (Econst_int (Int.repr 0) tint) tbool))
                (Ssequence
                  (Sset _fs2_tail
                    (Etempvar _fs2 (tptr (Tstruct _format_list noattr))))
                  (Ssequence
                    (Swhile
                      (Ebinop One
                        (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                        tint)
                      (Ssequence
                        (Sset _fs1_tail
                          (Etempvar _fs1 (tptr (Tstruct _format_list noattr))))
                        (Ssequence
                          (Swhile
                            (Ebinop One
                              (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint)
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'17
                                    (Efield
                                      (Ederef
                                        (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _G
                                      (tptr (Tstruct _t noattr))))
                                  (Ssequence
                                    (Sset _t'18
                                      (Efield
                                        (Ederef
                                          (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                                          (Tstruct _format_list noattr)) _G
                                        (tptr (Tstruct _t noattr))))
                                    (Scall (Some _t'3)
                                      (Evar _add_beside (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _t noattr))
                                                            (Tcons
                                                              (tptr (Tstruct _t noattr))
                                                              Tnil))
                                                          (tptr (Tstruct _t noattr))
                                                          cc_default))
                                      ((Etempvar _t'17 (tptr (Tstruct _t noattr))) ::
                                       (Etempvar _t'18 (tptr (Tstruct _t noattr))) ::
                                       nil))))
                                (Sset _G
                                  (Etempvar _t'3 (tptr (Tstruct _t noattr)))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'6)
                                    (Evar _max_width_check (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _t noattr))
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   Tnil)))
                                                             tbool
                                                             cc_default))
                                    ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                                     (Etempvar _width tuint) ::
                                     (Etempvar _height tuint) :: nil))
                                  (Sifthenelse (Etempvar _t'6 tbool)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'15
                                          (Efield
                                            (Ederef
                                              (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                              (Tstruct _format_list noattr))
                                            _G (tptr (Tstruct _t noattr))))
                                        (Ssequence
                                          (Sset _t'16
                                            (Efield
                                              (Ederef
                                                (Etempvar _t'15 (tptr (Tstruct _t noattr)))
                                                (Tstruct _t noattr)) _to_text
                                              (tptr (Tstruct _list noattr))))
                                          (Scall None
                                            (Evar _clear_to_text (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _list noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default))
                                            ((Etempvar _t'16 (tptr (Tstruct _list noattr))) ::
                                             nil))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'14
                                            (Efield
                                              (Ederef
                                                (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                (Tstruct _format_list noattr))
                                              _G (tptr (Tstruct _t noattr))))
                                          (Scall None
                                            (Evar _free (Tfunction
                                                          (Tcons (tptr tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                            ((Etempvar _t'14 (tptr (Tstruct _t noattr))) ::
                                             nil)))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                (Tstruct _format_list noattr))
                                              _G (tptr (Tstruct _t noattr)))
                                            (Etempvar _G (tptr (Tstruct _t noattr))))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'4)
                                                (Evar _malloc (Tfunction
                                                                (Tcons tulong
                                                                  Tnil)
                                                                (tptr tvoid)
                                                                cc_default))
                                                ((Esizeof (Tstruct _format_list noattr) tulong) ::
                                                 nil))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                    (Tstruct _format_list noattr))
                                                  _tail
                                                  (tptr (Tstruct _format_list noattr)))
                                                (Etempvar _t'4 (tptr tvoid))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'13
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                      (Tstruct _format_list noattr))
                                                    _tail
                                                    (tptr (Tstruct _format_list noattr))))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _t'13 (tptr (Tstruct _format_list noattr)))
                                                               (Ecast
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 (tptr tvoid))
                                                               tint)
                                                  (Scall None
                                                    (Evar _exit (Tfunction
                                                                  (Tcons tint
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                    ((Econst_int (Int.repr 1) tint) ::
                                                     nil))
                                                  Sskip))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'5)
                                                    (Evar _empty (Tfunction
                                                                   Tnil
                                                                   (tptr (Tstruct _t noattr))
                                                                   cc_default))
                                                    nil)
                                                  (Ssequence
                                                    (Sset _t'12
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'12 (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _G
                                                        (tptr (Tstruct _t noattr)))
                                                      (Etempvar _t'5 (tptr (Tstruct _t noattr))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'11 (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr)))
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tvoid))))
                                                  (Ssequence
                                                    (Sset _result_tail
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _result_tail (tptr (Tstruct _format_list noattr)))
                                                          (Tstruct _format_list noattr))
                                                        _tail
                                                        (tptr (Tstruct _format_list noattr))))
                                                    (Sset _has_item
                                                      (Ecast
                                                        (Econst_int (Int.repr 1) tint)
                                                        tbool))))))))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _G (tptr (Tstruct _t noattr)))
                                              (Tstruct _t noattr)) _to_text
                                            (tptr (Tstruct _list noattr))))
                                        (Scall None
                                          (Evar _clear_to_text (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _list noattr))
                                                                   Tnil)
                                                                 tvoid
                                                                 cc_default))
                                          ((Etempvar _t'10 (tptr (Tstruct _list noattr))) ::
                                           nil)))
                                      (Scall None
                                        (Evar _free (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        Tnil) tvoid
                                                      cc_default))
                                        ((Etempvar _G (tptr (Tstruct _t noattr))) ::
                                         nil)))))
                                (Sset _fs1_tail
                                  (Efield
                                    (Ederef
                                      (Etempvar _fs1_tail (tptr (Tstruct _format_list noattr)))
                                      (Tstruct _format_list noattr)) _tail
                                    (tptr (Tstruct _format_list noattr)))))))
                          (Sset _fs2_tail
                            (Efield
                              (Ederef
                                (Etempvar _fs2_tail (tptr (Tstruct _format_list noattr)))
                                (Tstruct _format_list noattr)) _tail
                              (tptr (Tstruct _format_list noattr)))))))
                    (Ssequence
                      (Scall None
                        (Evar _clear_format_list (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _format_list noattr))
                                                     Tnil) tvoid cc_default))
                        ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar _clear_format_list (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _format_list noattr))
                                                       Tnil) tvoid
                                                     cc_default))
                          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) ::
                           nil))
                        (Ssequence
                          (Sifthenelse (Eunop Onotbool
                                         (Etempvar _has_item tbool) tint)
                            (Ssequence
                              (Scall None
                                (Evar _clear_format_list (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _format_list noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                ((Etempvar _result (tptr (Tstruct _format_list noattr))) ::
                                 nil))
                              (Sreturn (Some (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)))))
                            Sskip)
                          (Ssequence
                            (Sset _new_result_tail
                              (Etempvar _result (tptr (Tstruct _format_list noattr))))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Ederef
                                          (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                          (Tstruct _format_list noattr))
                                        _tail
                                        (tptr (Tstruct _format_list noattr))))
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'8 (tptr (Tstruct _format_list noattr)))
                                            (Tstruct _format_list noattr))
                                          _tail
                                          (tptr (Tstruct _format_list noattr))))
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar _t'9 (tptr (Tstruct _format_list noattr)))
                                                     (Ecast
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr tvoid)) tint)
                                        Sskip
                                        Sbreak)))
                                  (Sset _new_result_tail
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr)))))
                                Sskip)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr))))
                                  (Scall None
                                    (Evar _clear_format_list (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _format_list noattr))
                                                                 Tnil) tvoid
                                                               cc_default))
                                    ((Etempvar _t'7 (tptr (Tstruct _format_list noattr))) ::
                                     nil)))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _new_result_tail (tptr (Tstruct _format_list noattr)))
                                        (Tstruct _format_list noattr)) _tail
                                      (tptr (Tstruct _format_list noattr)))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)))
                                  (Sreturn (Some (Etempvar _result (tptr (Tstruct _format_list noattr))))))))))))))))))))))
|}.

Definition f_format_list_copy := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_fs, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _format_list noattr))) ::
               (_t'3, (tptr (Tstruct _format_list noattr))) ::
               (_t'2, (tptr (Tstruct _t noattr))) :: (_t'1, (tptr tvoid)) ::
               (_t'5, (tptr (Tstruct _t noattr))) ::
               (_t'4, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _fs (tptr (Tstruct _format_list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _format_list noattr) tulong) :: nil))
      (Sset _result (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _result (tptr (Tstruct _format_list noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _fs (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _G
                (tptr (Tstruct _t noattr))))
            (Scall (Some _t'2)
              (Evar _format_copy (Tfunction
                                   (Tcons (tptr (Tstruct _t noattr)) Tnil)
                                   (tptr (Tstruct _t noattr)) cc_default))
              ((Etempvar _t'5 (tptr (Tstruct _t noattr))) :: nil)))
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct _format_list noattr)))
                (Tstruct _format_list noattr)) _G (tptr (Tstruct _t noattr)))
            (Etempvar _t'2 (tptr (Tstruct _t noattr)))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _fs (tptr (Tstruct _format_list noattr)))
                    (Tstruct _format_list noattr)) _tail
                  (tptr (Tstruct _format_list noattr))))
              (Scall (Some _t'3)
                (Evar _format_list_copy (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _format_list noattr))
                                            Tnil)
                                          (tptr (Tstruct _format_list noattr))
                                          cc_default))
                ((Etempvar _t'4 (tptr (Tstruct _format_list noattr))) :: nil)))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _result (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _tail
                (tptr (Tstruct _format_list noattr)))
              (Etempvar _t'3 (tptr (Tstruct _format_list noattr)))))
          (Sreturn (Some (Etempvar _result (tptr (Tstruct _format_list noattr))))))))))
|}.

Definition f_get_format_list_tail := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_fs, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_cur, (tptr (Tstruct _format_list noattr))) ::
               (_t'1, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _cur (Etempvar _fs (tptr (Tstruct _format_list noattr))))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _cur (tptr (Tstruct _format_list noattr)))
                (Tstruct _format_list noattr)) _tail
              (tptr (Tstruct _format_list noattr))))
          (Sifthenelse (Ebinop One
                         (Etempvar _t'1 (tptr (Tstruct _format_list noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            Sskip
            Sbreak))
        (Sset _cur
          (Efield
            (Ederef (Etempvar _cur (tptr (Tstruct _format_list noattr)))
              (Tstruct _format_list noattr)) _tail
            (tptr (Tstruct _format_list noattr)))))
      Sskip)
    (Sreturn (Some (Etempvar _cur (tptr (Tstruct _format_list noattr)))))))
|}.

Definition f_choice_doc := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_fs1, (tptr (Tstruct _format_list noattr))) ::
                (_fs2, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct _format_list noattr))) ::
               (_result__1, (tptr (Tstruct _format_list noattr))) ::
               (_result__2, (tptr (Tstruct _format_list noattr))) ::
               (_format_tail, (tptr (Tstruct _format_list noattr))) ::
               (_t'5, (tptr (Tstruct _format_list noattr))) ::
               (_t'4, (tptr (Tstruct _format_list noattr))) ::
               (_t'3, (tptr (Tstruct _format_list noattr))) ::
               (_t'2, (tptr (Tstruct _format_list noattr))) ::
               (_t'1, (tptr (Tstruct _format_list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _fs1 (tptr (Tstruct _format_list noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _format_list_copy (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _format_list noattr))
                                      Tnil)
                                    (tptr (Tstruct _format_list noattr))
                                    cc_default))
          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) :: nil))
        (Sset _result (Etempvar _t'1 (tptr (Tstruct _format_list noattr)))))
      (Ssequence
        (Scall None
          (Evar _clear_format_list (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _format_list noattr))
                                       Tnil) tvoid cc_default))
          ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) :: nil))
        (Sreturn (Some (Etempvar _result (tptr (Tstruct _format_list noattr)))))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _fs2 (tptr (Tstruct _format_list noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _format_list_copy (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _format_list noattr))
                                        Tnil)
                                      (tptr (Tstruct _format_list noattr))
                                      cc_default))
            ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) :: nil))
          (Sset _result__1
            (Etempvar _t'2 (tptr (Tstruct _format_list noattr)))))
        (Ssequence
          (Scall None
            (Evar _clear_format_list (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _format_list noattr))
                                         Tnil) tvoid cc_default))
            ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) :: nil))
          (Sreturn (Some (Etempvar _result__1 (tptr (Tstruct _format_list noattr)))))))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _format_list_copy (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _format_list noattr))
                                      Tnil)
                                    (tptr (Tstruct _format_list noattr))
                                    cc_default))
          ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) :: nil))
        (Sset _result__2
          (Etempvar _t'3 (tptr (Tstruct _format_list noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_format_list_tail (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _format_list noattr))
                                            Tnil)
                                          (tptr (Tstruct _format_list noattr))
                                          cc_default))
            ((Etempvar _result__2 (tptr (Tstruct _format_list noattr))) ::
             nil))
          (Sset _format_tail
            (Etempvar _t'4 (tptr (Tstruct _format_list noattr)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _format_list_copy (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _format_list noattr))
                                          Tnil)
                                        (tptr (Tstruct _format_list noattr))
                                        cc_default))
              ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) :: nil))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _format_tail (tptr (Tstruct _format_list noattr)))
                  (Tstruct _format_list noattr)) _tail
                (tptr (Tstruct _format_list noattr)))
              (Etempvar _t'5 (tptr (Tstruct _format_list noattr)))))
          (Ssequence
            (Scall None
              (Evar _clear_format_list (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _format_list noattr))
                                           Tnil) tvoid cc_default))
              ((Etempvar _fs1 (tptr (Tstruct _format_list noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _clear_format_list (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _format_list noattr))
                                             Tnil) tvoid cc_default))
                ((Etempvar _fs2 (tptr (Tstruct _format_list noattr))) :: nil))
              (Sreturn (Some (Etempvar _result__2 (tptr (Tstruct _format_list noattr))))))))))))
|}.

Definition f_construct_doc := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_width, tuint) :: (_height, tuint) :: (_s, (tptr tschar)) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
|}.

Definition f_evaluator_trivial := {|
  fn_return := (tptr (Tstruct _format_list noattr));
  fn_callconv := cc_default;
  fn_params := ((_width, tuint) :: (_height, tuint) ::
                (_d, (tptr (Tstruct _doc noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'15, (tptr (Tstruct _format_list noattr))) ::
               (_t'14, (tptr (Tstruct _format_list noattr))) ::
               (_t'13, (tptr (Tstruct _format_list noattr))) ::
               (_t'12, (tptr (Tstruct _format_list noattr))) ::
               (_t'11, (tptr (Tstruct _format_list noattr))) ::
               (_t'10, (tptr (Tstruct _format_list noattr))) ::
               (_t'9, (tptr (Tstruct _format_list noattr))) ::
               (_t'8, (tptr (Tstruct _format_list noattr))) ::
               (_t'7, (tptr (Tstruct _format_list noattr))) ::
               (_t'6, (tptr (Tstruct _format_list noattr))) ::
               (_t'5, (tptr (Tstruct _format_list noattr))) ::
               (_t'4, (tptr (Tstruct _format_list noattr))) ::
               (_t'3, (tptr (Tstruct _format_list noattr))) ::
               (_t'2, (tptr (Tstruct _format_list noattr))) ::
               (_t'1, (tptr (Tstruct _format_list noattr))) ::
               (_t'33, (tptr tvoid)) :: (_t'32, (tptr tvoid)) ::
               (_t'31, tulong) :: (_t'30, (tptr tvoid)) ::
               (_t'29, (tptr tvoid)) :: (_t'28, (tptr tvoid)) ::
               (_t'27, (tptr tvoid)) :: (_t'26, (tptr tvoid)) ::
               (_t'25, (tptr tvoid)) :: (_t'24, (tptr tvoid)) ::
               (_t'23, (tptr tvoid)) :: (_t'22, tulong) :: (_t'21, tuint) ::
               (_t'20, tuint) :: (_t'19, tuint) :: (_t'18, tuint) ::
               (_t'17, tuint) :: (_t'16, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'16
    (Efield
      (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
        (Tstruct _doc noattr)) _type tuint))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'16 tuint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Ssequence
        (Sset _t'33
          (Efield
            (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
              (Tstruct _doc noattr)) _child1 (tptr tvoid)))
        (Scall (Some _t'1)
          (Evar _construct_doc (Tfunction
                                 (Tcons tuint
                                   (Tcons tuint (Tcons (tptr tschar) Tnil)))
                                 (tptr (Tstruct _format_list noattr))
                                 cc_default))
          ((Etempvar _width tuint) :: (Etempvar _height tuint) ::
           (Etempvar _t'33 (tptr tvoid)) :: nil)))
      (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _format_list noattr))))))
    (Ssequence
      (Sset _t'17
        (Efield
          (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
            (Tstruct _doc noattr)) _type tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'17 tuint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'32
                (Efield
                  (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                    (Tstruct _doc noattr)) _child1 (tptr tvoid)))
              (Scall (Some _t'2)
                (Evar _evaluator_trivial (Tfunction
                                           (Tcons tuint
                                             (Tcons tuint
                                               (Tcons
                                                 (tptr (Tstruct _doc noattr))
                                                 Tnil)))
                                           (tptr (Tstruct _format_list noattr))
                                           cc_default))
                ((Etempvar _width tuint) :: (Etempvar _height tuint) ::
                 (Etempvar _t'32 (tptr tvoid)) :: nil)))
            (Ssequence
              (Sset _t'31
                (Efield
                  (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                    (Tstruct _doc noattr)) _shift tulong))
              (Scall (Some _t'3)
                (Evar _indent_doc (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint
                                        (Tcons
                                          (tptr (Tstruct _format_list noattr))
                                          (Tcons tulong Tnil))))
                                    (tptr (Tstruct _format_list noattr))
                                    cc_default))
                ((Etempvar _width tuint) :: (Etempvar _height tuint) ::
                 (Etempvar _t'2 (tptr (Tstruct _format_list noattr))) ::
                 (Etempvar _t'31 tulong) :: nil))))
          (Sreturn (Some (Etempvar _t'3 (tptr (Tstruct _format_list noattr))))))
        (Ssequence
          (Sset _t'18
            (Efield
              (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                (Tstruct _doc noattr)) _type tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'18 tuint)
                         (Econst_int (Int.repr 2) tint) tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'30
                      (Efield
                        (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                          (Tstruct _doc noattr)) _child1 (tptr tvoid)))
                    (Scall (Some _t'4)
                      (Evar _evaluator_trivial (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint
                                                     (Tcons
                                                       (tptr (Tstruct _doc noattr))
                                                       Tnil)))
                                                 (tptr (Tstruct _format_list noattr))
                                                 cc_default))
                      ((Etempvar _width tuint) :: (Etempvar _height tuint) ::
                       (Etempvar _t'30 (tptr tvoid)) :: nil)))
                  (Ssequence
                    (Sset _t'29
                      (Efield
                        (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                          (Tstruct _doc noattr)) _child2 (tptr tvoid)))
                    (Scall (Some _t'5)
                      (Evar _evaluator_trivial (Tfunction
                                                 (Tcons tuint
                                                   (Tcons tuint
                                                     (Tcons
                                                       (tptr (Tstruct _doc noattr))
                                                       Tnil)))
                                                 (tptr (Tstruct _format_list noattr))
                                                 cc_default))
                      ((Etempvar _width tuint) :: (Etempvar _height tuint) ::
                       (Etempvar _t'29 (tptr tvoid)) :: nil))))
                (Scall (Some _t'6)
                  (Evar _beside_doc (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons
                                            (tptr (Tstruct _format_list noattr))
                                            (Tcons
                                              (tptr (Tstruct _format_list noattr))
                                              Tnil))))
                                      (tptr (Tstruct _format_list noattr))
                                      cc_default))
                  ((Etempvar _width tuint) :: (Etempvar _height tuint) ::
                   (Etempvar _t'4 (tptr (Tstruct _format_list noattr))) ::
                   (Etempvar _t'5 (tptr (Tstruct _format_list noattr))) ::
                   nil)))
              (Sreturn (Some (Etempvar _t'6 (tptr (Tstruct _format_list noattr))))))
            (Ssequence
              (Sset _t'19
                (Efield
                  (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                    (Tstruct _doc noattr)) _type tuint))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'19 tuint)
                             (Econst_int (Int.repr 3) tint) tint)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'28
                          (Efield
                            (Ederef
                              (Etempvar _d (tptr (Tstruct _doc noattr)))
                              (Tstruct _doc noattr)) _child1 (tptr tvoid)))
                        (Scall (Some _t'7)
                          (Evar _evaluator_trivial (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tuint
                                                         (Tcons
                                                           (tptr (Tstruct _doc noattr))
                                                           Tnil)))
                                                     (tptr (Tstruct _format_list noattr))
                                                     cc_default))
                          ((Etempvar _width tuint) ::
                           (Etempvar _height tuint) ::
                           (Etempvar _t'28 (tptr tvoid)) :: nil)))
                      (Ssequence
                        (Sset _t'27
                          (Efield
                            (Ederef
                              (Etempvar _d (tptr (Tstruct _doc noattr)))
                              (Tstruct _doc noattr)) _child2 (tptr tvoid)))
                        (Scall (Some _t'8)
                          (Evar _evaluator_trivial (Tfunction
                                                     (Tcons tuint
                                                       (Tcons tuint
                                                         (Tcons
                                                           (tptr (Tstruct _doc noattr))
                                                           Tnil)))
                                                     (tptr (Tstruct _format_list noattr))
                                                     cc_default))
                          ((Etempvar _width tuint) ::
                           (Etempvar _height tuint) ::
                           (Etempvar _t'27 (tptr tvoid)) :: nil))))
                    (Scall (Some _t'9)
                      (Evar _above_doc (Tfunction
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons
                                               (tptr (Tstruct _format_list noattr))
                                               (Tcons
                                                 (tptr (Tstruct _format_list noattr))
                                                 Tnil))))
                                         (tptr (Tstruct _format_list noattr))
                                         cc_default))
                      ((Etempvar _width tuint) :: (Etempvar _height tuint) ::
                       (Etempvar _t'7 (tptr (Tstruct _format_list noattr))) ::
                       (Etempvar _t'8 (tptr (Tstruct _format_list noattr))) ::
                       nil)))
                  (Sreturn (Some (Etempvar _t'9 (tptr (Tstruct _format_list noattr))))))
                (Ssequence
                  (Sset _t'20
                    (Efield
                      (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                        (Tstruct _doc noattr)) _type tuint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'20 tuint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'26
                              (Efield
                                (Ederef
                                  (Etempvar _d (tptr (Tstruct _doc noattr)))
                                  (Tstruct _doc noattr)) _child1
                                (tptr tvoid)))
                            (Scall (Some _t'10)
                              (Evar _evaluator_trivial (Tfunction
                                                         (Tcons tuint
                                                           (Tcons tuint
                                                             (Tcons
                                                               (tptr (Tstruct _doc noattr))
                                                               Tnil)))
                                                         (tptr (Tstruct _format_list noattr))
                                                         cc_default))
                              ((Etempvar _width tuint) ::
                               (Etempvar _height tuint) ::
                               (Etempvar _t'26 (tptr tvoid)) :: nil)))
                          (Ssequence
                            (Sset _t'25
                              (Efield
                                (Ederef
                                  (Etempvar _d (tptr (Tstruct _doc noattr)))
                                  (Tstruct _doc noattr)) _child2
                                (tptr tvoid)))
                            (Scall (Some _t'11)
                              (Evar _evaluator_trivial (Tfunction
                                                         (Tcons tuint
                                                           (Tcons tuint
                                                             (Tcons
                                                               (tptr (Tstruct _doc noattr))
                                                               Tnil)))
                                                         (tptr (Tstruct _format_list noattr))
                                                         cc_default))
                              ((Etempvar _width tuint) ::
                               (Etempvar _height tuint) ::
                               (Etempvar _t'25 (tptr tvoid)) :: nil))))
                        (Scall (Some _t'12)
                          (Evar _choice_doc (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _format_list noattr))
                                                (Tcons
                                                  (tptr (Tstruct _format_list noattr))
                                                  Tnil))
                                              (tptr (Tstruct _format_list noattr))
                                              cc_default))
                          ((Etempvar _t'10 (tptr (Tstruct _format_list noattr))) ::
                           (Etempvar _t'11 (tptr (Tstruct _format_list noattr))) ::
                           nil)))
                      (Sreturn (Some (Etempvar _t'12 (tptr (Tstruct _format_list noattr))))))
                    (Ssequence
                      (Sset _t'21
                        (Efield
                          (Ederef (Etempvar _d (tptr (Tstruct _doc noattr)))
                            (Tstruct _doc noattr)) _type tuint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'21 tuint)
                                     (Econst_int (Int.repr 5) tint) tint)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'24
                                  (Efield
                                    (Ederef
                                      (Etempvar _d (tptr (Tstruct _doc noattr)))
                                      (Tstruct _doc noattr)) _child1
                                    (tptr tvoid)))
                                (Scall (Some _t'13)
                                  (Evar _evaluator_trivial (Tfunction
                                                             (Tcons tuint
                                                               (Tcons tuint
                                                                 (Tcons
                                                                   (tptr (Tstruct _doc noattr))
                                                                   Tnil)))
                                                             (tptr (Tstruct _format_list noattr))
                                                             cc_default))
                                  ((Etempvar _width tuint) ::
                                   (Etempvar _height tuint) ::
                                   (Etempvar _t'24 (tptr tvoid)) :: nil)))
                              (Ssequence
                                (Sset _t'23
                                  (Efield
                                    (Ederef
                                      (Etempvar _d (tptr (Tstruct _doc noattr)))
                                      (Tstruct _doc noattr)) _child2
                                    (tptr tvoid)))
                                (Scall (Some _t'14)
                                  (Evar _evaluator_trivial (Tfunction
                                                             (Tcons tuint
                                                               (Tcons tuint
                                                                 (Tcons
                                                                   (tptr (Tstruct _doc noattr))
                                                                   Tnil)))
                                                             (tptr (Tstruct _format_list noattr))
                                                             cc_default))
                                  ((Etempvar _width tuint) ::
                                   (Etempvar _height tuint) ::
                                   (Etempvar _t'23 (tptr tvoid)) :: nil))))
                            (Ssequence
                              (Sset _t'22
                                (Efield
                                  (Ederef
                                    (Etempvar _d (tptr (Tstruct _doc noattr)))
                                    (Tstruct _doc noattr)) _shift tulong))
                              (Scall (Some _t'15)
                                (Evar _fill_doc (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons
                                                        (tptr (Tstruct _format_list noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _format_list noattr))
                                                          (Tcons tulong Tnil)))))
                                                  (tptr (Tstruct _format_list noattr))
                                                  cc_default))
                                ((Etempvar _width tuint) ::
                                 (Etempvar _height tuint) ::
                                 (Etempvar _t'13 (tptr (Tstruct _format_list noattr))) ::
                                 (Etempvar _t'14 (tptr (Tstruct _format_list noattr))) ::
                                 (Etempvar _t'22 tulong) :: nil))))
                          (Sreturn (Some (Etempvar _t'15 (tptr (Tstruct _format_list noattr))))))
                        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                                         (tptr tvoid))))))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _list Struct
   (Member_plain _shift tulong :: Member_plain _line (tptr tschar) ::
    Member_plain _tail (tptr (Tstruct _list noattr)) :: nil)
   noattr ::
 Composite _t Struct
   (Member_plain _height tuint :: Member_plain _first_line_width tuint ::
    Member_plain _middle_width tuint ::
    Member_plain _last_line_width tuint ::
    Member_plain _to_text (tptr (Tstruct _list noattr)) :: nil)
   noattr ::
 Composite _string_list Struct
   (Member_plain _line (tptr tschar) ::
    Member_plain _tail (tptr (Tstruct _string_list noattr)) :: nil)
   noattr ::
 Composite _format_list Struct
   (Member_plain _G (tptr (Tstruct _t noattr)) ::
    Member_plain _tail (tptr (Tstruct _format_list noattr)) :: nil)
   noattr ::
 Composite _doc Struct
   (Member_plain _type tuint :: Member_plain _shift tulong ::
    Member_plain _child1 (tptr tvoid) :: Member_plain _child2 (tptr tvoid) ::
    nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_strlen, Gfun(Internal f_strlen)) :: (_strcpy, Gfun(Internal f_strcpy)) ::
 (_strcat, Gfun(Internal f_strcat)) :: (_max, Gfun(Internal f_max)) ::
 (_list_copy, Gfun(Internal f_list_copy)) ::
 (_new_list, Gfun(Internal f_new_list)) :: (_sp, Gfun(Internal f_sp)) ::
 (_get_applied_length, Gfun(Internal f_get_applied_length)) ::
 (_to_text_apply, Gfun(Internal f_to_text_apply)) ::
 (_less_components, Gfun(Internal f_less_components)) ::
 (_is_less_than, Gfun(Internal f_is_less_than)) ::
 (_empty, Gfun(Internal f_empty)) :: (_line, Gfun(Internal f_line)) ::
 (_newline, Gvar v_newline) ::
 (_format_copy, Gfun(Internal f_format_copy)) ::
 (_get_list_tail, Gfun(Internal f_get_list_tail)) ::
 (_list_concat, Gfun(Internal f_list_concat)) ::
 (_mdw_add_above, Gfun(Internal f_mdw_add_above)) ::
 (_to_text_add_above, Gfun(Internal f_to_text_add_above)) ::
 (_add_above, Gfun(Internal f_add_above)) ::
 (_mdw_add_beside, Gfun(Internal f_mdw_add_beside)) ::
 (_flw_add_beside, Gfun(Internal f_flw_add_beside)) ::
 (_line_concats, Gfun(Internal f_line_concats)) ::
 (_shift_list, Gfun(Internal f_shift_list)) ::
 (_to_text_add_beside, Gfun(Internal f_to_text_add_beside)) ::
 (_add_beside, Gfun(Internal f_add_beside)) ::
 (_mdw_add_fill, Gfun(Internal f_mdw_add_fill)) ::
 (_llw_add_fill, Gfun(Internal f_llw_add_fill)) ::
 (_flw_add_fill, Gfun(Internal f_flw_add_fill)) ::
 (_to_text_add_fill, Gfun(Internal f_to_text_add_fill)) ::
 (_add_fill, Gfun(Internal f_add_fill)) ::
 (_to_string, Gfun(Internal f_to_string)) ::
 (_total_width, Gfun(Internal f_total_width)) ::
 (_new_string_list, Gfun(Internal f_new_string_list)) ::
 (_split, Gfun(Internal f_split)) :: (_indent, Gfun(Internal f_indent)) ::
 (_clear_to_text, Gfun(Internal f_clear_to_text)) ::
 (_clear_format_list, Gfun(Internal f_clear_format_list)) ::
 (_max_width_check, Gfun(Internal f_max_width_check)) ::
 (_clear_last_format_element, Gfun(Internal f_clear_last_format_element)) ::
 (_indent_doc, Gfun(Internal f_indent_doc)) ::
 (_above_doc, Gfun(Internal f_above_doc)) ::
 (_fill_doc, Gfun(Internal f_fill_doc)) ::
 (_beside_doc, Gfun(Internal f_beside_doc)) ::
 (_format_list_copy, Gfun(Internal f_format_list_copy)) ::
 (_get_format_list_tail, Gfun(Internal f_get_format_list_tail)) ::
 (_choice_doc, Gfun(Internal f_choice_doc)) ::
 (_construct_doc, Gfun(Internal f_construct_doc)) ::
 (_evaluator_trivial, Gfun(Internal f_evaluator_trivial)) :: nil).

Definition public_idents : list ident :=
(_evaluator_trivial :: _construct_doc :: _choice_doc ::
 _get_format_list_tail :: _format_list_copy :: _beside_doc :: _fill_doc ::
 _above_doc :: _indent_doc :: _clear_last_format_element ::
 _max_width_check :: _clear_format_list :: _clear_to_text :: _indent ::
 _split :: _new_string_list :: _total_width :: _to_string :: _add_fill ::
 _to_text_add_fill :: _flw_add_fill :: _llw_add_fill :: _mdw_add_fill ::
 _add_beside :: _to_text_add_beside :: _shift_list :: _line_concats ::
 _flw_add_beside :: _mdw_add_beside :: _add_above :: _to_text_add_above ::
 _mdw_add_above :: _list_concat :: _get_list_tail :: _format_copy ::
 _newline :: _line :: _empty :: _is_less_than :: _less_components ::
 _to_text_apply :: _get_applied_length :: _sp :: _new_list :: _list_copy ::
 _max :: _strcat :: _strcpy :: _strlen :: _exit :: _free :: _malloc ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_fence :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


