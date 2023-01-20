Require Import ZArith Int.
Require Import String.
Require Import Coq.Lists.List.

Record t : Type := T {
  height           : nat;
  first_line_width : nat;
  middle_width     : nat;
  last_line_width  : nat;
  to_text          : nat -> string -> string
}.

Definition less_components (G:t) (G':t): bool :=
  (G.(height) <=? G'.(height)) &&
  (G.(first_line_width) <=? G'.(first_line_width)) && 
  (G.(middle_width) <=? G'.(middle_width)) &&
  (G.(last_line_width) <=? G'.(last_line_width)).

Definition is_less_than  (G:t) (G':t): bool :=
  match G.(height), G'.(height) with
  | 1,1  => less_components G G'
  | _,1  => false
  | 1,_  => false
  | _,_  => less_components G G'
  end.

Definition empty: t := T 0 0 0 0 (fun s t => t).

Definition line (nt:string): t :=
  let length := String.length nt in
    T 1 length length length (fun s t => append nt t).

Definition newline := String (Ascii.ascii_of_N 10) EmptyString.

Fixpoint sp n :=
    match n with
    | O    => EmptyString
    | S n' => append " " (sp n')
    end.

Definition add_above (G:t) (G':t): t:=
  match G.(height), G'.(height) with
    | O, _ => G'
    | _, O => G
    | _, _ => 
      let middle_with_new :=
         match G.(height), G'.(height) with
         | 1,1 => G.(first_line_width)
         | 1,_ => max G'.(first_line_width) G'.(middle_width)
         | 2,1 => G.(last_line_width)
         | _,1 => max G.(last_line_width) G.(middle_width)
         | 2,_ => max G.(last_line_width) (max G'.(first_line_width) G'.(middle_width))
         | _,_ => max G.(middle_width)
                  (max G.(last_line_width)
                  (max G'.(first_line_width)
                       G'.(middle_width)))
         end
      in 
         T
         (G.(height) + G'.(height))
         G.(first_line_width)
         middle_with_new
         G'.(last_line_width)
         (fun s t => G.(to_text) s (append newline (append (sp s) (G'.(to_text) s t))))
  end.

Definition add_beside (G:t) (G':t):t :=
  match G.(height), G'.(height) with
    | O, _ => G'
    | _, O => G
    | _, _ => 
      let middle_width_new :=
         match G.(height), G'.(height) with
         | 1,(1|2) => G.(first_line_width) + G'.(first_line_width)
         | _,1     => G.(middle_width)
         | 1,_     => G.(last_line_width) + G'.(middle_width)
         | 2,_     => max (G.(last_line_width) + G'.(first_line_width))
                          (G.(last_line_width) + G'.(middle_width))
         | _,_     => max G.(middle_width)
                      (max (G.(last_line_width) + G'.(first_line_width))
                           (G.(last_line_width) + G'.(middle_width)))
         end
      in
        let first_line_width_new :=
           if (G.(height) =? 1) then 
              G.(first_line_width) + G'.(first_line_width) 
           else
              G.(first_line_width)
        in
           T
            (G.(height) + G'.(height) - 1)
            first_line_width_new
            middle_width_new 
            (G.(last_line_width) + G'.(last_line_width))
            (fun s t => G.(to_text) s (G'.(to_text) (s + G.(last_line_width)) t))
  end.

Definition add_fill (G:t) (G':t) (shift:nat) :t :=
  match G.(height), G'.(height) with
    | O, _ => G'
    | _, O => G
    | _, _ => 
      let middle_width_new :=
         match G.(height), G'.(height) with
         | 1,(1|2) => G.(first_line_width) + G'.(first_line_width)
         | 1,_ => shift + G'.(middle_width)
         | 2,1 => G.(first_line_width)
         | 2,2 => G.(last_line_width) + G'.(first_line_width)
         | 2,_ => max (G.(last_line_width) + G'.(first_line_width)) (shift + G'.(middle_width))
         | _,1 => G.(middle_width)
         | _,2 => max G.(middle_width) (G.(last_line_width) + G'.(first_line_width))
         | _,_ => max G.(middle_width)
                  (max (G.(last_line_width) + G'.(first_line_width))
                          (shift + G'.(middle_width)))
         end
      in
        let first_line_width_new :=
          if (G.(height) =? 1) then 
              G.(first_line_width) + G'.(first_line_width) 
          else 
              G.(first_line_width)
        in
          let last_line_width_new := 
            if (G'.(height) =? 1) then 
                G'.(last_line_width) + G.(last_line_width) 
            else 
                G'.(last_line_width) + shift
          in
            T
              (G.(height) + G'.(height) - 1)
              first_line_width_new
              middle_width_new
              last_line_width_new
              (fun s t => G.(to_text) s (G'.(to_text) (s + shift) t))
  end.

Definition to_string (f:t) := 
  match f with
  | T _ _ _ _ to_text => to_text 0 EmptyString
  end.

Definition total_width (f:t) := 
  match f with
  | T _ fw m lw _ => max fw (max m lw)
  end.

Definition split regexp :=
  let
   fix sp_helper pos s:=
     match s with
     | EmptyString => EmptyString::nil
     | String _ s' =>
         match pos with
         | 0 =>
            match index 0 regexp s with
            | Some n => 
               substring 0 n s::
                sp_helper (n - 1 + String.length regexp) s'
            | None   => s::nil
            end
         | _ => sp_helper (pos - 1) s'
         end
     end
  in sp_helper 0.

Definition of_string s :=
  let lines := split newline s in
  let lineFormats := map line lines in 
  fold_left add_above lineFormats empty.

Definition indent' shift f :=
  match f with
  | T h fw m lw to_text => T
    h
    (fw + shift)
    (m + shift)
    (lw + shift)
    (fun s t => append (sp shift) (to_text (s + shift) t))
  end.
