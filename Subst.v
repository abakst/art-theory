Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import List.

Definition subst_t (X : Type) := list (X * X).

(* Definition wf_subst{A : Type} (s : subst_t A) : Prop  := NoDup (fst (split s)). *)

Class Subst (A X : Type) : Type :=
  subst: subst_t X -> A -> A.

Fixpoint subst_list (A X : Type) (SAX : Subst A X) (s : subst_t X) (l : list A) :=
  match l with
    | nil => nil
    | h :: t => subst s h :: subst_list A X SAX s t
  end.
  
Instance Subst_list (A X : Type) (SAX : Subst A X) : Subst (list A) X := subst_list A X SAX.