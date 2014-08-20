Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import List.
Import ListNotations.

Definition subst_t (D : Type) (R : Type) := D -> R.

(* Definition wf_subst{A : Type} (s : subst_t A) : Prop  := NoDup (fst (split s)). *)

Class Subst (A D R : Type) : Type :=
  subst: subst_t D R -> A -> A.

Fixpoint subst_prod (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R) (s : subst_t D R) (p : (A * B)) :=
  match p with
    | (p1, p2) => (subst s p1, subst s p2)
  end.

Instance Subst_prod (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R): Subst (A * B) D R := 
  subst_prod A B D R SA SB.

Fixpoint subst_list (A D R : Type) (SA : Subst A D R) (s : subst_t D R) (l : list A) :=
  match l with
    | nil => []
    | h :: t => subst s h :: subst_list A D R SA s t
  end.
  
Instance Subst_list (A D R : Type) (SA : Subst A D R) : Subst (list A) D R := 
  subst_list A D R SA.
(* Instance Subst_prod_list (A B D R : Type) (S : Subst A D R) : Subst (list (A * A)) D R := _. *)
(* Definition wf_subst (X : Type) (s : subst_t X) := *)
(*   NoDup (fst (split s)). *)