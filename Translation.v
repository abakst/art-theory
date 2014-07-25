Add LoadPath "vst".
Require Import Types.
Require Import ProgramLogic.
Require Import Language.
Require Import Judge.
Require Import Subst.
Require Import List.
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Open Scope pred.

Definition sep_base (x:var) (t:base_type) : pred world :=
  match t with
    | int_t => EX v : nat, (fun s => (eval s (var_e x) = Some (int_v v)))
    | bool_t => EX v : bool, (fun s => (eval s (var_e x) = Some (bool_v v)))
  end.

Fixpoint sep_pred (p:reft_prop) : pred world :=
  match p with
    | tt_r  => TT
    | rel_r e1 o e2 =>
      match o with
        | eq_brel => 
          EX v1 : value, EX v2 : value, 
             !! (v1 = v2) 
          && (fun s => Some v1 = (eval s e1)) 
          && (fun s => Some v2 = (eval s e2))
        | lt_brel => 
          EX v1 : nat, EX v2 : nat, 
             !! (v1 < v2) 
          && (fun s => Some (int_v v1) = (eval s e1)) 
          && (fun s => Some (int_v v2) = (eval s e2))
      end
    | not_r p => imp (sep_pred p) FF
    | and_r p1 p2 => sep_pred p1 && sep_pred p2
    | or_r p1 p2 => sep_pred p1 || sep_pred p2
  end.

Definition sep_ty (x:var) (t:reft_type) : pred world :=
  match t with
  | mkReft_type v b p => sep_base x b && sep_pred (subst ((v,x) :: nil) p)
  end.

Fixpoint sep_env (Γ : type_env) : pred world :=
  match Γ with
    | nil => TT
    | (x,t) :: Γ' => sep_ty x t && sep_env Γ'
  end.

Lemma var_eval :
  forall Γ x t,  (x,t) ∈ Γ -> (sep_env Γ |-- (fun s => eval s (var_e x) <> None)).
Proof.
  intros Γ.
  induction Γ as [ | xt].
  intros x t X w H v. auto.
  intros x t X w H v.
  specialize IHΓ with (x := x) (t := t).
  destruct t as [ vv b p ].
  apply in_inv in X.
  destruct X.
  (* assert (w x <> None). *)
  unfold sep_env in H. simpl in *. unfold sep_ty in H. unfold sep_pred in H.
  subst.
  destruct H as [[A B] C]. 
  clear B C.
  unfold sep_base in A. destruct b. 
   simpl in *.
     unfold exp in A. 
     rewrite v in A. elim A. intros. inversion H. 
   simpl in *.
    unfold exp in A.
    rewrite v in A. elim A. intros. inversion H.
  assert (eval w x <> None).
  apply IHΓ.
  apply H0.
  unfold sep_env in H. destruct xt. destruct H as [A B].
  fold sep_env in B. apply B. rewrite v in H1. auto.
Qed.

(* Lemma expr_eval :
  forall Γ e t,
    expr_type Γ e t -> (sep_env Γ) |-- (EX v : value, (fun s => eval s e = Some v)).
Proof.
  Admitted.
Qed. *)
