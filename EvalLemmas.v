Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Require Import Translation.
Require Import WFLemmas.
Require Import SubstLemmas.
Require Import Types.
Require Import Judge.
Require Import Language.
Require Import Tactics.

Lemma var_val : 
  forall Γ x ν b φ w,  (x,{ ν : b | φ}) ∈ Γ -> 
                       sep_env Γ w -> 
                       (EX v : (base_of_type b), 
                               (fun s => eval s (var_e x) = Some (val_of_base b v))) w.
Proof.
  induction Γ; repeat crush_sep False fail.  
Qed.

Lemma var_eval :
  forall Γ x t w, (x,t) ∈ Γ -> sep_env Γ w -> (EX v : value, (fun s => eval s (var_e x) = Some v)) w.
Proof.
  destruct t as [ν b φ]; crush_sep var_val fail.
Qed.

Lemma expr_eval : 
  forall Γ e T w, 
    sep_env Γ w -> expr_type Γ e T ->
                (EX v : value, (fun s => eval s e = Some v)) w.
Proof.
  autounfold in *. intros. crush_sep False fail. 
  destruct e as [v | x]. 
    crush_sep False fail.
    inversion H0; apply var_eval with (Γ := Γ) (t:= T);
    crush.
Qed.

Lemma expr_eval_ty :
  forall Γ e b φ w, 
    sep_env Γ w -> expr_type Γ e { ν : b | φ } -> 
      (EX v : base_of_type b , (fun s => eval s e = Some (val_of_base b v))) w.
Proof.
  autounfold in *. intros.
  destruct e. 
  + destruct b.
  - inversion H0. subst.
    destruct v. 
    * simpl. exists n. reflexivity.
    * simpl. exists b. reflexivity.
  - inversion H0. subst.
    destruct v.
    * simpl. exists n. reflexivity.
    * simpl. exists b. reflexivity.
  + inversion H0. subst.
    * simpl. pose (var_val Γ v ν b φ w H4 H). assumption.
Qed.

Lemma expr_eval_derives :
  forall Γ e t,
    expr_type Γ e t -> (sep_env Γ) |-- (EX v : value, (fun s => eval s e = Some v)).
Proof.
  intros Γ e t T w Den_Γ.
  destruct e.
  exists v. reflexivity.
  apply var_eval with (x := v) (t:=t) in Den_Γ .
  auto. inversion T. apply H1.
Qed.