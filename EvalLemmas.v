Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Require Import Translation.
Require Import WFLemmas.
Require Import SubstLemmas.
Require Import Types.
Require Import Judge.
Require Import Language.
Require Import ProgramLogic.
Require Import Tactics.

Open Scope pred.

Lemma var_val : 
  forall Γ x b φ w,  (x,{ ν : b | φ}) ∈ Γ -> 
                       sep_env Γ w -> 
                       (EX v : (base_of_type b), 
                               (fun s => eval s (var_e x) = Some (val_of_base b v))) w.
Proof.
  induction Γ. crush_sep False fail.  
  crush_sep False fail.
  fold (subst_pred (subst_one ν (var_e x)) (sep_base ν b0) w) in H.
  rewrite subst_vv_base_ap in H.
  apply H.
  crush_sep False fail.
Qed.

Lemma var_eval :
  forall Γ x b φ w, (x, { ν : b | φ }) ∈ Γ -> sep_env Γ w -> (EX v : value, (fun s => eval s (var_e x) = Some v)) w.
Proof.
  crush_sep False fail.
  apply var_val with (x := x) (b := b) (φ := φ)in H0 .
  destruct H0.
  destruct b. simpl in *. exists (int_v x0). assumption.
              simpl in *. exists (bool_v x0). assumption.
  assumption. 
Qed.

Lemma expr_eval : 
  forall Γ e b φ w, 
    sep_env Γ w -> expr_type Γ e { ν : b | φ } ->
                (EX v : value, (fun s => eval s e = Some v)) w.
Proof.
  autounfold in *. intros. 
  inversion H0. 
  subst.
  simpl. exists v. reflexivity.
  subst.
  apply var_eval with (Γ := Γ) (b := b) (φ := φ); crush.
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
    * simpl. pose (var_val Γ v b φ w H4 H). assumption.
Qed.

Lemma expr_eval_derives :
  forall Γ e b φ, 
    expr_type Γ e { ν : b | φ } -> (sep_env Γ) |-- (EX v : value, (fun s => eval s e = Some v)).
Proof.
  intros Γ e b φ T w Den_Γ.
  destruct e.
  exists v. reflexivity.
  apply var_eval with (x := v) (b := b) (φ := φ) in Den_Γ .
  auto. inversion T. apply H2.
Qed.

Lemma subst_env_eq_expr:
  forall G b x e w φ, 
    expr_type G e { ν : b | φ } ->
    sep_env G w ->
    (subst_pred (subst_one x e) (sep_env G)) w ->
    subst_pred (subst_one x e) (sep_env ((x, { ν : b | var_e ν .= e }) :: G)) w.
Proof.
  intros G b x e w φ etype senv H.
  pose (expr_eval_ty G e b φ w senv etype) as H0.
  rewrite subst_env_cons.
  split.
  unfold subst_pred.
  unfold subst_one.
  unfold sep_ty.
  split.
  unfold sep_base.
  unfold subst_one. 
  destruct H0.
  exists x0.
  simpl.
  destruct (eq_dec ν ν).
  simpl.
  destruct (eq_dec x x). assumption. contradiction n; reflexivity. contradiction n; reflexivity.

  unfold sep_pred.
  destruct H0.
  destruct b.
  simpl in x0.
  simpl in H0.
  exists (int_v x0).
  exists (int_v x0).
  constructor. constructor. constructor.
  simpl. unfold subst_one. simpl.
  destruct (eq_dec ν ν).
  simpl.
  destruct (eq_dec x x).
  symmetry.
  assumption.
  intuition.
  intuition.
  unfold subst_one.
  destruct e. 
  simpl. symmetry. apply H0.
  simpl. inversion etype. subst. simpl. 
  destruct (eq_dec v ν). simpl. 
  destruct (eq_dec x x). simpl. 
  symmetry. apply H0.
  intuition.
  intuition.
  destruct (eq_dec v x). symmetry. apply H0. symmetry. apply H0.
  
  simpl in *.
  symmetry in H0.
  exists (bool_v x0).
  exists (bool_v x0).
  repeat constructor.
  unfold subst_one. 
  destruct (eq_dec ν ν).
  simpl.
  destruct (eq_dec x x).
  simpl.
  apply H0. intuition. intuition.
  destruct e.
  apply H0.
  simpl. inversion etype. subst. 
  unfold subst_one.
  destruct (eq_dec v ν). simpl.
  destruct (eq_dec x x). 
  apply H0. intuition.
  destruct (eq_dec v x). apply H0. apply H0.
  assumption.
Qed.
