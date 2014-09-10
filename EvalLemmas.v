Add LoadPath "vst".
Require Import msl.Coqlib2.
Require Import msl.log_normalize.
Require Import msl.eq_dec.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Equality.

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
  forall Γ x b φ, 
    (x,{ ν : b | φ}) ∈ Γ ->
    sep_env Γ |-- (EX v : (base_of_type b),
                          (fun s => !!(eval s (var_e x) = val_of_base b v))).
Proof.
  induction Γ. 
  intuition.
  intuition.
  destruct H.
  + apply andp_left1. 
    apply andp_left1.
    apply andp_left1.
    destruct b.
    inversion H. subst. 
    apply andp_left1.
    apply exp_left.
    intro bb.
    apply andp_left1.
    apply (exp_right bb).
    apply derives_refl.
  + apply andp_left1.
    apply andp_left2.
    fold sep_env.
    apply IHΓ with (φ := φ).
    assumption.
Qed.

Lemma var_eval :
  forall Γ x b φ, 
    (x, { ν : b | φ }) ∈ Γ -> 
    sep_env Γ |-- (EX v : value, (fun s => !!(eval s (var_e x) = v))).
Proof.
  intros.
  pose (var_val Γ x b φ H).
  apply derives_trans with (Q := EX x0 : base_of_type b, (fun s => !!(eval s (var_e x) = val_of_base b x0))).
  assumption.
  destruct b.
  apply exp_left.
  intro xv.
  simpl.
  intro w.
  apply prop_left.
  intro.
  rewrite H0.
  simpl in xv.
  apply (exp_right (int_v xv)).
  apply prop_right.
  reflexivity.
Qed.

Lemma expr_eval :
  forall Γ Ξ e b φ,
    expr_type Γ Ξ e { ν : b | φ } ->
    sep_env Γ |-- (EX v : value, (fun s => !!(eval s e = v))).
Proof.
  intros.
  induction H.
  * apply (exp_right v). simpl. intro. apply prop_right. reflexivity.
  * apply var_eval with (Γ := Γ) (b := τ) (φ := φ0); assumption.
  * apply IHexpr_type. 
Qed.

Lemma expr_eval_ty :
  forall Γ Ξ e b φ,
    expr_type Γ Ξ e { ν : b | φ } ->
    sep_env Γ |-- 
      (EX v : base_of_type b , (fun s => !!(eval s e = val_of_base b v))).
Proof.
  intros.
  apply expr_eval with (e := e) (b := b) (φ := φ) (Ξ := Ξ) in H.
  apply derives_trans with 
    (Q := EX v : value, (fun s => !!(eval s e = v))).
  assumption.
  apply exp_left. intro vv.
  destruct b.
  destruct vv.
  simpl.
  intro w.
  apply prop_left.
  intro.
  apply (exp_right n).
  apply prop_right.
  assumption.
Qed.

Lemma exfalso_etype_fun :
  forall G Ξ f e1 e2 T,
    expr_type G Ξ (fun_e f e1 e2) T -> False.
Proof.
  intros.
  dependent induction H.
  auto.
Qed.

Lemma subst_env_eq_expr :
  forall G Grds b x e φ, 
    expr_type G Grds e { ν : b | φ } ->
    sep_env G && 
    (subst_pred (subst_one x e) (sep_env G))
    |-- subst_pred (subst_one x e) (sep_env ((x, { ν : b | var_e ν .= e }) :: G)).
Proof.
  intros.
  pose (expr_eval_ty G Grds e b φ H).
  rewrite subst_env_cons.
  apply derives_trans with (Q := sep_env G && subst_pred (subst_one x e) (sep_env G) && emp).
  apply andp_right. normalize. apply andp_left1. apply sep_env_pure.
  apply andp_derives.
  apply andp_derives.
  unfold sep_ty.
  destruct {ν : b | var_e ν .= e} eqn: T.
  inversion T. subst.
  rewrite subst_distr_andp.
  apply andp_right.
  apply derives_trans with 
   (Q := (EX v : base_of_type reft_base, (fun s => !!(eval s e = val_of_base reft_base v))) && emp).
    apply andp_right.
    assumption.
    apply sep_env_pure.
    unfold sep_env. 
    rewrite exp_andp1.
    apply exp_left. intro v. intro w. 
    (* apply prop_left. intro F. *)
    unfold sep_base, subst_one, subst, Subst_pred, subst_pred.
    simpl.
    apply andp_right.
    apply (exp_right v). 
    destruct (eq_dec x x). 
      apply derives_refl.
      congruence.
    apply andp_derives.
    unfold subst, Subst_pred, subst_pred. simpl.
    unfold subst, Subst_pred, Subst_var_expr, subst_pred.
    destruct (eq_dec ν ν).
    simpl.
    destruct e.
    simpl.
    destruct (eq_dec x x).
    simpl.
    normalize.
    normalize.
    congruence.
    normalize.
    destruct (eq_dec x x).
    simpl.
    destruct (eq_dec v0 ν).
    simpl.
    destruct (eq_dec x x).
    reflexivity.
    congruence.
    simpl.
    destruct (eq_dec v0 x).
    reflexivity.
    reflexivity.
    congruence.
    exfalso; eapply exfalso_etype_fun; eauto.
    congruence.
    normalize.
    apply sep_env_pure.
    normalize.
    normalize.
Qed.