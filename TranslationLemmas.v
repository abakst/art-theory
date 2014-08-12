Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Require Import Types.
Require Import Judge.
Require Import ProgramLogic.
Require Import Translation.
Require Import Language.
Require Import WFLemmas.
Require Import SubstLemmas.
Require Import EvalLemmas.
Require Import Tactics.

Lemma type_interp :
  forall Γ x T s,
      sep_env Γ s -> (expr_type Γ (var_e x) T) -> sep_ty x T s.
Proof.
  intros Γ x [ ν b φ ] w SE ET.
  unfold sep_ty.
  inversion ET. subst.
  split.
  + fold (subst_pred (subst_one ν (var_e x)) (sep_base ν b) w).
    rewrite subst_vv_base_ap. 
    apply expr_eval_ty with (Γ := Γ) (φ := φ).
    apply SE.
    apply ET.
  + generalize dependent Γ. 
    induction Γ. 
    - intros. inversion H2.
    - intros. apply in_inv in H2. destruct a. destruct H2.
      * inversion H. subst. apply SE.
      * apply IHΓ. unfold sep_env in SE.
        {
          apply SE. 
        } 
        {
          apply H. 
        } 
        { 
          inversion ET. 
          subst.
          apply in_inv in H3. destruct H3. 
          { 
            inversion H0. subst. constructor. apply H.
          }
          {
            constructor. apply H0.
          }
        }
Qed.

Lemma sep_proof_skip :
  forall Φ Γ Γ' (J : (Φ / Γ ⊢ skip_s ::: Γ')), 
    {{ sep_env Γ }} skip_s {{ sep_env Γ' }}.
Proof.
  intros. inversion J. constructor.
Qed.


Lemma sep_proof_assign :
  forall Φ Γ Γ' x e (J : (Φ / Γ ⊢ assign_s x e ::: Γ')), 
    wf_env Γ ->
    {{ sep_env Γ }} assign_s x e {{ sep_env Γ' }}.
Proof.
  intros Φ Γ Γ' x e J wfenv.
  inversion J. subst.
  apply semax_pre_post with (P' := EX v : value, (eval_to e v)
                                              && (subst_pred (subst_one x e )
                                                             (sep_env ((x, {ν : τ | (var_e ν) .= e }) :: Γ))))
                            (Q' := sep_env ((x,{ν : τ | (var_e ν) .= e }) :: Γ)).
  intro w. intro SE.
  pose (expr_eval Γ e τ φ w SE H6) as ValWit. 
  destruct ValWit.
  exists x0. split. apply H.
  apply subst_env_eq_expr with (φ := φ).
  assumption.
  assumption.
  rewrite subst_dom_env.
  assumption.
  assumption.
  split. unfold subst_one. destruct (eq_dec ν x). subst. contradiction H1. reflexivity. reflexivity.
  intros x' x'_in_ctx.
  unfold subst_one. destruct (eq_dec x' x). subst. 
  unfold var_in in *.
  unfold var_not_in in *. rewrite Forall_forall in H4. destruct (x'_in_ctx). apply H4 in H0. 
  contradiction H0. reflexivity. reflexivity.
  unfold subst_one. destruct (eq_dec ν x). subst. contradiction H1. reflexivity. reflexivity.
  auto.
  apply semax_assign with (e := e) (x := x) (P := (sep_env ((x, {ν : τ | var_e ν .= e}) :: Γ))).
Qed.

Theorem sep_proof_stmt :
  forall Φ Γ Γ' s (J : (Φ / Γ ⊢ s ::: Γ')),
    wf_env Γ ->
    {{ sep_env Γ }} s {{ sep_env Γ' }}.
Proof.
  intros.
  destruct s.
  + apply sep_proof_skip with (Φ := Φ). assumption.
  + apply sep_proof_assign with (Φ := Φ); assumption.
  + admit.
  + induction J.
    * apply semax_skip.
    * admit.
    * apply sep_proof_assign with (Φ := Φ). apply t_assign with (φ := φ); assumption. assumption.
    * apply semax_seq with (Q := sep_env Γ'). apply IHJ1. assumption. apply IHJ2. 
      apply wf_env_stmt with (P := Φ) (G := Γ) (s := s0); assumption.
Qed.

Corollary type_safety :
  forall Φ s Γ,
    Φ / nil ⊢ s ::: Γ -> {{ TT }} s {{ TT }}.
Proof.
  intros.
  assert (wf_env nil). constructor.
  apply semax_pre_post with (P' := sep_env nil) (Q' := sep_env Γ);
  first [ constructor | apply sep_proof_stmt with (Φ := Φ); assumption].
Qed.