Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Require Import Types.
Require Import Judge.
Require Import Translation.
Require Import Language.
Require Import ProgramLogic.
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
  + unfold sep_base.
    apply expr_eval_ty with (Γ := Γ) (φ := φ).
    assumption. assumption.
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
  forall Φ Γ Γ' x e (J : (Φ / Γ ⊢ assign_s x e ::: Γ')), x <> ν -> 
    {{ sep_env Γ }} assign_s x e {{ sep_env Γ' }}.
Proof.
  intros Φ Γ Γ' x e J NotVV.
  inversion J. subst.
  apply semax_pre_post with (P' := EX v : value, eval_to e v 
                                              && subst_pred x e (sep_env ((x, {ν : τ | (var_e ν) .= e }) :: Γ)))
                            (Q' := sep_env ((x,{ν : τ | (var_e ν) .= e }) :: Γ)).
  unfold derives.
  simpl.
  intro w. intro SE.
  assert (exists b, eval_to e b w) as ExVal.
    apply expr_eval with (Γ := Γ) (T := { ν : τ | φ }). apply SE. apply H5.
  destruct ExVal. exists x0.
  split. apply H. simpl.
  split. split.
  inversion H5. 
  unfold sep_base. subst. destruct v. simpl. exists n. destruct (eq_dec x x). reflexivity. contradiction n0. reflexivity.
  exists b. simpl. destruct (eq_dec x x). reflexivity. contradiction n. reflexivity.
  subst. unfold sep_base. 
  apply expr_eval_ty with (Γ := Γ) (φ := φ). 

exists x0.
  apply subst_none_base with (x := x) (e := e).
  destruct ExVal.
  exists x0. 
  split.
    assumption. 
    split. split. 
    unfold sep_base. 
    pose (expr_eval' Γ (var_e x) τ φ) as E'. 
    eapply E'. 
    split.
    unfold derives in E'.
    exists (val_of_base τ x0).
        (* destruct H3. unfold imp in H1. apply H1. *)
  split. split.
    apply SE.
    apply H5.
  elim ExVal.
    intro val. intro EvalTo.
  exists val.
  destruct t as [ν τ φ].
  hnf.
  split.
    apply EvalTo.
    split. split.

(* (*** The main thingie ***) *)
(* Theorem sep_type : *)
(*   forall Φ Γ s Γ', *)
(*     Φ / Γ ⊢ s ::: Γ' ->  *)
(*     {{ sep_env Γ }} s {{ sep_env Γ' }}. *)
(* Proof. *)
(*   intros. *)
(*   destruct s. *)