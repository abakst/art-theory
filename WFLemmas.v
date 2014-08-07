Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Require Import Translation.
Require Import Types.
Require Import Judge.
Require Import Language.
Require Import Subst.
Require Import Tactics.

Lemma fresh_var :
  forall x t Γ,
    var_not_in x Γ -> In (x,t) Γ -> False.
Proof.
  unfold var_not_in in *; pair_crush.
Qed.

Lemma var_not_in_exp :
  forall x e Γ,
    (x <> ν) -> var_not_in x Γ -> wf_expr Γ e -> (e <> (var_e x)).
Proof.
  intros x e Γ neq not_in wf_exp;
  inversion wf_exp; crush' fresh_var fail.
Qed.

Ltac wf_freshvar exp :=
  match goal with
    | [ x:var, G:type_env, V:var_not_in ?x ?G, H: wf_expr ?G _ |- _ ] => 
      let V1 := fresh "V"  in
      set (V1 := V);
      eapply var_not_in_exp with (e := exp) in V1
   end.

Lemma wf_env_ty :
  forall Γ x t, 
    wf_env Γ -> (x, t) ∈ Γ -> wf_type Γ t.
Proof.
  pair_crush' False wf_env.
Qed.

Lemma wf_type_prop : 
  forall Γ ν τ φ,
    wf_type Γ { ν : τ | φ } -> wf_prop Γ φ.
Proof.
  pair_crush' False wf_type.
Qed.

Lemma wf_expr_subst :
  forall Γ e x,
    wf_expr Γ e -> var_in x Γ ->
    wf_expr Γ (subst ((ν, x) :: nil) e).
Proof.
  intros; unfold var_in in *; destruct e; 
  repeat
    (match goal with
       | [ |- context[subst _ _] ] => unfold subst; simpl
       | [ |- context[eq_dec ?x ?v] ] => destruct (eq_dec x v)
     end; crush' wf_var fail).
Qed.

Lemma wf_prop_subst :
  forall Γ φ x,
    wf_prop Γ φ -> var_in x Γ ->
    wf_prop Γ (subst ((ν, x) :: nil) φ).
Proof.
  induction φ; intros; constructor; crush' wf_expr_subst ((wf_type, wf_prop), wf_expr).
Qed.

Lemma wf_env_prop :
  forall Γ x ν τ φ, 
    wf_env Γ -> (x, { ν : τ | φ }) ∈ Γ -> wf_prop Γ φ.
Proof.
  intros;
  apply wf_type_prop with (ν := ν) (τ := τ);
  apply wf_env_ty with (x := x); crush.
Qed.

Lemma wf_not_in :
  forall x t x' Γ,
    var_not_in x' Γ -> wf_type Γ t -> (x,t) ∈ Γ ->
    x <> x'.
Proof.
  intros; unfold var_not_in in *; crush; app_pair; crush.
Qed.