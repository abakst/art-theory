Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.
Require Import List.
Import ListNotations.

Require Import Translation.
Require Import Types.
Require Import Judge.
Require Import Language.
Require Import Subst.
Require Import Tactics.

Lemma subst_distr_pair :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R) 
         (θ : subst_t D R)  (x : A) (y : B),
    subst θ (x, y) = (subst θ x, subst θ y).
Proof.
  auto.
Qed.

Lemma subst_distr_pair_cons :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R) 
         (θ : subst_t D R) (x : A) (y : B) (l : list (A * B)),
    subst θ ((x, y) :: l) = ((subst θ x, subst θ y) :: subst θ l).
Proof.
  auto.
Qed.

Lemma subst_distr_cons :
  forall (A D R : Type) (SA : Subst A D R)
         (θ : subst_t D R) (x : A) (l : list A),
    subst θ (x :: l) = (subst θ x :: subst θ l).
Proof.
  auto.
Qed.

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

Lemma wf_type_prop : 
  forall Γ ν τ φ,
    wf_type Γ { ν : τ | φ } -> wf_prop Γ φ.
Proof.
  pair_crush' False wf_type.
Qed.

Ltac invert_wf_expr :=
  match goal with
    | [ e1 : expr, e2 : expr, H : wf_expr _ (fun_e _ ?e1 ?e2) |- appcontext[?e1] ] =>
      inversion H; crush
    | [ e1 : expr, e2 : expr, H : wf_expr _ (fun_e _ ?e1 ?e2) |- appcontext[?e2] ] =>
      inversion H; crush
  end.

Ltac break_wf_e := 
  repeat constructor; 
  unfold subst in *;
  unfold subst_var_one in *;
  simpl;
  invert_wf_expr.

Hint Unfold subst.
Hint Unfold subst_var_one.

Lemma wf_expr_subst :
  forall Γ e x,
    wf_expr Γ e -> var_in x Γ ->
    wf_expr Γ (subst (subst_var_one ν x) e).
Proof.
  intros; unfold var_in in *; induction e; autounfold in *; simpl;
  first [
      break_wf_e
    | match goal with
        | [ |- context[eq_dec ?x ?v] ] => destruct (eq_dec x v); crush' wf_var fail
        | _ => crush
      end 
    ].
Qed.

Lemma wf_prop_subst :
  forall Γ φ x,
    wf_prop Γ φ -> var_in x Γ ->
    wf_prop Γ (subst (subst_var_one ν x) φ).
Proof.
  induction φ; intros; constructor; crush' wf_expr_subst ((wf_type, wf_prop), wf_expr).
Qed.

Lemma wf_not_in :
  forall x t x' Γ,
    var_not_in x' Γ -> wf_type Γ t -> (x,t) ∈ Γ ->
    x <> x'.
Proof.
  intros; unfold var_not_in in *; crush; app_pair; crush.
Qed.

Lemma wf_expr_cons :
  forall G e v t,
         wf_expr G e -> wf_expr ((v,t) :: G) e.
Proof.
  intros.
  induction H.
  + constructor.
  + apply in_cons with (a:=(v,t)) in H. apply wf_var with (t:=t0). assumption.
  + constructor.
  + constructor. apply IHwf_expr1. apply IHwf_expr2.
Qed.

Lemma wf_env_ty_cons :
  forall G t v' t',
    wf_type G t -> wf_type ((v',t') :: G) t.
Proof.
  intros.
  inversion H. subst.
  induction H0.
  + constructor. constructor.
  + constructor. constructor; apply wf_expr_cons; assumption.
  + constructor. constructor. 
    specialize (IHwf_prop (wf_reft_t Γ b p H0)). inversion IHwf_prop. subst. assumption.
  + constructor. constructor.
    inversion H. subst.
    specialize (IHwf_prop1 (wf_reft_t Γ b p1 H0_)).
    inversion IHwf_prop1. assumption. 
    specialize (IHwf_prop2 (wf_reft_t Γ b p2 H0_0)).
    inversion IHwf_prop2. assumption. 
  + constructor. constructor.
    inversion H. subst.
    specialize (IHwf_prop1 (wf_reft_t Γ b p1 H0_)).
    inversion IHwf_prop1. assumption.
    specialize (IHwf_prop2 (wf_reft_t Γ b p2 H0_0)).
    inversion IHwf_prop2. assumption. 
Qed.
  
Lemma wf_env_ty :
  forall G x t,
    (x,t) ∈ G  -> wf_env G -> wf_type G t.
Proof.
  induction G as [ | [x' t']].
  + intros. inversion H.
  + intros. (* unfold In in H. destruct H. *)
    apply in_inv in H.
    destruct H.
    inversion H.
    subst.
    inversion H0.
    assumption.
    apply wf_env_ty_cons.
    apply IHG with (x:= x).
    assumption.
    inversion H0.
    subst.
    assumption.
Qed.

Lemma wf_env_ty_binding :
  forall G x b p,
    wf_env G ->
    (x, { ν : b | p }) ∈ G ->
    wf_type G { ν : b | p }.
Proof.
  intros.
  apply wf_env_ty with (x := x) (t := { ν : b | p }); assumption.
Qed.

Lemma wf_env_expr_ty :
  forall G e b p,
    wf_env G ->
    expr_type G e { ν : b | p } -> 
    wf_type G { ν : b | p }.
Proof.
  intros G e b p wfenv etype.
  inversion etype. 
  + constructor; repeat constructor.
  + subst. apply wf_env_ty_binding with (x := x) (b := b) (p := p) in wfenv; assumption.
  + assumption.
Qed.

Lemma wf_env_stmt :
  forall P G G' s,
    wf_env G ->
    P / G ⊢ s ::: G' ->
    wf_env G'.
Proof.
  intros P G G' s WF J.
  induction J.
  + assumption.
  + assumption. 
  + apply wf_env_var. assumption. assumption. assumption.
      constructor.
      constructor.
      constructor.
      subst.
      induction H1. constructor.
      apply wf_var with (t := { ν : τ0 | φ0}).
      unfold In. right. assumption.
      apply IHexpr_type; assumption.
  + apply IHJ2. apply IHJ1. assumption.
Qed.

Lemma wf_schema_ret_not_vv :
  forall S,
    wf_schema S -> fst (s_ret S) <> ν.
Proof.
  intros.
  inversion H.
  inversion H2.
  subst.
  destruct S as [xs ts [xret tret]]. simpl in *.
  inversion H4. subst.
  assumption.
Qed.

Lemma wf_env_no_vv :
  forall Γ,
    wf_env Γ -> var_not_in ν Γ.
Proof.
  induction Γ.
  + intuition.
  + destruct a as [ x t ].
    intro wf.
    inversion wf.
    subst.
    unfold var_not_in in *. rewrite Forall_forall in *.
    intros [ x' t' ].
    intro x'in.
    apply in_inv in x'in.
    destruct x'in.
    inversion H.
    subst.
    assumption.
    apply IHΓ.
    assumption.
    assumption.
Qed.

Hint Unfold wf_subst.
Lemma wf_subst_split :
  forall θ,
    wf_subst θ -> (θ ν = ν /\ forall v, θ v = ν -> v = ν).
Proof.
  intros.
  unfold wf_subst in H.
  split.
  apply H; reflexivity.
  apply H.
Qed.

Ltac wfsubst x :=
  let H := fresh "H" in
  pose (H := wf_subst_split x);
    match goal with
      | G : wf_subst _ |- _ =>
        specialize (H G); destruct H
    end.