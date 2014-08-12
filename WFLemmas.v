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

Lemma wf_not_in :
  forall x t x' Γ,
    var_not_in x' Γ -> wf_type Γ t -> (x,t) ∈ Γ ->
    x <> x'.
Proof.
  intros; unfold var_not_in in *; crush; app_pair; crush.
Qed.

Lemma wf_env_ty_cons :
  forall G t v' t',
    wf_type G t -> wf_type ((v',t') :: G) t.
Proof.
  intros.
  inversion H. subst.
  induction H0.
  + constructor. constructor.
  + constructor. constructor. 
    destruct e1. 
      constructor. 
      inversion H0. subst. apply in_cons with (a := (v',t')) in H4. apply wf_var with (t:=t). assumption.
      constructor.
    destruct e2.
      constructor.
      inversion H1. subst. apply in_cons with (a := (v',t')) in H4. apply wf_var with (t:=t). assumption.
      constructor.
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
  + intros. unfold In in H. destruct H.
    inversion H0. 
    inversion H7.
    inversion H.
    subst.
    apply wf_env_ty_cons. destruct t as [ vv bb tt ]. inversion H13. subst. apply H7.
    fold (In (x,t) G) in H. apply wf_env_ty_cons. apply IHG with (x := x). assumption.
    inversion H0. subst.
    assumption.
Qed.

Lemma wf_env_ty_binding :
  forall G x b p,
    wf_env G ->
    (x, { ν : b | p }) ∈ G ->
    wf_type G { ν : b | p }.
Proof.
  induction G as [ | [x' t'] G ].
  + intros. inversion H0.
  + intros. apply wf_env_ty_cons. 
    apply in_inv in H0.
    destruct H0.
    inversion H0. subst.
    inversion H. assumption.
    apply IHG with (x := x).
    inversion H. assumption.
    assumption.
Qed.

(* apply IHG. inversion H. subst. assumption. *)

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
  + admit.
  + apply wf_env_var. assumption. assumption. assumption.
    constructor.
    constructor.
    constructor.
    destruct e.
    constructor.
    inversion H1.
    subst. 
    apply wf_var with (t := { ν : τ | φ }).
    assumption.
  + apply IHJ2. apply IHJ1. assumption.
Qed.
    
    