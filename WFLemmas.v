Add LoadPath "vst".
Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import msl.Coqlib2.
Require Import msl.log_normalize.

Require Import Translation.
Require Import Types.
Require Import Language.
Require Export ProgramLogic.
Require Import Subst.
Require Import Tactics.
Require Import Judge.

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

Lemma wf_expr_ty_expr :
  forall Γ Ξ e T,
    expr_type Γ Ξ e T -> 
    wf_expr Γ e.
Proof.
  intros ? ? ? ? H.
  dependent induction H.
  + constructor.
  + apply wf_var with { ν : τ | φ }. 
    assumption.
  + apply IHexpr_type.
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

Lemma wf_env_cons_ty :
  forall G x t,
    wf_env ((x,t) :: G) -> wf_type ((x,t) :: G) t.
Proof.
  intros.
  apply wf_env_ty with (x := x).
  left. reflexivity.
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
  forall G Grd e b p,
    wf_env G ->
    expr_type G Grd e { ν : b | p } -> 
    wf_type G { ν : b | p }.
Proof.
  intros G Grd e b p wfenv etype.
  inversion etype. 
  + constructor; repeat constructor.
  + subst. apply wf_env_ty_binding with (x := x) (b := b) (p := p) in wfenv; assumption.
  + assumption.
Qed.

Lemma wf_env_nonmem :
  forall x t G, (x,t) ∈ G -> wf_env G -> x <> ν.
Proof.
  induction G as [| [x' t']].
  + intuition.
  + intros InH WfH.
    apply in_inv in InH.
    inversion WfH. subst.
    destruct InH. 
    inversion H.
    subst.
    assumption.
    apply IHG; assumption.
Qed.

Lemma wf_env_join :
  forall  (X : guards) (G G' G'' : type_env),
      join_env X G' G'' G -> wf_env G.
Proof. 
  intros. apply H.
Qed.

Lemma wf_heap_cons_env :
  forall G H x t,
    bind_not_in x H ->
    wf_heap G H -> wf_heap ((x,t) :: G) H.
Proof.
  intros G H x t nomem wf.
  induction H.
  + constructor.
  + inversion wf.
    subst.
    constructor; try assumption.
    unfold bind_not_in in nomem.
    rewrite Forall_forall in nomem.
    unfold var_not_in.
    rewrite Forall_forall.
    intros [x' t'] [x'mem | x'mem].
    inversion x'mem; subst.
    specialize (nomem (l , (x0, t0))).
    intro F.
    apply nomem. left. reflexivity. simpl in F. simpl. congruence.
    unfold var_not_in in H4.
    rewrite Forall_forall in H4.
    apply (H4 (x',t')). assumption.
    apply wf_env_ty_cons. assumption.
Qed.

Ltac freshvar :=
  match goal with 
    | [ H : fresh ?v _ _ |- ?v <> ν ] =>
      apply H
    | [ H : fresh ?v _ _ |- var_not_in ?v _ ] =>
      apply H
    | [ H : fresh ?v _ _ |- bind_not_in ?v _ ] =>
      apply H
  end.
    
Ltac varin :=
  try (assumption || congruence );
  match goal with
    | H : (?x, _) ∈ _ |- (?x, _) ∈ _ => eapply H
    | H : (?x, _ ) ∈ ?G |- (?x, _) ∈ (_ :: ?G) =>
      first [ right; varin | left; varin ]
    | _ => idtac
  end.

Ltac wellformed_expr :=
  try first [ constructor 
            | eapply wf_var; try varin ].

Ltac wellformed :=
  match goal with
    | |- wf_type _ _ => constructor; wellformed
    | |- wf_prop _ _ => constructor; wellformed
    | |- wf_expr _ _ => constructor; wellformed
    | H : expr_type _ _ ?e _ |- wf_expr _ ?e => induction H; wellformed_expr
  end.
    
Lemma wf_env_stmt :
  forall P G G' H H' X s,
    wf_env G ->
    (P ; G ; H ; X) ⊢ s ::: (G' ; H') ->
    wf_env G'.
Proof.
  intros P G G' H H' X s WF J.
  induction J.
  + assumption.
  + assumption. 
  + apply wf_env_var; try first [assumption | freshvar | wellformed].
    apply IHexpr_type; assumption.
  + apply wf_env_var; ( assumption || constructor || freshvar || wellformed ); constructor.
  + apply wf_env_join with (X := Ξ) (G' := Γ1) (G'' := Γ2); assumption.
  + apply IHJ2; apply IHJ1; assumption.
Qed.

Lemma wf_heap_stmt :
  forall P G G' H H' X s,
    wf_heap G H ->
    (P ; G ; H ; X) ⊢ s ::: (G' ; H') ->
    wf_heap G' H'.
Proof.
  intros until s. intros wf judge.
  induction judge.
  + assumption.
  + admit.
  + apply wf_heap_cons_env. 
    unfold var_not_in in H0. rewrite Forall_forall in H0.
    unfold bind_not_in. rewrite Forall_forall.
    intros [l [x t]] xin. simpl.
    inversion wf; subst. inversion xin. subst.
    apply (H0 (x, t)).
    apply in_inv in xin.
    destruct xin.
    inversion H7. subst.
    assumption.

Lemma wf_guards_cons :
  forall Γ Ξ xt,
    wf_guards Γ Ξ -> wf_guards (xt :: Γ) Ξ.
Proof.
  intros.
  assert (I :forall ξ, wf_guard Γ ξ -> wf_guard (xt :: Γ) ξ).
  {
    intros ξ wfg.
    unfold wf_guard in *.
    split.
    destruct wfg as [wf vvmem].
    induction wf.
    + constructor.
    + constructor; destruct xt as [x t]; apply wf_expr_cons; assumption.
    + constructor. apply IHwf. assumption. apply vvmem.
    + constructor. 
      apply IHwf1. assumption. simpl in vvmem. solve [intuition].
      apply IHwf2. assumption. simpl in vvmem. solve [intuition].
    + constructor. 
      apply IHwf1. assumption. simpl in vvmem. solve [intuition].
      apply IHwf2. assumption. simpl in vvmem. solve [intuition].
    + apply wfg.
  }
  unfold wf_guards in *.
  rewrite Forall_forall in *.
  intros ξ xmem.
  specialize (H ξ).
  apply I.
  apply H.
  apply xmem.
Qed.

Lemma env_monotonic :
  forall P X G G' s,
    (P ; G ; X) ⊢ s ::: G' ->
    Forall (fun xt => xt ∈ G') G.
Proof.
  intros.
  rewrite Forall_forall.
  induction H.
  + auto.
  + intros x xin.
    right. assumption.
  + intros x xin.
    right. assumption.
  + intros x' x'in. 
    unfold join_env in H2.
    destruct H2.
    destruct H3.
    specialize (H3 x').
    apply H3.
    split.
    apply IHstmt_type1.
    assumption.
    apply IHstmt_type2.
    assumption.
  + intros.
    apply IHstmt_type2.
    apply IHstmt_type1.
    assumption.
Qed.

Lemma wf_expr_bigger :
  forall G G' e,
    wf_expr G e ->
    Forall (fun xt => xt ∈ G') G ->
    wf_expr G' e.
Proof.
  intros.
  rewrite Forall_forall in H0.
  induction e.
  + constructor.
  + inversion H.
    apply wf_var with (t := t).
    apply H0.
    assumption.
    apply wf_vv.
  + inversion H.
    constructor.
    apply IHe1; assumption.
    apply IHe2; assumption.
Qed.

Lemma wf_prop_bigger :
  forall G G' p,
    wf_prop G p ->
    Forall (fun xt => xt ∈ G') G ->
    wf_prop G' p.
Proof.
  intros.
  induction p.
  + constructor.
  + inversion H; constructor; apply wf_expr_bigger with (G := G); assumption. 
  + inversion H; constructor; apply IHp; assumption.
  + inversion H. constructor. apply IHp1. assumption. apply IHp2. assumption.
  + inversion H. constructor. apply IHp1. assumption. apply IHp2. assumption.
Qed.

Lemma wf_guard_bigger :
  forall G G' g,
    wf_guard G g ->
    Forall (fun xt => xt ∈ G') G ->
    wf_guard G' g.
Proof.
  intros.
  split.
  apply wf_prop_bigger with (G := G).  apply H. assumption.
  apply H.
Qed.  

Lemma wf_guards_stmt :
  forall P G G' X s,
    (P ; G ; X) ⊢ s ::: G' ->
    wf_env G ->
    wf_guards G X ->
    wf_guards G' X.
Proof.
  intros P G G' X s J wfenv wfguards.
  induction J.
  + assumption.
  + apply wf_guards_cons; assumption.
  + apply wf_guards_cons; assumption.
  + destruct H0.
    destruct H1.
    unfold wf_guards.
    rewrite Forall_forall.
    intros x' x'in.
    apply wf_guard_bigger with (G := Γ).
    unfold wf_guards in wfguards.
    rewrite Forall_forall in wfguards.
    apply wfguards.
    assumption.
    rewrite Forall_forall.
    intros [x'' t''] x''in.
    apply H1.
    split.
    pose (env_monotonic Φ _ Γ Γ1 s1 J1) as monotonic.
    rewrite Forall_forall in monotonic.
    apply monotonic.
    assumption.
    pose (env_monotonic Φ _ Γ Γ2 s2 J2) as monotonic.
    rewrite Forall_forall in monotonic.
    apply monotonic.
    assumption.
  + apply IHJ2. 
    apply wf_env_stmt with (P := Φ) (G := Γ) (X := Ξ) (s := s1).
    assumption.
    assumption.
    apply IHJ1.
    assumption.
    assumption.
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

Lemma subst_nonfree_expr :
  forall v e e',
    ~ (v ∈ fv_expr e) -> 
    forall w, eval (λ i : var, eval w (subst_one v e' i), hp w) e = eval w e.
Proof.
  induction e.
  * constructor.
  * intros.
    assert (P : v <> v0).
    intro.
    apply H.
    rewrite H0.
    unfold In.
    simpl.
    tauto.
    unfold subst_one.
    simpl.
    destruct (eq_dec v0 v).
      symmetry in e. contradiction.
      reflexivity.
  * intros.
    simpl.
    unfold fv_expr in H.
    fold fv_expr in H.
    rewrite in_app_iff in H.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
    intuition.
    intuition.
Qed.

Lemma subst_distr_andp:
  forall (θ : subst_t var expr) (P Q : assert),
    (subst θ (andp P Q) = (andp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_andp_var:
  forall (θ : subst_t var var) (P Q : assert),
    (subst θ (andp P Q) = (andp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_andp' :
  forall (θ : subst_t var expr) (P Q : assert) w,
    (subst θ (andp P Q) w = (andp (subst θ P) (subst θ Q)) w).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_andp_var' :
  forall (θ : subst_t var var) (P Q : assert) w,
    (subst θ (andp P Q) w = (andp (subst θ P) (subst θ Q)) w).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_orp:
  forall (θ : subst_t var expr) (P Q : assert),
    (subst θ (orp P Q) = (orp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_imp :
  forall (θ : subst_t var expr) (P Q : assert),
    (subst θ (imp P Q) = (imp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_FF :
  forall θ, subst θ FF = FF.
Proof.
  reflexivity.
Qed.

Lemma subst_emp :
  forall θ, subst θ emp = emp.
Proof.
  reflexivity.
Qed.

Lemma subst_nonfree_prop :
  forall ξ v e,
    ~ (v ∈ fv_prop ξ) ->
    (subst (subst_one v e) (sep_pred ξ) = sep_pred ξ).
Proof.
  intros.
  induction ξ.
  + split; apply derives_refl.
  + destruct b. 
    unfold subst, Subst_pred, subst_pred, sep_pred.
    simpl in H.
    apply pred_ext;
    intro;
    simpl;
    try rewrite subst_nonfree_expr with (e := e0) (v := v) (e' := e);
    try rewrite subst_nonfree_expr with (e := e1) (v := v) (e' := e);
    first [ apply derives_refl | intuition ].
  + unfold sep_pred. fold sep_pred.
    repeat rewrite subst_distr_andp.
    repeat rewrite subst_distr_imp.
    rewrite subst_FF.
    rewrite IHξ.
    reflexivity.
    intuition.
  + unfold sep_pred. fold sep_pred.
    simpl in H.
    repeat rewrite subst_distr_andp.
    rewrite IHξ1;
    try rewrite IHξ2; 
    first [ reflexivity | intuition ].
  + unfold sep_pred. fold sep_pred.
    simpl in H.
    repeat rewrite subst_distr_andp.
    repeat rewrite subst_distr_orp.
    rewrite IHξ1;
    try rewrite IHξ2; 
    first [ reflexivity | intuition ].
Qed.

Lemma wf_expr_fv :
  forall x e Γ,
    x <> ν -> 
    var_not_in x Γ ->
    wf_expr Γ e ->
    ~ (x ∈ fv_expr e).
Proof.
  intros.
  induction e.
  * intuition.
  * inversion H1. subst.
    unfold fv_expr.
    intro. 
    destruct H2.
    unfold var_not_in in H0.
    rewrite Forall_forall in H0.
    specialize (H0 (x,t)).
    rewrite <- H2 in H0.
    apply H0 in H4.
    intuition.
    intuition.
    intro.
    unfold fv_expr in H3.
    destruct H3.
    intuition.
    intuition.
  * unfold fv_expr. fold fv_expr.
    inversion H1. subst.
    rewrite in_app_iff.
    intro.
    destruct H2.
    apply IHe1; assumption.
    apply IHe2; assumption.
Qed.

Lemma wf_prop_fv :
  forall x p Γ,
    x <> ν ->
    var_not_in x Γ ->
    wf_prop Γ p ->
    ~ (x ∈ fv_prop p).
Proof.
  induction p.
  + intuition.
  + intros Γ neqvv notin wfprop.
    unfold fv_prop.
    rewrite in_app_iff.
    intro.
    inversion wfprop. subst.
    destruct H as [notine | notine0].
    apply wf_expr_fv with (e := e) in notin.
    apply notin.
    apply notine.
    assumption.
    assumption.
    apply wf_expr_fv with (e := e0) in notin.
    apply notin.
    apply notine0.
    assumption.
    assumption.
  + intros Γ neqvv notin wfprop.
    simpl.
    inversion wfprop; subst.
    apply IHp with (Γ := Γ); assumption.
  + intros Γ neqvv notin wfprop.
    simpl.
    inversion wfprop; subst.
    rewrite in_app_iff.
    intro.
    destruct H.
    apply IHp1 with (Γ := Γ) in H; assumption.
    apply IHp2 with (Γ := Γ) in H; assumption.
  + intros Γ neqvv notin wfprop.
    simpl.
    inversion wfprop; subst.
    rewrite in_app_iff.
    intro.
    destruct H.
    apply IHp1 with (Γ := Γ) in H; assumption.
    apply IHp2 with (Γ := Γ) in H; assumption.
Qed.

    
Lemma wf_guard_vv_nonfree :
  forall Γ ξ,
    wf_guard Γ ξ ->
      nonfreevars (sep_pred ξ) ν.
Proof.
  intros.
  unfold wf_guard in H.
  destruct H as [wf fv].
  intuition.
  unfold nonfreevars.
  intro.
  rewrite subst_nonfree_prop.
  apply derives_refl.
  assumption.
Qed.

Lemma wf_guard_nonfree :
  forall x ξ Γ,
    var_not_in x Γ ->
    wf_guard Γ ξ ->
    nonfreevars (sep_pred ξ) x.
Proof.
  intros x ξ Γ nomem wfg.
  destruct (eq_dec x ν).
  + rewrite e. apply wf_guard_vv_nonfree with (Γ := Γ).
    assumption.
  + unfold nonfreevars.
    intros.
    intro e. rewrite subst_nonfree_prop. trivial.
    apply wf_prop_fv with (Γ := Γ).
    assumption.
    assumption.
    apply wfg.
Qed.

Lemma nonfree_distr_andp :
  forall (P Q : assert) x e,
    P |-- subst (subst_one x e) P ->
    Q |-- subst (subst_one x e) Q ->
    P && Q |-- subst (subst_one x e) (P && Q).
Proof.
  intros.
  rewrite subst_distr_andp.
  apply andp_derives; assumption.
Qed.

Lemma wf_guards_vv_nonfree :
  forall Γ Ξ,
    wf_guards Γ Ξ ->
      nonfreevars (sep_guards Ξ) ν.
Proof.
  intros.
  induction Ξ.
  + unfold nonfreevars.
    trivial.
  + unfold sep_guards.
    fold sep_guards.
    inversion H.
    subst.
    pose (P := wf_guard_vv_nonfree Γ a H2).
    unfold nonfreevars in *.
    intro e.
    apply nonfree_distr_andp.
    apply nonfree_distr_andp.
    apply P.
    apply IHΞ.
    assumption.
    rewrite subst_emp.
    apply derives_refl.
Qed.

Lemma wf_guards_nonfree :
  forall x Ξ Γ,
    var_not_in x Γ ->
    wf_guards Γ Ξ ->
    nonfreevars (sep_guards Ξ) x.
Proof.
  intros.
  induction Ξ.
  + unfold nonfreevars. trivial.
  + unfold sep_guards. fold sep_guards.
    inversion H0. subst.
    unfold nonfreevars. intro e.
    pose (P := wf_guard_nonfree x a Γ H H3).
    apply nonfree_distr_andp. 
    apply nonfree_distr_andp. 
    apply P.
    apply IHΞ; assumption.
    rewrite subst_emp.
    apply derives_refl.
Qed.

Lemma wf_expr_ty_expr_fv :
  forall Γ Ξ e T,
    wf_env Γ ->
    expr_type Γ Ξ e T -> 
    ~ (ν ∈ fv_expr e).
Proof.
  intros ? ? ? ? wf H.
  dependent induction H.
  + intuition.
  + pose (wf_env_no_vv Γ wf) as WF.
    unfold var_not_in in WF.
    rewrite Forall_forall in WF.
    intuition.
    simpl in H0.
    destruct H0.
    rewrite H0 in H.
    apply WF with (ν, {ν : τ | φ}).
    assumption.
    reflexivity.
    assumption.
  + apply IHexpr_type.
    assumption.
Qed.