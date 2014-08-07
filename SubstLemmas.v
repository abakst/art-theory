Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Require Import Translation.
Require Import Types.
Require Import Judge.
Require Import Language.
Require Import Subst.
Require Import WFLemmas.
Require Import Tactics.

Lemma subst_none_base :
  forall x e x' t' s,
   x <> x' -> (subst_pred x e (sep_base x' t') s) -> (sep_base x' t' s).
Proof.
  autounfold in *; crush_sep False fail; destruct (eq_dec x x') eqn:EQ; crush.
Qed.

Lemma subst_none_base' :
  forall x e x' t' s,
   x <> x' -> (sep_base x' t' s) -> (subst_pred x e (sep_base x' t') s).
Proof.
  autounfold in *; crush_sep False fail; destruct (eq_dec x x') eqn:EQ; crush.
Qed.

Lemma not_prop_1 :
  forall φ w,
    sep_pred (not_r φ) w -> (sep_pred φ) w -> FF w.
Proof.
  crush.
Qed.

Lemma not_prop_2 :
  forall φ w,
    sep_pred φ w -> FF w -> sep_pred (not_r φ) w.
Proof.
  crush.
Qed.
  
Lemma subst_not :
  forall x e φ w,
    subst_pred x e (sep_pred (not_r φ)) w -> (subst_pred x e (sep_pred φ) w -> FF w).
Proof.
  crush.
Qed.

Lemma not_inv:
  forall p q w,
    sep_pred p w -> sep_pred q w -> sep_pred (not_r q) w -> sep_pred (not_r p) w.
Proof.
  crush.
Qed.

Lemma not_inv2:
  forall p q w,
    sep_pred p w -> sep_pred (not_r q) w -> sep_pred q w -> sep_pred (not_r p) w.
Proof.
  crush.
Qed.

Lemma subst_none_eq :
  forall x e Γ ν τ e1 e2 s,
    var_not_in x Γ -> wf_type Γ { ν : τ | e1 .= e2 } -> (x <> ν) -> 
    (subst_pred x e (sep_pred (e1 .= e2)) s <-> sep_pred (e1 .= e2) s).
    (* /\ (sep_pred (e1 .= e2) s -> subst_pred x e (sep_pred (e1 .= e2)) s)). *)
Proof.
  unfold subst_pred;
  crush' var_not_in_exp (wf_expr, wf_prop, wf_type);
  destruct e1 eqn:E1; 
  destruct e2 eqn:E2;
  crush_sep False fail;
    repeat match goal with
             | [ H: context[eq_dec ?x ?y] |- _ ] => destruct (eq_dec x y)
             | |- context[eq_dec ?x ?y] => destruct (eq_dec x y)
             | |- appcontext[( _ && _ )] => split; simpl
          end; crush.
Qed.

Lemma subst_none_lt :
 forall x e Γ ν τ e1 e2 s,
    var_not_in x Γ -> wf_type Γ { ν : τ | e1 .< e2 } -> x <> ν ->
    (subst_pred x e (sep_pred (e1 .< e2)) s <-> sep_pred (e1 .< e2) s).
Proof.
  unfold subst_pred;
  crush' var_not_in_exp (wf_expr, wf_prop, wf_type);
  destruct e1;
  destruct e2;
  reduce_preds;
    repeat (match goal with
              | [ x:_, y:_, H:appcontext[!!(?x < ?y)] |- _] => exists x; exists y; simpl
              | [ H: context[eq_dec ?x ?y] |- _ ] => destruct (eq_dec x y)
              | |- context[eq_dec ?x ?y] => destruct (eq_dec x y)
              | |- appcontext[( _ && _ )] => split; simpl
            end; crush).
Qed.

Lemma subst_none_rel :
 forall x e Γ ν τ b e1 e2 s,
    var_not_in x Γ -> wf_type Γ { ν : τ | rel_r e1 b e2 } -> x <> ν ->
    (subst_pred x e (sep_pred (rel_r e1 b e2)) s <-> sep_pred (rel_r e1 b e2) s).
Proof.
  destruct b. apply subst_none_eq. apply subst_none_lt.
Qed.

Lemma subst_not_1 :
  forall φ s,
    (sep_pred (not_r φ) s -> (sep_pred φ s -> FF s)).
Proof.
  crush.
Qed.

Lemma subst_not_2 :
  forall φ s,
    (sep_pred φ s -> FF s) -> (sep_pred (not_r φ) s).
Proof.
  crush.
Qed.

Lemma subst_none_prop :
  forall φ x e Γ τ s,
    var_not_in x Γ -> wf_type Γ { ν : τ | φ } -> x <> ν ->
    (subst_pred x e (sep_pred φ) s <-> sep_pred φ s).
Proof.
  Ltac autocons := 
    repeat (econstructor || app_pred || eauto); crush.
  Ltac t :=
    first [btapply autocons | solve [left; btapply autocons] | solve [right; btapply autocons]].
  intro φ.
  induction φ.
  (* true *)
  crush. 
  (* rel *)
  intros; apply subst_none_rel with (Γ := Γ) (ν := ν) (τ := τ); auto.
  (* not *)
  wf_crush; t.
  (* and  *)
  wf_crush; t.
  (* or *)
  wf_crush; t. 
Qed.

Lemma subst_commute :
  forall (x y : var) (x' y' : expr) p s,
    (var_e y) <> x' -> (var_e x) <> y' -> x <> y -> x' <> y' ->
    subst_pred x x' (subst_pred y y' p) s =
      subst_pred y y' (subst_pred x x' p) s.
Proof.
  intros. unfold subst_pred. f_equal.
  destruct x' as [x'v | x']. 
    extensionality. simpl.
      destruct y' as [y'v | y'].
        destruct (eq_dec x x0). 
          destruct (eq_dec y x0). 
            rewrite e in H1. rewrite e0 in H1. exfalso. apply H1; reflexivity.
            reflexivity.
          destruct (eq_dec y x0).
            rewrite e in H1. reflexivity.
            reflexivity.
        destruct (eq_dec x x0).
          destruct (eq_dec y x0). 
            rewrite e in H1. rewrite e0 in H1. exfalso. apply H1; reflexivity.
            reflexivity.
          destruct (eq_dec y x0). 
            simpl. destruct (eq_dec x y'). 
              rewrite e0 in H0. contradiction H0. reflexivity.
              reflexivity.
            reflexivity.
    extensionality. simpl.
      destruct y' as [y'v | y'].
        destruct (eq_dec y x0).
          simpl. destruct (eq_dec x x0).
            rewrite e in H1. rewrite e0 in H1. contradiction H1. reflexivity.
            reflexivity. 
        destruct (eq_dec x x0). simpl.
          destruct (eq_dec y x'). 
            rewrite e0 in H. contradiction H. reflexivity.
            reflexivity.
          reflexivity.
       destruct (eq_dec y x0). simpl.
         destruct (eq_dec x y'). rewrite e0 in H0. contradiction H0. reflexivity.
         destruct (eq_dec y x'). rewrite e0 in H. contradiction H. reflexivity. 
         destruct (eq_dec x x0). rewrite e in H1. rewrite e0 in H1. contradiction H1. reflexivity.
         reflexivity.
         destruct (eq_dec y x'). rewrite e in H. contradiction H. reflexivity.
         reflexivity.
Qed.

Lemma subst_none_ty : 
  forall Γ x x' e T s, 
    x <> ν -> x' <> ν -> var_e ν <> e -> x <> x' ->
    var_not_in x Γ -> wf_type Γ T -> var_in x' Γ ->
    (subst_pred x e (sep_ty x' T) s -> sep_ty x' T s).
Proof.
  intros Γ x x' e T s neq_x_vv neq_x'_vv neq_e_vv neq_x_x' NotIn WF_Type VarIn.
  inversion WF_Type; subst.
  intro SubSep; destruct SubSep as [SepBase SepTy]; apply subst_none_base in SepBase.
  unfold sep_ty. split. assumption.
  fold (subst_pred x e (sep_pred (subst ((ν,x')::nil) p)) s) in SepTy.
  pose subst_none_prop as Foo.
  specialize (Foo (subst ((ν,x') :: nil) p) x e Γ b s NotIn).
  apply Foo.
  apply wf_reft_t. apply wf_prop_subst. 
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subst_none_ty' :
  forall Γ x x' e T s, 
    x <> ν -> x' <> ν -> var_e ν <> e -> x <> x' ->
    var_not_in x Γ -> wf_type Γ T -> var_in x' Γ ->
    (sep_ty x' T s -> subst_pred x e (sep_ty x' T) s ).
Proof.
  intros Γ x x' e T s neq_x_vv neq_x'_vv neq_e_vv neq_x_x' NotIn WF_Type VarIn.
  inversion WF_Type; subst.
  intro SepTy. destruct SepTy as [SepBase SepPred].
  apply subst_none_base' with (x := x) (e := e) (x' := x') (t' := b) in SepBase.
  2: assumption.
  unfold sep_ty.
  split. assumption.
  pose subst_none_prop as foo.
  specialize (foo (subst ((ν,x')::nil) p) x e Γ b s NotIn). 
  apply foo.
  apply wf_reft_t. apply wf_prop_subst. assumption. assumption. assumption. assumption.
Qed.
