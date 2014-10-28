Add LoadPath "vst".
Require Import CpdtTactics.
Require Import Types.
Require Import Language.
Require Export ProgramLogic.
Require Import Subst.
Require Import List.
Import ListNotations.
Require Import Coq.Unicode.Utf8.

Set Implicit Arguments.

Open Scope logic.

Definition sep_base (x:expr) (t:base_type) : assert :=
  match t with 
    | int_t   => (EX n : nat, eval_to x (int_v n))
    | ref_t l => (fun s => !!(eval s x = eval s (var_e l))) 
    | null    => eval_to x null_v
  end && emp.

Fixpoint sep_pred (p:reft_prop) : assert :=
  match p with
    | tt_r  => TT
    | eq_r e1 e2 => fun s => !!(eval s e1 = eval s e2)
    | not_r p => (sep_pred p) --> FF
    | and_r p1 p2 => sep_pred p1 && sep_pred p2
    | or_r p1 p2 => sep_pred p1 || sep_pred p2
  end && emp.

Definition sep_ty (x:expr) (t:reft_type) : assert :=
  match t with
  | mkReft_type b p => sep_base x b && (sep_pred (subst (subst_one ν x) p))
  end && emp.

Fixpoint sep_env (Γ : type_env) : assert :=
  match Γ with
    | nil => TT
    | (x,t) :: Γ' => sep_ty (var_e x) t && sep_env Γ'
  end && emp.

Fixpoint sep_heap (Σ : heap_env) : assert :=
  match Σ with
    | nil => emp
    | (l, (x, t))::Σ' =>
      (eval_to (var_e l) null_v 
               || (emapsto (var_e l) (var_e x)
                   * sep_ty (var_e x) t)) * sep_heap Σ'
  end.

Fixpoint sep_guards (Δ : guards) : assert :=
  match Δ with
    | nil => TT
    | p :: Δ' => sep_pred p && sep_guards Δ'
  end && emp.

Definition sep_schema (f:pname) (s:stmt) (S:proc_schema) : procspec := 
  match S with
    | mkSchema xs ts hi ho (x, t) =>
      (f, mkProc xs x [] s, 
          sep_env (combine xs ts) * TT, 
          sep_ty (var_e x) t * TT)
  end.

Fixpoint sep_proc_env (Φ : proc_env) : procspecs :=
  match Φ with
    | nil => nil
    | (f,(s,t)) :: Φ' => sep_schema f s t :: sep_proc_env Φ'
  end.

Definition disj_subst Γ (θ : var -> expr) :=
  θ ν = (var_e ν) /\ forall x, var_in x Γ -> θ x = (var_e x).

Lemma sep_base_pure : 
  forall x t, 
    pure (sep_base x t).
Proof.
  intros.
  unfold pure.
  unfold sep_base.
  apply andp_left2.
  apply derives_refl.
Qed.

Lemma sep_pred_pure :
  forall p,
    pure (sep_pred p).
Proof.
  intros.
  unfold pure.
  destruct p;
  unfold sep_pred; fold sep_pred; apply andp_left2; apply derives_refl.
Qed.

Lemma sep_ty_pure :
  forall x t,
    pure (sep_ty x t).
Proof.
  intros.
  unfold pure, sep_ty.
  destruct t.
  do 2 apply andp_left1.
  apply sep_base_pure.
Qed.

Lemma sep_env_pure :
  forall g,
    pure (sep_env g).
Proof.
  intros.
  unfold pure.
  destruct g.
  apply andp_left2. apply derives_refl.
  unfold sep_env. fold sep_env.
  apply andp_left2. apply derives_refl.
Qed.

Lemma sep_guard_pure :
  forall g,
    pure (sep_guards g).
Proof.
  intros.
  unfold pure, sep_guards.
  destruct g.
  normalize.
  apply andp_left2.
  apply derives_refl.
Qed.

Lemma subst_pure :
  forall s (P : assert),
    pure P -> pure (subst_pred s P).
Proof.
  firstorder.
Qed.
    

Hint Resolve sep_pred_pure sep_ty_pure sep_env_pure sep_guard_pure subst_pure : pure.

Ltac purity := 
  match goal with
    | |- context[emp] => eauto with pure
    | _: _ && _ |- context[emp] =>
      (apply andp_left1; purity || apply andp_left2; purity)
  end.