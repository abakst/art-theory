Add LoadPath "vst".
Require Import CpdtTactics.
Require Import Types.
Import HE.
Require Import Language.
Require Export ProgramLogic.
Require Import Subst.
Require Import List.
Import ListNotations.
Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.

Instance EQ_EQUIVALENCE : Equivalence (@eq assert) := _.

Set Implicit Arguments.

Open Scope logic.

Definition sep_base (x:expr) (t:base_type) : assert :=
  match t with 
    | int_t   => (EX n : nat, eval_to x (int_v n))
    | ref_t l => (fun s => !!(eval s x = eval s (locvar_e l))
                        && !!(eval s x <> null_v))
    | null_t  => (fun s => !!(eval s x = null_v))
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

Definition sep_heap_bind l (xt : type_binding) : assert :=
  let (x, t) := xt in
      (eval_to (locvar_e l) null_v) 
        || (emapsto (locvar_e l) (var_e x)
            * sep_ty (var_e x) t).

Fixpoint sep_heap' es :=
  match es with
    | nil => emp
    | (l, xt) :: es' => sep_heap_bind l xt * sep_heap' es'
  end.

Definition sep_heap (Σ : heap_env)  : assert :=
  fold (fun l xt a =>
          sep_heap_bind l xt * a) Σ emp.
  (* sep_heap' (elements Σ). *)
  (* fold (fun _ xt a => xt * a) *)
  (*   (mapi (fun l xt => sep_heap_bind l xt) Σ) *)
  (*   emp. *)

Fixpoint sep_guards (Δ : guards) : assert :=
  match Δ with
    | nil => TT
    | p :: Δ' => sep_pred p && sep_guards Δ'
  end && emp.

Definition sep_schema (f:pname) (s:stmt) (S:proc_schema) : procspec := 
  match S with
    | mkSchema xs ts hi ho (x, t) =>
      (f, mkProc xs x [] s, 
          sep_env (combine xs ts) * sep_heap hi,
          sep_ty (var_e x) t * sep_heap ho)
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
  destruct t0.
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
  forall s P,
    pure P -> pure (subst_pred s P).
Proof.
  firstorder.
Qed.

Lemma pure_andp_1 :
  forall P Q, pure P -> pure (P && Q).
Proof.
  intros.
  unfold pure.
  apply andp_left1.
  assumption.
Qed.

Lemma pure_andp_2 :
  forall P Q, pure Q -> pure (P && Q).
Proof.
  intros.
  unfold pure.
  apply andp_left2.
  assumption.
Qed.

Hint Resolve sep_pred_pure sep_ty_pure sep_env_pure sep_guard_pure subst_pure pure_andp_1 pure_andp_2 : pure.

Ltac purity := 
  match goal with
    | |- context[emp] => eauto with pure
    | _: _ && _ |- context[emp] =>
      (apply andp_left1; purity || apply andp_left2; purity)
  end.

(* Lemma sep_heap_decompose' : *)
(*   forall H l x t,  *)
(*     in (l, (x, t)) H ->  *)
(*     exists H', (sep_heap H = sep_heap_bind l x t * sep_heap H' *)
(*                 /\ (forall l', l <> l' -> (loc_in l' H <-> loc_in l' H'))). *)
(* Proof. *)
(*   induction H as [ | [l' [x' t']]]. *)
(*   + intros. contradiction H.  *)
(*   + intros. destruct H0.  *)
(*     * inv H0. *)
(*       unfold sep_heap at 1; fold sep_heap. *)
(*       exists H. repeat split.  *)
(*       intro. *)
(*       unfold loc_in in *. *)
(*       destruct H1. destruct H1. inv H1. congruence. *)
(*       exists x0. assumption. *)
(*       unfold loc_in. *)
(*       intros [xt]. intro. *)
(*       exists xt. eauto with datatypes. *)
(*     * specialize (IHlist l x t H0).  *)
(*       destruct IHlist as [ H'' ]. *)
(*       destruct H1 as [A B]. *)
(*       unfold sep_heap; fold sep_heap. *)
(*       rewrite A. *)
(*       rewrite <- sepcon_assoc. *)
(*       exists ((l',(x',t'))::H''). *)
(*       unfold sep_heap; fold sep_heap. *)
(*       rewrite <- sepcon_assoc. *)
(*       split. *)
(*         { f_equal. *)
(*           rewrite sepcon_comm. *)
(*           reflexivity. } *)
(*         { repeat split.  *)
(*           intros. *)
(*           unfold loc_in in *. *)
(*           destruct H2. destruct H2. inv H2. exists (x', t'). left. reflexivity. *)
(*           specialize (B l'0 H1). destruct B.  *)
(*           destruct H3. exists x0. assumption. *)
(*           exists x1. right. assumption. *)
          
(*           intro. *)
(*           unfold loc_in in *. *)
(*           destruct H2. destruct H2. inv H2. exists (x', t'). left. reflexivity. *)
(*           specialize (B l'0 H1). destruct B. *)
(*           destruct H4. exists x0. assumption. *)
(*           exists x1. right. assumption. } *)
(* Qed. *)

(* Lemma sep_heap_split : *)
(*   forall H H1 H2, *)
(*     heap_split H1 H2 H -> *)
(*     sep_heap H = sep_heap H1 * sep_heap H2. *)
(* Proof. *)
(*   intros H. *)
(*   induction H as [ | (l,xt)]; intros. *)
(*   + assert (H1 = []) by (eapply heap_split_emp1; eauto). *)
(*     assert (H2 = []) by (eapply heap_split_emp2; eauto). *)
(*     subst H1. subst H2. *)
(*     simpl. rewrite sepcon_emp. reflexivity. *)
(*   + assert ((l, xt) :: H = [(l, xt)] ++ H) by reflexivity. *)
(*     rewrite H3. *)
(*     rewrite sep_heap_app. *)
(*     destruct xt as [x t]. *)
(*     unfold sep_heap at 1. *)
(*     rewrite sepcon_emp. *)

(*     unfold heap_split in H0; decompose [and] H0. *)
(*     destruct (H9 l (x,t)). left. reflexivity. { *)
(*       destruct (sep_heap_decompose' H1 l x t) as [H1']. *)
(*       apply H8. *)
(*       specialize (IHlist H1' H2). *)
(*       rewrite IHlist. *)
(*       destruct H10. *)
(*       rewrite H10. *)
(*       rewrite sepcon_assoc. *)
(*       reflexivity. *)

(*       unfold heap_split. *)
(*       repeat split. *)
(*       inv H4. assumption. *)

(*     unfold heap_split in H0. *)
(*     destruct H0. *)
(*     specialize (H4 l xt). *)
(*     destruct H4. left. reflexivity. *)
(*     pose (sep_heap_decompose' H1 l x t) as H1_decomp. *)
(*     destruct H1_decomp as [H1']. apply H4.  *)
(*     specialize (IHlist H1' H2). *)
(*     destruct H5. *)
(*     rewrite IHlist. *)
(*     rewrite H5. *)
(*     unfold sep_heap; fold sep_heap. *)
(*     rewrite sepcon_emp. rewrite sepcon_assoc. reflexivity. *)
    
(*     unfold heap_split. split. { *)
(*       intros l0. *)
(*       repeat rewrite <- loc_in_not_in in *. *)
(*       intro l0_not_in. *)
(*       split. intro. *)
(*       specialize (H6 l0). *)
(*       specialize (H0 l0). *)
(*       repeat rewrite <- loc_in_not_in in H0. *)
(*       destruct H0. *)
(*       intro. *)
(*       intros l0. unfold loc_not_in in *. intros A. *)
(*       split. { *)

Import HE_Props.
Import HE_Props.F.
Import HE_Facts.

Lemma sep_heap_split' :
  forall H A,
    let f := (fun l xt a => sep_heap_bind l xt * a) in
    sep_heap H * A = fold f H A.
Proof.
  intros.
  unfold sep_heap.
  repeat rewrite fold_spec_right.
  
  induction (rev (elements H)) as [ | [l [x t]]].
  simpl.
  rewrite <- sepcon_emp.
  rewrite sepcon_comm.
  extensionality.
  normalize.
 
  unfold fold_right at 2.
  unfold fold_right at 2 in IHl.
  rewrite <- IHl.
  unfold f.
  unfold uncurry.
  simpl. extensionality ρ.
  rewrite sepcon_assoc.
  reflexivity.
Qed.

Corollary sep_heap_split'' :
  forall H1 H2,
    let f := (fun l xt a => sep_heap_bind l xt * a) in
    sep_heap H1 * sep_heap H2 = fold f H1 (sep_heap H2).
Proof.
  intros.
  apply sep_heap_split'.
Qed.
        
Lemma sep_heap_split :
  forall H H1 H2,
    heap_split H1 H2 H -> 
    sep_heap H = sep_heap H1 * sep_heap H2.
Proof.
  unfold heap_split in *.
  intros.
  set (f := (fun l xt a => sep_heap_bind l xt * a)).
  assert (sep_heap H1 * sep_heap H2 = fold f H1 (fold f H2 emp)).
  apply sep_heap_split''.
  rewrite H3.
  apply (Partition_fold (eqA := eq)).
  apply EQ_EQUIVALENCE.
  solve_proper.
  hnf. intros. extensionality. 
  repeat rewrite <- sepcon_assoc. 
  rewrite sepcon_comm with (P := sep_heap_bind k e). reflexivity.
  assumption.
Qed.