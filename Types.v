Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import Subst.
Require Export Language.
Require Import List.
Require Import ListSet.
Import ListNotations.

Definition vv : var := V 0.

Delimit Scope reft_scope with reft.

(** Type Language **)
Inductive base_type : Set :=
  | int_t  : base_type
  | null_t : base_type
  | ref_t  : var -> base_type.

Definition base_of_type b :=
  match b with
    | int_t   => nat
    | null_t  => unit
    | ref_t _ => loc
  end.

Inductive reft_prop : Set :=
  | tt_r  : reft_prop
  | eq_r  : expr -> expr -> reft_prop
  | not_r : reft_prop -> reft_prop
  | and_r : reft_prop -> reft_prop -> reft_prop
  | or_r  : reft_prop -> reft_prop -> reft_prop.

Fixpoint fv_prop φ :=
  match φ with 
    | tt_r => []
    | eq_r e1 e2 => fv_expr e1 ++ fv_expr e2
    | not_r φ => fv_prop φ
    | and_r φ1 φ2 => fv_prop φ1 ++ fv_prop φ2
    | or_r φ1 φ2 => fv_prop φ1 ++ fv_prop φ2
  end.

Record reft_type : Set := 
  mkReft_type { reft_base: base_type;
                reft_r: reft_prop } .

Fixpoint subst_prop_var (s : subst_t var var) prop :=
  match prop with
    | tt_r        => tt_r
    | eq_r e1 e2  => eq_r (subst s e1) (subst s e2)
    | not_r p     => not_r (subst_prop_var s p)
    | and_r p1 p2 => and_r (subst_prop_var s p1) (subst_prop_var s p2)
    | or_r p1 p2  => or_r (subst_prop_var s p1) (subst_prop_var s p2)
  end.

Fixpoint subst_prop (s : subst_t var expr) prop :=
  match prop with
    | tt_r        => tt_r
    | eq_r e1 e2  => eq_r (subst s e1) (subst s e2)
    | not_r p     => not_r (subst_prop s p)
    | and_r p1 p2 => and_r (subst_prop s p1) (subst_prop s p2)
    | or_r p1 p2  => or_r (subst_prop s p1) (subst_prop s p2)
  end.

Instance Subst_prop_var : Subst reft_prop var var := subst_prop_var.
Instance Subst_prop : Subst reft_prop var expr := subst_prop.

Fixpoint subst_base (s : subst_t var var) b :=
  match b with
    | ref_t l => ref_t (s l)
    | _        => b
  end.

Instance Subst_base_var : Subst base_type var var := subst_base.

Definition subst_r_var (s : subst_t var var) reft :=
  mkReft_type (subst s (reft_base reft))
              (subst s (reft_r reft)).

Definition subst_r s reft :=
  mkReft_type (reft_base reft)
              (subst s (reft_r reft)).

Instance Subst_reft_var : Subst reft_type var var := subst_r_var.
Instance Subst_reft : Subst reft_type var expr := subst_r.

Definition type_binding : Set := (var * reft_type)%type.

Definition dummyt (v : var) t p := mkReft_type t p.

Notation "x .= y" := (eq_r x y) (at level 70).
(* Notation "{ vv : t | P }" := (mkReft_type t P%reft) (at level 0, no associativity). *)
Notation "{ vv : t | P }" := (dummyt vv t P%reft) (at level 0, vv at level 99, no associativity).


(** Environments **)
Definition bind_env (B T : Set) : Set := list (B * T)%type.
Definition type_env : Set := bind_env var reft_type.
Definition heap_env : Set := list (var * type_binding)%type.

Fixpoint subst_heap_var s (h : heap_env) : heap_env :=
  match h with
    | nil => nil
    | (l, xt) :: h' => (subst s l, subst s xt) :: subst_heap_var s h'
  end.

Instance Subst_heap_var : Subst heap_env var var := subst_heap_var.

(** Procedures **)
Record proc_schema : Set :=
  mkSchema { s_formals: list var;
             s_formal_ts: list reft_type;
             s_heap_in: heap_env;
             s_heap_out: heap_env;
             s_ret: type_binding }.

Definition subst_schema (s : var -> var) S :=
  let subst_both s xt := (@subst _ _ _ Subst_var_var s (fst xt),
                          @subst _ _ _ Subst_reft_var s (snd xt)) in
  match S with
    | mkSchema xs ts hi ho xt =>
      mkSchema (subst s xs) (subst s ts) (subst_heap_var s hi) (subst_heap_var s ho) (subst_both s xt)
  end.

Instance Subst_proc_schema : Subst proc_schema var var := subst_schema.

Definition proc_env : Type := bind_env pname (stmt * proc_schema)%type.

Definition var_in : var -> type_env -> Prop := 
  fun x Γ => exists t, In (x, t) Γ.

Definition var_not_in : var -> type_env -> Prop :=
  fun x Γ => Forall (fun xt => (fst xt <> x)) Γ.

Definition bind_in : var -> heap_env -> Prop :=
  fun x Σ => exists l t, In (l, (x, t)) Σ.

Definition bind_not_in : var -> heap_env -> Prop :=
  fun x Σ => Forall (fun lxt => (fst (snd lxt)) <> x) Σ.

Definition loc_in : var -> heap_env -> Prop :=
  fun l Σ => exists b, In (l, b) Σ.

Definition loc_not_in : var -> heap_env -> Prop :=
  fun l Σ => Forall (fun lxt => (fst lxt <> l)) Σ.

Definition fun_in : (pname * (stmt * proc_schema)) -> proc_env -> Prop :=
  fun ft Φ => In ft Φ.

Definition fun_not_in : pname  -> proc_env -> Prop :=
  fun f Φ => Forall (fun ft => fst ft <> f) Φ.

Definition heap_split Σ1 Σ2 Σ :=
  forall l, 
    (loc_in l Σ /\ 
     ((loc_in l Σ1 /\ loc_not_in l Σ2) \/ (loc_in l Σ2 /\ loc_not_in l Σ1))
     \/ (loc_not_in l Σ /\ loc_not_in l Σ1 /\ loc_not_in l Σ2)).

Notation "X ∈ Y" := (In X Y) (at level 40).

Definition ext_type_env (e1 e2: type_env) := e1 ++ e2.
Definition ext_proc_env (e1 e2: proc_env) := e1 ++ e2.

(** Guards **)
Definition guard := reft_prop.
Definition guards := list reft_prop.

(** Hm **)
(** Ugh Equality **)
Instance EqDec_base_t : EqDec base_type := _.
Proof.
  hnf. decide equality; apply eq_dec.
Qed.

Instance EqDec_reft_prop : EqDec reft_prop := _.
Proof.
  hnf. decide equality; try apply eq_dec. 
Qed.

Instance EqDec_reft_type : EqDec reft_type := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_proc_schema : EqDec proc_schema := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Definition ν := vv.

Hint Rewrite Forall_forall.
Hint Unfold heap_split loc_not_in loc_in : heap.

Theorem loc_in_dec :
  forall l Σ, {loc_in l Σ} + {~ loc_in l Σ}.
Proof.
  intros.
  unfold loc_in.
  induction Σ.
  right. intuition. destruct H. inversion H.
  destruct IHΣ.
  left. destruct e. exists x. right. assumption.
  intuition.
  cut ({l = a0} + {l <> a0}). intro.
  destruct H. 
    rewrite <- e in *.
    left. exists b. left. reflexivity.
    right. intro. apply n.
    destruct H.
    destruct H. inversion H. subst.
    congruence.
    exists x. assumption.
  apply eq_dec.
Qed.

Lemma loc_in_not_in :
  forall Σ l,
    ~loc_in l Σ <-> loc_not_in l Σ.
Proof.
  intro Σ.
  unfold loc_not_in.
  unfold loc_in.
  induction Σ.
  intros.
  rewrite Forall_forall.
  constructor.
  intros.
  inversion H0.
  intros.
  intro. 
  destruct H0.
  inversion H0.
  constructor.
  intros.
  destruct (IHΣ l).
  rewrite Forall_forall in *.
  intros.
  destruct H2. subst.
  intuition.
  destruct x. subst. 
  apply H.
  exists t. left. reflexivity.
  apply H0.
  intro.
  apply H.
  destruct H3.
  exists x0. apply in_cons. assumption. assumption.
  intros.
  intro.
  destruct (IHΣ l).
  rewrite Forall_forall in *.
  destruct H0.
  destruct H0.
  destruct a. inversion H0. subst.
  specialize (H (l,x)). apply H. left. reflexivity. reflexivity.
  apply H2. intros.
  apply H. apply in_cons. assumption. exists x. assumption.
Qed. (** OOF **)

Lemma heap_split_comm :
  forall Σ1 Σ2 Σ,
    heap_split Σ1 Σ2 Σ ->
    heap_split Σ2 Σ1 Σ.
Proof.
  intros.
  unfold heap_split in *.
  intros. 
  destruct (H l); firstorder.
Qed.

Lemma heap_split_emp :
  forall l Σ1 Σ2 Σ,
    heap_split Σ1 Σ2 Σ ->
    loc_not_in l Σ ->
    loc_not_in l Σ1.
Proof.
  intros.
  unfold heap_split in H.
  specialize (H l).
  rewrite <- loc_in_not_in in *.
  destruct H.
  destruct H.
  congruence.
  destruct H. destruct H1.
  rewrite <- loc_in_not_in in *.
  assumption.
Qed.

Lemma heap_split_emp' :
  forall l Σ1 Σ2 Σ,
    heap_split Σ1 Σ2 Σ ->
    loc_not_in l Σ ->
    loc_not_in l Σ2.
Proof.
  intros.
  apply heap_split_comm in H.
  eapply heap_split_emp;
  eauto.
Qed.

Hint Resolve heap_split_emp heap_split_emp' loc_in_not_in : heaps.