Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import Subst.
Require Export Language.
Require Import List.
Require Export Coq.Structures.Equalities.
Require Import ListSet.
Require Export Coq.FSets.FMaps.
(* Require Import Coq.FSets.FMapList. *)
(* Require Import Coq.FSets.FMapFacts. *)
Require Import Coq.Structures.OrderedTypeEx.
Import ListNotations.

Definition vv : var := V 0.
Inductive loc := L : nat -> loc.

Definition subst_loc (s:subst_t loc loc) (l:loc) := s l.
Instance Subst_loc_loc : Subst loc loc loc := subst_loc.
Instance EqDec_loc : EqDec loc := _. 
Proof. hnf. decide equality. apply eq_dec. Qed.

(** Assume a mapping from locations to runtime addresses **)
Parameter runloc : loc -> addr.

Parameter runloc_inj : 
  forall l1 l2, runloc l1 <> null -> (runloc l1 <> runloc l2).

Definition subst_loc_one (l : loc) (l' : loc) : subst_t loc loc  :=
  fun i => if eq_dec i l then l' else i.

Delimit Scope reft_scope with reft.

(** Type Language **)
Inductive base_type : Set :=
  | int_t  : base_type
  | null_t : base_type
  | ref_t  : loc -> base_type.

Definition base_of_type b :=
  match b with
    | int_t   => nat
    | null_t  => unit
    | ref_t _ => addr
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

Definition subst_r_var (s : subst_t var var) reft :=
  mkReft_type (reft_base reft) (subst s (reft_r reft)).

Definition subst_base_loc (s : subst_t loc loc) b :=
  match b with
    | ref_t l => ref_t (s l)
    | _ => b
  end.

Instance Subst_base_loc : Subst base_type loc loc := subst_base_loc.

Definition subst_r_loc (s : subst_t loc loc) reft :=
  mkReft_type (subst s (reft_base reft)) (reft_r reft).

Definition subst_r s reft :=
  mkReft_type (reft_base reft) (subst s (reft_r reft)).

Instance Subst_reft_var : Subst reft_type var var := subst_r_var.
Instance Subst_reft : Subst reft_type var expr := subst_r.
Instance subst_reft_loc : Subst reft_type loc loc := subst_r_loc.

Definition type_binding : Set := (var * reft_type)%type.

Definition dummyt (v : var) t p := mkReft_type t p.

Notation "x .= y" := (eq_r x y) (at level 70).
(* Notation "{ vv : t | P }" := (mkReft_type t P%reft) (at level 0, no associativity). *)
Notation "{ vv : t | P }" := (dummyt vv t P%reft) (at level 0, vv at level 99, no associativity).


(** Environments **)
(* Module Type Loc. *)
(*   Definition t := loc. *)
(*   Definition eq := eq_dec. *)
(* End Loc. *)

Module Loc_as_OT <: UsualOrderedType.
  Definition t := loc.
  Definition eq := @eq loc.
  Definition eq_refl := @eq_refl loc.
  Definition eq_sym := @eq_sym loc.
  Definition eq_trans := @eq_trans loc.
  Definition lt l l' :=
    match (l, l') with
      | (L n, L n') => n < n'
    end.
  Definition eq_dec := eq_dec.
  Lemma lt_trans : forall l1 l2 l3,
                     lt l1 l2 -> lt l2 l3 -> lt l1 l3.
  Proof.
    intros.
    unfold lt in *.
    destruct l1. destruct l2. destruct l3.
    pose (Nat_as_OT.lt_trans n n0 n1).
    apply l. apply H. apply H0.
  Qed.

  Lemma lt_not_eq : forall l1 l2, lt l1 l2 -> ~ eq l1 l2.
  Proof.
    destruct l1 as [n1].
    destruct l2 as [n2].
    intros.
    pose (Nat_as_OT.lt_not_eq n1 n2).
    intuition.
    apply H1.
    injection H0.
    intro. subst.
    exfalso.
    apply H1.
    reflexivity.
  Qed.
  
  Definition compare x y : Compare lt eq x y.
  Proof.
    destruct x. destruct y.
    destruct (Nat_as_OT.compare n n0).
    apply LT. apply l.
    apply EQ. inversion e. subst. constructor.
    apply GT. apply l.
  Qed.
End Loc_as_OT.

Module UD_Loc <: OrderedType := UOT_to_OT(Loc_as_OT).
Module Loc_as_DT <: DecidableType := Loc_as_OT.

Module HE := FMapList.Make(UD_Loc).
Module HE_Facts := WFacts_fun(Loc_as_DT)(HE).
Module HE_Props := WProperties_fun(Loc_as_DT)(HE).

Definition bind_env (B T : Type) : Type := list (B * T)%type.
Definition type_env : Type := bind_env var reft_type.
Definition heap_env : Type := HE.t type_binding.
Definition heap_emp := HE.empty type_binding.

Definition subst_heap_var s (h : heap_env) : heap_env :=
  HE.map (fun xt => subst s xt) h.

Instance Subst_heap_var : Subst heap_env var var := subst_heap_var.
Instance Subst_binding_loc : Subst type_binding loc loc :=
  fun s xt => (fst xt, subst s (snd xt)).

Definition subst_heap_loc (s : loc -> loc) (h : heap_env) : heap_env :=
  HE.fold (fun k xt m => HE.add (s k) (subst s xt) m) h (HE.empty type_binding).

Instance Subst_heap_loc : Subst heap_env loc loc := subst_heap_loc.

(** Procedures **)
Record proc_schema : Type :=
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

Definition subst_schema_loc (s : loc -> loc) S :=
 match S with
   | mkSchema xs ts hi ho (x, t) =>
     mkSchema xs (subst s ts) (subst_heap_loc s hi)
              (subst_heap_loc s ho) (x, subst s t)
 end.              

Instance Subst_proc_schema : Subst proc_schema var var := subst_schema.
Instance Subst_proc_schema_loc : Subst proc_schema loc loc := subst_schema_loc.

Definition proc_env : Type := bind_env pname (stmt * proc_schema)%type.

Definition var_in : var -> type_env -> Prop := 
  fun x Γ => exists t, In (x, t) Γ.

Definition var_not_in : var -> type_env -> Prop :=
  fun x Γ => Forall (fun xt => (fst xt <> x)) Γ.

Definition bind_in : var -> heap_env -> Prop :=
  fun x Σ => exists l t, HE.find l Σ = Some (x,t).

Definition bind_not_in : var -> heap_env -> Prop :=
  fun x Σ => forall l t, (HE.find l Σ <> Some (x, t)).

Definition loc_in : loc -> heap_env -> Prop :=
  fun l Σ => HE.find l Σ <> None.

Definition loc_not_in : loc -> heap_env -> Prop :=
  fun l Σ => HE.find l Σ = None.

Definition ty_loc (T : reft_type) :=
  let (b, _) := T in
  match b with 
    | ref_t l => [l]
    | _        => []
  end.

Definition loc_not_in_ctx : loc -> type_env -> Prop :=
  fun l Γ => Forall (fun xt => ~ In l (ty_loc (snd xt))) Γ.

Definition fun_in : (pname * (stmt * proc_schema)) -> proc_env -> Prop :=
  fun ft Φ => In ft Φ.

Definition fun_not_in : pname  -> proc_env -> Prop :=
  fun f Φ => Forall (fun ft => fst ft <> f) Φ.

Notation "X ∈ Y" := (In X Y) (at level 40).

Definition disjoint (Σ1 Σ2 : heap_env) :=
     forall l, (HE.In l Σ1 -> ~ HE.In l Σ2)
     /\ forall l, (HE.In l Σ2 -> ~ HE.In l Σ1).

Definition heap_split Σ1 Σ2 Σ :=
  @HE_Props.Partition type_binding Σ Σ1 Σ2.
  (*    (forall l, ~HE.In l Σ -> ~HE.In l Σ1) *)
  (* /\ (forall l, ~HE.In l Σ -> ~HE.In l Σ2) *)
  (* /\ (forall l xt, HE.find l Σ = Some xt -> (HE.find l Σ1 = Some xt  *)
  (*                                        \/  HE.find l Σ2 = Some xt)) *)
  (* /\ disjoint Σ1 Σ2. *)

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

(* Instance EqDec_proc_schema : EqDec proc_schema := _. *)
(* Proof. *)
(*   hnf. decide equality; try apply eq_dec. *)
(* Qed. *)

Definition ν := vv.

Hint Rewrite Forall_forall.
Hint Unfold heap_split loc_not_in loc_in : heap.

Theorem loc_in_dec :
  forall l Σ, {loc_in l Σ} + {~ loc_in l Σ}.
Proof.
  intros.
  unfold loc_in.
  destruct (HE.find l Σ).
  left. discriminate.
  right. intuition.
Qed.

Lemma loc_in_not_in :
  forall Σ l,
    ~loc_in l Σ <-> loc_not_in l Σ.
Proof.
  intro Σ.
  unfold loc_not_in.
  unfold loc_in.
  intro l.
  destruct (HE.find l Σ) eqn: F.
  split.
  intro.
  exfalso.
  apply H. discriminate.
  intro. intro. contradiction.
  split.
  intro. reflexivity.
  intro.
  intro.
  contradiction.
Qed.

Lemma heap_split_comm :
  forall Σ1 Σ2 Σ,
    heap_split Σ1 Σ2 Σ ->
    heap_split Σ2 Σ1 Σ.
Proof.
  intros.
  unfold heap_split in *.
  apply HE_Props.Partition_sym.
  assumption.
Qed.

Import HE.
Import HE_Facts.
Import HE_Props.

Lemma heap_split_loc_not_in :
  forall l Σ1 Σ2 Σ,
    heap_split Σ1 Σ2 Σ ->
    loc_not_in l Σ ->
    loc_not_in l Σ1.
Proof.
  intros.
  unfold loc_not_in in *.
  unfold heap_split in *.
  unfold Partition in *.
  decompose [and] H.
  specialize (H2 l).
  apply not_find_in_iff in H0.
  apply not_find_in_iff.
  intro.
  apply H0.
  destruct H3.
  specialize (H2 x).
  destruct H2.
  exists x.
  apply H4.
  left.
  apply H3.
Qed.

Lemma heap_split_loc_not_in' :
  forall l Σ1 Σ2 Σ,
    heap_split Σ1 Σ2 Σ ->
    loc_not_in l Σ ->
    loc_not_in l Σ2.
Proof.
  intros.
  eauto using heap_split_loc_not_in, heap_split_comm.
Qed.

Hint Resolve heap_split_loc_not_in heap_split_loc_not_in' loc_in_not_in : heaps.

(* Lemma in_exists : *)
(*   forall (H : heap_env), *)
(*     H <> [] -> exists a, In a H. *)
(* Proof. *)
(*   intros. *)
(*   induction H. *)
(*   contradiction H0. reflexivity. *)
(*   exists a. left. reflexivity. *)
(* Qed. *)

Lemma heap_split_emp1 :
    forall H H1 H2,
      HE.Empty H -> 
      heap_split H1 H2 H -> HE.Empty H1.
Proof.
  unfold heap_split.
  intros.
  pose (@HE_Props.Partition_Empty _ H H1 H2 H3).
  destruct i.
  apply H4. assumption.
Qed.

Lemma heap_split_emp2 :
    forall H H1 H2,
      HE.Empty H -> 
      heap_split H1 H2 H -> HE.Empty H2.
Proof.
  intros.
  eauto using heap_split_comm, heap_split_emp1.
Qed.

Lemma heap_split_emp :
  forall H H1 H2,
    HE.Empty H ->
    heap_split H1 H2 H -> HE.Empty H1 /\ HE.Empty H2.
Proof.
  intros; split; eauto using heap_split_emp1, heap_split_comm.
Qed.

Hint Resolve 
     heap_split_emp1
     heap_split_emp2
     heap_split_emp
: heaps.