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

Fixpoint nonfv_prop {D R : Type} {S: Subst expr D R} φ (x : D) :=
  match φ with 
    | tt_r => True
    | eq_r e1 e2 => nonfv e1 x /\ nonfv e2 x
    | not_r φ => nonfv_prop φ x
    | and_r φ1 φ2 => nonfv_prop φ1 x /\ nonfv_prop φ2 x
    | or_r φ1 φ2 => nonfv_prop φ1 x /\ nonfv_prop φ2 x
  end.

Record reft_type : Set := 
  mkReft_type { reft_base: base_type;
                reft_r: reft_prop } .

Fixpoint subst_prop {D R : Type} {S: Subst expr D R} (s : subst_t D R) p :=
  match p with
    | tt_r        => tt_r
    | eq_r e1 e2  => eq_r (subst s e1) (subst s e2)
    | not_r p     => not_r (subst_prop s p)
    | and_r p1 p2 => and_r (subst_prop s p1) (subst_prop s p2)
    | or_r p1 p2  => or_r (subst_prop s p1) (subst_prop s p2)
  end.

Fixpoint eq_prop {D R : Type} {S: Subst expr D R} p1 p2 :=
  match (p1, p2) with
    | (tt_r, tt_r) => True
    | (eq_r e11 e12, eq_r e21 e22) => eq e11 e21 /\ eq e12 e22
    | (not_r p1, not_r p2) => eq_prop p1 p2
    | (and_r p11 p12, and_r p21 p22) => eq_prop p11 p21 /\ eq_prop p12 p22
    | (or_r p11 p12, or_r p21 p22) => eq_prop p11 p21 /\ eq_prop p12 p22
    | _ => False
  end.

Instance Eq_eqProp {D R : Type} {S: Subst expr D R} {E: Equivalence (eq (A := expr) (D := D) (R := R))}
: Equivalence eq_prop.
Proof.
  constructor; intro.
  induction x; repeat constructor; try reflexivity; try assumption.
  induction x; destruct y; intros; try inversion H; solve_instance.
  induction x; destruct y; destruct z; solve_instance.
Qed.

(* Definition subst_prop_loc (s : subst_t loc loc) (p : reft_prop) := p. *)
                                                       
(* Fixpoint subst_prop (s : subst_t var expr) prop := *)
(*   match prop with *)
(*     | tt_r        => tt_r *)
(*     | eq_r e1 e2  => eq_r (subst s e1) (subst s e2) *)
(*     | not_r p     => not_r (subst_prop s p) *)
(*     | and_r p1 p2 => and_r (subst_prop s p1) (subst_prop s p2) *)
(*     | or_r p1 p2  => or_r (subst_prop s p1) (subst_prop s p2) *)
(*   end. *)


(* Instance Subst_prop_loc : Subst reft_prop loc loc := subst_prop_loc. *)
(* Instance Subst_prop_var : Subst reft_prop var var := subst_prop_var. *)
Instance Subst_prop {D R : Type} {S: Subst expr D R} : Subst reft_prop D R := 
  mkSubst _ _ _ (eq_prop (S := S)) nonfv_prop subst_prop.

Instance FVSubst_prop
         {D R : Type} 
         `{S: SubstFV expr D R} 
         {E : Equivalence (eq (A := expr) (D := D) (R := R))}
         {P : Proper (Logic.eq ==> (eq (A := expr) (D := D) (R := R))
                               ==> (eq (A := expr) (D := D) (R := R))) subst}
         : SubstFV reft_prop D R _.
Proof.
  constructor.
  intros; induction e; solve_instance. 
Defined.

(* Definition subst_r_var (s : subst_t var var) reft := *)
(*   mkReft_type (reft_base reft) (subst s (reft_r reft)). *)

(* Definition subst_base_loc (s : subst_t loc loc) b := *)
(*   match b with *)
(*     | ref_t l => ref_t (s l) *)
(*     | _ => b *)
(*   end. *)

Definition subst_base {D R : Type} {S : Subst loc D R} s b :=
  match b with
    | ref_t l => ref_t (subst s l)
    | _ => b
  end.

Definition nonfv_base {D R : Type} {S : Subst loc D R} b (x : D) :=
  match b with
    | ref_t l => nonfv l x
    | _ => True
  end.

Definition eq_base {D R : Type} {S : Subst loc D R} {E : Equivalence (eq (A := loc))} (b1 b2 : base_type) := 
  match (b1, b2) with
    | (ref_t l, ref_t l') => (eq (D := D)) l l'
    | _ => Logic.eq b1 b2
  end.

Instance Subst_base 
         {D R : Type} 
         `{S : Subst loc D R} 
         {E : Equivalence (eq (A := loc))} : Subst base_type D R := 
  mkSubst _ _ _ (@eq_base D R S E) nonfv_base subst_base.

Instance FVSubst_base 
         {D R : Type} 
         `{S : SubstFV loc D R} 
         {E : Equivalence (eq (A := loc))} : SubstFV base_type D R _ := _.
Proof. 
  constructor; intros; destruct e; solve_instance.
Defined.

Instance Eq_eqBase 
         {D R : Type}
         {S : Subst loc D R}
         {E : Equivalence (@eq loc D R S) } : Equivalence (@eq base_type D R Subst_base).
Proof.
  constructor. 
  hnf; intros; destruct x; try reflexivity. unfold eq. simpl. unfold eq_base. reflexivity.

  hnf; intros; destruct x; destruct y; try inversion H; try reflexivity.
  unfold eq in *; simpl in *; unfold eq_base in *. symmetry. assumption.

  hnf; intros; destruct x; destruct y; try inversion H; destruct z; try inversion H0.
  assumption. assumption. unfold eq in *; simpl in *; unfold eq_base in *. eapply transitivity; eauto.
Defined.

Instance Subst_base_proper 
    {D R : Type} 
    {S : Subst loc D R}
    {P : Proper (Logic.eq ==> (@eq _ _ _ S) ==> (@eq _ _ _ S)) subst}
    {E : Equivalence (eq (A := loc))} :
       Proper (Logic.eq ==> (@eq_base D R S E) ==> (@eq_base D R S E)) subst.
Proof.
  repeat (hnf; intros).
  subst.
  unfold eq_base in H0.
  destruct x0; destruct y0; simpl; try reflexivity; try inversion H0.
  rewrite H0. reflexivity.
Qed.

(* Definition subst_r_loc (s : subst_t loc loc) reft := *)
(*   mkReft_type (subst s (reft_base reft)) (reft_r reft). *)

Definition subst_r {D R : Type} {S : Subst base_type D R} {S' : Subst reft_prop D R} s reft :=
  mkReft_type (subst s (reft_base reft)) (subst s (reft_r reft)).

Definition nonfv_reft_t {D R : Type} {S : Subst base_type D R} {S' : Subst reft_prop D R} 
           reft (x : D) := nonfv (reft_base reft) x /\ nonfv (reft_r reft) x.

Definition eq_reft_r {D R : Type} {S : Subst base_type D R} {S' : Subst reft_prop D R}
           r1 r2 := eq (reft_base r1) (reft_base r2) /\ eq (reft_r r1) (reft_r r2).

(* Instance Subst_reft_var : Subst reft_type var var := subst_r_var. *)
Instance Subst_reft {D R : Type} {S : Subst base_type D R} {S' : Subst reft_prop D R} : Subst reft_type D R
:= (mkSubst _ _ _ eq_reft_r nonfv_reft_t subst_r).

Instance Eq_eq_reft_r { D R : Type } 
         {S : Subst base_type D R}
         {S' : Subst reft_prop D R}
         {E: Equivalence (@eq _ _ _ S)}
         {E': Equivalence (@eq _ _ _ S')} : Equivalence (@eq _ _ _ Subst_reft).
Proof.
  constructor.
  constructor; reflexivity.
  constructor; symmetry; apply H. 
  constructor; eapply transitivity. apply H. apply H0. apply H. apply H0.
Qed.

Instance Eq_eq_reft_r_list : Equivalence (@eq (list reft_type) var var Subst_list) := Eq_eqList.

Instance Subst_reft_var : Subst reft_type var var := Subst_reft.
Instance Subst_reft_expr : Subst reft_type var expr := Subst_reft.
Instance Subst_reft_loc : Subst reft_type loc loc := Subst_reft.

Instance FVSubst_reft
{D R : Type} `{S : SubstFV base_type D R} `{S' : SubstFV reft_prop D R} : SubstFV reft_type D R _.
Proof.
  constructor; intros; solve_instance.
Defined.

Instance Eq_eqReft {D R : Type} {S : Subst base_type D R} {S' : Subst reft_prop D R}
         {Eb : Equivalence (@eq base_type D R S)}
         {Er : Equivalence (@eq reft_prop D R S')}
         : Equivalence (@eq _ _ _ (@Subst_reft D R S S')).
Proof.
  unfold eq. simpl.
  constructor; constructor. 
  reflexivity. reflexivity.
  inversion H; symmetry; assumption.
  inversion H; symmetry; assumption. 
  inversion H. inversion H0. eapply transitivity; eauto.
  inversion H. inversion H0. eapply transitivity; eauto.
Qed.

(* Instance subst_reft_loc : Subst reft_type loc loc := subst_r_loc. *)

Definition type_binding : Set := (var * reft_type)%type.
Hint Transparent type_binding.

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
  Definition eq := @Logic.eq loc.
  Definition eq_refl := @eq_refl loc.
  Definition eq_sym := @eq_sym loc.
  Definition eq_trans := @eq_trans loc.
  Definition lt l l' :=
    match (l, l') with
      | (L n, L n') => n < n'
    end.
  Definition eq_dec := (eq_dec (A := loc)).
  Lemma lt_trans : forall l1 l2 l3,
                     lt l1 l2 -> lt l2 l3 -> lt l1 l3.
  Proof.
    intros.
    unfold lt in *.
    destruct l1. destruct l2. destruct l3.
    pose (Nat_as_OT.lt_trans n n0 n1).
    apply l. apply H. apply H0.
  Qed.

  Lemma lt_not_eq : forall (l1 l2 : loc), lt l1 l2 -> ~ @Logic.eq loc l1 l2.
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

Hint Transparent type_env bind_env.

Instance Subst_heap_bind {D R : Type} {S : Subst loc D R} {S' : Subst type_binding D R}
: Subst (loc * type_binding) D R  := _.

(* Instance Subst_heap_bind_list {D R : Type} {S : Subst loc D R} {S' : Subst type_binding D R} *)
(*          {E : Equivalence (@eq _ _ _ S)} {E' : Equivalence (@eq _ _ _ S')} *)
(* : Subst (list (loc * type_binding)) D R := Subst_list. *)

Definition subst_heap 
           {D R : Type} {S : Subst loc D R} {S' : Subst type_binding D R}
           {E : Equivalence (@eq _ _ _ S)} {E' : Equivalence (@eq _ _ _ S')}
         s (h : heap_env) :=
  HE.fold (fun l xt m => HE.add (subst s l) (subst s xt) m) h (heap_emp).
  (* HE_Props.of_list (@subst (list (loc * type_binding)) D R Subst_list s (HE_Props.to_list h)). *)

Definition nonfv_heap {D R : Type} {S : Subst loc D R} {S : Subst type_binding D R}
         (h : heap_env) (v : D) :=
  forall l xt, HE.MapsTo l xt h -> (nonfv l v /\ nonfv xt v).

Import HE.
Import HE_Facts.
Import HE_Props.

(* Lemma fv_heap_list : *)
(*   forall (D R : Type) (S : Subst loc D R) (S' : Subst type_binding D R)  *)
(*          {E : Equivalence (@eq _ _ _ S)} {E' : Equivalence (@eq _ _ _ S')} *)
(*          (h : heap_env),  *)
(*     (forall x:D, fv_heap h x <-> (@nonfv (list (loc * type_binding)) D R Subst_list (HE.elements h) x)). *)
(* Proof. *)
(*   constructor. { *)
(*     intros. *)
(*     unfold fv_heap in H. *)
(*     destruct H as [l [[y t] [A B]]]. *)
(*     destruct B. *)
(*     simpl. *)
(*     rewrite HE_Props.F.elements_mapsto_iff in A. *)
(*     induction (HE.elements h) as [|[l' [y' t']]]. *)
(*     inversion A. *)
(*     simpl. inversion A. subst. inversion H1. inversion H2. simpl in *. subst. *)
(*     left. left. assumption. *)
(*     destruct y0. destruct t0. inversion H0. subst. *)
(*     right. apply IHl0. assumption. *)
 
(*     rewrite HE_Props.F.elements_mapsto_iff in A. *)
(*     induction (HE.elements h) as [|[l' [y' t']]]. *)
(*     inversion A. *)
(*     simpl in *. inversion A. destruct y0. destruct t0. inversion H1. simpl in *. *)
(*     inversion H0. subst. inversion H4. subst. left. right. assumption. *)
(*     right. apply IHl0. assumption. *)
(*   }  *)
(*   { *)
(*     intros. *)
(*     (* pose (elements_3w h).  *) *)
(*     (* pose (@elements_mapsto_iff _ h). *) *)
(*     unfold fv_heap. *)
(*     setoid_rewrite elements_mapsto_iff. *)
(*     (* generalize i. *) *)
(*     (* clear i. *) *)
(*     induction (elements h). *)
(*     intros. inversion H. *)
(*     intros. *)
(*     destruct a. *)
(*     destruct H. *)
(*     exists k. exists t0. constructor. left. reflexivity. destruct H. left. assumption. right. assumption. *)
(*     apply IHl in H. destruct H. destruct H. *)
(*     destruct H. *)
(*     exists x0. exists x1. constructor. right. assumption. assumption. *)
(*   } *)
(* Qed. *)

Lemma subst_list_step :
  forall (A D R : Type) (S : Subst A D R) (E : Equivalence (@eq _ _ _ S))
    (a : A) (l : list A) s,
    eq (subst s (a :: l)) (subst s a :: subst s l).
Proof.
  intros.
  simpl.
  constructor; reflexivity.
Qed.

Hint Transparent key.
Typeclasses Transparent key type_binding eq_base.

Instance Subst_heap 
           {D R : Type} 
           {S : Subst key D R }
           {S' : Subst type_binding D R }
           {E : Equivalence (@eq _ _ _ S)}
           {E' : Equivalence (@eq _ _ _ S')}
           (* {P: Proper (@eq _ _ _ S ==> @eq _ _ _ S' ==> Equal ==> Equal) (add (elt := type_binding)) } *)
  : Subst heap_env D R := mkSubst _ _ _ HE.Equal nonfv_heap subst_heap.

Instance Subst_heap_var : Subst heap_env var var := Subst_heap.
Instance Subst_heap_loc : Subst heap_env loc loc := Subst_heap.

Instance FVSubst_heap 
           {D R : Type} 
          `{S : SubstFV key D R }
          `{S': SubstFV type_binding D R }
           {E : Equivalence (@eq key D R _)}
           {E': Equivalence (@eq type_binding D R _)}
           {P: Proper (@eq key _ _ _ ==> (@eq type_binding _ _ _) ==> Equal ==> Equal) (add (elt := type_binding)) }
  : SubstFV heap_env D R _.
Proof.
  constructor.
  intros.
  unfold subst, Subst_heap, subst_heap.
  assert (Equal (fold (fun l xt m => add (subst s l) (subst s xt) m) e heap_emp)
                (fold (fun l xt m => add l xt m) e heap_emp)).
  apply (fold_rel (R := Equal) 
                  (f := fun l xt m => add (subst s l) (subst s xt) m)
                  (g := fun l xt m => add l xt m)).
  reflexivity.
  intros.
  unfold nonfv, Subst_heap, nonfv_heap in H. 
  rewrite subst_nonfv.
  rewrite subst_nonfv.
  apply add_m; easy.
  solve_instance.
  solve_instance.
  rewrite H0.
  apply fold_identity.
Defined.

(* Instance Subst_binding_loc : Subst type_binding loc loc := *)
(*   fun s xt => (fst xt, subst s (snd xt)). *)

(** Procedures **)
Record proc_schema : Type :=
  mkSchema { s_formals: list var;
             s_formal_ts: list reft_type;
             s_heap_in: heap_env;
             s_heap_out: heap_env;
             s_ret: type_binding }.

Definition subst_schema 
           {D R : Type} {Sv : Subst var D R } {St : Subst reft_type D R} {Sl : Subst key D R}
           {E : Equivalence (@eq _ _ _ Sv)}
           {E' : Equivalence (@eq _ _ _ St)}
           {E'' : Equivalence (@eq _ _ _ Sl)}
           {E''' : Equivalence (@eq type_binding _ _ _)}
           (* {P : Proper ((@eq _ _ _ Sl) ==> (@eq type_binding _ _ _) ==> Equal ==> Equal) *)
           (*             (add (elt := type_binding))} *)
           (s : subst_t D R) S :=
  match S with
    | mkSchema xs ts hi ho xt =>
      mkSchema (subst s xs) (subst s ts) (subst s hi) (subst s ho) (subst s xt)
  end.

Definition nonfv_schema
           {D R : Type} {Sv : Subst var D R } {St : Subst reft_type D R} {Sl : Subst key D R}
           {E : Equivalence (@eq _ _ _ Sv)}
           {E' : Equivalence (@eq _ _ _ St)}
           {E'' : Equivalence (@eq _ _ _ Sl)}
           {E''' : Equivalence (@eq type_binding _ _ _)}
           (* {P : Proper ((@eq _ _ _ Sl) ==> (@eq type_binding _ _ _) ==> Equal ==> Equal) *)
           (*             (add (elt := type_binding))} *)
           s x :=
  match s with
    | mkSchema xs ts hi ho xt =>
     nonfv xs x /\ nonfv ts x /\ nonfv hi x /\ nonfv ho x /\ nonfv xt x
  end.

Definition eq_schema
           {D R : Type} {Sv : Subst var D R } {St : Subst reft_type D R} {Sl : Subst key D R}
           {E : Equivalence (@eq _ _ _ Sv)}
           {E' : Equivalence (@eq _ _ _ St)}
           {E'' : Equivalence (@eq _ _ _ Sl)}
           {E''' : Equivalence (@eq type_binding _ _ _)}
           (* {P : Proper ((@eq _ _ _ Sl) ==> (@eq type_binding _ _ _) ==> Equal ==> Equal) *)
           (*             (add (elt := type_binding))} *)
           (s1 s2 : proc_schema) :=
  let (xs, ts, hi, ho, xt) := s1 in
  let (xs', ts', hi', ho', xt') := s2 in
  eq xs xs' /\ eq ts ts' /\ eq hi hi' /\ eq ho ho' /\ eq xt xt'.

Instance Subst_schema
           {D R : Type} {Sv : Subst var D R } {St : Subst reft_type D R} {Sl : Subst key D R}
           {E : Equivalence (@eq _ _ _ Sv)}
           {E' : Equivalence (@eq _ _ _ St)}
           {E'' : Equivalence (@eq _ _ _ Sl)}
           {E''' : Equivalence (@eq type_binding _ _ _)} :
            Subst proc_schema D R := mkSubst _ _ _ eq_schema nonfv_schema subst_schema.
Instance FVSubst_schema
           {D R : Type} `{Sv : SubstFV var D R } `{St : SubstFV reft_type D R} `{Sl : SubstFV key D R}
           {E : Equivalence (@eq var D R _)}
           {E' : Equivalence (@eq reft_type D R _)}
           {E'' : Equivalence (@eq key D R _)}
           {E''' : Equivalence (@eq type_binding D R _)} 
           {P : Proper ((@eq key _ _ _) ==> (@eq type_binding _ _ _) ==> Equal ==> Equal)
                       (add (elt := type_binding))}
         : SubstFV proc_schema D R Subst_schema := _.
Proof.
  constructor.
  intros θ [xs ts hi ho xt].
  intro.
  unfold eq.
  unfold subst.
  unfold Subst_schema. unfold eq_schema. unfold subst_schema.
  unfold nonfv in H. unfold Subst_schema in H. unfold nonfv_schema in H.
  repeat rewrite subst_nonfv;
  first [repeat constructor; reflexivity | apply H].
Defined.

Definition proc_env : Type := bind_env pname (stmt * proc_schema)%type.

Definition var_in : var -> type_env -> Prop := 
  fun x Γ => exists t, List.In (x, t) Γ.

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
  fun l Γ => Forall (fun xt => ~ List.In l (ty_loc (snd xt))) Γ.

Definition fun_in : (pname * (stmt * proc_schema)) -> proc_env -> Prop :=
  fun ft Φ => List.In ft Φ.

Definition fun_not_in : pname  -> proc_env -> Prop :=
  fun f Φ => Forall (fun ft => fst ft <> f) Φ.

Notation "X ∈ Y" := (List.In X Y) (at level 40).

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
  hnf. decide equality; apply eq_dec.eq_dec.
Qed.

Instance EqDec_reft_prop : EqDec reft_prop := _.
Proof.
  hnf. decide equality; try apply eq_dec.eq_dec.
Qed.

Instance EqDec_reft_type : EqDec reft_type := _.
Proof.
  hnf. decide equality; try apply eq_dec.eq_dec.
Qed.

Class SubstReft (D R : Type) `{SubstFV expr D R} `{ SubstFV reft_prop D R} : Type := 
  mkSubstReft {
      subst_tt_r : 
        forall (s : subst_t D R), 
          subst s tt_r = tt_r
      ;
      subst_rel_r : 
        forall (s : subst_t D R) e1 e2, 
          subst s (e1 .= e2) = (subst s e1 .= subst s e2)
      ;
      subst_not_r :
        forall (s : subst_t D R) p,
          subst s (not_r p) = not_r (subst s p)
      ;
      subst_and_r :
        forall (s : subst_t D R) p1 p2, 
          subst s (and_r p1 p2) = (and_r (subst s p1) (subst s p2))
      ;
      subst_or_r :
        forall (s : subst_t D R) p1 p2, 
          subst s (or_r p1 p2) = (or_r (subst s p1) (subst s p2))
    }.

Ltac rw_subst_reft :=
  repeat first [ setoid_rewrite subst_tt_r
               | setoid_rewrite subst_rel_r
               | setoid_rewrite subst_not_r
               | setoid_rewrite subst_or_r
               | setoid_rewrite subst_and_r
               ].

Instance SubstReft_var_var : SubstReft var var. 
Proof. solve_instance. Qed.

Instance SubstReft_var_expr : SubstReft var expr. 
Proof. solve_instance. Qed.

Instance SubstReft_loc_loc : SubstReft loc loc. 
Proof. solve_instance. Qed.

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