Add LoadPath "vst".

Require Export Coq.Structures.Equalities.
Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import List.
Import ListNotations.
Require Export Coq.Classes.Morphisms.
Import ProperNotations.
Require Import Setoid Morphisms RelationClasses Equivalence.

Definition subst_t (D : Type) (R : Type) := D -> option R.

Definition subst_one {D R : Type} {E: EqDec D} (x : D) (e : R) i := 
  if eq_dec x i then Some e else None.
(* Definition subst_one { D R : Type } { E : EqDec D } (d : D) (r : R) : subst_t D R := *)
(*   fun d' => if eq_dec d d' then Some r else None. *)

(* Definition wf_subst{A : Type} (s : subst_t A) : Prop  := NoDup (fst (split s)). *)
Class Subst (A D R : Type) := mkSubst {
  eq : A -> A -> Prop
  ;
  nonfv: A -> D -> Prop
  ;
  subst: subst_t D R -> A -> A 
}.

Class SubstFV (A D R : Type) `( S : Subst A D R ) := mkSubstFV {
  subst_nonfv: 
    forall (s : subst_t D R) e, 
      (forall x, s x <> None -> nonfv e x) -> eq (subst s e) e
}.

Definition fv_prod {A B D R : Type} `{SA :Subst A D R} `{SB : Subst B D R} (p : (A * B)) :=
  fun x => 
    match p with
      | (p1, p2) => nonfv p1 x /\ nonfv p2 x
    end.

Definition subst_prod {A B D R : Type} {SA : Subst A D R} {SB : Subst B D R} (s : subst_t D R) (p : (A * B)) :=
  match p with
    | (p1, p2) => (subst s p1, subst s p2)
  end.

Require Import Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Definition eq_prod {A B D R : Type} 
                   {SA : Subst A D R} {SB : Subst B D R} 
                   (p1 : (A * B)) (p2 : (A * B)) :=
  let (a, b) := p1 in
  let (x, y) := p2 in
  @eq A D R SA a x /\ @eq B D R SB b y.

Instance Eq_eqProd {A B D R : Type} {SA : Subst A D R} {SB : Subst B D R} 
         {E1 : Equivalence (eq (A := A)) }
         {E2 : Equivalence (eq (A := B)) }
: Equivalence (@eq_prod A B D R SA SB).
Proof.
  constructor.
  + hnf; destruct x; unfold eq_prod. 
    constructor; reflexivity.
  + hnf. destruct x. destruct y. intros. unfold eq_prod in *. 
    constructor; symmetry; apply H.
  + hnf. destruct x. destruct y. destruct z.
    intros.
    unfold eq_prod in *.
    destruct H. destruct H0.
    constructor.
    apply (transitivity H H0).
    apply (transitivity H1 H2).
Qed.

Instance Subst_prod (A B D R : Type) `{SA : Subst A D R } `{SB : Subst B D R}: Subst (A * B) D R.
Proof.
  refine (mkSubst _ _ _ eq_prod fv_prod subst_prod). 
Defined.

Instance FVSubst_prod {A B D R : Type} `{ SA : SubstFV A D R } `{ SB : SubstFV B D R } 
          : SubstFV (A * B) D R _ := _.
Proof.
  constructor.
  intros.
  destruct e.
  unfold subst; simpl.
  constructor;
  apply subst_nonfv; 
  repeat intro; apply H; intuition.
Defined.

Instance Subst_prod_proper 
         {A B D R : Type} 
         (SA : Subst A D R)
         (SB : Subst B D R)
         {E1: Equivalence (eq (A := A))}
         {E2: Equivalence (eq (A := B))}
         {P1: Proper (Logic.eq ==> eq (A := A) ==> eq (A := A)) subst }
         {P2: Proper (Logic.eq ==> eq (A := B) ==> eq (A := B)) subst }
         : Proper (Logic.eq ==> eq (A := (A * B)) ==> eq (A := (A * B))) subst.
Proof.
  hnf.
  intros s1 s2 ? [x1 y1] [x2 y2] eqxy.
  subst.
  inversion eqxy.
  simpl.
  rewrite H.
  rewrite H0.
  constructor; reflexivity.
Qed.

Fixpoint subst_list (A D R : Type) (SA : Subst A D R) (s : subst_t D R) (l : list A) :=
  match l with
    | nil => []
    | h :: t => subst s h :: subst_list A D R SA s t
  end.

Fixpoint fv_list {A D R : Type} {SA : Subst A D R} (l : list A) x :=
  match l with
    | nil => False
    | h :: t => @nonfv A D R SA h x /\ @fv_list A D R SA t x
  end.

Fixpoint eq_list { A D R : Type } { SA : Subst A D R } (l1 : list A) (l2 : list A) :=
  match (l1, l2) with
    | ([], []) => True
    | (h1 :: t1, h2 :: t2) => @eq A D R SA h1 h2 /\ eq_list t1 t2
    | _ => False
  end.

Instance Eq_eqList { A D R : Type }{ SA : Subst A D R } { E : Equivalence (eq (A := A)) } 
: Equivalence (@eq_list A D R SA).
Proof.
  constructor.
  hnf. induction x. reflexivity. simpl. constructor.  reflexivity. assumption.
  hnf. intro x. induction x; intros; destruct y.
  constructor. 
  inversion H.
  inversion H.
  simpl in *.
  constructor.
  symmetry.
  apply H.
  apply IHx. apply H.
  (** transitivity **)
  hnf.
  induction x; intros; destruct y; destruct z; try reflexivity;
  try match goal with 
        | H : eq [] ?x |- _ => inversion H
        | H : eq ?x [] |- _ => inversion H
        | H : eq_list [] ?x |- _ => inversion H
        | H : eq_list ?x [] |- _ => inversion H
      end.
  inversion H.
  simpl in *.
  destruct H. destruct H0.
  constructor. eapply transitivity; eauto. eapply IHx; eauto.
Qed.
  
Instance Subst_list {A D R : Type} {SA : Subst A D R} { E: Equivalence (eq (A := A)) }
: Subst (list A) D R := 
  (mkSubst _ _ _ eq_list fv_list (subst_list A D R SA)).

Instance FVSubst_list {A D R : Type} `{SA : SubstFV A D R} { E: Equivalence (eq (A := A)) }
: SubstFV (list A) D R _.
Proof.
  constructor.
  intros.
  induction e.
  + reflexivity.
  + unfold subst_list; fold subst_list.
    unfold fv_list in *. fold fv_list in *.
    simpl; constructor.
    apply subst_nonfv.
    repeat intro. apply H. intuition.
    rewrite IHe.
    reflexivity.
    repeat intro. apply H. intuition.
Defined.

Instance Subst_list_proper 
  {A D R : Type} {SA : Subst A D R} {E : Equivalence (eq (A := A))} 
  {P : Proper (Logic.eq ==> eq ==> eq) (subst (A := A))}
  : Proper (Logic.eq ==> eq ==> eq) (subst (A := list A)).
Proof.
  hnf.
  intros s1 s2 ?. subst.
  intro l. induction l as [ | h l ]; intros; destruct y.
  + reflexivity.
  + inversion H.
  + inversion H.
  + simpl. destruct H. rewrite H.
    constructor. reflexivity. apply IHl. assumption.
Qed.

Lemma subst_cons :
  forall { A D R : Type } { S : Subst A D R } { E : Equivalence (@eq _ _ _ S) }
         (s : subst_t D R) h t,
    subst s (h :: t) = subst s h :: subst s t.
Proof. firstorder. Qed.

Lemma subst_app :
  forall { A D R : Type } { S : Subst A D R } {E : Equivalence (@eq _ _ _ S) }
         (s : subst_t D R) l1 l2,
    subst s (l1 ++ l2) = subst s l1 ++ subst s l2.
Proof.
  intros.
  induction l1.
  reflexivity.
  rewrite subst_cons.
  simpl. f_equal. apply IHl1.
Qed.

Lemma subst_pair :
  forall { X Y D R : Type } { SX : Subst X D R } {SY : Subst Y D R} 
         (x : X) (y : Y) (s : subst_t D R),
    subst s (x, y) = (subst s x, subst s y).
Proof. reflexivity. Qed.

Lemma subst_rev :
  forall { A D R : Type } { S : Subst A D R } { E : Equivalence (@eq _ _ _ S) }
         s l,
    subst s (rev l) = rev (subst s l).
Proof.
  induction l; eauto.
  rewrite subst_cons.
  simpl.
  setoid_rewrite subst_app.
  rewrite IHl.
  reflexivity.
Qed.

Ltac step_subst := 
  try first [ rewrite subst_pair
            | rewrite subst_cons
            | rewrite subst_app
            | rewrite subst_rev
            ].