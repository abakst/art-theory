Add LoadPath "vst".
Require Import msl.msl_direct.
Require Export Lang.

Delimit Scope logic_scope with logic.

Definition world := var -> option value.
Definition den (s: state) : world := table_get s.
Definition defined (y: var) : pred world :=
   fun w => exists v, w y = Some v.

Definition eval_to (e: expr) (v:value) : pred world :=
  fun w => eval w e = Some v.

Instance Join_world: Join world := Join_equiv world.

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Sep_alg world := _.
Instance Canc_world : Canc_alg world := _.
Instance Disj_world : Disj_alg world := _.

Definition fun_set (f: var -> option value) (x: var) (y: option value) :=
  fun i => if eq_dec i x then y else f i.

Definition subst (x : var) (v : option value) (P: pred world) : (pred world) := 
  fun w => P (fun_set w x v).

Definition equal (x y: var) : pred world :=
  fun w => w x = w y.

Inductive modvars : stmt -> var -> Prop :=
| mod_assign: forall x e, modvars (assign_s x e) x
| mod_seq1: forall x s1 s2, modvars s1 x -> modvars (seq_s s1 s2) x
| mod_seq2: forall x s1 s2, modvars s2 x -> modvars (seq_s s1 s2) x.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall stk v, P stk -> P (fun_set stk x v).

Definition subset (S1 S2 : var -> Prop) := forall x, S1 x -> S2 x.

Inductive safe : (list stmt * state) -> Prop :=
| safe_step: forall s1 s2, step s1 s2 -> safe s2 -> safe s1
| safe_halt: forall s, safe (nil, s).

Definition guards (P: pred world) (ss : list stmt) : Prop :=
  forall s, P (den s) -> safe (ss, s).

Definition semax (P: pred world) (s: stmt) (Q: pred world): Prop :=
  forall F, subset (modvars s) (nonfreevars F) ->
    forall k, guards (Q * F) k -> guards (P * F) (s :: k).

Notation "{{ P }} s {{ Q }}" := (semax P%pred s Q%pred) (at level 90).

Lemma semax_skip:
  forall P, {{ P }} skip_s {{ P }}. (*(semax P skip_s P).*)
Proof.
  intros P.
  unfold semax.
  intros F H k HG st HP.
  eapply safe_step. constructor. 
  eauto.
Qed.

Lemma semax_seq:
  forall P Q R s1 s2, 
    {{ P }} s1 {{ Q }} -> {{ Q }} s2 {{ R }} -> 
    {{ P }} seq_s s1 s2 {{ R }} .
Proof.  
  intros P Q R s1 s2.
  intros S1 S2.
  intros F H k H0 s H1.
  assert (safe ( s1 :: s2 :: k, s)).
  Focus 2.
    inv H2; eapply safe_step; [constructor | eauto]; auto.
  apply (S1 F); auto.
  intros ? ?. apply H. apply mod_seq1. auto.
  apply S2.
  intros ? ?. apply H. apply mod_seq2. auto.
  auto.
Qed.

Lemma semax_assign:
  forall P x e v,
    {{ (subst x (Some v) P && eval_to e v) }} assign_s x e {{ P }}.
Proof.
  intros P x e v.
  intros F S k H0 st H1.
  destruct H1 as [stk1 [stk2 [A [[B C] D]]]].
  destruct A as [E1 E2]. rewrite E2 in *. 
  eapply safe_step. constructor.
  unfold eval_to in C.
  unfold den in *.
  rewrite <- E1. symmetry in C. apply C.
  apply H0.
  exists (fun_set (table_get st) x (Some v)). 
  exists (fun_set (table_get st) x (Some v)). 
  split; [| split].
  split; auto.
  unfold den in *.
  unfold subst in B. rewrite <- E1. apply B.
  unfold den in *. 
  apply (S x).
  apply mod_assign. 
  assumption.
Qed.

Lemma semax_frame:
  forall F P s Q,
    subset (modvars s) (nonfreevars F) ->
    {{ P }} s {{ Q }} ->
    {{ (P * F) }} s {{ (Q * F) }}.
Proof.
  repeat intro.
  rewrite sepcon_assoc in H2,H3. 
  assert (guards (P * (F * F0)) (s :: k)).
  apply H0. intros ? ?. 
  unfold subset in H.
  specialize (H x H4).
  specialize (H1 _ H4).
  repeat intro. 
  destruct H5 as [stk1 [stk2 [[? ?] [? ?]]]].
  subst.
  exists (fun_set stk x v).
  exists (fun_set stk x v).
  split; auto.
  split; auto. 
  apply H2; auto.
  apply H4; auto.
Qed.

Lemma semax_consequence:
  forall P P' s Q Q',
   P |-- P' -> Q' |-- Q -> {{ P' }} s {{ Q' }} ->
   {{ P }} s {{ Q }}.
Proof.
  repeat intro.
  apply (H1 F); auto.
  intros ? ?.
  apply H3.
  eapply sepcon_derives; try apply H5; auto.
  eapply sepcon_derives; try apply H4; auto.
Qed.

 
Example ex1: 
  {{ fun s => s 0 = (Some (int_v 0)) }} skip_s {{ TT }}.
Proof.
  eapply semax_consequence with (P' := TT) (Q' := TT) .
  repeat intro. constructor. constructor.
  apply semax_skip.
Qed.

Definition x : var := 0.
Definition one := int_v 1.
Definition n : expr := (value_e one).
Definition P := fun s => eval s x = Some one.

Example ex2:
  {{ TT }} assign_s x n {{ P }}.
Proof.
  apply semax_consequence with 
    (P' := (subst x (Some one) P && eval_to n one)%pred) (Q' := P).
  repeat intro. unfold P. unfold subst. unfold fun_set. 
  split; reflexivity. auto.
  apply semax_assign.
Qed.

(* ; specialize (H1 _ H4). *)
