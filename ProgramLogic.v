Add LoadPath "vst".
Require Import Language.
Require Import msl.msl_direct.

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

Definition subst_pred (x : var) (v : option value) (P: pred world) : (pred world) := 
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

(* Inductive safe : (list stmt * state) -> Prop := *)
(* | safe_step: forall s1 s2, step s1 s2 -> safe s2 -> safe s1 *)
(* | safe_halt: forall s, safe (nil, s). *)

(* Definition guards (P: pred world) (ss : list stmt) : Prop := *)
(*   forall s, P (den s) -> safe (ss, s). *)

Inductive semax : pred world -> stmt -> pred world -> Prop :=
  | semax_skip : 
      forall P, semax P skip_s P
  | semax_assign :
      forall P x e,
        semax (EX v : value, eval_to e v && subst_pred x (Some v) P) (assign_s x e)  P 
  | semax_seq : 
      forall P Q R s1 s2,
        semax P s1 Q -> semax Q s2 R -> 
        semax P (seq_s s1 s2) R
  | semax_pre_post :
      forall P P' s Q Q',
        (P |-- P') -> (Q' |-- Q) -> semax P' s Q' ->
        semax P s Q.
  
Notation "{{ P }} s {{ Q }}" := (semax P%pred s Q%pred) (at level 90).

(* Definition x:var := 0. *)

(* Example ex1: *)
(*   {{ TT }} assign_s x 1 {{ TT }}. *)
(* Proof. *)
(*   apply semax_pre_post with (P' := (eval_to (value_e 1) (int_v 1) && (subst x (Some (int_v 1)) TT))%pred) (Q' := TT). *)
(*   constructor. reflexivity. constructor. auto. apply semax_assign. *)
(* Qed. *)