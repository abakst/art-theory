Add LoadPath "vst".

Require Import Subst.
Require Import Language.
Require Import msl.msl_direct.

Delimit Scope logic_scope with logic.

Definition world := state.

Definition eval_to (e: expr) (v:value) : pred world :=
  fun w => eval w e = v.

Instance Join_world: Join world := Join_equiv world.

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Sep_alg world := _.
Instance Canc_world : Canc_alg world := _.
Instance Disj_world : Disj_alg world := _.

Definition fun_set (f: var -> option value) (x: var) (y: option value) :=
  fun i => if eq_dec i x then y else f i.

Definition subst_one (x : var) (e : expr) :=
  fun i => if eq_dec i x then e else (var_e i).

Definition subst_pred sub (P: pred world) : (pred world) := 
  fun w =>
    P (fun i => eval w (sub i)).

Definition subst_pred_var sub (P: pred world) : pred world :=
  fun w =>
    P (fun i => eval w (var_e (sub i))).
    
Instance Subst_pred_var : Subst (pred world) var var := subst_pred_var.
Instance Subst_pred : Subst (pred world) var expr := subst_pred.
                 
Definition equal (x y: var) : pred world :=
  fun w => w x = w y.

Inductive modvars : stmt -> var -> Prop :=
| mod_assign: forall x e, modvars (assign_s x e) x
| mod_proc: forall x f xs os, 
              In x os ->
              modvars (proc_s f xs os) x
| mod_seq1: forall x s1 s2, modvars s1 x -> modvars (seq_s s1 s2) x
| mod_seq2: forall x s1 s2, modvars s2 x -> modvars (seq_s s1 s2) x.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall stk v, P stk -> subst_pred (subst_one x v) P stk.

Definition subset (S1 S2 : var -> Prop) := forall x, S1 x -> S2 x.

Definition procspec := (pname * proc * pred world * pred world)%type.
  
Definition procspecs := list procspec.

Definition not_free_in (v : var) (v' : var) := v <> v'.

Definition unique_sub s (v : var) :=
  exists v', (s v = v' /\ (forall x, x <> v -> not_free_in v' (s x))).

Inductive semax : procspecs -> pred world -> stmt -> pred world -> Prop :=
  | semax_skip : 
      forall F P, semax F P skip_s P
  | semax_assign :
      forall F P x e,
        semax F (EX v : value, 
                      eval_to e v 
                   && subst_pred (subst_one x e) P) (assign_s x e)  P 
  | semax_proc :
      forall f p (F : procspecs) P Q,
        In (f, p, P, Q) F ->
        semax F P (proc_s f (p_args stmt p) (p_mod stmt p)) Q
  | semax_seq : 
      forall F P Q R s1 s2,
        semax F P s1 Q -> semax F Q s2 R -> 
        semax F P (seq_s s1 s2) R
  | semax_if :
      forall F P Q e s1 s2,
        semax F ((eval_to e (int_v 0) --> FF) && P) s1 Q -> 
        semax F (eval_to e (int_v 0) && P) s2 Q ->
        semax F P (if_s e s1 s2) Q
  | semax_subst :
      forall F P s Q θ,
        semax F P s Q -> (forall x, (modvars s x -> unique_sub θ x)) ->
        semax F (subst θ P) (subst θ s) (subst θ Q)
  | semax_pre_post :
      forall F P P' s Q Q',
        (P |-- P') -> (Q' |-- Q) -> semax F P' s Q' ->
        semax F P s Q
  | semax_frame :
      forall F P Q R s,
        semax F P s Q -> subset (modvars s) (nonfreevars R) ->
        semax F (P * R)%pred s (Q * R)%pred.

Notation "F |- {{ P }} s {{ Q }}" := (semax F P%pred s Q%pred) (no associativity, at level 90).

(* Definition x:var := 0. *)

(* Example ex1: *)
(*   {{ TT }} assign_s x 1 {{ TT }}. *)
(* Proof. *)
(*   apply semax_pre_post with (P' := (eval_to (value_e 1) (int_v 1) && (subst x (Some (int_v 1)) TT))%pred) (Q' := TT). *)
(*   constructor. reflexivity. constructor. auto. apply semax_assign. *)
(* Qed. *)