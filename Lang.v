(**  Module defining the programming languages:
     - Values
     - Expressions
     - Statements **)

Add LoadPath "vst".
Require Import Arith.
Require Import List.
Require Import msl.eq_dec.
Import Relations. 

Delimit Scope lang_scope with lang.

Definition var := nat.

Inductive value : Set :=
  | int_v  : nat -> value
  | bool_v : bool -> value.

(* Inductive bop := *)
(*   | plus_o : bop. *)

(* (** First we will need a notion of expressions in the language **) *)
(* Inductive expr :=  *)
(*   | value_e : value -> expr *)
(*   | var_e   : var -> expr *)
(*   | bop_e   : expr -> bop -> expr -> expr. *)

(* Fixpoint subst_expr (x:var) (e':expr) (e:expr) :=  *)
(*   match e with *)
(*     | var_e x' =>  *)
(*       if eq_dec x' x then e' else e *)
(*     | bop_e e1 o e2 =>  *)
(*       bop_e (subst_expr x e' e1) o (subst_expr x e' e2) *)
(*     | _ => e *)
(*   end. *)
      

(** Statements: all the fun stuff *)
Inductive stmt :=
  | skip_s   : stmt
  (* | assign_s : var -> expr -> stmt *)
  | seq_s    : stmt -> stmt -> stmt.

Coercion int_v: nat >-> value.
Coercion value_e: value >-> expr.
Coercion var_e: var >-> expr.
Notation "x .+ y" := (bop_e x plus_o y) (at level 57, right associativity).

(**** Semantics ****)
(*** a la Appel, PLFCC ***)
Definition table (A B : Type) := list (A * B).
Fixpoint table_get {A B}{H: EqDec A} (rho: table A B) (x: A) : option B :=
  match rho with
  | (y,v)::ys => if eq_dec x y then Some v else table_get ys x
  | nil => None
 end.

Definition table_set {A B}{H: EqDec A} (x: A) (v: B) (rho: table A B)  : table A B := (x,v)::rho.

Lemma table_gss {A B}{H: EqDec A}: forall rho x (v: B), table_get (table_set x v rho) x = Some v.
Proof.
intros.
simpl. destruct (eq_dec x x); auto. contradiction n; auto.
Qed.

Lemma table_gso {A B}{H: EqDec A}: forall rho x y (v:B), x<>y -> table_get (table_set x v rho) y = table_get rho y.
Proof.
intros.
simpl. destruct (eq_dec y x); auto.  contradiction H0; auto.
Qed.

Definition state := table var value.

Definition apply_op' o v1 v2 := 
  match (o, v1, v2) with
    | (plus_o, int_v v1', int_v v2') => 
      Some (int_v (v1' + v2'))
    | _ =>
      None
  end.

Definition apply_op o v1 v2 :=
  match (v1, v2) with
    | (Some v1', Some v2') => apply_op' o v1' v2'
    | _ => None
  end.

Fixpoint eval s e :=
  match e with
  | value_e v       => Some v
  | var_e   x       => s x
  | bop_e   e1 o e2 => apply_op o (eval s e1) (eval s e2)
  end.

Inductive step : relation (list stmt * state) :=
  | step_skip : 
      forall k s,
        step (skip_s :: k, s) (k, s)
  | step_assign :
      forall k s x e v,
      Some v = eval (table_get s) e -> 
      step (assign_s x e :: k, s) (k, table_set x v s)
  | step_seq :
      forall k s c1 c2 cs',
        step (c1 :: c2 :: k, s) cs' ->
        step (seq_s c1 c2 :: k, s) cs'.