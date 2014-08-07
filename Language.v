(**  Module defining the programming languages:
     - Values
     - Expressions
     - Statements **)
Add LoadPath "vst".
Require Import Arith.
Require Import List.
Require Import Subst.
Require Import msl.eq_dec.
Import Relations. 

Delimit Scope lang_scope with lang.

Inductive var : Set := V : nat -> var.
Inductive pname : Set := P : nat -> pname.

Inductive value : Set :=
  | int_v  : nat -> value
  | bool_v : bool -> value.

Inductive expr :=
  | value_e : value -> expr
  | var_e : var -> expr.

Record proc :=
    { p_arity: nat;
      p_args: list var;
      p_mod: list var
    }.

Inductive stmt :=
  | skip_s : stmt
  | assign_s : var -> expr -> stmt
  | proc_s : var  -> pname -> list var -> stmt (* x = p(e0...en) *)
  | seq_s  : stmt -> stmt -> stmt.

(* Coercion int_v: nat >-> value. *)
Coercion value_e: value >-> expr.
(* Coercion var_e: var >-> expr. *)

(*** Equality ***)
Instance EqDec_value : EqDec value := _.
Proof.
  hnf. decide equality. 
    decide equality. 
    decide equality.
Qed.

Instance EqDec_var : EqDec var := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_pname : EqDec pname := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_expr : EqDec expr := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_proc : EqDec proc := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_stmt : EqDec stmt := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

(*** Substitutions ***)
Fixpoint subst_var (s:subst_t var) (v:var) := 
  match s with 
    | nil => v
    | (x, x') :: s' => if eq_dec x v then x' else subst_var s' v
  end.

Instance Subst_var_var : Subst var var := subst_var.

Fixpoint subst_expr (s:subst_t var) (e:expr) := 
  match e with 
    | var_e v => (var_e (subst_var s v))
    | _ => e
  end.
Instance Subst_var_expr : Subst expr var := fun s v => subst_expr s v.

Fixpoint subst_stmt (s:subst_t var) (st:stmt) :=
  match st with
    | proc_s x p xs => proc_s (subst s x) p (subst s xs)
    | assign_s x e => assign_s (subst s x) (subst s e)
    | _ => st
  end.

Instance Subst_stmt : Subst stmt var := subst_stmt.

(**** Semantics ****)
(*** a la Appel, PLFCC ***)
Definition table (A B : Type) := list (A * B).
Fixpoint table_get {A B}{H: EqDec A} (rho: table A B) (x: A) : option B :=
  match rho with
  | (y,v)::ys => if eq_dec x y then Some v else table_get ys x
  | nil       => None
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

Definition eval s e :=
  match e with
    | value_e v => Some v
    | var_e v   => s v
  end.