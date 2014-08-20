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
Import ListNotations.

Delimit Scope lang_scope with lang.

Inductive var : Set := V : nat -> var.
Inductive pname : Set := P : nat -> pname.

Inductive value : Set :=
  | int_v  : nat -> value.

Inductive expr :=
  | value_e : value -> expr
  | var_e   : var -> expr
  | fun_e   : pname -> expr -> expr -> expr. 

Fixpoint fv_expr e :=
  match e with
    | var_e v => [v]
    | fun_e f e1 e2 => fv_expr e1 ++ fv_expr e2
    | _ => []
  end.

(* 
Procedure p(x0 ... xn)
- return value is stored in one of p_mod 
*)
Record proc' s :=
    { p_arity: nat;
      p_args: list var;
      p_mod: list var;
      p_body: s
    }.

Inductive stmt :=
  | skip_s   : stmt
  | assign_s : var -> expr -> stmt
  | proc_s   : pname -> list var -> list var -> stmt (* p(x0...xn), modifies y0...yn *)
  | seq_s    : stmt -> stmt -> stmt.

Definition proc := proc' stmt.
Definition mkProc := Build_proc' stmt.

(* Coercion int_v: nat >-> value. *)
Coercion value_e: value >-> expr.
(* Coercion var_e: var >-> expr. *)

(*** Equality ***)
Instance EqDec_value : EqDec value := _.
Proof.
  hnf. decide equality; apply eq_dec.
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
  hnf. decide equality; apply eq_dec.
Qed.

Instance EqDec_stmt : EqDec stmt := _.
Proof.
  hnf.
  decide equality;
  apply eq_dec.
Qed.

(*** Substitutions ***)
Definition subst_var (s:subst_t var var) (v:var) := s v.
Instance Subst_var_var : Subst var var var := subst_var.

Definition subst_var_one (v : var) (v' : var) : subst_t var var  :=
  fun i => if eq_dec i v then v' else i.

Fixpoint subst_expr_var (s:subst_t var var) (e:expr) := 
  match e with 
    | var_e v => var_e (s v)
    | fun_e p e1 e2 => fun_e p (subst_expr_var s e1) (subst_expr_var s e2)
    | _ => e
  end.
Instance Subst_var_var_expr : Subst expr var var := fun s v => subst_expr_var s v.

Fixpoint subst_expr (s:subst_t var expr) (e:expr) := 
  match e with 
    | var_e v => s v
    | fun_e p e1 e2 => fun_e p (subst_expr s e1) (subst_expr s e2)
    | _ => e
  end.
Instance Subst_var_expr : Subst expr var expr := fun s v => subst_expr s v.

Fixpoint subst_stmt (s:subst_t var var) (st:stmt) :=
  match st with
    | proc_s p xs os => proc_s p (subst s xs) (subst s os)
    | assign_s x e => assign_s (subst s x) (subst s e)
    | _ => st
  end.

Instance Subst_stmt : Subst stmt var var := subst_stmt.

Definition state := var -> value.

Parameter eval_fun : pname -> expr -> expr -> value.

Fixpoint eval s e :=
  match e with
    | value_e v => v
    | var_e v   => s v
    | fun_e f e1 e2 => 
      let v1 := eval s e1 in
      let v2 := eval s e2 in
      eval_fun f v1 v2
  end.