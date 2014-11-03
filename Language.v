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

Inductive var   : Set := V : nat -> var.
Inductive addr  : Set := A : nat -> addr.
Inductive pname : Set := P : nat -> pname.

Inductive value : Set :=
  | int_v  : nat -> value
  | addr_v : addr -> value.

Definition null   := A 0.
Definition null_v := addr_v null.

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

Definition FV e x := In x (fv_expr e).
  
(* 
Procedure p(x0 ... xn)
- return value is stored in one of p_mod 
*)
Record proc' {s} :=
    { p_args: list var;
      p_ret: var;
      p_mod: list var;
      p_body: s }.

Inductive stmt :=
| skip_s   : stmt
| pad_s    : var -> var -> stmt
| alloc_s  : var -> var -> expr -> stmt
| assign_s : var -> expr -> stmt
| proc_s   : pname -> list var -> var -> list var -> stmt (* p(x0...xn), modifies y0...yn *)
| seq_s    : stmt -> stmt -> stmt
| if_s     : expr -> stmt -> stmt -> stmt
| return_s : expr -> stmt.

Definition proc := @proc' stmt.

Inductive program := 
| entry_p    : stmt -> program
| procdecl_p : pname -> proc -> program -> program.

Definition mkProc := Build_proc' stmt.

(* Coercion int_v: nat >-> value. *)
Coercion value_e: value >-> expr.
(* Coercion var_e: var >-> expr. *)

(*** Equality ***)
Instance EqDec_var : EqDec var := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_addr : EqDec addr := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_pname : EqDec pname := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_value : EqDec value := _.
Proof.
  hnf. decide equality; apply eq_dec.
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
    | proc_s p xs r os => proc_s p (subst s xs) (subst s r) (subst s os)
    | assign_s x e => assign_s (subst s x) (subst s e)
    | _ => st
  end.

Instance Subst_stmt : Subst stmt var var := subst_stmt.

Definition state := var -> value.
Definition heap  := addr -> option value.
Definition world := (state * heap)%type.
Definition stk (w : world) : state := fst w.
Definition hp (w : world) : heap := snd w.

Parameter eval_fun : pname -> expr -> expr -> value.

Fixpoint eval s e :=
  match e with
    | value_e v => v
    | var_e v   => stk s v
    | fun_e f e1 e2 => 
      let v1 := eval s e1 in
      let v2 := eval s e2 in
      eval_fun f v1 v2
  end.

Definition subst_one (x : var) (e : expr) :=
  fun i => if eq_dec i x then e else (var_e i).

Inductive modvars : stmt -> var -> Prop :=
| mod_alloc1 : forall l v e, modvars (alloc_s l v e) l
| mod_alloc2 : forall l v e, modvars (alloc_s l v e) v
| mod_assign: forall x e, modvars (assign_s x e) x
| mod_proc1: forall f xs r os x, 
               In x os ->
               modvars (proc_s f xs r os) x
| mod_proc2: forall f xs r os, 
               modvars (proc_s f xs r os) r
| mod_seq1: forall x s1 s2, modvars s1 x -> modvars (seq_s s1 s2) x
| mod_seq2: forall x s1 s2, modvars s2 x -> modvars (seq_s s1 s2) x.