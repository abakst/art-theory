Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import Language.
Require Import List.
Require Import Subst.
Require Import msl.msl_direct.

Definition vv : var := V 0.

Delimit Scope reft_scope with reft.

(** Type Language **)
Inductive base_type : Set :=
  | int_t  : base_type.

Definition base_of_type b :=
  match b with
    | int_t => nat
  end.

Definition base_of_val (v: value) :=
  match v with
    | int_v  _ => int_t
  end.

Definition val_of_base : forall (b : base_type), (base_of_type b) -> value :=
  fun b => 
    match b with
      | int_t => fun x => int_v x
    end.

Inductive brel : Set :=
  | eq_brel : brel.

Inductive reft_prop : Set :=
  | tt_r   : reft_prop
  | rel_r  : expr -> brel -> expr -> reft_prop
  | not_r  : reft_prop -> reft_prop
  | and_r  : reft_prop -> reft_prop -> reft_prop
  | or_r   : reft_prop -> reft_prop -> reft_prop.

Record reft_type : Set := 
  mkReft_type { reft_base: base_type;
                reft_r: reft_prop } .

Fixpoint subst_prop_var (s : subst_t var var) prop :=
  match prop with
    | tt_r          => tt_r
    | rel_r e1 o e2 => rel_r (subst s e1) o (subst s e2)
    | not_r p       => not_r (subst_prop_var s p)
    | and_r p1 p2   => and_r (subst_prop_var s p1) (subst_prop_var s p2)
    | or_r p1 p2    => or_r (subst_prop_var s p1) (subst_prop_var s p2)
  end.

Fixpoint subst_prop (s : subst_t var expr) prop :=
  match prop with
    | tt_r          => tt_r
    | rel_r e1 o e2 => rel_r (subst s e1) o (subst s e2)
    | not_r p       => not_r (subst_prop s p)
    | and_r p1 p2   => and_r (subst_prop s p1) (subst_prop s p2)
    | or_r p1 p2    => or_r (subst_prop s p1) (subst_prop s p2)
  end.

Instance Subst_prop_var : Subst reft_prop var var := subst_prop_var.
Instance Subst_prop : Subst reft_prop var expr := subst_prop.

Definition subst_r_var (s : subst_t var var) reft :=
  mkReft_type (reft_base reft)
              (subst s (reft_r reft)).

Definition subst_r s reft :=
  mkReft_type (reft_base reft)
              (subst s (reft_r reft)).

Instance Subst_reft_var : Subst reft_type var var := subst_r_var.
Instance Subst_reft : Subst reft_type var expr := subst_r.

Definition type_binding : Set := (var * reft_type)%type.

Record proc_schema : Set :=
  mkSchema { s_formals: list var;
             s_formal_ts: list reft_type;
             s_ret: type_binding }.

Definition subst_schema s S :=
  let subst_both s xt := (subst s (fst xt), subst s (snd xt)) in
  match S with
    | mkSchema xs ts xt =>
      mkSchema (subst s xs) (subst s ts) (subst_both s xt)
  end.
Instance Subst_proc_schema : Subst proc_schema var var := subst_schema.

Definition dummyt (v : var) t p := mkReft_type t p.

Notation "x .= y" := (rel_r x eq_brel y) (at level 70).
(* Notation "{ vv : t | P }" := (mkReft_type t P%reft) (at level 0, no associativity). *)
Notation "{ vv : t | P }" := (dummyt vv t P%reft) (at level 0, vv at level 99, no associativity).


(** Environments **)

Definition bind_env (B T : Type) := list (B * T)%type.
Definition type_env : Type := bind_env var reft_type.
Definition proc_env : Type := bind_env pname (stmt * proc_schema)%type.

Definition var_in : var -> type_env -> Prop := 
  fun x Γ => exists t, In (x, t) Γ.

Definition var_not_in : var -> type_env -> Prop :=
  fun x Γ => Forall (fun xt => (fst xt <> x)) Γ.

Definition fun_in : (pname * (stmt * proc_schema)) -> proc_env -> Prop :=
  fun ft Φ => In ft Φ.

Notation "X ∈ Y" := (In X Y) (at level 40).

Definition ext_type_env (e1 e2: type_env) := e1 ++ e2.
Definition ext_proc_env (e1 e2: proc_env) := e1 ++ e2.

(** Hm **)
(** Ugh Equality **)
Instance EqDec_base_t : EqDec base_type := _.
Proof.
  hnf. decide equality.
Qed.

Instance EqDec_brel_t : EqDec brel := _.
Proof.
  hnf. decide equality.
Qed.

Instance EqDec_reft_prop : EqDec reft_prop := _.
Proof.
  hnf. decide equality; try apply eq_dec. 
Qed.

Instance EqDec_reft_type : EqDec reft_type := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_proc_schema : EqDec proc_schema := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Definition ν := vv.