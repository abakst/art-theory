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
  | int_t  : base_type
  | bool_t : base_type.

Definition base_of_type b :=
  match b with
    | int_t => nat
    | bool_t => bool
  end.

Definition base_of_val (v: value) :=
  match v with
    | int_v  _ => int_t
    | bool_v _ => bool_t
  end.

Definition val_of_base : forall (b : base_type), (base_of_type b) -> value :=
  fun b => 
    match b with
      | int_t => fun x => int_v x
      | bool_t => fun x => bool_v x
    end.

Inductive brel : Set :=
  | eq_brel : brel
  | lt_brel : brel.

Inductive reft_prop : Set :=
  | tt_r   : reft_prop
  | rel_r  : expr -> brel -> expr -> reft_prop
  | not_r  : reft_prop -> reft_prop
  | and_r  : reft_prop -> reft_prop -> reft_prop
  | or_r   : reft_prop -> reft_prop -> reft_prop.

Record reft_type : Set := 
  mkReft_type { reft_vv: var;
                reft_base: base_type;
                reft_r: reft_prop } .

Fixpoint subst_prop (s : subst_t var) prop :=
  match prop with
    | tt_r          => tt_r
    | rel_r e1 o e2 => rel_r (subst s e1) o (subst s e2)
    | not_r p       => not_r (subst_prop s p)
    | and_r p1 p2   => and_r (subst_prop s p1) (subst_prop s p2)
    | or_r p1 p2    => or_r (subst_prop s p1) (subst_prop s p2)
  end.

Instance Subst_prop : Subst reft_prop var := subst_prop.

Definition subst_r s reft :=
  mkReft_type (reft_vv reft)
              (reft_base reft)
              (subst s (reft_r reft)).

Instance Subst_reft : Subst reft_type var := subst_r.

Definition type_binding : Set := (var * reft_type)%type.

Record proc_schema : Set :=
  mkSchema { proc_args: list type_binding;
              proc_ret: type_binding }.

Definition proc_formals s := fst (List.split (proc_args s)).
Definition proc_formal_ts s := snd (List.split (proc_args s)).

Definition proc_binding : Set := (pname * proc_schema)%type.

Notation "x .= y" := (rel_r x eq_brel y) (at level 70).
Notation "x .< y" := (rel_r x lt_brel y) (at level 70).
Notation "{ v : t | P }" := (mkReft_type v t P%reft) (at level 0, v at level 99, no associativity).


(** Environments **)

Definition bind_env (B T : Type) := list (B * T)%type.
Definition type_env : Type := bind_env var reft_type.
Definition proc_env : Type := bind_env pname proc_schema.

Definition var_in : var -> type_env -> Prop := 
  fun x Γ => exists t, In (x, t) Γ.

Definition var_not_in : var -> type_env -> Prop :=
  fun x Γ => Forall (fun xt => (fst xt <> x)) Γ.

Definition fun_in : (pname * proc_schema) -> proc_env -> Prop :=
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