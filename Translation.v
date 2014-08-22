Add LoadPath "vst".
Require Import CpdtTactics.
Require Import Types.
Require Import ProgramLogic.
Require Import Language.
Require Import Subst.
Require Import List.
Import ListNotations.
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Set Implicit Arguments.

Open Scope pred.

Definition sep_base (x:var) (t:base_type) : pred world :=
  EX v : (base_of_type t), (fun s => (eval s (var_e x) = (val_of_base t v))).

Fixpoint sep_pred (p:reft_prop) : pred world :=
  match p with
    | tt_r  => TT
    | rel_r e1 o e2 =>
      match o with
        | eq_brel => (fun s => eval s e1 = eval s e2)
      end
    | not_r p => (sep_pred p) --> FF
    | and_r p1 p2 => sep_pred p1 && sep_pred p2
    | or_r p1 p2 => sep_pred p1 || sep_pred p2
  end.

Definition sep_ty (x:var) (t:reft_type) : pred world :=
  match t with
  | mkReft_type b p => sep_base x b && (sep_pred (subst (subst_one ν (var_e x)) p))
  end.

Fixpoint sep_env (Γ : type_env) : pred world :=
  match Γ with
    | nil => TT
    | (x,t) :: Γ' => sep_ty x t && sep_env Γ'
  end.

Definition sep_schema (f:pname) (s:stmt) (S:proc_schema) : procspec := 
  match S with
    | mkSchema xs ts (x, t) =>
      (f, mkProc (length xs) xs [x] s, sep_env (combine xs ts), sep_ty x t)
  end.

Fixpoint sep_proc_env (Φ : proc_env) : procspecs :=
  match Φ with
    | nil => nil
    | (f,(s,t)) :: Φ' => sep_schema f s t :: sep_proc_env Φ'
  end.

Definition disj_subst Γ (θ : var -> expr) :=
  θ ν = (var_e ν) /\ forall x, var_in x Γ -> θ x = (var_e x).