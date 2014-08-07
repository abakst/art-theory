Add LoadPath "vst".
Require Import CpdtTactics.
Require Import Types.
Require Import ProgramLogic.
Require Import Language.
Require Import Judge.
Require Import Subst.
Require Import List.
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Set Implicit Arguments.

(* Require String. Open Scope string_scope. *)

(* Ltac move_to_top x := *)
(*   match reverse goal with *)
(*   | H : _ |- _ => try move x after H *)
(*   end. *)

(* Tactic Notation "assert_eq" ident(x) constr(v) := *)
(*   let H := fresh in *)
(*   assert (x = v) as H by reflexivity; *)
(*   clear H. *)

(* Tactic Notation "Case_aux" ident(x) constr(name) := *)
(*   first [ *)
(*     set (x := name); move_to_top x *)
(*   | assert_eq x name; move_to_top x *)
(*   | fail 1 "because we are working on a different case" ]. *)

(* Tactic Notation "Case" constr(name) := Case_aux Case name. *)
(* Tactic Notation "SCase" constr(name) := Case_aux SCase name. *)
(* Tactic Notation "SSCase" constr(name) := Case_aux SSCase name. *)
(* Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name. *)
(* Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name. *)
(* Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name. *)
(* Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name. *)
(* Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name. *)

Open Scope pred.

(** Preliminaries ??? **)
Definition subst_pred (x: var) (e: expr) (p: pred world) : pred world :=
  fun w =>
    let w' := fun x' => if eq_dec x x' then eval w e else w x' in
    p w'.

(** The meat of the sauce :d tasty **)
Definition sep_base (x:var) (t:base_type) : pred world :=
  EX v : (base_of_type t), (fun s => (eval s (var_e x) = Some (val_of_base t v))).

Fixpoint sep_pred (p:reft_prop) : pred world :=
  match p with
    | tt_r  => TT
    | rel_r e1 o e2 =>
      match o with
        | eq_brel => 
          EX v1 : value, EX v2 : value, 
             !! (v1 = v2) 
          && (fun s => Some v1 = (eval s e1)) 
          && (fun s => Some v2 = (eval s e2))
        | lt_brel => 
          EX v1 : nat, EX v2 : nat, 
             !! (v1 < v2) 
          && (fun s => Some (int_v v1) = (eval s e1)) 
          && (fun s => Some (int_v v2) = (eval s e2))
      end
    | not_r p => (sep_pred p) --> FF
    | and_r p1 p2 => sep_pred p1 && sep_pred p2
    | or_r p1 p2 => sep_pred p1 || sep_pred p2
  end.

Definition sep_ty (x:var) (t:reft_type) : pred world :=
  match t with
  | mkReft_type v b p => sep_base x b 
                      && (sep_pred (subst ((v,x) :: nil) p))
  end.

Fixpoint sep_env (Γ : type_env) : pred world :=
  match Γ with
    | nil => TT
    | (x,t) :: Γ' => sep_ty x t && sep_env Γ'
  end.
  