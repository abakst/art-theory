Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.msl_direct.
Require Import Language.
Require Import Types.
Require Import List.
Require Import ListSet.
Require Import Subst.
 
(* Reserved Notation " Γ ⊢ e [ t ]" (at level 0, no associativity). *)
Reserved Notation "P / G ⊢ s ::: O " (at level 0, no associativity).

Definition ν := vv.

Inductive wf_type : type_env -> reft_type -> Prop :=
| wf_reft_t : forall Γ b p, wf_prop Γ p ->
(* ------------------------------------------------------------------- *)
  wf_type Γ { ν : b | p }

with
wf_prop : type_env -> reft_prop -> Prop :=
| wf_tt : forall Γ, 
(* ------------------------------------------------------------------- *)
            wf_prop Γ tt_r 
| wf_rel : forall Γ e1 o e2, wf_expr Γ e1 -> wf_expr Γ e2 ->
(* ------------------------------------------------------------------- *)
  wf_prop Γ (rel_r e1 o e2)
| wf_not : forall Γ p, wf_prop Γ p -> 
(* ------------------------------------------------------------------- *)
  wf_prop Γ (not_r p)
| wf_and : forall Γ p1 p2, wf_prop Γ p1 -> wf_prop Γ p2 -> 
(* ------------------------------------------------------------------- *)
  wf_prop Γ (and_r p1 p2)
| wf_or : forall Γ p1 p2, wf_prop Γ p1 -> wf_prop Γ p2 -> 
(* ------------------------------------------------------------------- *)
  wf_prop Γ (or_r p1 p2)

with 
wf_expr : type_env -> expr -> Prop :=
| wf_val : forall Γ v,
(* ------------------------------------------------------------------- *)
  wf_expr Γ (value_e v)
| wf_var : forall Γ v t, (v,t) ∈ Γ ->
(* ------------------------------------------------------------------- *)
  wf_expr Γ (var_e v)
| wf_vv : forall Γ,
(* ------------------------------------------------------------------- *)
  wf_expr Γ (var_e ν).

(* Definition wf_env Γ :=  *)
(*   var_not_in ν Γ /\ Forall (fun xt => wf_type Γ (snd xt)) Γ. *)

Inductive wf_env : type_env -> Prop :=
  | wf_env_nil :
(* ------------------------------------------------------------------- *)
    wf_env nil
  | wf_env_var : 
      forall Γ x T, 
        wf_env Γ -> (x <> ν) -> var_not_in x Γ -> wf_type Γ T ->
(* ------------------------------------------------------------------- *)
    wf_env ((x, T) :: Γ).

Inductive wf_schema : type_env -> proc_schema -> Prop :=
| wf_proc_schema : 
    forall Γ S, 
      NoDup (proc_formals S) -> 
      Forall (fun x => ~ (var_in x Γ)) (proc_formals S) ->
      ~ (var_in (fst (proc_ret S)) Γ) ->
      Forall (wf_type (ext_type_env Γ (proc_args S))) (proc_formal_ts S) ->
      wf_type (ext_type_env Γ (proc_args S)) (snd (proc_ret S)) ->
(* ------------------------------------------------------------------- *)
  wf_schema Γ S.

Inductive expr_type : type_env -> expr -> reft_type -> Prop :=
| t_const : forall Γ v,
(* ------------------------------------------------------------------- *)
  expr_type Γ (value_e v) { ν : (base_of_val v) | (var_e ν) .= (value_e v) }

| t_var : forall Γ x τ φ, (x, { ν : τ | φ }) ∈ Γ ->
(* ------------------------------------------------------------------- *)
  expr_type Γ (var_e x) { ν : τ | φ }.

Definition tc_list Γ (xs : list var) (ts : list reft_type) :=
  Forall (fun xt => expr_type Γ (var_e (fst xt)) (snd xt))
         (combine xs ts).

Definition subst_call S (xs : list var) := combine (proc_formals S) xs.
                              
Inductive stmt_type : proc_env -> type_env -> stmt -> type_env -> Prop :=
| t_skip : forall Φ Γ,
(* ------------------------------------------------------------------- *)
  (Φ / Γ ⊢ skip_s ::: Γ)
| t_proc_s : 
    forall Φ Γ (v:var) p S xs θ,
      (p,S) ∈ Φ -> wf_schema nil S -> (θ = subst_call S xs) ->
      var_not_in v Γ -> v <> ν ->
      tc_list Γ xs (subst θ (proc_formal_ts S)) ->
(* ------------------------------------------------------------------- *)
  (Φ / Γ ⊢ proc_s v p xs ::: ((v, subst θ (snd (proc_ret S))) :: Γ))
| t_assign : 
    forall Φ Γ v e τ φ, v <> ν ->
      var_not_in v Γ -> expr_type Γ e { ν : τ | φ } ->
(* ------------------------------------------------------------------- *)
  (Φ / Γ ⊢ assign_s v e ::: ((v, { ν : τ | (var_e ν) .= e }) :: Γ))
| t_seq : forall Φ Γ Γ' Γ'' s1 s2,
  (Φ / Γ ⊢ s1 ::: Γ') -> (Φ / Γ' ⊢ s2 ::: Γ'') ->
(* ------------------------------------------------------------------- *)
  (Φ / Γ ⊢ seq_s s1 s2 ::: Γ'')
where "P / G ⊢ s ::: O " := (stmt_type P G s O).


(* Definition x := 1. *)
(* Definition y := 2. *)
(* Definition z := 3. *)
(* Definition plus := 100. *)

(* Definition t := { ν : int_t | tt_r }. *)

(* Definition plus_schema := *)
(*   mkSchema ((9, { ν : int_t | tt_r }) :: (10, { ν : int_t | tt_r }) :: nil) *)
(*             (11, { ν : int_t | tt_r }). *)
(* Example ex1: *)
(*   wf_schema nil plus_schema. *)
(* Proof. *)
(*   constructor.  *)
(*   constructor. *)
(*     unfold In. unfold not. intro. destruct H. inversion H. apply H.  *)
(*   constructor. *)
(*     unfold In. unfold not. auto.  *)
(*   constructor. *)
(*   constructor. unfold not. intro. destruct H. unfold In in H. apply H. *)
(*   constructor. unfold not. intro. destruct H. unfold In in H. apply H. *)
(*   constructor. unfold not. intro. destruct H. unfold In in H. apply H. *)
(*   repeat constructor.  *)
(*   repeat constructor. *)
(* Qed. *)

(* Example ex2: *)
(*   ((plus, plus_schema) :: nil) / ((x, t) :: (y, t) :: nil) ⊢ proc_s z plus (x :: y :: nil) ::: ((z, t) :: (x, t) :: (y, t) :: nil). *)
(* Proof. *)
(*   apply t_proc_s with (Φ := ((plus, plus_schema) :: nil)) *)
(*                        (Γ := ((x, t) :: (y, t) :: nil)) *)
(*                        (v := z) (p := plus) (S := plus_schema) (θ := ((9, 1) :: (10, 2) :: nil)). *)
(*   constructor. reflexivity. *)
(*   apply ex1. *)
(*   compute. reflexivity.  *)
(*   unfold tc_list. constructor. *)
(*     simpl. constructor. constructor. compute. reflexivity. *)
(*     compute. constructor. constructor. *)
(*   constructor. simpl. constructor. compute. right.left. reflexivity. *)
(*   constructor. compute. constructor. *)
(*   constructor. *)
(* Qed. *)