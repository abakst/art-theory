Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.msl_direct.
Require Import Language.
Require Import Types.
Require Import List.
Import ListNotations.
Require Import ListSet.
Require Import Subst.
Require Import Translation.
 
Reserved Notation "P / G ⊢ s ::: O " (at level 0, no associativity).

Definition wf_subst θ := forall v, θ v = ν <-> v = ν.

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
  wf_expr Γ (var_e ν)

| wf_op : forall Γ f e1 e2,
            wf_expr Γ e1 -> wf_expr Γ e2 ->
(* ------------------------------------------------------------------- *)
  wf_expr Γ (fun_e f e1 e2).
            
Inductive wf_env : type_env -> Prop :=
  | wf_env_nil :
(* ------------------------------------------------------------------- *)
    wf_env nil
  | wf_env_var : 
      forall Γ x T, 
        wf_env Γ -> (x <> ν) -> var_not_in x Γ -> wf_type ((x,T) :: Γ) T ->
(* ------------------------------------------------------------------- *)
    wf_env ((x, T) :: Γ).

Inductive wf_schema : proc_schema -> Prop :=
| wf_proc_schema : 
    forall S, 
      length (s_formals S) = length (s_formal_ts S) ->
      wf_env (combine (s_formals S) (s_formal_ts S)) ->
      (* Forall (wf_type (ext_type_env Γ (proc_args S))) (proc_formal_ts S) -> *)
      wf_env (s_ret S :: (combine (s_formals S) (s_formal_ts S))) ->
(* ------------------------------------------------------------------- *)
  wf_schema S.

Inductive subtype : type_env -> reft_type -> reft_type -> Prop :=
| st_base : forall Γ b p p',
             ((sep_env Γ) |-- (sep_pred p --> sep_pred p')) ->
(* ------------------------------------------------------------------- *)
  subtype Γ { ν : b | p } { ν : b | p' }.

Inductive expr_type : type_env -> expr -> reft_type -> Prop :=
| t_const : forall Γ v,
(* ------------------------------------------------------------------- *)
  expr_type Γ (value_e v) { ν : (base_of_val v) | (var_e ν) .= (value_e v) }
            
| t_var : forall Γ x τ φ, (x, { ν : τ | φ }) ∈ Γ ->
(* ------------------------------------------------------------------- *)
  expr_type Γ (var_e x) { ν : τ | φ }

| t_sub : forall Γ e T T',
            expr_type Γ e T -> wf_type Γ T' -> subtype Γ T T' -> 
(* ------------------------------------------------------------------- *)
  expr_type Γ e T'.

Definition tc_list Γ (xts : list (var * reft_type)) :=
  Forall (fun xt => 
            expr_type Γ (var_e (fst xt)) (snd xt)) xts.

Fixpoint subst_of_list (sub : list (var*var)) : subst_t var var :=
  fun i => 
    match sub with
      | (x,x') :: sub' => if eq_dec i x then x' else subst_of_list sub' i
      | _ => i
    end.

Definition subst_call S (xr : var) (xs : list var) := 
  subst_of_list ((fst (s_ret S), xr) :: (combine (s_formals S) xs)).
                              
Inductive stmt_type : proc_env -> type_env -> stmt -> type_env -> Prop :=
| t_skip : forall Φ Γ,
(* ------------------------------------------------------------------- *)
  (Φ / Γ ⊢ skip_s ::: Γ)
| t_proc_s : 
    forall Φ Γ (v:var) f p S xs ts θ θS,
      (f,(p,S)) ∈ Φ -> wf_schema S -> wf_subst θ ->
      θS = subst θ S ->
      xs = subst θ (s_formals S) ->
      ts = subst θ (s_formal_ts S) ->
      v  = subst θ (fst (s_ret S)) ->
      (forall x, θ x = v <-> x = (fst (s_ret S))) ->
      (forall x', ~(In x' (fst (s_ret S) :: s_formals S)) -> θ x' = x') ->
      wf_env (subst θ (s_ret S) :: Γ) ->
      Forall (fun t => wf_type Γ t) ts ->
      tc_list Γ (combine xs ts) ->
(* ------------------------------------------------------------------- *)
  (Φ / Γ ⊢ proc_s f xs [v] ::: (subst θ (s_ret S) :: Γ))
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