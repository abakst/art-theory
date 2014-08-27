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
 
Reserved Notation "( Φ ; Γ ; Ξ ) ⊢ s ::: O" (at level 0, no associativity).

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

Definition wf_guard (Γ : type_env) (ξ : guard) :=
  wf_prop Γ ξ /\ ~(ν ∈ fv_prop ξ).

Definition wf_guards (Γ : type_env) (Ξ : guards) :=
  Forall (fun ξ => wf_guard Γ ξ) Ξ.

Inductive wf_schema : proc_schema -> Prop :=
| wf_proc_schema : 
    forall S, 
      length (s_formals S) = length (s_formal_ts S) ->
      wf_env (combine (s_formals S) (s_formal_ts S)) ->
      (* Forall (wf_type (ext_type_env Γ (proc_args S))) (proc_formal_ts S) -> *)
      wf_env (s_ret S :: (combine (s_formals S) (s_formal_ts S))) ->
(* ------------------------------------------------------------------- *)
  wf_schema S.

Inductive subtype : type_env -> guards -> reft_type -> reft_type -> Prop :=
| st_base : 
    forall Γ Ξ b p p',
      ((sep_env Γ && sep_guards Ξ) |-- (sep_pred p --> sep_pred p')) ->
(* ------------------------------------------------------------------- *)
  subtype Γ Ξ { ν : b | p } { ν : b | p' }.

Inductive expr_type : type_env -> guards -> expr -> reft_type -> Prop :=
| t_const : forall Γ Ξ v,
(* ------------------------------------------------------------------- *)
  expr_type Γ Ξ (value_e v) { ν : (base_of_val v) | (var_e ν) .= (value_e v) }
            
| t_var : forall Γ Ξ x τ φ, (x, { ν : τ | φ }) ∈ Γ ->
(* ------------------------------------------------------------------- *)
  expr_type Γ Ξ (var_e x) { ν : τ | φ }

| t_sub : forall Γ Ξ e T T',
            expr_type Γ Ξ e T -> wf_type Γ T' -> subtype Γ Ξ T T' -> 
(* ------------------------------------------------------------------- *)
  expr_type Γ Ξ e T'.

Definition tc_list Γ Ξ (xts : list (var * reft_type)) :=
  Forall (fun xt => 
            expr_type Γ Ξ (var_e (fst xt)) (snd xt)) xts.

Definition join_var Ξ Γ1 Γ2 xt :=
  match xt with
  | (x, t) =>
    (exists t1, ((x,t1) ∈ Γ1 /\ subtype Γ1 Ξ t1 t))
    /\ (exists t2, ((x,t2) ∈ Γ2 /\ subtype Γ2 Ξ t2 t))
  end.

Definition join_env Ξ Γ1 Γ2 Γ :=
  wf_env Γ 
  /\ (forall xt, (xt ∈ Γ1 /\ xt ∈ Γ2) <-> xt ∈ Γ)
  /\ Forall (fun xt => wf_type Γ (snd xt) 
                       /\ join_var Ξ Γ1 Γ2 xt) Γ.
  
                              
Inductive stmt_type : proc_env -> type_env -> guards -> stmt -> type_env -> Prop :=
| t_skip : forall Φ Γ Ξ,
(* ------------------------------------------------------------------- *)
   (Φ ; Γ ; Ξ) ⊢ skip_s ::: Γ

| t_proc_s : 
    forall Φ Γ Ξ (v:var) f p S xs ts θ θS,
      (f,(p,S)) ∈ Φ -> wf_schema S -> wf_subst θ ->
      θS = subst θ S ->
      xs = subst θ (s_formals S) ->
      ts = subst θ (s_formal_ts S) ->
      v  = subst θ (fst (s_ret S)) ->
      (forall x, θ x = v <-> x = (fst (s_ret S))) ->
      (forall x', ~(In x' (fst (s_ret S) :: s_formals S)) -> θ x' = x') ->
      wf_env (subst θ (s_ret S) :: Γ) ->
      Forall (fun t => wf_type Γ t) ts ->
      tc_list Γ Ξ (combine xs ts) ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Ξ) ⊢ proc_s f xs [v] ::: (subst θ (s_ret S) :: Γ))

| t_assign : 
    forall Φ Γ Ξ v e τ φ, v <> ν ->
      var_not_in v Γ -> expr_type Γ Ξ e { ν : τ | φ } ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Ξ)  ⊢ assign_s v e ::: ((v, { ν : τ | (var_e ν) .= e }) :: Γ))
    
| t_if : 
    forall Φ Γ Γ1 Γ2 Γ' Ξ e p s1 s2, 
      expr_type Γ Ξ e { ν : int_t | p } ->
      ( Φ ; Γ ; (not_r (e .= (int_v 0))) :: Ξ ) ⊢ s1 ::: Γ1 -> 
      ( Φ ; Γ ; (e .= (int_v 0)) :: Ξ) ⊢ s2 ::: Γ2 ->
      join_env Ξ Γ1 Γ2 Γ' ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Ξ) ⊢ if_s e s1 s2 ::: Γ')

| t_seq : forall Φ Ξ Γ Γ' Γ'' s1 s2,
  (Φ ; Γ ; Ξ) ⊢ s1 ::: Γ' -> (Φ ; Γ' ; Ξ) ⊢ s2 ::: Γ'' ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Ξ) ⊢ seq_s s1 s2 ::: Γ'')

where "( Φ ; Γ ; Ξ ) ⊢ s ::: O" := (stmt_type Φ Γ Ξ s O).