Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import Language.
Require Import Types.
Require Import List.
Import ListNotations.
Require Import ListSet.
Require Import Subst.
Require Export Translation.
 
Reserved Notation "( Φ ; Γ ; S ; Ξ ) ⊢ s ::: ( O ; H )" 
         (at level 0, no associativity).

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

Inductive wf_heap : type_env -> heap_env -> Prop :=
  | wf_emp : 
      forall Γ,
(* ------------------------------------------------------------------- *)
    wf_heap Γ nil
  | wf_heap_bind :
      forall Γ Σ l x t,
        loc_not_in l Σ -> bind_not_in x Σ -> 
        var_not_in x Γ -> x <> ν -> wf_type Γ t ->
(* ------------------------------------------------------------------- *)
    wf_heap Γ ((l, (x, t)) :: Σ).

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

Definition eq_dom Σ Σ' :=
  forall l, loc_in l Σ <-> loc_in l Σ'.

Definition heap_subtype Γ Ξ Σ Σ' :=
  eq_dom Σ Σ' /\
    forall l x, 
      (exists t t', (l, (x, t)) ∈ Σ  -> (l, (x, t')) ∈ Σ' ->
                    subtype Γ Ξ t t').

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
  /\ (forall x, (var_in x Γ1 /\ var_in x Γ2) <-> var_in x Γ)
  /\ Forall (fun xt => (* wf_type Γ (snd xt)  *)
                       (* /\  *)join_var Ξ Γ1 Γ2 xt) Γ.

Definition fresh_heap_binds (Σ : heap_env) (Γ : type_env)  :=
  Forall (fun lxt => var_not_in (fst (snd lxt)) Γ) Σ.

Definition fresh_heap_binds' (Σ : heap_env) (Σ' : heap_env) :=
  Forall (fun lxt => bind_not_in (fst (snd lxt)) Σ') Σ.

Definition heap_subst (Σ Σ': heap_env) (θ : subst_t var var) :=
  (forall x, bind_not_in x Σ -> θ x = x)
  /\ (forall l xt xt', (l, xt) ∈ Σ -> (l, xt') ∈ Σ' -> θ (fst xt) = fst xt').

Definition join_heap Γ1 Γ2 Γ Ξ Σ1 Σ2 Σ :=
    wf_heap Γ Σ 
    /\ fresh_heap_binds Σ Γ  
    /\ fresh_heap_binds Σ Γ1 
    /\ fresh_heap_binds Σ Γ2 
    /\ fresh_heap_binds' Σ Σ1 
    /\ fresh_heap_binds' Σ Σ2 
    /\ (exists θ1, heap_subst Σ1 Σ θ1)
    /\ (exists θ2, heap_subst Σ2 Σ θ2)
    /\ heap_subtype Γ1 Ξ Σ1 Σ 
    /\ heap_subtype Γ2 Ξ Σ2 Σ.

Definition fresh x Γ Σ :=
  x <> ν /\ var_not_in x Γ /\ bind_not_in x Σ.

Definition fresh_loc l Γ Σ :=
  match l with
    | L n =>
      (V n) <> ν /\ fresh (V n) Γ Σ /\ bind_not_in (V n) Σ /\ loc_not_in l Σ
  end.

Definition isub {A D R : Type} {S : Subst A D R } {SL : Subst A loc loc} 
                (θ : subst_t D R) (θl : subst_t loc loc) (t : A) 
  := subst θl (subst θ t).
                              
Inductive stmt_type : proc_env -> 
                      type_env -> 
                      heap_env ->
                      guards -> 
                      stmt -> 
                      type_env -> 
                      heap_env ->
                      Prop :=

| t_skip : forall Φ Γ Σ Ξ,
(* ------------------------------------------------------------------- *)
   (Φ ; Γ ; Σ ; Ξ) ⊢ skip_s ::: (Γ ; Σ)

| t_proc_s :
    forall Φ Γ Σ Σu Σm Ξ (v:var) f p S (θ : var -> var) (θl : loc -> loc),
      (f,(p,S)) ∈ Φ -> wf_schema S -> wf_subst θ -> heap_split Σu Σm Σ ->
      (forall x, θ x = (subst θ (fst (s_ret S))) <-> x = (fst (s_ret S))) ->
      (forall x', ~(In x' (fst (s_ret S) :: s_formals S)) -> θ x' = x') ->
      wf_env (isub θ θl (s_ret S) :: Γ) ->
      wf_heap (isub θ θl (s_ret S) :: Γ) (Σu ++ isub θ θl (s_heap_out S)) ->
      Forall (fun t => wf_type Γ t) (isub θ θl (s_formal_ts S)) ->
      tc_list Γ Ξ (combine (subst θ (s_formals S)) (isub θ θl (s_formal_ts S))) ->
      heap_subtype Γ Ξ Σm (isub θ θl (s_heap_in S)) ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ; Ξ)
     ⊢ proc_s f (subst θ (s_formals S)) (subst θ (fst (s_ret S))) [] 
       ::: (isub θ θl (s_ret S) :: Γ ; Σu ++ isub θ θl (s_heap_out S)))

| t_pad : 
    forall Φ Γ Σ Ξ l x a t,
      fresh x Γ Σ -> fresh a Γ Σ -> fresh_loc l Γ Σ -> wf_type Γ t ->
(* ------------------------------------------------------------------- *)
      ((Φ ; Γ ; Σ ; Ξ) ⊢ pad_s a x ::: (Γ ; (l,(x,t))::Σ))

| t_assign : 
    forall Φ Γ Σ Ξ v e τ φ, 
      fresh v Γ Σ -> expr_type Γ Ξ e { ν : τ | φ } ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ; Ξ)  ⊢ assign_s v e ::: ((v, {ν : τ | (var_e ν) .= e})::Γ ; Σ))

| t_alloc :
    forall Φ Γ Σ Ξ x y a l e t,
      fresh x Γ Σ -> fresh a Γ Σ -> x <> y -> 
      expr_type Γ Ξ e t -> wf_heap Γ ((l, (y, t))::Σ) ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ; Ξ) ⊢ alloc_s a x e ::: ((x, {ν : ref_t l | tt_r})::Γ ; ((l,(y,t))::Σ)))

| t_if : 
    forall Φ Γ Γ1 Γ2 Γ' Σ Σ1 Σ2 Σ' Ξ e p s1 s2, 
      expr_type Γ Ξ e { ν : int_t | p } ->
      ( Φ ; Γ ; Σ ; (e .= (int_v 1)) :: Ξ ) ⊢ s1 ::: (Γ1 ; Σ1) -> 
      ( Φ ; Γ ; Σ ; (e .= (int_v 0)) :: Ξ) ⊢ s2 ::: (Γ2 ; Σ2) ->
      join_env Ξ Γ1 Γ2 Γ' -> 
      join_heap Γ1 Γ2 Γ' Ξ Σ1 Σ2 Σ' -> 
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ; Ξ) ⊢ if_s e s1 s2 ::: (Γ' ; Σ'))

| t_seq : forall Φ Ξ Γ Γ' Γ'' Σ Σ' Σ'' s1 s2,
  (Φ ; Γ ; Σ ; Ξ) ⊢ s1 ::: (Γ' ; Σ') -> 
  (Φ ; Γ' ; Σ' ; Ξ) ⊢ s2 ::: (Γ'' ; Σ'') ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ;  Ξ) ⊢ seq_s s1 s2 ::: (Γ'' ; Σ''))
      
where 
"( Φ ; Γ ; S ; Ξ ) ⊢ s ::: ( O ; H )" 
  := (stmt_type Φ Γ S Ξ s O H).

Definition proc_init_env S := combine (s_formals S) (s_formal_ts S).
    
Inductive prog_type : proc_env -> program -> Prop :=
| t_prog_entry : 
    forall Φ Γ Σ s, 
      (Φ ; [] ; [] ; []) ⊢ s ::: (Γ ; Σ) ->
      prog_type Φ (entry_p s)
| t_prog_procdecl :
  forall Φ Γ Σ p pr body prog e S,
    wf_schema S -> 
    fun_not_in p Φ ->
    p_args pr = s_formals S -> 
    p_body pr = seq_s body (return_s e) ->
    p_ret pr = fst (s_ret S) ->
    p_mod pr = [] ->
    ((p, (p_body pr, S))::Φ ; proc_init_env S ; [] ; [] ) ⊢ body ::: (Γ ; Σ) ->
    expr_type Γ [] e (subst (subst_one (fst (s_ret S)) e) (snd (s_ret S))) ->
    prog_type ((p,(p_body pr, S)) :: Φ) prog ->
(* ------------------------------------------------------------------- *)
    prog_type Φ (procdecl_p p pr prog).

(* Notation  " Φ ⊢ p " := (proc_type Φ f s S) (at level 0, no associativity). *)