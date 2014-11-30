Add LoadPath "vst".

Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import Language.
Require Import Types.
Import HE.
Require Import List.
Import ListNotations.
Require Import ListSet.
Require Import Subst.
Require Import Translation.
 
Reserved Notation "( Φ ; Γ ; S ; Ξ ) ⊢ s ::: ( O ; H )" 
         (at level 0, no associativity).

Definition wf_subst (θ : subst_t var var) := 
  forall (v : var), subst θ v = ν <-> v = ν.

Inductive wf_type : type_env -> heap_env -> reft_type -> Prop :=
| wf_reft_t : forall Γ Σ b p, wf_prop Γ Σ p ->
(* ------------------------------------------------------------------- *)
  wf_type Γ Σ { ν : b | p }

with wf_prop : type_env -> heap_env -> reft_prop -> Prop :=
| wf_tt : forall Γ Σ, 
(* ------------------------------------------------------------------- *)
            wf_prop Γ Σ tt_r 

| wf_rel : forall Γ Σ e1 e2, wf_expr Γ Σ e1 -> wf_expr Γ Σ e2 ->
(* ------------------------------------------------------------------- *)
  wf_prop Γ Σ (eq_r e1 e2)

| wf_not : forall Γ Σ p, wf_prop Γ Σ p -> 
(* ------------------------------------------------------------------- *)
  wf_prop Γ Σ (not_r p)

| wf_and : forall Γ Σ p1 p2, wf_prop Γ Σ p1 -> wf_prop Γ Σ p2 -> 
(* ------------------------------------------------------------------- *)
  wf_prop Γ Σ (and_r p1 p2)

| wf_or : forall Γ Σ p1 p2, wf_prop Γ Σ p1 -> wf_prop Γ Σ p2 -> 
(* ------------------------------------------------------------------- *)
  wf_prop Γ Σ (or_r p1 p2)

with  wf_expr : type_env -> heap_env -> expr -> Prop :=
| wf_val : forall Γ Σ v,
(* ------------------------------------------------------------------- *)
  wf_expr Γ Σ (value_e v)

| wf_var_ctx : forall Γ Σ v, var_in v Γ ->
(* ------------------------------------------------------------------- *)
  wf_expr Γ Σ (var_e v)

| wf_var_hp : forall Γ Σ v, bind_in v Σ ->
(* ------------------------------------------------------------------- *)
  wf_expr Γ Σ (var_e v)

| wf_vv : forall Γ Σ,
(* ------------------------------------------------------------------- *)
  wf_expr Γ Σ (var_e ν)

| wf_op : forall Γ Σ f e1 e2,
            wf_expr Γ Σ e1 -> wf_expr Γ Σ e2 ->
(* ------------------------------------------------------------------- *)
  wf_expr Γ Σ (fun_e f e1 e2).

Definition fresh (x : var) (Γ : type_env) (Σ : heap_env) := 
  @nonfv _ _ var _ x ν /\ @nonfv _ _ var Subst_list Γ x /\ nonfv Σ x.

Definition fresh_loc (l : loc) (Γ : type_env) (Σ : heap_env) := 
  @nonfv _ _ loc Subst_list Γ l /\ nonfv Σ l.
            
Inductive wf_env : heap_env -> type_env -> Prop :=
  | wf_env_nil : forall Σ, 
(* ------------------------------------------------------------------- *)
    wf_env Σ nil

  | wf_env_var : 
      forall Γ Σ x T, 
        fresh x Γ Σ -> wf_env Σ Γ -> wf_type ((x,T) :: Γ) Σ T ->
(* ------------------------------------------------------------------- *)
    wf_env Σ ((x, T) :: Γ).

Inductive wf_heap : type_env -> heap_env -> heap_env -> Prop :=
  | wf_emp : 
      forall Γ Σ Σ', Empty Σ' ->
(* ------------------------------------------------------------------- *)
    wf_heap Γ Σ Σ'

  | wf_heap_bind :
      forall Γ Σ Σ0 Σ0' l x t,
        fresh x Γ Σ0 -> fresh_loc l Γ Σ0 -> bind_in x Σ ->
        wf_type Γ Σ t -> wf_heap Γ Σ Σ0 -> HE_Props.Add l (x,t) Σ0 Σ0' ->
(* ------------------------------------------------------------------- *)
    wf_heap Γ Σ Σ0'.

Definition wf_guard (Γ : type_env) (ξ : guard) :=
  wf_prop Γ heap_emp ξ /\ (@nonfv _ _ var _ ξ ν).

Definition wf_guards (Γ : type_env) (Ξ : guards) :=
  Forall (fun ξ => wf_guard Γ ξ) Ξ.

Inductive wf_schema : proc_schema -> Prop :=
| wf_proc_schema : 
    forall S, 
      length (s_formals S) = length (s_formal_ts S) ->
      wf_env (s_heap_in S) (combine (s_formals S) (s_formal_ts S))  ->
      wf_heap (combine (s_formals S) (s_formal_ts S)) (s_heap_in S) (s_heap_in S) ->
      (* Forall (wf_type (ext_type_env Γ (proc_args S))) (proc_formal_ts S) -> *)
      wf_env (s_heap_out S) (s_ret S :: (combine (s_formals S) (s_formal_ts S))) ->
      wf_heap (s_ret S :: (combine (s_formals S) (s_formal_ts S))) 
              (s_heap_out S) (s_heap_out S) ->
(* ------------------------------------------------------------------- *)
  wf_schema S.

Inductive subtype : type_env -> guards -> reft_type -> reft_type -> Prop :=
| st_base : 
    forall Γ Ξ b p p',
      sep_env Γ && sep_guards Ξ
         |-- ALL x : expr,  sep_pred (subst (subst_one ν x) p) -->
                             sep_pred (subst (subst_one ν x) p') ->
(* ------------------------------------------------------------------- *)
  subtype Γ Ξ { ν : b | p } { ν : b | p' }.

Definition eq_dom Σ Σ' :=
  forall l, loc_in l Σ <-> loc_in l Σ'.

Inductive heap_subtype : type_env -> guards -> heap_env -> heap_env -> Prop :=
  | hst_emp : forall Γ Ξ, 
(* ------------------------------------------------------------------- *)
    heap_subtype Γ Ξ heap_emp heap_emp

  | hst_bind : forall Γ Ξ Σ Σ' l x t t',
                 ~ HE.In l Σ -> ~ HE.In l Σ' -> 
                 subtype Γ Ξ t t' ->
                 heap_subtype Γ Ξ Σ Σ' ->
(* ------------------------------------------------------------------- *)
    heap_subtype Γ Ξ (add l (x,t) Σ) (add l (x,t') Σ').

(* Definition heap_subtype Γ Ξ Σ Σ' := *)
(*   forall l x t t', MapsTo l (x, t) Σ -> MapsTo l (x, t') Σ' -> *)
                   
(*   eq_dom Σ Σ' /\ *)
(*     forall l x,  *)
(*       (exists t t', MapsTo l (x, t) Σ  -> MapsTo l (x, t') Σ' -> *)
(*                     subtype Γ Ξ t t'). *)

Inductive expr_type : type_env -> heap_env -> guards -> expr -> reft_type -> Prop :=
| t_int : forall Γ Σ Ξ n,
(* ------------------------------------------------------------------- *)
  expr_type Γ Σ Ξ (value_e (int_v n)) { ν : int_t | var_e ν .= value_e (int_v n) }

| t_null : forall Γ Σ Ξ,
(* ------------------------------------------------------------------- *)
  expr_type Γ Σ Ξ (value_e null_v) { ν : null_t | var_e ν .= value_e null_v }

| t_var : forall Γ Σ Ξ x τ φ, (x, { ν : τ | φ }) ∈ Γ ->
(* ------------------------------------------------------------------- *)
  expr_type Γ Σ Ξ (var_e x) { ν : τ | φ }

| t_sub : forall Γ Σ Ξ e T T',
            expr_type Γ Σ Ξ e T -> wf_type Γ Σ T' -> subtype Γ Ξ T T' -> 
(* ------------------------------------------------------------------- *)
  expr_type Γ Σ Ξ e T'.

Definition tc_list Γ Σ Ξ (xts : list (var * reft_type)) :=
  Forall (fun xt => 
            expr_type Γ Σ Ξ (var_e (fst xt)) (snd xt)) xts.

Definition join_var Ξ Γ1 Γ2 xt :=
  match xt with
  | (x, t) =>
    (exists t1, ((x,t1) ∈ Γ1 /\ subtype Γ1 Ξ t1 t))
    /\ (exists t2, ((x,t2) ∈ Γ2 /\ subtype Γ2 Ξ t2 t))
  end.

Definition join_env Ξ Σ Γ1 Γ2 Γ :=
  wf_env Σ Γ
  /\ (forall x, (var_in x Γ1 /\ var_in x Γ2) <-> var_in x Γ)
  /\ Forall (fun xt => (* wf_type Γ (snd xt)  *)
                       (* /\  *)join_var Ξ Γ1 Γ2 xt) Γ.

Definition fresh_heap_binds (Σ : heap_env) (Γ : type_env)  :=
  forall l x t, MapsTo l (x,t) Σ -> var_not_in x Γ.

Definition fresh_heap_binds' (Σ : heap_env) (Σ' : heap_env) :=
  forall l x t, MapsTo l (x,t) Σ -> bind_not_in x Σ'.

Definition heap_subst (Σ Σ': heap_env) (θ : subst_t var var) :=
  (forall x, bind_not_in x Σ -> subst θ x = x)
  /\ (forall l xt xt', MapsTo l xt Σ -> MapsTo l xt' Σ' -> subst θ (fst xt) = fst xt').

Definition join_heap Γ1 Γ2 Γ Ξ Σ1 Σ2 Σ :=
    wf_heap Γ Σ Σ 
    /\ fresh_heap_binds Σ Γ  
    /\ fresh_heap_binds Σ Γ1 
    /\ fresh_heap_binds Σ Γ2 
    /\ fresh_heap_binds' Σ Σ1 
    /\ fresh_heap_binds' Σ Σ2 
    /\ (exists θ1, heap_subst Σ1 Σ θ1)
    /\ (exists θ2, heap_subst Σ2 Σ θ2)
    /\ heap_subtype Γ1 Ξ Σ1 Σ 
    /\ heap_subtype Γ2 Ξ Σ2 Σ.

Definition isub {A : Type} {S : Subst A var var} {S' : Subst A loc loc}
           (θ : subst_t var var) (θl : subst_t loc loc) (t : A) : A
  := subst θl (subst θ t).

Definition fresh_new S θ θl Γ Σ :=
  (forall x, x ∈ isub θ θl (mod_vars S) -> fresh x Γ Σ)
  /\ fresh (isub θ θl (fst (s_ret S))) Γ Σ
  /\ forall l, l ∈ isub θ θl (mod_locs S) -> fresh_loc l Γ Σ.

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
    forall Φ Γ Σ Σ' Σu Σm Ξ (v:var) f p S (θ : subst_t var var) (θl : subst_t loc loc),
      NonUnifyingSub θ (s_heap_in S) -> NonUnifyingSub θ (s_heap_out S) ->
      NonUnifyingSub θl (subst θ (s_heap_in S)) -> NonUnifyingSub θl (subst θ (s_heap_out S)) ->
      (f,(p,S)) ∈ Φ -> wf_schema S -> wf_subst θ -> 
      heap_split Σu Σm Σ -> heap_split Σu (isub θ θl (s_heap_out S)) Σ' ->
      (forall x, subst θ x = (isub θ θl (fst (s_ret S))) <-> x = (fst (s_ret S))) ->
      (forall x', ~(In x' (fst (s_ret S) :: mod_vars S ++ s_formals S)) -> subst θ x' = x') ->
      fresh_new S θ θl Γ Σ ->
      wf_env Σ' (isub θ θl (s_ret S) :: Γ) ->
      wf_heap (isub θ θl (s_ret S) :: Γ) Σ' Σ' ->
      Forall (fun t => wf_type Γ Σ t) (@isub _ Subst_list Subst_list  θ θl (s_formal_ts S)) ->
      tc_list Γ Σ Ξ (combine (isub θ θl (s_formals S)) (@isub _ Subst_list Subst_list θ θl (s_formal_ts S))) ->
      heap_subtype Γ Ξ Σm (isub θ θl (s_heap_in S)) ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ; Ξ)
     ⊢ (isub θ θl (proc_s f (s_formals S) (fst (s_ret S)) (mod_vars S) (mod_locs S)))
       ::: (isub θ θl (s_ret S) :: Γ ; Σ'))

| t_pad : 
    forall Φ Γ Σ Ξ l x t,
      fresh x Γ Σ -> (* fresh a Γ Σ -> *) fresh_loc l Γ Σ -> wf_type Γ Σ t ->
(* ------------------------------------------------------------------- *)
      ((Φ ; Γ ; Σ ; Ξ) ⊢ pad_s l x ::: (Γ ; add l (x,t) Σ))

| t_assign : 
    forall Φ Γ Σ Ξ v e τ φ, 
      fresh v Γ Σ -> expr_type Γ Σ Ξ e { ν : τ | φ } ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ; Ξ)  ⊢ assign_s v e ::: ((v, {ν : τ | (var_e ν) .= e})::Γ ; Σ))

| t_alloc :
    forall Φ Γ Σ Ξ x y l e t,
      fresh x Γ Σ (* -> fresh a Γ Σ *) -> x <> y -> 
      expr_type Γ Σ Ξ e t -> wf_heap Γ (add l (y,t) Σ) (add l (y,t) Σ) ->
(* ------------------------------------------------------------------- *)
  ((Φ ; Γ ; Σ ; Ξ) ⊢ alloc_s l x e ::: ((x, {ν : ref_t l | tt_r})::Γ ; (add l (y,t) Σ)))

| t_if : 
    forall Φ Γ Γ1 Γ2 Γ' Σ Σ1 Σ2 Σ' Ξ e p s1 s2, 
      expr_type Γ Σ Ξ e { ν : int_t | p } ->
      ( Φ ; Γ ; Σ ; (e .= (int_v 1)) :: Ξ ) ⊢ s1 ::: (Γ1 ; Σ1) -> 
      ( Φ ; Γ ; Σ ; (e .= (int_v 0)) :: Ξ) ⊢ s2 ::: (Γ2 ; Σ2) ->
      join_env Ξ Σ' Γ1 Γ2 Γ' -> 
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
      (Φ ; [] ; empty type_binding ; []) ⊢ s ::: (Γ ; Σ) ->
      prog_type Φ (entry_p s)
| t_prog_procdecl :
  forall Φ Γ Σ p pr body prog e S,
    wf_schema S -> 
    fun_not_in p Φ ->
    p_args pr = s_formals S -> 
    p_body pr = seq_s body (return_s e) ->
    p_ret pr = fst (s_ret S) ->
    p_mod pr = [] ->
    ((p, (p_body pr, S))::Φ ; proc_init_env S ; empty type_binding ; [] ) ⊢ body ::: (Γ ; Σ) ->
    expr_type Γ (empty type_binding) [] e (subst (subst_one (fst (s_ret S)) e) (snd (s_ret S))) ->
    prog_type ((p,(p_body pr, S)) :: Φ) prog ->
(* ------------------------------------------------------------------- *)
    prog_type Φ (procdecl_p p pr prog).

(* Notation  " Φ ⊢ p " := (proc_type Φ f s S) (at level 0, no associativity). *)

Lemma heap_split_fresh :
  forall h h1 h2 x g,
    fresh x g h -> heap_split h1 h2 h -> fresh x g h1.
Proof.
  intros.
  unfold fresh in *.
  unfold heap_split in *.
  split; try split.
  apply H.
  apply H.
  decompose [and] H. clear H.
  simpl nonfv. unfold nonfv_heap.
  intros.
  destruct H0.
  simpl nonfv in *. unfold nonfv_heap in *.
  specialize (H2 l xt).
  destruct H2.
  split. trivial. 
  specialize (H4 l xt).
  simpl nonfv in H4.
  apply H4. apply H5. left. assumption.
Qed.

Lemma heap_split_fresh_loc :
  forall h h1 h2 x g,
    fresh_loc x g h -> heap_split h1 h2 h -> fresh_loc x g h1.
Proof.
  intros.
  unfold fresh in *.
  unfold heap_split in *.
  unfold fresh_loc in *.
  simpl nonfv in *.
  split. easy. unfold nonfv_heap. intros.
  destruct H0. destruct (H2 l xt). unfold nonfv_heap in *. destruct H.
  specialize (H5 l xt). apply H5.
  apply H4. left. easy.
Qed.

Lemma heap_split_nonfv :
  forall (x : var) (h h1 h2 : heap_env),
    heap_split h1 h2 h -> nonfv h x -> nonfv h1 x.
Proof.
  intros.
  simpl nonfv in *.
  unfold nonfv_heap in *.
  unfold heap_split in *.
  destruct H.
  intros. 
  specialize (H0 l xt).
  specialize (H1 l xt).
  apply H0.
  apply H1.
  left.
  easy.
Qed.

Hint Resolve heap_split_fresh heap_split_fresh_loc : heaps.