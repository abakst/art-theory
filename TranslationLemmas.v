Add LoadPath "vst".
Require Import msl.Coqlib2.
Require Import msl.log_normalize.
Require Import msl.eq_dec.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Equality.

Require Import Types.
Require Import Judge.
Require Import Subst.
Require Import ProgramLogic.
Require Import Translation.
Require Import Language.
Require Import WFLemmas.
Require Import SubstLemmas.
Require Import EvalLemmas.
Require Import Tactics.
Require Import List.
Import ListNotations.

Lemma forall_p_combine :
  forall (X Y : Type) (P : Y -> Prop) (xs : list X) (ys : list Y),
    length xs = length ys ->
    Forall P ys -> 
    Forall (fun xy => P (snd xy)) (combine xs ys).
Proof.
  intros.
  rewrite Forall_forall in *.
  intros.
  destruct x as [x y].
  simpl in *.
  pose (combine_split xs ys H).
  specialize (H0 y).
  apply in_combine_r in H1.
  apply H0.
  assumption.
Qed.

Lemma sub_eq_expr :
  forall (e : expr) x x', 
    subst (subst_one x (var_e x')) e 
    = subst (fun i => if eq_dec i x then x' else i) e.
Proof.
  induction e.
  * reflexivity.
  * intros. unfold subst. simpl. unfold subst_one. foo. 
  * intros.
    unfold subst at 1.
    unfold Subst_var_expr.
    unfold Language.subst_expr.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
Qed.
  
Lemma sub_eq :
  forall (p : reft_prop) x x', 
    subst (subst_one x (var_e x')) p 
    = subst (fun i => if eq_dec i x then x' else i) p.
Proof.
  intros.
  induction p.
  constructor.
  unfold subst.
  unfold Subst_prop, Subst_prop_var, subst_prop, subst_prop_var.
  rewrite sub_eq_expr.
  rewrite sub_eq_expr.
  reflexivity.
  unfold subst in *.
  simpl.
  rewrite IHp.
  reflexivity.
  unfold subst in *.
  simpl.
  rewrite IHp1.
  rewrite IHp2.
  reflexivity.
  unfold subst in *.
  simpl.
  rewrite IHp1.
  rewrite IHp2.
  reflexivity.
Qed.

Lemma subst_vv_ty:
  forall x x' T,
    x <> ν ->
    sep_ty (var_e x) T 
    |-- subst (subst_one ν x') (sep_ty (var_e x) T).
Proof.
  intros.
  unfold subst.
  unfold sep_ty.
  destruct T as [b p].
  rewrite subst_distr_andp.
  apply andp_derives.
  rewrite subst_distr_andp.
  apply andp_derives.
  unfold sep_base.
  unfold subst, Subst_pred, subst_pred.
  simpl in *.
  intro w.
  apply exp_left.
  intro vv.
  rewrite <- exp_andp1.
  apply andp_derives.
  normalize.
  apply (exp_right vv).
  apply prop_right.
  unfold subst_one. 
  destruct (eq_dec x ν).
    congruence.
    rewrite <- H0. reflexivity.
  apply derives_refl.
  intro w.
  unfold subst at 2, Subst_pred, subst_pred.
  repeat rewrite <- subst_ty_prop.
  unfold subst, Subst_pred, subst_pred.
  assert
     ((λ i : var, eval w (subst_one ν (var_e x) i))
      = (λ i : var,
               eval (fun i0 => eval w (subst_one ν x' i0), hp w)
                    (subst_one ν (var_e x) i))).
  extensionality i.
  unfold subst_one. 
  destruct (eq_dec i ν). 
  simpl.
  destruct (eq_dec x ν). intuition. reflexivity.
  destruct (eq_dec i ν). intuition. simpl.
  destruct (eq_dec i ν). intuition. reflexivity.
  rewrite <- H0.
  simpl.
  apply derives_refl.
  normalize.
Qed.
 
Lemma vv_sub_env :
  forall G,  
    var_not_in ν G -> 
      (forall x,
         sep_env G |-- subst (subst_one ν x) (sep_env G)).
Proof.
  intro G.
  induction G.
  + simpl. trivial.
  + destruct a as [b p].
    unfold sep_env in *.
    fold sep_env in *.
    intro H.
    intro e.
    repeat rewrite subst_distr_andp.
    apply andp_derives.
    apply andp_derives.
    apply subst_vv_ty.
    unfold var_not_in in H.
    rewrite Forall_forall in H.
    apply H with (x := (b, p)).
    left. reflexivity.
    apply IHG.
    inversion H.
    assumption.
    trivial.
Qed.

Lemma vv_sub_guards :
  forall G Grds,
    wf_guards G Grds -> 
      forall (x : expr),
      sep_guards Grds |-- subst (subst_one ν x) (sep_guards Grds).
Proof.
  intros G Grds.
  induction Grds as [| p].
  + simpl. trivial.
  + intros wf x.
    unfold sep_guards in *; fold sep_guards in *.
    inversion wf. subst.
    pose (wf_guards_vv_nonfree G Grds H2).
    repeat rewrite subst_distr_andp.
    repeat apply andp_derives.
    rewrite subst_nonfree_prop.
    apply derives_refl.
    apply H1.
    apply n.
    trivial.
Qed.

Lemma subtype_interp_pred :
  forall Γ Ξ φ φ' x b,
    var_not_in ν Γ ->
    wf_guards Γ Ξ -> 
    subtype Γ Ξ { ν : b | φ } { ν : b | φ' } -> 
    (sep_env Γ && sep_guards Ξ) |-- 
      sep_pred (subst (subst_one ν x) φ) --> 
      sep_pred (subst (subst_one ν x) φ').
Proof.
  intros.
  inversion H1. subst.
  simpl.
  intro.
  rewrite <- (subst_ty_prop φ (subst_one ν x) x0).
  rewrite <- (subst_ty_prop φ' (subst_one ν x) x0).
  apply derives_trans with
    (Q := subst (subst_one ν x) (sep_env Γ) x0 &&
          subst (subst_one ν x) (sep_guards Ξ) x0).
  apply andp_derives.
  apply vv_sub_env; assumption.
  apply vv_sub_guards with (G := Γ); assumption.
  unfold subst, Subst_pred, subst_pred.
  simpl in H5.
  apply H5.
Qed.

Lemma subtype_interp :
  forall Γ Ξ φ φ' x b,
    var_not_in ν Γ ->
    wf_guards Γ Ξ ->
    subtype Γ Ξ { ν : b | φ } { ν : b | φ' } -> 
      sep_env Γ && sep_guards Ξ |-- 
              sep_ty x { ν : b | φ } --> sep_ty x { ν : b | φ' }.
Proof.
  intros.
  unfold sep_ty.
  rewrite <- imp_andp_adjoint.
  repeat apply andp_right.
  apply andp_left2. apply andp_left1. apply andp_left1. apply derives_refl.
  apply derives_trans with (Q := (sep_pred (subst (subst_one ν x) φ) 
                              && (sep_pred (subst (subst_one ν x) φ) 
                                 --> sep_pred (subst (subst_one ν x) φ')))).
  apply andp_right.
  apply andp_left2. apply andp_left1. apply andp_left2. apply derives_refl.
  apply andp_left1. apply subtype_interp_pred with (b := b); assumption.
  apply modus_ponens.
  repeat apply andp_left1.
  apply sep_env_pure.
Qed.

Lemma heap_subtype_interp :
  forall Γ Ξ Σ Σ',
    wf_guards Γ Ξ ->
    heap_subtype Γ Ξ Σ Σ' ->
    sep_env Γ && sep_guards Ξ |-- sep_heap Σ --> sep_heap Σ'.
Proof.
  intros.
  rewrite <- imp_andp_adjoint.
  unfold heap_subtype in *.
  unfold sep_heap.
  induction Σ.
  destruct Σ'.
  apply andp_left2. apply derives_refl.
  destruct H0.
  unfold eq_dom in H0.
  destruct (H0 (fst p)).
  exfalso. unfold loc_in in H3. exists (snd p). left. destruct p. reflexivity.
  inversion H3.
  destruct Σ'.
  destruct H0.
  unfold eq_dom in H0.
  destruct (H0 (fst a)).
  unfold loc_in in H2. 
  destruct H2. exists (snd a). left. destruct a. reflexivity. inversion H2.
  unfold sep_heap. fold sep_heap.

Lemma vv_sub_env_eval :
  forall e ν x v w,
    x <> ν -> 
    eval w (subst (subst_one ν (var_e x)) e)
    = eval (λ i : var, eval w (subst_one ν v i), hp w) (subst (subst_one ν (var_e x)) e).
Proof.
  induction e.
  + intros. unfold subst, subst_one. reflexivity.
  + intros. unfold subst, subst_one.
    foo.
  + intros. unfold subst, subst_one in *. 
            unfold Subst_var_expr, subst_var, Language.subst_expr.
            simpl in *.
            unfold Subst_var_expr in *.
            rewrite IHe1 with (v:=v).
            rewrite IHe2 with (v:=v).
            reflexivity.
            assumption.
            assumption.
Qed.

Lemma vv_sub_env_prop :
  forall p ν x v w,
    x <> ν ->
    sep_pred (subst (subst_one ν (var_e x)) p) w =
    sep_pred (subst (subst_one ν (var_e x)) p)
             (λ i : var, eval w (subst_one ν v i), hp w).
Proof.
  intros.
  induction p.
  + constructor.
  + destruct b. unfold subst, Subst_prop, subst_prop. simpl.
    rewrite <- vv_sub_env_eval with (v := v).
    rewrite <- vv_sub_env_eval with (v := v).
    reflexivity.
    assumption.
    assumption.
  + simpl in *. unfold subst in *. unfold imp.
    rewrite IHp.
    reflexivity.
  + simpl. unfold subst, Subst_prop in *. 
    unfold andp.
    rewrite IHp1.
    rewrite IHp2.
    reflexivity.
  + simpl. unfold subst, Subst_prop in *. 
    unfold orp.
    rewrite IHp1.
    rewrite IHp2.
    reflexivity.
Qed.

Lemma vv_sub_env_ty :
  forall T x v,
    x <> ν ->
    sep_ty (var_e x) T |-- subst (subst_one ν v) (sep_ty (var_e x) T).
Proof.
  intros.
  unfold sep_ty in *.
  destruct T as [b p].
  repeat rewrite subst_distr_andp.
  repeat apply andp_derives.
  unfold subst. 
  unfold Subst_pred, subst_pred, subst_one.
  unfold sep_base.
  apply exp_left.
  intro vv.
  simpl.
  intro w.
  rewrite <- exp_andp1.
  apply andp_derives.
  apply prop_left.
  intro EQ.
  apply (exp_right vv).
  apply prop_right.
  destruct (eq_dec x ν). intuition. assumption.
  trivial.
  intro w.
  rewrite vv_sub_env_prop with (v:= v).
  apply derives_refl.
  assumption.
  trivial.
Qed.

Lemma subst_vv_env :
  forall Γ,
    var_not_in ν Γ ->
    nonfreevars (sep_env Γ) ν.
Proof.
  intros.
  induction Γ.
  + unfold nonfreevars. intro. apply derives_refl.
  + unfold sep_env. destruct a as [x [b p]].
    fold sep_env.
    unfold nonfreevars.
    intro e.
    repeat rewrite subst_distr_andp.
    repeat apply andp_derives.
    apply vv_sub_env_ty.
      unfold var_not_in in H.
      rewrite Forall_forall in H.
      apply (H (x, { ν : b | p })); left; reflexivity.
    apply IHΓ.
    inversion H.
    assumption.
    trivial.
Qed.

Lemma sep_env_base_var :
  forall Γ x b p,
    (x, { ν : b | p }) ∈ Γ ->
    sep_env Γ |-- sep_base (var_e x) b.
Proof.
  induction Γ.
  + intros. inversion H.
  + intros. 
    apply in_inv in H. 
    destruct a as [x' [b' p']].
    destruct H.
    inversion H. subst.
    apply andp_left1.
    apply andp_left1.
    apply andp_left1.
    apply andp_left1.
    apply derives_refl.
    unfold sep_env; fold sep_env.
    apply andp_left1.
    apply andp_left2.
    apply (IHΓ _ _ p).
    assumption.
Qed.

Lemma sep_env_base_val :
  forall Γ (v : value),
    sep_env Γ |-- sep_base v (base_of_val v).
Proof.
  intros.
  unfold sep_base.
  destruct (base_of_val v), v.
  unfold base_of_type.
  apply (exp_right n).
  simpl. intro. apply andp_right. apply prop_right. reflexivity.
  apply sep_env_pure.
Qed.

Lemma type_interp :
  forall Γ Ξ x T,
    var_not_in ν Γ ->
    expr_type Γ Ξ x T ->
    wf_guards Γ Ξ -> 
    sep_env Γ && sep_guards Ξ |-- sep_ty x T.
Proof.
  intros Γ Ξ x T vvnotin ET. (* [ ν b φ ]  w SE ET. *)
  unfold sep_ty.
  dependent induction ET.
  {
    intros wfg.
    apply andp_right.
    apply andp_right.
    apply andp_left1. 
    apply sep_env_base_val.
    intro w.
    simpl.
    apply andp_right.
    apply prop_right.
    unfold subst, Subst_var_expr, subst_one. simpl. foo.
    apply andp_left1; apply sep_env_pure.
    apply andp_left1; apply sep_env_pure.
  }
  {
    intros wfg.
    apply andp_right.
    apply andp_right.
  * apply andp_left1; apply sep_env_base_var with (p := φ); assumption.
  * clear wfg.
    apply andp_left1.
    induction Γ.
    + intuition.
    + intros. 
      destruct a as [x' [ b' p' ]].
      apply in_inv in H.
      destruct H.
      inversion H; subst.
      unfold sep_env; fold sep_env.
      apply andp_left1.
      apply andp_left1.
      apply andp_left1.
      apply andp_left2.
      solve [intuition].
      unfold sep_env; fold sep_env.
      apply andp_left1.
      apply andp_left2.
      apply IHΓ.
      inversion vvnotin. assumption.
      assumption.
   * apply andp_left1; apply sep_env_pure.
  }
  {
    fold (sep_ty e T) in IHET.
    fold (sep_ty e T').
    intro.
    apply derives_trans with (Q := sep_env Γ && sep_guards Ξ && sep_ty e T).
    apply andp_right.
    apply andp_right.
      apply andp_left1; apply derives_refl.
      apply andp_left2; apply derives_refl.
      apply IHET; assumption.
    apply imp_andp_adjoint.
    destruct T, T'. inversion H0. subst.
    apply subtype_interp; assumption.
  }
Qed.

Lemma types_interp :
  forall Γ Ξ xs ts,
    var_not_in ν Γ ->  
    wf_guards Γ Ξ ->
    tc_list Γ Ξ (combine xs ts) ->
    sep_env Γ && sep_guards Ξ |-- sep_env (combine xs ts).
Proof.
  intros.
  unfold tc_list in H1.
  rewrite Forall_forall in H1.
  unfold sep_env.
  induction (combine xs ts).
  + normalize. apply andp_left1. apply sep_env_pure.
  + destruct a. 
    fold sep_env.
    apply andp_right.
    apply andp_right.
    apply type_interp with (Γ := Γ);
      [ assumption | apply H1 with (x := (v,r)); left; reflexivity | assumption].
    apply IHl. 
    intro. intro.
    apply H1.
    unfold In. right. apply H2.
    apply andp_left1; apply sep_env_pure.
Qed.

Lemma funspec_nomem :
  forall Φ p, 
    fun_not_in p Φ ->
    Forall (fun ps => fst4 ps <> p) (sep_proc_env Φ).
Proof.
  intros.
  induction Φ.
  + constructor.
  + rewrite Forall_forall in *.
    intros [ [[p' pr] P] Q ] mem.
    destruct a as [p'' [s t]].
    unfold sep_proc_env in mem. fold sep_proc_env in mem.
    apply in_inv in mem.
    destruct mem.
    simpl in *.
    unfold sep_schema in H0.
    destruct t.
    destruct s_ret.
    inversion H0. subst.
    unfold fun_not_in in H.
    rewrite Forall_forall in H.
    specialize (H (p', (s, {| s_formals := s_formals; s_formal_ts := s_formal_ts; s_ret := (v,r) |}))).
    apply H.
    left. reflexivity.
    apply IHΦ.
    inversion H. assumption.
    assumption.
Qed.
    
Lemma funspec_interp :
  forall F f p t,
    In (f, (p,t)) F -> In (sep_schema f p t) (sep_proc_env F).
Proof.
  intros.
  induction F.
  + inversion H.
  + destruct H. destruct a. destruct p1. inversion H. subst.
    apply in_inv. left. reflexivity.
    apply IHF in H.
    unfold sep_proc_env.
    destruct a.
    destruct p1.
    simpl.
    right.
    apply H.
Qed.
(* Lemma sep_pred_pure : *)
(*   forall p Q, *)
(*     (sep_pred p && emp) && Q = sep_pred p * Q. *)
(* Proof. *)
(*   intros. *)
(*   induction p. *)
(*   simpl. *)
(*   extensionality. *)
(*   rewrite <- sepcon_emp at 1. *)
(*   rewrite sepcon_comm. *)
(*   apply pred_ext. *)
(*   apply sepcon_derives. *)
(*   apply prop_right. trivial. *)
(*   apply andp_left2. apply derives_refl. *)
  
(*   unfold pure. *)
(*   induction p. *)
(*   simpl.  *)
(*   repeat intro. *)
(*   repeat (unfold join, Join_fun, Join_lower, Join_discrete in H0; hnf in H0). *)
(*   destruct H0. *)
(*   destruct a. destruct a0. destruct b. *)
(*   unfold TT, prop in H. simpl in H. *)
(*   unfold pure. *)

(*   unfold identity. *)
(*   hnf. *)
(*   repeat intro. *)

(*   unfold join in H0. *)
(*   unfold Join_world in H0. *)
(*   destruct a. *)
(*   destruct a0. *)
(*   destruct b.  *)
(*   simpl in H0. *)
(*   hnf in H0. *)
(*   destruct H0. *)
(*   simpl in *. *)
(*   unfold join in *. *)
(*   hnf in *. *)
(*   unfold join, Join_equiv in *. *)
(*   unfold join, Join_lower, Join_discrete in H1. *)
(*   destruct H0 with (x := V 0). *)
  

Lemma sep_ty_pure_subst :
  forall x t θ,
    pure (subst θ (sep_ty x t)).
Proof.
  intros.
  unfold pure.
  destruct t.
  unfold subst, sep_ty, Subst_pred, subst_pred.
  intro w.
  simpl.
  apply andp_left2.
  trivial.
Qed.

(* Lemma sep_env_pure : *)
(*   forall G, *)
(*     pure (sep_env G). *)
(* Proof. *)
(*   intros. *)
(*   unfold pure. *)
(*   intro. intro. *)
(*   unfold identity. *)
(*   intros w1 w2. *)
(*   intros. *)
(*   apply H0. *)
(* Qed. *)

(* Lemma sep_guards_pure : *)
(*   forall G, *)
(*     pure (sep_guards G). *)
(* Proof. *)
(*   unfold pure. *)
(*   unfold identity. *)
(*   intros. *)
(*   intro. *)
(*   intro. *)
(*   intros w1 w2. *)
(*   intro. *)
(*   apply H0. *)
(* Qed. *)

Lemma sep_proof_skip :
  forall Φ Ξ Γ Γ' (J : (Φ ; Γ ; Ξ) ⊢ skip_s ::: Γ'), 
    sep_proc_env Φ |- {{ sep_env Γ * sep_guards Ξ }} skip_s {{ sep_env Γ' * sep_guards Ξ }}.
Proof.
  intros. inversion J. subst. constructor.
Qed.

Lemma sep_proof_assign :
  forall Φ Ξ Γ Γ' x e (J : (Φ ; Γ ; Ξ)⊢ assign_s x e ::: Γ'), 
    wf_env Γ ->
    wf_guards Γ Ξ ->
    sep_proc_env Φ |- {{ sep_env Γ * sep_guards Ξ }} assign_s x e {{ sep_env Γ' * sep_guards Ξ }}.
Proof.
  intros Φ Ξ Γ Γ' x e J wfenv wfguards.
  inversion J. subst.
  apply semax_frame.
  apply semax_pre_post with (P' := (EX v : value, (eval_to e v))
                                              && (subst_pred (subst_one x e )
                                                             (sep_env ((x, {ν : τ | (var_e ν) .= e }) :: Γ))))
                            (Q' := sep_env ((x,{ν : τ | (var_e ν) .= e }) :: Γ)).
  apply andp_right.
  unfold eval_to.
  simpl.
  intro w.
  rewrite <- exp_andp1.
  apply andp_right.
  apply (expr_eval Γ Ξ e τ φ H7).
  purity.
  apply derives_trans with (Q := sep_env Γ && subst_pred (subst_one x e) (sep_env Γ)).
  simpl. intro w.
  rewrite subst_dom_env. 
    apply andp_right; trivial.
    assumption.
    split. unfold subst_one. foo.
    intros x' x'_in.
    unfold subst_one. destruct (eq_dec x' x). subst.
    unfold var_in, var_not_in in *.
    rewrite Forall_forall in *.
    destruct x'_in.
    apply H5 in H.
    contradiction H. reflexivity. reflexivity.
    unfold subst_one. destruct (eq_dec ν x); congruence.
  apply subst_env_eq_expr with (Grds := Ξ) (φ := φ).
  assumption.
  apply derives_refl.
  rewrite exp_andp1.
  apply semax_assign with (e := e) (x := x) (P := (sep_env ((x, {ν : τ | var_e ν .= e}) :: Γ))).
  unfold subset.
  intros.
  inversion H. subst.
  apply wf_guards_nonfree with (Γ := Γ); assumption.
Qed.

Lemma sep_args_sub :
  forall Γ Ξ (xs' : list var) ts' (θ : subst_t var var) xs ts,
    length xs = length ts ->
    xs' = subst θ xs ->
    ts' = subst θ ts ->
    tc_list Γ Ξ (combine xs' ts') ->
    var_not_in ν Γ -> 
    wf_guards Γ Ξ ->
    sep_env Γ && sep_guards Ξ |-- sep_env (subst θ (combine xs ts)).
Proof.
  intros.
  assert (C: subst θ (combine xs ts) =
                      combine xs' ts').
    rewrite H0. rewrite H1.
    rewrite <- subst_combine with (xs := xs) (ys := ts).
    reflexivity.
    assumption.
  rewrite C.
  apply types_interp; assumption.
Qed.

Lemma sep_env_cons :
  forall x t Γ,
    sep_ty (var_e x) t * sep_env Γ |-- sep_env ((x,t) :: Γ).
Proof.
  intros.
  unfold sep_env at 2. fold sep_env.
  rewrite <- sepcon_emp at 1.
  rewrite <- sepcon_pure_andp.
  rewrite <- sepcon_pure_andp.
  apply sepcon_derives.
  apply sepcon_derives.
  apply derives_refl.
  apply derives_refl.
  apply derives_refl.
  apply sep_ty_pure.
  apply sep_env_pure.
  unfold pure. apply andp_left1. apply sep_ty_pure.
  apply derives_refl.
Qed.
  
Lemma sep_env_cons_sub :
  forall x b p θ Γ,
    θ ν = ν -> (forall x , θ x = ν -> x = ν) ->
    subst θ (sep_ty (var_e x) { ν : b | p }) * sep_env Γ
    |-- sep_env ((subst θ (x,{ ν : b | p })) :: Γ).
Proof.
  intros x b p θ Γ vv_id vv_im.
  unfold sep_env; fold sep_env.
  rewrite sepcon_pure_andp.
  simpl.
  intro w.
  apply andp_right.
  apply andp_derives.
  rewrite subst_lift_assert.
  rewrite <- subst_ty_distr. 
  unfold sep_ty. simpl.
  apply andp_derives.
  apply andp_derives.
  unfold subst, Subst_var_var. apply derives_refl.
  unfold subst. simpl.
  rewrite subst_lift_pred. unfold subst. simpl. apply derives_refl.
  apply derives_refl.
  rewrite vv_id. reflexivity.
  apply subst_vv_not_in_range.
  intro v. split. apply vv_im. intro. rewrite H. assumption.
  apply derives_refl.
  apply andp_left2. apply sep_env_pure.
  apply sep_ty_pure_subst.
  apply sep_env_pure.
Qed.

Lemma sep_proof_proc_ret :
  forall (θ : subst_t var var) x t Γ, 
    θ ν = ν -> (forall x, θ x = ν -> x = ν) ->
    wf_type (subst θ (x,t) :: Γ) (subst θ t)  ->
   (subst θ (sep_ty (var_e x) t)) * sep_env Γ |--
    sep_env ((subst θ (x,t)) :: Γ).
Proof.
  intros θ x t Γ vvid vvim wf H.
  destruct t as [ b p ].
  simpl in *.
  apply sep_env_cons_sub. 
  assumption.
  assumption.
Qed.

Lemma sep_proof_proc_sub :
  forall x v θ,
    v  = subst θ x ->
    (forall x', θ x' = v <-> x = x') ->
    unique_sub θ x.
Proof.
  intros x v θ vdef subprop.
  unfold unique_sub.
  exists v.
  split.
  symmetry. apply vdef.
  intros.
  unfold not_free_in.
  specialize (subprop x0).
  destruct subprop.
  intuition.
  apply H.
  symmetry.
  intuition.
Qed.

Lemma sep_proof_proc_mod :
  forall f xs x x',
    modvars (proc_s f xs x []) x' -> x = x'.
Proof.
  intros.
  inversion H.
  intuition.
  reflexivity.
Qed.

Ltac wfenv_ty_t :=
  match goal with 
    | [ X : ?x = ?a, Y : ?y = ?b, H : wf_type _ _ |- _ ] =>
      rewrite X in H; rewrite Y in H; assumption
    | [ H : (?x, ?y) = subst _ (_, _) |- _ ] => 
      unfold subst, Subst_prod, subst_prod in H; inversion H; wfenv_ty_t
    | [ H : wf_env (subst ?x (?f ?z) :: ?G) |- wf_type (subst ?x (?f ?z) :: ?G) _ ]  =>
      inversion H; destruct (f z); simpl in *; wfenv_ty_t
  end.

Lemma lift_assert :
  forall {P Q : assert} w, P |-- Q ->(P w |-- Q w).
Proof.
  intros.
  apply H.
Qed.

Lemma sep_proof_proccall :
  forall Φ Ξ Γ Γ' f xs v (J : (Φ ; Γ ; Ξ) ⊢ proc_s f xs v [] ::: Γ'),
    wf_env Γ ->
    wf_guards Γ Ξ ->
    sep_proc_env Φ |- {{ sep_env Γ * sep_guards Ξ }} proc_s f xs v [] {{ sep_env Γ' * sep_guards Ξ }}.
Proof.
  intros until v. 
  intros J wf wfg.
  inversion J as [ | ? ? ? ? ? p S ? ? θ θS fmem wfS wfθ 
                     ? ? ? ? retid substid wfenv wfsubty tclist
                     | | | ]. 
  simpl in *. subst.
  destruct S as [fxs fts [rx rt]] eqn:S_def.
  simpl in *.
  apply funspec_interp in fmem.
  unfold sep_schema in fmem. 
  apply semax_pre_post with 
  (P' := ((Subst.subst θ (sep_env (combine fxs fts)))) * (sep_env Γ * sep_guards Ξ)) 
  (Q' := ((Subst.subst θ (sep_ty (var_e rx) rt))) * (sep_env Γ * sep_guards Ξ)).
  intro w.
  simpl.
  rewrite <- (subst_in_env Γ).
  rewrite sepcon_pure_andp at 1.
2: purity.
2: purity.
  rewrite (sepcon_pure_andp (sep_env (subst θ (combine fxs fts)) w)). 
2: purity.
2: purity.
  apply andp_right.
  pose sep_args_sub as argstc; simpl in argstc; apply argstc with (xs' := subst θ fxs) (ts' := subst θ fts).
  inversion wfS; assumption.
  reflexivity.
  reflexivity.
  assumption.
  apply wf_env_no_vv; assumption.
  assumption.
  rewrite sepcon_pure_andp; try apply derives_refl; purity.
  wfsubst θ.
  assumption.
  assumption.
  rewrite subst_combine.
  apply forall_p_combine.
  inversion wfS; repeat rewrite <- subst_length; assumption.
  assumption.
  inversion wfS; assumption.
  rewrite <- sepcon_assoc.
  simpl.
  intro w.
  apply sepcon_derives.
  pose sep_proof_proc_ret as RT; simpl in RT; apply RT.
  apply wfθ; reflexivity.
  apply wfθ.
  inversion wfenv; assumption.
  apply derives_refl.
  apply semax_frame.
  subst.
  assert (A : subst θ (proc_s f fxs rx []) = proc_s f (subst θ fxs) (subst θ rx) []).
  unfold subst at 1. simpl. reflexivity.
  rewrite <- A.
  apply semax_subst.
  apply (semax_proc f (mkProc fxs rx [] p)).
  assumption.
  intros.
  assert (rx = x) by 
      (apply sep_proof_proc_mod with (f:=f) (xs:= fxs); assumption).
  subst.
  apply sep_proof_proc_sub with (v := subst θ x).
  reflexivity.
  intros.
  specialize (retid x').
  constructor; intro; [ symmetry | idtac ]; apply retid; [ idtac | symmetry]; assumption.
  unfold subset.
  intros.
  unfold nonfreevars.
  intros.
  assert (A : subst θ rx = x).
    apply sep_proof_proc_mod with (f := f) (xs := subst θ fxs).
    assumption.
  assert (B : x <> ν).
    inversion wfenv.
    rewrite <- A.
    assumption.
  rewrite sepcon_pure_andp.
2: purity.
2: purity.
  rewrite subst_distr_andp.
  apply andp_derives.
  simpl.
  unfold subst, Subst_pred.
  intro w.
  rewrite subst_dom_env.
    apply derives_refl.
    assumption.
    apply subst_one_is_disj.
    assumption.
    assumption.
    inversion wfenv. rewrite <- A. assumption.
    unfold subst_one. foo.
  intro w.
  rewrite subst_dom_guards with (Γ := Γ).
  apply derives_refl.
  assumption.
  apply subst_one_is_disj.
  assumption.
  assumption.
  inversion wfenv. rewrite <- A. assumption.
Qed.

Lemma subtype_same_base :
  forall Ξ Γ b b' p p',
    subtype Γ Ξ { ν : b | p } { ν : b' | p' } ->
    subtype Γ Ξ { ν : b | p } { ν : b | p' }.
Proof.
  intros.
  inversion H.
  subst.
  assumption.
Qed.

Lemma types_interp2 :
  forall Ξ Γ Γ', 
    wf_env Γ -> wf_guards Γ Ξ ->
   (forall x t, (x,t) ∈ Γ' -> (exists t1, (x,t1) ∈ Γ /\ subtype Γ Ξ t1 t)) ->
   sep_env Γ && sep_guards Ξ |-- sep_env Γ'.
Proof.
  intros Ξ Γ Γ' wfe wfg H.
  induction Γ' as [| [x t]].
  + apply andp_right. normalize. purity.
  + unfold sep_env; fold sep_env.
    apply andp_right.
    apply andp_right.
    specialize (H x t).
    destruct H. left. reflexivity.
    destruct t as [b p].
    destruct x0 as [b0 p0].
    apply derives_trans with (Q := sep_env Γ && sep_guards Ξ && sep_ty (var_e x) {ν : b | p0}).
    apply andp_right. trivial. apply type_interp.
    apply wf_env_no_vv.
    exact wfe.
    constructor.
    destruct H. inversion H0. subst.
    apply H.
    exact wfg.
    rewrite imp_andp_adjoint.
    pose subtype_interp as ST. simpl in ST. simpl. apply ST.
    apply wf_env_no_vv.
    exact wfe.
    exact wfg.
    destruct H.
    inversion H0; subst.
    assumption.
    apply IHΓ'.
    intros x0 t0 x0mem.
    apply H.
    right.
    apply x0mem.
    purity.
Qed.

Lemma join_swap :
  forall Γ1 Γ2 Γ' Ξ,
    join_env Ξ Γ1 Γ2 Γ' <-> join_env Ξ Γ2 Γ1 Γ'.
Proof.
  intros.
  unfold join_env.
  constructor.
  intros [a [b c]].
  split.
  assumption.
  split.
  intros xt.
  specialize (b xt).
  rewrite and_comm.
  apply b.
  unfold join_var in *.
  rewrite Forall_forall in *.
  intros [x t].
  intro.
  destruct c with (x,t).
  apply H.
  split.
  apply H0.
  rewrite and_comm.
  apply H1.
  intros [a [b c]].
  split.
  assumption.
  split.
  intros xt.
  specialize (b xt).
  rewrite and_comm.
  apply b.
  unfold join_var in *.
  rewrite Forall_forall in *.
  intros [x t].
  intro.
  destruct c with (x,t).
  apply H.
  split.
  apply H0.
  rewrite and_comm.
  apply H1.
Qed.
  
Lemma join_interp :
  forall Γ1 Γ2 Γ' Ξ ,
    wf_env Γ1 -> wf_env Γ2 -> wf_guards Γ1 Ξ ->
    join_env Ξ Γ1 Γ2 Γ' ->
    (sep_env Γ1 && sep_guards Ξ) |-- sep_env Γ' && sep_guards Ξ.
Proof.
  intros until Ξ.
  intros wf1 wf2 wfg J.
  apply andp_right.
  destruct J as [wfJ [J1 J2]].
  rewrite Forall_forall in J2.
  unfold join_var in J2.
  apply types_interp2.
  assumption.
  assumption.
  intros x t xtmem.
  specialize (J2 (x,t) xtmem).
  apply J2.
  apply andp_left2; apply derives_refl.
Qed.

Lemma sep_proof_if_derives :
  forall Ξ Γ Γ1 Γ2 Γ' e t g,
    wf_env Γ ->
    wf_env Γ1 ->
    wf_env Γ2 ->
    wf_guards Γ Ξ ->
    wf_guards Γ1 Ξ ->
    wf_guards Γ2 Ξ ->
    join_env Ξ Γ1 Γ2 Γ' ->
    expr_type Γ Ξ e t ->
    (* (Φ; Γ; not_r (e .= int_v 0) :: Ξ)⊢s1 ::: (Γ1) -> *)
    (* (Φ; Γ; (e .= int_v 0) :: Ξ)⊢s2 ::: (Γ2) -> *)
    sep_env Γ1 * sep_guards (g :: Ξ) |-- sep_env Γ' && sep_guards Ξ.
Proof.
  intros until g. intros wf wf1 wf2 wfg wfg1 wfg2 joinenv et.
  unfold sep_guards; fold sep_guards.
  rewrite sepcon_pure_andp.
2: purity.
2: purity.
  repeat rewrite <- andp_assoc.
  apply andp_left1.
  rewrite andp_assoc.
  rewrite andp_comm.
  rewrite andp_assoc.
  apply andp_left2.
  rewrite andp_comm.
  apply join_interp with (Γ2 := Γ2); assumption.
Qed.

Lemma wf_guard_expr_type1 :
  forall Γ Ξ e t,
    wf_env Γ ->
    expr_type Γ Ξ e t ->
    wf_guard Γ (e .= int_v 1).
Proof.
  intros.
  split.
  repeat constructor.
  apply wf_expr_ty_expr with Ξ t.
    assumption.
  simpl. rewrite  app_nil_r.
  apply wf_expr_ty_expr_fv with Γ Ξ t; assumption.
Qed.

Lemma wf_guard_expr_type2 :
  forall Γ Ξ e t,
    wf_env Γ ->
    expr_type Γ Ξ e t ->
    wf_guard Γ (e .= int_v 0).
Proof.
  intros.
  split.
  repeat constructor.
  apply wf_expr_ty_expr with Ξ t.
    assumption.
  simpl. rewrite  app_nil_r.
  apply wf_expr_ty_expr_fv with Γ Ξ t; assumption.
Qed.

Lemma sep_proof_if :
  forall Φ Ξ Γ Γ1 Γ2 Γ' s1 s2 e t,
    wf_env Γ ->
    wf_guards Γ Ξ ->
    expr_type Γ Ξ e t ->
    (Φ; Γ; (e .= int_v 1) :: Ξ)⊢s1 ::: (Γ1) ->
    (Φ; Γ; (e .= int_v 0) :: Ξ)⊢s2 ::: (Γ2) ->
    join_env Ξ Γ1 Γ2 Γ' ->
    (wf_env Γ
         → wf_guards Γ ((e .= int_v 1) :: Ξ)
           → sep_proc_env Φ |- 
             {{sep_env Γ * sep_guards ((e .= int_v 1) :: Ξ)}}s1
             {{sep_env Γ1 * sep_guards ((e .= int_v 1) :: Ξ)}}) ->
    (wf_env Γ
       → wf_guards Γ ((e .= int_v 0) :: Ξ)
         → sep_proc_env Φ |- 
           {{sep_env Γ * sep_guards ((e .= int_v 0) :: Ξ)}}s2
           {{sep_env Γ2 * sep_guards ((e .= int_v 0) :: Ξ)}}) ->
    sep_proc_env Φ |- {{ sep_env Γ && sep_guards Ξ }} 
                        if_s e s1 s2 
                        {{ sep_env Γ' && sep_guards Ξ }}.
Proof.
  intros until t.
  intros wf wfg et H1 H2 joinenv IH1 IH2.
  assert (WF1 : wf_env Γ1).
    apply wf_env_stmt with Φ Γ ((e .= int_v 1) :: Ξ) s1; assumption.
  assert (WF2 : wf_env Γ2).
    apply wf_env_stmt with Φ Γ (((e .= int_v 0)) :: Ξ) s2; assumption.
  assert (WFG1 : wf_guards Γ1 ((e .= int_v 1) :: Ξ)).
    apply wf_guards_stmt with Φ Γ s1. assumption. assumption.
    apply Forall_cons. 
      apply wf_guard_expr_type1 with Ξ t; assumption. 
      assumption.
  assert (WFG2 : wf_guards Γ2 ((e .= int_v 0) :: Ξ)).
    apply wf_guards_stmt with Φ Γ s2. assumption. assumption.
    apply Forall_cons. 
      apply wf_guard_expr_type2 with Ξ t; assumption. 
      assumption.
  apply semax_if.
  rewrite andp_comm.
  rewrite andp_assoc.
  rewrite andp_comm with (P := sep_guards Ξ).
  apply semax_pre_post with (P' := sep_env Γ * sep_guards ((e .= int_v 1) :: Ξ))
                            (Q' := sep_env Γ1 * sep_guards ((e .= int_v 1) :: Ξ)).
  rewrite sepcon_pure_andp.
    repeat apply andp_right.
    apply andp_left1. apply derives_refl.
    apply andp_left2. apply andp_left1. 
    unfold eval_to. simpl. intro. apply andp_left1. apply derives_refl.
    apply andp_left1. purity.
    fold sep_guards.
    do 2 apply andp_left2. apply derives_refl.
    apply andp_left1. purity.
    purity.
    apply sep_guard_pure.
  apply sep_proof_if_derives with Γ Γ2 e t.  
    assumption.
    assumption.
    assumption.
    assumption.
    inversion WFG1; assumption.
    inversion WFG2; assumption.
    assumption.
    assumption.
  apply IH1.
  assumption.
  apply Forall_cons.
    apply wf_guard_expr_type1 with Ξ t; assumption.
    assumption.
  apply semax_pre_post with (P' := sep_env Γ * sep_guards ((e .= int_v 0) :: Ξ))
                            (Q' := sep_env Γ2 * sep_guards ((e .= int_v 0) :: Ξ)).
    rewrite sepcon_pure_andp.
    repeat apply andp_right.
    apply andp_left2. apply andp_left1. apply derives_refl.
    apply andp_left1. unfold eval_to. intro. apply andp_left1. apply derives_refl.
    apply andp_left2. purity.
    fold sep_guards.
    apply andp_left2. apply andp_left2. apply derives_refl.
    apply andp_left2. purity.
    purity.
    apply sep_guard_pure.
  apply sep_proof_if_derives with Γ Γ1 e t;
    repeat first [ assumption | inversion WFG1; assumption | inversion WFG2; assumption].
  apply join_swap. assumption.
  apply IH2.
  assumption.
  apply Forall_cons.
    apply wf_guard_expr_type2 with Ξ t; assumption.
    assumption.
Qed.

Theorem sep_proof_stmt :
  forall Φ Ξ Γ Γ' s (J : (Φ ; Γ ; Ξ) ⊢ s ::: Γ'),
    wf_env Γ ->
    wf_guards Γ Ξ ->
    sep_proc_env Φ |- {{ sep_env Γ && sep_guards Ξ }} s {{ sep_env Γ' && sep_guards Ξ }}.
Proof.
  intros.
  rewrite <- sepcon_pure_andp.
  rewrite <- sepcon_pure_andp.
  dependent induction J.
  + apply sep_proof_skip with (Φ := Φ) (Ξ := Ξ). constructor.
  + apply sep_proof_proccall with (Φ := Φ) (Ξ := Ξ).
    econstructor; eauto.
    assumption.
    assumption.
  + apply sep_proof_assign with (Φ := Φ) (Ξ := Ξ). 
    econstructor; eauto.
    assumption.
    assumption.
  + repeat rewrite sepcon_pure_andp.
    apply sep_proof_if with Γ1 Γ2 { ν : int_t | p }; assumption.
    purity.
    purity.
    purity.
    purity.
  + apply semax_seq with (Q := sep_env Γ' * sep_guards Ξ).
    apply IHJ1; assumption.
    apply IHJ2. 
    apply wf_env_stmt with (P := Φ) (G := Γ) (X := Ξ) (s := s1); assumption.
    apply wf_guards_stmt with (P := Φ) (G := Γ) (X := Ξ) (s := s1); assumption.
 + apply sep_env_pure.
 + apply sep_guard_pure.
 + apply sep_env_pure.
 + apply sep_guard_pure.
Qed.

Corollary type_safety_stmt :
  forall Φ Γ s, (Φ ; [] ; []) ⊢ s ::: Γ -> sep_proc_env Φ |- {{ emp }} s {{ TT }}.
Proof.
  intros.
  assert (wf_env nil). constructor.
  assert (wf_guards nil nil). constructor.
  apply semax_pre_post with (P' := sep_env nil && sep_guards nil) 
                            (Q' := sep_env Γ && sep_guards nil);
  first [ apply sep_proof_stmt with (Φ := Φ) (Ξ := []); assumption
        | unfold sep_guards; normalize ].
Qed.

Theorem sep_proof_program :
  forall Φ p,
    prog_type Φ p -> semax_prog (sep_proc_env Φ) p.
Proof.
  intros Φ p H.
  induction H.
  + constructor.
    apply type_safety_stmt with Γ; assumption.
  + assert (WFΓ : wf_env Γ).
      inversion H.
      pose (wf_env_stmt _ _ Γ _ body H9 H5).
      apply w.
    destruct pr. 
    simpl in *.
    subst.
    pose (@semax_procdecl_p (sep_proc_env Φ)
                           e
                           body
                           (sep_schema p (seq_s body (return_s e)) S)
                           prog) as P.
    unfold sep_schema in P.
    destruct S.
    destruct s_ret.
    simpl in *.
    simpl in *.
    apply P.
    reflexivity.
    apply funspec_nomem.
    assumption.
    simpl in *.
    apply semax_pre_post with (P' := sep_env (combine s_formals s_formal_ts) && sep_guards [])
                              (Q' := sep_env Γ && sep_guards []).
    apply andp_right. 
      apply derives_refl. 
      unfold sep_guards. apply andp_right. normalize. purity.
    destruct r as [ τ φ ].
    apply derives_trans with (Q := sep_ty (subst (subst_one v e) (var_e v)) 
                                         (subst (subst_one v e) {ν : τ | φ})).
    unfold subst, Subst_var_expr, subst_one at 1, Language.subst_expr.
    destruct (eq_dec v v).
    apply type_interp.
    inversion H.
    apply wf_env_no_vv. 
    apply WFΓ.
    assumption.
    constructor.
    intuition.
    intro.
    rewrite subst_ty_distr. apply derives_refl.
    inversion H.
    clear P. clear H1.
    inversion H3.
    unfold subst_one.
    destruct (eq_dec ν v). intuition. subst. reflexivity.
    assert (NEQ : v <> ν).
    inversion H.
    inversion H3. assumption.
    apply subst_vv_not_in_range_exp.
    apply wf_expr_ty_expr_fv with (Γ := Γ) (Ξ := []) (T := subst (subst_one v e) { ν : τ | φ }).
    apply WFΓ.
    assumption.
    apply sep_proof_stmt in H5.
    apply H5.
    inversion H.
    apply H2.
    constructor.
    apply IHprog_type.
Qed.