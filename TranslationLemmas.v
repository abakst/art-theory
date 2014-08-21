Add LoadPath "vst".
Require Import msl.msl_direct.
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

Lemma subtype_interp_pred :
  forall Γ φ φ' b,
    subtype Γ { ν : b | φ } { ν : b | φ' } -> 
    (forall w,
      sep_env Γ w -> 
      sep_pred φ w -> sep_pred φ' w).
Proof.
  intros.
  inversion  H.
  apply H4; assumption.
Qed.

Lemma subtype_interp :
  forall Γ φ φ' x b,
    subtype Γ { ν : b | φ } { ν : b | φ' } -> 
    (forall w,
      sep_env Γ w -> 
      sep_ty x { ν : b | φ } w ->
      sep_ty x { ν : b | φ' } w).
Proof.
  intros.
  unfold sep_ty.
  split.
  apply H1.
  apply subtype_interp_pred with Γ φ b.
  assumption.
  unfold subst_one.
  
  
  intros G p p' x b. 
  induction G.
  + intros. inversion H. simpl in *.
    split. apply H1. apply H4. constructor. apply H1.
  + intros st w senv st1.
    


  w stype.
  inversion stype; subst.
  induction G.
  + destruct xin; inversion H.
  + destruct a as [ x' t' ].
    unfold imp, derives in *.
    unfold var_in in xin.
    destruct xin as [ ? xin ].
    apply in_inv in xin.
    destruct xin as [ xin | xin ].
    inversion xin; subst.
    inversion stype. subst.
    split.
    apply st1.
    apply H2.
    



    inversion xin; subst.
    unfold sep_env.
    fold sep_env.
    split.
    unfold sep_ty.
    destruct x0.
    inversion stype. subst.
    
  
  
  
  
  

Lemma type_interp :
  forall Γ x T,
    expr_type Γ (var_e x) T ->
    forall w,
      (sep_env Γ w -> sep_ty x T w).
Proof.
  intros Γ x T ET. (* [ ν b φ ]  w SE ET. *)
  dependent induction ET. 
  unfold sep_ty.
  intros w SE.
  split.
  + fold (subst_pred (subst_one ν (var_e x)) (sep_base ν τ) w).
    rewrite subst_vv_base_ap. 
    apply expr_eval_ty with (Γ := Γ) (φ := φ).
    apply SE.
    constructor; assumption.
  + generalize dependent Γ. 
    induction Γ. 
    - intros. inversion H.
    - intros. apply in_inv in H. destruct a. destruct H.
      * inversion H. subst. apply SE.
      * apply IHΓ. unfold sep_env in SE.
        {
          apply H. 
        } 
        {
          apply SE. 
        } 
  + intros w SE.
    destruct T as [ vv b p ]. destruct T' as [ vv' b' p' ].
    inversion H.
    inversion H0.
    subst.
    unfold subst_pred.
    split.
    apply IHET.
    assumption.
    unfold andp in IHET.
    unfold derives, imp in H8.
    specialize (H8 w SE).
    specialize (IHET w SE).
    destruct IHET.
    
    apply H8.

Lemma type_interp :
  forall Γ x T w,
    sep_env Γ w -> (expr_type Γ (var_e x) T) -> sep_ty x T w.
Proof.
  intros Γ x T (* [ ν b φ ] *) w SE ET.
  unfold sep_ty.
  subst.
  dependent induction ET. 
  split.
  + fold (subst_pred (subst_one ν (var_e x)) (sep_base ν τ) w).
    rewrite subst_vv_base_ap. 
    apply expr_eval_ty with (Γ := Γ) (φ := φ).
    apply SE.
    constructor; assumption.
  + generalize dependent Γ. 
    induction Γ. 
    - intros. inversion H.
    - intros. apply in_inv in H. destruct a. destruct H.
      * inversion H. subst. apply SE.
      * apply IHΓ. unfold sep_env in SE.
        {
          apply H. 
        } 
        {
          apply SE. 
        } 
  + destruct T as [ vv b p ]. destruct T' as [ vv' b' p' ].
    inversion H.
    inversion H0.
    subst.
    specialize (IHET SE).
    destruct IHET.
    split.
    assumption.
    unfold derives, imp in H8.
    apply H8.
    
    
    
Qed.

Lemma types_interp :
  forall Γ xs ts s,
    sep_env Γ s ->
    tc_list Γ (combine xs ts) ->
    sep_env (combine xs ts) s.
Proof.
  intros.
  unfold tc_list in H0.
  rewrite Forall_forall in H0.
  unfold sep_env.
  induction (combine xs ts).
  + constructor.
  + destruct a. split.
    apply type_interp with (Γ := Γ).
    assumption. apply H0 with (x := (v,r)). unfold In. left. reflexivity.
    apply IHl. 
    intro. intro.
    apply H0.
    unfold In. right. apply H1.
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

Lemma sep_proof_skip :
  forall Φ Γ Γ' (J : (Φ / Γ ⊢ skip_s ::: Γ')), 
    sep_proc_env Φ |- {{ sep_env Γ }} skip_s {{ sep_env Γ' }}.
Proof.
  intros. inversion J. constructor.
Qed.

Lemma sep_proof_assign :
  forall Φ Γ Γ' x e (J : (Φ / Γ ⊢ assign_s x e ::: Γ')), 
    wf_env Γ ->
    sep_proc_env Φ |- {{ sep_env Γ }} assign_s x e {{ sep_env Γ' }}.
Proof.
  intros Φ Γ Γ' x e J wfenv.
  inversion J. subst.
  apply semax_pre_post with (P' := EX v : value, (eval_to e v)
                                              && (subst_pred (subst_one x e )
                                                             (sep_env ((x, {ν : τ | (var_e ν) .= e }) :: Γ))))
                            (Q' := sep_env ((x,{ν : τ | (var_e ν) .= e }) :: Γ)).
  intro w. intro SE.
  pose (expr_eval Γ e τ φ w SE H6) as ValWit. 
  destruct ValWit.
  exists x0. split. apply H.
  apply subst_env_eq_expr with (φ := φ).
  assumption.
  assumption.
  rewrite subst_dom_env.
  assumption.
  assumption.
  split. unfold subst_one. destruct (eq_dec ν x). subst. contradiction H1. reflexivity. reflexivity.
  intros x' x'_in_ctx.
  unfold subst_one. destruct (eq_dec x' x). subst. 
  unfold var_in in *.
  unfold var_not_in in *. rewrite Forall_forall in H4. destruct (x'_in_ctx). apply H4 in H. 
  contradiction H. reflexivity. reflexivity.
  unfold subst_one. destruct (eq_dec ν x). subst. contradiction H1. reflexivity. reflexivity.
  auto.
  apply semax_assign with (e := e) (x := x) (P := (sep_env ((x, {ν : τ | var_e ν .= e}) :: Γ))).
Qed.

Lemma sep_ty_pure :
  forall x t,
    pure (sep_ty x t).
Proof.
  intros.
  unfold pure.
  intro w.
  intro.
  unfold identity.
  intros w' w''.
  intro. apply H0.
Qed.

Lemma sep_ty_pure_subst :
  forall x t θ,
    pure (subst θ (sep_ty x t)).
Proof.
  intros.
  unfold pure.
  intro w.
  intro.
  unfold identity.
  intros w' w''.
  intro.
  apply H0.
Qed.

Lemma sep_env_pure :
  forall G,
    pure (sep_env G).
Proof.
  intros.
  unfold pure.
  intro. intro.
  unfold identity.
  intros w1 w2.
  intros.
  apply H0.
Qed.

Lemma sep_args_sub :
  forall Γ (xs : list var) ts (θ : subst_t var var) S w,
    length (s_formals S) = length (s_formal_ts S) ->
    xs = subst θ (s_formals S) ->
    ts = subst θ (s_formal_ts S) ->
    tc_list Γ (combine xs ts) ->
    sep_env Γ w ->
    sep_env (subst θ (combine (s_formals S) (s_formal_ts S))) w.
Proof.
  intros.
  assert (C: subst θ (combine (s_formals S) (s_formal_ts S)) = 
                      combine xs ts).
    rewrite H0. rewrite H1. 
    rewrite <- subst_combine with (xs := s_formals S) (ys := s_formal_ts S).
    reflexivity.
    assumption.
  rewrite C.
  apply types_interp with Γ.
  assumption.
  assumption.
Qed.

Lemma sep_env_cons :
  forall x t Γ w,
    (sep_ty x t * sep_env Γ)%pred w ->
    sep_env ((x,t) :: Γ) w.
Proof.
  intros.
  unfold sep_env.
  split.
  rewrite sepcon_pure_andp in H.
  destruct H.
  apply H.
  apply sep_ty_pure.
  apply sep_env_pure.
  rewrite sepcon_pure_andp in H.
  destruct H.
  apply H0.
  apply sep_ty_pure.
  apply sep_env_pure.
Qed.
  
Lemma sep_env_cons_sub :
  forall x b p θ Γ w ,
    θ ν = ν -> (forall x , θ x = ν -> x = ν) ->
    ((subst θ (sep_ty x { ν : b | p })) * sep_env Γ)%pred w ->
    sep_env ((subst θ (x,{ ν : b | p })) :: Γ) w.
Proof.
  intros x b p θ Γ w vv_id vv_im.
  unfold sep_env.
  intro.
  rewrite sepcon_pure_andp in H.
  destruct H.
  split.
  unfold subst in H. unfold Subst_pred_var in H.
  apply subst_ty_distr; assumption.
  apply H0.
  apply sep_ty_pure_subst with (t := {ν : b | p}) .
  apply sep_env_pure.
Qed.

Lemma sep_proof_proc_ret :
  forall (θ : subst_t var var) S Γ w, 
    θ ν = ν -> (forall x, θ x = ν -> x = ν) ->
    wf_schema S ->
    wf_type (subst θ (s_ret S) :: Γ) (subst θ (snd (s_ret S)))  ->
   (((subst θ (sep_ty (fst (s_ret S)) (snd (s_ret S)))) * sep_env Γ)%pred w)  ->
    (sep_env ((subst θ (s_ret S)) :: Γ) w).
Proof.
  intros θ S Γ w vvid vvim wfschema wf H.
  destruct S as [xs arity [x [ vv b p ]]].
  inversion wfschema. clear H0 H1. simpl in H2. 
  inversion H2.
  inversion H8. subst.
  unfold s_ret.
  apply sep_env_cons_sub; assumption.
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
    modvars (proc_s f xs [x]) x' -> x = x'.
Proof.
  intros.
  inversion H.
  apply in_inv in H4.
  intuition.
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

Lemma sep_proof_proccall :
  forall Φ Γ Γ' f xs v (J : (Φ / Γ ⊢ proc_s f xs [v] ::: Γ')),
    wf_env Γ ->
    sep_proc_env Φ |- {{ sep_env Γ }} proc_s f xs [v] {{ sep_env Γ' }}.
Proof.
  intros. 
  inversion J. 
  apply funspec_interp in H3.
  unfold sep_schema in H3. 
  apply semax_pre_post with 
  (P' := (Subst.subst θ (sep_env (combine (s_formals S) (s_formal_ts S)))) * sep_env Γ) 
  (Q' := (Subst.subst θ (sep_ty (fst (s_ret S)) (snd (s_ret S))))  * sep_env Γ).
  repeat intro. repeat exists a. 
  split. unfold join. constructor; reflexivity.
  split.
  pose subst_in_env.
  specialize (i Γ (combine (s_formals S) (s_formal_ts S)) θ a).
  wfsubst θ.
  apply i.
  assumption.
  assumption.
  rewrite subst_combine.
  apply forall_p_combine.
  inversion H4. repeat rewrite <- subst_length. assumption.
  rewrite <- H8. assumption.
  inversion H4. assumption.
  apply sep_args_sub with (Γ := Γ) (xs := xs) (ts := ts).
  inversion H4. assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  (**  **)
  (* inversion H14. *)
  (* destruct (s_ret S) eqn: sret. *)
  (* unfold subst, Subst_prod, subst_prod in H18. inversion H18. *)
  (* rewrite <- H25 in *. *)
  (* rewrite <- H26 in *. *)
  (** **)
  unfold derives.
  intro w.
  apply sep_proof_proc_ret.
  apply wf_subst_split; assumption.
  apply wf_subst_split; assumption.
  assumption.
  wfenv_ty_t.
  apply semax_frame.
  subst.
  destruct S as [ xs ts [x t]].
  simpl in *.
  assert (A : subst θ (proc_s f xs [x]) = proc_s f (subst θ xs) [subst θ x]).
  unfold subst at 1. simpl. reflexivity.
  rewrite <- A.
  apply semax_subst.
  apply (semax_proc f (mkProc (length xs) xs [x] p)).
  assumption.
  intros.
  assert (x = x0) by
      (apply sep_proof_proc_mod with (f:=f) (xs:= xs); assumption).
  subst.
  apply sep_proof_proc_sub with (v := subst θ x0).
  reflexivity.
  intros.
  constructor.
  intro.
  specialize (H10 x').
  symmetry.
  apply H10.
  assumption.
  intro.
  specialize (H10 x').
  apply H10.
  symmetry.
  assumption.
  unfold subset.
  intros.
  unfold nonfreevars.
  intros.
  rewrite subst_dom_env.
  assumption.
  assumption.
  assert (subst θ (fst (s_ret S)) = x) .
    apply sep_proof_proc_mod with (f:=f) (xs:= (subst θ (s_formals S))). 
    rewrite <- H9. 
    rewrite <- H7.
    assumption.
  apply subst_one_is_disj.
  rewrite <- H9 in H20.
  rewrite H20 in *.
  destruct S as [fxs fts [xr tr]]. simpl in *.
  subst.
  inversion H14. assumption.
  assumption.
  destruct S as [fxs fts [xr tr]]. simpl in *.
  subst.
  inversion H14.
  assumption.
  destruct S as [fx fts [xr tr]]. simpl in *.
  subst.
  unfold subst_one.
  assert (subst θ xr = x) .
   apply sep_proof_proc_mod with (f:=f) (xs:= (subst θ fx)). assumption.
  assert (x <> ν).
  inversion H14. rewrite H0 in H8. assumption.
  destruct (eq_dec ν x).
    intuition.
    reflexivity.
Qed.

Theorem sep_proof_stmt :
  forall Φ Γ Γ' s (J : (Φ / Γ ⊢ s ::: Γ')),
    wf_env Γ ->
    sep_proc_env Φ |- {{ sep_env Γ }} s {{ sep_env Γ' }}.
Proof.
  intros.
  destruct s.
  + apply sep_proof_skip with (Φ := Φ). assumption.
  + apply sep_proof_assign with (Φ := Φ); assumption.
  + inversion J. subst. apply sep_proof_proccall with (Φ := Φ); assumption. 
  + induction J.
    * apply semax_skip.
    * apply sep_proof_proccall.
      apply t_proc_s with (p := p) (ts := ts) (θS := θS); assumption.
      assumption.
    * apply sep_proof_assign with (Φ := Φ). apply t_assign with (φ := φ); assumption. assumption.
    * apply semax_seq with (Q := sep_env Γ'). apply IHJ1. assumption. apply IHJ2. 
      apply wf_env_stmt with (P := Φ) (G := Γ) (s := s0); assumption.
Qed.

Corollary type_safety :
  forall Φ s Γ,
    Φ / nil ⊢ s ::: Γ -> sep_proc_env Φ |- {{ TT }} s {{ TT }}.
Proof.
  intros.
  assert (wf_env nil). constructor.
  apply semax_pre_post with (P' := sep_env nil) (Q' := sep_env Γ);
  first [ constructor | apply sep_proof_stmt with (Φ := Φ); assumption].
Qed.