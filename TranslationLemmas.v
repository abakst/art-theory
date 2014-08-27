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
    forall w,
      sep_ty x T w -> 
      subst (fun i => if eq_dec i ν then x' else i) (sep_ty x T) w.
Proof.
  intros.
  unfold subst.
  unfold sep_ty.
  destruct T as [b p].
  simpl in *.
  split.
  destruct H0.
  unfold sep_base in *.
  destruct H0.
  exists x0.
  simpl.
  destruct (eq_dec x ν). intuition. apply H0.
  destruct H0.
  clear H0.
  rewrite sub_eq in *.
  simpl.
  rewrite <- subst_ty_prop in *.
  unfold subst, Subst_pred_var, subst_pred_var in *.
  simpl in *.
  assert
     ((λ i : var, w (if eq_dec i ν then x else i))
      = (λ i : var,
               w
                 (if eq_dec (if eq_dec i ν then x else i) ν
                  then x'
                  else if eq_dec i ν then x else i))).
  extensionality i.
  destruct (eq_dec i ν). destruct (eq_dec x ν). intuition. reflexivity.
  destruct (eq_dec i ν). intuition. reflexivity.
  rewrite <- H0.
  assumption.
Qed.
 
Lemma vv_sub_env :
  forall G,  
    var_not_in ν G -> 
    forall w,
      sep_env G w ->
      (forall x,
        subst (fun i => if eq_dec i ν then x else i) (sep_env G) w).
Proof.
  intro G.
  induction G.
  + simpl. constructor.
  + destruct a as [b p].
    unfold sep_env in *.
    fold sep_env in *.
    split.
    destruct H0.
    apply subst_vv_ty.
    unfold var_not_in in H.
    rewrite Forall_forall in H.
    apply H with (x := (b, p)).
    left. reflexivity.
    assumption.
    apply IHG.
    unfold var_not_in in *.
    inversion H.
    apply H4.
    apply H0.
Qed.

Lemma vv_sub_guards :
  forall G Grds,
    wf_guards G Grds -> 
    forall w,
      sep_guards Grds w ->
      (forall (x : var),
         subst (fun i => if eq_dec i ν then x else i) (sep_guards Grds) w).
Proof.
  intros G Grds.
  induction Grds as [| p].
  + simpl. constructor.
  + intros wf w sg x.
    unfold sep_guards in *. fold sep_guards in *.
    inversion wf.
    pose (wf_guards_vv_nonfree G Grds H2 w (var_e x)).
    assert (EQ : (fun i => eval w (if eq_dec i ν then var_e x else var_e i))
                   = (fun i => eval w (var_e (if eq_dec i ν then x else i)))).
      extensionality i.
      destruct (eq_dec i ν). reflexivity. reflexivity.
    split.
    rewrite <- EQ.
    apply subst_nonfree_prop.
    apply H1.
    apply sg.
    rewrite <- EQ.
    apply s.
    apply sg.
Qed.

Lemma subtype_interp_pred :
  forall Γ Ξ φ φ' x b,
    var_not_in ν Γ ->
    wf_guards Γ Ξ -> 
    subtype Γ Ξ { ν : b | φ } { ν : b | φ' } -> 
    (sep_env Γ && sep_guards Ξ) |-- 
      sep_pred (subst (subst_one ν (var_e x)) φ) --> 
      sep_pred (subst (subst_one ν (var_e x)) φ').
Proof.
  unfold derives, imp in *.
  intros.
  inversion H1. subst.
  unfold derives, imp in *.
  rewrite sub_eq.
  rewrite <- subst_ty_prop.
  unfold subst.
  unfold Subst_pred_var.
  unfold subst_pred_var.
  apply H7.
  split.
  apply vv_sub_env.
  assumption.
  solve [apply H2].
  rewrite sub_eq in H3.
  rewrite <- subst_ty_prop in H3.
  fold (Subst_pred (subst_one ν (var_e x)) (sep_guards Ξ) a).
  assert (P : nonfreevars (sep_guards Ξ) ν).
    apply wf_guards_vv_nonfree with Γ. assumption.
    unfold nonfreevars in P.
  specialize (P a (var_e x)).
  fold Subst_pred in P.
  fold subst in P.
  apply vv_sub_guards with (G := Γ).
  assumption.
  apply H2.
  rewrite sub_eq in H3.
  rewrite <- subst_ty_prop in H3.
  apply H3.
Qed.

Lemma subtype_interp :
  forall Γ Ξ φ φ' x b,
    var_not_in ν Γ ->
    wf_guards Γ Ξ ->
    subtype Γ Ξ { ν : b | φ } { ν : b | φ' } -> 
      sep_env Γ && sep_guards Ξ |-- sep_ty x { ν : b | φ } --> sep_ty x { ν : b | φ' }.
Proof.
  intros.
  unfold sep_ty.
  simpl.
  rewrite <- imp_andp_adjoint.
  apply andp_right.
  apply andp_left2. apply andp_left1. intuition.
  apply modus_ponens with (P := sep_pred (subst (subst_one ν (var_e x)) φ)).
  apply andp_left2. apply andp_left2. intuition.
  apply andp_left1. apply subtype_interp_pred with (b := b).
  assumption.
  assumption.
  assumption.
Qed.

Lemma vv_sub_env_eval :
  forall e ν x v w,
    x <> ν -> 
    eval w (subst (subst_one ν (var_e x)) e)
    = eval (λ i : var, eval w (subst_one ν v i)) (subst (subst_one ν (var_e x)) e).
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
             (λ i : var, eval w (subst_one ν v i)).
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
  forall T x v w,
    x <> ν ->
    sep_ty x T w -> 
    subst (subst_one ν v) (sep_ty x T) w.
Proof.
  intros.
  unfold subst.
  unfold sep_ty in *.
  destruct T as [b p].
  split.
  destruct H0.
  clear H1.
  destruct H0.
  exists x0.
  simpl.
  unfold subst_one.
  destruct (eq_dec x ν). intuition. assumption.
  rewrite <- vv_sub_env_prop with (v:= v).
  apply H0.
  assumption.
Qed.

Lemma subst_vv_env :
  forall Γ,
    var_not_in ν Γ ->
    nonfreevars (sep_env Γ) ν.
Proof.
  intros.
  induction Γ.
  + constructor.
  + unfold sep_env. destruct a as [x [b p]].
    fold sep_env.
    simpl in *.
    split.
    pose (vv_sub_env_ty { ν : b | p } x v).
    unfold sep_ty in s.
    simpl in s.
    unfold subst, Subst_pred, subst_pred in s.
    unfold subst.
    apply s.
    unfold var_not_in in H.
    rewrite Forall_forall in H.
    apply H with (x0 := (x, {ν : b | p })).
    left. reflexivity.
    apply H0.
    apply IHΓ.
    unfold var_not_in in H.
    inversion H.
    apply H4.
    apply H0.
Qed.

Lemma sep_env_base_var :
  forall Γ x b p,
    (x, { ν : b | p }) ∈ Γ ->
    sep_env Γ |-- sep_base x b.
Proof.
  induction Γ.
  intros.
  inversion H.
  intros.
  apply in_inv in H.
  destruct a as [x' [b' p']].
  destruct H.
  inversion H.
  subst.
  simpl in *.
  repeat apply andp_left1.
  intuition.
  unfold sep_env.
  fold sep_env.
  apply andp_left2.
  apply IHΓ with (p := p).
  assumption.
Qed.

Lemma type_interp :
  forall Γ Ξ x T,
    var_not_in ν Γ ->
    expr_type Γ Ξ (var_e x) T ->
    wf_guards Γ Ξ -> 
    sep_env Γ && sep_guards Ξ |-- sep_ty x T.
Proof.
  intros Γ Ξ x T vvnotin ET. (* [ ν b φ ]  w SE ET. *)
  unfold sep_ty. 
  dependent induction ET.
  {
    intros wfg.
  simpl in *.
  apply andp_right.
  * apply andp_left1. apply sep_env_base_var with (p := φ).
    assumption.
  * clear wfg.
    apply andp_left1.
    induction Γ.
    + intuition.
    + intros. 
      destruct a as [x' [ b' p' ]].
      apply in_inv in H.
      destruct H.
      inversion H; subst.
      unfold sep_env.
      fold sep_env.
      apply andp_left1.
      unfold sep_ty.
      apply andp_left2.
      solve [intuition].
      unfold sep_env. fold sep_env.
      apply andp_left2.
      apply IHΓ.
      assumption.
      inversion vvnotin. assumption.
  }
  {
    fold (sep_ty x T) in IHET.
    fold (sep_ty x T').
    intro.
    apply modus_ponens with (P := sep_ty x T).
    apply IHET.
    assumption.
    destruct T, T'.
    apply H1.
    inversion H0; subst.
    apply subtype_interp.
    assumption.
    assumption.
    assumption.
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
  + constructor.
  + destruct a. 
    fold sep_env.
    apply andp_right.
    apply type_interp with (Γ := Γ).
    assumption. apply H1 with (x := (v,r)). unfold In. left. reflexivity.
    assumption.
    apply IHl. 
    intro. intro.
    apply H1.
    unfold In. right. apply H2.
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

Lemma sep_guards_pure :
  forall G,
    pure (sep_guards G).
Proof.
  unfold pure.
  unfold identity.
  intros.
  intro.
  intro.
  intros w1 w2.
  intro.
  apply H0.
Qed.


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
  apply semax_pre_post with (P' := EX v : value, (eval_to e v)
                                              && (subst_pred (subst_one x e )
                                                             (sep_env ((x, {ν : τ | (var_e ν) .= e }) :: Γ))))
                            (Q' := sep_env ((x,{ν : τ | (var_e ν) .= e }) :: Γ)).
  intro w. intros SE.
  pose (expr_eval Γ Ξ e τ φ w SE H7) as ValWit. 
  destruct ValWit.
  exists x0. split. apply H.
  apply subst_env_eq_expr with (Grds := Ξ) (φ := φ).
  assumption.
  assumption.
  rewrite subst_dom_env.
  assumption.
  assumption.
  split. unfold subst_one. destruct (eq_dec ν x). subst. contradiction H1. reflexivity. reflexivity.
  intros x' x'_in_ctx.
  unfold subst_one. destruct (eq_dec x' x). subst. 
  unfold var_in in *.
  unfold var_not_in in *. rewrite Forall_forall in H5. destruct (x'_in_ctx). apply H5 in H. 
  contradiction H. reflexivity. reflexivity.
  unfold subst_one. destruct (eq_dec ν x). subst. contradiction H1. reflexivity. reflexivity.
  auto.
  apply semax_assign with (e := e) (x := x) (P := (sep_env ((x, {ν : τ | var_e ν .= e}) :: Γ))).
  unfold subset.
  intros.
  inversion H. subst.
  apply wf_guards_nonfree with (Γ := Γ).
  assumption.
  assumption.
Qed.

Lemma sep_args_sub :
  forall Γ Ξ (xs' : list var) ts' (θ : subst_t var var) xs ts w,
    length xs = length ts ->
    xs' = subst θ xs ->
    ts' = subst θ ts ->
    tc_list Γ Ξ (combine xs' ts') ->
    var_not_in ν Γ -> 
    wf_guards Γ Ξ ->
    sep_env Γ w ->
    sep_guards Ξ w ->
    sep_env (subst θ (combine xs ts)) w.
Proof.
  intros.
  assert (C: subst θ (combine xs ts) =
                      combine xs' ts').
    rewrite H0. rewrite H1.
    rewrite <- subst_combine with (xs := xs) (ys := ts).
    reflexivity.
    assumption.
  rewrite C.
  assert (P : sep_env Γ w /\ sep_guards Ξ w) by (split; assumption).
  fold (@andp world (sep_env Γ) (sep_guards Ξ) w) in P.
  generalize P.
  generalize w.
  fold (@derives world (sep_env Γ && sep_guards Ξ) (sep_env (combine xs ts))).
  apply types_interp.
  assumption. assumption. assumption.
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
  forall (θ : subst_t var var) x t Γ w, 
    θ ν = ν -> (forall x, θ x = ν -> x = ν) ->
    wf_type (subst θ (x,t) :: Γ) (subst θ t)  ->
   (((subst θ (sep_ty x t)) * sep_env Γ)%pred w)  ->
    (sep_env ((subst θ (x,t)) :: Γ) w).
Proof.
  intros θ x t Γ w vvid vvim wf H.
  destruct t as [ b p ].
  simpl in *.
  apply sep_env_cons_sub. 
  assumption.
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
  forall Φ Ξ Γ Γ' f xs v (J : (Φ ; Γ ; Ξ) ⊢ proc_s f xs [v] ::: Γ'),
    wf_env Γ ->
    wf_guards Γ Ξ ->
    sep_proc_env Φ |- {{ sep_env Γ * sep_guards Ξ }} proc_s f xs [v] {{ sep_env Γ' * sep_guards Ξ }}.
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
  (Q' := ((Subst.subst θ (sep_ty rx rt))) * (sep_env Γ * sep_guards Ξ)).
  intro a.
  intro Env.
  repeat exists a. 
  split. unfold join. constructor; reflexivity.
  split.
  pose subst_in_env.
  specialize (i Γ (combine fxs fts) θ a).
  wfsubst θ.
  apply i.
  assumption.
  assumption.
  rewrite subst_combine.
  apply forall_p_combine.
  inversion wfS; repeat rewrite <- subst_length; assumption.
  assumption.
  inversion wfS; assumption.
  apply sep_args_sub with (Ξ := Ξ) (Γ := Γ) (xs' := subst θ fxs) (ts' := subst θ fts).
  inversion wfS; assumption.
  reflexivity.
  reflexivity.
  assumption.
  apply wf_env_no_vv; assumption.
  assumption.
  rewrite sepcon_pure_andp in Env.
  apply Env.
  apply sep_env_pure.
  apply sep_guards_pure.
  rewrite sepcon_pure_andp in Env.
  apply Env.
  apply sep_env_pure.
  apply sep_guards_pure.
  apply Env.
  rewrite <- sepcon_assoc.
  apply sepcon_derives.
  unfold derives.
  intro w.
  intro Env.
  apply sep_proof_proc_ret.
  apply wf_subst_split; assumption.
  apply wf_subst_split; assumption.
  apply wf_env_cons_ty; assumption.
  apply Env.
  firstorder.
  apply semax_frame.
  subst.
  assert (A : subst θ (proc_s f fxs [rx]) = proc_s f (subst θ fxs) [subst θ rx]).
  unfold subst at 1. simpl. reflexivity.
  rewrite <- A.
  apply semax_subst.
  apply (semax_proc f (mkProc (length fxs) fxs [rx] p)).
  assumption.
  intros.
  assert (rx = x) by 
      (apply sep_proof_proc_mod with (f:=f) (xs:= fxs); assumption).
  subst.
  apply sep_proof_proc_sub with (v := subst θ x).
  reflexivity.
  intros.
  constructor.
  intro.
  specialize (retid x').
  symmetry.
  apply retid.
  assumption.
  intro.
  specialize (retid x').
  apply retid.
  symmetry.
  assumption.
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
  rewrite subst_dom_andp.
  rewrite <- sepcon_pure_andp.
  assumption.
  apply sep_env_pure.
  apply sep_guards_pure.
  apply subst_dom_env.
  assumption.
  apply subst_one_is_disj.
  assumption.
  assumption.
  inversion wfenv. rewrite <- A. assumption.
  unfold subst_one. destruct (eq_dec ν x). rewrite e in B. intuition. reflexivity.
  apply subst_dom_guards with (Γ := Γ).
  assumption.
  apply subst_one_is_disj.
  assumption.
  assumption.
  inversion wfenv. rewrite <- A. assumption.
  apply sep_env_pure.
  apply sep_guards_pure.
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
  + 
  + apply semax_seq with (Q := sep_env Γ' * sep_guards Ξ).
    apply IHJ1; assumption.
    apply IHJ2. 
    apply wf_env_stmt with (P := Φ) (G := Γ) (X := Ξ) (s := s1); assumption.
    apply wf_guards_stmt with (P := Φ) (G := Γ) (X := Ξ) (s := s1); assumption.
 + apply sep_env_pure.
 + apply sep_guards_pure.
 + apply sep_env_pure.
 + apply sep_guards_pure.
Qed.

Corollary type_safety :
  forall Φ Γ s,
    (Φ ; nil ; []) ⊢ s ::: Γ -> sep_proc_env Φ |- {{ TT }} s {{ TT }}.
Proof.
  intros.
  assert (wf_env nil). constructor.
  assert (wf_guards nil nil). constructor.
  apply semax_pre_post with (P' := sep_env nil && sep_guards nil) (Q' := sep_env Γ && sep_guards nil);
  first [ constructor | apply sep_proof_stmt with (Φ := Φ) (Ξ := []); assumption].
  constructor.
  constructor.
Qed.