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

(* Require Import WFLemmas. *)
(* Require Import SubstLemmas. *)
(* Require Import EvalLemmas. *)
(* Require Import Tactics. *)
(* Require Import List. *)
Import ListNotations.

(* Lemma forall_p_combine : *)
(*   forall (X Y : Type) (P : Y -> Prop) (xs : list X) (ys : list Y), *)
(*     length xs = length ys -> *)
(*     Forall P ys ->  *)
(*     Forall (fun xy => P (snd xy)) (combine xs ys). *)
(* Proof. *)
(*   intros. *)
(*   rewrite Forall_forall in *. *)
(*   intros. *)
(*   destruct x as [x y]. *)
(*   simpl in *. *)
(*   pose (combine_split xs ys H). *)
(*   specialize (H0 y). *)
(*   apply in_combine_r in H1. *)
(*   apply H0. *)
(*   assumption. *)
(* Qed. *)

Lemma subst_emp_id :
  forall s,
    subst_pred s emp = emp.
Proof.
  normalize.
Qed.

Hint Resolve subst_emp_id : subst.

Lemma vv_not_fv :
  forall G Gr H e T,
    wf_env H G -> expr_type G H Gr e T -> ~ FV e ν.
Proof.
  intros.
  induction H1; eauto with datatypes.
  + induction Γ.
    contradiction H.
    apply in_inv in H.
    destruct a as [x' [b' p']].
    destruct H. inversion H. subst.
    inversion H0. subst.
    unfold FV.
    unfold fv_expr.
    intro.
    inversion H1. subst x. apply H5. reflexivity. contradiction.
    apply IHΓ. inversion H0. assumption. assumption.
Qed.

Lemma fresh_var_cons :
  forall G H xt x, fresh x (xt :: G) H -> fresh x G H.
Proof. 
  firstorder. 
  unfold var_not_in in *.
  rewrite Forall_forall in *.
  intros.
  apply H1.
  eauto with datatypes.
Qed.
  
Lemma fresh_var_nonmem_env :
  forall G H x, fresh x G H -> var_not_in x G.
Proof.
  firstorder.
Qed.

Lemma fresh_var_nonmem_heap :
  forall G H x, fresh x G H -> bind_not_in x H.
Proof.
  firstorder.
Qed.

Lemma var_not_in_not_eq :
  forall G x x' t, var_not_in x ((x',t) :: G) -> x' <> x.
Proof.
  intros.
  unfold var_not_in in *.
  rewrite Forall_forall in *.
  specialize (H (x',t)).
  apply H.
  left.
  reflexivity.
Qed.

Lemma bind_not_in_not_eq :
  forall H v l x t, bind_not_in v ((l,(x,t)) :: H) -> x <> v.
Proof.
  intros.
  unfold bind_not_in in *.
  rewrite Forall_forall in *.
  specialize (H0 (l,(x,t))).
  apply H0.
  eauto with datatypes.
Qed.

Lemma var_not_in_and_in :
  forall G x, var_not_in x G -> ~ (var_in x G).
Proof.
  unfold var_not_in.
  unfold var_in.
  intros.
  rewrite Forall_forall in *.
  firstorder.
Qed.

Lemma bind_not_in_and_in :
  forall H x, bind_not_in x H <-> ~ (bind_in x H).
Proof.
  intros.
  unfold bind_not_in, bind_in.
  rewrite Forall_forall.
  firstorder.
  intro.
  subst x.
  destruct x0 as [l [x t]].
  apply (H0 l).
  exists t.
  apply H1.
Qed.

Hint Resolve 
     fresh_var_nonmem_env
     fresh_var_nonmem_heap
     var_not_in_not_eq 
     var_not_in_and_in
     bind_not_in_and_in
     fresh_var_cons
     vv_not_fv
: var.

Lemma subst_dist_sepcon :
  forall P Q (s : var -> expr),
    subst_pred s (P * Q) = subst_pred s P * subst_pred s Q.
Proof.
  firstorder.
Qed.

Lemma subst_dist_andp :
  forall P Q (s : var -> expr),
    subst_pred s (P && Q) = subst_pred s P && subst_pred s Q.
Proof.
  firstorder.
Qed.

Lemma subst_dist_orp :
  forall P Q (s : var -> expr),
    subst_pred s (P || Q) = subst_pred s P || subst_pred s Q.
Proof.
  firstorder.
Qed.

Lemma subst_dist_imp :
  forall P Q (s : var -> expr),
    subst_pred s (P --> Q) = subst_pred s P --> subst_pred s Q.
Proof.
  firstorder.
Qed.

Lemma fresh_var_expr_fv :
  forall G H e x, 
    fresh x G H -> wf_expr G H e -> FV e x -> False.
Proof.
  induction e.
  + firstorder.
  + firstorder.
    inversion H1; subst.
    inversion H1; subst. 
      eapply var_not_in_and_in; eauto.
      eapply bind_not_in_and_in; eauto.
      congruence.
      eapply bind_not_in_and_in; eauto.
      congruence.
  + intro x.
    unfold FV in *.
    intros.
    simpl in *.
    apply in_app_or in H2.
    inversion H1; subst.
    destruct H2.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
Qed.

Lemma nonfree_var_expr_eval :
  forall e e' x,
    (FV e x -> False) ->
    forall w,
      (eval (fun i : var => eval w (subst_one x e' i), hp w) e = eval w e).
Proof.
  unfold FV.
  intros.
  induction e.
  + firstorder.
  + simpl. unfold subst_one.
    destruct (eq_dec v x); simpl.
    subst v.
    contradiction H. left. reflexivity.
    reflexivity.
  + simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
    intro. apply H. simpl. apply in_or_app. right. assumption.
    intro. apply H. simpl. apply in_or_app. left. assumption.
Qed.

Lemma fresh_var_nonfree_pred :
  forall G H p x,
    fresh x G H -> wf_prop G H p -> nonfreevars (sep_pred p) x.
Proof.
  intros.
  induction p.
  + firstorder.
  + inversion H1; subst.
    unfold nonfreevars.
    intro e'.
    unfold subst_pred.
    simpl. extensionality w.
    f_equal.
    f_equal.
    repeat rewrite nonfree_var_expr_eval.
    reflexivity.
    eauto using fresh_var_expr_fv.
    eauto using fresh_var_expr_fv.
  + unfold sep_pred; fold sep_pred.
    unfold nonfreevars in *.
    intro e.
    rewrite subst_dist_andp.
    rewrite subst_dist_imp.
    f_equal.
    rewrite <- IHp with (v := e).
    apply  pred_ext.
    apply derives_refl.
    apply derives_refl.
    inversion H1; auto.
  + unfold sep_pred; fold sep_pred.
    unfold nonfreevars in *.
    intro e.
    inversion H1.
    repeat rewrite subst_dist_andp.
    repeat f_equal.
    auto.
    auto.
  + unfold sep_pred; fold sep_pred.
    unfold nonfreevars in *.
    intro e.
    inversion H1.
    repeat rewrite subst_dist_andp.
    repeat rewrite subst_dist_orp.
    repeat f_equal.
    auto.
    auto.
Qed.

Hint Constructors wf_expr : wf.
Hint Constructors wf_prop : wf.

Lemma wf_expr_cons :
  forall G H xt e,
    wf_expr G H e -> wf_expr (xt :: G) H e.
Proof.
  intros.
  induction e. 
  + constructor.
  + inversion H0; subst; eauto with datatypes wf.
      unfold var_in in *;
    destruct H4; constructor; exists x; eauto with datatypes wf.
  + inversion H0; subst; eauto with wf datatypes.
Qed.

Hint Resolve wf_expr_cons : wf.

Lemma wf_prop_cons :
  forall G H xt p,
    wf_prop G H p -> wf_prop (xt :: G) H p.
Proof.
  intros.
  induction p; inversion H0; eauto with wf.
Qed.

Hint Transparent wf_type.
Hint Resolve wf_prop_cons : wf.
Hint Constructors wf_env : wf.

Lemma wf_type_cons :
  forall G H xt b p ,
    wf_type G H { ν : b | p } -> wf_type (xt :: G) H { ν : b | p }.
Proof.
  intros.
  unfold wf_type in *.
  simpl in *.
  destruct b; eauto with wf.
  destruct H0.
  split; eauto with wf.
Qed.

Hint Resolve wf_type_cons : wf.
Hint Constructors reft_type.
    
Lemma wf_ty_mem :
  forall G H x b p,
    (x, { ν : b | p }) ∈ G ->
    wf_env H G ->
    wf_type G H { ν : b | p }.
Proof.
  intros.
  induction G as [ | [x' [b' p']]]; subst.
    + contradiction.
    + apply in_inv in H0. destruct H0. inversion H0. subst.
      inversion H1; subst.
      assumption.
      inversion H1. subst. eauto with wf.
Qed.

Hint Resolve wf_ty_mem : wf.

Lemma wf_prop_from_ty :
  forall G H b p,
    wf_type G H { ν : b | p } -> wf_prop G H p.
Proof.
  intros.
  destruct b; apply H0.
Qed.

Hint Resolve wf_prop_from_ty : wf.

Ltac split_subst_var :=
  match goal with 
    | |- appcontext[_ (subst_one ?x _) (var_e ?v)] =>
      unfold subst; unfold subst_one; simpl;
      destruct (eq_dec v x); subst
  end.

Lemma subst_expr_fun :
  forall (s : var -> expr) f e1 e2,
    subst s (fun_e f e1 e2) = fun_e f (subst s e1) (subst s e2).
Proof.
  firstorder.
Qed.

Lemma subst_prop_rel :
  forall (s : var -> expr) e1 e2,
    subst s (eq_r e1 e2) = eq_r (subst s e1) (subst s e2).
Proof. firstorder. Qed.

Lemma subst_prop_not :
  forall (s : var -> expr) p,
    subst s (not_r p) = not_r (subst s p).
Proof.
  firstorder.
Qed.

Lemma subst_prop_and :
  forall (s : var -> expr) p1 p2,
    subst s (and_r p1 p2) = and_r (subst s p1) (subst s p2).
Proof.
  firstorder.
Qed.

Lemma subst_prop_or :
  forall (s : var -> expr) p1 p2,
    subst s (or_r p1 p2) = or_r (subst s p1) (subst s p2).
Proof.
  firstorder.
Qed.

Lemma wf_prop_not :
  forall G H p, wf_prop G H p -> wf_prop G H (not_r p).
Proof. firstorder. Qed.

Lemma wf_prop_and :
  forall G H p1 p2, 
    wf_prop G H p1 -> wf_prop G H p2 -> wf_prop G H (and_r p1 p2).
Proof. firstorder. Qed.

Lemma wf_prop_or :
  forall G H p1 p2, 
    wf_prop G H p1 -> wf_prop G H p2 -> wf_prop G H (or_r p1 p2).
Proof. firstorder. Qed.

Hint Rewrite 
     subst_prop_rel subst_expr_fun subst_prop_and subst_prop_or subst_prop_not 
: wf.
Hint Resolve 
     subst_prop_rel subst_expr_fun subst_prop_and subst_prop_or subst_prop_not 
     wf_prop_and wf_prop_or wf_prop_not 
: wf.

Lemma wf_subst_vv_expr :
  forall G H e e',
    wf_expr G H e -> wf_expr G H e' ->
    wf_expr G H (subst (subst_one ν e') e).
Proof.
  intros.
  induction e.
  + eauto with wf.
  + inversion H0; split_subst_var; eauto with wf.
  + inversion H0; rewrite subst_expr_fun; eauto with wf.
Qed.

Lemma wf_expr_mem :
  forall G H x b e1 e2, 
    wf_env H G ->
    (x, { ν : b | e1 .= e2 }) ∈ G ->
    wf_expr G H e1.
Proof.
  intros.
  assert (wf_type G H { ν : b | e1 .= e2 }) by eauto with wf.
  inversion H2. inversion H6. eauto.
Qed.

Lemma wf_expr_swap :
  forall G H e1 e2,
    wf_prop G H (e1 .= e2) -> wf_prop G H (e2 .= e1).
Proof.
  intros.
  inversion H0; eauto with wf.
  Grab Existential Variables.
  exact int_t.
Qed.

Hint Resolve wf_subst_vv_expr wf_expr_mem wf_expr_swap : wf.

Lemma wf_subst_vv_pred :
  forall G H p e,
    wf_env H G ->
    wf_expr G H e ->
    wf_prop G H p -> 
    wf_prop G H (subst (subst_one ν e) p).
Proof.
  intros.
  induction p; inversion H2; autorewrite with wf; eauto with wf.
Qed.
  
Hint Resolve wf_subst_vv_pred : wf.

Lemma var_nonmem_free_ctx :
  forall G H x, fresh x G H -> wf_env H G -> nonfreevars (sep_env G) x.
Proof.
  intros G H x fr wf.
  induction G as [| (x',t')].
  + unfold nonfreevars. normalize.
  + destruct t' as [b p]. 
    assert (x' <> x).
      apply var_not_in_not_eq with (G := G) (t := { ν : b | p }). 
      apply fr.
    unfold nonfreevars in *. 
    intros.
    unfold sep_env; fold sep_env.
    repeat rewrite subst_dist_andp.
    f_equal.
    f_equal.
    unfold sep_ty. 
    repeat rewrite subst_dist_andp.
    repeat f_equal.
    unfold sep_base, subst_pred, subst_one.
    destruct b; unfold eval_to; simpl; extensionality; repeat f_equal; try extensionality;
      try match goal with
          | |- appcontext[eq_dec ?x ?y] => destruct (eq_dec x y); (contradiction || reflexivity)
          end.
    assert (x' <> v0).
      eapply var_not_in_not_eq. 
    inversion wf. subst.
    inversion H7. subst.
    rewrite <- fresh_var_nonfree_pred. reflexivity.
    eauto.
    apply wf_subst_vv_pred. assumption. 
    constructor. exists ({ ν : b | p }). left. reflexivity. (* Should automate this *)
    assumption.
    apply IHG; inversion wf; eauto with var wf.
Qed.

Lemma wf_heap_loc_fresh :
  forall G H n x t, 
    wf_heap G ((L n, (x, t)) :: H) ((L n, (x, t)) :: H) ->
    fresh (V n) G H.
Proof.
  intros.
  inversion H0. subst.
  unfold fresh_loc in *.
  apply H8.
Qed.

Hint Resolve wf_heap_loc_fresh : var wf.

Lemma wf_heap_loc_not_in :
  forall G H n x t, 
    wf_heap G ((L n, (x, t)) :: H) ((L n, (x, t)) :: H) ->
    var_not_in (V n) G.
Proof.
  eauto with var wf.
Qed.
Hint Resolve wf_heap_loc_not_in : var wf.

Lemma var_nonmem_free_heap :
  forall G H x, fresh x G H -> wf_heap G H H -> nonfreevars (sep_heap H) x.
Proof.
  intros.
  induction H as [| [l [x' [b p]]]].
  + unfold nonfreevars. normalize.
  + assert (x' <> x).
      eapply bind_not_in_not_eq. apply H0.
    unfold nonfreevars in *.
    intros.
    unfold sep_heap; fold sep_heap.
    destruct l eqn: Loc.
    rewrite subst_dist_sepcon.
    rewrite subst_dist_orp.
    f_equal.
    f_equal.
    unfold eval_to. simpl. 
    extensionality.
    unfold subst_pred.
    f_equal.
    assert (fresh (V n) G H) by eauto with var.
    assert (bind_not_in x ((L n, (x', { ν : b | p})) :: H)) by eauto with var wf.
    unfold subst_one; simpl; destruct (eq_dec (V n) x).
    exfalso. apply 
    (* inversion H1. *)
    (* unfold fresh_loc in *. *)
    (* unfold fresh in H0. *)
    (* unfold bind_not_in in H0. *)
    (* simpl. unfold subst_one. simpl. *)
    destruct (eq_dec (V n) x).
Admitted.
Lemma var_nonmem_free_grd :
  forall G H g x, 
    fresh x G H -> wf_env H G -> wf_guards G H g -> 
    nonfreevars (sep_guards g) x.
Proof.
  intros.
  induction g as [| g'].
  + unfold nonfreevars. normalize.
  + unfold sep_guards; fold sep_guards.
    unfold nonfreevars. 
    intros.
    repeat rewrite subst_dist_andp.
    repeat f_equal.
    rewrite <- fresh_var_nonfree_pred.
      reflexivity. eauto. inversion H2. unfold wf_guard in H5.
      apply H5.
      apply IHg. inversion H2. auto.
Qed.

Lemma var_val :
  forall Γ x b φ, 
    (x,{ ν : b | φ}) ∈ Γ ->
    sep_env Γ |-- (EX v : (base_of_type b),
                          (fun s => !!(eval s (var_e x) = val_of_base b v))).
Proof.
  induction Γ. 
  intuition.
  intuition.
  destruct H.
  + apply andp_left1. 
    apply andp_left1.
    apply andp_left1.
    destruct b.
    inversion H. subst. 
    apply andp_left1.
    apply exp_left.
    intro bb.
    apply andp_left1.
    apply (exp_right bb).
    apply derives_refl.
  + apply andp_left1.
    apply andp_left2.
    fold sep_env.
    apply IHΓ with (φ := φ).
    assumption.
Qed.

Lemma var_eval :
  forall Γ x b φ, 
    (x, { ν : b | φ }) ∈ Γ -> 
    sep_env Γ |-- (EX v : value, (fun s => !!(eval s (var_e x) = v))).
Proof.
  intros.
  pose (var_val Γ x b φ H).
  apply derives_trans with (Q := EX x0 : base_of_type b, (fun s => !!(eval s (var_e x) = val_of_base b x0))).
  assumption.
  apply exp_left.
  intro xv.
  simpl.
  intro w.
  apply prop_left.
  intro.
  rewrite H0.
  simpl in xv.
  apply (exp_right (val_of_base b xv)).
  apply prop_right.
  reflexivity.
Qed.

Lemma expr_eval :
  forall Γ Σ Ξ e b φ,
    expr_type Γ Σ Ξ e { ν : b | φ } ->
    sep_env Γ |-- (EX v : value, (fun s => !!(eval s e = v))).
Proof.
  intros.
  induction H.
  * apply (exp_right v). simpl. intro. apply prop_right. reflexivity.
  * apply var_eval with (Γ := Γ) (b := τ) (φ := φ0); assumption.
  * apply IHexpr_type. 
Qed.

Lemma expr_eval_ty' :
  forall Γ Σ Ξ e T,
    expr_type Γ Σ Ξ e T ->
    sep_env Γ |-- sep_base e (reft_base T).
Proof.
  intros.
  unfold sep_base.
  rewrite <- exp_andp1.
  apply andp_right.
  2: apply sep_env_pure.
  dependent induction H;
    match goal with
      | v : value |- appcontext[EX _ : _, _] => 
        destruct v;
          match goal with
            | z : _ |- _ => apply (exp_right z)
            | _ => apply (exp_right tt)
          end;
          simpl; intro; normalize
      | v : var |- _ => eapply var_val; eauto
      | H : subtype _ _ _ _ |- _ =>
        inversion H; subst; assumption
    end.
Qed.

Lemma expr_eval_ty :
  forall Γ Σ Ξ e b φ,
    expr_type Γ Σ Ξ e { ν : b | φ } ->
    sep_env Γ |-- 
      (EX v : base_of_type b , (fun s => !!(eval s e = val_of_base b v))).
Proof.
  intros.
  apply derives_trans with
    (Q := sep_base e (reft_base { ν : b | φ })).
  eapply expr_eval_ty'; eauto.
  unfold sep_base. 
  rewrite <- exp_andp1. apply andp_left1. normalize.
Qed.

Lemma exfalso_etype_fun :
  forall G Σ Ξ f e1 e2 T,
    expr_type G Σ Ξ (fun_e f e1 e2) T -> False.
Proof.
  intros.
  dependent induction H.
  auto.
Qed.

Hint Resolve 
     expr_eval_ty
     exfalso_etype_fun
     expr_eval_ty'
     expr_eval
     var_val
     var_eval
: eval.

Lemma subst_ty_base_pred :
  forall v s b p,
    subst_pred s (sep_ty (var_e v) { ν : b | p }) =
    subst_pred s (sep_base (var_e v) b && sep_pred (subst (subst_one ν (var_e v)) p) && emp).
Proof.
  firstorder.
Qed.

Lemma subst_convert_expr :
  forall v w e e',
   ~ (FV e v) ->
   eval w (subst (subst_one v e') e) =
   eval (λ i : var, eval w (if eq_dec i v then e' else var_e i), hp w) e.
Proof.
  induction e; intros; auto.
  unfold subst_expr. fold subst_expr.
  rewrite subst_expr_fun. unfold subst. simpl.
  unfold FV in H.
  simpl in H.
  rewrite IHe2; try rewrite IHe1; (reflexivity || eauto with datatypes).
Qed.

Lemma subst_help:
  forall v e e' w,
    ~ FV e v ->
    (eval w e = eval (λ i : var, eval w (if eq_dec i v then e' else var_e i), hp w) e).
Proof.
  induction e.
  + auto.
  + intros.
    simpl. destruct (eq_dec v0 v). subst v0. contradiction H.
    unfold FV in *.
    simpl in *.
    eauto.
    reflexivity.
  + intros.
    simpl.
    unfold FV in H. simpl in H.
    rewrite <- IHe1.
    rewrite <- IHe2.
    reflexivity.
    eauto with datatypes.
    eauto with datatypes.
Qed.

Lemma subst_expr_non_fv :
  forall v e e',
    ~ FV e v -> subst (subst_one v e') e = e.
Proof.
  induction e; intros; eauto with var.
  + simpl. unfold subst_one. 
    unfold subst. unfold Subst_var_expr. simpl.
    destruct (eq_dec v0 v).
    subst v0.
    contradiction H. unfold FV. simpl. eauto with datatypes.
    reflexivity.
  + rewrite subst_expr_fun.
    unfold FV in H.
    simpl in H.
    Hint Transparent FV.
    rewrite IHe1. rewrite IHe2.
    reflexivity.
    eauto with datatypes.
    eauto with datatypes.
Qed.

Lemma subst_assign_eq_true :
  forall v b e,
    ~ (FV e ν) ->
    ~ (FV e v) ->
    sep_base e b
             |-- subst_pred (subst_one v e) (sep_ty (var_e v) {ν : b | var_e ν .= e}).
Proof.
  intros.
  rewrite subst_ty_base_pred.
  repeat rewrite subst_dist_andp.
  repeat apply andp_right. 
    unfold subst_one, subst_pred.
    unfold sep_base. simpl.
    intro w. apply exp_left. intro bt.
    apply exp_right with (x := bt).
    destruct (eq_dec v v). apply derives_refl. congruence.
  rewrite subst_prop_rel.
  rewrite subst_expr_non_fv with (e := e).
  unfold subst, Subst_var_expr, subst_one. simpl.
  unfold subst_pred.
  destruct (eq_dec ν ν). 
  simpl.
  destruct (eq_dec v v).
  intro w.
  rewrite subst_help with (v := v) (e' := e).
  normalize.
  apply sep_base_pure.
  assumption.
  congruence.
  congruence.
  assumption.
  apply sep_base_pure.
Qed.

Lemma expr_type_wf :
  forall G H Grds e T,
    expr_type G H Grds e T -> wf_expr G H e.
Proof.
  intros.
  induction H0.
  + constructor.
  + constructor. exists {ν : τ | φ}. eauto.
  + apply IHexpr_type.
Qed.

Ltac nfv_env := 
  match goal with
    | H : nonfreevars _ ?v |- appcontext[subst_one ?v _] =>
      unfold nonfreevars in H; erewrite <- H; simpl; eauto using andp_left1, andp_left2, derives_refl
    | |- _ |-- subst_pred (subst_one ?v _) ?P =>
      assert (nonfreevars P v); eauto using var_nonmem_free_ctx, var_nonmem_free_grd; nfv_env
  end.

Lemma sep_proof_assign :
  forall Φ Ξ Γ Σ τ v e,
    wf_env Σ Γ ->
    wf_heap Γ Σ Σ ->
    wf_guards Γ Σ Ξ ->
    stmt_type Φ Γ Σ Ξ (assign_s v e) ((v, {ν : τ | (var_e ν) .= e})::Γ) Σ ->
    semax (sep_proc_env Φ) 
          (sep_env Γ && sep_guards Ξ * sep_heap Σ) 
          (assign_s v e) 
          (sep_env ((v, {ν : τ | (var_e ν) .= e})::Γ) && sep_guards Ξ * sep_heap Σ).
Proof.
  intros.
  match goal with
    | H : stmt_type _ _ _ _ ?s _ _ |- semax _ _ ?s _ => inversion H; subst
  end.
  apply semax_frame.
  apply semax_pre_post with
     (P' := (EX v : value, eval_to e v)
              && subst_pred (subst_one v e) (sep_env ((v, {ν : τ | (var_e ν) .= e}) :: Γ) && sep_guards Ξ))
     (Q' := (sep_env ((v, {ν : τ | (var_e ν) .= e}) :: Γ) && sep_guards Ξ)).
  unfold sep_env at 2; fold sep_env.
  normalize.
  rewrite <- exp_andp1.
  apply andp_right.
  apply andp_left1.
  eapply derives_trans.
  eapply expr_eval_ty' with (T := { ν : τ | φ}); eauto.
  unfold sep_base.
  simpl. normalize. intros. apply exp_right with (val_of_base τ x0). unfold eval_to. normalize.
  repeat rewrite subst_dist_andp.
  repeat apply andp_right.
  apply derives_trans with (Q := sep_base e τ).
  apply andp_left1.
  eapply expr_eval_ty' with (T := { ν : τ | φ }); eauto.
  apply subst_assign_eq_true.
  eapply vv_not_fv; eauto.
  intro; eapply fresh_var_expr_fv; eauto.
  eapply expr_type_wf; eauto.
  nfv_env.
  rewrite subst_emp_id; apply andp_left1; apply sep_env_pure.
  nfv_env.
  normalize.
  rewrite exp_andp1; apply semax_assign.
  unfold subset. intros. inversion H3. subst x.
  eapply var_nonmem_free_heap; eauto.
Qed.
  


Lemma sep_proof_stmt :
  forall Φ Ξ Γ Γ' Σ Σ' s,
    wf_env Σ Γ ->
    wf_heap Γ Σ Σ ->
    wf_guards Γ Σ Ξ ->
    stmt_type Φ Γ Σ Ξ s Γ' Σ' ->
    sep_proc_env Φ |- {{ sep_env Γ && sep_guards Ξ * sep_heap Σ }} s {{ sep_env Γ' && sep_guards Ξ * sep_heap Σ' }}.
Proof.
  intros until s.
  intros wf wf_h wf_g H. induction H.
  + (** Skip **) admit.
  + (** f(x) **) admit.
  + (** pad **) admit.
  + eapply sep_proof_assign; eauto. 
    eapply t_assign; eauto.
  + (** alloc **) admit.
  + (** if-then-else **) admit.
  + (** s1;s2 **) admit.
Qed.
  
(*   intros. *)
(*   rewrite <- sepcon_pure_andp. *)
(*   rewrite <- sepcon_pure_andp. *)
(*   dependent induction J. *)
(*   + apply sep_proof_skip with (Φ := Φ) (Ξ := Ξ). constructor. *)
(*   + apply sep_proof_proccall with (Φ := Φ) (Ξ := Ξ). *)
(*     econstructor; eauto. *)
(*     assumption. *)
(*     assumption. *)
(*   + apply sep_proof_assign with (Φ := Φ) (Ξ := Ξ).  *)
(*     econstructor; eauto. *)
(*     assumption. *)
(*     assumption. *)
(*   + repeat rewrite sepcon_pure_andp. *)
(*     apply sep_proof_if with Γ1 Γ2 { ν : int_t | p }; assumption. *)
(*     purity. *)
(*     purity. *)
(*     purity. *)
(*     purity. *)
(*   + apply semax_seq with (Q := sep_env Γ' * sep_guards Ξ). *)
(*     apply IHJ1; assumption. *)
(*     apply IHJ2.  *)
(*     apply wf_env_stmt with (P := Φ) (G := Γ) (X := Ξ) (s := s1); assumption. *)
(*     apply wf_guards_stmt with (P := Φ) (G := Γ) (X := Ξ) (s := s1); assumption. *)
(*  + apply sep_env_pure. *)
(*  + apply sep_guard_pure. *)
(*  + apply sep_env_pure. *)
(*  + apply sep_guard_pure. *)
(* Qed. *)

(* Corollary type_safety_stmt : *)
(*   forall Φ Γ s, (Φ ; [] ; []) ⊢ s ::: Γ -> sep_proc_env Φ |- {{ emp }} s {{ TT }}. *)
(* Proof. *)
(*   intros. *)
(*   assert (wf_env nil). constructor. *)
(*   assert (wf_guards nil nil). constructor. *)
(*   apply semax_pre_post with (P' := sep_env nil && sep_guards nil)  *)
(*                             (Q' := sep_env Γ && sep_guards nil); *)
(*   first [ apply sep_proof_stmt with (Φ := Φ) (Ξ := []); assumption *)
(*         | unfold sep_guards; normalize ]. *)
(* Qed. *)

Theorem sep_proof_program :
  forall Φ p,
    prog_type Φ p -> semax_prog (sep_proc_env Φ) p.
Proof.
  Admitted.
(*   intros Φ p H. *)
(*   induction H. *)
(*   + constructor. *)
(*     apply type_safety_stmt with Γ; assumption. *)
(*   + assert (WFΓ : wf_env Γ). *)
(*       inversion H. *)
(*       pose (wf_env_stmt _ _ Γ _ body H9 H5). *)
(*       apply w. *)
(*     destruct pr.  *)
(*     simpl in *. *)
(*     subst. *)
(*     pose (@semax_procdecl_p (sep_proc_env Φ) *)
(*                            e *)
(*                            body *)
(*                            (sep_schema p (seq_s body (return_s e)) S) *)
(*                            prog) as P. *)
(*     unfold sep_schema in P. *)
(*     destruct S. *)
(*     destruct s_ret. *)
(*     simpl in *. *)
(*     simpl in *. *)
(*     apply P. *)
(*     reflexivity. *)
(*     apply funspec_nomem. *)
(*     assumption. *)
(*     simpl in *. *)
(*     apply semax_pre_post with (P' := sep_env (combine s_formals s_formal_ts) && sep_guards []) *)
(*                               (Q' := sep_env Γ && sep_guards []). *)
(*     apply andp_right.  *)
(*       apply derives_refl.  *)
(*       unfold sep_guards. apply andp_right. normalize. purity. *)
(*     destruct r as [ τ φ ]. *)
(*     apply derives_trans with (Q := sep_ty (subst (subst_one v e) (var_e v))  *)
(*                                          (subst (subst_one v e) {ν : τ | φ})). *)
(*     unfold subst, Subst_var_expr, subst_one at 1, Language.subst_expr. *)
(*     destruct (eq_dec v v). *)
(*     apply type_interp. *)
(*     inversion H. *)
(*     apply wf_env_no_vv.  *)
(*     apply WFΓ. *)
(*     assumption. *)
(*     constructor. *)
(*     intuition. *)
(*     intro. *)
(*     rewrite subst_ty_distr. apply derives_refl. *)
(*     inversion H. *)
(*     clear P. clear H1. *)
(*     inversion H3. *)
(*     unfold subst_one. *)
(*     destruct (eq_dec ν v). intuition. subst. reflexivity. *)
(*     assert (NEQ : v <> ν). *)
(*     inversion H. *)
(*     inversion H3. assumption. *)
(*     apply subst_vv_not_in_range_exp. *)
(*     apply wf_expr_ty_expr_fv with (Γ := Γ) (Ξ := []) (T := subst (subst_one v e) { ν : τ | φ }). *)
(*     apply WFΓ. *)
(*     assumption. *)
(*     apply sep_proof_stmt in H5. *)
(*     apply H5. *)
(*     inversion H. *)
(*     apply H2. *)
(*     constructor. *)
(*     apply IHprog_type. *)
(* Qed. *)
