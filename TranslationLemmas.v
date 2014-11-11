Add LoadPath "vst".
Require Import msl.Coqlib2.
Require Import msl.log_normalize.
Require Import msl.eq_dec.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Equality.

Require Import Types. Import HE.
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

Lemma combine_cons :
  forall A B (a:A) (b:B) xs ys,
    combine (a :: xs) (b :: ys) = (a, b) :: combine xs ys.
Proof.
  reflexivity.
Qed.

(* Lemma subst_combine_proj : *)
(*   forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R) *)
(*          (xys : list (A * B)) (θ : subst_t D R), *)
(*     subst θ xys = combine (subst θ (fst (split xys))) (subst θ (snd (split xys))). *)
(* Proof. *)
(*   intros. *)
(*   induction xys. *)
(*   * reflexivity. *)
(*   * destruct a.  *)
(*     rewrite split_fst. *)
(*     rewrite split_snd. *)
(*     unfold subst at 2 3. *)
(*     unfold Subst_list. unfold subst_list. fold subst_list. *)
(*     rewrite combine_cons. *)
(*     unfold subst at 2 3 in IHxys. *)
(*     unfold Subst_list in IHxys. *)
(*     rewrite <- IHxys. *)
(*     reflexivity. *)
(* Qed. *)

Lemma subst_combine :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R)
         (xs : list A) (ys : list B) (θ : subst_t D R),
    length xs = length ys ->
    subst θ (combine xs ys) = combine (subst θ xs) (subst θ ys).
Proof.
  intros until xs.
  induction xs.
  intros. destruct ys.
    reflexivity.
    reflexivity.
  intros. destruct ys.
    inversion H.
    unfold subst at 2 3.
    unfold Subst_list.
    unfold subst_list. fold subst_list.
    rewrite combine_cons.
    rewrite combine_cons. 
    unfold subst at 1.
    unfold subst_list at 1.
    fold subst_list.
    unfold subst at 1.
    unfold Subst_prod at 1. unfold subst_prod.
    inversion H.
    specialize (IHxs ys θ H1).
    unfold subst at 2 3 in IHxs. unfold Subst_list in IHxs.
    rewrite <- IHxs.
    reflexivity.
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

Lemma bind_not_in_cons :
  forall (H : heap_env) (l : loc) xt x',
   ~ In l H ->  bind_not_in x' (add l xt H) -> bind_not_in x' H.
Proof.
  intros.
  assert ((fst xt) <> x').
  intro. subst x'.
  unfold bind_not_in in *.
  specialize (H1 l (snd xt)).
  destruct (eq_dec l l).
  rewrite HE_Props.F.add_eq_o in H1.
  apply H1. destruct xt. reflexivity. reflexivity. 
  congruence.
  
  unfold bind_not_in in *.
  intros l' t'.
  
  specialize (H1 l').
  rewrite HE_Props.F.add_o in H1.
  destruct (HE_Props.F.eq_dec l l').
  
  subst l.
  apply HE_Props.F.not_find_in_iff in H0.
  intro. rewrite H0 in H3. discriminate H3.
  
  apply H1.
Qed.

Lemma fresh_var_cons_hp :
  forall G H l xt x, ~ In l H -> fresh x G (add l xt H) -> fresh x G H.
Proof.
  intros.
  unfold fresh in *.
  decompose [and] H1.
  repeat split; try assumption.
  eapply bind_not_in_cons; eauto.
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
  specialize (H (x',t0)).
  apply H.
  left.
  reflexivity.
Qed.

Lemma bind_not_in_not_eq :
  forall H v l x t, bind_not_in v (add l (x,t) H) -> x <> v.
Proof.
  intros.
  unfold bind_not_in in *.
  specialize (H0 l t0).
  rewrite HE_Props.F.add_eq_o in H0.
  intro.
  subst.
  congruence.
  reflexivity.
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
  firstorder.
Qed.

Lemma bind_in_and_not_in_eq :
  forall x x' H, bind_not_in x' H -> bind_in x H -> x <> x'.
Proof.
  unfold bind_not_in, bind_in.
  intros.
  destruct H1.
  specialize (H0 x0).
  destruct H1.
  specialize (H0 x1).
  congruence.
Qed.
  
Hint Resolve 
     fresh_var_nonmem_env
     fresh_var_nonmem_heap
     var_not_in_not_eq 
     var_not_in_and_in
     bind_not_in_and_in
     bind_in_and_not_in_eq
     fresh_var_cons
     fresh_var_cons_hp
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

Lemma subst_dist_andp_loc :
  forall P Q (s : loc -> loc),
    subst_pred_loc s (P && Q) = subst_pred_loc s P && subst_pred_loc s Q.
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

Ltac push_subst :=
  (repeat (first [ rewrite subst_dist_andp 
                 | rewrite subst_dist_andp_loc
                 | rewrite subst_dist_orp 
                 | rewrite subst_dist_sepcon ])).

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
      apply bind_not_in_and_in in H4. congruence.
      congruence.
      apply bind_not_in_and_in in H4. congruence.
      congruence.
  + firstorder.
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

Hint Transparent stk hp runloc fst snd.

Lemma nonfree_var_expr_eval :
  forall e e' x,
    (FV e x -> False) ->
    forall w,
      (eval (fun i : var => eval w (subst_one x e' i), runloc w, hp w) e = eval w e).
Proof.
  unfold FV.
  intros.
  induction e.
  + firstorder.
  + simpl. unfold subst_one. unfold stk, fst.
    destruct (eq_dec v x); simpl.
    subst v.
    contradiction H. left. reflexivity.
    reflexivity.
  + reflexivity.
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

Hint Resolve fresh_var_nonfree_pred : wf var.
Hint Rewrite fresh_var_nonfree_pred : wf.
Hint Constructors wf_expr wf_prop wf_type wf_env wf_heap : wf.


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
  + inversion H0.
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

Hint Resolve wf_prop_cons : wf.

Lemma wf_type_cons :
  forall G H xt b p ,
    wf_type G H { ν : b | p } -> wf_type (xt :: G) H { ν : b | p }.
Proof.
  intros.
  inversion H0; eauto with wf.
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

Ltac wf_invert :=
  match goal with
    | H: wf_type _ _ { ν : _ | ?p } |- wf_prop _ _ ?p => inversion H; eauto with wf
  end.

Lemma wf_prop_from_ty :
  forall G H b p,
    wf_type G H { ν : b | p } -> wf_prop G H p.
Proof.
  intros; wf_invert.
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
Proof. firstorder. Qed.

Lemma subst_prop_and :
  forall (s : var -> expr) p1 p2,
    subst s (and_r p1 p2) = and_r (subst s p1) (subst s p2).
Proof. firstorder. Qed.

Lemma subst_prop_or :
  forall (s : var -> expr) p1 p2,
    subst s (or_r p1 p2) = or_r (subst s p1) (subst s p2).
Proof. firstorder. Qed.

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
  + inversion H0.
  + inversion H0; rewrite subst_expr_fun; eauto with wf.
Qed.

Lemma wf_expr_mem :
  forall G H e1 e2, 
    wf_prop G H (e1 .= e2) ->
    wf_expr G H e1.
Proof.
  intros.
  inversion H0.
  eauto with wf.
Qed.

Hint Constructors base_type.

Lemma wf_expr_swap :
  forall G H e1 e2,
    wf_prop G H (e1 .= e2) -> wf_prop G H (e2 .= e1).
Proof.
  intros.
  inversion H0; eauto with wf.
  Grab Existential Variables.
  eauto.
Qed.

Hint Resolve wf_subst_vv_expr wf_expr_mem wf_expr_swap : wf.

Lemma wf_subst_vv_pred :
  forall G H p e,
    wf_expr G H e ->
    wf_prop G H p -> 
    wf_prop G H (subst (subst_one ν e) p).
Proof.
  intros.
  induction p; inversion H1; autorewrite with wf; eauto with wf.
Qed.
  
Hint Resolve wf_subst_vv_pred : wf.

Lemma fresh_var_nonfree_ty :
  forall G H t x v,
    x <> v ->
    fresh v G H -> 
    var_in x G \/ bind_in x H -> 
    wf_type G H t -> nonfreevars (sep_ty (var_e x) t) v.
Proof.
  intros.
  unfold nonfreevars.
  intro e.
  unfold sep_ty. 
  destruct t0 as [ b p ].
  push_subst.
  f_equal.
  f_equal.
  + unfold sep_base.
    destruct b;
      push_subst; repeat (extensionality; f_equal); 
      unfold eval_to, subst_one, subst_pred; simpl; unfold stk; simpl;
      destruct (eq_dec x v); try first [contradiction | reflexivity ].
  + erewrite <- fresh_var_nonfree_pred. reflexivity. eauto with wf. apply wf_subst_vv_pred; eauto with wf var.
    match goal with 
      | H: (var_in _ _  \/ bind_in _ _) |- _ =>
        destruct H; eauto with wf
    end.
Qed.

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
    destruct b; unfold eval_to; simpl; repeat (f_equal; extensionality);
    unfold stk; simpl;
      try match goal with
          | |- appcontext[eq_dec ?x ?y] => destruct (eq_dec x y); (contradiction || reflexivity)
          end.
    inversion wf. subst.
    inversion H7. subst.
    rewrite <- fresh_var_nonfree_pred. reflexivity.
    eauto.
    apply wf_subst_vv_pred. 
    constructor. exists ({ ν : b | p }). left. reflexivity. (* Should automate this *)
    assumption.
    apply IHG; inversion wf; eauto with var wf.
Qed.

(* 
Lemma wf_heap_loc_fresh :
  forall G H l x t,
    wf_heap G (add l (x, t) H) (add l (x, t) H) ->
    fresh_loc l G H.
Proof.
  intros.
  inv H0.
  rewrite (@HE_Props.elements_Empty (var * reft_type)) in H1.
  pose (HE_Props.F.elements_mapsto_iff (add l (x, t0) H) l (x, t0)).
  destruct i. 
  rewrite H1 in H0.
  assert (MapsTo l (x, t0) (add l (x, t0) H)).
  apply HE_Props.F.find_mapsto_iff.
  rewrite HE_Props.F.add_eq_o. reflexivity. reflexivity.
  apply H0 in H3.
  inv H3.
  constructor.

  pose (@HE_Props.F.empty_o type_binding l).
  pose (@find (type_binding) l (HE.empty type_binding) = @find type_binding l (add l (x, t0) H)).
  Set Printing All. idtac.
  rewrite e in P.
  unfold fresh_loc in *.
  apply H8.
Qed.

Lemma wf_heap_fresh_trans :
  forall G H H' x,
    wf_heap G H H' -> fresh x G H -> fresh x G H'.
Proof.
  intros until x.
  induction H' as [| [l [x' t']]].
  + firstorder. unfold bind_not_in. eauto with datatypes.
  + intros.
    inv H0.
    destruct (IHH' H12).
    auto.
    unfold fresh.
    destruct H2.
    repeat (split; try assumption). 
    assert (x' <> x).
      eauto with wf var.
    unfold bind_not_in.
    eauto with wf var.
Qed.

Hint Resolve wf_heap_loc_fresh : var wf.
*)

Lemma sep_heap_emp :
  sep_heap (empty type_binding) = emp.
Proof.
  reflexivity.
Qed.
(*
Lemma MapsTo_sepheap :
  forall H l xt,
    InA (eq_key_elt (elt := type_binding)) (l,xt) H -> 
    exists H1 H2,
      (H = H1 ++ (l, xt) :: H2)
      /\ (sep_heap' H |-- sep_heap' H1 * sep_heap_bind l xt * sep_heap' H2).
Proof.
  intros.
  induction H as [| [l' xt']]. 
    * inversion H0.
    * destruct (InA_split H0) as [H' [[l'' xt''] [H'']]]. 
      destruct H1. inv H1. simpl in H3. simpl in H4. subst.
      inv H0.
      inv H3. simpl in H0. simpl in H1. subst.
      exists []. exists H.
      split. reflexivity.
      unfold sep_heap'; fold sep_heap'.
      rewrite sepcon_assoc.
      rewrite sepcon_comm with (P := emp).
      rewrite sepcon_emp.
      apply derives_refl.
      apply IHlist in H3.
      destruct H3 as [H1'].
      destruct H0 as [H1''].
      destruct H0.
      exists ((l',xt') :: H1'). exists H1''.
      split. 
      simpl.
      rewrite H0. reflexivity.
      unfold sep_heap'; fold sep_heap'.
      rewrite sepcon_comm with (Q := sep_heap' H1').
      rewrite sepcon_comm with (Q := sep_heap_bind l'' xt'').
      rewrite sepcon_assoc.
      rewrite sepcon_comm with (Q := sep_heap' H1'').
      rewrite <- sepcon_assoc.
      rewrite <- sepcon_assoc.
      rewrite sepcon_comm with (Q := sep_heap' H).
      apply sepcon_derives.
      rewrite sepcon_comm.
      rewrite <- sepcon_assoc.
      apply H1.
      apply derives_refl.
Qed.

Lemma sep_heap_app :
  forall H1 H2,
    sep_heap' (H1 ++ H2) = sep_heap' H1 * sep_heap' H2.
Proof.
  induction H1 as [| [l xt]]; intros.
  rewrite app_nil_l.
  apply pred_ext.
  rewrite <- sepcon_emp at 1. rewrite sepcon_comm.
  apply derives_refl. 
  rewrite <- sepcon_emp. rewrite sepcon_comm.
  apply derives_refl.
  rewrite <- app_comm_cons.
  unfold sep_heap'; fold sep_heap'.
  rewrite IHlist.
  rewrite sepcon_assoc.
  reflexivity.
Qed.
*)

Definition eqA := eq_key_elt (elt := type_binding).

(*
Lemma In_app_sub :
  forall p p' H H' H'',
    (InA eqA p (p' :: H) ↔ InA eqA p (H' ++ p' :: H''))
    ->
    (eqA p p' \/ (InA eqA p H ↔ InA eqA p (H' ++ H''))).
Proof.
  intros until p'.
  destruct (eq_dec p p').
  subst. left. reflexivity.
  intro H.
  induction H; intros. 
  right.
  destruct H.
  constructor; intro. 
   * inv H1.
   * apply InA_app in H1.
     destruct H1.
     cut (InA eqA p (H' ++ p' :: H'')).
     intro. apply H0 in H2. inv H2. inv H4. destruct p. destruct p'. simpl in H2, H3. subst.
     congruence. assumption.
     apply InA_app_iff.
     apply HE_Props.eqke_equiv.
       left. apply H1.
     cut (InA eqA p (H' ++ p' :: H'')).
     intro. apply H0 in H2. inv H2. inv H4. destruct p. destruct p'. simpl in H2, H3. subst.
     congruence. assumption.
     apply InA_app_iff.
       apply HE_Props.eqke_equiv.
       right.
       apply InA_cons. right. assumption.
       apply HE_Props.eqke_equiv.
  * destruct H0.
    destruct (eq_dec p p').
    left. inv e. reflexivity.
    right.
    constructor; intro.
    + cut (InA eqA p (p' :: a :: H)).
      intro.
      apply H0 in H3.
      apply InA_app_iff. apply HE_Props.eqke_equiv.
      apply InA_app in H3.
      destruct H3. left. assumption.
      inv H3. inv H5. destruct p. destruct p'. simpl in *. subst. congruence.
      right. assumption. apply HE_Props.eqke_equiv.
      apply InA_cons. right. assumption.
    + cut (InA eqA p (H' ++ p' :: H'')).
      intro IN.
      apply H1 in IN. inv IN.
      inv H4. destruct p; destruct p'; simpl in *; subst; congruence.
      assumption.
      apply InA_app_iff. apply HE_Props.eqke_equiv.
      apply InA_app in H2.
      destruct H2. left. assumption. right. apply InA_cons. right. assumption.
      apply HE_Props.eqke_equiv.
Qed.
*)

Lemma EqMapsTo :
  forall H H',
    Equal H H' -> sep_heap H = sep_heap H'.
Proof.
  unfold sep_heap.
  intros.
  apply HE_Props.fold_Equal.
  apply EQ_EQUIVALENCE.
  repeat (hnf; intros; subst).
  reflexivity.
  hnf.
  intros.
  simpl.
  extensionality ρ.
  repeat rewrite <- sepcon_assoc.
  rewrite sepcon_comm with (P := sep_heap_bind k e ρ).
  reflexivity.
  assumption.
Qed.

Lemma sep_heap_maps :
  forall H l xt,
    MapsTo l xt H ->
    MapsTo l (sep_heap_bind l xt)  (mapi (fun l xt => sep_heap_bind l xt) H).
Proof.
  intros.
  apply HE_Props.F.mapi_1bis.
  intros. rewrite H1. reflexivity. assumption.
Qed.

Lemma sep_heap_add :
  forall H l xt,
    ~ In l H -> sep_heap (add l xt H) = sep_heap_bind l xt * sep_heap H.
Proof.
  intros.
  unfold sep_heap.
  set (f := fun l xt a => sep_heap_bind l xt * a).
  assert (eq (fold f (add l xt H) emp) (f l xt (fold f H emp))).
  apply HE_Props.fold_add. apply EQ_EQUIVALENCE.
  solve_proper.
  repeat (hnf; intros; subst). unfold f.
  rewrite sepcon_comm. rewrite sepcon_assoc. rewrite sepcon_comm with (P := a).
  reflexivity.
  assumption.
  apply H1.
Qed.

Lemma sep_heap_Emp :
  forall H, Empty H -> sep_heap H = emp.
Proof.
  intros.
  unfold sep_heap. rewrite HE_Props.fold_Empty. reflexivity. apply EQ_EQUIVALENCE.
  assumption.
Qed.

Lemma fresh_loc_not_In :
  forall l G H, fresh_loc l G H -> ~ In l H.
Proof.
  intros.
  unfold fresh_loc in *.
  decompose [and] H0.
  apply HE_Props.F.not_find_in_iff.
  apply H0.
Qed.

Lemma var_nonmem_free_heap :
  forall G H H' x, fresh x G H -> wf_heap G H H' -> nonfreevars (sep_heap H') x.
Proof.
  intros.
  induction H1.
  + unfold nonfreevars. intro e.
    rewrite sep_heap_Emp; easy. 
  + assert (x0 <> x).
      eauto with wf var.
    unfold nonfreevars in *.
    rewrite sep_heap_add.
    intro e.
    push_subst.
    f_equal.
    unfold sep_heap_bind.
    push_subst.
    f_equal.
    f_equal.
    unfold emapsto, eval_to; simpl.
    unfold subst_pred, subst_one; simpl.
    unfold stk, runloc; simpl.
    destruct (eq_dec x0 x).
    contradiction. reflexivity.
    rewrite <- fresh_var_nonfree_ty; eauto.
    eauto.
    eapply fresh_loc_not_In; eauto.
 Qed.

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

Hint Constructors value.

Lemma var_val :
  forall Γ x b φ, 
    (x,{ ν : b | φ}) ∈ Γ ->
    sep_env Γ |-- (EX v : value,
                          (fun s => !!(eval s (var_e x) =  v))).
Proof.
  induction Γ. 
  intuition.
  intuition.
  destruct H.
  + do 3 apply andp_left1. 
    destruct b.
    inv H.
    apply andp_left1.
    unfold sep_base.
    destruct b0.
      * rewrite exp_andp1; apply exp_left; intros; eapply exp_right.
        apply andp_left1. simpl.
        intro w. unfold eval_to. apply andp_left1. normalize.
      * intro w. simpl. eapply exp_right. normalize. 
      * simpl. intro w. repeat apply andp_left1. eapply exp_right.
        normalize.
  + apply andp_left1. apply andp_left2.
    eauto.
Qed.

Lemma var_eval :
  forall Γ x b φ, 
    (x, { ν : b | φ }) ∈ Γ -> 
    sep_env Γ |-- (EX v : value, (fun s => !!(eval s (var_e x) = v))).
Proof.
  intros.
  eauto using var_val.
Qed.

Lemma expr_eval :
  forall Γ Σ Ξ e b φ,
    expr_type Γ Σ Ξ e { ν : b | φ } ->
    sep_env Γ |-- (EX v : value, eval_to e v).
Proof.
  intros.
  unfold eval_to.
  simpl. intros. rewrite <- exp_andp1.
  apply andp_right.
  2: apply sep_env_pure.
  induction H; eauto using exp_right, var_eval;
  eapply exp_right; simpl; eauto using prop_right.
Qed.

Lemma exfalso_etype_fun :
  forall G Σ Ξ f e1 e2 T,
    expr_type G Σ Ξ (fun_e f e1 e2) T -> False.
Proof.
  intros.
  dependent induction H.
  auto.
Qed.

Ltac evalto_intro v w :=
  apply exp_left; intro v; simpl; normalize; intro w.

Lemma expr_eval_ty' :
  forall Γ Σ Ξ e T,
    expr_type Γ Σ Ξ e T ->
    sep_env Γ |-- sep_base e (reft_base T).
Proof.
  intros.
  unfold sep_base.
  destruct T.
  apply andp_right.
  2: apply sep_env_pure.
  dependent induction H;
    simpl in *.
    intro w.
    apply exp_right with (x := n). unfold eval_to.
    apply andp_right.
    normalize.
    apply sep_env_pure.

    intro w. apply prop_right. reflexivity.

    intro w. induction Γ as [| (x', t')]. contradiction.
      apply in_inv in H. destruct H. inv H. simpl.
      apply andp_left1. apply andp_left1. 
      unfold sep_ty. simpl. apply andp_left1. apply andp_left1.
      unfold sep_base. simpl. apply andp_left1. apply derives_refl.
      unfold sep_env. fold sep_env.
      simpl.
      apply andp_left1. apply andp_left2. apply IHΓ. assumption.

      inv H1. eauto.
Qed.

(* Lemma expr_eval_ty : *)
(*   forall Γ Σ Ξ e b φ, *)
(*     expr_type Γ Σ Ξ e { ν : b | φ } -> *)
(*     sep_env Γ |--  *)
(*       (EX v : base_of_type b , (fun s => !!(eval s e = val_of_base b v))). *)
(* Proof. *)
(*   intros. *)
(*   apply derives_trans with *)
(*     (Q := sep_base e (reft_base { ν : b | φ })). *)
(*   eapply expr_eval_ty'; eauto. *)
(*   unfold sep_base.  *)
(*   rewrite <- exp_andp1. apply andp_left1. normalize. *)
(* Qed. *)

Hint Resolve 
     (* expr_eval_ty *)
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
   eval (λ i : var, eval w (if eq_dec i v then e' else var_e i), runloc w, hp w) e.
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
    (eval w e = eval (λ i : var, eval w (if eq_dec i v then e' else var_e i), runloc w, hp w) e).
Proof.
  induction e.
  + auto.
  + intros.
    unfold eval, stk; simpl. 
    destruct (eq_dec v0 v). subst v0. contradiction H.
    unfold FV in *.
    simpl in *.
    eauto.
    reflexivity.
  + auto.
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
    intro w. 
    apply andp_derives.
    destruct b; unfold eval_to, eval, stk; simpl; destruct (eq_dec v v) eqn:?X;
      try (apply derives_refl || congruence).
    apply derives_refl.
  rewrite subst_prop_rel.
  rewrite subst_expr_non_fv with (e := e).
  unfold subst, Subst_var_expr, subst_one. simpl.
  unfold subst_pred, eval, stk.
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
  induction H0; try econstructor; eauto.
  exists {ν : τ | φ}. eauto.
Qed.

Ltac nfv_env := 
  match goal with
    | H : nonfreevars _ ?v |- appcontext[subst_one ?v _] =>
      unfold nonfreevars in H; erewrite <- H; simpl; eauto using andp_left1, andp_left2, derives_refl
    | |- _ |-- subst_pred (subst_one ?v _) ?P =>
      assert (nonfreevars P v); eauto using var_nonmem_free_ctx, var_nonmem_free_grd; nfv_env
  end.

Lemma sep_base_eval :
  forall e τ φ,
    sep_base e (reft_base {ν : τ | φ}) |-- exp (eval_to e).
Proof.
  intros.
  unfold sep_base.
  destruct τ;
    simpl; intro w; try rewrite exp_andp1; try apply exp_left; try eapply exp_right; unfold eval_to; normalize.
  intros.
  eapply exp_right. apply andp_right. rewrite H. apply prop_right. reflexivity. normalize.
Qed.

Lemma sep_schema_in_env :
  forall Φ f p S,
    (f, (p, S)) ∈ Φ -> sep_schema f p S ∈ sep_proc_env Φ.
Proof.
  induction Φ as [ | (f', (p', S'))]; intros; eauto with datatypes.
  unfold sep_proc_env; fold sep_proc_env. 
  inv H. inv H0. left. reflexivity. right. apply IHΦ. assumption.
Qed.

Ltac do_pure' :=
  match goal with
    | |- appcontext[?X && ?Y] => apply andp_left1; do_pure'
    | |- appcontext[sep_ty] => apply sep_ty_pure
    | |- appcontext[sep_env ?X] => apply sep_env_pure
    | |- appcontext[sep_guards ?X] => apply sep_guard_pure
  end.

Ltac do_pure :=
  match goal with
    | |- _ |-- emp => do_pure'
    | |- pure _ => do_pure'
  end.

Hint Constructors expr_type.

Ltac apply_subst :=
  unfold subst, Subst_prop, subst_prop, Subst_var_expr, subst_expr, subst_one;
  match goal with 
    | |- appcontext[eq_dec ?x ?x] => 
      destruct (eq_dec x x); [ idtac | congruence ]
    | _ => idtac
  end.

Ltac unfold_in :=
  match goal with 
    | H: _ ∈ (_ :: _)|- _ => inversion_clear H; subst; unfold_in
    | H: _ = _ |- _ => inversion_clear H; subst; unfold_in
    | _ => idtac
  end.

Lemma type_mem_interp :
  forall Γ x T,
    (x, T) ∈ Γ -> sep_env Γ |-- sep_ty (var_e x) T.
Proof.
  induction Γ as [|[x' T']]; intros.
  + contradiction.
  + unfold sep_env; fold sep_env.
    unfold_in. do 2 apply andp_left1. apply derives_refl.
    apply andp_left1. apply andp_left2. auto.
Qed.

Corollary type_mem_interp_pred :
  forall Γ x b p,
    (x, {ν : b | p }) ∈ Γ -> sep_env Γ |-- sep_pred (subst (subst_one ν (var_e x)) p).
Proof.
  intros.
  eapply derives_trans.
  apply type_mem_interp.
  eauto.
  unfold sep_ty.
  apply andp_left1. apply andp_left2. apply derives_refl.
Qed.

Lemma subtype_interp_pred :
  forall Γ Ξ φ φ' x b,
    subtype Γ Ξ { ν : b | φ } { ν : b | φ' } -> 
    (sep_env Γ && sep_guards Ξ) |-- 
      sep_pred (subst (subst_one ν x) φ) --> 
      sep_pred (subst (subst_one ν x) φ').
Proof.
  intros.
  inv H.
  eapply derives_trans.
  apply H3.
  apply allp_left with (x0 := x).
  apply derives_refl.
Qed.

Lemma subtype_interp :
  forall Γ Ξ φ φ' x b,
    subtype Γ Ξ { ν : b | φ } { ν : b | φ' } -> 
      sep_env Γ && sep_guards Ξ |-- 
              sep_ty x { ν : b | φ } --> sep_ty x { ν : b | φ' }.
Proof with apply derives_refl.
  intros.
  unfold sep_ty.
  rewrite <- imp_andp_adjoint.
  eapply subtype_interp_pred in H.
  repeat rewrite <- andp_assoc.
  rewrite <- imp_andp_adjoint in H.
  repeat apply andp_right.
  apply andp_left1. apply andp_left2. apply andp_left1. apply andp_left1...
  apply andp_left2...
  apply andp_left1.
  destruct { ν : b | φ } eqn: FOO.
  inv FOO.
  rewrite andp_comm with (P := sep_base x reft_base).
  rewrite <- andp_assoc.
  apply andp_left1. 
  apply H.
  apply andp_left2...
Qed.

Hint Constructors subtype.

Lemma type_interp :
  forall Γ Σ Ξ x T,
    expr_type Γ Σ Ξ x T ->
    sep_env Γ && sep_guards Ξ |-- sep_ty x T.
Proof.
  intros Γ Σ Ξ x T ET.
  pose (expr_eval_ty' Γ Σ Ξ x T) as E.
  Ltac kill_easy :=
   unfold sep_ty; apply andp_right; try do_pure; apply andp_right; apply andp_left1; eauto.
  Ltac kill_consts :=
    repeat apply_subst; apply andp_right; [ simpl; intros; apply prop_right; reflexivity | do_pure].
  dependent induction ET; try kill_easy; try kill_consts.
  clear E.
  eapply type_mem_interp_pred; eauto.
  inv H0.
  eapply derives_trans with (Q := sep_env Γ && sep_guards Ξ && sep_ty e { ν : b | p }).
  apply andp_right. apply derives_refl.
  apply IHET; eauto.
  rewrite imp_andp_adjoint.
  eapply subtype_interp; eauto. 
Qed.

Lemma types_interp :
  forall Γ Σ Ξ xts,
    tc_list Γ Σ Ξ xts ->
    sep_env Γ && sep_guards Ξ |-- sep_env xts.
Proof.
  induction xts as [ | xt]; intros.
  + unfold sep_env at 2. apply andp_right. normalize. apply andp_left1. apply sep_env_pure.
  + unfold sep_env at 2. fold sep_env. repeat apply andp_right.
    * destruct xt as [x t].
      inv H.
      apply andp_right.
      eapply type_interp; eauto.
      normalize.
    * do_pure.
Qed.

Lemma heap_subtype_interp :
  forall Γ Ξ Σ Σ',
    heap_subtype Γ Ξ Σ Σ' ->
    sep_env Γ && sep_guards Ξ * sep_heap Σ |-- sep_heap Σ'.
Proof.
  intros.
  induction H.
  rewrite <- sepcon_emp.
  rewrite sepcon_comm.
  apply sepcon_derives. 
  apply derives_refl. 
  do_pure.
  repeat rewrite sep_heap_add; eauto.
  rewrite <- andp_dup with (P := sep_env Γ && sep_guards Ξ).
  rewrite <- sepcon_pure_andp with (P := sep_env Γ && sep_guards Ξ).
  rewrite <- sepcon_assoc.
  rewrite sepcon_comm with (Q := sep_heap Σ).
  rewrite <- sepcon_assoc.
  rewrite <- sepcon_assoc.
  rewrite sepcon_comm with (P := sep_heap Σ).
  rewrite sepcon_assoc.
  rewrite sepcon_comm with (Q := sep_heap Σ').
  apply sepcon_derives. 
  assumption.
  unfold sep_heap_bind.
  destruct t0 as [b1 p1]. destruct t' as [b2 p2].
  assert (b1 = b2).
    inv H1. reflexivity.
  subst b2.
  apply (subtype_interp _ _ _ _ (var_e x) b1) in H1.
  rewrite sepcon_comm.
  rewrite distrib_orp_sepcon.
  apply orp_left.
  apply orp_right1. rewrite <- sepcon_emp. apply sepcon_derives. apply derives_refl. do_pure.
  apply orp_right2. rewrite sepcon_assoc. apply sepcon_derives. apply derives_refl.
  rewrite sepcon_pure_andp; try do_pure.
  rewrite <- imp_andp_adjoint in H1.
  rewrite andp_comm. 
  eauto; do_pure.
  do_pure.
  do_pure.
Qed.

Lemma subst_loc_expr :
  forall G H (s : loc -> loc) (e : expr),
    wf_expr G H e ->
    subst s e = e.
Proof.
  intros; match goal with 
            | H : wf_expr _ _ _ |- _ => induction H
          end; simpl; auto.
  unfold subst. simpl.
  fold (subst s e1).
  fold (subst s e2).
  rewrite IHwf_expr1.
  rewrite IHwf_expr2.
  reflexivity.
Qed.

Lemma wf_expr_not_loc :
  forall G H (s : loc -> loc) e,
    wf_expr G H e -> 
    forall w, eval w e = eval (stk w, fun l => runloc w (s l), hp w) e.
Proof.
  intros.
  induction H0; eauto.
  simpl. rewrite IHwf_expr1. rewrite IHwf_expr2. reflexivity.
Qed.

Lemma subst_loc_pred_prop' :
  forall G H (s : loc -> loc) (p : reft_prop),
    wf_prop G H p -> 
    forall x, sep_pred p x = subst_pred_loc s (sep_pred p) x.
Proof.
  intros until p.
  induction p; intros H0 x; inv H0; eauto. 
  unfold subst_pred_loc.
  unfold sep_pred.
  simpl.
  f_equal.
  repeat erewrite <- wf_expr_not_loc; eauto.
  
  unfold subst_pred_loc in *.
  simpl.
  rewrite <- IHp.
  reflexivity.
  assumption.

  simpl.
  unfold subst_pred_loc in *.
  simpl.
  rewrite <- IHp1; try assumption.
  rewrite <- IHp2; try assumption.
  reflexivity.
   
  simpl.
  unfold subst_pred_loc in *.
  simpl.
  rewrite <- IHp1; try assumption.
  rewrite <- IHp2; try assumption.
  reflexivity.
Qed.

Lemma subst_loc_pred_prop :
  forall G H (s : loc -> loc) p,
    wf_prop G H p ->
    sep_pred (subst s p) = subst_pred_loc s (sep_pred p).
Proof.
  intros.
  unfold subst, Subst_prop_loc, subst_prop_loc.
  extensionality.
  erewrite <- subst_loc_pred_prop'; eauto.
Qed.

Lemma subst_base_loc :
  forall G H (s : loc -> loc) e b,
    wf_expr G H e ->
    sep_base (subst s e) (subst s b) = subst_pred_loc s (sep_base e b).
Proof.
  intros.
  unfold sep_base; destruct b; simpl; erewrite subst_loc_expr; eauto; unfold subst_pred_loc; extensionality.
  + f_equal.
    f_equal.
    extensionality.
    unfold eval_to.
    erewrite <- wf_expr_not_loc; eauto.
  + f_equal.
    f_equal.
    erewrite <- wf_expr_not_loc; eauto.
  + f_equal.
    f_equal.
    erewrite <- wf_expr_not_loc; eauto.
    erewrite <- wf_expr_not_loc; eauto.
Qed.

Lemma subst_prop_loc_var_comm :
  forall (p : reft_prop) (s1 : subst_t var expr) (s2 : subst_t loc loc),
    subst s1 (subst s2 p) = subst s2 (subst s1 p).
Proof.
  firstorder.
Qed.

Lemma subst_ty_loc :
  forall G H (s : loc -> loc) x T,
    wf_expr G H x ->
    wf_type G H T ->
    sep_ty (subst s x) (subst s T) = subst_pred_loc s (sep_ty x T).
Proof.
  intros.
  destruct T.
  unfold sep_ty at 2.
  push_subst.
  erewrite <- subst_base_loc; eauto.
  erewrite <- subst_loc_pred_prop; eauto.
  unfold sep_ty.
  unfold subst at 1. simpl. extensionality. f_equal. f_equal. f_equal.
  rewrite <- subst_prop_loc_var_comm.
  erewrite subst_loc_expr; eauto.
  inv H1.
  eauto with *.
  Grab Existential Variables.
  exact reft_base.
Qed.

Lemma subst_ty :
  forall {A B : Type} 
         {ST : Subst reft_type A B} 
         {SE : Subst expr A B }
         {SA : Subst assert A B } (θ : A -> B) x T,
    sep_ty (subst θ x) (subst θ T) = subst θ (sep_ty x T).
Proof.
  intros.
  unfold sep_ty at 2.
  destruct T as [b p]. 
  unfold subst at 3.

Ltac lift_apply l :=
  let X := fresh "X" in
  try (simpl; intro); pose l as X; simpl in X; eapply X; clear X. 

Lemma sep_proof_proc_call :
    forall Φ Γ Γ' Σ Σ' Ξ f xs r,
    wf_env Σ Γ ->
    wf_heap Γ Σ Σ ->
    wf_guards Γ Σ Ξ ->
    ((Φ ; Γ ; Σ ; Ξ) ⊢ proc_s f xs r [] ::: ( Γ' ; Σ')) ->
    (* ((Φ ; Γ ; Σ ; Ξ) *)
    (*    ⊢ proc_s f (subst θ (s_formals S)) (subst θ (fst (s_ret S))) [] ::: (Γ' ; Σ')) -> *)
    semax (sep_proc_env Φ)
          ((sep_env Γ && sep_guards Ξ) * sep_heap Σ)
          (proc_s f xs r [])
          ((sep_env Γ' && sep_guards Ξ) * sep_heap Σ').
Proof with (try assumption).
  (** Here we goo... **)
  intros.
  inv H2.
  rewrite sep_heap_split with (H1 := Σu) (H2 := Σm)...
  rewrite sep_heap_split with (H := Σ') (H1 := Σu) (H2 := isub θ θl (s_heap_out S))...
  rewrite sepcon_comm with (P := sep_heap Σu).
  rewrite sepcon_comm with (P := sep_heap Σu).
  rewrite <- sepcon_assoc.
  rewrite <- sepcon_assoc.
  apply semax_frame with (R := sep_heap Σu).
  pose (sep_schema f p S) as SchemDef.
  unfold sep_schema in SchemDef. destruct S as [xs ts hi ho [x t]]. simpl in *.
  apply semax_pre_post with (P' := sep_env (combine (isub θ θl xs) (isub θ θl ts)) 
                                   * sep_heap (isub θ θl hi) * (sep_env Γ && sep_guards Ξ))
                            (Q' := sep_ty (isub θ θl (var_e x)) (isub θ θl t) * sep_heap (isub θ θl ho) * (sep_env Γ && sep_guards Ξ)).
  (** P ==> P' **)
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  rewrite sepcon_pure_andp with (P := sep_env Γ && sep_guards Ξ); try do_pure.
  simpl. intro w.
  rewrite <- andp_dup with (P := sep_env Γ w && sep_guards Ξ w).
  rewrite <- sepcon_pure_andp with (P := sep_env Γ w && sep_guards Ξ w); try do_pure.
  rewrite sepcon_assoc.
  apply sepcon_derives.
  apply andp_right. 
  rewrite <- andp_dup with (P := sep_env Γ w && sep_guards Ξ w) at 1.
  rewrite <- sepcon_pure_andp with (P := sep_env Γ w && sep_guards Ξ w); try do_pure.
  apply derives_refl.
  lift_apply types_interp; eauto.
  lift_apply heap_subtype_interp; eauto.
  (** Q' ==> Q **)
  intro ρ.
  rewrite <- sepcon_pure_andp with (P := sep_ty (var_e (subst θ x)) (subst θl (subst θ t)) ρ).
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  apply sepcon_derives.
  rewrite sepcon_pure_andp; try do_pure.
  rewrite sepcon_pure_andp; try do_pure.
  simpl.
  apply andp_right. apply andp_right. apply andp_right. apply andp_left2. apply derives_refl.
  do 2 apply andp_left1. apply derives_refl.
  do_pure.
  apply andp_left1. apply andp_left2. apply derives_refl.
  apply derives_refl.
  do_pure.
  do_pure.
  apply semax_frame with (R := sep_env Γ && sep_guards Ξ).
  unfold isub in *.
  rewrite <- subst_combine.
  rewrite <- subst_combine.
  rewrite <- subst_dist_sepcon.

  
    
    
  

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
  eapply sep_base_eval.
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
