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

(* Lemma subst_emp_id : *)
(*   forall {A D R : Type} {s : subst_t A D R}, *)
(*     subst s emp = emp. *)
(* Proof. *)
(*   normalize. *)
(* Qed. *)

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
  forall {A B D R : Type} {SA : Subst A D R} {SB : Subst B D R} 
         {EA: Equivalence (@eq _ _ _ SA)}
         {EB : Equivalence (@eq _ _ _ SB)}
         {EB' : Equivalence (@eq _ _ _ (Subst_prod A B D R))}
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
    simpl subst at 1. unfold Subst.subst_prod.
    inversion H.
    specialize (IHxs ys θ H1).
    unfold subst at 2 3 in IHxs. unfold Subst_list in IHxs.
    rewrite <- IHxs.
    reflexivity.
Qed.

(* Hint Resolve subst_emp_id : subst. *)

Ltac subst_all :=
  repeat
    match goal with
      | H : (_, _) = (_, _) |- _ => inv H
      | H : ?X = ?Y |- _ => subst X
      | H : ?X = ?Y |- _ => inv H
    end.

Lemma vv_not_fv :
  forall G Gr H e T,
    wf_env H G -> expr_type G H Gr e T -> NFV e ν.
Proof.
  intros.
  induction H1; eauto with datatypes.
  + unfold NFV. intro. solve_by_inversion.
  + unfold NFV. intro. solve_by_inversion.
  + induction H0.
    contradiction H.
    intuition.
    destruct T as [b p].
    apply_in_env in_inv.
    decompose_all. 
    subst_all.
    unfold NFV. unfold fv_expr. 
    intro. inv H. intuition.
    intuition.
    intuition.
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
(* Qed. *)
  
Lemma fresh_var_nonmem_env :
  forall G H (x : var), fresh x G H -> var_not_in x G.
Proof.
  unfold fresh. unfold var_not_in.
  intros.
  rewrite Forall_forall.
  intros.
  decompose [and] H0. clear H0.
  destruct x0. simpl.
  unfold nonfv in H4. simpl in *.
  induction G as [| [x' t']].
  + inv H1.
  + inv H1. inv H0. inv H4. apply H0.
    apply IHG. assumption. inv H4. assumption.
Qed.

Lemma fresh_var_nonmem_heap :
  forall G H x, fresh x G H -> bind_not_in x H.
Proof.
  unfold fresh. unfold bind_not_in.
  intros.
  decompose [and] H0. clear H0. unfold nonfv in *; simpl in *.
  unfold nonfv_heap in H4.
  specialize (H4 l (x, t0)).
  intro.
  rewrite <- HE_Props.F.find_mapsto_iff in H0.
  apply H4 in H0. destruct H0. apply H2. reflexivity.
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
  forall G x, var_not_in x G <-> ~ (var_in x G).
Proof.
  unfold var_not_in.
  unfold var_in.
  intros.
  rewrite Forall_forall in *.
  firstorder.
  destruct x0.
  intro.
  apply (H r).
  inv H1. apply H0.
Qed.

Lemma fresh_var_not_in :
  forall G H x, fresh x G H -> ~ (var_in x G).
Proof.
  intros.
  induction G as [| [x' t']].
  + intro. inv H1. intuition.
  + intro. inv H1. inv H2. inv H1.
    apply H0. reflexivity.
    inv H0. unfold nonfv in H3. simpl in *.
    decompose [and] H3.
    apply IHG. constructor. assumption.
    constructor. assumption. assumption. exists x0. assumption.
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
     fresh_var_not_in
     (* fresh_var_cons_hp *)
     vv_not_fv
: var.

(* Lemma subst_dist_sepcon_loc : *)
(*   forall P Q (s : loc -> loc), *)
(*     subst_pred_loc s (P * Q) = subst_pred_loc s P * subst_pred_loc s Q. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Lemma subst_dist_sepcon : *)
(*   forall P Q (s : var -> expr), *)
(*     subst_pred s (P * Q) = subst_pred s P * subst_pred s Q. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Lemma subst_dist_andp : *)
(*   forall P Q (s : var -> expr), *)
(*     subst_pred s (P && Q) = subst_pred s P && subst_pred s Q. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Lemma subst_dist_andp_loc : *)
(*   forall P Q (s : loc -> loc), *)
(*     subst_pred_loc s (P && Q) = subst_pred_loc s P && subst_pred_loc s Q. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Lemma subst_dist_sepcon_loc : *)
(*   forall P Q (s : loc -> loc), *)
(*     subst_pred_loc s (P * Q) = subst_pred_loc s P * subst_pred_loc s Q. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Lemma subst_dist_orp : *)
(*   forall P Q (s : var -> expr), *)
(*     subst_pred s (P || Q) = subst_pred s P || subst_pred s Q. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Lemma subst_dist_imp : *)
(*   forall P Q (s : var -> expr), *)
(*     subst_pred s (P --> Q) = subst_pred s P --> subst_pred s Q. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

Lemma fresh_bind_Add :
  forall G H H' x x' l t,
    fresh x' G H' -> 
    fresh_loc l G H ->
    HE_Props.Add l (x,t) H H' -> 
    True ->
    fresh x' G H.
Proof.
  intros.
  unfold HE_Props.Add in *.
  unfold fresh in * |-. decompose_all.
  simpl nonfv in * |-.
  unfold nonfv_heap in *.
  split. 
  hassumption.
  split.
  hassumption.
  do 3 intro.
  specialize (H5 l0 xt).
  rewrite HE_Props.F.find_mapsto_iff in *.
  unfold type_binding in *.
  rewrite H2 in *.
  rewrite HE_Props.F.add_o in *.
  destruct xt. 
  destruct (HE_Props.F.eq_dec l l0). 
  subst.
  unfold fresh_loc in *. decompose_all.
  simpl nonfv in H7. unfold nonfv_heap in *.
  destruct (H7 l0 (v,r)).
  rewrite HE_Props.F.find_mapsto_iff. hassumption. congruence.
  intuition.
Qed.

Ltac instantiate_ex :=
  repeat match goal with
    | H : exists _,_ |- _ => destruct H
  end.

Lemma fresh_var_expr_fv' :
  forall G H x, 
    (* fresh x G H -> wf_expr G H e -> wf_heap G H H -> nonfv e x. *)
    x <> ν ->
    wf_expr G H (var_e x) -> 
    bind_in x H \/ var_in x G.
    (* fresh x G H -> wf_expr G H e (** -> wf_heap G H H **) -> nonfv e x. *)
Proof.
  intros.
  dependent induction H1.
  right. assumption.
  left. assumption.
  contradiction H0. reflexivity.
Qed.

Lemma nonmem_var_expr_fv :
  forall G H x e,
    x <> ν ->
    ~ var_in x G ->
    ~ bind_in x H ->
    wf_expr G H e ->
    nonfv e x.
Proof.
  intros.
  induction H3; try easy.
  + intro. simpl fv_expr in *. inv H3; eauto with var. 
  + intro. simpl fv_expr in *. inv H3; eauto with var.
  + intro. simpl fv_expr in *. inv H; intuition.
  + simpl nonfv. unfold NFV. simpl fv_expr. intro.
    apply_in_env in_app_or.
    intuition.
Qed.

Hint Resolve nonmem_var_expr_fv : var.

Lemma fresh_var_expr_fv :
  forall G H x e,
    fresh x G H -> wf_expr G H e -> nonfv e x.
Proof.
  intros.
  eapply nonmem_var_expr_fv; eauto. apply H0. eauto with var. rewrite <- bind_not_in_and_in. eauto with var.
Qed.

Hint Constructors wf_expr wf_prop wf_type wf_env : wf.

Lemma wf_expr_weaken_heap :
  forall G H H' x e l t,
    wf_expr G H e -> 
    ~ HE.In l H ->
    HE_Props.Add l (x,t) H H' ->
    wf_expr G H' e.
Proof.
  intros.
  dependent induction H0; eauto with wf.
  apply wf_var_hp.
  unfold bind_in in *.
  instantiate_ex.
  apply_in_env HE_Props.F.not_find_in_iff.
  exists x0. exists x1.
  rewrite H2 in *.
  rewrite HE_Props.F.add_o.
  destruct (HE_Props.F.eq_dec l x0).
  subst. congruence.
  assumption.
Qed.

Lemma wf_pred_weaken_heap :
  forall G H H' x p l t,
    wf_prop G H p ->
    ~ HE.In l H ->
    HE_Props.Add l (x,t) H H' ->
    wf_prop G H' p.
Proof.
  intros.
  dependent induction H0; eauto with wf.
  constructor;
  eauto using wf_expr_weaken_heap.
Qed.

Lemma wf_ty_weaken_heap :
  forall G H H' x t l t',
    wf_type G H t ->
    ~ HE.In l H ->
    HE_Props.Add l (x,t') H H' ->
    wf_type G H' t.
Proof.
  intros.
  inv H0.
  eauto using wf_pred_weaken_heap with wf.
Qed.

Lemma nonmem_var_pred_fv :
  forall G H x p,
    x <> ν ->
    ~ var_in x G ->
    ~ bind_in x H ->
    wf_prop G H p ->
    nonfv p x.
Proof.
  intros.
  induction H3; try easy. 
  + split; eauto using nonmem_var_expr_fv.
  + split; intuition.
  + split; intuition.
Qed.

Lemma fresh_var_pred_fv :
  forall G H p x,
    fresh x G H -> wf_prop G H p -> nonfv p x.
Proof.
  intros.
  eapply nonmem_var_pred_fv.
  hassumption.
  eauto with var.
  rewrite <- bind_not_in_and_in.
  eauto with var.
  assumption.
Qed.

Lemma nonmem_var_type_fv :
  forall G H t x,
    x <> ν ->
    ~ var_in x G ->
    ~ bind_in x H ->
    wf_type G H t ->
    nonfv t x.
Proof.
  intros.
  destruct t0.
  split. destruct reft_base; easy.
  inv H3.
  eauto using nonmem_var_pred_fv.
Qed.    

Hint Transparent stk hp runloc fst snd.

(** 
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
**)

Lemma nonfree_var_expr_eval :
  forall G H e e' x,
    fresh x G H ->
    wf_expr G H e ->
    forall w,
      eval w e = eval (λ i : var, if eq_dec x i then e' else stk w i, runloc w, hp w) e.
Proof.
  intros.
  induction H1.
  * reflexivity.
  * pose (fresh_var_expr_fv Γ Σ v).
    simpl in n. unfold NFV  in n. simpl in n.
    simpl. unfold stk. simpl.
    destruct (eq_dec x v).
    destruct (n (var_e x)); subst; try assumption. constructor. assumption. left. congruence. reflexivity.
  * simpl. unfold stk. simpl.
    destruct (eq_dec x v); subst.
    apply_in_env fresh_var_nonmem_heap. 
    apply_in_env bind_not_in_and_in. contradiction. reflexivity.
  * simpl eval. unfold stk. simpl. destruct (eq_dec x ν). subst. firstorder.
    reflexivity.
  * simpl eval. rewrite IHwf_expr1. rewrite IHwf_expr2. reflexivity. assumption. assumption.
Qed.

Lemma nonfv_not_r :
  forall p (x : var),
    nonfv (sep_pred p) x -> nonfv (sep_pred (not_r p)) x.
Proof.
  intros.
  simpl.
  unfold nonfv_assert.
  intros;
  specialize (H w v).
  f_equal; f_equal; apply H.
Qed.

Lemma nonfv_and_r :
  forall p1 p2 (x : var),
    nonfv (sep_pred p1) x -> nonfv (sep_pred p2) x -> nonfv (sep_pred (and_r p1 p2)) x.
Proof.
  intros.
  simpl.
  unfold nonfv_assert.
  intros;
  specialize (H w v);
  specialize (H0 w v).
  do 2 f_equal. apply H.  apply H0.
Qed.

Lemma nonfv_or_r :
  forall p1 p2 (x : var),
    nonfv (sep_pred p1) x -> nonfv (sep_pred p2) x -> nonfv (sep_pred (or_r p1 p2)) x.
Proof.
  intros.
  simpl.
  unfold nonfv_assert.
  intros;
  specialize (H w v);
  specialize (H0 w v).
  do 2 f_equal. apply H.  apply H0.
Qed.

Lemma fresh_var_nonfree_pred :
  forall G H p x,
    fresh x G H -> wf_prop G H p -> nonfv (sep_pred p) x.
Proof.
  intros.
  apply SubstProp_var. 
  induction p; try easy.
  inv H1. split; eauto using fresh_var_expr_fv.
  simpl. apply IHp. inv H1; easy.
  simpl. inv H1. split; intuition.
  simpl. inv H1. split; intuition.
Qed.

Lemma wf_expr_nonfree_locs :
  forall G H e, 
    wf_expr G H e -> (forall (l : loc), nonfv e l).
Proof.
  intros.
  induction H0; try easy.
  simpl nonfv. unfold NFL. 
  simpl.
  intro.
  apply in_app_or in H. intuition.
Qed.

Lemma wf_prop_nonfree_locs :
  forall G H p,
    wf_prop G H p -> (forall (l : loc), nonfv p l).
Proof.
  intros. simpl. unfold nonfv_prop.
  induction H0; eauto using wf_expr_nonfree_locs. 
Qed.

Lemma wf_type_nonfree_locs :
  forall G H t,
    wf_type G H t -> (forall (l : loc), nonfv (reft_r t) l).
Proof.
  intros.
  inv H0.
  eauto using wf_prop_nonfree_locs.
Qed.
Hint Resolve wf_expr_nonfree_locs wf_prop_nonfree_locs wf_type_nonfree_locs : wf.

Lemma wf_heap_nonfree_locs :
  forall G H,
    wf_heap G H H ->
    (forall l x t, MapsTo l (x,t) H -> (forall (l : loc), nonfv (reft_r t) l)).
Proof.
  intros.
  unfold wf_heap in *.
  apply H0 in H1.
  decompose_all.
  destruct t0.
  eapply wf_type_nonfree_locs.
  hassumption.
Qed.

Lemma wf_ctx_nonfree_locs :
  forall G H,
    wf_env H G -> 
    Forall (fun xt => (forall (l : loc), nonfv (reft_r (snd xt)) l)) G.
Proof.
  intros.
  rewrite Forall_forall.
  induction H0; intros.
  + solve_by_inversion. 
  + match goal with | H : List.In _ (_ :: _) |- _ =>  inv H end;
    eauto with wf.
Qed.

Hint Resolve wf_ctx_nonfree_locs wf_heap_nonfree_locs : wf.
Hint Resolve fresh_var_nonfree_pred : wf var.
Hint Rewrite fresh_var_nonfree_pred : wf.

Lemma wf_expr_cons :
  forall G H xt e,
    wf_expr G H e -> wf_expr (xt :: G) H e.
Proof.
  intros.
  induction H0; eauto with wf.
  + constructor. unfold var_in in *. instantiate_ex.
    exists x. right. assumption.
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

Lemma wf_guards_cons :
  forall G g x t,
    wf_guards G g -> wf_guards ((x,t) :: G) g.
Proof.
  induction g; intros.
  + unfold wf_guards. rewrite Forall_forall. intuition.
  + unfold wf_guards in *.
    rewrite Forall_forall in *.
    intros.
    inv H0.
    unfold wf_guard.
    specialize (H x0). destruct H. left. reflexivity.
    split.
    apply wf_prop_cons.
    assumption.
    assumption.
    unfold wf_guard.
    destruct (H x0). right. assumption. split.
    apply wf_prop_cons. assumption. assumption.
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
    + apply in_inv in H0. destruct H0. inv H0. 
      inv H1. 
      apply wf_type_cons.
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

(**
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

**)
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

(* Hint Rewrite  *)
(*      subst_prop_rel subst_expr_fun subst_prop_and subst_prop_or subst_prop_not  *)
(* : wf. *)
Hint Resolve 
     (* subst_prop_rel subst_expr_fun subst_prop_and subst_prop_or subst_prop_not  *)
     wf_prop_and wf_prop_or wf_prop_not 
: wf.

Ltac split_subst_var :=
  match goal with 
    | |- appcontext[_ (subst_one ?x _) (var_e ?v)] =>
      unfold subst; unfold subst_one; simpl;
      destruct (eq_dec x v); subst
  end.

Lemma wf_subst_vv_expr :
  forall G H e e',
    wf_expr G H e -> wf_expr G H e' ->
    wf_expr G H (subst (subst_one ν e') e).
Proof.
  intros.
  induction e.
  + eauto with wf.
  + inv H0; split_subst_var; eauto with wf.
  + inversion H0.
  + inversion H0; rewrite subst_fun; eauto with wf.
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
  induction p; inv H1; rw_subst_reft; eauto with wf.
Qed.
  
Hint Resolve wf_subst_vv_pred : wf.

Lemma fresh_var_nonfree_ty :
  forall G H t x v,
    x <> v ->
    fresh v G H -> 
    var_in x G \/ bind_in x H -> 
    wf_type G H t -> nonfv (sep_ty (var_e x) t) v.
Proof.
  Hint Transparent NFV.
  intros.
  apply SubstTy_var.
  simpl. 
  firstorder.
  simpl.
  unfold nonfv_reft_t.
  split. destruct (reft_base t0); easy. 
  inv H3.
  eapply fresh_var_pred_fv; eauto.
Qed.

Lemma var_nonmem_free_ctx :
  forall G H x, fresh x G H -> wf_env H G -> nonfv (sep_env G) x.
Proof.
  intros G H x fr wf.
  induction G as [| (x',t')].
  + unfold nonfv. simpl. unfold nonfv_assert. normalize.
  + destruct t' as [b p]. 
    assert (x' <> x).
      apply var_not_in_not_eq with (G := G) (t := { ν : b | p }). 
      eauto with var.
    unfold sep_env. fold sep_env.
    apply nonfv_andp. split.
    apply nonfv_andp. split.
    eapply fresh_var_nonfree_ty; eauto.
    left. unfold var_in. exists { ν : b | p}. left. reflexivity.
    inv wf. apply wf_type_cons. easy.
    apply IHG. eauto with var. inv wf. easy. easy.
Qed.

Instance Subst_list_ty_var_var : Subst (list reft_type) var var := Subst_list. 
Instance Subst_list_ty_loc_loc : Subst (list reft_type) loc loc := Subst_list. 
Instance Subst_list_env_var_var : Subst type_env var var := Subst_list. 
Instance Subst_list_env_loc_loc : Subst type_env loc loc := Subst_list. 

Lemma fresh_wf_ctx_nonfv :
  forall H G x,
    fresh x G H -> wf_env H G -> nonfv G x.
Proof.
  intros.
  induction G as [| [x' t']].
  + firstorder.
  + simpl nonfv. unfold fv_list. split.
    unfold fresh in *.
    decompose_all.
    split.
    apply_in_env @subst_cons_prod_neq_1. hassumption. 
    apply_in_env @subst_cons_prod_neq_2. hassumption.
    apply IHG.
    eauto using fresh_var_cons.
    match goal with
      | H : wf_env _ _ |- _ => inv H; hassumption end.
Qed.

Lemma fresh_loc_not_in_heap :
  forall G H l,
    fresh_loc l G H -> ~ In l H.
Proof.
  firstorder.
Qed.

Hint Resolve fresh_loc_not_in_heap : var wf fresh heaps.
        
Lemma wf_ctx_weaken_heap :
  forall G H H' l x t,
    wf_env H G ->
    fresh x G H ->
    fresh_loc l G H ->
    HE_Props.Add l (x,t) H H' ->
    wf_env H' G.
Proof.
  intros.
  induction G as [| [x' t']]. 
  + eauto with wf.
  + inv H0.
    constructor; try hassumption.
    assert (x <> x').
    intro. subst. hassumption. reflexivity.
    unfold bind_not_in in *.
    intros l'' t''.
    rewrite H3.
    intro.
    rewrite HE_Props.F.add_o in *.
    destruct (HE_Props.F.eq_dec l l'').
    subst_all. congruence.
    specialize (H8 l'' t''). intuition.
    assumption.
    firstorder.
    firstorder.
    eapply wf_ty_weaken_heap; eauto with fresh.
Qed.

Lemma expr_type_wf :
  forall G H Grds e T,
    expr_type G H Grds e T -> wf_expr G H e.
Proof.
  intros.
  induction H0; try econstructor; eauto.
  exists {ν : τ | φ}. eauto.
Qed.

Lemma wf_stmt :
  forall Φ Γ Ξ Σ s Γ' Σ',
    wf_env Σ Γ ->
    (Φ ; Γ ; Σ ; Ξ) ⊢ s ::: ( Γ' ; Σ') ->
    wf_env Σ' Γ'.
Proof.
  intros.
  induction H0.
  + trivial.
  + trivial.
  + eapply wf_ctx_weaken_heap; eauto.
  + constructor; eauto with wf var.
    hassumption.
    constructor.
    constructor.
    eauto with wf.
    eauto using expr_type_wf with var wf.
  + constructor.
    apply var_not_in_and_in. eapply fresh_var_not_in. hassumption.
    rewrite bind_not_in_and_in.
    intro.
    unfold bind_in in *.
    instantiate_ex.
    rewrite H4 in *.
    rewrite HE_Props.F.add_o in *.
    destruct (HE_Props.F.eq_dec l x0). subst_all. congruence.
    apply fresh_var_nonmem_heap in H0.
    rewrite bind_not_in_and_in in *.
    apply H0. exists x0. exists x1. assumption.
    hassumption.
    eapply wf_ctx_weaken_heap; eauto.
    eauto with wf.
  + hassumption.
  + intuition.
Qed.

Lemma wf_weaken_heap :
  forall Γ Σ Σ' l x T,
    wf_heap Γ Σ Σ ->
    fresh x Γ Σ ->
    fresh_loc l Γ Σ ->
    HE_Props.Add l (x, T) Σ Σ' ->
    wf_heap Γ Σ' Σ.
Proof.
  firstorder.
Qed.

Lemma fresh_binder_no_mapping :
  forall Γ Σ l x t,
    fresh x Γ Σ ->
    MapsTo l (x,t) Σ -> False.
Proof.
  firstorder.
Qed.

Lemma wf_heap_add :
  forall Γ Σ Σ' l x t,
    wf_type Γ Σ t ->
    fresh x Γ Σ ->
    fresh_loc l Γ Σ ->
    wf_heap Γ Σ Σ ->
    HE_Props.Add l (x,t) Σ Σ' ->
    wf_heap Γ Σ' Σ'.
Proof.
  + split; repeat intro.
    rewrite HE_Props.F.find_mapsto_iff in *.
    rewrite H3 in *.
    rewrite <- HE_Props.F.find_mapsto_iff in *.
    rewrite HE_Props.F.add_mapsto_iff in *.
    decompose_all. subst_all.
    eauto using wf_ty_weaken_heap with wf var fresh heaps.
    apply_in_env H2. eauto using wf_ty_weaken_heap with fresh.
    repeat rewrite HE_Props.F.find_mapsto_iff in *.
    repeat rewrite H3 in H4.
    destruct H4.
    repeat rewrite <- HE_Props.F.find_mapsto_iff in *.
    repeat rewrite HE_Props.F.add_mapsto_iff in *.
    decompose_all. repeat subst_all. easy. subst_all.
    unfold wf_heap in *. decompose_all.
    exfalso. eauto using fresh_binder_no_mapping.
    subst_all. exfalso. eauto using fresh_binder_no_mapping.
    unfold wf_heap in *. decompose_all.
    destruct (H8 l0 l' x0 t1 t'). split; assumption. split; assumption.
Qed.

Hint Resolve wf_heap_add fresh_binder_no_mapping : wf var heaps.
 
Lemma expr_type_wf_type :
  forall Γ Σ Ξ e b p,
    expr_type Γ Σ Ξ e { ν : b | p } ->
    wf_env Σ Γ ->
    wf_type Γ Σ { ν : b | p }.
Proof.
  intros.
  induction H; eauto with wf.
Qed.
Hint Resolve expr_type_wf_type : wf.
Ltac add_mapsto := 
    match goal with
      | A : HE_Props.Add _ _ _ _,
        H : MapsTo _ _ _ 
        |- _ => rewrite HE_Props.F.find_mapsto_iff in H;
                rewrite A in H;
                rewrite <- HE_Props.F.find_mapsto_iff in H;
                rewrite HE_Props.F.add_mapsto_iff in H
    end.

Lemma wf_heap_stmt :
  forall Φ Γ Ξ Σ s Γ' Σ',
    wf_env Σ Γ ->
    wf_heap Γ Σ Σ ->
    (Φ ; Γ ; Σ ; Ξ) ⊢ s ::: ( Γ' ; Σ') ->
    wf_heap Γ' Σ' Σ'.
Proof.
  intros.
  induction H1; intros; eauto.
  + eauto with wf.
  + firstorder. destruct t0. apply wf_type_cons. eauto using expr_type_wf with wf.
  + assert (wf_heap Γ Σ' Σ'). apply wf_heap_add with (Σ := Σ) (l := l) (x := y) (t := t0); eauto with wf.
    destruct t0. constructor. 
    eauto using expr_type_wf_type with wf.
    split.
    intros.
    add_mapsto.
    decompose_all;
    subst_all;
    destruct t1.
    eauto using wf_ty_weaken_heap with wf var fresh heaps.
    apply H0 in H9.
    eauto using wf_ty_weaken_heap with wf var fresh heaps.
    intros.
    decompose_all.
    repeat add_mapsto.
    decompose_all; subst_all.
    easy.
    exfalso. eauto using fresh_binder_no_mapping.
    exfalso. eauto using fresh_binder_no_mapping.
    unfold wf_heap in *. decompose_all.
    eapply H13. split; eauto.
  + hassumption.
  + apply IHstmt_type2.
    eauto using wf_stmt.
    apply IHstmt_type1.
    eauto using wf_stmt.
    assumption.
    Grab Existential Variables.
    exact (int_t).
Qed.

Lemma In_imp_var_in :
  forall xt G, xt ∈ G -> var_in (fst xt) G.
Proof.
  unfold var_in. 
  destruct xt as [x t].
  intros. exists t. auto.
Qed.

Hint Resolve In_imp_var_in : env.

Lemma env_monotonic :
  forall P X G G' Hp Hp' s,
    (P ; G ; Hp ; X) ⊢ s ::: (G' ; Hp') ->
    forall x, var_in x G -> var_in x G'.
Proof.
  Ltac envmono := 
    auto with env ||
    (intros; unfold var_in; 
    match goal with
      | H: var_in ?x ?G |- (exists _, _) => destruct H;
      match goal with
        | t: reft_type |- _ =>
          exists t; first [right; apply H | try left; apply H ]
      end
      | H : appcontext[join_env] |- _ => apply H; envmono
    end).
  intros; induction H; envmono. 
Qed.

Lemma wf_expr_bigger :
  forall G G' H e,
    wf_expr G H e ->
    (forall x, var_in x G -> var_in x G') ->
    wf_expr G' H e.
Proof.
  intros.
  induction e.
  + constructor.
  + inv H0.
    unfold var_in in *.
    destruct (H1 v).
    instantiate_ex.
    exists x. assumption.
    constructor. exists x. assumption.
    apply wf_var_hp. assumption.
    apply wf_vv.
  + inversion H0.
  + inv H0.
    constructor.
    intuition.
    intuition.
Qed.

Lemma wf_prop_bigger :
  forall G G' H p,
    wf_prop G H p ->
    (forall x, var_in x G -> var_in x G') ->
    wf_prop G' H p.
Proof.
  intros.
  induction p; try first [ solve [constructor] | inv H0; constructor; intuition ].
  apply wf_expr_bigger with (G := G); assumption. 
  apply wf_expr_bigger with (G := G); assumption. 
Qed.

Lemma wf_guard_bigger :
  forall G G' g,
    wf_guard G g ->
    (forall x, var_in x G -> var_in x G') ->
    wf_guard G' g.
Proof.
  intros.
  split.
  apply wf_prop_bigger with (G := G).  apply H. assumption.
  apply H.
Qed.  

Lemma wf_guards_bigger :
  forall G G' g,
    wf_guards G g ->
    (forall x, var_in x G -> var_in x G') ->
    wf_guards G' g.
Proof.
  intros.
  induction g; constructor.
  inv H. eauto using wf_guard_bigger.
  inv H. intuition.
Qed.

Lemma wf_guards_stmt :
  forall Φ Γ Ξ Σ s Γ' Σ',
    wf_env Σ Γ ->
    wf_guards Γ Ξ ->
    (Φ ; Γ ; Σ ; Ξ) ⊢ s ::: ( Γ' ; Σ') ->
    wf_guards Γ' Ξ.
Proof.
  intros.
  induction H1; eauto.
  + unfold isub. destruct (s_ret S).
    simpl subst at 1. unfold Subst.subst_prod. simpl subst at 1. unfold Subst.subst_prod.
    apply wf_guards_cons. assumption.
  + apply wf_guards_cons. assumption.
  + apply wf_guards_cons. assumption.
  + intuition. 
    unfold join_env in *.
    eapply wf_guards_bigger; eauto.
    assert (forall x, var_in x Γ -> var_in x Γ1). eapply env_monotonic; eauto.
    assert (forall x, var_in x Γ -> var_in x Γ2). eapply env_monotonic; eauto.
    intros.
    apply H2. intuition.
  + apply IHstmt_type2.
    eauto using wf_stmt.
    apply IHstmt_type1.
    eauto using wf_stmt.
    assumption.
Qed.

Lemma sep_heap_emp :
  sep_heap (empty type_binding) = emp.
Proof.
  reflexivity.
Qed.


Lemma EqMapsTo :
  forall H H',
    Equal H H' -> sep_heap H = sep_heap H'.
Proof.
  unfold sep_heap.
  intros.
  apply HE_Props.fold_Equal.
  apply eq_equivalence.
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
  apply HE_Props.fold_add. apply eq_equivalence.
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
  unfold sep_heap. rewrite HE_Props.fold_Empty. reflexivity. apply eq_equivalence.
  assumption.
Qed.

Lemma fresh_loc_not_In :
  forall l G H, fresh_loc l G H -> nonfv H l.
Proof.
  firstorder.
Qed.

Lemma fv_var_sep_heap_bind :
  forall k e (x : var),
  @nonfv loc var var _ k x -> 
  @nonfv type_binding var var _ e x ->
   @nonfv assert var var _  (sep_heap_bind k e) x.
Proof.
  intros. destruct e.
  unfold sep_heap_bind.
  apply nonfv_orp. split.
  unfold eval_to. unfold eval. 
  simpl. unfold nonfv_assert. simpl. intros.
  f_equal.
  apply nonfv_sepcon. split.
  unfold emapsto. simpl. unfold nonfv_assert. intros.
  f_equalize. f_equal. extensionality. f_equalize.
  unfold eval_to. simpl. f_equalize. f_equal. f_equal.
  unfold subst_one. unfold stk. simpl. destruct (eq_dec x v). 
  subst x. inv H0. simpl in *. congruence. reflexivity.
  apply SubstTy_var. inv H0. unfold nonfv in H1. simpl in *.
  intro. simpl in *. intuition.
  inv H0. 
  simpl in *. unfold nonfv_reft_t in *.
  destruct H2. split.
  assumption. 
  induction (reft_r r); simpl in *; intuition.
Qed.

Lemma fv_var_sep_heap :
  forall (H : heap_env) (x : var), nonfv H x -> nonfv (sep_heap H) x.
Proof.
  intros.
  unfold sep_heap.
  apply HE_Props.fold_rec_bis.
  intros. assumption. easy.
  intros. apply nonfv_sepcon. constructor.
  unfold nonfv in H0. simpl in H0.
  unfold nonfv_heap in H0. specialize (H0 k e). apply H0 in H1.
  apply fv_var_sep_heap_bind; easy.
  easy.
Qed.

Lemma var_nonmem_free_heap :
  forall G H x, fresh x G H -> wf_heap G H H -> nonfv (sep_heap H) x.
Proof.
  intros.
  apply fv_var_sep_heap.
  apply H0.
Qed.

(* Lemma var_nonmem_free_heap : *)
(*   forall G H H' x, fresh x G H -> wf_heap G H H' -> nonfv (sep_heap H') x. *)
(* Proof. *)
(*   intros. *)
(*   apply fv_var_sep_heap. *)
(*   induction H1. simpl nonfv. repeat intro. *)
(*   rewrite HE_Props.F.elements_mapsto_iff in *. *)
(*   rewrite HE_Props.elements_Empty in *. *)
(*   rewrite H in *. inv H1. *)

(*   (* apply IHwf_heap in H0. *) *)
(*   (* simpl nonfv in H0. unfold nonfv_heap in *. *) *)
(*   repeat intro. *)
(*   unfold HE_Props.Add in *. *)
(*   unfold nonfv. simpl. unfold nonfv_heap. *)
(*   rewrite  HE_Props.F.find_mapsto_iff in *. *)
(*   specialize (H5 l0). unfold type_binding in *. rewrite H5 in H6. *)
(*   rewrite <- HE_Props.F.find_mapsto_iff in *. *)
(*   rewrite HE_Props.F.add_mapsto_iff in *. *)
(*   decompose [and or] H6; clear H6. destruct xt. inv H9. *)
(*   split. easy. *)
(*   simpl. *)
(*   (* apply fresh_var_nonmem_heap in H0. *) *)
(*   compare v x.  *)
(*   intro. subst. exfalso. apply bind_not_in_and_in in H2. contradiction.  *)
(*   eapply fresh_var_nonmem_heap. eauto. *)
(*   intro. split. easy. unfold nonfv_reft_t.  *)
(*   split. simpl nonfv. destruct r. simpl. destruct reft_base; easy. *)
(*   simpl nonfv. destruct r. simpl. eauto with var. *)
(*   induction reft_r; try easy.  *)
(*   + simpl. *)

(*   admit. decide equality. *)
(*   simpl nonfv in IHwf_heap. unfold nonfv_heap in IHwf_heap.  *)
(*   simpl nonfv in IHwf_heap. eapply IHwf_heap; eauto. *)
(*  Qed. *)

Ltac step :=
  match goal with
      | |- appcontext[?f (cons _ _)] => unfold f; fold f
  end.

Lemma wf_expr_empty_heap :
  forall G e, wf_expr G heap_emp e -> forall H, wf_expr G H e.
Proof.
  intros.
  dependent induction H; eauto with wf var.
    unfold bind_in in *. destruct H. destruct H.
    rewrite HE_Props.F.empty_o in *. discriminate H.
Qed.

Lemma wf_prop_empty_heap :
  forall G p, wf_prop G heap_emp p -> forall H, wf_prop G H p.
Proof.
  intros.
  dependent induction H; eauto using wf_expr_empty_heap with wf.
Qed.

Lemma var_nonmem_free_grd :
  forall G g x,
    x <> ν ->
    ~ var_in x G ->
    wf_guards G g ->
    nonfv (sep_guards g) x.
Proof.
  intros.
  induction g as [| g'].
  + easy.
  + step. apply nonfv_andp. split. apply nonfv_andp. split.
    apply SubstProp_var. 
    apply nonmem_var_pred_fv with (G := G) (H := heap_emp); auto.
    intro. unfold bind_in in *. instantiate_ex.
    rewrite HE_Props.F.empty_o in *. congruence.
    unfold wf_guards in *. inv H1. apply H4.
    inv H1.
    intuition.
    easy.
Qed.

Lemma var_nonmem_free_grd' :
  forall G H g x, 
    fresh x G H -> wf_env H G -> wf_guards G g -> 
    nonfv (sep_guards g) x.
Proof.
  intros.
  induction g as [| g'].
  + easy.
  + step. apply nonfv_andp. split. apply nonfv_andp. split.
    apply SubstProp_var. inv H2.
    destruct H5.
    eapply fresh_var_pred_fv; eauto. apply wf_prop_empty_heap. easy.
    apply IHg. inv H2. apply H6. easy.
Qed.

Hint Constructors value.

Lemma var_val :
  forall Γ x b φ, 
    (x,{ ν : b | φ}) ∈ Γ ->
    sep_env Γ |-- (EX v : value,
                          (fun s => !!(eval s (var_e x) = Some v))).
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
        intro w. unfold eval_to. 
        simpl. apply andp_left1. normalize.
      * intro w. simpl. eapply exp_right. instantiate (1 := null_v).
        unfold eval_to. simpl. apply andp_left1. apply andp_left1. normalize.
      * unfold OkRef. simpl. intro. 
        apply (exp_right (match (runloc x0 l) with 
                            | Some a => addr_v a 
                            | None => addr_v (A 0)
                          end)).
        destruct (runloc x0 l).
        repeat apply andp_left1. apply derives_refl.
        apply andp_left1. rewrite andp_comm. rewrite <- andp_assoc.
        apply andp_left1.
        apply derives_extract_prop; intros.
        apply prop_left. intro. congruence.
  + apply andp_left1. apply andp_left2.
    eauto.
Qed.


Lemma lift_derives :
  forall (P Q : assert) x,
    P |-- Q -> P x |-- Q x.
Proof.
  firstorder.
Qed.

Lemma lift_andp :
  forall (P Q : assert) x,
    (P && Q) x = P x && Q x.
Proof. easy. Qed.

Lemma lift_sepconp :
  forall (P Q : assert) x,
    (P * Q) x = P x * Q x.
Proof. easy. Qed.

Lemma lift_emp :
  forall (x : world),
    emp = emp x.
Proof. easy. Qed.

Ltac fix_assert_help :=
  repeat first [ rewrite <- lift_andp
               | rewrite <- lift_sepconp
               | erewrite lift_emp 
               | apply lift_derives
               ].

Ltac fix_assert :=
  let x := fresh "ρ" in
  match goal with 
    | |- appcontext[fun ρ : world  => _] => intro x; fix_assert_help; clear x
    | _ => idtac
  end.

Lemma var_eval :
  forall Γ x b φ w, 
    (x, { ν : b | φ }) ∈ Γ -> 
    sep_env Γ w |-- (EX v : value, eval_to (var_e x) v w).
Proof.
  intros.
  unfold eval_to.
  simpl.
  rewrite <- exp_andp1.
  apply andp_right.
  apply var_val in H. simpl in H.
  specialize (H w).
  eapply derives_trans.
  apply H.
  normalize.
  apply sep_env_pure.
Qed.

Lemma expr_eval :
  forall Γ Σ Ξ e b φ,
    expr_type Γ Σ Ξ e { ν : b | φ } ->
    sep_env Γ |-- (EX v : value, eval_to e v).
Proof.
  intros.
  simpl.
  intros.
  induction H.
  + eapply exp_right. unfold eval_to; simpl. apply andp_right. apply prop_right. reflexivity.
    apply sep_env_pure.
  + eapply exp_right. unfold eval_to; simpl. apply andp_right. apply prop_right. reflexivity.
    apply sep_env_pure.
  + eapply var_eval. apply H.
  + eauto using exp_right, var_eval.
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
    apply exp_right with (x := n). unfold eval_to; simpl.
    apply andp_right.
    normalize.
    apply sep_env_pure.

    intro w. unfold eval_to; simpl. apply andp_right. apply prop_right. reflexivity.
    apply sep_env_pure.

    intro w. induction Γ as [| (x', t')]. contradiction.
      apply in_inv in H. destruct H. inv H. simpl.
      apply andp_left1. apply andp_left1. 
      unfold sep_ty. simpl. apply andp_left1. apply andp_left1.
      unfold sep_base. simpl. apply andp_left1. apply derives_refl.
      step.
      simpl.
      apply andp_left1. apply andp_left2. apply IHΓ. assumption.

      inv H1. eauto.
Qed.

Hint Resolve 
     exfalso_etype_fun
     expr_eval_ty'
     expr_eval
     var_val
     var_eval
: eval.

Lemma subst_ty_base_pred :
  forall {D R : Type} {S : Subst assert D R } (s : subst_t D R) v b p,
    subst s (sep_ty (var_e v) { ν : b | p }) =
    subst s (sep_base (var_e v) b && sep_pred (subst (subst_one ν (var_e v)) p) && emp).
Proof.
  firstorder.
Qed.

(**
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
**)

(* Definition F P  *)

Instance Proper_sep_ty :
    Proper (Logic.eq ==> (@eq reft_type var expr _) 
                     ==> (Logic.eq ( A := assert)) ) sep_ty.
Proof.
  hnf.
  intros. subst x.
  hnf.
  intros t1 t2. intros equ. 
  inv equ.
  unfold eq in *. simpl in *.
  destruct t1. destruct t2. simpl in *.
  unfold eq_base in *. 
  assert (reft_base = reft_base0).
  destruct reft_base; destruct reft_base0; try easy. inv H. easy.
  subst reft_base0.
  unfold sep_ty. f_equal. f_equal.
  clear H.
  generalize H0. clear H0. generalize reft_r0. clear reft_r0.
  induction reft_r; destruct reft_r0; intros; try easy.
  inv H0. rewrite H. rewrite H1. reflexivity.
  simpl in H0. simpl. extensionality. f_equal. f_equal. 
  unfold subst in IHreft_r. simpl in *. erewrite IHreft_r. eauto. easy.
  simpl in H0.
  simpl in *. rewrite (IHreft_r1 reft_r0_1). rewrite (IHreft_r2 reft_r0_2).
  reflexivity. easy. easy.
  simpl in *. rewrite (IHreft_r1 reft_r0_1). rewrite (IHreft_r2 reft_r0_2).
  reflexivity. easy. easy.
Qed.

Lemma subst_help :
  forall (v : var) (e x : expr) ,
    nonfv e ν ->
    nonfv x ν -> nonfv (subst (subst_one v e) x) ν.
Proof.
  intros.
  unfold subst_one. unfold subst. simpl.
  unfold NFV.
  induction x; simpl.
  + easy. 
  + destruct (eq_dec v v0); simpl. subst v.
    intuition.
    compute in H0. intuition.
  + easy.
  + intro. apply in_app_or in H1.
    simpl in H0. unfold NFV in H0. simpl in H0. 
    assert (nonfv x1 ν).
    intro.
    apply H0. apply in_or_app. left. easy.
    assert (nonfv x2 ν). 
    intro.
    apply H0. apply in_or_app. right. easy.
    intuition.
Qed.

Lemma subst_assign_eq_true :
  forall (v : var) b (e : expr),
    (v <> ν) -> nonfv e ν -> nonfv e v -> 
    sep_base e b
             |-- subst (subst_one v e) (sep_ty (var_e v) {ν : b | var_e ν .= e}).
Proof.
  intros.
  rewrite <- sep_ty_subst.
  setoid_rewrite subst_nonfv at 2.
  unfold subst_one. unfold subst. simpl. destruct (eq_dec v v).
  intro w.
  destruct ({ν : b | var_e ν .= e}) eqn: FOO.
  inv FOO.
  unfold sep_ty.
  simpl. apply andp_right. apply andp_right.
  normalize.
  pose (subst_nonfv (subst_one ν e) e).
  setoid_rewrite e1. apply andp_right. apply prop_right.
  unfold subst_one. destruct (eq_dec ν ν). reflexivity. congruence.
  apply sep_base_pure.
  intros v' X. intro. simpl in H0. unfold NFV in H0. 
  unfold subst_one in X. destruct (eq_dec ν v'). subst v'. congruence.
  congruence.
  apply sep_base_pure.
  congruence.
  intro v'. intro X.
  unfold nonfv. simpl. unfold nonfv_reft_t. split.
  unfold nonfv. simpl. destruct b; easy. 
  split. intro. unfold subst_one in X. destruct (eq_dec v v'). subst v'.
  unfold fv_expr in *. inv H2. congruence. inv H3. congruence.
  unfold subst_one in X. destruct (eq_dec v v'). subst v'. easy. congruence.
  unfold subst. simpl. unfold subst_one. destruct (eq_dec v ν).
  subst v. congruence. reflexivity.
  intros e' X.
  apply subst_help; easy.
Qed.

Lemma sep_base_eval :
  forall e τ φ,
    sep_base e (reft_base {ν : τ | φ}) |-- exp (eval_to e).
Proof.
  intros.
  unfold sep_base.
  destruct τ;
    simpl; intro w; try rewrite exp_andp1; try apply exp_left. 
    try eapply exp_right; unfold eval_to; normalize.
  intros.
  eapply exp_right. simpl. apply andp_right. rewrite H. apply prop_right. reflexivity. normalize.
  try eapply exp_right; unfold eval_to; simpl; normalize.
  unfold OkRef.
  unfold eval_to.
  simpl.
  rewrite <- exp_andp1.
  apply andp_right.
  apply andp_left1.
  rewrite andp_assoc.
  apply derives_extract_prop. intro.
  apply derives_extract_prop. intro.
  apply prop_left. intro.
  simpl in *.
  destruct (runloc w l). apply (exp_right (addr_v a)). normalize.
  congruence.
  repeat apply (andp_left2). easy.
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

(* Lemma subst_loc_expr : *)
(*   forall (s : subst_t loc loc) (e : expr), *)
(*     fl_expr e = [] -> *)
(*     subst s e = e. *)
(* Proof. *)
(*   intros. *)
(*   unfold subst.  *)
(*   simpl. *)
(*   induction e; simpl in *; try first [reflexivity | congruence]. *)
(*   apply app_eq_nil in H. *)
(*   rewrite IHe1; repeat (reflexivity || rewrite IHe2 || intuition). *)
(* Qed. *)

(* Lemma wf_expr_not_loc : *)
(*   forall (s : subst_t loc loc) e, *)
(*     fl_expr e = [] ->  *)
(*     forall w, eval w e = eval (subst s w) (* (stk w, fun l => runloc w (s l), hp w) *) e. *)
(* Proof. *)
(*   intros. *)
(*   induction e; eauto. *)
(*   inv H. *)
(*   simpl in *. *)
(*   apply app_eq_nil in H. *)
(*   intuition. *)
(*   rewrite H. *)
(*   rewrite H2. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma subst_loc_pred_prop' : *)
(*   forall (s : subst_t loc loc) (p : reft_prop), *)
(*     fl_prop p = [] -> *)
(*     forall x, sep_pred p x = subst s (sep_pred p) x. *)
(* Proof. *)
(*   intros until p. *)
(*   induction p; intro; eauto.  *)
(*   +  intro w. *)
(*      unfold sep_pred. *)
(*      unfold fl_prop in *. *)
(*      apply app_eq_nil in H. *)
(*      unfold subst_pred_loc. *)
(*      simpl. *)
(*      f_equal. *)
(*      intuition; repeat erewrite <- wf_expr_not_loc; eauto. *)
(*   + intro w. *)
(*     unfold subst_pred_loc in *. *)
(*     simpl. *)
(*     rewrite <- IHp. *)
(*     reflexivity. *)
(*     assumption. *)
(*   + intro w. *)
(*     unfold subst_pred_loc in *. *)
(*     simpl in *. *)
(*     apply app_eq_nil in H. *)
(*     rewrite <- IHp1; try solve [intuition; eauto]. *)
(*     rewrite <- IHp2; intuition; eauto. *)
(*   + intro w. *)
(*     unfold subst_pred_loc in *. *)
(*     simpl in *. *)
(*     apply app_eq_nil in H. *)
(*     rewrite <- IHp1; try solve [intuition; eauto]. *)
(*     rewrite <- IHp2; intuition; eauto. *)
(* Qed. *)

(* Lemma subst_pred_expr : *)
(*   forall {D R : Type}  *)
(*          {SE : Subst expr D R} *)
(*          {SA : Subst assert D R} *)
(*          {SAA : SubstAssert D R} *)
(*          (s : subst_t D R) e v, *)
(*     subst s e  *)

(* Lemma subst_loc_pred_prop : *)
(*   forall {D R : Type}  *)
(*          {S : Subst reft_prop D R}  *)
(*          {SE : Subst expr D R} *)
(*          {SR : SubstReft D R} *)
(*          {SA : Subst assert D R} *)
(*          {SAA : SubstAssert D R} *)
(*          (s : subst_t D R) p,  *)
(*     fl_prop p = [] -> *)
(*     sep_pred (subst s p) = subst s (sep_pred p). *)
(* Proof. *)
(*   Hint Transparent sep_pred. *)
(*   intros. *)
(*   induction p; intros. *)
(*   { *)
(*   rewrite subst_tt_r. *)
(*   unfold sep_pred; push_subst. *)
(*      admit.  *)
(*   } *)
(*   { *)
(*   rewrite subst_rel_r. *)
(*   unfold sep_pred; push_subst. *)
(*   simpl. *)
(*   extensionality. *)
(*   f_equal. *)
(* Qed. *)

(*   intros. *)
(*   unfold subst, Subst_prop_loc, subst_prop_loc. *)
(*   extensionality. *)
(*   erewrite <- subst_loc_pred_prop'; eauto. *)
(* Qed. *)

(* Lemma subst_base_loc : *)
(*   forall (s : loc -> loc) e b, *)
(*     fl_expr e = [] ->  *)
(*     sep_base (subst s e) (subst s b) = subst_pred_loc s (sep_base e b). *)
(* Proof. *)
(*   intros. *)
(*   unfold sep_base; destruct b; simpl; erewrite subst_loc_expr; eauto; unfold subst_pred_loc; extensionality. *)
(*   + f_equal. *)
(*     f_equal. *)
(*     extensionality. *)
(*     unfold eval_to. *)
(*     erewrite <- wf_expr_not_loc; eauto. *)
(*   + f_equal. *)
(*     f_equal. *)
(*     erewrite <- wf_expr_not_loc; eauto. *)
(*   + f_equal. *)
(*     f_equal. *)
(*     erewrite <- wf_expr_not_loc; eauto. *)
(*     erewrite <- wf_expr_not_loc; eauto. *)
(* Qed. *)

(* Lemma subst_prop_loc_var_comm : *)
(*   forall (p : reft_prop) (s1 : subst_t var expr) (s2 : subst_t loc loc), *)
(*     subst s1 (subst s2 p) = subst s2 (subst s1 p). *)
(* Proof. *)
(*   intros. *)
(*   rewrite subst_nonfv. *)
(* Qed. *)

(* Lemma subst_fl_closed_expr : *)
(*   forall v x e, *)
(*     fl_expr x = [] -> *)
(*     fl_expr e = [] -> *)
(*     fl_expr (subst (subst_one v x) e) = []. *)
(* Proof. *)
(*   intros; *)
(*   induction e; try reflexivity. *)
(*   + unfold subst, subst_one. simpl. *)
(*     destruct (eq_dec v0 v); assumption.  *)
(*   + inv H0. *)
(*   + simpl in *. *)
(*     apply app_eq_nil in H0. *)
(*     destruct H0. *)
(*     unfold subst in IHe1. *)
(*     unfold subst in IHe2. *)
(*     rewrite IHe1. *)
(*     rewrite IHe2. *)
(*     reflexivity. *)
(*     assumption. *)
(*     assumption. *)
(* Qed. *)

(* Lemma subst_fl_closed_prop : *)
(*   forall v x p, *)
(*     fl_expr x = [] -> *)
(*     fl_prop p = [] -> *)
(*     fl_prop (subst (subst_one v x) p ) = []. *)
(* Proof. *)
(*   intros. *)
(*   induction p. *)
(*   + reflexivity. *)
(*   + simpl in *. *)
(*     unfold subst. *)
(*     apply app_eq_nil in H0. *)
(*     repeat rewrite subst_fl_closed_expr; try (reflexivity || apply H || apply H0). *)
(*   + auto. *)
(*   + simpl in *. *)
(*     apply app_eq_nil in H0. *)
(*     unfold subst in *. *)
(*     rewrite IHp1. *)
(*     rewrite IHp2. *)
(*     reflexivity. *)
(*     apply H0. *)
(*     apply H0. *)
(*   + simpl in *. *)
(*     apply app_eq_nil in H0. *)
(*     unfold subst in *. *)
(*     rewrite IHp1. *)
(*     rewrite IHp2. *)
(*     reflexivity. *)
(*     apply H0. *)
(*     apply H0. *)
(* Qed. *)

(**

Lemma subst_ty_loc :
  (* forall {D R : Type} {S : Subst assert D R} {Sa : SubstAssert D R} {St : Subst reft_type D R} {Sp : Subst reft_prop D R} {Se : Subst expr D R} (s : subst_t D R) x T, *)
  forall x T (s : subst_t loc loc),
  (forall (l : loc), nonfv x l) ->
  (forall (l : loc), nonfv (reft_r T) l) ->
  (forall (x : expr), nonfv x ν -> nonfv (subst s x) ν) ->
    sep_ty (subst s x) (subst s T) = subst s (sep_ty x T).
Proof.
  intros.
  destruct T as [b p].
  setoid_rewrite sep_ty_subst.
  reflexivity.
  unfold subst. simpl. reflexivity.
  intros. 
  apply H1.
  easy.
Qed.

Lemma subst_heap_loc'' :
  forall (s : subst_t loc loc) L,
    Forall (fun lxt => (forall (l : loc), nonfv (reft_r (snd (snd lxt))) l)) L ->
    (subst s
      (fold_right (fun lxt a => sep_heap_bind (fst lxt) (snd lxt) * a) emp L)
   = fold_right (fun lxt a => sep_heap_bind (fst lxt) (snd lxt) * a) emp (subst s L)).
Proof.
  intros.
  induction L as [ | [l [x t]]].
  reflexivity.
  push_subst.
  unfold fold_right at 2.
  unfold fold_right at 2 in IHL.
  rewrite <- IHL.
  unfold fold_right.
  push_subst.
  f_equal.
  unfold fst, snd.
  unfold sep_heap_bind. 
  extensionality w.
  push_subst.
  f_equal. f_equal.
  rewrite (subst_ty_loc s (var_e x)).
  reflexivity.
  reflexivity.
  inv H. eauto with datatypes.
  inv H; assumption.
Qed.

Lemma helper :
  forall l1 l2,
    NoDupA eqk l1 -> NoDupA eqk l2 -> 
    (forall (lxt : (loc * type_binding)), InA eqA lxt l1 <-> InA eqA lxt l2) ->
    Equal (HE_Props.of_list l1) (HE_Props.of_list l2).
Proof.
  intros.
  rewrite HE_Props.F.Equal_mapsto_iff.
  intros l xt.
  specialize (H1 (l,xt)).
  apply HE_Props.of_list_1 with (k := l) ( e := xt) in H.
  apply HE_Props.of_list_1 with (k := l) ( e := xt) in H0.
  rewrite H.
  rewrite H0.
  destruct H1.
  split.
  intro.
  apply H1. assumption.
  intro.
  apply H2. assumption.
Qed.

Lemma thingie' :
  forall {D R : Type} {Sl : Subst loc D R} {St : Subst type_binding D R } 
         s (x y : loc * type_binding),
    (forall (l m : loc), subst s l = subst s m -> l = m) ->
    eqk (subst s x) (subst s y) -> eqk x y.
Proof.
  intros.
  destruct x as [l xt].
  destruct y as [m yt].
  inv H0.
  apply H in H2.
  subst.
  reflexivity.
Qed.

Lemma thingie :
  forall {D R : Type} {S : Subst loc D R } {S' : Subst type_binding D R} 
         (s : subst_t D R) (e : (loc * type_binding)) l,
    (forall (l m : loc), subst s l = subst s m -> l = m) ->
    InA eqk (subst s e) (subst s l) -> InA eqk e l.
Proof.
  intros.
  induction l.
  + inv H0.
  + rewrite subst_cons in H0.
    inv H0.
    left.
    apply (thingie' s). 
    assumption.
    apply H2.
    right.
    apply IHl.
    assumption.
Qed.

Lemma NoDupA_subst_heap_binds :
  forall {D R : Type} {S : Subst loc D R } {S' : Subst type_binding D R } 
         s (L : list (loc * type_binding)),
    (forall (l m : loc), subst s l = subst s m -> l = m) ->
    NoDupA eqk L ->
    NoDupA eqk (subst s L).
Proof.
  intros.
  induction L as [ | [l xt]].
  + eauto.
  + push_subst.
    apply NoDupA_cons.
    intro.
    inv H0.
    apply H4.
    apply (thingie s).
    assumption.
    assumption.
    apply IHL.
    inv H0; assumption.
Qed.

Lemma NoDup_Heap :
  forall {D R : Type} {S : Subst loc D R} {S' : Subst type_binding D R} s H,
    (forall (l m : loc), s l = s m -> l = m) ->
    (forall lxt, InA eqA lxt (elements (subst s H)) <-> 
                InA eqA lxt (subst s (elements H))).
Proof.
  intros.
  unfold subst.
  destruct lxt as [l xt].
  pose (HE_Props.of_list_1).
  specialize (i type_binding (subst s (HE_Props.to_list H)) l xt).
  split.
  intro.
  apply i.
  apply NoDupA_subst_heap_binds. assumption.
  apply elements_3w.
  apply HE_Props.F.elements_mapsto_iff.
  assumption.
  intro.
  apply i.
  apply NoDupA_subst_heap_binds. assumption.
  apply elements_3w.
  assumption.
Qed.

Lemma subst_eq_heaps :
  forall {D R : Type} {S : Subst loc D R} {S' : Subst type_binding D R} s H,
    (forall (l m : loc), s l = s m -> l = m) ->
    Equal (subst s H) (HE_Props.of_list (subst s (elements H))).
Proof.
  intros.
  assert (forall lxt, InA eqA lxt (elements (subst s H)) <-> InA eqA lxt (subst s (elements H)))
  by (apply NoDup_Heap; assumption).
  assert (Equal (HE_Props.of_list (elements (subst s H))) (HE_Props.of_list (subst s (elements H)))).
  apply helper.
  apply elements_3w.
  apply NoDupA_subst_heap_binds.
  assumption.
  apply elements_3w.
  apply H1.
  rewrite HE_Props.of_list_3 in H2.
  assumption.
Qed.  

Instance EQA_EQUIVALENCE : Equivalence eqA := _.
Instance EQK_EQUIVALENCE : Equivalence eqk := _.

Lemma heap_equiv_elements_subst :
  forall {D R : Type} {S : Subst loc D R} {S' : Subst type_binding D R} H s,
    (forall (l m : loc), s l = s m -> l = m) ->
    equivlistA
      eqA
      (rev (elements (HE_Props.of_list (subst s (elements H)))))
      (subst s (rev (elements H))).
Proof.
  intros.
  push_subst.
  pose (@HE_Props.of_list_2 type_binding).
  cut (forall l l', equivlistA eqA l l' -> equivlistA eqA (rev l) (rev l')).
  intros.
  symmetry.
  apply H1.
  apply HE_Props.of_list_2.
  apply NoDupA_subst_heap_binds.
  assumption.
  apply elements_3w.
  intros.
  intro. destruct H1 with (x := x).
  constructor; intros; apply InA_rev; try apply EQA_EQUIVALENCE;
  [ apply H2 | apply H3]; apply InA_rev; try apply EQA_EQUIVALENCE; assumption.
Qed.

Lemma heap_free_locs :
  forall (h : heap_env),
    (forall l x t, MapsTo l (x,t) h -> fl_prop (reft_r t) = []) ->
    (forall l x t, List.In (l,(x,t)) (elements h) -> fl_prop (reft_r t) = []).
Proof.
  intros.
  apply H with (l := l) (x := x).
  apply In_InA with (eqA := eqA) in H0.
  apply HE_Facts.elements_mapsto_iff.
  apply H0.
  apply EQA_EQUIVALENCE.
Qed.

Lemma subst_heap_loc :
  forall {D R : Type} {S : Subst loc D R} {S' : Subst type_binding D R} {SA: Subst assert D R}
         (s : subst_t D R) H,
    (forall l x t, MapsTo l (x,t) H -> fl_prop (reft_r t) = []) ->
    (forall (l m : loc), subst s l = subst s m -> l = m) ->
    sep_heap (subst s H) = subst s (sep_heap H).
Proof.
  intros.
  unfold sep_heap at 2.
  rewrite HE_Props.fold_spec_right.
  rewrite subst_heap_loc''.
  unfold sep_heap.
  rewrite HE_Props.fold_Equal with (m1 := subst s H) (m2 := HE_Props.of_list (subst s (elements H))).
  rewrite fold_1.
  rewrite <- fold_left_rev_right.
  rewrite 
    (fold_right_equivlistA).
    auto.
    apply HE_Props.eqke_equiv.
    apply EQ_EQUIVALENCE.
    destruct x. destruct y.
    intros. inv H2. simpl in *. subst. reflexivity.
    hnf. intros. 
    simpl. extensionality ρ. 
    do 2 rewrite <- sepcon_assoc.
    rewrite sepcon_comm with (P := sep_heap_bind (fst x) (snd x) (ρ)).
    reflexivity.
    apply NoDupA_rev. apply EQA_EQUIVALENCE. 
    apply HE_Props.NoDupA_eqk_eqke.
    apply elements_3w.
    apply HE_Props.NoDupA_eqk_eqke.
    apply NoDupA_subst_heap_binds.
    assumption.
    apply NoDupA_rev. 
    apply EQK_EQUIVALENCE.
    apply elements_3w.
    apply heap_equiv_elements_subst.
    assumption.
    apply EQ_EQUIVALENCE.
    solve_proper.
    hnf. intros. 
    simpl. extensionality ρ. 
    do 2 rewrite <- sepcon_assoc.
    rewrite sepcon_comm with (P := sep_heap_bind k e (ρ)).
    reflexivity.
    apply subst_eq_heaps.
    assumption.
    rewrite Forall_forall.
    intros.
    rewrite <- in_rev in H2.
    destruct x as [l [x t]].
    eapply heap_free_locs; eauto.
Qed.
**)

(* Lemma subst_ctx_loc : *)
(*   forall G s, *)
(*     (Forall (fun xt => fl_prop (reft_r (snd xt)) = []) G) -> *)
(*     sep_env (@subst _ _ _ (Subst_list (var * reft_type) loc loc (Subst_prod _ _ _ _ _ _)) s G) *)
(*     = subst s (sep_env G). *)
(* Proof. *)
(*   intros. *)
(*   induction G as [ | [x t]]. *)
(*   + reflexivity. *)
(*   + push_subst. *)
(*     unfold sep_env; fold sep_env. *)
(*     simpl. *)
(*     extensionality w. *)
(*     unfold subst, Subst_pred_loc, subst_pred_loc. *)
(*     f_equal. f_equal. *)
(*     rewrite (subst_ty_loc s (var_e x)). *)
(*     reflexivity. *)
(*     reflexivity. *)
(*     rewrite Forall_forall in *. specialize (H (x, t)). apply H. left. reflexivity. *)
(*     unfold subst in IHG. *)
(*     rewrite IHG. reflexivity.  *)
(*     inv H. assumption. *)
(* Qed. *)

Ltac lift_apply l :=
  let X := fresh "X" in
  try (simpl; intro); pose l as X; simpl in X; eapply X; clear X. 

Lemma subtype_args :
  forall Γ Ξ Σ Σm args Σarg,
    tc_list Γ Σ Ξ args ->
    heap_subtype Γ Ξ Σm Σarg ->
  sep_env Γ && sep_guards Ξ * sep_heap Σm
   |-- sep_env args * sep_heap Σarg * (sep_env Γ && sep_guards Ξ).
Proof.
  intros.
  rewrite <- andp_dup with (P := sep_env Γ && sep_guards Ξ) at 1.
  rewrite <- sepcon_pure_andp with (P := sep_env Γ && sep_guards Ξ); try do_pure.
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  apply sepcon_derives.
  rewrite <- andp_dup with (P := sep_env Γ && sep_guards Ξ) at 1.
  rewrite <- sepcon_pure_andp with (P := sep_env Γ && sep_guards Ξ); try do_pure.
  rewrite <- sepcon_assoc.
  rewrite sepcon_comm.
  apply sepcon_derives.
  eauto using types_interp.
  rewrite sepcon_comm.
  eauto using heap_subtype_interp.
  apply derives_refl.
Qed.

Notation "S · T" := (subst S T) (right associativity, at level 60).
(* Lemma loc_sub_proc_call : *)
(*   forall (θ : subst_t loc loc) f xs x mxs mls, *)
(*     (θ·proc_s f xs x mxs mls) = proc_s f xs x mxs (θ·mls). *)
(* Proof. *)
(*   Admitted. *)

Lemma loc_sub_var2var :
  forall (θ : subst_t loc loc), var_2_var θ.
Proof.
  firstorder.
Qed.

Lemma var_sub_var2var :
  forall (θ : subst_t var var), var_2_var θ.
Proof.
  firstorder.
Qed.

Lemma wf_subst_vv_nonfv :
  forall (θ : subst_t var var),
    wf_subst θ  ->
    ∀ x0 : expr, nonfv x0 ν → nonfv (θ · x0) ν.
Proof.
  intros. unfold wf_subst in *.
  induction x0; simpl nonfv in *; unfold NFV in *; simpl fv_expr in *.
  + trivial.
  + destruct (H v). intuition. simpl subst in *.
    destruct H3; intuition.
  + trivial.
  + intro. apply in_app_or in H1. destruct H1; intuition.
Qed.

Lemma loc_subst_vv_nonfv :
  forall (θ : subst_t loc loc), 
    forall (e : expr), nonfv e ν -> nonfv (θ · e) ν.
Proof.
  intros.
  induction e; simpl nonfv in *; unfold NFV in *; simpl fv_expr in *; trivial.
  intro. apply in_app_or in H0. destruct H0; intuition.
Qed.
(**
Lemma MapsToSubst' :
  forall (θ : subst_t loc loc) h l x t,
    (MapsTo l (x, t) (θ · h) ->
    (exists (l' : loc) x' t', (l = θ · l') /\ (x = θ · x') /\ (t = θ · t') /\ MapsTo (θ · l') (θ · x', θ · t') (θ · h))).
Proof.
  intros until t0.
  simpl subst at 1 8.
  unfold subst_heap.
  (* unfold NonUnifyingSub. *)
  apply HE_Props.fold_rel with 
  (f := fun l xt a => add (θ · l) (θ·xt) a)
  (g := fun l xt a => add (θ · l) (θ·xt) a)
  (R := fun A B => 
          MapsTo l (x, t0) A -> 
          (exists l' x' t', (l = θ · l') /\ (x = θ · x') /\ (t0 = θ · t') /\ MapsTo (θ · l') (θ · x', θ · t') B)).
  intros. inv H.
  intros.
  rewrite HE_Props.F.add_mapsto_iff in H1.
  decompose [and or] H1; clear H1.
  destruct e.
  simpl subst in H4. unfold Subst.subst_prod in H4. inv H4.
  setoid_rewrite HE_Props.F.add_mapsto_iff.
  exists k. exists v. exists r. repeat split. left. intuition.
  apply H0 in H4. destruct H4. destruct H1. destruct H1. decompose [and] H1. clear H1.
  exists x0. exists x1. exists x2. repeat split. easy. easy. easy.
  apply HE_Props.F.add_mapsto_iff.
  right. subst l. intuition.
Qed.

Lemma MapsToSubst :
  forall (θ : subst_t loc loc) h l x t,
    (MapsTo l (x, t) (θ · h) ->
    (exists (l' : loc) x' t', MapsTo (θ · l') (θ · x', θ · t') (θ · h))).
Proof.
  intros. apply MapsToSubst' in H. destruct H. destruct H.  destruct H. exists x0, x1, x2.
  intuition.
Qed.
  
Lemma nonunifying_closed :
  forall (θ : subst_t var var)  (θ' : subst_t loc loc) h,
    NonUnifyingSub θ h -> NonUnifyingSub θ' h -> NonUnifyingSub θ (θ θ' · h).
Proof.
  intros.
  unfold NonUnifyingSub in *.
  decompose [and] H. clear H.
  decompose [and] H0. clear H0.
  split. trivial.
  intros l x t.
  split.
  intro M.
  destruct (H3 l x t).
  destruct (H2 l x t).
  apply MapsToSubst in M.
  destruct M as [l' M]. destruct M as [x' M]. destruct M as [t' M].
  rewrite <- H3 in M.
  rewrite H2 in M.
**)
Lemma subst_vv_fresh :
  forall (s : subst_t var var),
    wf_subst s ->
    s · (var_e ν) = var_e ν.
Proof.
  intros.
  unfold wf_subst in *.
  destruct (H ν).
  simpl subst in  *. simpl in *.
  rewrite H1; reflexivity.
Qed.

Hint Resolve loc_sub_var2var var_sub_var2var loc_subst_vv_nonfv wf_subst_vv_nonfv subst_vv_fresh : subst.

Definition unique_sub' P (s : subst_t var var) (x : var) :=
  forall v, P v -> x <> v -> nonfv (subst s v) (subst s x).

Goal forall s x, unique_sub' (fun _ => True) s x -> unique_sub s x.
Proof.
  firstorder.
Qed.

Lemma bind_in_empty_false :
  forall (x : var) h,
    bind_in x h -> ~ Empty h.
Proof.
  intros.
  intro.
  assert (elements h = []). apply HE_Props.elements_Empty. easy.
  unfold bind_in in *.
  instantiate_ex.
  rewrite <- HE_Props.F.find_mapsto_iff in *.
  rewrite HE_Props.F.elements_mapsto_iff in *.
  unfold type_binding in *.
  rewrite  H1 in *.
  inversion H.
Qed.

Lemma wf_unique_binds :
  forall (x : var) l l' t t' g h h',
    l <> l' ->
    wf_heap g h h' ->
    MapsTo l (x,t) h' ->
    MapsTo l' (x,t') h' ->
    False.
Proof.
  intros.
  unfold wf_heap in *.
  decompose_all.
  apply H. 
  specialize (H3 l l' x t0 t').
  apply H3. split; assumption.
Qed.

Lemma unique_binds_neq :
  forall (x x': var) l t t' (h : heap_env),
    MapsTo l (x, t) h ->
    MapsTo l (x', t') h ->
    x = x'.
Proof.
  intros. 
  rewrite HE_Props.F.find_mapsto_iff in *.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

Lemma modvars_unique_sub :
  forall (x : var) (s : subst_t var var) S,
    NonUnifyingSub s (s_heap_out S) ->
    NonUnifyingSub s (s_heap_in S) ->
    List.In x (mod_vars S) ->
    unique_sub s x.
Proof.
  intros.
  exists (subst s x).
  split. reflexivity.
  intro x'. intro neq. unfold nonfv. simpl. intro.
  destruct S as [xs ts hi ho xt]. simpl in *.
  apply_in_env new_mod_vars_schema.
  unfold NonUnifyingSub in *.
  decompose_all.
  unfold bind_in in *.
  instantiate_ex.
  rewrite <- HE_Props.F.find_mapsto_iff in *.
  assert (MapsTo x0 (x', x1) ho).
  rewrite H5. simpl subst at 2. rewrite H2. rewrite <- H5. assumption.
  contradiction neq.
  eapply unique_binds_neq; eauto.
Qed.

Lemma modlocs_unique_sub :
  forall (l : loc) (s : subst_t loc loc) (s' : subst_t var var) S,
    NonUnifyingSub s (subst s' (s_heap_out S)) ->
    List.In l (mod_locs S) ->
    unique_lsub s l.
Proof.
  intros.
  repeat intro.
  unfold NonUnifyingSub in *.
  decompose_all.
  apply H in H1.
  congruence.
Qed.

Lemma locs_var_sub :
  forall (s : subst_t var var) (L : list loc),
    subst s L = L.
Proof. 
  induction L. reflexivity.
  rewrite subst_cons.
  rewrite IHL.
  f_equal.
Qed.

(* Lemma wf_heap_bind_not_in_env : *)
(*   forall x G H, *)
(*     wf_heap G H H -> *)
(*     bind_in x H ->  *)
(*     ~ var_in x G. *)
(* Proof. *)
(*   intros. *)
(*   intro. *)
(*   induction H0. *)
(*   + eapply bind_in_empty_false; eauto. *)
(*   + unfold bind_in in *. *)
(*     instantiate_ex. rewrite <- HE_Props.F.find_mapsto_iff in *. *)
(*     rewrite HE_Props.F.add_mapsto_iff in *. *)
(*     decompose_all; decompose_all. *)
(*     inv H7. *)
(*     apply_in_env fresh_var_not_in. intuition. *)
(*     apply IHwf_heap. exists x1. exists x2. rewrite <- HE_Props.F.find_mapsto_iff. *)
(*     easy. easy. *)
(* Qed. *)

Lemma fresh_loc_not_mem' :
  forall G H (l : loc),
    fresh_loc l G H -> forall xt, ~ MapsTo l xt H.
Proof.
  intros.
  intro.
  unfold fresh_loc in H0.
  destruct H0.
  simpl nonfv in *.
  unfold nonfv_heap in *.
  apply H2 in H1. intuition.
Qed.


Lemma fresh_loc_not_mem :
  forall G H (l : loc),
    fresh_loc l G H -> ~ In l H.
Proof.
  intros.
  intro.
  rewrite HE_Props.F.in_find_iff in *.
  assert (exists xt, find l H = Some xt).
  destruct (find l H). exists t0. reflexivity.
  congruence.
  instantiate_ex.
  eapply fresh_loc_not_mem' in H0.
  rewrite HE_Props.F.find_mapsto_iff in *.
  apply H0.
  apply H2.
Qed.

(* Lemma remove_add_inv : *)
(*   forall (h : heap_env) l e, *)
(*     ~ In l h ->  *)
(*     Equal (remove l (add l e h)) h. *)
(* Proof. *)
(*   setoid_rewrite HE_Props.F.Equal_mapsto_iff. *)
(*   intros. *)
(*   symmetry. *)
(*   rewrite HE_Props.F.find_mapsto_iff in *. *)
(*   rewrite HE_Props.F.find_mapsto_iff in *. *)
(*   compare l k. *)
(*   intros.  *)
(*   split. intro. rewrite HE_Props.F.not_find_in_iff in *. congruence. *)
(*   intro.  *)
(*   rewrite HE_Props.F.remove_eq_o in H0. congruence. assumption. *)
(*   intros. *)
(*   rewrite HE_Props.F.remove_neq_o. *)
(*   rewrite HE_Props.F.add_neq_o. reflexivity. *)
(*   assumption. *)
(*   assumption. *)
(*   apply eq_dec. *)
(* Qed. *)

Instance Proper_add l x t (h : heap_env) :
  Proper (Equal ==> iff) (HE_Props.Add l (x,t) h).
Proof. 
  unfold HE_Props.Add.
  solve_proper.
Qed.

Lemma wf_expr_Equal_heaps :
  forall G H H' e,
    Equal H H' ->
    wf_expr G H e ->
    wf_expr G H' e.
Proof.
  intros.
  induction H1; eauto with wf.
  + apply wf_var_hp.
    unfold bind_in in *.
    instantiate_ex.
    exists x. exists x0.
    solve_by_rewrite.
Qed.

Hint Resolve wf_expr_Equal_heaps : wf.

Lemma wf_pred_Equal_heaps :
  forall G H H' p,
    Equal H H' -> wf_prop G H p -> wf_prop G H' p.
Proof.
  intros.
  induction H1; eauto with wf.
Qed.

Hint Resolve wf_pred_Equal_heaps : wf.
Lemma wf_ty_Equal_heaps :
  forall G H H' b p,
    Equal H H' -> wf_type G H { ν : b | p } ->
    wf_type G H' { ν : b | p }.
Proof.
  intros.
  constructor.
  inv H1.
  eauto with wf.
Grab Existential Variables.
exact (int_t).
Qed.
Hint Resolve wf_ty_Equal_heaps : wf.

Lemma wf_Equal_heaps :
  forall G H H',
    wf_heap G H H' -> forall H'', Equal H' H'' -> wf_heap G H H''.
Proof.
  intros.
  unfold wf_heap in *.
  split.
  intros.
  destruct t0.
  decompose_all.
  eapply wf_ty_Equal_heaps. hassumption.
  rewrite <- H1 in H2.
  eapply H0. eauto.
  intros l' l'' x t' t''.
  intro MT. decompose_all.
  rewrite <- H1 in *.
  eapply H4. split; eauto.
Qed.

(** 
Lemma wf_heap_split : 
  forall G Ho H,
    wf_heap G Ho H ->
         forall H1 H2,
           heap_split H1 H2 H -> wf_heap G Ho H1.
Proof.
  intros.
  unfold heap_split in *.
  unfold HE_Props.Partition in *.
  split. intros.
  unfold wf_heap in *.
  decompose_all.
  assert (MapsTo l (x, t0) H).
  apply H5. left. assumption.
  
  split.
  
  intros until H. intro. 
  intros H'
  induction H0; intros.
  + split; constructor; unfold heap_split in *;
    apply_in_env HE_Props.Partition_Empty;
    intuition.
  + 
    unfold heap_split in *.
    assert (~ In l Σ0).
    apply_in_env fresh_loc_not_mem; easy.
    (* assert (HE_Props.Add l (x, t0) Σ0 (add l (x, t0) Σ0)) by firstorder. *)
    pose (@HE_Props.Partition_Add type_binding Σ0 Σ0' l (x,t0) H8 H4 H5 H6 H7). 
    instantiate_ex.
    decompose_all; decompose_all.
    split.
    apply wf_heap_bind with (l := l) (x := x) (t := t0) (Σ0 := x0); eauto with heaps.
    specialize (IHwf_heap x0 H6).
    apply IHwf_heap. assumption.
    apply (IHwf_heap x0 H6). assumption.
    split.

    apply IHwf_heap in H10. apply H10.
    

    assert (HE_Props.Partition Σ0 x0 H5). unfold HE_Props.Partition in *.
    split.
    apply HE_Props.Disjoint_sym.
    easy. intros. split; intro. apply H10 in H11. destruct H11. right. easy. left. easy.
    apply H10. destruct H11. right. easy. left. easy.
   
    apply wf_heap_bind with (l := l) (x := x) (t := t0) (Σ0 := x0); eauto with heaps.
    apply IHwf_heap in H11. apply H11.
Qed.

Corollary wf_heap_split_1 :
  forall G Ho H1 H2 H,
    wf_heap G Ho H -> heap_split H1 H2 H -> wf_heap G Ho H1.
Proof.
  intros.
  apply_in_env (wf_heap_split G Ho); eauto.
  destruct H3. auto.
Qed.

Corollary wf_heap_split_2 :
  forall G Ho H1 H2 H,
    wf_heap G Ho H -> heap_split H1 H2 H -> wf_heap G Ho H2.
Proof.
  intros.
  apply_in_env heap_split_comm.
  eauto using wf_heap_split_1.
Qed.

Hint Resolve wf_heap_split_1 wf_heap_split_2 : heaps.
**)

Lemma nonfv_wf_cons :
  forall (x : var) t g (h : heap_env),
    wf_env h ((x,t) :: g) -> nonfv (sep_env g) x.
Proof.
  intros.
  inv H.
  clear H8.
  induction H7. 
  + easy.
  + step. apply nonfv_andp. split. apply nonfv_andp. split. apply SubstTy_var.
    inv H3. simpl nonfv. unfold NFV. simpl. intro. inv H3. apply H9. reflexivity. easy.
    rewrite bind_not_in_and_in in *.
    eapply nonmem_var_type_fv; eauto.
    rewrite var_not_in_and_in in *.
    intro.
    apply H3. unfold var_in in *. instantiate_ex. exists x1. right. assumption.
    apply IHwf_env. inv H3. assumption. assumption.
    easy.
Qed.

Lemma subst_list_length : 
  forall (s : subst_t var var) (l1 : list var) (l2 : list reft_type),
    length l1 = length l2 -> 
    length (subst s l1) = length (subst s l2).
Proof.
  intros until l1.
  induction l1; intros; destruct l2; try easy.
  simpl length.
  simpl subst in IHl1. erewrite IHl1. reflexivity. 
  inv H. reflexivity.
Qed.

Lemma weaken_env :
  forall x t h Γ Ξ,
     sep_ty x t * sep_heap h * (sep_env Γ && sep_guards Ξ)
   |-- sep_ty x t && sep_env Γ && emp && sep_guards Ξ * sep_heap h.
Proof.
  intros.
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  apply sepcon_derives.
  rewrite sepcon_pure_andp; try do_pure.
  apply andp_right. apply andp_right. apply andp_right. apply andp_left2. apply derives_refl.
  do 2 apply andp_left1. apply derives_refl.
  do_pure.
  apply andp_left1. apply andp_left2. apply derives_refl.
  apply derives_refl.
Qed.

Lemma sep_proof_proc_call :
    forall Φ Γ Γ' Σ Σ' Ξ f xs mxs mls r,
    wf_env Σ Γ ->
    wf_heap Γ Σ Σ ->
    wf_guards Γ Ξ ->
    ((Φ ; Γ ; Σ ; Ξ) ⊢ proc_s f xs r mxs mls ::: ( Γ' ; Σ')) ->
    (* ((Φ ; Γ ; Σ ; Ξ) *)
    (*    ⊢ proc_s f (subst θ (s_formals S)) (subst θ (fst (s_ret S))) [] ::: (Γ' ; Σ')) -> *)
    semax (sep_proc_env Φ)
          ((sep_env Γ && sep_guards Ξ) * sep_heap Σ)
          (proc_s f xs r mxs mls)
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
  fix_assert; eauto using subtype_args. 
  (** Q' ==> Q **)
  fix_assert. eauto using weaken_env.
  apply semax_frame with (R := sep_env Γ && sep_guards Ξ).
  unfold isub in *.
  setoid_rewrite <- subst_combine.
  setoid_rewrite <- subst_combine.
  assert (sep_heap (subst θl (subst θ hi)) = subst θl (sep_heap (subst θ hi))).
  apply sep_heap_subst; eauto with subst. 
  rewrite H2.
  assert (sep_heap (subst θ hi) = subst θ (sep_heap  hi)).
  apply sep_heap_subst; eauto with subst. 
  rewrite H3.
  assert (sep_heap (subst θl (subst θ ho)) = subst θl (sep_heap (subst θ ho))).
  apply sep_heap_subst; eauto with subst.
  rewrite H4.
  assert (sep_heap (subst θ ho) = subst θ (sep_heap ho)).
  apply sep_heap_subst; eauto with subst.
  rewrite H5.
  destruct t as [r P]. fold { ν : r | P }.
  setoid_rewrite sep_ty_subst; try eauto with subst.
  setoid_rewrite sep_ty_subst; try eauto with subst.
  (* assert (sep_env (subst θl (subst θ (combine xs ts))) = subst ?θl (sep_env (subst θ (combine xs ts)))). *)
  setoid_rewrite sep_env_subst; try eauto with subst.
  setoid_rewrite sep_env_subst; try eauto with subst.
  repeat rewrite <- subst_sepcon.
  assert ( forall mxs0 mls0, subst θl (subst θ (proc_s f xs x mxs0 mls0)) = proc_s f (subst θl (subst θ xs))
                                                              (subst θl (subst θ x))
                                                              (subst θl (subst θ mxs0))
                                                              (subst θl (subst θ mls0))).
  reflexivity.
  simpl subst in H6.
  rewrite <- H6.
  apply semax_subst_loc.
  pose semax_subst.
  simpl subst in s.
  apply s.
  set (S := mkSchema xs ts hi ho (x, { ν : r | P})).
  set (foo := mkProc xs x (mod_vars S) (mod_locs S) p). 
  assert (xs = p_args foo). reflexivity.
  assert (x = p_ret foo). reflexivity.
  assert (mod_vars S = p_mod foo). reflexivity.
  assert (mod_locs S = p_modl foo). reflexivity.
  rewrite H7. rewrite H20. rewrite H21. rewrite H22.
  apply semax_proc.
  match goal with
    | H : _ |- _ => apply sep_schema_in_env in H; unfold sep_schema in H; apply H
  end.
  intro mv.
  intro mvs.
  inv mvs.
  eapply modvars_unique_sub; eauto. eauto. eauto.
  exists (subst θ mv). split. reflexivity. intro x'. intro neq.
  simpl nonfv. simpl.
  intro.
  unfold subst_var_loc in *. 
  rewrite H17 in H7. congruence.
  intro ml.
  intro mls.
  inv mls.
  set (S := mkSchema xs ts hi ho (x, { ν : r | P})).
  apply modlocs_unique_sub with (s' := θ) (S := S); eauto.
  assert (mod_locs S = subst θ (mod_locs S)).
  rewrite locs_var_sub. reflexivity.
  rewrite H7.
  assumption.
  inv H13. apply H2.
  apply subst_list_length.
  inv H13. apply H2.
  unfold subset.
  intros.
  inv H2.
  pose (nonfv_andp (D := var)). simpl nonfv in n. apply n.
  split.
  eapply var_nonmem_free_ctx; eauto.
  apply H19.
  apply H21.
  eapply var_nonmem_free_grd'.
  apply H19.
  apply H21.
  auto.
  auto.
  pose (nonfv_andp (D := var)). simpl nonfv in n. apply n. split.
  eapply nonfv_wf_cons; eauto.
  inv H24.
  rewrite var_not_in_and_in in *. rewrite bind_not_in_and_in in *.
  eapply var_nonmem_free_grd; eauto with var.
  unfold subset.
  intros.
  inv H2.
  apply fv_var_sep_heap.
  eapply heap_split_nonfv.
  apply H15.
  apply H19. apply H21.
  apply fv_var_sep_heap.
  eapply heap_split_nonfv.
  apply H15.
  apply H19.
Qed.
    
Ltac solve_sub := match goal with
                      | H : @nonfv _ _ _ _ _ ?v |- appcontext[@subst_one _ _ _ ?v _] =>
                        simpl nonfv in H;
                          unfold nonfv_assert in H;
                          simpl; setoid_rewrite <- H;
                          eauto using andp_left1, andp_left2, derives_refl
                    end.
Ltac nfv_env :=
  match goal with
    | |- context[@subst _ _ _ _ (subst_one ?v _) ?P] =>
      assert (nonfv P v); eauto using var_nonmem_free_ctx, var_nonmem_free_grd, var_nonmem_free_grd'
      ; solve_sub
  end.
  

Lemma sep_proof_assign :
  forall Φ Ξ Γ Σ τ v e,
    wf_env Σ Γ ->
    wf_heap Γ Σ Σ ->
    wf_guards Γ Ξ ->
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
              && subst (subst_one v e) (sep_env ((v, {ν : τ | (var_e ν) .= e}) :: Γ) && sep_guards Ξ))
     (Q' := (sep_env ((v, {ν : τ | (var_e ν) .= e}) :: Γ) && sep_guards Ξ)).
  unfold sep_env at 2; fold sep_env.
  normalize.
  rewrite <- exp_andp1.
  apply andp_right.
  apply andp_left1.
  eapply derives_trans.
  eapply expr_eval_ty' with (T := { ν : τ | φ}); eauto.
  eapply sep_base_eval.
  repeat rewrite subst_andp.
  repeat apply andp_right.
  apply derives_trans with (Q := sep_base e τ).
  apply andp_left1.
  eapply expr_eval_ty' with (T := { ν : τ | φ }); eauto.
  apply subst_assign_eq_true.
  apply H10.
  eapply vv_not_fv; eauto.
  intro; eapply fresh_var_expr_fv; eauto.
  eapply expr_type_wf; eauto.
  apply andp_left1.
  nfv_env.
  apply andp_left1. apply sep_env_pure.
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
    wf_guards Γ Ξ ->
    stmt_type Φ Γ Σ Ξ s Γ' Σ' ->
    sep_proc_env Φ |- {{ sep_env Γ && sep_guards Ξ * sep_heap Σ }} s {{ sep_env Γ' && sep_guards Ξ * sep_heap Σ' }}.
Proof.
  intros until s.
  intros wf wf_h wf_g H. induction H.
  + apply semax_skip.
  + eapply sep_proof_proc_call; eauto. 
    eapply t_proc_s; eauto.
  + (** pad **) admit.
  + eapply sep_proof_assign; eauto. 
    eapply t_assign; eauto.
  + (** alloc **) admit.
  + (** if-then-else **) admit.
  + apply semax_seq with (Q := sep_env Γ' && sep_guards Ξ * sep_heap Σ').
    intuition.
    apply IHstmt_type2. eauto using wf_stmt. eauto using wf_heap_stmt. eauto using wf_guards_stmt.
Qed.
  
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
