Add LoadPath "vst".
Require Import CpdtTactics.
Require Import Types.
Import HE.
Require Import Language.
Require Export ProgramLogic.
Require Import Subst.
Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.

Set Implicit Arguments.

Open Scope logic.

Definition OkRef x l s :=
(!!(eval s x = eval s (locvar_e l))
                        && !!(eval s x <> Some null_v)
                        && !!(eval s x <> None)).

Definition sep_base (x:expr) (t:base_type) : assert :=
  match t with 
    | int_t   => (EX n : nat, eval_to x (int_v n))
    | ref_t l => OkRef x l
    | null_t  => eval_to x null_v
  end && emp.

Fixpoint sep_pred (p:reft_prop) : assert :=
  match p with
    | tt_r  => TT
    | eq_r e1 e2 => fun s => !!(eval s e1 = eval s e2)
    | not_r p => (sep_pred p) --> FF
    | and_r p1 p2 => sep_pred p1 && sep_pred p2
    | or_r p1 p2 => sep_pred p1 || sep_pred p2
  end && emp.

Definition sep_ty (x:expr) (t:reft_type) : assert :=
  match t with
  | mkReft_type b p => sep_base x b && (sep_pred (subst (subst_one ν x) p))
  end && emp.

Fixpoint sep_env (Γ : type_env) : assert :=
  match Γ with
    | nil => TT
    | (x,t) :: Γ' => sep_ty (var_e x) t && sep_env Γ'
  end && emp.

Definition sep_heap_bind l (xt : type_binding) : assert :=
  (eval_to (locvar_e l) null_v) 
    || (emapsto (locvar_e l) (var_e (fst xt))
        * sep_ty (var_e (fst xt)) (snd xt)).

Fixpoint sep_heap' es :=
  match es with
    | nil => emp
    | (l, xt) :: es' => sep_heap_bind l xt * sep_heap' es'
  end.

Definition sep_heap (Σ : heap_env)  : assert :=
  fold (fun l xt a =>
          sep_heap_bind l xt * a) Σ emp.
  (* sep_heap' (elements Σ). *)
  (* fold (fun _ xt a => xt * a) *)
  (*   (mapi (fun l xt => sep_heap_bind l xt) Σ) *)
  (*   emp. *)

Fixpoint sep_guards (Δ : guards) : assert :=
  match Δ with
    | nil => TT
    | p :: Δ' => sep_pred p && sep_guards Δ'
  end && emp.

Definition binds (h : heap_env) :=
  fold (fun _ xt bs => set_add eq_dec (fst xt) bs) h [].

Definition locs (h : heap_env) :=
  fold (fun l _ bs => set_add eq_dec l bs) h [].

Definition mod_vars S :=
  let h1s := binds (s_heap_in S)  in
  let h2s := binds (s_heap_out S) in
  set_diff eq_dec h2s h1s.

Definition mod_locs S :=
  let h1s := locs (s_heap_in S)  in
  let h2s := locs (s_heap_out S) in
  set_diff eq_dec h2s h1s.
  

Definition sep_schema (f:pname) (s:stmt) (S:proc_schema) : procspec := 
  match S with
    | mkSchema xs ts hi ho (x, t) =>
      (f, mkProc xs x (mod_vars S) (mod_locs S) s, 
          sep_env (combine xs ts) * sep_heap hi,
          sep_ty (var_e x) t * sep_heap ho)
  end.

Fixpoint sep_proc_env (Φ : proc_env) : procspecs :=
  match Φ with
    | nil => nil
    | (f,(s,t)) :: Φ' => sep_schema f s t :: sep_proc_env Φ'
  end.

Definition disj_subst Γ (θ : var -> expr) :=
  θ ν = (var_e ν) /\ forall x, var_in x Γ -> θ x = (var_e x).

Lemma help_in_rev :
  forall l L, (exists (e : type_binding), InA (eq_key_elt (elt := type_binding)) (l,e) L)
                       <-> (exists (e : type_binding), InA (eq_key_elt (elt := type_binding)) (l, e) (rev L)).
Proof.
  intros.
  split; intros; destruct H; exists x; apply InA_rev; eauto using HE_Props.eqke_equiv.
Qed.

Lemma help_in_rev' :
  forall b L, (exists l (e : reft_type), InA (eq_key_elt (elt := type_binding)) (l,(b,e)) L)
                       <-> (exists l (e : reft_type), InA (eq_key_elt (elt := type_binding)) (l, (b, e)) (rev L)).
Proof.
  intros.
  split; intros; destruct H; destruct H; exists x, x0; apply InA_rev; eauto using HE_Props.eqke_equiv.
Qed.

Lemma locs_in_heap :
  forall h l,
    loc_in l h <-> In l (locs h).
Proof.
  intros.
  unfold loc_in.
  unfold locs.
  rewrite <- HE_Props.F.in_find_iff.
  rewrite HE_Props.F.elements_in_iff.
  rewrite HE_Props.fold_spec_right.
  split. intros.
  destruct H.
  rewrite <- InA_rev in H.
  induction (rev (elements h)).
  inv H.
  unfold HE_Props.uncurry in *.
  inv H.
  apply set_add_intro2. apply H1.
  apply set_add_intro1; apply IHl0. easy.
  apply HE_Props.eqke_equiv.
  intros. 
  rewrite help_in_rev.
  induction (rev (elements h)).
  inv H.
  unfold HE_Props.uncurry in *.
  unfold fold_right in H. fold fold_right in H.
  apply set_add_elim in H. destruct H.
  rewrite H. exists (snd a). left. destruct a. reflexivity.
  apply IHl0 in H. destruct H. exists x. right. assumption.
Qed.

Lemma ack_foo :
  forall L b,
     b ∈ fold_right
          (HE_Props.uncurry
             (λ (_ : key) (xt : var * reft_type) (bs : set var),
              set_add eq_dec (fst xt) bs)) []
         L  ->
   exists (l : key) (e : reft_type),
     InA (eq_key_elt (elt:=type_binding)) (l, (b, e)) L.
Proof.
  intros.
  induction L. inv H.
  simpl in H. unfold HE_Props.uncurry in *.
  apply set_add_elim in H.
  destruct H.
  rewrite H.
  exists (fst a). exists (snd (snd a)). left. destruct a. destruct p. reflexivity.
  apply IHL in H. destruct H. destruct H. exists x, x0.
  right. assumption.
Qed.

Lemma binds_in_heap :
  forall (h : heap_env) (b : var),
    bind_in b h <-> In b (binds h).
Proof.
  intros.
  unfold bind_in.
  unfold binds.
  setoid_rewrite <- HE_Props.F.find_mapsto_iff.
  setoid_rewrite HE_Props.F.elements_mapsto_iff.
  rewrite HE_Props.fold_spec_right.
  split. intros.
  destruct H. destruct H. rewrite <- InA_rev in H.
  induction (rev ((elements (elt := var * reft_type)) h)). inv H.
  unfold fold_right; fold fold_right. unfold HE_Props.uncurry in *.
  inv H.
  apply set_add_intro2. destruct a. destruct p. inv H1. simpl in *. congruence.
  apply set_add_intro1. apply IHl. easy.
  apply HE_Props.eqke_equiv.
  intro.
  rewrite help_in_rev'.
  eauto using ack_foo.
Qed.

Lemma new_mod_locs_schema :
  forall S l,
    In l (mod_locs S) <-> (loc_in l (s_heap_out S) /\ ~ loc_in l (s_heap_in S)).
Proof.
  intros. destruct S as [xs ts hi ho rt]. simpl.
  split; intros.
  unfold mod_locs in *.
  split.
  apply locs_in_heap.
  simpl in *.
  apply set_diff_elim1 in H. easy.
  rewrite locs_in_heap.
  eapply set_diff_elim2; eauto.
  destruct H.
  unfold mod_locs.
  apply set_diff_intro.
  apply locs_in_heap. apply H.
  rewrite locs_in_heap in H0. apply H0.
Qed.

Lemma new_mod_vars_schema :
  forall S v,
    In v (mod_vars S) <-> (bind_in v (s_heap_out S) /\ ~ bind_in v (s_heap_in S)).
Proof.
  intros. destruct S as [xs ts hi ho rt]. simpl.
  split; intros.
  unfold mod_vars in *.
  split.
  apply binds_in_heap.
  simpl in *.
  apply set_diff_elim1 in H. easy.
  rewrite binds_in_heap.
  eapply set_diff_elim2; eauto.
  destruct H.
  unfold mod_vars.
  apply set_diff_intro.
  apply binds_in_heap. apply H.
  rewrite binds_in_heap in H0. apply H0.
Qed.

Lemma sep_base_pure : 
  forall x t, 
    pure (sep_base x t).
Proof.
  intros.
  unfold pure.
  unfold sep_base.
  apply andp_left2.
  apply derives_refl.
Qed.

Lemma sep_pred_pure :
  forall p,
    pure (sep_pred p).
Proof.
  intros.
  unfold pure.
  destruct p;
  unfold sep_pred; fold sep_pred; apply andp_left2; apply derives_refl.
Qed.

Lemma sep_ty_pure :
  forall x t,
    pure (sep_ty x t).
Proof.
  intros.
  unfold pure, sep_ty.
  destruct t0.
  do 2 apply andp_left1.
  apply sep_base_pure.
Qed.

Lemma sep_env_pure :
  forall g,
    pure (sep_env g).
Proof.
  intros.
  unfold pure.
  destruct g.
  apply andp_left2. apply derives_refl.
  unfold sep_env. fold sep_env.
  apply andp_left2. apply derives_refl.
Qed.

Lemma sep_guard_pure :
  forall g,
    pure (sep_guards g).
Proof.
  intros.
  unfold pure, sep_guards.
  destruct g.
  normalize.
  apply andp_left2.
  apply derives_refl.
Qed.

Lemma pure_andp_1 :
  forall P Q, pure P -> pure (P && Q).
Proof.
  intros.
  unfold pure.
  apply andp_left1.
  assumption.
Qed.

Lemma pure_andp_2 :
  forall P Q, pure Q -> pure (P && Q).
Proof.
  intros.
  unfold pure.
  apply andp_left2.
  assumption.
Qed.

Hint Resolve sep_pred_pure sep_ty_pure sep_env_pure sep_guard_pure subst_pure pure_andp_1 pure_andp_2 : pure.

Ltac purity := 
  match goal with
    | |- context[emp] => eauto with pure
    | _: _ && _ |- context[emp] =>
      (apply andp_left1; purity || apply andp_left2; purity)
  end.

(* Lemma sep_heap_decompose' : *)
(*   forall H l x t,  *)
(*     in (l, (x, t)) H ->  *)
(*     exists H', (sep_heap H = sep_heap_bind l x t * sep_heap H' *)
(*                 /\ (forall l', l <> l' -> (loc_in l' H <-> loc_in l' H'))). *)
(* Proof. *)
(*   induction H as [ | [l' [x' t']]]. *)
(*   + intros. contradiction H.  *)
(*   + intros. destruct H0.  *)
(*     * inv H0. *)
(*       unfold sep_heap at 1; fold sep_heap. *)
(*       exists H. repeat split.  *)
(*       intro. *)
(*       unfold loc_in in *. *)
(*       destruct H1. destruct H1. inv H1. congruence. *)
(*       exists x0. assumption. *)
(*       unfold loc_in. *)
(*       intros [xt]. intro. *)
(*       exists xt. eauto with datatypes. *)
(*     * specialize (IHlist l x t H0).  *)
(*       destruct IHlist as [ H'' ]. *)
(*       destruct H1 as [A B]. *)
(*       unfold sep_heap; fold sep_heap. *)
(*       rewrite A. *)
(*       rewrite <- sepcon_assoc. *)
(*       exists ((l',(x',t'))::H''). *)
(*       unfold sep_heap; fold sep_heap. *)
(*       rewrite <- sepcon_assoc. *)
(*       split. *)
(*         { f_equal. *)
(*           rewrite sepcon_comm. *)
(*           reflexivity. } *)
(*         { repeat split.  *)
(*           intros. *)
(*           unfold loc_in in *. *)
(*           destruct H2. destruct H2. inv H2. exists (x', t'). left. reflexivity. *)
(*           specialize (B l'0 H1). destruct B.  *)
(*           destruct H3. exists x0. assumption. *)
(*           exists x1. right. assumption. *)
          
(*           intro. *)
(*           unfold loc_in in *. *)
(*           destruct H2. destruct H2. inv H2. exists (x', t'). left. reflexivity. *)
(*           specialize (B l'0 H1). destruct B. *)
(*           destruct H4. exists x0. assumption. *)
(*           exists x1. right. assumption. } *)
(* Qed. *)

(* Lemma sep_heap_split : *)
(*   forall H H1 H2, *)
(*     heap_split H1 H2 H -> *)
(*     sep_heap H = sep_heap H1 * sep_heap H2. *)
(* Proof. *)
(*   intros H. *)
(*   induction H as [ | (l,xt)]; intros. *)
(*   + assert (H1 = []) by (eapply heap_split_emp1; eauto). *)
(*     assert (H2 = []) by (eapply heap_split_emp2; eauto). *)
(*     subst H1. subst H2. *)
(*     simpl. rewrite sepcon_emp. reflexivity. *)
(*   + assert ((l, xt) :: H = [(l, xt)] ++ H) by reflexivity. *)
(*     rewrite H3. *)
(*     rewrite sep_heap_app. *)
(*     destruct xt as [x t]. *)
(*     unfold sep_heap at 1. *)
(*     rewrite sepcon_emp. *)

(*     unfold heap_split in H0; decompose [and] H0. *)
(*     destruct (H9 l (x,t)). left. reflexivity. { *)
(*       destruct (sep_heap_decompose' H1 l x t) as [H1']. *)
(*       apply H8. *)
(*       specialize (IHlist H1' H2). *)
(*       rewrite IHlist. *)
(*       destruct H10. *)
(*       rewrite H10. *)
(*       rewrite sepcon_assoc. *)
(*       reflexivity. *)

(*       unfold heap_split. *)
(*       repeat split. *)
(*       inv H4. assumption. *)

(*     unfold heap_split in H0. *)
(*     destruct H0. *)
(*     specialize (H4 l xt). *)
(*     destruct H4. left. reflexivity. *)
(*     pose (sep_heap_decompose' H1 l x t) as H1_decomp. *)
(*     destruct H1_decomp as [H1']. apply H4.  *)
(*     specialize (IHlist H1' H2). *)
(*     destruct H5. *)
(*     rewrite IHlist. *)
(*     rewrite H5. *)
(*     unfold sep_heap; fold sep_heap. *)
(*     rewrite sepcon_emp. rewrite sepcon_assoc. reflexivity. *)
    
(*     unfold heap_split. split. { *)
(*       intros l0. *)
(*       repeat rewrite <- loc_in_not_in in *. *)
(*       intro l0_not_in. *)
(*       split. intro. *)
(*       specialize (H6 l0). *)
(*       specialize (H0 l0). *)
(*       repeat rewrite <- loc_in_not_in in H0. *)
(*       destruct H0. *)
(*       intro. *)
(*       intros l0. unfold loc_not_in in *. intros A. *)
(*       split. { *)

Import HE_Props.
Import HE_Props.F.
Import HE_Facts.

Lemma sep_heap_split' :
  forall H A,
    let f := (fun l xt a => sep_heap_bind l xt * a) in
    sep_heap H * A = fold f H A.
Proof.
  intros.
  unfold sep_heap.
  repeat rewrite fold_spec_right.
  
  induction (rev (elements H)) as [ | [l [x t]]].
  simpl.
  rewrite <- sepcon_emp.
  rewrite sepcon_comm.
  extensionality.
  normalize.
 
  unfold fold_right at 2.
  unfold fold_right at 2 in IHl.
  rewrite <- IHl.
  unfold f.
  unfold uncurry.
  simpl. extensionality ρ.
  rewrite sepcon_assoc.
  reflexivity.
Qed.

Corollary sep_heap_split'' :
  forall H1 H2,
    let f := (fun l xt a => sep_heap_bind l xt * a) in
    sep_heap H1 * sep_heap H2 = fold f H1 (sep_heap H2).
Proof.
  intros.
  apply sep_heap_split'.
Qed.
        
Lemma sep_heap_split :
  forall H H1 H2,
    heap_split H1 H2 H -> 
    sep_heap H = sep_heap H1 * sep_heap H2.
Proof.
  unfold heap_split in *.
  intros.
  set (f := (fun l xt a => sep_heap_bind l xt * a)).
  assert (sep_heap H1 * sep_heap H2 = fold f H1 (fold f H2 emp)).
  apply sep_heap_split''.
  rewrite H3.
  apply (Partition_fold (eqA := Logic.eq)).
  apply eq_equivalence.
  solve_proper.
  hnf. intros. extensionality. 
  repeat rewrite <- sepcon_assoc. 
  rewrite sepcon_comm with (P := sep_heap_bind k e). reflexivity.
  assumption.
Qed.

Class SubstBase ( D R : Type )
  `{SL : Subst loc D R} `{SB : @Subst base_type D R}
  `{SE : SubstExpr D R} `{SA : SubstAssert D R}
  `{S  : @SubstFV base_type D R SB} : Type := {
  subst_int_t : 
    forall (s : subst_t D R), subst s int_t = int_t
  ;
  subst_null_t : 
    forall (s : subst_t D R), subst s null_t = null_t
  ;
  subst_ref_t : 
    forall l (s : subst_t D R), subst s (ref_t l) = ref_t (subst s l)
  ;
  nonfv_base_t :
    forall bt e (x : D),
      nonfv e x ->
      nonfv bt x -> nonfv (sep_base e bt) x
  }.

Ltac f_equalize :=
  match goal with
    | |- (fun _ => _) = (fun _ => _) => extensionality
    | |- (_ && _) _ = (_ && _) _ => f_equal; f_equalize
    | |- (_ && _) = (_ && _) => f_equal; f_equalize
    | |- EX _:_, _ = EX _:_, _ => f_equal; f_equalize
    | _ => idtac
  end.

Lemma SubstProp_var :
  forall p (x : var),
    nonfv p x -> nonfv (sep_pred p) x.
Proof.
  intros.
  induction p; try easy.
  + unfold sep_pred. apply nonfv_andp.
    simpl. split.
    simpl in H.
    unfold nonfv_assert. intros. f_equalize.
    repeat rewrite <- nonfv_eval. reflexivity. easy. easy. easy.
  + unfold sep_pred. fold sep_pred. apply nonfv_andp.
    split.
    apply nonfv_imp. split.
    apply IHp. apply H. easy. easy.
  + unfold sep_pred; fold sep_pred; apply nonfv_andp. split.
    apply nonfv_andp. split.
    apply IHp1. apply H. apply IHp2. apply H. easy.
  + unfold sep_pred; fold sep_pred; apply nonfv_andp. split.
    apply nonfv_orp. split.
    apply IHp1. apply H. apply IHp2. apply H. easy.
Qed.

Ltac nonfv_base_simp := match goal with
                          | |- nonfv (_ && _) _ => apply nonfv_andp; split; nonfv_base_simp
                          | |- nonfv ?f _ => unfold f; nonfv_base_simp
                          | |- nonfv (?f _) _ => unfold f; nonfv_base_simp
                          | |- nonfv (?f _ _) _ => unfold f; nonfv_base_simp
                          | b : base_type |- appcontext[match ?b with _ => _ end]   =>
                            destruct b; unfold eval_to; nonfv_base_simp
                          | _ => idtac
                        end.

Ltac crush_substbase := 
  constructor; try firstorder;
  intros;
  nonfv_base_simp;
  simpl; unfold nonfv_assert; intros; f_equalize; try rewrite <- nonfv_eval; easy.

Instance SepBase_var_var : @SubstBase var var _ _ _ _ _ _ _ _ _ _ _ _ := _.
Proof. crush_substbase. Defined.

Instance SepBase_var_expr : @SubstBase var expr _ _ _ _ _ _ _ _ _ _ _ _  := _.
Proof.  crush_substbase. Defined.

Instance SepBase_loc_loc : @SubstBase loc loc _ _ _ _ _ _ _ _ _ _ _ _  := _.
Proof. 
  constructor; try firstorder; intros; nonfv_base_simp.
  simpl. unfold nonfv_assert. intros. f_equalize. rewrite <- nonfv_eval; easy.
  simpl. unfold nonfv_assert. intros. f_equalize. rewrite <- nonfv_eval; easy. easy.
  simpl. unfold nonfv_assert. intros. f_equalize. f_equal. f_equal. rewrite <- nonfv_eval; easy.
  unfold subst, subst_one. simpl. unfold runloc. simpl.
  destruct (eq_dec.eq_dec x l). compute in H0. subst x. congruence. easy.
  rewrite <- nonfv_eval; easy.
  rewrite <- nonfv_eval; easy.
  easy.
Defined.

Lemma SubstTy_var :
  forall e t (x : var),
    nonfv e x -> nonfv t x -> nonfv (sep_ty e t) x.
Proof.
  intros. destruct t0.
  unfold sep_ty.
  apply nonfv_andp. split.
  apply nonfv_andp. split.
  apply nonfv_base_t. easy. destruct reft_base; firstorder.
  apply SubstProp_var.
  eauto.
  induction reft_r; try easy.
  simpl. split.
  simpl in H0. unfold nonfv_reft_t in H0. destruct H0. simpl in H1. 
  pose nonfv_subst. apply n. clear n. apply H1. apply H.
  pose nonfv_subst. apply n. clear n. apply H0. apply H.
  simpl. apply IHreft_r. assumption.
  simpl. simpl in H0. unfold nonfv_reft_t in H0.  simpl in H0. destruct H0.
  split. 
  apply IHreft_r1; split; easy. 
  apply IHreft_r2; split; easy. 
  simpl. simpl in H0. unfold nonfv_reft_t in H0.  simpl in H0. destruct H0. split.
  apply IHreft_r1; split; easy. 
  apply IHreft_r2; split; easy. 
  easy.
Qed.

Lemma foo :  forall (P Q : assert), (fun w => (P w && Q w)) = ((fun w => P w) && (fun w => Q w)).
  firstorder.
Qed.

Class SubstPull ( D R : Type )  {S1 : Subst world D R} `{S2 : Subst expr D R} : Type 
:=
   subst_eval : 
     forall (w : world) (s : subst_t D R) (x : expr),
       eval w (subst s x) = eval (subst s w) x .

Instance SubstPull_var : @SubstPull var var _ _.
Proof.
  hnf.
    unfold subst. simpl.
    induction x.
    + reflexivity.
    + simpl. unfold subst_var. unfold stk. destruct w. destruct p. simpl.
      destruct (s v). reflexivity. reflexivity.
    + reflexivity.
    + simpl. rewrite IHx1. rewrite IHx2. reflexivity. 
Qed.

Instance SubstPull_expr : @SubstPull var expr _ _.
Proof.
  hnf.
    unfold subst. simpl.
    induction x.
    + reflexivity.
    + simpl.
      unfold stk. destruct w. destruct p. simpl.
      destruct (s v). reflexivity. reflexivity.
    + reflexivity.
    + simpl. rewrite IHx1. rewrite IHx2. reflexivity.
Qed.

Instance SubstPull_loc : @SubstPull loc loc _ _.
Proof.
  hnf.
    unfold subst. simpl.
    induction x.
    + reflexivity.
    + reflexivity. 
    + simpl. destruct w. destruct p. unfold runloc. simpl. unfold subst_loc. simpl.
      destruct (s l). destruct (l0 l1); reflexivity.
      destruct (l0 l); reflexivity.
    + simpl. rewrite IHx1. rewrite IHx2. reflexivity.
Qed.

Section Subst.

  (** Base Assumptions **)
  Context { D R : Type}.
  Context { EqDecD : EqDec D}.
  Context {Sub_Loc : Subst loc D R}.
  Context {Sub_LocFV : SubstFV loc D R Sub_Loc}.
  Context {Sub_Var : Subst var D R}.
  Context {Sub_Expr : Subst expr D R}.
  Context {Sub_ExprFV : SubstFV expr D R Sub_Expr}.
  Context {Sub_Wld : Subst world D R}.
  (* Context {SubWld : SubstWorld D R Sub_Var Sub_Wld}. *)
  Context {Sub_Assrt : Subst assert D R}.
  Context {SubAssrt : @SubstAssert D R Sub_Wld Sub_Assrt}.
  Definition eq_loc  := @eq _ _ _ Sub_Loc.
  Definition eq_var  := @eq _ _ _ Sub_Var.
  Definition eq_expr := @eq _ _ _ Sub_Expr.
  Context { Eq_eq_loc : Equivalence eq_loc}.
  Context { Eq_eq_var : Equivalence eq_var}.
  Context { Eq_eq_expr : Equivalence eq_expr}.

  Context { SubExpr : @SubstExpr D R EqDecD Sub_Loc Sub_Expr Sub_ExprFV Sub_Wld}.

  (** Base Types **)
  Instance Sub_Base : Subst base_type D R :=  @Subst_base D R Sub_Loc Eq_eq_loc.
  Instance Sub_BaseFV : SubstFV base_type D R Sub_Base := 
    @FVSubst_base D R Sub_Loc Sub_LocFV Eq_eq_loc.
  Context { SubBase : (@SubstBase D R Sub_Loc Sub_Base EqDecD Sub_Loc
                                  Sub_Expr Sub_ExprFV Sub_Wld SubExpr Sub_Wld Sub_Assrt 
                                  SubAssrt Sub_BaseFV)}.
  Instance Eq_eq_base : Equivalence (@eq base_type D R Sub_Base) :=
    @Eq_eqBase D R Sub_Loc Eq_eq_loc.
 
  (** Props **)
  Instance Sub_Prop : Subst reft_prop D R := @Subst_prop D R Sub_Expr.
  Instance Eq_eq_Prop : Equivalence (@eq reft_prop D R Sub_Prop) :=
    @Eq_eqProp D R Sub_Expr Eq_eq_expr.

  (** Reft Types **)
  Instance Sub_Type : Subst reft_type D R := @Subst_reft D R Sub_Base Sub_Prop.
  Instance Eq_eq_Type : Equivalence (@eq reft_type D R Sub_Type) :=
    @Eq_eq_reft_r D R Sub_Base Sub_Prop Eq_eq_base Eq_eq_Prop.

  Instance Sub_TyBi : Subst type_binding D R := 
    @Subst_prod var reft_type D R Sub_Var Sub_Type.
  Instance Eq_eq_TyBi : Equivalence (@eq type_binding D R Sub_TyBi) :=
    @Eq_eqProd var reft_type D R Sub_Var Sub_Type Eq_eq_var Eq_eq_Type.

  Instance Sub_Ctx  : Subst type_env D R := 
    @Subst_list type_binding D R Sub_TyBi Eq_eq_TyBi.
  Instance Sub_Heap : Subst heap_env D R :=
    @Subst_heap D R Sub_Loc Sub_TyBi Eq_eq_loc Eq_eq_TyBi.
  Instance Sub_HeapBinds : Subst (list (loc * type_binding)) D R :=
    @Subst_list (loc * type_binding) D R (@Subst_prod loc type_binding D R Sub_Loc Sub_TyBi)
    (@Eq_eqProd loc type_binding D R Sub_Loc Sub_TyBi Eq_eq_loc Eq_eq_TyBi).
  
  (** Pulling **) 
  Context { Sub_Pull_Expr : @SubstPull D R Sub_Wld Sub_Expr}.

Lemma sep_base_subst :
  forall (s : subst_t D R) x b,
    sep_base (subst s x) (subst s b) = subst s (sep_base x b).
Proof.
  intros.
  unfold sep_base.
  destruct b;
  first [rewrite subst_int_t | rewrite subst_null_t | rewrite subst_ref_t].
  simpl. rewrite subst_wld. extensionality.
  f_equal. f_equal. extensionality.
  unfold eval_to. simpl. rewrite subst_eval. reflexivity.
  unfold eval_to. extensionality. rewrite subst_wld.
  simpl. f_equal. f_equal. f_equal.
  f_equal. rewrite subst_eval. reflexivity.
  rewrite subst_andp.
  f_equal.
  rewrite subst_wld. extensionality w.
  unfold OkRef.
  rewrite subst_eval. f_equal. f_equal.
  f_equal. f_equal.
  rewrite <- subst_eval.
  f_equal. f_equal. 
  rewrite <- subst_locvar.
  reflexivity.
  simpl.
  rewrite subst_wld. reflexivity.
Qed.

Lemma sep_pred_subst :
  (* forall { D R : Type }  *)
  (*        `{Sl : Subst loc D R}  *)
  (*        `{SFV : SubstFV expr D R} *)
  (*        `{SFVB : SubstFV base_type D R} *)
  (*        { E : EqDec D } *)
  (*        {SW : Subst world D R} *)
  (*        {S : SubstExpr D R (Sl := Sl)}  *)
  (*        `{S' : SubstBase D R (SL := Sl)}  *)
  (*        {SW : Subst world D R}  *)
  (*        {SA : Subst assert D R} *)
  (*        `{S'''' : (@SubstPull D R SW _)}  *)
  (*        `{S : @SubstAssert D R SW _} *)
         forall (s : subst_t D R) x,
    sep_pred (subst s x) = subst s (sep_pred x).
Proof.
  intros.
  induction x.
  + simpl; rewrite subst_wld; reflexivity.
  + simpl. rewrite subst_wld. extensionality. f_equal. do 2 rewrite subst_eval. reflexivity.
  + unfold sep_pred. 
    simpl subst at 1. unfold subst_prop; fold subst_prop.
    rewrite subst_andp. f_equal.
    rewrite subst_imp. f_equal. apply IHx.
    rewrite subst_wld. reflexivity.
    rewrite subst_wld. reflexivity.
  + simpl subst at 1. unfold subst_prop; fold subst_prop. 
    unfold sep_pred.
    rewrite subst_andp. rewrite subst_andp.
    fold sep_pred.
    f_equal. f_equal. assumption. assumption. rewrite subst_wld. reflexivity.
  + simpl subst at 1. unfold subst_prop. fold subst_prop. 
    unfold sep_pred.
    rewrite subst_andp. rewrite subst_orp.
    fold sep_pred.
    f_equal. f_equal. assumption. assumption. rewrite subst_wld. reflexivity.
Qed.

Lemma subst_ty_base_pred :
  forall {D R : Type} {S : Subst assert D R } (s : subst_t D R) v b p,
    subst s (sep_ty v { ν : b | p }) =
    subst s (sep_base v b && sep_pred (subst (subst_one ν v) p) && emp).
Proof.
  firstorder.
Qed.

Lemma commuting_subst :
  forall (s : subst_t D R) x (e : expr),
    (subst s (var_e ν) = var_e ν) ->
    (forall (x : expr), (nonfv x ν) -> nonfv (subst s x) ν) ->
    subst (subst_one ν (subst s x)) (subst s e) = subst s (subst (subst_one ν x) e).
Proof.
  intros.
  induction e.
  simpl. rewrite subst_value. reflexivity.
  compare ν v.
  intro.
  subst v. 
  rewrite H. simpl subst at 4. unfold subst_expr. unfold subst_one. simpl.
  destruct (eq_dec.eq_dec ν ν). reflexivity. congruence.

  intros.
  assert (subst (subst_one ν (subst s x)) (subst s (var_e v)) = subst s (var_e v)).
  pose (subst_nonfv (subst_one ν (subst s x)) (subst s (var_e v))).
  rewrite e. reflexivity.
  intro v'.
  unfold subst_one.
  intro.
  destruct (eq_dec.eq_dec ν v'). subst v'. apply H0. intro. inversion H2. congruence. inv H3.
  congruence.

  rewrite H1.
  pose (subst_nonfv (subst_one ν x) (var_e v)).
  rewrite e. reflexivity. 
  intro v'. unfold subst_one. destruct (eq_dec.eq_dec ν v'). intro. subst v'. unfold nonfv. simpl.
  unfold NFV. simpl. intro. destruct H3; congruence.
  congruence.
  decide equality.

  repeat rewrite <- subst_locvar. simpl.
  rewrite subst_locvar. reflexivity.
  
  repeat rewrite subst_fun.
  rewrite IHe1.
  rewrite IHe2. 
 reflexivity.
Qed.
  
Lemma boo :
  forall  (s : subst_t D R) x p,
    (subst s (var_e ν) = var_e ν) ->
    (forall (x : expr), (nonfv x ν) -> nonfv (subst s x) ν) ->
   sep_pred (subst_prop (subst_one ν (subst s x)) (subst_prop s p)) =
   subst s (sep_pred (subst_prop (subst_one ν x) p)) .
Proof.
  intros.
  rewrite <- sep_pred_subst.
  f_equal.
  simpl.
  induction p.
  + reflexivity.
  + simpl.
    repeat rewrite commuting_subst; easy.
  + simpl. rewrite IHp. reflexivity.
  + simpl. rewrite IHp1. rewrite IHp2. reflexivity.
  + simpl. rewrite IHp1. rewrite IHp2. reflexivity.
Qed.

Lemma sep_ty_subst :
  forall (s : subst_t D R) x b p,
    (subst s (var_e ν) = var_e ν) ->
    (forall (x : expr), nonfv x ν -> nonfv (subst s x) ν) ->
    sep_ty (@subst _ _ _ Sub_Expr s x) (@subst _ _ _ Sub_Type s {ν : b | p}) = @subst _ _ _ Sub_Assrt s (sep_ty x {ν : b | p}).
Proof.
  intros.
  rewrite subst_ty_base_pred.
  unfold sep_ty.
  simpl subst at 1.
  unfold subst_r.
  extensionality.
  simpl reft_base.
  rewrite sep_base_subst.
  rewrite subst_andp.
  rewrite subst_andp.
  (* rewrite subst_wld. *)
  (* rewrite subst_wld. *)
  (* rewrite subst_wld. *)
  f_equal.
  f_equal.
  cut (
        sep_pred (subst (subst_one ν (subst s x)) (subst s p)) =
        subst s (sep_pred (subst (subst_one ν x) p))
  ). 
  intro.
  simpl reft_r.
  rewrite H1. reflexivity.
  pose (boo s x p).
  simpl subst at 1.
  simpl subst at 2. 
  simpl subst at 3.
  rewrite e; easy. 
  extensionality. simpl. rewrite subst_wld. reflexivity.
Qed.

Lemma subst_prod :
  forall s x y,
    subst s (x, y) = (subst s x, subst s y).
Proof.
  reflexivity.
Qed.

Definition var_2_var (θ : subst_t D R) :=
  forall x, var_e (subst θ x) = subst θ (var_e x).

Lemma sep_env_subst :
  forall (s : subst_t D R) xts,
    var_2_var s ->
    (subst s (var_e ν) = var_e ν) ->
    (forall (x : expr), nonfv x ν -> nonfv (subst s x) ν) ->
    sep_env (subst s xts) = subst s (sep_env xts).
Proof.
  intros.
  induction xts as [| [x t]].
  - rewrite subst_wld. reflexivity.
  - setoid_rewrite subst_cons. 
    unfold sep_env. fold sep_env.
    setoid_rewrite subst_prod.
    do 2 setoid_rewrite subst_andp.
    f_equal. f_equal.
    rewrite H.
    destruct t as [b p].
    rewrite <- sep_ty_subst.
    reflexivity.
    assumption.
    assumption.
    intuition.
    rewrite subst_wld.
    reflexivity.
Qed.

Lemma sep_guards_subst :
  forall (s : subst_t D R) g,
    sep_guards (subst s g) = subst s (sep_guards g).
Proof.
  intros.
  induction g as [| φ ].
  + rewrite subst_wld. reflexivity.
  + setoid_rewrite subst_cons.
    unfold sep_guards. fold sep_guards.
    rewrite subst_andp.
    rewrite subst_andp.
    rewrite <- IHg.
    f_equal. f_equal. rewrite sep_pred_subst. reflexivity. 
    rewrite subst_wld. reflexivity.
Qed.

  Ltac push n := rewrite subst_prod at n.
  
  (* Lemma lift_fun : *)
  (*   forall (P : mpred) w, *)
  (*     ((fun (x : world) => P x) && emp)  *)
  (*     ((fun (x : world) => P) && (@emp (world -> mpred) _ _)) w = fun (x : world) => (P && (@emp mpred _ _)). *)
  (* Proof. *)
  (*   firstorder. *)
  (* Qed. *)
  

  Lemma sep_heap_bind_subst :
    forall (s : subst_t D R) l xt,
      var_2_var s ->
      (subst s (var_e ν) = var_e ν) ->
      (forall (x : expr), nonfv x ν -> nonfv (subst s x) ν) ->
      sep_heap_bind (subst s l) (subst s xt) = subst s (sep_heap_bind l xt).
  Proof.
    intros s l [x t]. intros.
    unfold sep_heap_bind.
    rewrite subst_prod.
    unfold snd. unfold fst.
    rewrite subst_orp.
    f_equal.
    unfold eval_to.
    rewrite subst_andp.
    f_equal.
    rewrite subst_wld.
    extensionality w.
    rewrite subst_locvar.
    rewrite subst_eval.
    reflexivity.
    rewrite subst_wld. 
    reflexivity.
    rewrite H.
    rewrite subst_sepcon.
    f_equal.
    rewrite subst_locvar.
    unfold emapsto. 
    rewrite subst_wld.
    simpl. extensionality w. f_equal. extensionality addr. f_equal. extensionality v.
    f_equal. f_equal.
    unfold eval_to.
    simpl.
    rewrite subst_eval.
    reflexivity.
    unfold eval_to.
    simpl andp. cbv beta.
    f_equal.
    f_equal.
    rewrite subst_eval.
    reflexivity.
    destruct t as [b p].
    rewrite <- sep_ty_subst.
    reflexivity.
    easy.
    easy.
  Qed.

Ltac push_subst :=
  (repeat (first [ rewrite subst_andp 
                 | rewrite subst_orp 
                 | rewrite subst_sepcon 
                 | rewrite subst_imp
                 ])).

Definition eqk := @eq_key type_binding.

Lemma thingie' :
  forall (s : subst_t D R) (x y : loc * type_binding),
    (forall (l m : loc), (subst s l) = (subst s m) -> l = m) ->
    eqk (subst s x) (subst s y) -> eqk x y.
Proof.
  intros.
  destruct x as [l xt].
  destruct y as [m yt].
  inv H0.
  specialize (H l m).
  unfold eqk.
  apply H. easy.
Qed.

Lemma thingie :
  forall (s : subst_t D R) (e : (loc * type_binding)) l,
    (forall (l m : loc), (subst s l) = (subst s m) -> l = m) ->
    InA eqk (subst s e) (subst s l) -> InA eqk e l.
Proof.
  intros.
  induction l.
  + inv H0.
  + simpl subst at 2 in H0.
    unfold subst_list in H0. fold subst_list in H0.
    inv H0.
    left.
    apply (thingie' s). 
    assumption.
    apply H2.
    right.
    apply IHl.
    assumption.
Qed.

Lemma transpose_sep_heap_bind :
   transpose_neqkey Logic.eq
     (λ (l : key) (xt : type_binding) (a : assert), sep_heap_bind l xt * a).
Proof.
  hnf. intros.
  extensionality. rewrite sepcon_comm. rewrite sepcon_comm with (P := sep_heap_bind k e).
  rewrite sepcon_assoc. reflexivity.
Qed.

Definition NonUnifyingSub (θ : subst_t D R) (h : heap_env) :=
  (forall (l1 l2 : loc), l1 <> l2 -> subst θ l1 <> subst θ l2) /\
  forall l x t,
    MapsTo l (x, t) h <-> MapsTo (subst θ l) (subst θ x, subst θ t) (subst θ h).

Lemma push_sep_heap_subst_1 : 
  forall s h,
       subst s (sep_heap h) 
       = fold (fun l xt a => subst s (sep_heap_bind l xt) * a) h emp.
Proof.
  intros.
  unfold sep_heap.
  rewrite subst_wld.
  extensionality w.
  apply fold_rel with (R := fun (A B : assert) => A (subst s w) = B w).
  reflexivity.
  intros.
  simpl. rewrite H0.
  rewrite subst_wld. reflexivity.
Qed.

Lemma subst_heap_bindings :
  forall s l (h : heap_env),
    (forall (l1 l2 : loc), l1 <> l2 -> subst s l1 <> subst s l2) ->
    ~ HE.In l (fold (add (elt := type_binding)) h heap_emp) -> ~ HE.In (subst s l) (subst s h).
  simpl subst at 2.
  unfold subst_heap.
  intros until h. intro Hyp.
  apply fold_rel with (R := fun A B => ~ HE.In l A -> ~ HE.In (subst s l) B); intros.
  + intro. apply H. apply empty_in_iff in H0. intuition.
  + simpl in *.
    intro.
    apply H1.
    apply add_in_iff in H2.
    apply add_in_iff.
    destruct H2. 
    left.
    compare k l. tauto.
    intro. apply Hyp in n. exfalso. apply n. apply H2. decide equality.
    right.
    apply H0 in H2. inv H2. 
    intro. apply H1. apply add_in_iff. 
    compare k l. tauto. intro. right. assumption.
    decide equality.
Qed.

Lemma transpose_neqkey_add :
  forall s, 
    (forall (l1 l2 : loc), l1 <> l2 -> subst s l1 <> subst s l2) ->
    transpose_neqkey Equal
                     (λ (l0 : key) (xt0 : type_binding) (m0 : t type_binding),
                      add (subst s l0) (subst s xt0) m0).
Proof.
  intros; hnf; intros.
  simpl.
  rewrite Equal_mapsto_iff. intros.
  repeat rewrite add_mapsto_iff.
  split. intros. decompose [and or] H1; clear H1.
  right. split. rewrite <- H3. apply H. intuition. 
  left. intuition.
  left. intuition.
  right. intuition.
  intros. decompose [and or] H1; clear H1.
  right. split. rewrite <- H3. apply H. intuition.
  left. intuition.
  left. intuition.
  right. intuition.
Qed.

Lemma subst_heap_eq : 
  forall s h h',
    (∀ l1 l2 : loc, l1 ≠ l2 → subst s l1 ≠ subst s l2) ->
    Equal h h' -> 
    Equal (subst_heap s h) (subst_heap s h').
Proof.
  intros.
  unfold subst_heap.
  apply fold_Equal. apply Equal_ST.
  solve_proper.
  apply transpose_neqkey_add.
  assumption.
  assumption.
Qed.

Lemma subst_heap_add : forall s k e m,
    (forall (l1 l2 : loc), l1 <> l2 -> subst s l1 <> subst s l2) ->
       ¬HE.In (elt:=type_binding) k m ->
       Equal (subst_heap s (add k e m)) (add (subst s k) (subst s e) (subst_heap s m)).
Proof.
  intros.
  rewrite Equal_mapsto_iff.
  intros l xt.
  rewrite add_mapsto_iff.
  split. intro.
  unfold subst_heap in H1.
  rewrite fold_add in H1.
  rewrite add_mapsto_iff in H1. decompose [and or] H1; clear H1.
  left. intuition. right.  intuition.
  apply Equal_ST. solve_proper.
  apply transpose_neqkey_add. apply H. assumption.
  unfold subst_heap.
  rewrite fold_add.
  rewrite add_mapsto_iff. 
  intros. decompose [and or] H1; clear H1.
  left. intuition.
  right. intuition.
  apply Equal_ST.
  solve_proper.
  apply transpose_neqkey_add. apply H. 
  assumption.
Qed.

Lemma subst_heap_add_step : 
  forall k e h,
    ~ HE.In k h ->
    sep_heap (add k e h) = 
    sep_heap_bind k e * sep_heap h.
Proof.
  intros.
  unfold sep_heap.
  rewrite fold_add. reflexivity. apply eq_equivalence. solve_proper. 
  hnf. intros. simpl. extensionality. rewrite sepcon_comm. rewrite sepcon_comm with (P := sep_heap_bind k0 e0 x).
  rewrite sepcon_assoc. normalize.
  assumption.
Qed.
                             
Lemma push_sep_heap_subst_2 :
  forall s h,
    NonUnifyingSub s h ->
    sep_heap (subst s h) = fold (fun l xt a => (sep_heap_bind (subst s l) (subst s xt)) * a) h emp.
Proof.
  intros.
  unfold sep_heap.
  simpl subst at 1.
  apply fold_rec_bis with (P := fun M A => 
                                  fold (fun l xt a => sep_heap_bind l xt * a) (subst_heap s M) emp 
                                  = A).
  intros.
  rewrite <- H1.
  apply fold_Equal.
  apply eq_equivalence. solve_proper. apply transpose_sep_heap_bind. apply subst_heap_eq. apply H.
  symmetry. assumption.
  compute. reflexivity.
  intros.
  assert (Equal (subst_heap s (add k e m')) (add (subst s k) (subst s e) (subst_heap s m'))).
  apply subst_heap_add. apply H. apply H1.
  assert (fold (fun l xt a => sep_heap_bind l xt * a) (subst_heap s (add k e m')) emp
          = fold (fun l xt a => sep_heap_bind l xt * a) (add (subst s k) (subst s e) (subst_heap s m')) emp).
  apply fold_Equal. apply eq_equivalence. solve_proper. apply transpose_sep_heap_bind. easy.
  rewrite H4.
  pose (@subst_heap_add_step (subst s k) (subst s e) (subst_heap s m')).
  rewrite <- H2.
  unfold sep_heap in e0.
  rewrite e0.
  reflexivity.
  apply subst_heap_bindings.
  apply H.
  intro.
  apply H1.
  rewrite In_m. apply H5. reflexivity. symmetry. apply fold_identity.
Qed.

(* Lemma goo :  *)
(*   forall (s : subst_t D R) h l xt, *)
(*     (forall (l m : loc), (subst s l) = (subst s m) -> l = m) -> *)
(*     (MapsTo l xt (fold (add (elt := type_binding)) h heap_emp) -> *)
(*     MapsTo (subst s l) (subst s xt) (subst s h)). *)
(* Proof. *)
(*   intros until xt. intro OkSub. *)
(*   simpl subst at 3. *)
(*   unfold subst_heap. *)
(*   apply fold_rel with  *)
(*   (R := fun A B => MapsTo l xt A -> MapsTo (subst s l) (subst s xt) B). *)
(*   + rewrite empty_mapsto_iff. intuition. *)
(*   + repeat setoid_rewrite add_mapsto_iff. *)
(*     intros. *)
(*     destruct H1. destruct H1; subst. left. split; reflexivity. *)
(*     right. destruct H1. split. *)
(*     intro. apply OkSub in H3. congruence. auto. *)
(* Qed. *)
  
Lemma sep_heap_subst :
  forall (s : subst_t D R) h,
      var_2_var s ->
      (subst s (var_e ν) = var_e ν) ->
      (forall (x : expr), nonfv x ν -> nonfv (subst s x) ν) ->
      NonUnifyingSub s h ->
    sep_heap (subst s h) = subst s (sep_heap h).
Proof.
    intros.
    rewrite push_sep_heap_subst_1.
    rewrite push_sep_heap_subst_2; try easy.
    apply fold_rel. reflexivity.
    intros. subst.
    rewrite sep_heap_bind_subst; easy.
Qed.

End Subst.
   
Corollary sep_base_subst_var :
  forall (s : subst_t var var) x b, subst s (sep_base x b) = sep_base (subst s x) (subst s b).
Proof.
  intros; exact (eq_sym (sep_base_subst s x b)).
Qed.

Corollary sep_base_subst_expr :
  forall (s : subst_t var expr) x b, subst s (sep_base x b) = sep_base (subst s x) (subst s b).
Proof.
  intros; exact (eq_sym (sep_base_subst s x b)).
Qed.

Corollary sep_base_subst_loc :
  forall (s : subst_t loc loc) x b, subst s (sep_base x b) = sep_base (subst s x) (subst s b).
Proof.
  intros; exact (eq_sym (sep_base_subst s x b)).
Qed.

Corollary sep_pred_subst_expr :
  forall (θ : subst_t var expr) φ,
    subst θ (sep_pred φ) = sep_pred (subst θ φ).
Proof.
  intros.
  exact (eq_sym (sep_pred_subst θ φ)).
Qed.

Definition lift_var_subst (s : subst_t var var) :=
  fun i => match s i with
             | Some v => Some (var_e v)
             | None => None
           end.
(** wf G (H1 * H2) (H1 * H2) 
    x ∈ H2 ==> x ∉ H1
    wf (H0 * H1) G ==> x ∉ H1
    modvar x ==> x ∉ H0 **)
  