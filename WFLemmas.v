Add LoadPath "vst".
Require Import Coq.Unicode.Utf8.
Require Import msl.eq_dec.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import msl.Coqlib2.
Require Import msl.log_normalize.

Require Import Translation.
Require Import Types.
Require Import Language.
Require Export ProgramLogic.
Require Import Subst.
Require Import Tactics.
Require Import Judge.

Ltac freshloc l :=
  destruct l;
  match goal with
    | H : fresh_loc ?x _ _ |- loc_not_in ?x _ => apply H
  end.

Lemma fresh_imp_loc_not_in :
  forall l G H,
    fresh_loc l G H -> loc_not_in l H.
Proof.
  intros; destruct l; firstorder.
Qed.

Lemma fresh_imp_bind_not_in :
  forall x G H,
    fresh x G H -> bind_not_in x H.
Proof.
  firstorder.
Qed.

Lemma fresh_imp_var_not_in :
  forall x G H,
    fresh x G H -> var_not_in x G.
Proof.
  firstorder.
Qed.

Lemma fresh_imp_var_not_vv :
  forall x G H,
    fresh x G H -> x <> ν.
Proof.
  firstorder.
Qed.

Lemma in_imp_var_in :
  forall x t G,
    (x,t) ∈ G -> var_in x G.
Proof.
  firstorder.
Qed.

Lemma var_in_cons :
  forall a x G,
    var_in x G -> var_in x (a :: G).
Proof.
  firstorder.
Qed.

Lemma var_not_in_cons :
  forall a x G,
    var_not_in x (a :: G) -> var_not_in x G.
Proof.
  unfold var_not_in.
  intros.
  rewrite Forall_forall in *.
  firstorder.
Qed.

Lemma bind_in_cons :
  forall a x H,
    bind_in a H -> bind_in a (x :: H).
Proof.
  firstorder.
Qed.

Lemma bind_not_in_cons :
  forall a x H,
    bind_not_in x (a :: H) -> bind_not_in x H.
Proof.
  unfold bind_not_in.
  intros.
  rewrite Forall_forall in *.
  firstorder.
Qed.

Lemma loc_not_in_cons :
  forall a l H,
    loc_not_in l (a :: H) -> loc_not_in l H.
Proof.
  intros. unfold loc_not_in in *. 
  rewrite Forall_forall in *.
  firstorder.
Qed.

Lemma fresh_loc_cons_1 :
  forall x a G H,
    fresh_loc x (a :: G) H -> fresh_loc x G H.
Proof.
  intros.
  firstorder.
  unfold fresh_loc in *. destruct x.
  repeat split; try apply H0.
  unfold fresh in H0.
  eapply var_not_in_cons.
  apply H0.
Qed.

Lemma fresh_loc_cons_2 :
  forall x a G H,
    fresh_loc x G (a :: H) -> fresh_loc x G H.
Proof.
  intros.
  firstorder.
  unfold fresh_loc in *. destruct x.
  destruct H0 as [A [B C]].
  repeat split; (eauto using bind_not_in_cons, 
                             loc_not_in_cons, 
                             fresh_imp_bind_not_in).
  apply B.
Qed.

Lemma fresh_cons_1 :
  forall x a G H,
    fresh x G (a :: H) -> fresh x G H.
Proof.
  intros.
  firstorder. eauto using bind_not_in_cons.
Qed.

Lemma fresh_cons_2 :
  forall x a G H,
    fresh x (a :: G) H -> fresh x G H.
Proof.
  intros.
  firstorder. eauto using var_not_in_cons.
Qed.

Lemma wf_env_no_bind :
  forall G H v t, 
    wf_env H ((v, t) :: G) -> bind_not_in v H.
Proof.
  intros.
  inversion H0. 
  firstorder.
Qed.

Lemma fresh_var_neq :
  forall G H v t x,
    fresh x ((v,t) :: G) H -> 
    x <> v.
Proof.
  unfold fresh.
  intros.
  intuition.
  subst.
  unfold var_not_in in *. rewrite Forall_forall in H0.
  contradiction (H0 (v,t));
  firstorder.
Qed.

Lemma var_neq_bind_not_in :
  forall G H l x t v,
    x <> v -> fresh v G H -> fresh v G ((l, (x,t)) :: H).
Proof.
  intros.
  unfold fresh in *.
  split; (repeat split); try apply H1.
  unfold bind_not_in in *.
  rewrite Forall_forall in *.
  intros [l' [x' t']] [?|?]. 
    inversion 0; subst; auto.
    decompose [and or] H1.
    eauto.
Qed.

Hint Resolve 
     in_imp_var_in
     var_in_cons
     var_not_in_cons
     bind_in_cons
     bind_not_in_cons
     fresh_loc_cons_1
     fresh_loc_cons_2
     fresh_cons_1
     fresh_cons_2
     fresh_imp_loc_not_in
     fresh_imp_var_not_vv
     fresh_imp_var_not_in
     fresh_imp_bind_not_in
     fresh_var_neq
     var_neq_bind_not_in
     wf_env_no_bind
: wf.

Lemma var_neq_fresh_loc :
  forall G H x l t,
    (V l) <> x -> 
    fresh_loc (L l) G H -> fresh_loc (L l) ((x,t) :: G) H.
Proof.
  intros.
  unfold fresh_loc in *.
  decompose [and] H1.
  repeat split; eauto with wf.
  unfold fresh in H4.
  decompose [and] H4.
  unfold var_not_in in *. rewrite Forall_forall in *.
  intros [x' t'] mem.
  destruct mem. inversion H6. subst.
    intuition.
    auto.
Qed.

Hint Resolve var_neq_fresh_loc : wf.

Hint Constructors
     wf_type
     wf_env
: wf.

Lemma subst_distr_pair :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R) 
         (θ : subst_t D R)  (x : A) (y : B),
    subst θ (x, y) = (subst θ x, subst θ y).
Proof.
  auto.
Qed.

Lemma subst_distr_pair_cons :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R) 
         (θ : subst_t D R) (x : A) (y : B) (l : list (A * B)),
    subst θ ((x, y) :: l) = ((subst θ x, subst θ y) :: subst θ l).
Proof.
  auto.
Qed.

Lemma subst_distr_cons :
  forall (A D R : Type) (SA : Subst A D R)
         (θ : subst_t D R) (x : A) (l : list A),
    subst θ (x :: l) = (subst θ x :: subst θ l).
Proof.
  auto.
Qed.

Lemma fresh_var :
  forall x t Γ,
    var_not_in x Γ -> In (x,t) Γ -> False.
Proof.
  unfold var_not_in in *; pair_crush.
Qed.

(* Lemma var_not_in_exp : *)
(*   forall x e Γ Σ, *)
(*     (x <> ν) -> var_not_in x Γ -> wf_expr Γ Σ e -> (e <> (var_e x)). *)
(* Proof. *)
(*   intros x e Γ Σ neq not_in wf_exp. *)
(*   inversion wf_exp. subst. *)
(*   inversion wf_exp; crush' fresh_var fail. *)
(* Qed. *)

(* Ltac wf_freshvar exp := *)
(*   match goal with *)
(*     | [ x:var, G:type_env, V:var_not_in ?x ?G, H: wf_expr ?G _ |- _ ] =>  *)
(*       let V1 := fresh "V"  in *)
(*       set (V1 := V); *)
(*       eapply var_not_in_exp with (e := exp) in V1 *)
(*    end. *)

Lemma wf_type_prop : 
  forall Γ Σ ν τ φ,
    wf_type Γ Σ { ν : τ | φ } -> wf_prop Γ Σ φ.
Proof.
  pair_crush' False wf_type.
Qed.

Hint Constructors wf_expr : wf.

Lemma wf_expr_ty_expr :
  forall Γ Σ Ξ e T,
    expr_type Γ Σ Ξ e T -> 
    wf_expr Γ Σ e.
Proof.
  intros ? ? ? ? ? H.
  dependent induction H; eauto with wf.
Qed.
 
Ltac invert_wf_expr :=
  match goal with
    | [ e1 : expr, e2 : expr, H : wf_expr _ (fun_e _ ?e1 ?e2) |- appcontext[?e1] ] =>
      inversion H; crush
    | [ e1 : expr, e2 : expr, H : wf_expr _ (fun_e _ ?e1 ?e2) |- appcontext[?e2] ] =>
      inversion H; crush
  end.

Ltac break_wf_e := 
  repeat constructor; 
  unfold subst in *;
  unfold subst_var_one in *;
  simpl;
  invert_wf_expr.

Hint Unfold subst.
Hint Unfold subst_var_one.

Lemma wf_expr_subst :
  forall Γ Σ e x,
    wf_expr Γ Σ e -> var_in x Γ ->
    wf_expr Γ Σ (subst (subst_var_one ν x) e).
Proof.
  intros; unfold var_in in *; induction e; autounfold in *; simpl.
  auto.
  match goal with
    | [ |- context[eq_dec ?x ?v] ] => destruct (eq_dec x v); crush' wf_var_ctx fail
    | _ => crush
  end.
  constructor; eauto with wf;
  inversion H; eauto.
Qed.

Lemma wf_prop_subst :
  forall Γ Σ φ x,
    wf_prop Γ Σ φ -> var_in x Γ ->
    wf_prop Γ Σ (subst (subst_var_one ν x) φ).
Proof.
  induction φ; intros; constructor; crush' wf_expr_subst ((wf_type, wf_prop), wf_expr).
Qed.

Lemma wf_not_in :
  forall x t x' Γ Σ ,
    var_not_in x' Γ -> wf_type Γ Σ t -> (x,t) ∈ Γ ->
    x <> x'.
Proof.
  intros; unfold var_not_in in *; crush; app_pair; crush.
Qed.

Lemma wf_expr_cons :
  forall G Hp e v t,
         wf_expr G Hp e -> wf_expr ((v,t) :: G) Hp e.
Proof.
  intros. induction H; eauto with wf.
Qed.

Lemma wf_expr_heap_cons :
  forall G Hp e l v t,
    wf_expr G Hp e -> wf_expr G ((l, (v, t)) :: Hp) e.
Proof.
  intros. induction H; eauto with wf.
Qed.

Hint Constructors wf_prop : wf.

Lemma wf_env_ty_cons :
  forall G Hp t v' t',
    wf_type G Hp t -> wf_type ((v',t') :: G) Hp t.
Proof.
  intros.
  inversion H. subst.
  induction H0.
  + eauto with wf.
  + eauto using wf_expr_cons with wf. 
  + constructor. constructor. 
    specialize (IHwf_prop (wf_reft_t Γ Σ b p H0)). inversion IHwf_prop. subst. assumption.
  + constructor. constructor.
    inversion H. subst.
    specialize (IHwf_prop1 (wf_reft_t Γ Σ b p1 H0_)).
    inversion IHwf_prop1. assumption. 
    specialize (IHwf_prop2 (wf_reft_t Γ Σ b p2 H0_0)).
    inversion IHwf_prop2. assumption. 
  + constructor. constructor.
    inversion H. subst.
    specialize (IHwf_prop1 (wf_reft_t Γ Σ b p1 H0_)).
    inversion IHwf_prop1. assumption.
    specialize (IHwf_prop2 (wf_reft_t Γ Σ b p2 H0_0)).
    inversion IHwf_prop2. assumption. 
Qed.
  
Hint Resolve wf_env_ty_cons : wf.

Lemma wf_hp_ty_cons :
  forall G Hp t l x t',
    wf_type G Hp t ->
    wf_type G ((l, (x,t')) :: Hp) t.
Proof.
  intros.
  inversion H. subst.
  induction H0.
  + eauto with wf.
  + eauto using wf_expr_heap_cons with wf.
  + do 2 constructor.
    specialize (IHwf_prop (wf_reft_t Γ Σ b p H0)). inversion IHwf_prop. subst. assumption.
  + constructor. constructor.
    inversion H. subst.
    specialize (IHwf_prop1 (wf_reft_t Γ Σ b p1 H0_)).
    inversion IHwf_prop1. assumption. 
    specialize (IHwf_prop2 (wf_reft_t Γ Σ b p2 H0_0)).
    inversion IHwf_prop2. assumption. 
  + constructor. constructor.
    inversion H. subst.
    specialize (IHwf_prop1 (wf_reft_t Γ Σ b p1 H0_)).
    inversion IHwf_prop1. assumption.
    specialize (IHwf_prop2 (wf_reft_t Γ Σ b p2 H0_0)).
    inversion IHwf_prop2. assumption. 
Qed.

Hint Resolve wf_hp_ty_cons : wf.

Lemma wf_env_ty :
  forall G Hp x t,
    (x,t) ∈ G  -> wf_env Hp G -> wf_type G Hp t.
Proof.
  induction G as [ | [x' t']].
  + intros. inversion H.
  + intros. (* unfold In in H. destruct H. *)
    apply in_inv in H.
    destruct H.
    inversion H.
    subst.
    inversion H0.
    assumption.
    apply wf_env_ty_cons.
    apply IHG with (x:= x).
    assumption.
    inversion H0.
    subst.
    assumption.
Qed.

Lemma wf_env_cons_ty :
  forall G H x t,
    wf_env H ((x,t) :: G) -> wf_type ((x,t) :: G) H t.
Proof.
  intros.
  apply wf_env_ty with (x := x); firstorder.
Qed.

Lemma wf_env_ty_binding :
  forall G H x b p,
    wf_env H G ->
    (x, { ν : b | p }) ∈ G ->
    wf_type G H { ν : b | p }.
Proof.
  intros.
  apply wf_env_ty with (x := x) (t := { ν : b | p }); assumption.
Qed.

Lemma wf_env_expr_ty :
  forall G H Grd e b p,
    wf_env H G ->
    expr_type G H Grd e { ν : b | p } -> 
    wf_type G H { ν : b | p }.
Proof.
  intros G H Grd e b p wfenv etype.
  inversion etype. 
  + constructor. constructor. auto using wf_vv. constructor.
  + eauto using wf_env_ty_binding.
  + auto.
Qed.

Lemma wf_env_nonmem :
  forall x t G Hp, (x,t) ∈ G -> wf_env Hp G -> x <> ν.
Proof.
  induction G as [| [x' t']].
  + intuition.
  + intros Hp InH WfH.
    apply in_inv in InH.
    inversion WfH. subst.
    destruct InH. 
    inversion H.
    subst.
    apply H3.
    eauto.
Qed.

Lemma wf_env_join :
  forall  (X : guards) Hp (G G' G'' : type_env),
      join_env X Hp G' G'' G -> wf_env Hp G.
Proof. 
  intros. apply H.
Qed.

Ltac varneq :=
  match goal with
    | H : fresh _ _ _ |- _ <> _ =>
      unfold fresh in H; decompose [and] H; varneq
    | H : var_not_in _ _ |- _ <> _ =>
      unfold var_not_in in H;
        rewrite Forall_forall in H;
        auto
  end.

Lemma wf_env_cons_hp :
  forall G H x l t,
  fresh x G H ->
  fresh_loc l G H ->
  (* H2 : wf_type Γ Σ t *)
    wf_env H G -> wf_env ((l, (x,t)) :: H) G.
Proof.
  intros.
  induction G.
  + constructor.
  + destruct a. 
    inversion H2. subst.
    apply wf_env_var;
    eauto with wf.
Qed.

Lemma wf_heap_cons_env :
  forall G H H0 x t,
    bind_not_in x H0 ->
    wf_heap G H H0 -> 
    wf_heap ((x,t) :: G) H H0.
Proof.
  intros G H H0 x t nomem wf.
  induction H0.
  + constructor.
  + inversion wf.
    subst.
    constructor; try assumption.
    unfold bind_not_in in nomem.
    rewrite Forall_forall in nomem.
    repeat split. apply H3. 
    unfold var_not_in. rewrite Forall_forall.
    intros [x' t'] [x'mem | x'mem].
    inversion x'mem; subst.
    specialize (nomem (L l , (x0, t0))).
    intro F.
    apply nomem. left. reflexivity. simpl in F. simpl. congruence.
    varneq.
    eauto using IHlist with wf.
    inversion wf. subst.
    eapply var_neq_fresh_loc.
    inversion wf. subst.
    eauto with wf.
    inversion wf. subst. unfold fresh_loc. destruct l.
    inversion H12. split; auto.
    split.
    destruct H2.
    eauto with wf.
Qed.

Hint Resolve wf_heap_cons_env : wf.

Ltac freshvar :=
  match goal with 
    | [ H : fresh ?v _ _ |- ?v <> ν ] =>
      apply H
    | [ H : fresh ?v _ _ |- var_not_in ?v _ ] =>
      apply H
    | [ H : fresh ?v _ _ |- bind_not_in ?v _ ] =>
      apply H
  end.
    
Ltac varin :=
  try (assumption || congruence );
  match goal with
    | H : (?x, _) ∈ _ |- (?x, _) ∈ _ => eapply H
    | H : (?x, _ ) ∈ ?G |- (?x, _) ∈ (_ :: ?G) =>
      first [ right; varin | left; varin ]
    | _ => idtac
  end.

Ltac wellformed_expr :=
  try first [ eauto with wf
            | eapply wf_var_ctx; try varin 
            | eapply wf_var_hp; try varin
            ].

Ltac wellformed :=
  match goal with
    | |- wf_type _ _ _ => constructor; wellformed
    | |- wf_prop _ _ _ => constructor; wellformed
    | |- wf_expr _ _ _ => constructor; wellformed
    | H : expr_type _ _ _ ?e _ |- wf_expr _ _ _ => induction H; eauto with wf
  end.
    
Lemma wf_env_stmt :
  forall P G G' H H' X s,
    wf_env H G ->
    (P ; G ; H ; X) ⊢ s ::: (G' ; H') ->
    wf_env H' G'.
Proof.
  intros P G G' H H' X s WF J.
  induction J.
  + assumption.
  + assumption. 
  + eauto using wf_env_cons_hp with wf.
  + apply wf_env_var; eauto with wf.
    wellformed.
  + constructor; eauto with wf.
    apply wf_env_cons_hp.
    inversion H3.
    unfold fresh. split; auto.
    inversion H3.
    unfold fresh_loc. split; eauto with wf. split; eauto with wf.
    unfold fresh. split; eauto with wf.
    inversion H3. subst. constructor. assumption. split; assumption.
    inversion H3. subst. unfold fresh_loc. destruct l. split; try assumption.
    eauto using wf_env_cons_hp with wf.
  + apply wf_env_var; try first [assumption | freshvar | wellformed];
    apply IHexpr_type; assumption.
  + apply wf_env_var; ( assumption || constructor || freshvar || wellformed ); constructor.
  + eapply wf_env_join; eauto.
  + auto.
Qed.

(** Or should there just be a tactic...? **)

Ltac freshness :=
  unfold join_heap in *;
  (solve [try constructor; eauto with wf]
  || match goal with
       | H : appcontext[wf_heap ?x ?y] |- wf_heap ?x ?y => apply H
       | H : wf_heap _ _ |- wf_heap _ _ =>
         inversion H; subst; freshness
     end).

Lemma wf_heap_stmt :
  forall P G G' H H' X s,
    wf_heap G H ->
    (P ; G ; H ; X) ⊢ s ::: (G' ; H') ->
    wf_heap G' H'.
Proof.
  intros until s; intros wf judge; induction judge; freshness.
Qed.

Lemma wf_guards_cons :
  forall Γ Ξ xt,
    wf_guards Γ Ξ -> wf_guards (xt :: Γ) Ξ.
Proof.
  intros.
  assert (I :forall ξ, wf_guard Γ ξ -> wf_guard (xt :: Γ) ξ).
  {
    intros ξ wfg.
    unfold wf_guard in *.
    split.
    destruct wfg as [wf vvmem].
    induction wf.
    + constructor.
    + constructor; destruct xt as [x t]; apply wf_expr_cons; assumption.
    + constructor. apply IHwf. assumption. apply vvmem.
    + constructor. 
      apply IHwf1. assumption. simpl in vvmem. solve [intuition].
      apply IHwf2. assumption. simpl in vvmem. solve [intuition].
    + constructor. 
      apply IHwf1. assumption. simpl in vvmem. solve [intuition].
      apply IHwf2. assumption. simpl in vvmem. solve [intuition].
    + apply wfg.
  }
  unfold wf_guards in *.
  rewrite Forall_forall in *.
  intros ξ xmem.
  specialize (H ξ).
  apply I.
  apply H.
  apply xmem.
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
  forall G G' e,
    wf_expr G e ->
    (forall x, var_in x G -> var_in x G') ->
    wf_expr G' e.
Proof.
  intros.
  induction e.
  + constructor.
  + inversion H.
    unfold var_in in *.
    destruct (H0 v).
    exists t. apply H3.
    apply wf_var with x.
    assumption.
    apply wf_vv.
  + inversion H.
    constructor.
    apply IHe1; assumption.
    apply IHe2; assumption.
Qed.

Lemma wf_prop_bigger :
  forall G G' p,
    wf_prop G p ->
    (forall x, var_in x G -> var_in x G') ->
    wf_prop G' p.
Proof.
  intros.
  induction p.
  + constructor.
  + inversion H; constructor; apply wf_expr_bigger with (G := G); assumption. 
  + inversion H; constructor; apply IHp; assumption.
  + inversion H. constructor. apply IHp1. assumption. apply IHp2. assumption.
  + inversion H. constructor. apply IHp1. assumption. apply IHp2. assumption.
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

Lemma wf_guards_join :
  forall Ξ Γ1 Γ2 Γ y,
    join_env Ξ Γ1 Γ2 Γ -> 
      var_in y Γ1 -> 
      var_in y Γ2 ->
      var_in y Γ.
Proof.
  intros.
  unfold join_env in *.
  rewrite Forall_forall in *.
  apply H.
  auto.
Qed.

Hint Resolve env_monotonic wf_guards_join wf_guard_bigger wf_env_stmt : wf.

Lemma wf_guards_stmt :
  forall P G G' H H' X s,
    (P ; G ; H ; X) ⊢ s ::: (G' ; H') ->
    wf_env G ->
    wf_guards G X ->
    wf_guards G' X.
Proof.
  intros P G G' H H' X s J wfenv wfguards.
  induction J.
  + assumption.
  + apply wf_guards_cons; assumption.
  + assumption.
  + apply wf_guards_cons; assumption.
  + apply wf_guards_cons; assumption. 
  + unfold wf_guards in *;
    rewrite Forall_forall in *; 
    intros.
    eapply wf_guard_bigger; eauto. 
    intros y yin.
    eauto with wf.
  + eauto with wf.
Qed.

Lemma wf_schema_ret_not_vv :
  forall S,
    wf_schema S -> fst (s_ret S) <> ν.
Proof.
  intros.
  inversion H.
  inversion H2.
  subst.
  destruct S as [xs ts hi ho [xret tret]]. simpl in *.
  inversion H4. subst.
  assumption.
Qed.

Lemma wf_env_no_vv :
  forall Γ,
    wf_env Γ -> var_not_in ν Γ.
Proof.
  induction Γ.
  + intuition.
  + destruct a as [ x t ].
    intro wf.
    inversion wf.
    subst.
    unfold var_not_in in *. rewrite Forall_forall in *.
    intros [ x' t' ].
    intro x'in.
    apply in_inv in x'in.
    destruct x'in.
    inversion H.
    subst.
    assumption.
    apply IHΓ.
    assumption.
    assumption.
Qed.

Hint Unfold wf_subst.
Lemma wf_subst_split :
  forall θ,
    wf_subst θ -> (θ ν = ν /\ forall v, θ v = ν -> v = ν).
Proof.
  intros.
  unfold wf_subst in H.
  split.
  apply H; reflexivity.
  apply H.
Qed.

Ltac wfsubst x :=
  let H := fresh "H" in
  pose (H := wf_subst_split x);
    match goal with
      | G : wf_subst _ |- _ =>
        specialize (H G); destruct H
    end.

Lemma subst_nonfree_expr :
  forall v e e',
    ~ (v ∈ fv_expr e) -> 
    forall w, eval (λ i : var, eval w (subst_one v e' i), hp w) e = eval w e.
Proof.
  induction e.
  * constructor.
  * intros.
    assert (P : v <> v0).
    intro.
    apply H.
    rewrite H0.
    unfold In.
    simpl.
    tauto.
    unfold subst_one.
    simpl.
    destruct (eq_dec v0 v).
      symmetry in e. contradiction.
      reflexivity.
  * intros.
    simpl.
    unfold fv_expr in H.
    fold fv_expr in H.
    rewrite in_app_iff in H.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
    intuition.
    intuition.
Qed.

Lemma subst_distr_andp:
  forall (θ : subst_t var expr) (P Q : assert),
    (subst θ (andp P Q) = (andp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_andp_var:
  forall (θ : subst_t var var) (P Q : assert),
    (subst θ (andp P Q) = (andp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_andp' :
  forall (θ : subst_t var expr) (P Q : assert) w,
    (subst θ (andp P Q) w = (andp (subst θ P) (subst θ Q)) w).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_andp_var' :
  forall (θ : subst_t var var) (P Q : assert) w,
    (subst θ (andp P Q) w = (andp (subst θ P) (subst θ Q)) w).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_orp:
  forall (θ : subst_t var expr) (P Q : assert),
    (subst θ (orp P Q) = (orp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_distr_imp :
  forall (θ : subst_t var expr) (P Q : assert),
    (subst θ (imp P Q) = (imp (subst θ P) (subst θ Q))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma subst_FF :
  forall θ, subst θ FF = FF.
Proof.
  reflexivity.
Qed.

Lemma subst_emp :
  forall θ, subst θ emp = emp.
Proof.
  reflexivity.
Qed.

Lemma subst_nonfree_prop :
  forall ξ v e,
    ~ (v ∈ fv_prop ξ) ->
    (subst (subst_one v e) (sep_pred ξ) = sep_pred ξ).
Proof.
  intros.
  induction ξ.
  + split; apply derives_refl.
  + destruct b. 
    unfold subst, Subst_pred, subst_pred, sep_pred.
    simpl in H.
    apply pred_ext;
    intro;
    simpl;
    try rewrite subst_nonfree_expr with (e := e0) (v := v) (e' := e);
    try rewrite subst_nonfree_expr with (e := e1) (v := v) (e' := e);
    first [ apply derives_refl | intuition ].
  + unfold sep_pred. fold sep_pred.
    repeat rewrite subst_distr_andp.
    repeat rewrite subst_distr_imp.
    rewrite subst_FF.
    rewrite IHξ.
    reflexivity.
    intuition.
  + unfold sep_pred. fold sep_pred.
    simpl in H.
    repeat rewrite subst_distr_andp.
    rewrite IHξ1;
    try rewrite IHξ2; 
    first [ reflexivity | intuition ].
  + unfold sep_pred. fold sep_pred.
    simpl in H.
    repeat rewrite subst_distr_andp.
    repeat rewrite subst_distr_orp.
    rewrite IHξ1;
    try rewrite IHξ2; 
    first [ reflexivity | intuition ].
Qed.

Lemma wf_expr_fv :
  forall x e Γ,
    x <> ν -> 
    var_not_in x Γ ->
    wf_expr Γ e ->
    ~ (x ∈ fv_expr e).
Proof.
  intros.
  induction e.
  * intuition.
  * inversion H1. subst.
    unfold fv_expr.
    intro. 
    destruct H2.
    unfold var_not_in in H0.
    rewrite Forall_forall in H0.
    specialize (H0 (x,t)).
    rewrite <- H2 in H0.
    apply H0 in H4.
    intuition.
    intuition.
    intro.
    unfold fv_expr in H3.
    destruct H3.
    intuition.
    intuition.
  * unfold fv_expr. fold fv_expr.
    inversion H1. subst.
    rewrite in_app_iff.
    intro.
    destruct H2.
    apply IHe1; assumption.
    apply IHe2; assumption.
Qed.

Lemma wf_prop_fv :
  forall x p Γ,
    x <> ν ->
    var_not_in x Γ ->
    wf_prop Γ p ->
    ~ (x ∈ fv_prop p).
Proof.
  induction p.
  + intuition.
  + intros Γ neqvv notin wfprop.
    unfold fv_prop.
    rewrite in_app_iff.
    intro.
    inversion wfprop. subst.
    destruct H as [notine | notine0].
    apply wf_expr_fv with (e := e) in notin.
    apply notin.
    apply notine.
    assumption.
    assumption.
    apply wf_expr_fv with (e := e0) in notin.
    apply notin.
    apply notine0.
    assumption.
    assumption.
  + intros Γ neqvv notin wfprop.
    simpl.
    inversion wfprop; subst.
    apply IHp with (Γ := Γ); assumption.
  + intros Γ neqvv notin wfprop.
    simpl.
    inversion wfprop; subst.
    rewrite in_app_iff.
    intro.
    destruct H.
    apply IHp1 with (Γ := Γ) in H; assumption.
    apply IHp2 with (Γ := Γ) in H; assumption.
  + intros Γ neqvv notin wfprop.
    simpl.
    inversion wfprop; subst.
    rewrite in_app_iff.
    intro.
    destruct H.
    apply IHp1 with (Γ := Γ) in H; assumption.
    apply IHp2 with (Γ := Γ) in H; assumption.
Qed.

    
Lemma wf_guard_vv_nonfree :
  forall Γ ξ,
    wf_guard Γ ξ ->
      nonfreevars (sep_pred ξ) ν.
Proof.
  intros.
  unfold wf_guard in H.
  destruct H as [wf fv].
  intuition.
  unfold nonfreevars.
  intro.
  rewrite subst_nonfree_prop.
  apply derives_refl.
  assumption.
Qed.

Lemma wf_guard_nonfree :
  forall x ξ Γ,
    var_not_in x Γ ->
    wf_guard Γ ξ ->
    nonfreevars (sep_pred ξ) x.
Proof.
  intros x ξ Γ nomem wfg.
  destruct (eq_dec x ν).
  + rewrite e. apply wf_guard_vv_nonfree with (Γ := Γ).
    assumption.
  + unfold nonfreevars.
    intros.
    intro e. rewrite subst_nonfree_prop. trivial.
    apply wf_prop_fv with (Γ := Γ).
    assumption.
    assumption.
    apply wfg.
Qed.

Lemma nonfree_distr_andp :
  forall (P Q : assert) x e,
    P |-- subst (subst_one x e) P ->
    Q |-- subst (subst_one x e) Q ->
    P && Q |-- subst (subst_one x e) (P && Q).
Proof.
  intros.
  rewrite subst_distr_andp.
  apply andp_derives; assumption.
Qed.

Lemma wf_guards_vv_nonfree :
  forall Γ Ξ,
    wf_guards Γ Ξ ->
      nonfreevars (sep_guards Ξ) ν.
Proof.
  intros.
  induction Ξ.
  + unfold nonfreevars.
    trivial.
  + unfold sep_guards.
    fold sep_guards.
    inversion H.
    subst.
    pose (P := wf_guard_vv_nonfree Γ a H2).
    unfold nonfreevars in *.
    intro e.
    apply nonfree_distr_andp.
    apply nonfree_distr_andp.
    apply P.
    apply IHΞ.
    assumption.
    rewrite subst_emp.
    apply derives_refl.
Qed.

Lemma wf_guards_nonfree :
  forall x Ξ Γ,
    var_not_in x Γ ->
    wf_guards Γ Ξ ->
    nonfreevars (sep_guards Ξ) x.
Proof.
  intros.
  induction Ξ.
  + unfold nonfreevars. trivial.
  + unfold sep_guards. fold sep_guards.
    inversion H0. subst.
    unfold nonfreevars. intro e.
    pose (P := wf_guard_nonfree x a Γ H H3).
    apply nonfree_distr_andp. 
    apply nonfree_distr_andp. 
    apply P.
    apply IHΞ; assumption.
    rewrite subst_emp.
    apply derives_refl.
Qed.

Lemma wf_expr_ty_expr_fv :
  forall Γ Ξ e T,
    wf_env Γ ->
    expr_type Γ Ξ e T -> 
    ~ (ν ∈ fv_expr e).
Proof.
  intros ? ? ? ? wf H.
  dependent induction H.
  + intuition.
  + pose (wf_env_no_vv Γ wf) as WF.
    unfold var_not_in in WF.
    rewrite Forall_forall in WF.
    intuition.
    simpl in H0.
    destruct H0.
    rewrite H0 in H.
    apply WF with (ν, {ν : τ | φ}).
    assumption.
    reflexivity.
    assumption.
  + apply IHexpr_type.
    assumption.
Qed.