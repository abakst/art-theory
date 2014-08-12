Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

Require Import Types.
Require Import Judge.
Require Import Language.
Require Import ProgramLogic.
Require Import Translation.
Require Import Subst.
Require Import WFLemmas.
Require Import Tactics.

Open Scope pred.
Lemma subst_empty : 
  forall p sub,
    (forall x, sub x = None) ->
    subst_pred sub p = p.
Proof.
  intros. unfold subst_pred. extensionality w. 
  f_equal. extensionality i. 
  specialize (H i).
  rewrite H. reflexivity.
Qed.

Ltac invProp e1 e2 :=
        match goal with
          | [ H : wf_prop _ (rel_r e1 _ e2) |- _ ] =>
            inversion H;
            match goal with
                | [ H : wf_expr _ e1 |- _ ] => inversion H
                | [ H : wf_expr _ e2 |- _ ] => inversion H
            end
        end.

Ltac invTypes :=
  match goal with
    | [ H : wf_type _ { _ : _ | (rel_r ?e1 _ ?e2) } |- _ ] => 
      inversion H; invProp e1 e2
    | [ H : wf_prop _ (rel_r ?e1 _ ?e2) |- _ ] =>
      invProp e1 e2
  end; subst.

Ltac nonsense_var :=
  match goal with
    | [ H : var_not_in ?x _, G: (?v, ?t) ∈ _, X: ?x = ?v |- _ ] =>
      exfalso;
      unfold var_not_in in H; 
      rewrite Forall_forall in H;
      specialize (H (v,t)); 
      intuition
    | [ H : var_not_in ?x _, G: (?v, ?t) ∈ _, X: ?v = ?x |- _ ] =>
      exfalso;
      unfold var_not_in in H; 
      rewrite Forall_forall in H;
      specialize (H (v,t)); 
      intuition
    | [ H : wf_expr _ (var_e ?v), C : var_not_in ?v ?G |- _ ] =>
      exfalso; 
      inversion H; 
      unfold var_not_in in C;
      rewrite Forall_forall in C; 
      solve [match goal with
               | [ _ : (?v, ?t) ∈ ?G |- _ ] => specialize (C (v,t)); intuition
               | _ => intuition  
             end]
    | _ => contradiction; reflexivity
  end.

Hint Unfold subst_pred.
Hint Unfold subst_one.
Hint Unfold exp.
Hint Unfold andp.
Hint Unfold orp.
Hint Unfold imp.
Hint Unfold prop.
  
Ltac break_subst := 
  simpl; autounfold; 
  first 
    [ reflexivity 
    | subst; nonsense_var
    | match goal with 
        | |- appcontext[eq_dec ?x ?y] => 
          destruct (eq_dec x y); subst; break_subst
        | |- context[match (?θ ?v) with
                       | Some _ => _
                       | None => _
                     end] =>
          let Z := fresh "Z" in destruct (θ v) eqn: Z; break_subst
        | [ Z : ?s ?v = Some _, E : disj_subst ?G ?s, H : wf_expr ?G (var_e ?v)
          |- _ ] => 
            unfold disj_subst in E;
            destruct E as [ E1 E2 ];
            inversion H;
            match goal with
              | _ => subst; rewrite E1 in Z; inversion Z
              | [ H2 : (?v, ?t) ∈ ?G |- _ ] =>
                let H3 := fresh "H" in
                assert (H3: var_in v G) by (exists t; assumption);
                  specialize (E2 v H3);
                  rewrite E2 in Z;
                  inversion Z
            end
        | [ H : Some _ = None |- _ ] => inversion H
        | [ H : None = Some _ |- _ ] => inversion H
      end].

Lemma subst_singleton :
  forall G p x e,
    x <> ν -> var_not_in x G -> wf_prop G p ->
    (forall w, subst_pred (subst_one x e) (sep_pred p) w = (sep_pred p) w).
Proof.
  induction p.
  + intros; reflexivity.
  + intros;
    match goal with 
      | [ H: wf_prop _ (rel_r ?e ?b ?e0) |- appcontext[rel_r ?e ?b ?e0] ] =>
        inversion H; destruct e; destruct e0; destruct b; break_subst
    end.
  + intros. simpl. unfold imp. inversion H1. specialize (IHp x e H H0 H4). rewrite <- IHp. reflexivity.
  + intros. simpl. unfold subst_pred. unfold andp. 
    inversion H1. 
    specialize (IHp1 x e H H0 H5).
    specialize (IHp2 x e H H0 H6).
    fold (subst_pred (subst_one x e) (sep_pred p1) w).
    fold (subst_pred (subst_one x e) (sep_pred p2) w).
    rewrite <- IHp1.
    rewrite <- IHp2.
    reflexivity.
  + intros. simpl. unfold imp. inversion H1.
    specialize (IHp1 x e H H0 H5).
    specialize (IHp2 x e H H0 H6).
    simpl. unfold orp. rewrite <- IHp1. rewrite <- IHp2. reflexivity.
Qed.

Lemma subst_empty_dom_base :
  forall x b θ,
    θ x = None -> 
    forall w, 
      (subst_pred θ (sep_base x b) w = sep_base x b w).
Proof.
  intros.
  unfold sep_base.
  simpl. autounfold. rewrite H. reflexivity.
Qed.

Lemma subst_empty_dom_pred :
  forall G p θ,
    disj_subst G θ -> 
    wf_prop G p ->
    forall w, 
      (subst_pred θ (sep_pred p) w = sep_pred p w).
Proof.
  intros.
  induction p.
  + constructor.
  + inversion H0. destruct e; destruct e0; destruct b; break_subst.
  + simpl. autounfold. rewrite <- IHp. reflexivity. inversion H0; assumption.
  + simpl; autounfold; inversion H0. rewrite <- IHp1. rewrite <- IHp2. reflexivity. 
    assumption. assumption.
  + simpl; autounfold; inversion H0. rewrite <- IHp1. rewrite <- IHp2. reflexivity.
    assumption. assumption.
Qed.

  
Lemma subst_vv_pred :
  forall G p x θ,
    disj_subst G θ -> wf_prop G p -> 
    forall w,
    (subst_pred (subst_one ν (var_e x)) (subst_pred θ (sep_pred p)) w
               =
    subst_pred (subst_one ν (var_e x)) (sep_pred p) w).
Proof.
  intros.
  apply subst_empty_dom_pred with (G := G).
  assumption.
  assumption.
Qed.

Lemma subst_vv_pred' :
  forall G p x θ,
    disj_subst G θ -> wf_prop G p -> θ x = None -> 
    forall w,
    (subst_pred θ (subst_pred (subst_one ν (var_e x)) (sep_pred p)) w
               =
    subst_pred (subst_one ν (var_e x)) (sep_pred p) w).
Proof.
  intros.
  induction p.
  + constructor.
  + inversion H0.
    destruct e; destruct e0; destruct b; break_subst.
  + intros. simpl.
    unfold FF.
    unfold prop.
    unfold imp.
    unfold subst_pred at 3. 
    fold (subst_pred (subst_one ν (var_e x)) (sep_pred p) w).
    rewrite <- IHp.
    reflexivity.
    inversion H0.
    assumption.
  + intros. inversion H0.
    specialize (IHp1 H5). specialize (IHp2 H6).
    simpl.
    unfold andp.
    unfold subst_pred at 3.
    fold (subst_pred (subst_one ν (var_e x)) (sep_pred p1) w).
    fold (subst_pred (subst_one ν (var_e x)) (sep_pred p2) w).
    rewrite <- IHp1.
    rewrite <- IHp2.
    reflexivity.
  + intros. inversion H0.
    specialize (IHp1 H5).
    specialize (IHp2 H6).
    simpl.
    unfold orp.
    unfold subst_pred at 3.
    fold (subst_pred (subst_one ν (var_e x)) (sep_pred p1) w).
    fold (subst_pred (subst_one ν (var_e x)) (sep_pred p2) w).
    rewrite <- IHp1.
    rewrite <- IHp2.
    reflexivity.
Qed.

Lemma subst_vv_base :
  forall b x w θ,
    θ ν = None ->
    subst_pred (subst_one ν (var_e x)) (subst_pred θ (sep_base ν b)) w
               =
    subst_pred (subst_one ν (var_e x)) (sep_base ν b) w.
Proof.
  intros.
  unfold sep_base.
  autounfold.
  simpl. rewrite H. destruct (eq_dec ν ν). reflexivity. contradiction n. reflexivity.
Qed.

Lemma subst_vv_base' :
  forall b x w θ,
    θ ν = None -> θ x = None ->
    subst_pred θ (subst_pred (subst_one ν (var_e x)) (sep_base ν b)) w
               =
    subst_pred (subst_one ν (var_e x)) (sep_base ν b) w.
Proof.
  intros.
  unfold sep_base.
  autounfold.
  simpl.
  destruct (eq_dec ν ν). simpl. rewrite H0. reflexivity.
  rewrite H. reflexivity.
Qed.

Lemma subst_vv_base_ap :
  forall b x w,
    subst_pred (subst_one ν (var_e x)) (sep_base ν b) w
    = sep_base x b w.
Proof.
  intros.
  unfold sep_base.
  unfold subst_pred.
  unfold exp. 
  unfold subst_one.
  simpl.
  destruct (eq_dec ν ν).
  simpl. reflexivity.
  contradiction n.
  reflexivity.
Qed.

Lemma sep_ty_split :
  forall x b p,
    forall w, (sep_ty x { ν : b | p } w =
    ((subst_pred (subst_one ν (var_e x)) (sep_base ν b)) w 
    /\ (subst_pred (subst_one ν (var_e x)) (sep_pred p) w))).
Proof.
  intros.
  split.
Qed.

Lemma subst_ty :
  forall G b p x θ w,
    disj_subst G θ -> wf_type G { ν : b | p } -> θ x = None -> θ ν = None ->
      (subst_pred θ (sep_ty x { ν : b | p }) w
       =
       sep_ty x { ν : b | p } w).
Proof.
  intros.
  unfold subst_pred.
  rewrite sep_ty_split.
  rewrite sep_ty_split.
  fold (subst_pred θ (subst_pred (subst_one ν (var_e x)) (sep_pred p)) w).
  fold (subst_pred θ (subst_pred (subst_one ν (var_e x)) (sep_base ν b)) w).
  f_equal. 
  rewrite <- subst_vv_base' with (θ := θ). 
    reflexivity. assumption. assumption.
  rewrite <- subst_vv_pred' with (G := G) (θ := θ). 
    reflexivity. assumption. apply wf_type_prop with (ν := ν) (τ := b).
    assumption. assumption.
Qed.

Lemma disj_subst_cons :
  forall G x t θ,
    disj_subst ((x,t) :: G) θ -> disj_subst G θ.
Proof.
  induction G.
  + intros. 
    unfold disj_subst in *.
    destruct H.
    split.
    assumption.
    intros.
    unfold var_in in H1.
    destruct H1.
    inversion H1.
  + intros.
    unfold disj_subst in *.
    destruct H.
    split.
    assumption.
    destruct a.
    intros.
    apply H0.
    unfold var_in in H1.
    unfold var_in.
    destruct H1.
    unfold In.
    unfold In in H1.
    destruct H1. inversion H1. subst.
    exists x1. right. left. assumption.
    fold (In (x0, x1) G) in H1.
    exists x1.
    right.
    right.
    assumption.
Qed.

Lemma subst_dom_env :
  forall G θ,
    wf_env G -> disj_subst G θ -> θ ν = None -> 
    forall w,
      subst_pred θ (sep_env G) w = sep_env G w.
Proof.
  induction G.
  + intros. reflexivity.
  + intros. destruct a. unfold sep_env. unfold andp.
    unfold subst_pred. f_equal. 
    fold (subst_pred θ (sep_ty v r) w).
    inversion H. inversion H8. subst.
    apply subst_ty with (G := G).
    unfold disj_subst in H0.
    apply disj_subst_cons with (x := v) (t := { ν : b | p } ).
    assumption.
    assumption.
    apply H0. unfold var_in. exists { ν : b | p }. left. reflexivity.
    assumption.
    apply IHG. 
    inversion H. assumption.
    apply disj_subst_cons in H0. apply H0.
    assumption.
Qed.

Lemma subst_env_cons : 
  forall G θ x t w,
      (subst_pred θ (sep_env ((x,t) :: G)) w) = 
                    (subst_pred θ (sep_ty x t) w /\ subst_pred θ (sep_env G) w).  
Proof.
  reflexivity.
Qed.