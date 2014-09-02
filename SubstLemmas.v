Add LoadPath "vst".
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Equality.

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
    (forall x, sub x = (var_e x)) ->
    subst_pred sub p = p.
Proof.
  intros. unfold subst_pred. extensionality w. 
  f_equal. extensionality i. 
  specialize (H i).
  rewrite H. reflexivity.
Qed.

Ltac foo :=
  simpl in *;
  subst;
  intuition;
  match goal with
        | [ H : appcontext[eq_dec ?x ?y] |- _ ] => destruct (eq_dec x y); foo
        | |- appcontext[eq_dec ?x ?y] => destruct (eq_dec x y); foo
        | [ H : ?θ ?x = ?x, 
                F : ?θ ?v = ?x,
                    G : forall v : _, ?θ v = ?x -> v = ?x |- _ ] =>
          specialize (G v F); contradiction
        | _ => idtac
  end; first [ contradiction | reflexivity | intuition].


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

Lemma subst_expr :
  forall G x e e',
    x <> ν ->
    var_not_in x G ->
    wf_expr G e -> 
    forall w, 
      (eval (fun i => eval w (subst_one x e' i)) e = eval w e).
Proof.
  intros.
  simpl.
  induction e.
  + reflexivity.
  + simpl. autounfold. destruct (eq_dec v x). 
    * rewrite <- e in H0. unfold var_not_in in H0. inversion H1. rewrite Forall_forall in H0. specialize (H0 (v,t) H4). contradiction H0. reflexivity.
    subst. contradiction H. symmetry. assumption.
    * reflexivity.
  + simpl. rewrite <- IHe1. rewrite <- IHe2. simpl. reflexivity. 
    inversion H1. assumption. 
    inversion H1. assumption. 
Qed.

Lemma subst_singleton :
  forall G p x e,
    x <> ν -> var_not_in x G -> wf_prop G p ->
    (forall w, subst_pred (subst_one x e) (sep_pred p) w = (sep_pred p) w).
Proof.
  induction p.
  + intros; reflexivity.
  + intros.
    inversion H1. 
    unfold subst_pred. simpl. destruct b. 
    repeat rewrite subst_expr with (G := G) (x := x) (e' := e1); first [reflexivity | assumption].
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

Lemma subst_disj_expr :
  forall G θ v,
    disj_subst G θ -> wf_expr G (var_e v) ->
    forall w, eval w (θ v) = w v.
Proof.
  intros.
  destruct H.
  inversion H0.
  rewrite (H1 v). 
  reflexivity.
  exists t; assumption.
  rewrite H.
  reflexivity.
Qed.

Lemma subst_empty_dom_expr :
  forall G θ e,
    disj_subst G θ ->
    wf_expr G e ->
    forall w,
      (eval (fun i => eval w (θ i)) e = eval w e).
Proof.
  intros.
  unfold disj_subst in H. destruct H.
  induction e.
  * reflexivity.
  * simpl. rewrite subst_disj_expr with (G := G). reflexivity. split; assumption. assumption.
  * simpl. inversion H0. rewrite IHe1. rewrite IHe2. reflexivity. assumption. assumption.
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
  + inversion H0. unfold subst_pred. simpl. destruct b.
    repeat rewrite subst_empty_dom_expr with (G := G) (θ := θ); first [reflexivity | assumption].
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

Lemma subst_vv_expr :
  forall G θ x e,
    disj_subst G θ ->
    wf_expr G e ->
    θ x = var_e x ->
    forall w,
      (eval (fun i => eval (fun i' => eval w (θ i')) (subst_one ν (var_e x) i)) e)
      = eval (fun i => eval w (subst_one ν (var_e x) i)) e.
Proof.
  intros.
  induction e.
  * reflexivity.
  * simpl. unfold subst_one. destruct (eq_dec v ν). 
    + simpl. subst. rewrite H1. reflexivity.
    + simpl. apply subst_disj_expr with (G := G); assumption.
  * simpl. inversion H0. subst. rewrite IHe1. rewrite IHe2. reflexivity. assumption. assumption.
Qed.

Lemma subst_vv_pred' :
  forall G p x θ,
    disj_subst G θ -> wf_prop G p -> θ x = (var_e x)-> 
    forall w,
    (subst_pred θ (subst_pred (subst_one ν (var_e x)) (sep_pred p)) w
               =
    subst_pred (subst_one ν (var_e x)) (sep_pred p) w).
Proof.
  intros.
  induction p.
  + constructor.
  + inversion H0. destruct b. unfold subst_pred. 
    unfold sep_pred. repeat rewrite subst_vv_expr with (G := G); first [reflexivity | assumption].
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

(* Lemma subst_vv_base : *)
(*   forall b x w θ, *)
(*     θ ν = var_e ν - *)
(*     subst_pred (subst_one ν (var_e x)) (subst_pred θ (sep_base ν b)) w *)
(*                = *)
(*     subst_pred (subst_one ν (var_e x)) (sep_base ν b) w. *)
(* Proof. *)
(*   intros. *)
(*   unfold sep_base. *)
(*   autounfold. *)
(*   simpl.  *)
(*   rewrite H.  *)
(*   simpl. *)
(*   destruct (eq_dec ν ν). reflexivity. contradiction n. reflexivity. *)
(* Qed. *)

(* Lemma subst_vv_base' : *)
(*   forall b x w θ, *)
(*     θ ν = var_e ν -> θ x = var_e x -> *)
(*     subst_pred θ (subst_pred (subst_one ν (var_e x)) (sep_base ν b)) w *)
(*                = *)
(*     subst_pred (subst_one ν (var_e x)) (sep_base ν b) w. *)
(* Proof. *)
(*   intros. *)
(*   unfold sep_base. *)
(*   autounfold. *)
(*   simpl. *)
(*   destruct (eq_dec ν ν). *)
(*   * simpl. rewrite H0. reflexivity. *)
(*   * simpl. rewrite H. reflexivity. *)
(* Qed. *)

(* Lemma subst_vv_base_ap : *)
(*   forall b x w, *)
(*     subst_pred (subst_one ν (var_e x)) (sep_base ν b) w *)
(*     = sep_base x b w. *)
(* Proof. *)
(*   intros. *)
(*   unfold sep_base. *)
(*   unfold subst_pred. *)
(*   unfold exp.  *)
(*   unfold subst_one. *)
(*   simpl. *)
(*   destruct (eq_dec ν ν). *)
(*   simpl. reflexivity. *)
(*   contradiction n. *)
(*   reflexivity. *)
(* Qed.  *)

(* Lemma subst_vv_expr2 : *)
(*   forall G θ p x, *)
(*     disj_subst G θ -> wf_prop G p -> θ x = (var_e x) ->  *)
(*     forall w, *)
(*     (sep_pred (subst (subst_one ν (var_e x)) p) (λ i : var, eval w (θ i)) = *)
(*      sep_pred (subst (subst_one ν (var_e x)) p) w). *)
(* Proof. *)  

Lemma subst_expr_help2 :
  forall θ e w,
    eval w (Language.subst_expr θ e) = eval (fun i => eval w (θ i)) e.
Proof.
  induction e.
  + reflexivity.
  + intros. reflexivity.
  + intros. simpl in *. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Lemma subst_vv_expr2 :
  forall G θ e x,
    disj_subst G θ -> wf_expr G e -> subst θ x = x ->
    forall w,
    eval (λ i : var, eval w (θ i))
      (subst (λ i : var, if eq_dec i ν then x else var_e i) e) =
    eval w (subst (λ i : var, if eq_dec i ν then x else var_e i) e).
Proof.
  unfold subst, Subst_var_expr at 1.
  intros G sub e x disj wf xid.
  induction e.
  + reflexivity.
  + intro w. unfold subst. simpl.
    unfold subst in xid.
    destruct (eq_dec v ν).
    rewrite <- subst_expr_help2. rewrite xid. reflexivity.
    rewrite <- subst_expr_help2. 
    unfold disj_subst in disj.
    destruct disj.
    simpl.
    rewrite H0 with (x := v).
    reflexivity.
    inversion wf. 
    unfold var_in.
    exists t. assumption.
    intuition.
  + intro w.
    simpl.
    inversion wf.
    rewrite IHe1.
    rewrite IHe2.
    unfold subst. reflexivity.
    assumption.
    assumption.
Qed.
    
Lemma subst_vv_pred2 :
  forall G θ p x,
    disj_subst G θ -> wf_prop G p -> subst θ x = x ->
    forall w,
    (sep_pred (subst (subst_one ν x) p) (λ i : var, eval w (θ i)) =
     sep_pred (subst (subst_one ν x) p) w).
Proof.
  intros G sub p x disj wf xxid.
  unfold subst, Subst_prop, subst_one.
  induction p.
  + constructor.
  + intro w. destruct b. simpl.
    (* subst. *)
    inversion wf.
    repeat (rewrite subst_vv_expr2 with (G := G)); first [assumption | reflexivity].
  + intro w.
    simpl. unfold imp.
    rewrite IHp. reflexivity.
    inversion wf; assumption.
  + intro w. simpl. unfold andp.
    inversion wf.
    f_equal; [ rewrite IHp1 | rewrite IHp2 ]; first [assumption | reflexivity].
  + intro w. simpl. unfold orp.
    inversion wf.
    f_equal; [ rewrite IHp1 | rewrite IHp2 ]; first [assumption | reflexivity].
Qed.

Lemma sep_ty_split :
  forall x b p,
    forall w, (sep_ty x { ν : b | p } w =
    (sep_base x b w
    /\ (sep_pred (subst (subst_one ν x) p) w))).
Proof.
  reflexivity.
Qed.

Lemma subst_ty :
  forall G b p x θ w,
    disj_subst G θ -> wf_type G { ν : b | p } -> 
    subst θ x = x -> θ ν = var_e ν ->
      (subst_pred θ (sep_ty x { ν : b | p }) w
       =
       sep_ty x { ν : b | p } w).
Proof.
  intros.
  unfold subst_pred.
  rewrite sep_ty_split.
  rewrite sep_ty_split.
  f_equal.
  fold (subst_pred θ (sep_base x b) w).
  unfold sep_base, subst_pred.
  simpl.
  destruct b.
  simpl.
  unfold exp.
  rewrite <- subst_expr_help2.
  unfold subst, Subst_var_expr in H1.
  rewrite H1.
  reflexivity.
  rewrite subst_vv_pred2 with (G := G) (θ := θ).
  reflexivity.
  assumption.
  apply wf_type_prop with (ν := ν) (τ := b).
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
    wf_env G -> disj_subst G θ -> θ ν = var_e ν -> 
    forall w,
      subst_pred θ (sep_env G) w = sep_env G w.
Proof.
  induction G.
  + intros. reflexivity.
  + intros. destruct a. unfold sep_env. unfold andp.
    unfold subst_pred. f_equal. 
    fold (subst_pred θ (sep_ty (var_e v) r) w).
    inversion H. inversion H8. subst.
    apply subst_ty with (G := (v, { ν : b | p }) :: G).
    assumption.
    assumption.
    apply H0. unfold var_in. exists { ν : b | p }. left. reflexivity.
    assumption.
    apply IHG. 
    inversion H. assumption.
    apply disj_subst_cons in H0. apply H0.
    assumption.
Qed.

Lemma subst_dom_guards :
  forall Ξ Γ θ,
    wf_guards Γ Ξ -> 
    disj_subst Γ θ ->
    forall w,
      subst_pred θ (sep_guards Ξ) w = sep_guards Ξ w.
Proof.
  induction Ξ.
  + reflexivity.
  + intros.
    unfold sep_guards. fold sep_guards.
    unfold andp.
    unfold subst_pred.
    inversion H. subst. 
    f_equal.
    fold (subst_pred θ (sep_pred a) w).
    apply subst_empty_dom_pred with (G := Γ).
    assumption.
    apply H3.
    apply IHΞ with (Γ := Γ); assumption.
Qed.

Lemma subst_dom_andp :
  forall P Q θ,
    (forall w, subst_pred θ P w = P w) ->
    (forall w, subst_pred θ Q w = Q w) ->
    (forall w, subst_pred θ (P && Q) w = (P && Q) w).
Proof.
  intros.
  unfold andp.
  rewrite <- H.
  rewrite <- H0.
  reflexivity.
Qed.

Lemma subst_env_cons : 
  forall G θ x t w,
      (subst_pred θ (sep_env ((x,t) :: G)) w) = 
                    (subst_pred θ (sep_ty (var_e x) t) w /\ subst_pred θ (sep_env G) w).  
Proof.
  reflexivity.
Qed.

Lemma subst_ty_prop :
  forall p (θ : subst_t var expr) w,
    subst θ (sep_pred p) w = sep_pred (subst θ p) w.
Proof.
  induction p.
  * constructor.
  * intros.
    destruct b.
    unfold subst.
    unfold Subst_pred.
    unfold subst_pred.
    unfold Subst_prop.
    unfold subst_prop.
    unfold subst.
    unfold Subst_var_expr.
    unfold subst_expr_var.
    unfold sep_pred.
    simpl. f_equal.
    induction e.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    - induction e0.
      + reflexivity.
      + reflexivity.
      + simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
 * intros. 
   specialize (IHp θ w).
   unfold subst in *.
   unfold Subst_pred in *.
   unfold subst_pred in *.
   unfold Subst_prop in *.
   unfold subst_prop in *.
   simpl.
   unfold imp.
   rewrite <- IHp.
   reflexivity.
 * intros. 
   specialize (IHp1 θ w).
   specialize (IHp2 θ w).
   unfold subst in *.
   unfold Subst_pred in *.
   unfold subst_pred in *.
   unfold Subst_prop in *.
   unfold subst_prop in *.
   simpl.
   unfold andp.
   rewrite <- IHp1.
   rewrite <- IHp2.
   reflexivity.
 * intros. 
   specialize (IHp1 θ w).
   specialize (IHp2 θ w).
   unfold subst in *.
   unfold Subst_pred in *.
   unfold subst_pred in *.
   unfold Subst_prop in *.
   unfold subst_prop in *.
   simpl.
   unfold orp.
   rewrite <- IHp1.
   rewrite <- IHp2.
   reflexivity.
Qed.

(* Lemma subst_ty_base : *)
(*   forall x t θ w, *)
(*     subst θ (sep_base x t) w = sep_base (subst θ x) t w. *)
(* Proof. *)
(*   unfold subst, Subst_pred, Subst_var_expr.  *)
(*   reflexivity. *)
(* Qed. *)

Lemma subst_env_ty :
  forall xts (θ : subst_t var expr) x t w,
    subst θ (sep_env ((x,t)::xts)) w = (subst θ (sep_ty (var_e x) t) w /\ subst θ (sep_env xts) w).
Proof.
  induction xts as [| [x' t']].
  * reflexivity.
  * intros.
    simpl.
    split.
Qed.

Lemma subst_length :
  forall (A D R: Type) (SX : Subst A D R) (θ : subst_t D R) (xs : list A),
    length xs = length (subst θ xs).
Proof.
  induction xs; crush.
Qed.

Lemma split_compute :
  forall A B xs (a:A) (b:B),
    split ((a,b) :: xs) = (a :: fst (split xs), b :: snd (split xs)).
Proof.
  intros.
  simpl.
  destruct (split xs).
  reflexivity.
Qed.

Lemma split_fst :
  forall A B xs (a:A) (b:B),
    fst (split ((a, b) :: xs)) = a :: (fst (split xs)).
Proof.
  induction xs.
  reflexivity.
  destruct a as [x y].
  intros.
  rewrite split_compute with (a := a) (b := b). simpl.
  reflexivity.
Qed.

Lemma split_snd :
  forall A B xs (a:A) (b:B),
    snd (split ((a, b) :: xs)) = b :: (snd (split xs)).
Proof.
  induction xs.
  reflexivity.
  destruct a as [x y].
  intros.
  rewrite split_compute with (a := a) (b := b). simpl.
  reflexivity.
Qed.

Lemma subst_split_fst :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R)
         (xys : list (A * B)) (θ : subst_t D R),
    subst θ (fst (split xys)) = fst (split (subst θ xys)).
Proof.
  intros.
  induction xys.
  + reflexivity.
  + unfold subst at 2. unfold Subst_list. unfold subst_list. fold subst_list. 
    destruct a. unfold subst. unfold Subst_prod at 1. unfold subst_prod at 1.
    rewrite split_fst with (a := subst θ a).
    unfold subst at 2 in IHxys. unfold Subst_list in IHxys. rewrite <- IHxys.
    rewrite split_fst. unfold subst_list. fold subst_list. reflexivity.
Qed.

Lemma subst_split_snd :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R)
         (xys : list (A * B)) (θ : subst_t D R),
    subst θ (snd (split xys)) = snd (split (subst θ xys)).
Proof.
  intros.
  induction xys.
  + reflexivity.
  + unfold subst at 2. unfold Subst_list. unfold subst_list. fold subst_list. 
    destruct a. unfold subst. unfold Subst_prod at 1. unfold subst_prod at 1.
    rewrite split_snd with (a := subst θ a).
    unfold subst at 2 in IHxys. unfold Subst_list in IHxys. rewrite <- IHxys.
    rewrite split_snd. unfold subst_list. fold subst_list. reflexivity.
Qed.

Lemma combine_cons :
  forall A B (a:A) (b:B) xs ys,
    combine (a :: xs) (b :: ys) = (a, b) :: combine xs ys.
Proof.
  reflexivity.
Qed.

Lemma subst_combine_proj :
  forall (A B D R : Type) (SA : Subst A D R) (SB : Subst B D R)
         (xys : list (A * B)) (θ : subst_t D R),
    subst θ xys = combine (subst θ (fst (split xys))) (subst θ (snd (split xys))).
Proof.
  intros.
  induction xys.
  * reflexivity.
  * destruct a. 
    rewrite split_fst.
    rewrite split_snd.
    unfold subst at 2 3.
    unfold Subst_list. unfold subst_list. fold subst_list.
    rewrite combine_cons.
    unfold subst at 2 3 in IHxys.
    unfold Subst_list in IHxys.
    rewrite <- IHxys.
    reflexivity.
Qed.

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

Lemma sep_base_subst :
  forall θ b,
    θ ν = ν ->
    forall w,
      sep_base (subst θ (var_e ν)) b w = subst θ (sep_base (var_e ν) b) w.
Proof.
  constructor.
Qed.

Hint Unfold subst : subst.
Hint Unfold Subst_var_var : subst.
Hint Unfold Subst_reft_var : subst.
Hint Unfold Subst_prop_var : subst.
Hint Unfold Subst_pred_var : subst.
Hint Unfold subst_r_var : subst.
Hint Unfold subst_pred_var : subst.

Ltac unfold_subst := autounfold with subst.
Ltac unfold_subst_all := repeat autounfold with subst in *.

Lemma sub_pred_rewrite :
  forall p x θ w,
  subst θ (sep_pred (subst (subst_one ν (var_e x)) p)) w
  = sep_pred (subst (subst_one ν (var_e x)) p) (fun i => eval w (var_e (θ i))).
Proof.
  reflexivity.
Qed.

Ltac unfold_t :=
  unfold subst in *;
  unfold subst_one in *;
  simpl in *;
  unfold subst in *; simpl in *;
  unfold Subst_pred_var in *;
  unfold Subst_pred in *;
  unfold subst_pred;
  unfold subst_pred_var in *.

(*
Lemma foo1 :
  forall θ x e w,
    θ ν = ν ->
    θ x = x ->
   (eval (λ i : var, w (θ i))
     (subst
        (λ i : var, if eq_dec i ν then var_e x else var_e i) e) =
   eval (λ i : var, w (if eq_dec i ν then x else θ i)) e).
Proof.
  intros.
  induction e.
  + reflexivity.
  + simpl.
    unfold subst. simpl. destruct (eq_dec v ν). simpl. rewrite H0. reflexivity.
    reflexivity.
  + simpl.
    unfold subst in *.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
Qed.

Lemma foo:
  forall x e1 e2 θ,
    θ ν = ν ->
    θ x = x ->
    (forall v, v <> ν -> θ v <> ν) ->
    forall w,
    (subst θ (sep_pred (subst (subst_one ν (var_e x)) (e1 .= e2))) w =
     (subst (fun i => if eq_dec i ν then x else θ i)
           (sep_pred (e1 .= e2)) w)).
Proof.
  intros.
  unfold_t. simpl.
  unfold Subst_var_expr.
  f_equal.
  apply foo1. assumption. assumption.
  apply foo1. assumption. assumption.
Qed.

Lemma bar :
  forall p x θ,
    θ ν = ν ->
    θ x = x ->
    (forall v, v <> ν -> θ v <> ν) ->
    (forall w,
      subst θ (sep_pred (subst (subst_one ν (var_e x)) p)) w =
      subst (fun i => if eq_dec i ν then x else θ i) (sep_pred p) w).
Proof.
  induction p.
  + constructor.
  + intros. 
    destruct b.
    rewrite foo.
    reflexivity.
    assumption.
    assumption.
    assumption.
  + intros.
    unfold subst in *.
    simpl. unfold imp. 
    unfold Subst_pred_var. unfold subst_pred_var.
    fold (subst_pred_var θ (sep_pred (Subst_prop (subst_one ν (var_e x)) p)) w).
    rewrite IHp.
    simpl.
    unfold Subst_pred_var. unfold subst_pred_var. simpl. reflexivity.
    assumption.
    assumption.
    assumption.
  + intros.
    unfold subst in *.
    simpl. unfold andp.
    unfold Subst_pred_var. unfold subst_pred_var.
    fold (subst_pred_var θ (sep_pred (Subst_prop (subst_one ν (var_e x)) p1)) w).
    fold (subst_pred_var θ (sep_pred (Subst_prop (subst_one ν (var_e x)) p2)) w).
    simpl.
    unfold Subst_pred_var. unfold subst_pred_var. simpl. 
    f_equal.
    apply IHp1; assumption.
    apply IHp2; assumption.
  + intros.
    unfold subst in *.
    simpl. unfold orp.
    unfold Subst_pred_var. unfold subst_pred_var.
    fold (subst_pred_var θ (sep_pred (Subst_prop (subst_one ν (var_e x)) p1)) w).
    fold (subst_pred_var θ (sep_pred (Subst_prop (subst_one ν (var_e x)) p2)) w).
    simpl.
    unfold Subst_pred_var. unfold subst_pred_var. simpl. 
    f_equal.
    apply IHp1; assumption.
    apply IHp2; assumption.
Qed.

Lemma qux' :
  forall θ x e w,
    θ ν = ν ->
    θ x = x ->
    (forall v, v <> ν -> θ v <> ν) ->
  eval (λ i : var, eval (λ i0 : var, w (θ i0)) (subst_one ν (var_e x) i)) e =
   eval (λ i : var, eval w (if eq_dec i ν then var_e x else var_e i)) (subst θ e).
Proof.
  intros.
  unfold subst.
  unfold subst_one.
  unfold Subst_var_var_expr.
  induction e.
  + reflexivity.
  + simpl.
    destruct (eq_dec v ν).
    simpl.
    destruct (eq_dec (θ v) ν).
    rewrite H0. reflexivity.
    contradiction n. rewrite e. assumption.
    destruct (eq_dec (θ v) ν).
    exfalso; apply H1 with v; assumption.
    reflexivity.
  + simpl.
    f_equal.
    rewrite <- IHe1. reflexivity.
    rewrite <- IHe2. reflexivity.
Qed.

Lemma qux :
  forall p x θ w,
    θ ν = ν ->
    θ x = x ->
    (forall v, v <> ν -> θ v <> ν) ->
    (sep_pred p
         (λ i : var, eval (λ i0 : var, w (θ i0)) (subst_one ν (var_e x) i))
         <->
         sep_pred (Subst_prop_var θ p)
                  (λ i : var, eval w (if eq_dec i ν then var_e x else var_e i))).
Proof.
  intros.
  induction p.
  + repeat constructor.
  + intros. 
    destruct b. constructor.
    intro. unfold Subst_prop_var. unfold subst_prop_var.
    unfold sep_pred in *.
    rewrite <- qux'.
    rewrite <- qux'. 
    apply H2. 
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    intro. unfold Subst_prop_var. unfold subst_prop_var.
    unfold sep_pred in *.
    rewrite  qux'.
    rewrite  qux'. 
    apply H2. 
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
  + constructor.
    simpl. unfold imp.
    rewrite IHp.
    auto.
    simpl.
    unfold imp.
    rewrite IHp.
    auto.
  + constructor.
    simpl.
    unfold andp.
    rewrite IHp1.
    rewrite IHp2.
    auto.
    simpl.
    unfold andp.
    rewrite IHp1.
    rewrite IHp2.
    auto.
  + constructor.
    simpl.
    unfold orp.
    rewrite IHp1.
    rewrite IHp2.
    auto.
    simpl.
    unfold orp.
    rewrite IHp1.
    rewrite IHp2.
    auto.
Qed.

Lemma sep_ty_subst :
  forall b p x θ,
    θ ν = ν ->
    θ x = x ->
    (forall v, v <> ν -> θ v <> ν) ->
    (forall w,
      subst θ (sep_ty x { ν : b | p }) w <->
      sep_ty (subst θ x) (subst θ { ν : b | p }) w).
Proof.
  intros.
  unfold sep_ty.
  unfold subst.
  unfold Subst_reft_var. unfold subst_r_var.
  unfold Subst_pred_var. unfold subst_pred_var.
  unfold subst_pred.
  unfold andp.
  constructor.
  intro.
  destruct H2.
  split. 
  clear H3.
  simpl.
  unfold Subst_var_var in *. unfold subst_var.
  (** NEW **)
  destruct H2.
  exists x0.
  simpl in *.
  rewrite H0 in *.
  apply H2.
  (** NEW **)
  unfold subst_one.
  simpl in *.
  unfold subst.
  unfold Subst_var_var.
  unfold subst_var.
  rewrite H0.
  unfold Subst_prop in *.
  unfold subst_one in *.
  rewrite <- qux. assumption. assumption. assumption. assumption.
  intros.
  destruct H2.
  split.
  clear H3.
  simpl. unfold subst in *. unfold Subst_var_var in *. unfold subst_var in *. simpl in *.
  rewrite H in H2. rewrite H0 in H2. 
  unfold sep_base in *.
  destruct H2.
  exists x0. simpl in *.
  unfold subst_one in *.
  destruct (eq_dec ν ν).
  simpl in *.
  rewrite H0.
  apply H2.
  contradiction n. reflexivity.
  simpl.
  unfold subst_one in *.
  apply qux.
  assumption.
  assumption.
  assumption.
  unfold subst in H3. simpl in H3.
  unfold Subst_var_var in H3. unfold subst_var in H3.
  rewrite H0 in H3.
  rewrite H in H3.
  apply H3.
Qed.
*)

Lemma subst_one_is_disj :
  forall G x v,
    x <> ν ->
    wf_env G ->
    var_not_in x G ->
    disj_subst G (subst_one x v).
Proof.
  intros.
  split.
    unfold subst_one.
    destruct (eq_dec ν x).
    intuition.
    reflexivity.
  intro x'.
  intro.
  unfold subst_one.
  destruct (eq_dec x' x).
    unfold var_in in H2.
    destruct H2.
    nonsense_var.
    reflexivity.
Qed.

Lemma eval_distr :
  forall θ e v w,
    θ ν = ν ->
    (forall v, θ v = ν -> v = ν) ->
     (eval
        (λ i : var, eval w (if eq_dec i (θ ν) then var_e (θ v) else var_e i))
        (subst θ e)
      =
      (eval
         (λ i : var,
                eval (λ i0 : var, w (θ i0)) (if eq_dec i ν then var_e v else var_e i))
         e)). 
Proof.
  intros.
  unfold subst. unfold Subst_var_var_expr.
  induction e.
  + reflexivity.
  + simpl. rewrite H.
    foo.
  + simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Lemma expr_subst_eq_1 :
  forall θ e v w,
    θ ν = ν ->
    (forall v, θ v = ν -> v = ν) ->
   (eval w
     (subst (λ i : var, if eq_dec i ν then var_e (θ v) else var_e i)
        (subst θ e)) =
    eval (λ i : var, w (θ i))
       (subst (λ i : var, if eq_dec i ν then var_e v else var_e i) e)).
Proof.
  intros.
  unfold subst. unfold Subst_var_expr. unfold Language.subst_expr.
  induction e.
  reflexivity.
  foo.
  simpl in *.
  rewrite <- IHe1.
  rewrite <- IHe2.
  reflexivity.
Qed.

(* Lemma expr_subst_eq_2 : *)
(*   forall θ e v w, *)
(*     θ ν = var_e ν -> *)
(*     (forall e, Language.subst_expr θ e = var_e ν -> e = var_e ν) -> *)
(*    (eval w *)
(*      (subst (λ i : var, if eq_dec i ν then θ v else var_e i) *)
(*         (subst θ e)) = *)
(*     eval (λ i : var, eval w (θ i)) *)
(*        (subst (λ i : var, if eq_dec i ν then var_e v else var_e i) e)). *)
(* Proof. *)
(*   intros. *)
(*   induction e. *)
(*   + reflexivity. *)
(*   + unfold subst. simpl. *)
(*     destruct (eq_dec v0 ν). *)
(*     rewrite e. rewrite H. foo. *)
(*     simpl. *)
(*     unfold Subst_var_expr. *)
(*     unfold Language.subst_expr. *)
(*     fold Language.subst_expr. *)
(*     destruct (θ v0). *)
(*     simpl. reflexivity. *)
(*     simpl. destruct (eq_dec v1 ν). *)
(* Admitted. *)
(*   intros. *)
(*   unfold subst. unfold Subst_var_expr. unfold Language.subst_expr. *)
(*   induction e. *)
(*   { reflexivity. } *)
(*   { *)
(*     destruct (eq_dec v0 ν). *)
(*     + simpl. *)
(*       rewrite e. *)
(*       rewrite H. *)
(*       destruct (eq_dec ν ν). *)
(*       reflexivity. intuition. *)
(*     + simpl. *)
(*       f_equal. *)
(*     simpl.  *)
(*     induction (θ v0). *)
(*     reflexivity. *)
    
(*   } *)

(*   simpl in *. *)
(*   rewrite <- IHe1. *)
(*   rewrite <- IHe2. *)
(*   reflexivity. *)
(* Qed. *)

Lemma subst_expr_distr :
  forall θ e1 e2 v w,
    θ ν = ν ->
    (forall v, θ v = ν -> v = ν) ->
   (eval w
     (subst (λ i : var, if eq_dec i ν then var_e (θ v) else var_e i)
        (subst θ e1)) =
   eval w
     (subst (λ i : var, if eq_dec i ν then var_e (θ v) else var_e i)
        (subst θ e2))
   ↔ eval (λ i : var, w (θ i))
       (subst (λ i : var, if eq_dec i ν then var_e v else var_e i) e1) =
     eval (λ i : var, w (θ i))
       (subst (λ i : var, if eq_dec i ν then var_e v else var_e i) e2)).
Proof.
  intros.
  rewrite expr_subst_eq_1.
  rewrite expr_subst_eq_1.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma subst_nonfree_expr2 :
  forall e e' w,
    ~ (ν ∈ fv_expr e) ->
   eval w (Language.subst_expr (subst_one ν e') e) =
   eval w e.
Proof.
  intros.
  induction e.
  + reflexivity.
  + unfold subst_one.
    destruct (eq_dec v ν).
    rewrite e in H.
    exfalso. apply H. left. reflexivity.
    simpl.
    destruct (eq_dec v ν). intuition. reflexivity.
  + simpl.
    simpl in H.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
    simpl in H.
    intro.
    apply H.
    apply in_or_app.
    right. assumption.
    intro.
    apply H.
    apply in_or_app.
    left.
    assumption.
Qed.

Lemma subst_expr_help :
  forall θ v (e : expr) w,
  θ ν = var_e ν ->
  (forall e, ν ∈ fv_expr (Language.subst_expr θ e) → ν ∈ fv_expr e) ->
   eval w
     (Language.subst_expr
        (λ i : var, if eq_dec i ν then Language.subst_expr θ e else var_e i)
        (Language.subst_expr θ (var_e v))) =
   eval (λ i : var, eval w (θ i))
     (Language.subst_expr (λ i : var, if eq_dec i ν then e else var_e i)
        (var_e v)).
Proof.
  intros.
  simpl.
  destruct (eq_dec v ν). 
  { rewrite e0. rewrite H. simpl.
    destruct (eq_dec ν ν). rewrite subst_expr_help2. reflexivity. intuition. }
  { simpl. 
    fold (subst_one ν (Language.subst_expr θ e)).
    rewrite subst_nonfree_expr2.
    reflexivity.
    intro.
    specialize (H0 (var_e v)).
    apply H0 in H1.
    inversion H1.
    intuition.
    inversion H2.
  }
Qed.

Lemma subst_expr_distr' :
  forall θ e e' w,
    θ ν = (var_e ν) ->
    (forall e, ν ∈ fv_expr (Language.subst_expr θ e) → ν ∈ fv_expr e) ->
   eval w
     (subst
        (λ i : var, if eq_dec i ν then Language.subst_expr θ e else var_e i)
        (subst θ e'))
   = eval (λ i : var, eval w (θ i))
       (subst (λ i : var, if eq_dec i ν then e else var_e i) e').
Proof.
  unfold subst. unfold Subst_var_expr.
  simpl.
  intros.
  induction e'.
  + reflexivity.
  + apply subst_expr_help; assumption.
  + simpl. 
    rewrite IHe'1.
    rewrite IHe'2.
    reflexivity.
Qed.
    
Lemma subst_base_distr :
  forall θ b e w,
  sep_base (Language.subst_expr θ e) b w <->
  sep_base e b (λ i : var, eval w (θ i)).
Proof.
  intros θ b e w.
  unfold subst.
  unfold sep_base.
  unfold exp.
  rewrite <- subst_expr_help2.
  reflexivity.
Qed.

Lemma subst_prop_distr :
  forall θ e p w,
   (θ ν = var_e ν) ->
   (forall e, ν ∈ fv_expr (Language.subst_expr θ e) → ν ∈ fv_expr e) ->
  ((sep_pred
    (subst_prop (subst_one ν (Language.subst_expr θ e))
                (subst_prop θ p)) w)
    <->
   (sep_pred (subst_prop (subst_one ν e) p) (λ i : var, eval w (θ i)))).
Proof.
  intros.
  induction p.
  + constructor; reflexivity.
  + destruct b.
    unfold subst_one.
    simpl.
    rewrite subst_expr_distr'.
    rewrite subst_expr_distr'.
    reflexivity.
    assumption.
    assumption.
    assumption.
    assumption.
  + simpl. unfold imp. simpl.
    rewrite <- IHp.
    reflexivity.
  + simpl. unfold andp. rewrite IHp1. rewrite IHp2. reflexivity.
  + simpl. unfold orp. rewrite IHp1. rewrite IHp2. reflexivity.
Qed.

Lemma subst_ty_distr :
  forall θ e b p w,
   θ ν = var_e ν ->
   (forall e, ν ∈ fv_expr (Language.subst_expr θ e) → ν ∈ fv_expr e) ->
   (sep_ty (subst θ e) (subst θ { ν : b | p }) w <->
   subst θ (sep_ty e { ν : b | p }) w).
Proof.
  simpl.
  unfold subst.
  unfold sep_ty.
  intros θ e b p w vvid vvuniq.
  unfold Subst_pred, subst_pred.
  unfold Subst_var_expr, subst_var.
  unfold Subst_prop.
  constructor.
  intros [base prop].
  split.  
  apply subst_base_distr; assumption.
  apply subst_prop_distr; assumption.
  intros [base prop].
  split.
  apply subst_base_distr; assumption.
  apply subst_prop_distr; assumption.
Qed.

Lemma subst_vv_not_in_range_exp :
  forall e,
    ~ (ν ∈ fv_expr e) ->
   (forall v e0, 
      ν ∈ fv_expr (Language.subst_expr (subst_one v e) e0) → ν ∈ fv_expr e0).
Proof.
  unfold subst, Subst_var_expr, subst_one.
  intros.
  induction e0.
  inversion H0.
  simpl.
  simpl in H0.
  destruct (eq_dec v0 v).
    intuition.
    simpl in H0. apply H0.
  simpl.
  apply in_or_app.
  simpl in *.
  apply in_app_or in H0.
  destruct H0.
  left.
  apply IHe0_1.
  assumption.
  right.
  apply IHe0_2.
  assumption.
Qed.

Lemma subst_vv_not_in_range :
  forall θ,
    (forall v, θ v = ν <-> v = ν) ->
    (forall e, ν ∈ fv_expr (Language.subst_expr (λ i : var, var_e (θ i)) e) -> 
             ν ∈ fv_expr e).
Proof.
  unfold subst, Subst_var_var_expr.
  intros.
  induction e.
  inversion H0.
  inversion H0.
  rewrite H in H1.
  rewrite H1.
  simpl. left. reflexivity.
  inversion H1.
  simpl.
  apply in_or_app.
  simpl in H0.
  apply in_app_or in H0.
  destruct H0.
  left.
  apply IHe1. assumption.
  right.
  apply IHe2. assumption.
Qed. 

Lemma subst_lift_expr :
  forall (θ : var -> var) (e : expr),
    subst (fun i => var_e (θ i)) e = subst θ e.
Proof.
  intros.
  induction e.
  + reflexivity.
  + reflexivity.
  + unfold subst in *. simpl in *.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
Qed.

Lemma subst_lift_pred :
  forall (θ : var -> var) (p : reft_prop),
    subst (fun i => var_e (θ i)) p = subst θ p.
Proof.
  intros.
  unfold subst, Subst_prop, Subst_prop_var.
  induction p. 
  + reflexivity.
  + destruct b. simpl.
    repeat rewrite subst_lift_expr.
    reflexivity.
  + simpl. repeat rewrite IHp. reflexivity.
  + simpl. rewrite IHp1. rewrite IHp2. reflexivity.
  + simpl. rewrite IHp1. rewrite IHp2. reflexivity.
Qed.

(* Lemma subst_lift_ty : *)
(*   forall (θ : var -> var) x b p, *)
(*     subst (fun i => var_e (θ i)) (sep *)

Lemma help_me_out :
  forall θ x' b p w,
 (sep_base (var_e (subst θ x')) b &&
           sep_pred (subst (subst_one ν (var_e (subst θ x'))) (subst θ p))) w <->
   sep_ty (subst (λ i : var, var_e (θ i)) (var_e x'))
          (subst (λ i : var, var_e (θ i)) {ν : b | p}) w.
Proof.
  intros. 
  assert (P : var_e (subst θ x') = subst (λ i : var, var_e (θ i)) (var_e x')).
    reflexivity.
  constructor.  {
  intros [A B].
  split. 
  - apply A.
  - rewrite <- P.
    simpl.
    rewrite subst_lift_pred.
    apply B.
  }{
  intros [A B].
  split.
  - apply A.
  - rewrite P.
    simpl.
    rewrite <- subst_lift_pred.
    apply B.
  }
Qed.

Lemma subst_in_env :
  forall Γ xts θ w,
    θ ν = ν ->
    (forall v, θ v = ν <-> v = ν) ->
    Forall (fun xt => wf_type Γ (snd xt)) (subst θ xts) ->
    (sep_env (subst θ xts) w <->
    subst θ (sep_env xts) w).
Proof.
  intros until xts.
  induction xts.
  + constructor; reflexivity.
  + intros θ w vvid vvuniq wf.
    destruct a as [x' [b p]].
    rewrite subst_distr_pair_cons in wf.
    unfold subst.
    unfold Subst_pred_var.
    unfold subst_pred_var.
    unfold sep_env.
    fold sep_env.
    constructor.
    split.
    apply subst_ty_distr.
    rewrite vvid. reflexivity.
    apply subst_vv_not_in_range with (θ := θ).
    apply vvuniq.
    simpl in H.
    apply help_me_out.
    apply H.
    apply IHxts.
    assumption.
    assumption.
    inversion wf; assumption.
    apply H.
    split.
    simpl in H.
    destruct H.
    unfold sep_ty. 
    simpl.
    apply help_me_out.
    rewrite subst_ty_distr.
    apply H.
    rewrite vvid. reflexivity.
    apply subst_vv_not_in_range with (θ := θ).
    assumption.
    apply IHxts.
    assumption.
    assumption.
    inversion wf; assumption.
    apply H.
Qed.