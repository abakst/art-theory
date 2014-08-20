Add LoadPath "vst".
Require Export CpdtTactics.
Require Import Types.
Require Import Judge.
Require Import Subst.
Require Import ProgramLogic.
Require Import Language.
Require Import Translation.
Require Import msl.msl_direct.
Require Import Coq.Unicode.Utf8.

(** Generally Useful ?? **)
Hint Unfold var_not_in.
Hint Unfold var_in.
(* Hint Unfold wf_env. *)
Hint Unfold Subst_var_expr.
Hint Unfold subst.
Hint Unfold derives.
Hint Unfold imp.
Hint Unfold subst_pred.
Hint Unfold sep_base.

Hint Rewrite -> Forall_forall.
Hint Rewrite -> in_inv.

Hint Resolve in_inv.

Hint Constructors wf_prop.

Open Scope pred.

Ltac eval_refl :=
  match goal with
    | [Q : Some _ = eval _ (_ ?e1),
       R : Some _ = eval _ (_ ?e2)
       |- @eq (option value) (Some ?e1) (_ _ (_ ?e2)) ] =>
      simpl in *; try eval_refl

    | [ P : Some ?v = _, 
        Q : Some ?v = _ 
        |- Some ?v = eval _ _ ] => simpl in *; try eval_refl


    | P : ?T |- ?T => assumption

    | [ H: ?x <> ?y,
        P: Some _ = (if eq_dec ?x ?y then _ else _)
      |- Some _ = eval _ _ ] =>
      let e0 := fresh "e0" in
      destruct (eq_dec x y) as [ e0 | e0 ];
      [ rewrite e0 in H; contradiction H; auto | auto ]
                                                 
    | [ V: (var_e ?x' <> var_e ?x),
        H: Some ?v = (if eq_dec ?x ?x' then _ else ?v')
        |- Some ?v = ?v' ] =>
        let e0 := fresh "e0" in
        destruct (eq_dec x x') as [ e0 | e0];
        [ rewrite e0 in V; contradiction V; auto | auto ]

     |[ V : var_e ?x' <> var_e ?x,
        P : Some ?v = ?eval
        |- Some ?v = (if eq_dec ?x ?x' then _ else ?eval)] =>
        let e0 := fresh "e0" in
        destruct (eq_dec x x') as [ e0 | e0 ];
        [ rewrite e0 in V; contradiction V; auto | auto ]

    | [ V : (var_e ?e2 <> var_e ?x),
        Q : Some ?v = _,
        R : Some ?v = (if eq_dec ?x ?e2 then _ else _)
        |- @eq (option value) (Some ?e1) (_ ?e2) ] =>
        let e0 := fresh "e0" in
        try (rewrite <- Q; rewrite R); destruct (eq_dec x e2) as [ e0 | e0 ];
        [ rewrite e0 in V; contradiction V; auto | auto ]; try assumption

     |[ V : var_e ?ex2 ≠ var_e ?x,
        P : Some ?v = _,
        Q : Some ?v = _ ?ex2
        |- Some _ = (if eq_dec ?x ?ex2 then _ else _ ?ex2)] =>
        let e0 := fresh "e0" in
        try (rewrite <- P; rewrite Q); destruct (eq_dec x ex2) as [ e0 | e0 ];
        [ rewrite e0 in V; contradiction V; auto | auto ]

    | [ e1:value, e2:value,
       Q : Some _ = Some ?e1,
       R : Some _ = Some ?e2
        |- (Some ?e1) = (Some ?e2) ] =>
      rewrite <- Q; rewrite R; reflexivity

    | [Q : Some ?e1 = eval _ _,
       R : Some ?e1 = eval _ _
       |- (Some ?e1) = _ ] =>
      simpl in *; try eval_refl

    | [ P : ?e <> (var_e ?x),
        Q : Some ?v = eval _ ?e
        |- Some ?v = eval _ ?e ] => destruct e; simpl in *; try (assumption ||  eval_refl)
  end.

Ltac crush_eval := 
  match goal with
    |         |- Some _ = eval _ _ => eval_refl
    | e2:expr |- Some _ = _ _ ?e2 => destruct e2; eval_refl
  end.

Ltac freshvar :=
  let H := fresh "H" in
  match goal with
    | [ Γ:_, x:_, H1 :_, I : In ?p _ |- _] => 
      set (H := H1);
      unfold var_not_in in H; 
      rewrite Forall_forall in H;
      specialize (H p I);
      simpl in H
    | [ H:var_not_in ?x ((?y, ?r) :: _) |- ?x <> ?y ] =>
      unfold var_not_in in H;
      rewrite Forall_forall in H;
      specialize (H (y,r));
      intuition
    (*   (apply H || intuition) *)
    | [ H:var_not_in ?y ((?x, ?r) :: _) |- ?x <> ?y ] =>
      unfold var_not_in in H;
      rewrite Forall_forall in H;
      specialize (H (x,r));
      apply H
  end.

Ltac app_pair :=
  match goal with 
    | [ x : _, t : _, H : _ |- _ ] => specialize (H (x, t))
  end.

Ltac pair_crush' lems invs := 
  crush' lems invs 
  || app_pair; try crush' lems invs 
  || crush' lems invs ; app_pair; try crush' lems invs.

Ltac pair_crush := pair_crush' False fail.

Ltac reduce_preds :=
  repeat match goal with
    | |- appcontext[(_ && _)] => split; simpl
    | [ H: appcontext[(_ && _)] |- _ ] => destruct H
    | [ H: appcontext[!!(_ = _)] |- _ ] => destruct H (* This one is safe...? *)
  end.

Ltac crush_sep lems inv := 
  crush' lems inv; repeat reduce_preds;
  repeat match goal with
    | [ H : appcontext[(_ || _)] |- _ ] => destruct H
    | [ H : (EX _ : _, _) _ |- _ ] => destruct H
    | [ H : (_ && _) _ |- _ ] => destruct H; crush_sep lems inv
    | [ H : _ (_ && _) _ |- _ ] => destruct H; crush_sep lems inv
    | [ H : (_ |-- _), a : _ |- _ ] => specialize (H a); destruct H
    | [ b : _, x : _ |- (EX _ : _, _) _ ] => exists (val_of_base b x)
    | [ v : _  |- (EX _ : _, _) _ ] => exists v 
    | [ v : nat |- (EX _ : value, _) _] => exists (int_v v)                                              
    | _ => idtac
  end; crush.



Ltac wf_expr H :=
  let G := fresh "G" in
  let v := fresh "v" in
  let t := fresh "t" in
  let NEQ := fresh "NEQ" in
  let NotIn := fresh "NotIn" in
  inversion H as
      [ G v | G v t NEQ NotIn | G ].

Ltac wf_prop H :=
  let G := fresh "G" in
  let b := fresh "b" in
  let p := fresh "p" in
  let p' := fresh "p'" in
  let e1 := fresh "e1" in
  let o := fresh "o" in
  let e2 := fresh "e2" in
  let WF:= fresh "WF" in
  let WF':= fresh "WF'" in
  inversion H as
      [ G
      | G e1 o e2 WF WF'
      | G p WF
      | G p p' WF WF'
      | G p p' WF WF' ];
    first [ wf_expr WF; wf_expr WF' | idtac].

Ltac wf_ty H :=
  let G := fresh "G" in
  let b := fresh "b" in
  let p := fresh "p" in
  let WF:= fresh "WF" in
      inversion H as [ G b p WF ]; wf_prop WF.
                                                                             
Ltac wellformed H :=
  first [ wf_ty H | wf_prop H | wf_expr H ]; subst.

(* Hint Rewrite subst_not_2. *)
(* Hint Rewrite subst_not_1. *)

Ltac app_pred := 
  match goal with
    | [ H: _ |- appcontext[sep_pred ?p] ] => 
      match type of H with
        | forall _:_, _ => fail 1
        | _ -> _ => fail 1
        | appcontext[sep_pred ?p] => (apply H || (intro; apply H) || (intros; apply H))
      end
  end.
  
Ltac commit t1 t2 t3 :=
  (left; t1; t3) 
  || (right; t2; t3).

Ltac wf_crush :=
  crush;
  (do 2 match goal with 
         | [ H: wf_prop _ ( _ _ _ ) |- _ ] => inversion H; subst
         | [ H: wf_type _ { _ : _ | _ _ _ } |- _ ] => inversion H; subst
         | [ H: wf_prop _ ( _ _ ) |- _ ] => inversion H; subst
         | [ H: wf_type _ {_ : _ | _ _ } |- _ ] => inversion H; subst
       end);
  crush_sep False fail;
  try app_pred.

Ltac btapply k :=
  match goal with
    | [ H : appcontext[?f] |- ?f ] => destruct H; k
    | [ H : forall _:?t, _, x:?t |- _ ] => specialize (H x); btapply k
  end.
