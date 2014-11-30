Add LoadPath "vst".

Require Import Subst.
Require Import Language.
Require Export Logic.
(* Require Import msl.msl_direct. *)

(* Delimit Scope logic_scope with logic. *)

Declare Module Semax : SEMAX.
Import Semax.
Export Semax.

Class SubstAssert (D R : Type) `{S : Subst world D R} `{S : Subst assert D R} : Type := mkSubstAssert
{
  subst_wld :
    forall s (P : assert),
      subst s P = (fun w => P (subst s w))
  ;
  subst_andp : 
    forall P Q (s : subst_t D R),
      subst s (andp P Q) = andp (subst s P) (subst s Q)
  ;
  subst_orp : 
    forall  P Q (s : subst_t D R),
      subst s (orp P Q) = orp (subst s P) (subst s Q)
  ;
  subst_sepcon : 
    forall  P Q (s : subst_t D R),
      subst s (sepcon P Q) = sepcon (subst s P) (subst s Q)
  ;
  subst_imp : 
    forall  P Q (s : subst_t D R),
      subst s (imp P Q) = imp (subst s P) (subst s Q)
  ;
  subst_pure :
    forall  (P : assert) (s : subst_t D R),
      pure P -> pure (subst s P)
  ;
  nonfv_andp :
    forall (P Q : assert) (x : D),
      (nonfv P x) /\ (nonfv Q x) -> nonfv (andp P Q) x
  ;
  nonfv_orp :
    forall (P Q : assert) (x : D),
      (nonfv P x) /\ (nonfv Q x) -> nonfv (orp P Q) x
  ;
  nonfv_imp :
    forall (P Q : assert) (x : D),
      (nonfv P x) /\ (nonfv Q x) -> nonfv (imp P Q) x
  ;
  nonfv_sepcon :
    forall (P Q : assert) (x : D),
      (nonfv P x) /\ (nonfv Q x) -> nonfv (sepcon P Q) x
  ;
  nonfv_TT :
    forall (x : D),
      nonfv TT x
  ; nonfv_emp :
    forall (x : D),
      nonfv emp x
}.

Instance SubstAssert_Loc : SubstAssert loc loc := _.
Proof. 
  constructor; intros; try firstorder;
  simpl in *; unfold nonfv_assert in *;  destruct H;
  intros w va;
  specialize (H w va); specialize (H0 w va);
  rewrite H; rewrite H0; reflexivity.
Defined.

Instance SubstAssert_Var_Expr : SubstAssert var expr := _.
Proof. 
  constructor; intros; try firstorder;
  simpl in *; unfold nonfv_assert in *;  destruct H;
  intros w va;
  specialize (H w va); specialize (H0 w va);
  rewrite H; rewrite H0; reflexivity.
Defined.

Instance SubstAssert_Var_Var : SubstAssert var var := _.
Proof. 
  constructor; intros; try firstorder;
  simpl in *; unfold nonfv_assert in *;  destruct H;
  intros w va;
  specialize (H w va); specialize (H0 w va);
  rewrite H; rewrite H0; reflexivity.
Defined.
