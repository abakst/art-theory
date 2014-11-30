(**  Module defining the programming languages:
     - Values
     - Expressions
     - Statements **)
Add LoadPath "vst".
Require Import CpdtTactics.
Require Import Arith.
Require Import List.
Require Import Subst.
Require Import msl.eq_dec.
Import Relations. 
Import ListNotations.

Delimit Scope lang_scope with lang.

Inductive loc   : Set := L : nat -> loc.
Inductive var   : Set := V : nat -> var.
Inductive addr  : Set := A : nat -> addr.
Inductive pname : Set := P : nat -> pname.

Definition subst_loc (s:subst_t loc loc) (l:loc) := 
  match s l with 
    | Some l' => l'
    | _       => l
  end.

Instance Subst_loc_loc : Subst loc loc loc := 
  mkSubst _ _ _ Logic.eq (fun l x => ~ l = x) subst_loc.
Instance Subst_loc_vars : Subst loc var var := 
  mkSubst _ _ _ Logic.eq (fun _ _ => True) (fun _ x => x).

Instance FVSubst_loc_loc : SubstFV loc loc loc _ := _.
Proof. 
  firstorder. 
  unfold subst; simpl; unfold subst_loc; simpl.
  specialize (H e). 
  destruct (s e).
  destruct H. discriminate. reflexivity. reflexivity.
Defined.
Instance FVSubst_loc_vars : SubstFV loc var var Subst_loc_vars := _.
Proof. firstorder. Defined.

Instance Eq_eqLoc_loc : Equivalence (@eq loc loc loc Subst_loc_loc) := _.
Instance Eq_eqLoc_var : Equivalence (@eq loc var var Subst_loc_vars) := _.

Instance EqDec_loc : EqDec loc := _. 
Proof. hnf; decide equality; apply eq_dec. Defined.

Definition subst_loc_one (l : loc) (l' : loc) : subst_t loc loc  :=
  fun i => if eq_dec i l then (Some l') else None.

Definition null   := A 0.

Inductive value : Set :=
  | int_v  : nat -> value
  | addr_v : addr -> value.

Definition null_v := addr_v null.

Inductive expr :=
  | value_e  : value -> expr
  | var_e    : var -> expr
  | locvar_e : loc -> expr
  | fun_e    : pname -> expr -> expr -> expr. 

Fixpoint fv_expr e :=
  match e with
    | var_e v => [v]
    | fun_e f e1 e2 => fv_expr e1 ++ fv_expr e2
    | _ => []
  end.

Fixpoint fl_expr e :=
  match e with
    | locvar_e l => [l]
    | fun_e e e1 e2 => fl_expr e1 ++ fl_expr e2
    | _ => []
  end.

Definition NFV e x := ~ In x (fv_expr e).
Definition NFL e l := ~ In l (fl_expr e).
  
(* 
Procedure p(x0 ... xn)
- return value is stored in one of p_mod 
*)
Record proc' {s} :=
    { p_args: list var;
      p_ret: var;
      p_mod: list var;
      p_modl: list loc;
      p_body: s }.

Inductive stmt :=
| skip_s   : stmt
| pad_s    : loc -> var -> stmt
| alloc_s  : loc -> var -> expr -> stmt
| assign_s : var -> expr -> stmt
| proc_s   : pname -> list var -> var -> list var -> list loc -> stmt (* p(x0...xn), modifies y0...yn *)
| seq_s    : stmt -> stmt -> stmt
| if_s     : expr -> stmt -> stmt -> stmt
| return_s : expr -> stmt.

Definition proc := @proc' stmt.

Inductive program := 
| entry_p    : stmt -> program
| procdecl_p : pname -> proc -> program -> program.

Definition mkProc := Build_proc' stmt.

(* Coercion int_v: nat >-> value. *)
Coercion value_e: value >-> expr.
(* Coercion var_e: var >-> expr. *)

(*** Equality ***)
Instance EqDec_var : EqDec var := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_addr : EqDec addr := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_pname : EqDec pname := _.
Proof.
  hnf. decide equality; try apply eq_dec.
Qed.

Instance EqDec_value : EqDec value := _.
Proof.
  hnf. decide equality; apply eq_dec.
Qed.


Instance EqDec_expr : EqDec expr := _.
Proof.
  hnf. decide equality; apply eq_dec.
Qed.

Instance EqDec_stmt : EqDec stmt := _.
Proof.
  hnf.
  decide equality;
  apply eq_dec.
Qed.

(*** Substitutions ***)
Definition subst_var (s:subst_t var var) (v:var) := 
  match s v with
    | Some v' => v'
    | _       => v
  end.

Instance Subst_var_var : Subst var var var := 
  mkSubst _ _ _ Logic.eq (fun v x => v <> x) subst_var.
Instance FVSubst_var_var : SubstFV var var var _.
Proof. 
  constructor.
  intros. unfold subst; simpl; unfold subst_var; simpl. 
  specialize (H e).
  destruct (s e). 
  destruct H. discriminate. reflexivity. reflexivity.
Defined.
Instance Eq_Var_var : Equivalence (@eq var var var Subst_var_var) := _.

Definition subst_var_one (v : var) (v' : var) : subst_t var var  :=
  fun i => if eq_dec i v then Some v' else None.

Fixpoint subst_expr_var (s:subst_t var var) (e:expr) := 
  match e with 
    | var_e v => var_e (subst s v)
    | fun_e p e1 e2 => fun_e p (subst_expr_var s e1) (subst_expr_var s e2)
    | _ => e
  end.

Hint Unfold subst_expr_var NFV fv_expr NFL fl_expr In : subst.

Lemma nonfv_fun :
  forall f x e1 e2,
    NFV (fun_e f e1 e2) x -> NFV e1 x /\ NFV e2 x.
Proof.
  intros.
  unfold NFV in *.
  simpl in H.
  constructor; intro; apply H; apply in_or_app.
  left. assumption. right. assumption.
Qed.

Lemma nonfl_fun :
  forall f x e1 e2,
    NFL (fun_e f e1 e2) x -> NFL e1 x /\ NFL e2 x.
Proof.
  intros.
  unfold NFV in *.
  simpl in H.
  constructor; intro; apply H; apply in_or_app.
  left. assumption. right. assumption.
Qed.

Instance Subst_var_var_expr : Subst expr var var := 
  mkSubst _ _ _ Logic.eq NFV subst_expr_var.
Instance FVSubst_var_var_expr : SubstFV expr var var _ := _.
Proof.
  constructor.
  intros.
  unfold subst. simpl.
  induction e; try reflexivity.
  + repeat autounfold with subst in *.
    rewrite subst_nonfv. reflexivity.
    repeat intro. specialize (H x). apply H. assumption. rewrite H1.
    simpl. left. reflexivity.
  + simpl in *. 
    pose (nonfv_fun).
    rewrite IHe1. rewrite IHe2. reflexivity.
    repeat intro. apply (a p x e1 e2). apply (H x). assumption. assumption.
    repeat intro. specialize (a p x e1 e2).
    destruct a. intro. apply (H x). assumption. assumption.
    apply H2. assumption.
Defined.
Instance Eq_Var_expr : Equivalence (@eq expr var var Subst_var_var_expr) := _.

Fixpoint subst_expr (s:subst_t var expr) (e:expr) := 
  match e with 
    | var_e v => match s v with | Some e' => e' | _ => var_e v end
    | fun_e p e1 e2 => fun_e p (subst_expr s e1) (subst_expr s e2)
    | _ => e
  end.

Instance Subst_var_expr : Subst expr var expr := 
  mkSubst _ _ _ Logic.eq NFV subst_expr.
Instance FVSubst_var_expr : SubstFV expr var expr  _:= _.
Proof.
  constructor.
  intros.
  induction e; try reflexivity.
  + specialize (H v). unfold NFV, fv_expr, In in H. intuition. unfold subst; simpl; unfold subst_expr; simpl.
    destruct (s v).
    destruct H. intro. inversion H. left. reflexivity. reflexivity.
  + simpl in *. 
    rewrite IHe1. rewrite IHe2. reflexivity.
    repeat intro. apply (nonfv_fun p x e1 e2). apply (H x). assumption. assumption.
    repeat intro. destruct (nonfv_fun p x e1 e2).
    intro. apply (H x). assumption. assumption.
    apply H2. assumption.
Defined.
Instance Eq_expr_var_expr : Equivalence (@eq expr var expr Subst_var_expr) := _.

Instance Subst_loc_expr : Subst loc var expr := 
  mkSubst _ _ _ Logic.eq (fun _ _ => True) (fun _ x => x).
Instance FVSubst_loc_expr : SubstFV loc var expr _ := _.
Proof. firstorder. Defined.
Instance Eq_loc_expr : Equivalence (@eq loc var expr Subst_loc_expr) := _.

Definition subst_var_loc (s : subst_t loc loc) (x : var) : var := x.
Fixpoint subst_expr_loc (s : subst_t loc loc) (x : expr) : expr := 
  match x with
    | locvar_e l => locvar_e (subst s l)
    | fun_e p e1 e2 => fun_e p (subst_expr_loc s e1) (subst_expr_loc s e2)
    | _ => x
  end.
Instance Subst_loc_var : Subst var loc loc := 
  mkSubst _ _ _ Logic.eq (fun _ _ => True) subst_var_loc.
Instance FVSubst_loc_var : SubstFV var loc loc _ := _.
Proof. firstorder. Defined.
Instance Eq_var_loc_var : Equivalence (@eq var loc loc Subst_loc_var) := _.

Instance Subst_expr_loc : Subst expr loc loc := 
  mkSubst _ _ _ Logic.eq NFL subst_expr_loc.
Instance FVSubst_expr_loc : SubstFV expr loc loc _ := _.
Proof.
  constructor.
  intros.
  induction e; try reflexivity.
  + specialize (H l); unfold NFL, fl_expr, In in *; intuition. 
    simpl. unfold subst_loc. destruct (s l). 
    destruct H. intro. inversion H. left. reflexivity. reflexivity.
  + simpl in *.
    rewrite IHe1. rewrite IHe2. reflexivity.
    repeat intro. apply (nonfl_fun p x e1 e2). apply (H x). assumption. assumption.
    repeat intro. destruct (nonfl_fun p x e1 e2).
    intro. apply (H x). assumption. assumption.
    apply H2. assumption.
Defined.
Instance Eq_expr_loc_loc : Equivalence (@eq expr loc loc Subst_expr_loc) := _.

Definition state := var -> option value.
Definition locmap := loc -> option addr.
Definition heap  := addr -> option value.
Definition world := ((state * locmap) * heap)%type.
Definition stk (w : world) : state := fst (fst w).
Definition hp (w : world) : heap := snd w.
Definition runloc (w : world) := snd (fst w). 

Parameter eval_fun : pname -> expr -> expr -> value.

Fixpoint eval s e :=
  match e with
    | value_e v => Some v
    | var_e v   => stk s v
    | locvar_e l =>  match runloc s l with 
                       |Some a => Some (addr_v a)
                       | _     => None
                     end
    | fun_e f e1 e2 => 
      match (eval s e1, eval s e2) with
        | (Some v1, Some v2) => Some (eval_fun f v1 v2)
        | _ => None
      end
  end.

Instance Subst_world_var : Subst world var var :=
  mkSubst _ _ _ Logic.eq (fun w i => stk w i = None) 
          (fun s w => (fun i => 
                         match (s i) with
                           | Some i' => stk w i'
                           | None => stk w i
                         end, runloc w, hp w)).

Instance Subst_world_expr : Subst world var expr :=
  mkSubst _ _ _ Logic.eq (fun w i => stk w i = None) 
          (fun s w => (fun i => 
                         match (s i) with
                           | Some e => eval w e
                            | None => stk w i
                         end, runloc w, hp w)).

Instance Subst_world_loc : Subst world loc loc := 
  mkSubst _ _ _ Logic.eq (fun w i => runloc w i = None)
          (fun s w => (stk w,
                       fun l => 
                         match (s l) with 
                           | Some l' => runloc w l'
                           | None => runloc w l
                         end, hp w)).

(* Class SubstWorld (D R : Type) (S: Subst var D R) `(SW : Subst world D R) := { *)
(*   subst_world_var : *)
(*     forall (s : subst_t D R) v w, *)
(*       stk (subst s w) v = stk w (subst s v) *)
(* }. *)

(* Instance SubstWorld_var : SubstWorld var var _ _. *)
(* Proof.  *)
(*   constructor. *)
(*   intros. unfold subst. simpl. destruct w. destruct p. *)
(*   unfold stk. simpl. unfold subst_var. destruct (s v); reflexivity. *)
(* Qed. *)

(* Instance SubstWorld_loc : SubstWorld loc loc _ _. *)
(* Proof. constructor; firstorder. Qed. *)

Class SubstExpr (D R : Type) {E : EqDec D} {Sl : Subst loc D R} 
      `{S : SubstFV expr D R} {SW : Subst world D R} : Type := {
    subst_fun : 
      forall (s : subst_t D R) p e1 e2,
        subst s (fun_e p e1 e2) = fun_e p (subst s e1) (subst s e2)
   ;
   subst_value : 
      forall (s : subst_t D R) v,
        subst s (value_e v) = value_e v
   ;
   subst_locvar :
     forall (s : subst_t D R) l,
       locvar_e (subst s l) = subst s (locvar_e l)
   ;
   nonfv_eval :
     forall e (x : D) v w,
       nonfv e x -> eval w e = eval (subst (subst_one x v) w) e
   ;
   nonfv_subst :
     forall (e e' : expr) (x : D) v,
       nonfv e x -> nonfv e' x -> nonfv (subst (subst_one v e') e) x
}.

Instance SubstExpr_var_var : SubstExpr var var. 
Proof. 
  firstorder. {
  unfold nonfv in H. simpl in H. unfold NFV in H.
  destruct w as [[s ?] ?].
  induction e; simpl in *; unfold stk; simpl.
  + reflexivity.
  + unfold subst_one. destruct (eq_dec x v0). subst. destruct H. left. reflexivity. reflexivity.
  + reflexivity.
  + rewrite IHe1. rewrite IHe2. reflexivity. 
    intro. apply H. apply in_or_app. right. assumption.
    intro. apply H. apply in_or_app. left. assumption.
}{ 
  induction e; intros; simpl in *; unfold stk; simpl. easy.
  unfold subst_one. destruct (eq_dec v v0). easy. 
  unfold NFV in *. intro. apply H. easy. easy.
  unfold NFV in *.
  simpl.
  intro.
  apply in_app_or in H1.
  simpl in H. 
  apply H. apply in_or_app. intuition.
}
Defined.

Instance SubstExpr_var_expr : SubstExpr var expr. 
Proof. 
  firstorder. {
  unfold nonfv in H. simpl in H. unfold NFV in H.
  destruct w as [[s ?] ?].
  induction e; simpl in *; unfold stk; simpl.
  + reflexivity.
  + unfold subst_one. destruct (eq_dec x v0). subst. destruct H. left. reflexivity. reflexivity.
  + reflexivity.
  + rewrite IHe1. rewrite IHe2. reflexivity. 
    intro. apply H. apply in_or_app. right. assumption.
    intro. apply H. apply in_or_app. left. assumption.
    }{
    
  induction e. intros; simpl in *; unfold stk; simpl. easy.
  unfold subst_one. simpl. destruct (eq_dec v v0). easy. 
  unfold NFV in *. intro. apply H. easy. easy.
  simpl in *.
  intro.
  simpl in H1. apply in_app_or in H1. apply H. simpl. 
  unfold NFV in H. simpl in H.
  unfold NFV in *. simpl in *. intuition.
}
Defined.

Instance SubstExpr_loc_loc : SubstExpr loc loc.
Proof. 
  firstorder. 
  {
  unfold nonfv in H. simpl in H. unfold NFL in H.
  destruct w as [[s ?] ?].
  induction e; simpl in *; unfold stk, runloc; simpl.
  + reflexivity.
  + reflexivity. 
  + unfold subst_one. destruct (eq_dec x l0). subst. destruct H. left. reflexivity. reflexivity.
  + rewrite IHe1. rewrite IHe2. reflexivity. 
    intro. apply H. apply in_or_app. right. assumption.
    intro. apply H. apply in_or_app. left. assumption.
  }
  {
    induction e; try easy. 
    unfold subst_one. simpl. destruct (eq_dec v v0). assumption.
    unfold NFL. intro. intuition.
    unfold nonfv in *. simpl in *.
    unfold NFL in H. simpl in H. intro. simpl in *. intuition.
    apply H. apply in_or_app. apply in_app_or in H1. unfold NFL in *. intuition.
  }
Defined.

Fixpoint subst_stmt {D R : Type} 
         {S1 : Subst var D R}
         {S2 : Subst loc D R} 
         {S3 : Subst expr D R}
         {E1 : Equivalence (eq (A := var))}
         {E1 : Equivalence (eq (A := loc))}
         {E1 : Equivalence (eq (A := expr))}
         (s:subst_t D R) (st:stmt) :=
  match st with
    | pad_s l x => pad_s (subst s l) (subst s x)
    | alloc_s l v e => alloc_s (subst s l) (subst s v) (subst s e)
    | assign_s x e => assign_s (subst s x) (subst s e)
    | proc_s p xs r os ls => proc_s p (subst s xs) (subst s r) (subst s os) (subst s ls)
    | return_s e => return_s (subst s e)
    | seq_s s1 s2 => seq_s (subst_stmt s s1) (subst_stmt s s2)
    | if_s e s1 s2 => if_s (subst s e) (subst_stmt s s1) (subst_stmt s s2)
    | _ => st
  end.

Fixpoint nonfv_stmt 
         {D R : Type} 
         {S1 : Subst var D R}
         {S2 : Subst loc D R} 
         {S3 : Subst expr D R}
         {E1 : Equivalence (@eq _ _ _ S1)}
         {E2 : Equivalence (@eq _ _ _ S2)}
         {E3 : Equivalence (@eq _ _ _ S3)}
         s (x : D) :=
  match s with
    | skip_s => False
    | pad_s l v => nonfv l x /\ nonfv v x
    | alloc_s l v e => nonfv l x /\ nonfv v x /\ nonfv e x
    | assign_s v e => nonfv v x /\ nonfv e x
    | proc_s p vs v vs' ls => nonfv v x /\ nonfv vs x /\ nonfv vs' x /\ nonfv ls x
    | seq_s s1 s2 => nonfv_stmt s1 x /\ nonfv_stmt s2 x
    | if_s e s1 s2 => nonfv e x /\ nonfv_stmt s1 x /\ nonfv_stmt s2 x
    | return_s e => nonfv e x
  end.

Fixpoint eq_stmt 
         {D R : Type} 
         {S1 : Subst var D R}
         {S2 : Subst loc D R} 
         {S3 : Subst expr D R}
         {E1 : Equivalence (@eq _ _ _ S1)}
         {E2 : Equivalence (@eq _ _ _ S2)}
         {E3 : Equivalence (@eq _ _ _ S3)}
         s1 s2 :=
  match (s1, s2) with
    | (skip_s, skip_s) => True
    | (pad_s l1 x1, pad_s l2 x2) => eq l1 l2 /\ eq x1 x2
    | (alloc_s l1 x1 e1, alloc_s l2 x2 e2) => eq l1 l2 /\ eq x1 x2 /\ eq e1 e2
    | (assign_s x1 e1, assign_s x2 e2) => eq x1 x2 /\ eq e1 e2
    | (proc_s p1 vs1 v1 vs'1 ls1,
       proc_s p2 vs2 v2 vs'2 ls2) => p1 = p2 /\ eq vs1 vs2 /\ eq v1 v2 /\ eq vs'1 vs'2 /\ eq ls1 ls2
    | (seq_s s1 t1, seq_s s2 t2) => eq_stmt s1 s2 /\ eq_stmt t1 t2
    | (if_s e1 s1 t1, if_s e2 s2 t2) => eq e1 e2 /\ eq_stmt s1 s2 /\ eq_stmt t1 t2
    | (return_s e1, return_s e2) => eq e1 e2
    | _ => False
  end.

Instance Equiv_eqStmt 
         {D R : Type} 
         {S1 : Subst var D R}
         {S2 : Subst loc D R} 
         {S3 : Subst expr D R}
         {E1 : Equivalence (@eq _ _ _ S1)}
         {E2 : Equivalence (@eq _ _ _ S2)}
         {E3 : Equivalence (@eq _ _ _ S3)}
: Equivalence (@eq_stmt D R _ _ _ _ _ _).
Proof.
  constructor.
  hnf. intros. induction x; try first [ reflexivity
                                      | repeat constructor; reflexivity
                                      ].
  constructor; assumption.
  repeat constructor; try reflexivity; try assumption.
  simpl; reflexivity.

  hnf. intro x. induction x; intros; (destruct y; try inversion H).
  reflexivity.
  simpl. rewrite H0. rewrite H1. constructor; reflexivity.
  simpl. rewrite H0. destruct H1. rewrite H1. rewrite H2. repeat constructor; reflexivity.
  simpl. simpl in H.
  repeat constructor; first [ rewrite H0; reflexivity | rewrite H1; reflexivity].
  repeat constructor; simpl in *; symmetry; apply H.
  constructor. apply IHx1. assumption. apply IHx2. assumption.
  constructor. symmetry. assumption. constructor. apply IHx1. apply H1. apply IHx2. apply H1.
  simpl in *. symmetry; assumption.

  hnf.
  intros x.
  induction x; intros; destruct y; destruct z; try match goal with | H : eq_stmt _ _ |- _ => solve [inversion H] end;
  try reflexivity; simpl in *; repeat match goal with 
                                        | H : _ /\ _ |- _ => destruct H
                                      end.
  (constructor; eapply transitivity; eauto).
  (repeat constructor; eapply transitivity; eauto).
  (constructor; eapply transitivity; eauto).
  (repeat constructor); try solve [ eapply transitivity; eauto ].
  constructor. eapply IHx1; eauto. eapply IHx2; eauto.
  repeat constructor. eapply transitivity; eauto. eapply IHx1; eauto. eapply IHx2; eauto.
  eapply transitivity; eauto.
Qed.

Ltac solve_fv := 
  (match goal with
    | |- appcontext[@nonfv _] => unfold nonfv; simpl
  end;
  unfold nonfv_stmt;
  try reflexivity;
  try assumption;
  intuition;
  match goal with
    | x : ?T, H : (forall _: ?T, _) |- _ => destruct (H x); solve_fv
    | |- _ \/ _ => first [left; solve_fv | right; solve_fv]
  end).
       
Ltac solve_instance := 
  first [reflexivity 
        | repeat constructor;
          (repeat apply subst_nonfv); 
          match goal with
            | |- appcontext[@nonfv _] => solve_fv
            | _ => firstorder
          end].

Instance Subst_stmt :
 Subst stmt var var := mkSubst stmt var var (@eq_stmt var var Subst_var_var _ _ _ _ _) nonfv_stmt subst_stmt.
Instance FVSubst_stmt : SubstFV stmt var var Subst_stmt.
Proof.
 constructor. intros. induction e;
   match goal with 
     | |- appcontext [@subst stmt] => 
       unfold subst, Subst_stmt, subst_stmt 
   end; solve_instance.
Defined. 

Definition eq_stmt_v := (eq_stmt (D := var) (R := var)).
Definition eq_stmt_l := (eq_stmt (D := loc) (R := loc)).

Instance Subst_stmt_var_proper : 
  Proper (Logic.eq ==> eq_stmt_v ==> eq_stmt_v) subst.
Proof.
  pose (Subst_list_proper (A := var) (D := var) (R := var)).
  pose (Subst_list_proper (A := loc) (D := var) (R := var)).
  hnf; intros. rewrite H. 
  hnf; intro. subst y.
  induction x0; intros y eqh; destruct y;
  try solve [inversion eqh]; try reflexivity;
  match goal with | H : eq_stmt_v _ _ |- _ => inversion_clear H end;
  repeat match goal with 
           | H : eq _ _ |- _ => inversion_clear H 
           | H : eq _ _ /\ _ |- _ => decompose [and] H; clear H; subst
         end; try reflexivity.
  simpl. 
  unfold eq_stmt_v. unfold eq_stmt. rewrite H1. rewrite H2. rewrite H5. repeat constructor; reflexivity.
  unfold eq_stmt_v. hnf. 
  apply IHx0_1 in H. apply IHx0_2 in H0. constructor; assumption.
  destruct H0.
  hnf.
  apply IHx0_1 in H. apply IHx0_2 in H0. unfold eq_stmt_v in *.
  repeat constructor; (reflexivity || assumption).
Qed.

Instance Subst_stmt_loc : Subst stmt loc loc := 
  mkSubst _ _ _ (@eq_stmt loc loc _ _ _ _ _ _) nonfv_stmt subst_stmt.
Instance FVSubst_stmt_loc : SubstFV stmt loc loc _ := _.
Proof.
 constructor. intros. induction e;
   try match goal with 
     | |- appcontext [@subst stmt loc loc] => 
       unfold subst, Subst_stmt_loc, subst_stmt
   end; solve_instance.
Defined.

Instance Subst_stmt_loc_proper :
  Proper (Logic.eq ==> eq_stmt_l ==> eq_stmt_l) subst.
Proof.
  pose (Subst_list_proper (A := var) (D := loc) (R := loc)).
  pose (Subst_list_proper (A := var) (D := loc) (R := loc)).
  pose (Subst_list_proper (A := loc) (D := loc) (R := loc)).
  hnf; intros. rewrite H. 
  hnf; intro. subst y.
  induction x0; intros y eqh; destruct y;
  try solve [inversion eqh]; try reflexivity;
  match goal with | H : eq_stmt_l _ _ |- _ => inversion_clear H end;
  repeat match goal with 
           | H : eq _ _ |- _ => inversion_clear H 
           | H : eq _ _ /\ _ |- _ => decompose [and] H; clear H; subst
         end; try reflexivity.
  hnf. 
  rewrite H1. rewrite H2. rewrite H5. repeat constructor; reflexivity.
  unfold eq_stmt_l. hnf. 
  apply IHx0_1 in H. apply IHx0_2 in H0. constructor; assumption.
  destruct H0.
  hnf.
  apply IHx0_1 in H. apply IHx0_2 in H0. unfold eq_stmt_l in *.
  repeat constructor; (reflexivity || assumption).
Qed.
(* Definition subst_one (x : var) (e : expr) := *)
(*   fun i => if eq_dec i x then e else (var_e i). *)

Inductive modvars : stmt -> var -> Prop :=
| mod_alloc : forall l v e, modvars (alloc_s l v e) v
| mod_assign: forall x e, modvars (assign_s x e) x
| mod_proc1: forall f xs r os ls x, 
               In x os ->
               modvars (proc_s f xs r os ls) x
| mod_proc2: forall f xs r os ls, 
               modvars (proc_s f xs r os ls) r
| mod_seq1: forall x s1 s2, modvars s1 x -> modvars (seq_s s1 s2) x
| mod_seq2: forall x s1 s2, modvars s2 x -> modvars (seq_s s1 s2) x.

Inductive modlocs : stmt -> loc -> Prop :=
| modl_alloc : forall l v e, modlocs (alloc_s l v e) l
| modl_proc : forall f xs r os ls l,
                In l ls -> modlocs (proc_s f xs r os ls) l.

(** Dummy instance! **)
Instance Subst_var_expr_dummy : Subst var var expr :=
  mkSubst _ _ _ Logic.eq (fun v x => v <> x) (fun s v => v).
