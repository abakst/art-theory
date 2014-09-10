Add LoadPath "vst".
Require Export Language.
Require Export Subst.
(* Require Export ProgramLogic. *)
Require Export msl.base.
Require Export msl.log_normalize.
Require Export msl.alg_seplog.
Require Export msl.seplog.

Local Open Scope logic.
Set Implicit Arguments.

(** 
Here we instantiate the separation logic that will be used to reason about
our programming language. Assertions built in this language will be
used to give the axiomatic semantics (proof rules) to the language, and
will serve as the target of our translation from the type judgements.

If we wanted to, we would define a module with signature SEMAX, which
would require us to provide a *model* that satisfies the definitions
and axioms of SEMAX.
**)

Module Type SEMAX.
  Definition adr := nat.

  (** We require that our model satisfy all sorts of algebraic
goodness, with the end result being all of the treats offered by the
MSL: NatDed gives us the usual logical facts and connectives.  SepLog
gives us emp, *, -*, etc.  ClassicalSep tell us P * emp = P etc..  **)

  Parameter mpred :Type.
  Parameter Nm: NatDed mpred.  Existing Instance Nm.
  Parameter Sm: SepLog mpred.  Existing Instance Sm.
  Parameter Cm: ClassicalSep mpred.  Existing Instance Cm.
  Parameter Im: Indir mpred.  Existing Instance Im.
  Parameter Rm: RecIndir mpred.  Existing Instance Rm.
  Parameter SIm: SepIndir mpred.  Existing Instance SIm.
  Parameter SRm: SepRec mpred.  Existing Instance SRm.
  Parameter mapsto: forall (v1 v2: adr), mpred.
  
  Definition assert := world -> mpred.

  Definition pure{A : Type} {N : NatDed A } {S : SepLog A} (P : A) := P |-- emp.
  Axiom sepcon_pure_andp : forall {A : Type} {N : NatDed A} {S : SepLog A} (P Q : A), pure P -> pure Q -> ((P * Q) = (P && Q)).
 
  Definition eval_to (e: expr) (v:value) : assert :=
    fun (w : world) => !!(eval w e = v) && emp.

  Definition subst_pred sub (P: assert) : (assert) := 
    fun w =>
      P (fun i => eval w (sub i), hp w).
  
  Definition subst_pred_var sub (P: assert) : assert :=
    fun w =>
      P (fun i => eval w (var_e (sub i)), hp w).
    
  Instance Subst_pred_var : Subst (assert) var var := subst_pred_var.
  Instance Subst_pred : Subst (assert) var expr := subst_pred.
                 
  Definition equal (x y: var) : assert :=
    fun w => !!(stk w x = stk w y).

  Axiom mapsto_conflict:  forall a b c, mapsto a b * mapsto a c |-- FF.
  Parameter allocpool: forall (b: adr), mpred.
  Axiom alloc: forall b, allocpool b = ((!! (b > 0) && mapsto b 0) * allocpool (S b)).

  Definition subset (S1 S2 : var -> Prop) := forall x, S1 x -> S2 x.
  Definition not_free_in (v : var) (v' : var) := v <> v'.
  Definition unique_sub s (v : var) :=
    exists v', (s v = v' /\ (forall x, x <> v -> not_free_in v' (s x))).
  (* Definition nonfreevars (P: assert) (x: var) : Prop := *)
  (*     P |-- (ALL v : _, subst_pred (subst_one x v) P). *)
  Definition nonfreevars (P: assert) (x: var) : Prop :=
    forall v, (P |-- subst_pred (subst_one x v) P).
  
  Definition procspec := (pname * proc * assert * assert)%type.
  Definition procspecs := list procspec.
  
  Inductive semax : procspecs -> assert -> stmt -> assert -> Prop :=
  | semax_skip : 
      forall F P, semax F P skip_s P
  | semax_assign :
      forall F P x e,
        semax F (EX v : value, 
                      eval_to e v 
                   && subst_pred (subst_one x e) P) (assign_s x e)  P 
  | semax_proc :
      forall f p (F : procspecs) P Q,
        In (f, p, P, Q) F ->
        semax F P (proc_s f (p_args p) (p_ret p) (p_mod p)) Q
  | semax_seq : 
      forall F P Q R s1 s2,
        semax F P s1 Q -> semax F Q s2 R -> 
        semax F P (seq_s s1 s2) R
  | semax_if :
      forall F P Q e s1 s2,
        semax F (eval_to e (int_v 1) && P) s1 Q -> 
        semax F (eval_to e (int_v 0) && P) s2 Q ->
        semax F P (if_s e s1 s2) Q
  | semax_subst :
      forall F P s Q θ,
        semax F P s Q -> (forall x, (modvars s x -> unique_sub θ x)) ->
        semax F (subst θ P) (subst θ s) (subst θ Q)
  | semax_pre_post :
      forall F P P' s Q Q',
        (P |-- P') -> (Q' |-- Q) -> semax F P' s Q' ->
        semax F P s Q
  | semax_frame :
      forall F P Q R s,
        semax F P s Q -> subset (modvars s) (nonfreevars R) ->
        semax F (P * R)%logic s (Q * R)%logic.
      
  Notation "F |- {{ P }} s {{ Q }}" := (semax F P s Q) (no associativity, at level 90).
  
  Definition fst4{A B C D : Type} (t : (A * B * C * D)) :=
    match t with
      | (a,_,_,_) => a
    end.

  Definition snd4{A B C D : Type} (t : (A * B * C * D)) :=
    match t with
      | (_,a,_,_) => a
    end.

  Definition thd4{A B C D : Type} (t : (A * B * C * D)) :=
    match t with
      | (_,_,a,_) => a
    end.

  Definition fth4{A B C D : Type} (t : (A * B * C * D)) :=
    match t with
      | (_,_,_,a) => a
    end.

  Inductive semax_prog : procspecs -> program -> Prop :=
  | semax_entry_p :
      forall F s,
        semax F emp s TT ->
        semax_prog F (entry_p s)
  | semax_procdecl_p :
      forall F e body ps prog,
        p_body (snd4 ps) = seq_s body (return_s e) ->
        Forall (fun ps' => fst4 ps' <> fst4 ps) F ->
        semax (ps :: F) (thd4 ps) body (subst (subst_one (p_ret (snd4 ps)) e) (fth4 ps)) ->
        semax_prog (ps :: F) prog ->
        semax_prog F (procdecl_p (fst4 ps) (snd4 ps) prog).
End SEMAX.