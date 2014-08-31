Add LoadPath "vst".

Require Import Subst.
Require Import Language.
Require Import msl.msl_direct.

Delimit Scope logic_scope with logic.

Definition world := state.

Definition eval_to (e: expr) (v:value) : pred world :=
  fun w => eval w e = v.

Instance Join_world: Join world := Join_equiv world.

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Sep_alg world := _.
Instance Canc_world : Canc_alg world := _.
Instance Disj_world : Disj_alg world := _.

Definition fun_set (f: var -> option value) (x: var) (y: option value) :=
  fun i => if eq_dec i x then y else f i.

Definition subst_pred sub (P: pred world) : (pred world) := 
  fun w =>
    P (fun i => eval w (sub i)).

Definition subst_pred_var sub (P: pred world) : pred world :=
  fun w =>
    P (fun i => eval w (var_e (sub i))).
    
Instance Subst_pred_var : Subst (pred world) var var := subst_pred_var.
Instance Subst_pred : Subst (pred world) var expr := subst_pred.
                 
Definition equal (x y: var) : pred world :=
  fun w => w x = w y.

Inductive modvars : stmt -> var -> Prop :=
| mod_assign: forall x e, modvars (assign_s x e) x
| mod_proc1: forall f xs r os x, 
               In x os ->
               modvars (proc_s f xs r os) x
| mod_proc2: forall f xs r os, 
               modvars (proc_s f xs r os) r
| mod_seq1: forall x s1 s2, modvars s1 x -> modvars (seq_s s1 s2) x
| mod_seq2: forall x s1 s2, modvars s2 x -> modvars (seq_s s1 s2) x.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall stk v, P stk -> subst_pred (subst_one x v) P stk.

Definition subset (S1 S2 : var -> Prop) := forall x, S1 x -> S2 x.

Definition procspec := (pname * proc * pred world * pred world)%type.
  
Definition procspecs := list procspec.

Definition not_free_in (v : var) (v' : var) := v <> v'.

Definition unique_sub s (v : var) :=
  exists v', (s v = v' /\ (forall x, x <> v -> not_free_in v' (s x))).

Inductive semax : procspecs -> pred world -> stmt -> pred world -> Prop :=
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
        semax F ((eval_to e (int_v 0) --> FF) && P) s1 Q -> 
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
        semax F (P * R)%pred s (Q * R)%pred.
      
Notation "F |- {{ P }} s {{ Q }}" := (semax F P%pred s Q%pred) (no associativity, at level 90).

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
      semax F TT s TT ->
      semax_prog F (entry_p s)
| semax_procdecl_p :
    forall F e body ps prog,
      p_body (snd4 ps) = seq_s body (return_s e) ->
      Forall (fun ps' => fst4 ps' <> fst4 ps) F ->
      semax (ps :: F) (thd4 ps) body (subst (subst_one (p_ret (snd4 ps)) e) (fth4 ps)) ->
      semax_prog (ps :: F) prog ->
      semax_prog F (procdecl_p (fst4 ps) (snd4 ps) prog).