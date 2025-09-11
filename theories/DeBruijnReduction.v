From Stdlib Require Import Bool Nat List.
From Stdlib.Classes Require Import Morphisms.
Import ListNotations.

(**************************************************************************)
(** *** lambda terms. *)
(**************************************************************************)

(** Untyped lambda terms, using de Bruijn indices. *)
Inductive term :=
| var : nat -> term
| app : term -> term -> term
| lam : term -> term.

(**************************************************************************)
(** *** Substitution. *)
(**************************************************************************)

(** [lift depth ofs t] adds [ofs] to all de Bruijn indices in [t]
    which are greater or equal to [depth]. *)
Fixpoint lift (depth : nat) (ofs : nat) (t : term) : term :=
  match t with
  | var i => if i <? depth then var i else var (i + ofs)
  | app t1 t2 => app (lift depth ofs t1) (lift depth ofs t2)
  | lam t => lam (lift (depth + 1) ofs t)
  end.

Definition lift0 := lift 0.

(** [subst n u t] substitutes de Bruijn index [n] with [u] in [t]. *)
Fixpoint subst (n : nat) (u : term) (t : term) : term :=
  match t with
  | var i =>
    if i <? n then var i
    else if i =? n then lift 0 n u
    else var (i - 1)
  | app t1 t2 => app (subst n u t1) (subst n u t2)
  | lam t => lam (subst (n + 1) u t)
  end.

Definition subst0 := subst 0.

(**************************************************************************)
(** *** Reduction relation. *)
(**************************************************************************)

Reserved Notation "t '~~>₁' u" (at level 60, no associativity).
Reserved Notation "t '~~>' u" (at level 60, no associativity).

Inductive red1 : term -> term -> Prop :=
| red1_beta t u :
    app (lam t) u ~~>₁ subst0 u t
| red1_app_l t t' u :
    t ~~>₁ t' -> app t u ~~>₁ app t' u
| red1_app_r t u u' :
    u ~~>₁ u' -> app t u ~~>₁ app t u'
| red1_lam t t' :
    t ~~>₁ t' -> lam t ~~>₁ lam t'
where "t '~~>₁' u" := (red1 t u).

Inductive red : term -> term -> Prop :=
| red_refl t : t ~~> t
| red_step t1 t2 t3 : t1 ~~> t2 -> t2 ~~>₁ t3 -> t1 ~~> t3
where "t '~~>' u" := (red t u).

Lemma red_red1 t t' : t ~~>₁ t' -> t ~~> t'.
Proof. intros H. eapply red_step ; [apply red_refl | exact H]. Qed.

#[local] Instance red_Equivalence : PreOrder red.
Proof.
constructor.
- intros t. apply red_refl.
- intros t1 t2 t3 H1 H2. induction H2.
  + assumption.
  + apply red_step with (t2 := t2) ; auto.
Qed.

#[local] Instance red_app : Proper (red ==> red ==> red) app.
Proof.
intros t t' Ht u u' Hu. transitivity (app t u').
- induction Hu.
  + reflexivity.
  + transitivity (app t t2) ; [assumption|]. apply red_red1. now apply red1_app_r.
- induction Ht.
  + reflexivity.
  + transitivity (app t2 u') ; [assumption|]. apply red_red1. now apply red1_app_l.
Qed.

#[local] Instance red_lam : Proper (red ==> red) lam.
Proof.
intros t t' Ht. induction Ht.
- reflexivity.
- transitivity (lam t2) ; [assumption|]. apply red_red1. now apply red1_lam.
Qed.

Lemma red_beta t u : app (lam t) u ~~> subst0 u t.
Proof. apply red_red1. constructor. Qed.

(**************************************************************************)
(** *** Monadic programs. *)
(**************************************************************************)

(** A simple error monad. *)
Inductive M (A : Type) : Type :=
| Success (x : A) : M A
| OutOfFuel : M A.
Arguments Success {A} x.
Arguments OutOfFuel {A}.

Definition ret {A} (x : A) : M A :=
  Success x.

Definition bind {A B} (mx : M A) (f : A -> M B) : M B :=
  match mx with
  | Success x => f x
  | OutOfFuel => OutOfFuel
  end.

(** [let*] monadic notation. *)
Notation "'let*' x ':=' t 'in' u" := (bind t (fun x => u))
  (at level 100, right associativity, t at next level, x pattern).

(** Primitive to fail. *)
Definition fail {A} : M A := OutOfFuel.

(** Weakest-precondition. *)
Definition wp {A} (m : M A) (Q : A -> Prop) :=
  match m with
  | OutOfFuel => True
  | Success a => Q a
  end.

Lemma wp_fail {A} Q : wp (@fail A) Q.
Proof. cbn. constructor. Qed.

Lemma wp_ret {A} (a : A) Q : Q a -> wp (ret a) Q.
Proof. intros H. cbn. assumption. Qed.

Lemma wp_bind {A B} (m : M A) (f : A -> M B) Q :
  wp m (fun a => wp (f a) Q) -> wp (let* x := m in f x) Q.
Proof.
intros H. destruct m ; cbn in * ; assumption.
Qed.

Lemma wp_consequence {A} (m : M A) Q Q' :
  (forall a, Q a -> Q' a) -> wp m Q -> wp m Q'.
Proof.
intros H1 H2. destruct m ; cbn in *.
- apply H1. assumption.
- constructor.
Qed.

Ltac wp_step :=
  match goal with
  | [ |- wp (ret _) _ ] => apply wp_ret
  | [ |- wp (bind _ _) _ ] => apply wp_bind
  | [ |- wp fail _ ] => apply wp_fail
  end.

Ltac wp_steps :=
  repeat wp_step.

(** Hoare triples. *)
Definition hoare_triple {A} (P : Prop) (m : M A) (Q : A -> Prop) :=
  forall Q', P -> (forall a, Q a -> Q' a) -> wp m Q'.

(** Hoare triple. *)
Notation "'{{' P '}}' m '{{' v '.' Q '}}'" := (hoare_triple P m (fun v => Q))
  (at level 100, v binder).

(**************************************************************************)
(** *** Stack reduction machine. *)
(**************************************************************************)

Fixpoint apps (f : term) (xs : list term) : term :=
  match xs with
  | [] => f
  | x :: xs => apps (app f x) xs
  end.

(** This instance could be more general, but I only need this at the moment. *)
#[local] Instance red_apps : Proper (red ==> eq ==> red) apps.
Proof.
intros f f' Hf xs ? <-. induction xs in f, f', Hf |- * ; cbn.
- assumption.
- apply IHxs. now rewrite Hf.
Qed.

Definition zip (t : term * list term) := apps (fst t) (snd t).

(** Strong call-by-value stack reduction machine. *)
Fixpoint reduce_stack (fuel : nat) (t : term) (stack : list term) : M (term * list term) :=
  match fuel with 0 => fail | S fuel =>
  match t with
  | var i => ret (var i, stack)
  | app f x => reduce_stack fuel f (x :: stack)
  | lam t =>
    match stack with
    | x :: stack =>
      let* x := reduce_stack fuel x [] in
      reduce_stack fuel (subst0 (zip x) t) stack
    | [] =>
      let* t := reduce_stack fuel t [] in
      ret (lam (zip t), [])
    end
  end
  end.

Lemma reduce_stack_correct fuel t stack :
  {{ True }} reduce_stack fuel t stack {{ t'. apps t stack ~~> zip t' }}.
Proof.
induction fuel in t, stack |- * ; cbn [reduce_stack] ; intros Φ _ HΦ.
- wp_step.
- destruct t.
  + wp_step. apply HΦ. cbn. reflexivity.
  + apply IHfuel ; [constructor|]. intros [t' stack'] H. apply HΦ. exact H.
  + destruct stack as [| x stack].
    * wp_step. apply IHfuel ; [constructor|].
      intros [t' stack'] H'. cbn in H'. wp_step. apply HΦ. cbn.
      rewrite H'. reflexivity.
    * wp_step. apply IHfuel ; [constructor|].
      intros [t' stack'] H. cbn in H. apply IHfuel ; [constructor|].
      intros [t'' stack''] H1. apply HΦ. cbn in *.
      rewrite H. rewrite red_beta. rewrite H1. reflexivity.
Qed.


