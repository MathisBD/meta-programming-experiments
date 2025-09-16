From Stdlib Require Import Bool Nat List String.
From Stdlib.Classes Require Import Morphisms.
From stdpp Require Import gmap.
Import ListNotations.

(**************************************************************************)
(** *** lambda terms. *)
(**************************************************************************)

(** A name is a unique identifier for a variable.
    In a real implementation we would use an integer instead of a string. *)
Definition name := string.

Definition eqb_name (n n' : name) : bool :=
  if string_dec n n' then true else false.

Lemma eqb_name_spec n n' :
  reflect (n = n') (eqb_name n n').
Proof.
unfold eqb_name. destruct (string_dec n n').
- now left.
- now right.
Qed.

Lemma eqb_name_refl n : eqb_name n n = true.
Proof. destruct (eqb_name_spec n n) ; auto. Qed.

(** Untyped lambda terms in the locally nameless style. *)
Inductive term :=
| fvar (x : name) : term
| bvar (i : nat) : term
| app (t1 : term) (t2 : term) : term
| lam (t : term) : term.

(**************************************************************************)
(** *** Free variables. *)
(**************************************************************************)

(** [fv t] computes the set of free variables in [t]. *)
Fixpoint fv (t : term) : gset name :=
  match t with
  | fvar x => {[ x ]}
  | bvar i => ∅
  | app t1 t2 => fv t1 ∪ fv t2
  | lam t => fv t
  end.

(**************************************************************************)
(** *** Opening and closing. *)
(**************************************************************************)

Fixpoint open (n : nat) (u : term) (t : term) : term :=
  match t with
  | fvar x => fvar x
  | bvar i => if i =? n then u else bvar i
  | app t1 t2 => app (open n u t1) (open n u t2)
  | lam t => lam (open (n+1) u t)
  end.

(** [t ^^ u] replaces de Bruijn index [0] with [u] in [t].
    It assumes [u] is locally closed (so no lifting is needed). *)
Notation "t '^^' u" := (open 0 u t) (at level 30, no associativity).
Notation "t '^' x" := (open 0 (fvar x) t) (at level 30, no associativity).

Fixpoint close (n : nat) (x : name) (t : term) : term :=
  match t with
  | fvar y => if eqb_name x y then bvar n else fvar y
  | bvar i => bvar i
  | app t1 t2 => app (close n x t1) (close n x t2)
  | lam t => lam (close (n+1) x t)
  end.

(** [t \^ x] replaces variable [x] with de Bruijn index [0] in [t]. *)
Notation "t '\^' x" := (close 0 x t) (at level 30, no associativity).

Lemma fv_open_1 u t : fv t ⊆ fv (t ^^ u).
Proof.
generalize 0. intros k. induction t in k, u |- * ; cbn.
- reflexivity.
- apply empty_subseteq.
- apply union_mono.
  + apply IHt1.
  + apply IHt2.
- apply IHt.
Qed.

Lemma fv_open_2 u t : fv (t ^^ u) ⊆ fv t ∪ fv u.
Proof.
generalize 0. intros k. induction t in k, u |- * ; cbn.
- apply union_subseteq_l.
- destruct (Nat.eqb_spec i k) ; subst.
  + apply union_subseteq_r.
  + cbn. apply empty_subseteq.
- apply union_least.
  + rewrite IHt1. apply union_least.
    * apply union_subseteq_l', union_subseteq_l.
    * apply union_subseteq_r.
  + rewrite IHt2. apply union_least.
    * apply union_subseteq_l', union_subseteq_r.
    * apply union_subseteq_r.
- apply IHt.
Qed.

(**************************************************************************)
(** *** Locally closed terms. *)
(**************************************************************************)

(** A term is locally closed iff all its de Bruijn indices have
    a corresponding binder.
    E.g. the term [lam (bvar 2)] is _not_ locally closed
    because de Bruijn index [2] is unbound. *)
Inductive lc : term -> Prop :=
| lc_fvar x :
    lc (fvar x)
| lc_app t1 t2 :
    lc t1 -> lc t2 -> lc (app t1 t2)
| lc_lam x t :
    x ∉ fv t -> lc (t ^ x) -> lc (lam t).

(*Lemma open_open k x k' x' t :
  k ≠ k' -> open k x (open k' x' t) = open k' x' (open k x t).
Proof. Admitted.*)

(**************************************************************************)
(** *** Named substitution. *)
(**************************************************************************)

Fixpoint subst (x : name) (u : term) (t : term) : term :=
  match t with
  | fvar y => if eqb_name x y then u else fvar y
  | bvar i => bvar i
  | app t1 t2 => app (subst x u t1) (subst x u t2)
  | lam t => lam (subst x u t)
  end.

Notation "'[' x '~>' u ']' t" := (subst x u t)
  (at level 20, left associativity, format "[ x  ~>  u ] t").

(** Substituting a fresh name is the identity. *)
Lemma subst_fresh x t u :
  x ∉ fv t -> [x ~> u]t = t.
Proof.
intros H. induction t in x, u, H |- * ; cbn in *.
- apply not_elem_of_singleton in H. destruct (eqb_name_spec x x0) ; auto. exfalso. auto.
- reflexivity.
- rewrite IHt1, IHt2 ; [reflexivity| ..].
  + now apply not_elem_of_union in H.
  + now apply not_elem_of_union in H.
- f_equal. now apply IHt.
Qed.

(** Opening is the identity on locally closed terms. *)
Lemma open_lc k u t :
  lc t -> open k u t = t.
Proof. Admitted.

(** Substitution distributes on the open operation. *)
Lemma subst_open x u t1 t2 :
  lc u -> [x ~> u](t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
intros Hu. generalize 0. intros k. induction t1 in k |- * ; cbn.
- destruct (eqb_name_spec x x0) ; subst.
  + now rewrite open_lc.
  + cbn. reflexivity.
- destruct (Nat.eqb_spec i k) ; subst ; reflexivity.
- now rewrite IHt1_1, IHt1_2.
- now rewrite IHt1.
Qed.

(** Substitution and open for distinct names commute. *)
Lemma subst_open_var x y u t :
  x <> y ->
  lc u ->
  ([x ~> u]t) ^ y = [x ~> u](t ^ y).
Proof.
intros H Hu. rewrite subst_open by assumption. cbn.
destruct (eqb_name_spec x y) ; subst ; auto.
exfalso. auto.
Qed.

(** Opening up an abstraction of body [t] with a term [u] is the same as opening
    up the abstraction with a fresh name [x] and then substituting [u] for [x]. *)
Lemma subst_intro x t u :
  x ∉ fv t ->
  lc u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
intros Hx Hu. rewrite subst_open by assumption. cbn.
rewrite (eqb_name_refl x). now rewrite subst_fresh.
Qed.

Lemma fv_subst_1 x u t :
  fv t ⊆ fv ([x ~> u]t) ∪ {[ x ]}.
Proof.
induction t ; cbn.
- destruct (eqb_name_spec x x0) ; subst.
  + apply union_subseteq_r.
  + apply union_subseteq_l.
- apply empty_subseteq.
- apply union_least.
  + rewrite IHt1. apply union_least.
    * apply union_subseteq_l', union_subseteq_l.
    * apply union_subseteq_r.
  + rewrite IHt2. apply union_least.
    * apply union_subseteq_l', union_subseteq_r.
    * apply union_subseteq_r.
- assumption.
Qed.

(** Substitution respects local closure. *)
Lemma subst_lc x u t :
  lc u -> lc t -> lc ([x ~> u]t).
Proof.
intros Hu Ht. induction Ht in x, u, Hu |- * ; cbn.
- destruct (eqb_name_spec x x0).
  + assumption.
  + constructor.
- constructor ; [now apply IHHt1 | now apply IHHt2].
- destruct (exist_fresh (fv t ∪ fv u ∪ {[ x ]})) as [y Hy]. apply lc_lam with y.
  + admit.
  + rewrite subst_open_var by admit.

  + intros Hy' ; apply Hy ; clear Hy. apply fv_subst_1.  rewrite <-e in * ; clear e y.  admit.
  + rewrite subst_open_var ; auto. apply H0 ; auto.
    intros H' ; apply Hy ; clear Hy. apply fv_subst_1 with (x := x) (u := u) in H'.
    rewrite elem_of_union in H'. destruct H' ; [assumption|].
    rewrite elem_of_singleton in H1 ; subst. exfalso. auto.



(** Strong induction principle for [lc]. *)
Lemma lc_ind_strong (P : term -> Prop) :
  (forall x, P (fvar x)) ->
  (forall t1 t2, P t1 -> P t2 -> P (app t1 t2)) ->
  (forall t, (forall x, x ∉ fv t -> P (t ^ x)) -> P (lam t)) ->
  forall t, lc t -> P t.
Proof.
intros Hfvar Happ Hlam t Ht. induction Ht.
- apply Hfvar.
- now apply Happ.
- apply Hlam. intros y Hy.



Lemma lc_lam_intro x t :
  x ∉ fv t -> lc (t ^ x) -> lc (lam t).
Proof.
intros Hx H. apply lc_lam. intros y Hy.
rewrite subst_intro with (x := x) by auto.



(**************************************************************************)
(** *** Reduction relation. *)
(**************************************************************************)

Reserved Notation "t '~~>₁' u" (at level 60, no associativity).
Reserved Notation "t '~~>' u" (at level 60, no associativity).

Inductive red1 : term -> term -> Prop :=
| red1_beta t u :
    app (lam t) u ~~>₁ t ^^ u
| red1_app_l t t' u :
    t ~~>₁ t' -> app t u ~~>₁ app t' u
| red1_app_r t u u' :
    u ~~>₁ u' -> app t u ~~>₁ app t u'
| red1_lam (L : gset name) t t' :
    (forall x, x ∉ L -> t ^ x ~~>₁ t' ^ x) ->
    lam t ~~>₁ lam t'
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

Lemma red_lam (L : gset name) t t' :
  (forall x, x ∉ L -> t ^ x ~~> t' ^ x) ->
  lam t ~~> lam t'.
Proof. Admitted.

Lemma red_lam_intro x t t' :
  x ∉ fv t ->
  t ^ x ~~> t' ^ x ->
  lam t ~~> lam t'.
Proof. Admitted.

(*Lemma lam_intro_aux x t t' :
  x ∉ fv t -> t ^ x ~~>₁ t' ^ x ->
  forall y, y ∉ fv t -> t ^ y ~~> t' ^ y.
Proof.
intros Hx H y Hy.
Admitted.*)

Lemma red_beta t u : app (lam t) u ~~> t ^^ u.
Proof. apply red_red1. constructor. Qed.

(**************************************************************************)
(** *** Contexts and well-scoped terms. *)
(**************************************************************************)

Inductive local_decl :=
(* Local definition. *)
| LocalDef : name -> term -> local_decl
(* Local assumption (no body). *)
| LocalAssum : name -> local_decl.

(** A local context stores the declarations of all free variables
    in scope. The most recent declaration is at the head of the list. *)
Definition context := list local_decl.

(** The domain of a context is the set of variables which are bound
    by the context. *)
Fixpoint domain (ctx : context) : gset name :=
  match ctx with
  | [] => ∅
  | LocalDef x _ :: ctx => {[ x ]} ∪ domain ctx
  | LocalAssum x :: ctx => {[ x ]} ∪ domain ctx
  end.

(** A term is well-scoped iff all of its free variables appear in the context.
    In particular [bvar i] is never well-scoped. *)
Inductive well_scoped : context -> term -> Prop :=
| well_scoped_fvar ctx x :
    x ∈ domain ctx -> well_scoped ctx (fvar x)
| well_scoped_app ctx t1 t2 :
    well_scoped ctx t1 ->
    well_scoped ctx t2 ->
    well_scoped ctx (app t1 t2)
| well_scoped_lam (L : gset name) ctx t :
    (forall x, x ∉ L -> well_scoped (LocalAssum x :: ctx) (t ^ x)) ->
    well_scoped ctx (lam t).

Lemma well_scoped_lc ctx t : well_scoped ctx t -> lc t.
Proof.
intros H. induction H.
- constructor.
- now constructor.
- now apply lc_lam with L.
Qed.

Lemma well_scoped_fv ctx t :
  well_scoped ctx t -> fv t ⊆ domain ctx.
Proof.
intros H. induction H ; cbn.
- now rewrite <-elem_of_subseteq_singleton.
- now apply union_least.
- destruct (exist_fresh (L ∪ fv t)) as [x Hx].
  apply not_elem_of_union in Hx. destruct Hx as [Hx1 Hx2].
  specialize (H0 x Hx1). cbn in H0. intros y Hy.
  assert (y ∈ fv (t ^ x)) as Hy'. { now apply fv_open_1. }
  specialize (H0 y Hy').
  rewrite elem_of_union in H0. destruct H0.
  + rewrite elem_of_singleton in H0. subst. done.
  + assumption.
Qed.

(**************************************************************************)
(** *** Monadic programs. *)
(**************************************************************************)

(** Our monad [M] allows several effects:
    - read/write access to a local context.
    - critical failure.
    - out of fuel, which is not considered a failure. *)

Inductive result (A : Type) : Type :=
| Success (x : A) : result A
| Error : result A
| OutOfFuel : result A.
Arguments Success {A} x.
Arguments Error {A}.
Arguments OutOfFuel {A}.

Definition M (A : Type) : Type :=
  context -> result (context * A).

Definition ret {A} (x : A) : M A :=
  fun ctx => Success (ctx, x).

Definition bind {A B} (mx : M A) (f : A -> M B) : M B :=
  fun ctx =>
    match mx ctx with
    | Success (ctx, x) => f x ctx
    | OutOfFuel => OutOfFuel
    | Error => Error
    end.

(** [let*] monadic notation. *)
Notation "'let*' x ':=' t 'in' u" := (bind t (fun x => u))
  (at level 100, right associativity, t at next level, x pattern).

(** Signal fuel is out. *)
Definition out_of_fuel {A} : M A := fun ctx => OutOfFuel.

(** Fail. *)
Definition error {A} : M A := fun ctx => Error.

(** Read the local context. *)
Definition get_ctx : M context :=
  fun ctx => Success (ctx, ctx).

(** Replace the local context. *)
Definition put_ctx (ctx : context) : M unit :=
  fun _ => Success (ctx, tt).

(** Extend the local context with a new local declaration,
    run a computation, and restore the local context. *)
Definition with_decl {A} (d : local_decl) (m : M A) : M A :=
  let* ctx := get_ctx in
  let* _ := put_ctx (d :: ctx) in
  let* a := m in
  let* _ := put_ctx ctx in
  ret a.

(** [fresh_name] returns a name which is not in the current context. *)
Definition fresh_name : M name. Admitted.

(**************************************************************************)
(** *** Program logic. *)
(**************************************************************************)

(** Propositions which can depend on the context. *)
(*Definition cprop := context -> Prop.

(** Embed [cprop] into [Prop]. *)
Definition embed (P : cprop) : Prop := forall ctx, P ctx.
Notation "'⊢' P" := (embed P) (at level 90).*)

(** Weakest-precondition: [wp ctx m Q] means that running [m] in initial
    context [ctx] will not raise an error (out of fuel is fine), and the
    return value and final context satisfy [Q]. *)
Definition wp {A} (ctx1 : context) (m : M A) (Q : context -> A -> Prop) : Prop :=
  match m ctx1 with
  | OutOfFuel => True
  | Error => False
  | Success (ctx2, a) => Q ctx2 a
  end.

Lemma wp_ret {A} ctx (a : A) Q :
  Q ctx a -> wp ctx (ret a) Q.
Proof. intros H. cbn. assumption. Qed.

Lemma wp_bind {A B} ctx (m : M A) (f : A -> M B) Q :
  wp ctx m (fun ctx' a => wp ctx' (f a) Q) -> wp ctx (let* x := m in f x) Q.
Proof.
cbv. destruct (m ctx) as [[ctx' a] | |] ; cbn ; intros H ; [| auto..].
destruct (f a ctx') as [[ctx'' b] | |] ; auto.
Qed.

Lemma wp_consequence {A} ctx (m : M A) Q Q' :
  (forall a ctx', Q a ctx' -> Q' a ctx') -> wp ctx m Q -> wp ctx m Q'.
Proof.
intros H1. cbv. destruct (m ctx) as [[ctx' a] | |] ; cbn ; intros H ; [| auto..].
apply H1. assumption.
Qed.

Lemma wp_out_of_fuel {A} ctx Φ : wp ctx (@out_of_fuel A) Φ.
Proof. cbn. constructor. Qed.

Lemma wp_put ctx ctx' Φ :
  Φ ctx' tt -> wp ctx (put_ctx ctx') Φ.
Proof. cbn. auto. Qed.

Lemma wp_get ctx Φ :
  Φ ctx ctx -> wp ctx get_ctx Φ.
Proof. cbn. auto. Qed.

Lemma wp_with_decl {A} ctx Φ d (m : M A) :
  wp (d :: ctx) m (fun _ a => Φ ctx a) -> wp ctx (with_decl d m) Φ.
Proof. cbv. destruct (m (d :: ctx)) as [[a ctx'] | |] ; auto. Qed.

Lemma wp_fresh_name ctx Φ :
  (forall x, x ∉ domain ctx -> Φ ctx x) -> wp ctx fresh_name Φ.
Proof. Admitted.

Ltac wp_step :=
  match goal with
  | [ |- wp _ (ret _) _ ] => apply wp_ret
  | [ |- wp _ (bind _ _) _ ] => apply wp_bind
  | [ |- wp _ out_of_fuel _ ] => apply wp_out_of_fuel
  | [ |- wp _ get_ctx _ ] => apply wp_get
  | [ |- wp _ (put_ctx _) _ ] => apply wp_put
  | [ |- wp _ (with_decl _ _) _ ] => apply wp_with_decl
  | [ |- wp _ fresh_name _ ] => apply wp_fresh_name
  end.

Ltac wp_steps := repeat wp_step.

(** Hoare triples. *)
Definition hoare_triple {A} (P : context -> Prop) (m : M A) (Q : context -> A -> Prop) : Prop :=
  forall ctx, forall Φ, P ctx -> (forall a ctx', Q ctx' a -> Φ ctx' a) -> wp ctx m Φ.

(** Hoare triple. *)
Notation "'{{' c1 '.' P '}}' m '{{' c2 v '.' Q '}}'" :=
  (hoare_triple (fun c1 => P) m (fun c2 v => Q))
  (at level 100, c1 binder, v binder, c2 binder).

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

(** Strong call-by-value stack reduction machine.
    The implementation is quite naive. *)
Fixpoint reduce_stack (fuel : nat) (t : term) (stack : list term) : M (term * list term) :=
  match fuel with 0 => out_of_fuel | S fuel =>
  match t with
  | fvar x => ret (fvar x, stack)
  | bvar i => error
  | app f x => reduce_stack fuel f (x :: stack)
  | lam t =>
    match stack with
    | arg :: stack =>
      let* arg := reduce_stack fuel arg [] in
      reduce_stack fuel (t ^^ zip arg) stack
    | [] =>
      let* x := fresh_name in
      with_decl (LocalAssum x)
        (let* t := reduce_stack fuel (t ^ x) [] in
         ret (lam (zip t \^ x), []))
    end
  end
  end.

Lemma reduce_stack_correct fuel t stack :
  {{ ctx . well_scoped ctx t }} reduce_stack fuel t stack {{ _ t'. apps t stack ~~> zip t' }}.
Proof.
induction fuel in t, stack |- * ; cbn [reduce_stack] ; intros ctx Φ H HΦ.
- wp_step.
- destruct H.
  + wp_step. apply HΦ. cbn. reflexivity.
  + apply IHfuel ; [assumption|]. intros [t' stack'] H'. apply HΦ.
  + destruct stack as [| x stack].
    * wp_steps. intros x Hx. wp_steps. apply IHfuel.
      { admit. }
      intros [t' stack'] ctx' H'. cbn in H'. wp_step. apply HΦ. cbn.
      apply red_lam_intro with x.
      { intros Hx' ; apply Hx. inversion H ; subst. }
      eapply red_lam. setoid_rewrite open_close. with (L := \).
      admit. (*rewrite H'. reflexivity.*)
    * wp_step. apply IHfuel ; [constructor|].
      intros [t' stack'] H. cbn in H. apply IHfuel ; [constructor|].
      intros [t'' stack''] H1. apply HΦ. cbn in *.
      rewrite H. rewrite red_beta. rewrite H1. reflexivity.
Qed.


