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

Definition name_eq (n : name) (n' : name) : bool :=
  if string_dec n n' then true else false.

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

Fixpoint open_ (n : nat) (u : term) (t : term) : term :=
  match t with
  | fvar x => fvar x
  | bvar i => if i =? n then u else bvar i
  | app t1 t2 => app (open_ n u t1) (open_ n u t2)
  | lam t => lam (open_ (n+1) u t)
  end.

(*Definition open (u : term) (t : term) : term := open_ 0 u t.*)

(** [t ^^ u] replaces de Bruijn index [0] with [u] in [t].
    It assumes [u] is locally closed (so no lifting is needed). *)
Notation "t '^^' u" := (open_ 0 u t) (at level 30, no associativity).
Notation "t '^' x" := (open_ 0 (fvar x) t) (at level 30, no associativity).

Fixpoint close_ (n : nat) (x : name) (t : term) : term :=
  match t with
  | fvar y => if name_eq x y then bvar n else fvar y
  | bvar i => bvar i
  | app t1 t2 => app (close_ n x t1) (close_ n x t2)
  | lam t => lam (close_ (n+1) x t)
  end.

(** [t \^ x] replaces variable [x] with de Bruijn index [0] in [t]. *)
Notation "t '\^' x" := (close_ 0 x t) (at level 30, no associativity).

Lemma open_close x t : (t \^ x) ^ x = t.
Admitted.

Lemma fv_open_1 u t : fv t ⊆ fv (t ^^ u).
Proof.
enough (forall k, fv t ⊆ fv (open_ k u t)). { apply H. }
intros k. induction t in k, u |- * ; cbn.
- reflexivity.
- apply empty_subseteq.
- apply union_mono.
  + apply IHt1.
  + apply IHt2.
- apply IHt.
Qed.

Lemma fv_open_2 u t : fv (t ^^ u) ⊆ fv t ∪ fv u.
Proof.
enough (forall k, fv (open_ k u t) ⊆ fv t ∪ fv u). { apply H. }
intros k. induction t in k, u |- * ; cbn.
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
| lc_lam (L : gset name) t :
    (forall x, x ∉ L -> lc (t ^ x)) -> lc (lam t).

(** [body t] states that [t] is the body of a locally closed abstraction:
    [t] can only contain de Bruijn index [0]. *)
Definition body (t : term) : Prop :=
  exists L : gset name, forall x, x ∉ L -> lc (t ^ x).

Lemma lc_lam_iff_body t :
  lc (lam t) <-> body t.
Proof.
split ; intros H.
- inversion H ; subst. exists L. assumption.
- destruct H as [L H]. apply lc_lam with L. assumption.
Qed.

(*Lemma body_bvar i : body (bvar i) -> i = 0.
Proof.
intros [L H]. destruct (exist_fresh L) as [x Hx]. specialize (H x Hx).
cbn in H. destruct i ; auto. cbn in H. inversion H.
Qed.

Lemma open_lc u t :
  lc u -> body t -> lc (open u t).
Proof.
intros H1 H2. induction t ; cbn.
- apply lc_fvar.
- destruct i ; cbn.
  + assumption.
  + now apply body_bvar in H2.
- admit.
-*)

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
    | [] =>
      let* x := fresh_name in
      with_decl (LocalAssum x)
        (let* t := reduce_stack fuel (t ^ x) [] in
         ret (lam (zip t \^ x), []))
    | arg :: stack =>
      let* arg := reduce_stack fuel arg [] in
      reduce_stack fuel (t ^^ zip arg) stack
    end
  end
  end.

Lemma reduce_stack_correct fuel t stack :
  {{ ctx . well_scoped ctx t /\ Forall (well_scoped ctx) stack }}
    reduce_stack fuel t stack
  {{ _ t'. apps t stack ~~> zip t' }}.
Proof.
induction fuel in t, stack |- * ; cbn [reduce_stack] ; intros ctx Φ [Ht Hstack] HΦ.
- wp_step.
- destruct Ht.
  + wp_step. apply HΦ. cbn. reflexivity.
  + apply IHfuel ; [auto|]. intros [t' stack'] H'. apply HΦ.
  + destruct stack as [| x stack].
    * wp_steps. intros x Hx. wp_steps. apply IHfuel.
      {
        split ; [|auto].
        (* Here we want to apply [H] which corresponds to the rule for lambda in [well_scoped].
           We get stuck because the premise of the rule is too strong.
           Indeed, we get an _arbitrary_ set [L], and we need to show that the name
           [x] we got from [fresh_name] is not in [L].
           i.e. we would need the rule for [well_scoped_lam] to have a universally quantified
           premise. *)
        admit.
      }
      intros [t' stack'] ctx' H'. cbn in H'. wp_step. apply HΦ. cbn.
      (* Here the premise of the rule for reduction under lambdas is too strong:
         we need to prove that the bodies reduce to each other for co-finitely many
         fresh names, but we only know that is the case for exactly one fresh name
         (the one generated by [fresh_name]).
         i.e. we would need the rule for [red1_lam] to have an existentially quantified
         premise. *)
      eapply red_lam with (L := domain ctx).
      admit.
    * wp_step. apply IHfuel.
      { split ; [|auto]. inversion Hstack ; now subst. }
      intros [t' stack'] ctx' H'. cbn in H'. apply IHfuel ; [constructor|].
      intros [t'' stack''] H1. apply HΦ. cbn in *.
      rewrite H. rewrite red_beta. rewrite H1. reflexivity.*)
      admit.
Qed.


