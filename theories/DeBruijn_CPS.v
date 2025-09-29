From Stdlib Require Import Bool Nat List Lia.
From Stdlib.Classes Require Import Morphisms.
From Equations Require Import Equations.
Import ListNotations.

(** If [H] is a hypothesis [H : P -> Q], [feed H] first asks to prove [P],
    and then the original goal with [H : Q]. *)

Ltac feed_aux H :=
  match type of H with
  | ?P -> ?Q =>
    let HP := fresh "H" in
    assert P as HP ; [| specialize (H HP) ; clear HP ]
  end.

Tactic Notation "feed" ident(H) "by" tactic3(t) :=
  feed_aux H ; [now t|].

Tactic Notation "feed" ident(H) :=
  feed_aux H.

(**************************************************************************)
(** *** lambda terms. *)
(**************************************************************************)

(** Untyped lambda terms, using de Bruijn indices. *)
Inductive term :=
| var : nat -> term
| app : term -> term -> term
| lam : term -> term.

(**************************************************************************)
(** *** Renamings. *)
(**************************************************************************)

(** A renaming is a map from de Bruijn indices to de Bruijn indices. *)
Definition ren := nat -> nat.

Definition rid : ren :=
  fun i => i.

Definition rshift : ren :=
  fun i => S i.

Definition rcons (i : nat) (r : ren) : ren :=
  fun i' =>
    match i' with
    | 0 => i
    | S i' => r i'
    end.

Definition rcomp (r1 r2 : ren) : ren :=
  fun i => r2 (r1 i).

Definition rup (r : ren) : ren :=
  rcons 0 (rcomp r rshift).

(** [lift0 ofs] is a renaming which adds [ofs] to every index. *)
Fixpoint lift0 (ofs : nat) : ren :=
  match ofs with
  | 0 => rid
  | S ofs => rcomp rshift (lift0 ofs)
  end.

(** [lift base ofs] is a renaming which adds [ofs] to every index
    greater or equal to [base]. *)
Fixpoint lift (base ofs : nat) : ren :=
  match base with
  | 0 => lift0 ofs
  | S base => rup (lift base ofs)
  end.

(** [rename r t] applies renaming [r] to term [t]. *)
Fixpoint rename (r : ren) (t : term) : term :=
  match t with
  | var i => var (r i)
  | app t1 t2 => app (rename r t1) (rename r t2)
  | lam t => lam (rename (rup r) t)
  end.

(**************************************************************************)
(** *** Substitutions. *)
(**************************************************************************)

(** A substitution is a map from de Bruijn indices to terms. *)
Definition subst := nat -> term.

Definition sid : subst :=
  fun i => var i.

Definition sshift : subst :=
  fun i => var (S i).

Definition scons (t : term) (s : subst) : subst :=
  fun i =>
    match i with
    | 0 => t
    | S i => s i
    end.

Definition srcomp (s : subst) (r : ren) : subst :=
  fun i => rename r (s i).

Definition rscomp (r : ren) (s : subst) : subst :=
  fun i => s (r i).

Definition sup (s : subst) : subst :=
  scons (var 0) (srcomp s rshift).

(** [substitute s t] applies substitution [s] to term [t]. *)
Fixpoint substitute (s : subst) (t : term) : term :=
  match t with
  | var i => s i
  | app t1 t2 => app (substitute s t1) (substitute s t2)
  | lam t => lam (substitute (sup s) t)
  end.

(**************************************************************************)
(** *** Contexts and well-scoped terms. *)
(**************************************************************************)

(** In this example, local declarations contain no information.
    In a more realistic setting, a local declaration for a variable
    would contain the variable's type and body (if present). *)
Inductive ldecl := LDecl.

Definition context := list ldecl.

Inductive well_scoped : context -> term -> Prop :=
| well_scoped_var ctx i :
    i < length ctx -> well_scoped ctx (var i)
| well_scoped_app ctx t1 t2 :
    well_scoped ctx t1 ->
    well_scoped ctx t2 ->
    well_scoped ctx (app t1 t2)
| well_scoped_lam ctx t :
    well_scoped (LDecl :: ctx) t ->
    well_scoped ctx (lam t).

#[export] Hint Resolve well_scoped_var well_scoped_app well_scoped_lam : well_scoped.

Lemma well_scoped_weaken ctx ctx' t :
  length ctx <= length ctx' -> well_scoped ctx t -> well_scoped ctx' t.
Proof.
intros Hc H. induction H in ctx', Hc |- *.
- constructor. lia.
- constructor ; auto.
- constructor. apply IHwell_scoped. cbn. lia.
Qed.

Lemma well_scoped_weaken' ctx t :
  well_scoped ctx t -> well_scoped (LDecl :: ctx) t.
Proof. apply well_scoped_weaken ; cbn ; lia. Qed.
#[export] Hint Resolve well_scoped_weaken' : well_scoped.

(** Well-scopedness is preserved by renamings, under certain conditions. *)
Lemma rename_well_scoped r t c1 c2 :
  well_scoped c1 t ->
  (forall i, i < length c1 -> r i < length c2) ->
  well_scoped c2 (rename r t).
Proof.
intros Ht Hr. induction Ht in r, Hr, c2 |- * ; cbn.
- constructor. now apply Hr.
- constructor.
  + now apply IHHt1.
  + now apply IHHt2.
- constructor. apply IHHt. intros i Hi. destruct i as [|i] ; cbn in *.
  + lia.
  + unfold rcomp, rshift. rewrite <-PeanoNat.Nat.succ_lt_mono. apply Hr. lia.
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
Definition with_decl {A} (d : ldecl) (m : M A) : M A :=
  let* ctx := get_ctx in
  let* _ := put_ctx (d :: ctx) in
  let* a := m in
  let* _ := put_ctx ctx in
  ret a.

(** Convenient function to build a lambda abstraction. *)
Definition mk_lambda (f : M term) : M term :=
  with_decl LDecl
    (let* body := f in
     ret (lam body)).

(**************************************************************************)
(** *** Program logic. *)
(**************************************************************************)

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

Lemma wp_mk_lambda f ctx Φ :
  (wp (LDecl :: ctx) f (fun _ body => Φ ctx (lam body))) ->
  wp ctx (mk_lambda f) Φ.
Proof.
intros H. unfold mk_lambda. apply wp_with_decl, wp_bind. apply H.
Qed.

Ltac wp_step :=
  match goal with
  | [ |- wp _ (ret _) _ ] => apply wp_ret
  | [ |- wp _ (bind _ _) _ ] => apply wp_bind
  | [ |- wp _ out_of_fuel _ ] => apply wp_out_of_fuel
  | [ |- wp _ get_ctx _ ] => apply wp_get
  | [ |- wp _ (put_ctx _) _ ] => apply wp_put
  | [ |- wp _ (with_decl _ _) _ ] => apply wp_with_decl
  | [ |- wp _ (mk_lambda _) _ ] => apply wp_mk_lambda
  end.

Ltac wp_steps := repeat wp_step.

(** Hoare triples. *)
Definition hoare_triple {A} (P : context -> Prop) (m : M A) (Q : context -> A -> Prop) : Prop :=
  forall ctx, forall Φ, P ctx -> (forall a, Q ctx a -> Φ ctx a) -> wp ctx m Φ.

(** Hoare triple. *)
Notation "'{{' c1 '.' P '}}' m '{{' c2 v '.' Q '}}'" :=
  (hoare_triple (fun c1 => P) m (fun c2 v => Q))
  (at level 100, c1 binder, v binder, c2 binder).

(**************************************************************************)
(** *** CPS transformation meta-program. *)
(**************************************************************************)

Fixpoint cps (n : nat) (t : term) (k : term) : M term :=
  match n with 0 => out_of_fuel | S n =>
  match t with
  | var i => ret (app k (var i))
  | app t1 t2 =>
    let* k1 := mk_lambda ( (* x1 *)
      let* k2 := mk_lambda ( (* x2 *)
        ret (app (var 1 (* x1 *)) (app (var 0 (* x2 *)) (rename (lift0 2) k))))
      in cps n (rename (lift0 1) t2) k2)
    in
    cps n t1 k1
  | lam t' =>
    let* rhs :=
      mk_lambda ( (* x *)
      mk_lambda ( (* k' *)
        cps n (rename (lift0 1) t') (var 0 (* k' *))
      ))
    in
    ret (app k rhs)
  end
  end.

Lemma cps_safe n t k :
  {{ ctx. well_scoped ctx t /\ well_scoped ctx k }}
    cps n t k
  {{ ctx t'. well_scoped ctx t' }}.
Proof.
induction n in k, t |- * ; intros ctx Φ [Ht Hk] HΦ ; cbn ; [constructor|].
destruct t ; cbn.
- apply HΦ. auto with well_scoped.
- inversion Ht ; subst. wp_steps.
  apply IHn.
  { split.
    - eapply rename_well_scoped ; [exact H3|]. intros i Hi.
      unfold rcomp, rshift, rid. cbn. lia.
    - constructor. constructor.
      + constructor. cbn. lia.
      + constructor.
        * constructor. cbn. lia.
        * eapply rename_well_scoped ; [exact Hk|]. intros i Hi.
          unfold rcomp, rshift, rid. cbn. lia. }
  intros t' Ht'. apply IHn. { auto with well_scoped. }
  intros t'' Ht''. apply HΦ. assumption.
- wp_steps. apply IHn.
  { split.
    - inversion Ht ; subst. eapply rename_well_scoped ; [eassumption|].
      intros i Hi. unfold rcomp, rshift, rid. cbn in *. lia.
    - constructor. cbn. lia. }
  intros t' Ht'. wp_steps. apply HΦ. auto with well_scoped.
Qed.
