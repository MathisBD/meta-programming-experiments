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
| lam : term -> term
| letin : term -> term -> term.

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
  | letin t u => letin (rename r t) (rename (rup r) u)
  end.

(**************************************************************************)
(** *** Contexts and well-scoped terms. *)
(**************************************************************************)

Inductive ldecl :=
| LAssum : ldecl
| LDef : term -> ldecl.

Definition context := list ldecl.

(** [scoping n t] states that [t] every de Bruijn index in [t]
    is smaller than [n]. *)
Inductive scoping : nat -> term -> Prop :=
| scoping_var n i :
    i < n -> scoping n (var i)
| scoping_app n t1 t2 :
    scoping n t1 ->
    scoping n t2 ->
    scoping n (app t1 t2)
| scoping_lam n t :
    scoping (S n) t ->
    scoping n (lam t)
| scoping_letin n t u :
    scoping n t ->
    scoping (S n) u ->
    scoping n (letin t u).

#[export] Hint Resolve scoping_var scoping_app scoping_lam scoping_letin : scoping.
#[export] Hint Extern 10 (_ < _) => lia : scoping.

Lemma scoping_var_zero n :
  scoping (S n) (var 0).
Proof. constructor. lia. Qed.

Lemma scoping_var_succ n i :
  scoping n (var i) -> scoping (S n) (var (S i)).
Proof. constructor. inversion H ; subst. lia. Qed.

#[export] Hint Resolve scoping_var_zero scoping_var_succ : scoping.

Lemma scoping_weaken n n' t :
  n <= n' -> scoping n t -> scoping n' t.
Proof.
intros Hn H. induction H in n', Hn |- *.
- constructor. lia.
- constructor ; auto.
- constructor. apply IHscoping. lia.
- constructor.
  + apply IHscoping1. assumption.
  + apply IHscoping2. lia.
Qed.

Lemma scoping_weaken_one n t :
  scoping n t -> scoping (S n) t.
Proof. apply scoping_weaken ; lia. Qed.
#[export] Hint Resolve scoping_weaken_one : scoping.

(** [rscoping n1 n2 r] states that [r] maps a context of size [n1]
    into a context of size [n2]. *)
Definition rscoping (n1 n2 : nat) (r : ren) : Prop :=
  forall i, i < n1 -> r i < n2.

Lemma rscoping_rid n :
  rscoping n n rid.
Proof. intros i Hi. unfold rid. lia. Qed.

Lemma rscoping_rshift n :
  rscoping n (S n) rshift.
Proof. intros i Hi. unfold rshift. lia. Qed.

Lemma rscoping_rcomp n1 n2 n3 r r' :
  rscoping n1 n2 r ->
  rscoping n2 n3 r' ->
  rscoping n1 n3 (rcomp r r').
Proof. intros H1 H2 i Hi. unfold rcomp. apply H2, H1. assumption. Qed.

Lemma rscoping_rcons n1 n2 i r :
  i < n2 ->
  rscoping n1 n2 r ->
  rscoping (S n1) n2 (rcons i r).
Proof. *
intros H1 H2 [|j] Hj ; cbn.
- assumption.
- apply H2. lia.
Qed.

#[export] Hint Resolve rscoping_rid rscoping_rshift rscoping_rcomp rscoping_rcons : scoping.
#[export] Hint Unfold rup : scoping.

(** Scoping is preserved by renaming. *)
Lemma scoping_rename r t n1 n2 :
  scoping n1 t ->
  rscoping n1 n2 r ->
  scoping n2 (rename r t).
Proof.
intros Ht Hr. induction Ht in r, Hr, n2 |- * ; cbn.
- constructor. now apply Hr.
- constructor.
  + now apply IHHt1.
  + now apply IHHt2.
- constructor. apply IHHt. intros i Hi. destruct i as [|i] ; cbn in *.
  + lia.
  + unfold rcomp, rshift. rewrite <-PeanoNat.Nat.succ_lt_mono. apply Hr. lia.
- constructor.
  + now apply IHHt1.
  + apply IHHt2. intros i Hi. destruct i as [|i] ; cbn in *.
    * lia.
    * unfold rcomp, rshift. rewrite <-PeanoNat.Nat.succ_lt_mono. apply Hr. lia.
Qed.

#[export] Hint Resolve scoping_rename : scoping.

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

Notation "x >>= f" := (bind x f) (at level 50, no associativity).
Notation "f =<< x" := (bind x f) (at level 50, no associativity).

(** [let*] monadic notation. *)
Notation "'let*' x ':=' t 'in' u" := (bind t (fun x => u))
  (at level 100, right associativity, t at next level, x pattern).

Definition fmap {A B} (f : A -> B) (mx : M A) : M B :=
  let* x := mx in
  ret (f x).

Notation "f <$> x" := (fmap f x) (at level 30, right associativity).

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

(** Convenience function to build a lambda abstraction. *)
Definition mk_lambda (f : M term) : M term :=
  with_decl LAssum
    (let* body := f in
     ret (lam body)).

(** Convenience function to build a let-expression. *)
Definition mk_letin (def : term) (f : M term) : M term :=
  with_decl (LDef def)
    (let* body := f in
     ret (letin def body)).

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

Lemma wp_fmap {A B} ctx (f : A -> B) (mx : M A) Φ :
  wp ctx mx (fun ctx x => Φ ctx (f x)) -> wp ctx (fmap f mx) Φ.
Proof. intros H. unfold fmap. apply wp_bind. apply H. Qed.

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
  (wp (LAssum :: ctx) f (fun _ body => Φ ctx (lam body))) ->
  wp ctx (mk_lambda f) Φ.
Proof.
intros H. unfold mk_lambda. apply wp_with_decl, wp_bind. apply H.
Qed.

Lemma wp_mk_letin def f ctx Φ :
  (wp (LDef def :: ctx) f (fun _ body => Φ ctx (letin def body))) ->
  wp ctx (mk_letin def f) Φ.
Proof.
intros H. unfold mk_letin. apply wp_with_decl, wp_bind. apply H.
Qed.

Ltac wp_step :=
  match goal with
  | [ |- wp _ (ret _) _ ] => apply wp_ret
  | [ |- wp _ (bind _ _) _ ] => apply wp_bind
  | [ |- wp _ (fmap _ _) _ ] => apply wp_fmap
  | [ |- wp _ out_of_fuel _ ] => apply wp_out_of_fuel
  | [ |- wp _ get_ctx _ ] => apply wp_get
  | [ |- wp _ (put_ctx _) _ ] => apply wp_put
  | [ |- wp _ (with_decl _ _) _ ] => apply wp_with_decl
  | [ |- wp _ (mk_lambda _) _ ] => apply wp_mk_lambda
  | [ |- wp _ (mk_letin _ _) _ ] => apply wp_mk_letin
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

(** [apps f xs] forms the n-ary application of [f] to arguments [xs]. *)
Fixpoint apps (f : term) (xs : list term) : term :=
  match xs with
  | [] => f
  | x :: xs => apps (app f x) xs
  end.

Fixpoint cps (n : nat) (t : term) (k : term) : M term :=
  match n with 0 => out_of_fuel | S n =>
  match t with
  | var i => ret (app k (var i))
  | app t1 t2 =>
    cps n t1 =<< mk_lambda ( (* x1 *)
    cps n (rename (lift0 1) t2) =<< mk_lambda ( (* x2 *)
    ret (apps (var 1 (* x1 *)) [ var 0 (* x2 *) ; rename (lift0 2) k ])))
  | lam t' =>
    app k <$>
      mk_lambda ( (* x *)
      mk_lambda ( (* k' *)
      cps n (rename (lift0 1) t') (var 0 (* k' *))))
  | letin t u =>
    cps n t =<< mk_lambda ( (* v *)
    mk_letin (var 0 (* v *)) ( (* x *)
    cps n (rename (lift 1 1) u) (rename (lift0 2) k)))
  end
  end.

(** Prove a goal of the form [scoping _ _].
    Succeeds or does nothing. *)
Ltac prove_scoping :=
  match goal with
  | [ |- scoping _ _ ] =>
    solve [ cbn in * ; autounfold with scoping ; eauto 10 with scoping ]
  end.

Lemma cps_safe n t k :
  {{ ctx. scoping (length ctx) t /\ scoping (length ctx) k }}
    cps n t k
  {{ ctx t'. scoping (length ctx) t' }}.
Proof.
induction n in k, t |- * ; intros ctx Φ [Ht Hk] HΦ ; cbn ; [constructor|].
destruct t ; cbn.
- apply HΦ. prove_scoping.
- inversion Ht ; subst. wp_steps.
  apply IHn. { split ; prove_scoping. }
  intros t' Ht'. apply IHn. { split ; prove_scoping. }
  intros t'' Ht''. apply HΦ. assumption.
- wp_steps. apply IHn. { inversion Ht ; subst. split ; prove_scoping. }
  intros t' Ht'. wp_steps. apply HΦ. prove_scoping.
- inversion Ht ; subst. wp_steps.
  apply IHn. { split ; prove_scoping. }
  intros t' Ht'. apply IHn. { split ; prove_scoping. }
  intros t'' Ht''. apply HΦ. assumption.
Qed.
