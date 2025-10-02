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

(** [apps f xs] forms the n-ary application of [f] to arguments [xs]. *)
Fixpoint apps (f : term) (xs : list term) : term :=
  match xs with
  | [] => f
  | x :: xs => apps (app f x) xs
  end.

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

Definition subst := nat -> term.

Definition sid : subst :=
  fun i => var i.

Definition sshift : subst :=
  fun i => var (S i).

Definition scons (t : term) (s : subst) : subst :=
  fun i' =>
    match i' with
    | 0 => t
    | S i' => s i'
    end.

Definition srcomp (s : subst) (r : ren) : subst :=
  fun i => rename r (s i).

Definition rscomp (r : ren) (s : subst) : subst :=
  fun i => s (r i).

Definition sup (s : subst) : subst :=
  scons (var 0) (srcomp s rshift).

(** [substitute r t] applies substitution [s] to term [t]. *)
Fixpoint substitute (s : subst) (t : term) : term :=
  match t with
  | var i => s i
  | app t1 t2 => app (substitute s t1) (substitute s t2)
  | lam t => lam (substitute (sup s) t)
  end.

Definition scomp (s1 s2 : subst) : subst :=
  fun i => substitute s2 (s1 i).

(**************************************************************************)
(** *** Beta reduction. *)
(**************************************************************************)

Reserved Notation "t '~~>₁' u" (at level 55, no associativity).
Reserved Notation "t '~~>+' u" (at level 55, no associativity).

Inductive red1 : term -> term -> Prop :=
| red1_beta t u : app (lam t) u ~~>₁ substitute (scons u sid) t
| red1_app_l t t' u : t ~~>₁ t' -> app t u ~~>₁ app t' u
| red1_app_r t u u' : u ~~>₁ u' -> app t u ~~>₁ app t u'
| red1_lam t t' : t ~~>₁ t' -> lam t ~~>₁ lam t'
where "t '~~>₁' u" := (red1 t u).

Inductive red_plus : term -> term -> Prop :=
| red_plus_base t1 t2 : t1 ~~>₁ t2 -> t1 ~~>+ t2
| red_plus_trans t1 t2 t3 : t1 ~~>+ t2 -> t2 ~~>+ t3 -> t1 ~~>+ t3
where "t '~~>+' u" := (red_plus t u).

#[export] Instance red_plus_Transitive : Transitive red_plus.
Proof. exact red_plus_trans. Qed.

#[export] Instance red_plus_app_l : Proper (red_plus ==> eq ==> red_plus) app.
Proof.
intros t t' Ht ? u ->. induction Ht.
- apply red_plus_base, red1_app_l. assumption.
- etransitivity ; eauto.
Qed.

#[export] Instance red_plus_app_r : Proper (eq ==> red_plus ==> red_plus) app.
Proof.
intros ? t -> u u' Hu. induction Hu.
- apply red_plus_base, red1_app_r. assumption.
- etransitivity ; eauto.
Qed.

#[export] Instance red_plus_lam : Proper (red_plus ==> red_plus) lam.
Proof.
intros t t' Ht. induction Ht.
- apply red_plus_base, red1_lam. assumption.
- etransitivity ; eauto.
Qed.

Lemma red1_rename_aux r t u :
  substitute (scons (rename r u) sid) (rename (rup r) t) =
  rename r (substitute (scons u sid) t).
Proof. Admitted.

#[export] Instance red1_rename r : Proper (red1 ==> red1) (rename r).
Proof.
intros t t' Ht. induction Ht in r |- * ; cbn.
- rewrite <-red1_rename_aux. apply red1_beta.
- apply red1_app_l, IHHt.
- apply red1_app_r, IHHt.
- apply red1_lam, IHHt.
Qed.

#[export] Instance red_plus_rename r : Proper (red_plus ==> red_plus) (rename r).
Proof.
intros t t' Ht. induction Ht.
- apply red_plus_base, red1_rename. assumption.
- etransitivity ; eauto.
Qed.

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
    scoping n (lam t).

#[export] Hint Resolve scoping_var scoping_app scoping_lam : scoping.
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
Qed.

#[export] Hint Resolve scoping_rename : scoping.

(** Prove a goal of the form [scoping _ _].
    Succeeds or does nothing. *)
Ltac prove_scoping :=
  match goal with
  | [ |- scoping _ _ ] =>
    solve [ cbn in * ; autounfold with scoping ; eauto 10 with scoping ]
  end.

(**************************************************************************)
(** *** Monadic programs. *)
(**************************************************************************)

(** Our monad [M] allows several effects:
    - read/write access to a local context.
    - out of fuel, which is not considered a failure. *)

Inductive result (A : Type) : Type :=
| Success (x : A) : result A
| OutOfFuel : result A.
Arguments Success {A} x.
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

(**************************************************************************)
(** *** Relational program logic. *)
(**************************************************************************)

(** Relational weakest-precondition: [wp2 (c1, c2) (m1, m2) Q] means that
    running [m1] and [m2] in initial context [c1] and [c2] will not raise
    an error (out of fuel is fine), and the return values and final
    contexts satisfy [Q]. *)
Definition wp2 {A B} (c : context * context) (m : M A * M B) (Q : context * context -> A * B -> Prop) : Prop :=
  let (c1, c2) := c in
  let (m1, m2) := m in
  match m1 c1, m2 c2 with
  | Success (c1', a), Success (c2', b) => Q (c1', c2') (a, b)
  | _, _ => True
  end.

Lemma wp2_ret {A1 A2} c1 c2 (a1 : A1) (a2 : A2) Q :
  Q (c1, c2) (a1, a2) -> wp2 (c1, c2) (ret a1, ret a2) Q.
Proof. intros H. cbn. assumption. Qed.

Lemma wp2_bind {A1 B1 A2 B2} c1 c2 (m1 : M A1) (m2 : M A2)
  (f1 : A1 -> M B1) (f2 : A2 -> M B2) Q :
  wp2 (c1, c2) (m1, m2) (fun '(c1', c2') '(a1, a2) => wp2 (c1', c2') (f1 a1, f2 a2) Q) ->
  wp2 (c1, c2) (let* x := m1 in f1 x, let* x := m2 in f2 x) Q.
Proof.
unfold wp2, bind. intros H.
destruct (m1 c1) as [[c1' a1] |] eqn:E1 ; destruct (m2 c2) as [[c2' a2] |] eqn:E2.
all: auto. destruct (f1 a1 c1') as [[] |] ; auto.
Qed.

Lemma wp2_bind_l1 {A1 B1 A2} c1 c2 (m1 : M A1) (m2 : M A2) (f1 : A1 -> M B1) Φ :
  wp2 (c1, c2) (m1, m2) (fun '(c1', c2') '(a1, a2) => wp2 (c1', c2') (f1 a1, ret a2) Φ) ->
  wp2 (c1, c2) (let* x := m1 in f1 x, m2) Φ.
Proof.
unfold wp2, bind. intros H.
destruct (m1 c1) as [[c1' a1] |] eqn:E1 ; destruct (m2 c2) as [[c2' a2] |] eqn:E2.
all: auto. destruct (f1 a1 c1') as [[] |] ; auto.
Qed.

Lemma wp2_bind_l2 {A1 B1 A2} c1 c2 (m1 : M A1) (m2 : M A2) (f1 : A1 -> M B1) Φ :
  wp2 (c1, c2) (m1, ret tt) (fun '(c1', c2') '(a1, _) => wp2 (c1', c2') (f1 a1, m2) Φ) ->
  wp2 (c1, c2) (let* x := m1 in f1 x, m2) Φ.
Proof.
unfold wp2, bind. intros H. cbn in *.
destruct (m1 c1) as [[c1' a1] |] eqn:E1 ; destruct (m2 c2) as [[c2' a2] |] eqn:E2.
all: auto.
Qed.

Lemma wp2_bind_r1 {A1 A2 B2} c1 c2 (m1 : M A1) (m2 : M A2) (f2 : A2 -> M B2) Φ :
  wp2 (c1, c2) (m1, m2) (fun '(c1', c2') '(a1, a2) => wp2 (c1', c2') (ret a1, f2 a2) Φ) ->
  wp2 (c1, c2) (m1, let* x := m2 in f2 x) Φ.
Proof.
unfold wp2, bind. intros H.
destruct (m1 c1) as [[c1' a1] |] eqn:E1 ; destruct (m2 c2) as [[c2' a2] |] eqn:E2.
all: auto.
Qed.

Lemma wp2_bind_r2 {A1 A2 B2} c1 c2 (m1 : M A1) (m2 : M A2) (f2 : A2 -> M B2) Φ :
  wp2 (c1, c2) (ret tt, m2) (fun '(c1', c2') '(_, a2) => wp2 (c1', c2') (m1, f2 a2) Φ) ->
  wp2 (c1, c2) (m1, let* x := m2 in f2 x) Φ.
Proof.
unfold wp2, bind. intros H. cbn in *.
destruct (m1 c1) as [[c1' a1] |] eqn:E1 ; destruct (m2 c2) as [[c2' a2] |] eqn:E2.
all: auto.
Qed.

Lemma wp2_fmap_l {A1 B1 A2} c1 c2 (f1 : A1 -> B1) (m1 : M A1) (m2 : M A2) Φ :
  wp2 (c1, c2) (m1, m2) (fun '(c1', c2') '(a1, a2) => Φ (c1', c2') (f1 a1, a2)) ->
  wp2 (c1, c2) (fmap f1 m1, m2) Φ.
Proof. intros H. unfold fmap. apply wp2_bind_l1. apply H. Qed.

Lemma wp2_fmap_r {A1 A2 B2} c1 c2 (f2 : A2 -> B2) (m1 : M A1) (m2 : M A2) Φ :
  wp2 (c1, c2) (m1, m2) (fun '(c1', c2') '(a1, a2) => Φ (c1', c2') (a1, f2 a2)) ->
  wp2 (c1, c2) (m1, fmap f2 m2) Φ.
Proof. intros H. unfold fmap. apply wp2_bind_r1. apply H. Qed.

Lemma wp2_consequence {A1 A2} c1 c2 (m1 : M A1) (m2 : M A2) Φ Φ' :
  wp2 (c1, c2) (m1, m2) Φ ->
  (forall c1 c2 a1 a2, Φ (c1, c2) (a1, a2) -> Φ' (c1, c2) (a1, a2)) ->
  wp2 (c1, c2) (m1, m2) Φ'.
Proof.
unfold wp2.
destruct (m1 c1) as [[c1' a1] |] eqn:E1 ; destruct (m2 c2) as [[c2' a2] |] eqn:E2.
all: auto.
Qed.

Lemma wp2_out_of_fuel_l {A1 A2} c1 c2 (m : M A2) Φ :
  wp2 (c1, c2) (@out_of_fuel A1, m) Φ.
Proof. unfold wp2. cbn. constructor. Qed.

Lemma wp2_out_of_fuel_r {A1 A2} c1 c2 (m : M A1) Φ :
  wp2 (c1, c2) (m, @out_of_fuel A2) Φ.
Proof. unfold wp2. cbn. destruct (m c1) as [[] |] ; constructor. Qed.

Lemma wp2_put_l {A} c1 c1' c2 (m : M A) Φ :
   wp2 (c1', c2) (ret tt, m) Φ ->
   wp2 (c1, c2) (put_ctx c1', m) Φ.
Proof. unfold wp2. cbn. auto. Qed.

Lemma wp2_put_r {A} c1 c2 c2' (m : M A) Φ :
  wp2 (c1, c2') (m, ret tt) Φ ->
  wp2 (c1, c2) (m, put_ctx c2') Φ.
Proof. unfold wp2. cbn. auto. Qed.

Lemma wp2_get_l {A} c1 c2 (m : M A) Φ :
  wp2 (c1, c2) (ret tt, m) (fun '(c1', c2') '(_, a2) => Φ (c1', c2') (c1', a2)) ->
  wp2 (c1, c2) (get_ctx, m) Φ.
Proof. cbn. auto. Qed.

Lemma wp2_get_r {A} c1 c2 (m : M A) Φ :
  wp2 (c1, c2) (m, ret tt) (fun '(c1', c2') '(a1, _) => Φ (c1', c2') (a1, c2')) ->
  wp2 (c1, c2) (m, get_ctx) Φ.
Proof. cbn. auto. Qed.

Lemma wp2_with_decl_l {A1 A2} c1 c2 d (m1 : M A1) (m2 : M A2) Φ :
  wp2 (d :: c1, c2) (m1, m2) (fun '(_, c2') '(a1, a2) => Φ (c1, c2') (a1, a2)) ->
  wp2 (c1, c2) (with_decl d m1, m2) Φ.
Proof.
intros H. unfold with_decl.
apply wp2_bind_l2, wp2_get_l, wp2_ret.
apply wp2_bind_l2, wp2_put_l, wp2_ret.
apply wp2_bind_l1, H.
Qed.

Lemma wp2_with_decl_r {A1 A2} c1 c2 d (m1 : M A1) (m2 : M A2) Φ :
  wp2 (c1, d :: c2) (m1, m2) (fun '(c1', _) '(a1, a2) => Φ (c1', c2) (a1, a2)) ->
  wp2 (c1, c2) (m1, with_decl d m2) Φ.
Proof.
intros H. unfold with_decl.
apply wp2_bind_r2, wp2_get_r, wp2_ret.
apply wp2_bind_r2, wp2_put_r, wp2_ret.
apply wp2_bind_r1, H.
Qed.

Lemma wp2_mk_lambda_l {A} c1 c2 (m : M A) f Φ :
  wp2 (LAssum :: c1, c2) (f, m) (fun '(_, c2') '(body, a) => Φ (c1, c2') (lam body, a)) ->
  wp2 (c1, c2) (mk_lambda f, m) Φ.
Proof.
intros H. unfold mk_lambda. apply wp2_with_decl_l, wp2_bind_l1. apply H.
Qed.

Lemma wp2_mk_lambda_r {A} c1 c2 (m : M A) f Φ :
  wp2 (c1, LAssum :: c2) (m, f) (fun '(c1', _) '(a, body) => Φ (c1', c2) (a, lam body)) ->
  wp2 (c1, c2) (m, mk_lambda f) Φ.
Proof.
intros H. unfold mk_lambda. apply wp2_with_decl_r, wp2_bind_r1. apply H.
Qed.

(*Lemma wp2_pull_r {A1 B1} c1 c2 (m : M A1) (f : A1 -> M B1) Φ :
  wp2 (c1, c2) (let* x := m in f x, m) Φ ->
  wp2 (c1, c2) (m, ret tt) (fun '(c1', c2') '(a, _) => wp2 (c1', c2') (f a, m) Φ).
Proof.
unfold wp2, bind.
destruct (m c1) as [[c1' a1] |] eqn:E1 ; cbn ; auto.
Qed.*)

Lemma wp2_mk_lambda c1 c2 f1 f2 Φ :
  wp2 (LAssum :: c1, LAssum :: c2) (f1, f2) (fun '(_, _) '(a1, a2) => Φ (c1, c2) (lam a1, lam a2)) ->
  wp2 (c1, c2) (mk_lambda f1, mk_lambda f2) Φ.
Proof.
intros H. unfold mk_lambda. apply wp2_with_decl_l, wp2_bind_l1.
apply wp2_with_decl_r, wp2_bind_r1. apply H.
Qed.

(*Ltac wp_step :=
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
  (at level 100, c1 binder, v binder, c2 binder).*)

(**************************************************************************)
(** *** CPS transformation meta-program. *)
(**************************************************************************)

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
  end
  end.

(** This lemma is trivial, but would be more tricky if [cps] could fail. *)
Lemma cps_same n ctx t k :
  wp2 (ctx, ctx) (cps n t k, cps n t k) (fun '(c, c') '(u, u') => u = u' /\ c = ctx /\ c' = ctx).
Proof.
induction n in ctx, t, k |- * ; cbn [cps] ; [apply wp2_out_of_fuel_l|].
destruct t.
- apply wp2_ret. auto.
- apply wp2_bind, wp2_mk_lambda, wp2_bind, wp2_mk_lambda, wp2_ret.
  eapply wp2_consequence ; [apply IHn|]. intros ? ? ? t2' (-> & -> & ->).
  eapply wp2_consequence ; [apply IHn|]. intros ? ? ? t1' (-> & -> & ->).
  auto.
- apply wp2_bind, wp2_mk_lambda, wp2_bind, wp2_mk_lambda.
  eapply wp2_consequence ; [apply IHn|]. intros ? ? ? t' (-> & -> & ->).
  apply wp2_ret. auto.
Qed.

(** [cps] commutes with renamings. *)
Lemma cps_rename_r {A} (m : M A) n c1 c2 t k r Φ :
  wp2 (c1, c2) (m, cps n t k) (fun '(c1', c2') '(a, t') => Φ (c1', c2') (a, rename r t')) ->
  wp2 (c1, c2) (m, cps n (rename r t) (rename r k)) Φ.
Proof.
intros H. induction n in c1, c2, m, r, t, k, H |- * ; cbn [cps] in * ; [apply wp2_out_of_fuel_r|].
destruct t.
- cbn in *. destruct (m c1) as [[] |] ; auto.
- cbn [rename]. apply wp2_bind_r1, wp2_mk_lambda_r, wp2_bind_r2, wp2_mk_lambda_r, wp2_ret.
  assert (rename (lift0 1) (rename r t2) = rename (rup r) (rename rshift t2)) as ->.
  { admit. }
  assert (lam (apps (var 1) [ var 0 ; rename (lift0 2) (rename r k)]) =
    rename (rup r) (lam (apps (var 1) [ var 0 ; rename (lift0 2) k]))) as ->.
  { cbn [rename apps]. f_equal. f_equal. unfold rup. admit. }
  eapply wp2_consequence ; [apply IHn|].
  +  admit.
  + intros c1' c2' ct2 ct2' Hct.
Admitted.

(** Reduction in the continuation. *)
Lemma cps_red_cont n ctx t k k' :
  k ~~>+ k' ->
  wp2 (ctx, ctx) (cps n t k, cps n t k') (fun _ '(u, u') => u ~~>+ u').
Proof.
intros Hk. induction n in t, k, k', Hk, ctx |- * ; cbn [cps] ; [apply wp2_out_of_fuel_l|].
destruct t.
- apply wp2_ret. apply red_plus_app_l ; [|reflexivity]. assumption.
- apply wp2_bind, wp2_mk_lambda, wp2_bind, wp2_mk_lambda, wp2_ret.
  eapply wp2_consequence ; [apply IHn|]. { now apply red_plus_lam, red_plus_app_r, red_plus_rename. }
  intros c1' c2' ct2 ct2' H2. cbn in H2.
  eapply wp2_consequence ; [apply IHn|]. { now apply red_plus_lam. }
  intros c1'' c2'' ct1 ct1' H1. cbn in H1. assumption.
- apply wp2_bind, wp2_mk_lambda, wp2_mk_lambda.
  eapply wp2_consequence ; [apply cps_same|]. *
  intros ? ? ? t' (-> & -> & ->). apply wp2_ret.
  now apply red_plus_app_l.
Qed.

(** Reduction in the term. *)
Lemma cps_red n ctx t t' k :
  t ~~>₁ t' ->
  wp2 (ctx, ctx) (cps n t k, cps n t' k) (fun _ '(u, u') => u ~~>+ u').
Proof.
intros Ht. induction n in t, t', k, Ht, ctx |- * ; [apply wp2_out_of_fuel_l|].
inversion Ht ; subst.
- unfold cps at 1 ; fold cps.
  apply wp2_bind_l1, wp2_mk_lambda_l, wp2_bind_l1, wp2_mk_lambda_l.
  fold cps.
  admit.
- cbn [cps]. apply wp2_bind, wp2_mk_lambda, wp2_bind, wp2_mk_lambda, wp2_ret.
  eapply wp2_consequence ; [apply cps_same|]. intros _ _ ? cu (-> & -> & ->).
  eapply wp2_consequence ; [apply IHn|]. { assumption. } intros c1' c2' ct ct'.
  cbn. auto.
- cbn [cps]. apply wp2_bind, wp2_mk_lambda, wp2_bind, wp2_mk_lambda, wp2_ret.
  eapply wp2_consequence ; [apply IHn|]. { now apply red1_rename. }
  intros c1' c2' cu cu' Hu. cbn  in Hu.
  apply cps_red_cont. now apply red_plus_lam.
- cbn [cps]. unfold fmap. apply wp2_bind, wp2_mk_lambda, wp2_mk_lambda.
  eapply wp2_consequence ; [apply IHn|]. { now apply red1_rename. }
  intros c1' c2' ct ct' Ht'. cbn in Ht'.
  apply wp2_ret. repeat f_equiv. exact Ht'.
Admitted.