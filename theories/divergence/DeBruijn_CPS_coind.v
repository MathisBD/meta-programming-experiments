From Coinduction Require Import all.
From Stdlib Require Import Bool Nat List Lia.
From Stdlib.Classes Require Import Morphisms.
Import ListNotations.

Set Primitive Projections.

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

(** Size of a term. *)
Fixpoint term_size (t : term) : nat :=
  match t with
  | var _ => 0
  | app t1 t2 => S (term_size t1 + term_size t2)
  | lam t => S (term_size t)
  end.

(** Well-founded inductions on terms using their size. *)
Lemma term_size_ind (P : term -> Prop)
  (IH : forall t, (forall t', term_size t' < term_size t -> P t') -> P t) :
  forall t, P t.
Proof.
intros t.
induction (Wf_nat.well_founded_ltof term term_size t) as [t IHt Ht].
unfold Wf_nat.ltof in *. apply IH. apply Ht.
Qed.

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

(** Renaming a term doesn't change its size. *)
Lemma size_rename r t :
  term_size (rename r t) = term_size t.
Proof.
induction t in r |- * ; cbn.
- reflexivity.
- rewrite IHt1, IHt2 ; lia.
- rewrite IHt ; lia.
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
  le n n' -> scoping n t -> scoping n' t.
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
(** *** Events. *)
(**************************************************************************)

Notation "F '~>' G" := (forall A, F A -> G A)
  (at level 99, right associativity, only parsing) : type_scope.

(** Events. *)

Variant failE : Type -> Type :=
| Fail {A} : failE A.

Variant ctxE : Type -> Type :=
| GetCtx : ctxE context
| PutCtx : context -> ctxE unit.

(** Sum of events. *)

Variant sumE (E F : Type -> Type) : Type -> Type :=
| sumE_left A : E A -> sumE E F A
| sumE_right A : F A -> sumE E F A.

Arguments sumE_left {E F A}.
Arguments sumE_right {E F A}.

Notation "E '+'' F" := (sumE E F) (at level 30, right associativity).

(** Automatic injection of events. *)

Class inject (E F : Type -> Type) : Type := {
  inj {A} : E A -> F A
}.

Notation "E '>->' F" := (inject E F) (at level 40, no associativity).

#[export] Instance inject_same E : inject E E := {
  inj {A} (e : E A) := e
}.

#[export] Instance inject_left E F1 F2 : inject E F1 -> inject E (F1 +' F2) := {
  inj {A} (e : E A) := sumE_left (inj e)
}.

#[export] Instance inject_right E F1 F2 : inject E F2 -> inject E (F1 +' F2) := {
  inj {A} (e : E A) := sumE_right (inj e)
}.

(**************************************************************************)
(** *** Interaction trees. *)
(**************************************************************************)

Variant itreeF (itree : (Type -> Type) -> Type -> Type) (E : Type -> Type) (A : Type) : Type :=
| RetF (x : A)
| TauF (m : itree E A)
| VisF {B} (e : E B) (k : B -> itree E A).

Arguments RetF {itree E A}.
Arguments TauF {itree E A}.
Arguments VisF {itree E A B}.

CoInductive itree (E : Type -> Type) (A : Type) : Type := go
{ observe : itreeF itree E A }.

Arguments go {E A}.
Arguments observe {E A}.

(*Section WeakBisimulation.
  Context {E : Type -> Type} {A : Type}.

  Inductive bisimF (R : itree E A -> itree E A -> Prop) : itree E A -> itree E A -> Prop :=
  (** Congruence rules. *)
  | bisim_ret x : bisimF R (Ret x) (Ret x)
  | bisim_tau m m' : R m m' -> bisimF R (Tau m) (Tau m')
  | bisim_vis {B} (e : E B) k k' :
      (forall x, R (k x) (k' x)) -> bisimF R (Vis e k) (Vis e k')
  (** Strip off a single [Tau] on either side. *)
  | bisim_tau_l m m' : bisimF R m m' -> bisimF R (Tau m) m'
  | bisim_tau_r m m' : bisimF R m m' -> bisimF R m (Tau m').

  Lemma bisimF_mono : Proper (leq ==> leq) bisimF.
  Proof.
  intros R R' HR m m' Hm. induction Hm ; constructor ; auto.
  - now apply HR.
  - intros x. now apply HR.
  Qed.

  Definition bisim_mon : mon (itree E A -> itree E A -> Prop) :=
    {| body := bisimF ; Hbody := bisimF_mono |}.

End WeakBisimulation.

(** Weak bisimulation (equality on itrees). *)
Infix "~" := (gfp bisim_mon) (at level 70).
(* Intuitively, the pairs in our coinduction candidate *)
Infix "[~]" := (elem _) (at level 70).
(* Intuitively, the pairs that will be unlocked after a step *)
Infix "{~}" := (bisim_mon (elem _)) (at level 70).*)

Definition Ret {E A} (x : A) : itree E A := go (RetF x).
Definition Tau {E A} (m : itree E A) : itree E A := go (TauF m).
Definition Vis {E A B} (e : E B) (k : B -> itree E A) : itree E A := go (VisF e k).


Definition bind {E A B} (m : itree E A) (f : A -> itree E B) : itree E B :=
  (cofix bind_ m' :=
    match observe m' with
    | RetF x => f x
    | TauF m' => Tau (bind_ m')
    | VisF e k => Vis e (fun x => bind_ (k x))
    end) m.

(*Lemma bind_bisim {E A B} :
  Proper (gfp bisim_mon ==> pointwise_relation A (gfp bisim_mon) ==> gfp bisim_mon) (@bind E A B).
Proof.
intros m m' Hm f f' Hf. unfold pointwise_relation in Hf. coinduction R CIH.
cbn.*)

Notation "x >>= f" := (bind x f) (at level 50, no associativity).
Notation "f =<< x" := (bind x f) (at level 50, no associativity).

(** [let*] monadic notation. *)
Notation "'let*' x ':=' t 'in' u" := (bind t (fun x => u))
  (at level 100, right associativity, t at next level, x pattern).

Definition fmap {E A B} (f : A -> B) (mx : itree E A) : itree E B :=
  let* x := mx in
  Ret (f x).

Notation "f <$> x" := (fmap f x) (at level 30, right associativity).

Definition trigger {E F} `{E >-> F} : E ~> itree F :=
  fun A e => Vis (inj e) Ret.

Arguments trigger {E F} {_} {A} e.

(** (mutual) fixpoint combinator. *)
Definition mrec {recE E} (handle_recE : recE ~> itree (recE +' E)) : recE ~> itree E :=
  fun A e =>
    (cofix loop {A} (m : itree (recE +' E) A) : itree E A :=
      match observe m with
      | RetF x => Ret x
      | TauF m => Tau (loop m)
      | VisF (sumE_left e) k =>
        Tau (loop (bind (handle_recE _ e) k))
      | VisF (sumE_right e) k =>
        Tau (let* x := trigger e in loop (k x))
      end) _ (handle_recE _ e).

Arguments mrec {recE E} handle_recE {A} e.

(** Fail. *)
Definition fail {E A} `{failE >-> E} : itree E A :=
  trigger Fail.

(** Read the local context. *)
Definition get_ctx {E} `{ctxE >-> E} : itree E context :=
  trigger GetCtx.

(** Replace the local context. *)
Definition put_ctx {E} `{ctxE >-> E} (ctx : context) : itree E unit :=
  trigger (PutCtx ctx).

(** Extend the local context with a new local declaration,
    run a computation, and restore the local context. *)
Definition with_decl {E A} `{ctxE >-> E} (d : ldecl) (m : itree E A) : itree E A :=
  let* ctx := get_ctx in
  let* _ := put_ctx (d :: ctx) in
  let* a := m in
  let* _ := put_ctx ctx in
  Ret a.

(** Convenience function to build a lambda abstraction. *)
Definition mk_lambda {E} `{ctxE >-> E} (f : itree E term) : itree E term :=
  with_decl LAssum
    (let* body := f in
     Ret (lam body)).

(**************************************************************************)
(** *** Semantics of monadic computations. *)
(**************************************************************************)

(*Reserved Notation "'(' c1 ',' m1 ')' '~>' '(' c2 ',' m2 ')'"
  (at level 0, no associativity).

(** Coinductive small-step reduction relation. *)
CoInductive step {A} : context * M A -> context * M A -> Prop :=
| step_ret c x :
    (c, Ret x) ~> (c, Ret x)
| step_tau c m :
    (c, Tau m) ~> (c, m)
| step_get_ctx c k :
    (c, Vis GetCtx k) ~> (c, k c)
| step_put_ctx c1 c2 k :
    (c1, Vis (PutCtx c2) k) ~> (c2, k tt)
where "'(' c1 ',' m1 ')' '~>' '(' c2 ',' m2 ')'" := (step (c1, m1) (c2, m2)).*)

(**************************************************************************)
(** *** Termination. *)
(**************************************************************************)

(*Inductive terminates {A} : context -> M A -> Prop :=
| terminates_ret c x :
    terminates c (Ret x)
| terminates_tau c m :
    terminates c m -> terminates c (Tau m)
| terminates_error {B} c (k : B -> M A) :
    terminates c (Vis Error k)
| terminates_get_ctx c k :
    terminates c (k c) -> terminates c (Vis GetCtx k)
| terminates_put_ctx c1 c2 k :
    terminates c2 (k tt) -> terminates c1 (Vis (PutCtx c2) k).*)

(**************************************************************************)
(** *** Program logic. *)
(**************************************************************************)

(*(** Weakest-precondition: [wp ctx m Q] means that running [m] in initial
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
  (at level 100, c1 binder, v binder, c2 binder).*)

(**************************************************************************)
(** *** CPS transformation meta-program. *)
(**************************************************************************)

Variant cpsE : Type -> Type :=
| CPS : term -> term -> cpsE term.

(** Handle a single [cpsE] event. Recursive calls are added as new events. *)
Definition handle_cpsE {E} `{ctxE >-> E} : cpsE ~> itree (cpsE +' E) :=
  fun _ e =>
  match e with
  | CPS (var i) k => Ret (app k (var i))
  | CPS (app t1 t2) k =>
    let* k2 :=
      mk_lambda ( (* x2 *)
      Ret (apps (var 1 (* x1 *)) [ var 0 (* x2 *) ; rename (lift0 2) k ]))
    in
    let* k1 :=
      mk_lambda ( (* x1 *)
      trigger (CPS (rename (lift0 1) t2) k2))
    in
    trigger (CPS t1 k1)
  | CPS (lam t') k =>
    app k <$>
      mk_lambda ( (* x *)
      mk_lambda ( (* k' *)
      trigger (CPS (rename (lift0 1) t') (var 0 (* k' *)))))
  end.

(** Tie the knot. *)
Definition cps {E} `{ctxE >-> E} (t k : term) : itree E term :=
  mrec handle_cpsE (CPS t k).

Lemma cps_var i k : observe (cps (var i) k) = RetF (app k (var i)).
Proof. cbn. reflexivity. Qed.

(** Termination, specialized to [ctxE] events. *)
Inductive terminates {A} : context -> itreeF itree ctxE A -> Prop :=
| terminates_ret c x :
    terminates c (RetF x)
| terminates_tau c m :
    terminates c (observe m) -> terminates c (TauF m)
| terminates_get_ctx c k :
    terminates c (observe (k c)) -> terminates c (VisF GetCtx k)
| terminates_put_ctx c1 c2 k :
    terminates c2 (observe (k tt)) -> terminates c1 (VisF (PutCtx c2) k).

Lemma cps_terminates c t k : terminates c (observe (cps t k)).
Proof.
induction t in c, k |- * using term_size_ind. destruct t.
- cbn. apply terminates_ret.
- cbn.
  repeat first [ cbn ; apply terminates_tau
               | cbn ; apply terminates_get_ctx
               | cbn ; apply terminates_put_ctx].
  cbn.
  apply terminates_tau ; cbn.
  apply terminates_get_ctx ; cbn.
  apply terminates_tau ; cbn.
  apply terminates_put_ctx ; cbn.
  apply terminates_tau ; cbn.
  apply terminates_put_ctx ; cbn.
  apply terminates_tau ; cbn.
  apply terminates_get_ctx ; cbn.
  apply terminates_tau ; cbn.


(*Lemma cps_safe n t k :
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
Qed.*)