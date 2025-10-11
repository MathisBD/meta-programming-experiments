From Stdlib Require Import Bool Nat Lia Classes.Morphisms.

(**************************************************************************)
(** *** Monadic programs. *)
(**************************************************************************)

Axiom context : Type.

Inductive M_ : Type -> Type :=
| Ret {A} : A -> M_ A
| Bind {A B} : M_ A -> (A -> M_ B) -> M_ B
| GetCtx : M_ context
| PutCtx : context -> M_ unit
| Fail {A} : M_ A
| OutOfFuel {A} : M_ A.

Definition M A :=
  nat -> M_ A.

Definition ret {A} (x : A) : M A :=
  fun _ => Ret x.

Definition bind {A B} (m : M A) (f : A -> M B) : M B :=
  fun n => Bind (m n) (fun x => f x n).

(** [let*] monadic notation. *)
Notation "'let*' x ':=' t 'in' u" := (bind t (fun x => u))
  (at level 100, right associativity, t at next level, x pattern).

Definition fmap {A B} (f : A -> B) (m : M A) : M B :=
  let* x := m in
  ret (f x).

Notation "f <$> x" := (fmap f x) (at level 30, right associativity).

Definition get_ctx : M context :=
  fun _ => GetCtx.

Definition put_ctx c : M unit :=
  fun _ => PutCtx c.

Definition fail {A} : M A :=
  fun _ => Fail.

Definition out_of_fuel {A} : M A :=
  fun _ => OutOfFuel.

(** Fixpoint combinator. *)
Fixpoint fix1 {A B} (F : (A -> M B) -> (A -> M B)) (x : A) (n : nat) : M_ B :=
  match n with
  | 0 => OutOfFuel
  | S n => F (fun x' _ => fix1 F x' n) x n
  end.

(** Example: factorial function. *)
Definition fact : nat -> M nat :=
  fix1 (fun fact k =>
    match k with
    | 0 => ret 1
    | S k => mult (S k) <$> fact k
    end).

(**************************************************************************)
(** *** Program semantics (as a monadic interpreter). *)
(**************************************************************************)

Inductive result A :=
| RSuccess (x : A)
| RFail
| ROutOfFuel.

Arguments RSuccess {A}.
Arguments RFail {A}.
Arguments ROutOfFuel {A}.

Fixpoint run_ {A} (m : M_ A) (c : context) : result (context * A) :=
  match m with
  | Ret x => RSuccess (c, x)
  | Bind m f =>
    match run_ m c with
    | RSuccess (c', x) => run_ (f x) c'
    | RFail => RFail
    | ROutOfFuel => ROutOfFuel
    end
  | GetCtx => RSuccess (c, c)
  | PutCtx c' => RSuccess (c', tt)
  | Fail => RFail
  | OutOfFuel => ROutOfFuel
  end.

(**************************************************************************)
(** *** (Partial) program logic. *)
(**************************************************************************)

Definition wp_result {A} (r : result (context * A)) (Φ : A -> context -> Prop) : Prop :=
  match r with
  | RSuccess (c, x) => Φ x c
  | RFail => False
  | ROutOfFuel => True
  end.

(** A weakest precondition which does not require termination. *)
Definition wp {A} (m : M A) (c : context) (Φ : A -> context -> Prop) : Prop :=
  forall n, wp_result (run_ (m n) c) Φ.

(** Hoare triples. *)
Definition hoare {A} (P : context -> Prop) (m : M A) (Q : A -> context -> Prop) :=
  forall c, P c -> wp m c Q.

Lemma wp_result_consequence {A} Φ Φ' (r : result (context * A)) :
  wp_result r Φ ->
  (forall x c, Φ x c -> Φ' x c) ->
  wp_result r Φ'.
Proof. intros H HΦ. destruct r as [[] | |] ; cbn in * ; auto. Qed.

Lemma wp_consequence {A} Φ Φ' (m : M A) c :
  wp m c Φ ->
  (forall x c, Φ x c -> Φ' x c) ->
  wp m c Φ'.
Proof.
intros H HΦ n. eapply wp_result_consequence.
- apply H.
- apply HΦ.
Qed.

Lemma wp_ret {A} (a : A) c Φ :
  Φ a c -> wp (ret a) c Φ.
Proof. intros H n. cbn. assumption. Qed.

(** The converse implication might not be true? *)
Lemma wp_bind {A B} (m : M A) (f : A -> M B) c Φ :
  wp m c (fun x c' => wp (f x) c' Φ) -> wp (bind m f) c Φ.
Proof.
intros H n. cbn. specialize (H n). unfold wp_result in *.
destruct (run_ (m n) c) as [[] | |] ; auto. apply H.
Qed.

Lemma wp_get_ctx c Φ :
  Φ c c -> wp get_ctx c Φ.
Proof. intros H n. cbn. assumption. Qed.

Lemma wp_put_ctx c c' Φ :
  Φ tt c' -> wp (put_ctx c') c Φ.
Proof. intros H n. cbn. assumption. Qed.

Lemma wp_out_of_fuel {A} c Φ :
  wp (@out_of_fuel A) c Φ.
Proof. intros n. cbn. constructor. Qed.

Lemma hoare_fix1 {A B} (F : (A -> M B) -> (A -> M B))
  (P : A -> context -> Prop) (Q : A -> B -> context -> Prop) :
  (forall f,
    (forall x, hoare (P x) (f x) (Q x)) ->
    (forall x, hoare (P x) (F f x) (Q x))) ->
  forall x, hoare (P x) (fix1 F x) (Q x).
Proof.
cbn. intros HF x c Hx n. induction n in c, x, Hx, HF, c, P, Q |- * ; cbn.
- constructor.
- apply HF ; [|exact Hx]. intros c' x' Hx' _. eapply IHn ; eassumption.
Qed.

(** Example: proving a simple property of factorial. *)
Lemma fact_pos :
  forall k, hoare (fun _ => True) (fact k) (fun res _ => max 1 k <= res).
Proof.
apply hoare_fix1 with (P := fun _ _ => True) (Q := fun k res _ => max 1 k <= res).
intros f Hf k c _. destruct k.
- apply wp_ret. lia.
- apply wp_bind. eapply wp_consequence ; [now apply Hf|].
  intros k' c'' Hk'. cbn beta in Hk'. apply wp_ret.
  assert (1 <= k') by lia. lia.
Qed.

(**************************************************************************)
(** *** Monotonicity. *)
(**************************************************************************)

(** Partial order relation on [result A]. *)
Inductive lessdefR {A} : result A -> result A -> Prop :=
| lessdefR_oof x : lessdefR ROutOfFuel x
| lessdefR_fail : lessdefR RFail RFail
| lessdefR_suc a : lessdefR (RSuccess a) (RSuccess a).

#[export] Instance lessdefR_preorder A : PreOrder (@lessdefR A).
Proof.
constructor.
- intros [] ; constructor.
- intros r1 r2 r3 H1 H2. destruct r1.
  + destruct r2 ; inversion H1 ; subst. assumption.
  + destruct r2 ; inversion H1 ; subst. assumption.
  + constructor.
Qed.

(** Partial order relation on [M_ A]. *)
Definition lessdef_ {A} (m m' : M_ A) :=
  forall c, lessdefR (run_ m c) (run_ m' c).

#[export] Instance lessdef__preorder A : PreOrder (@lessdef_ A).
Proof.
constructor.
- intros m c. reflexivity.
- intros m1 m2 m3 H1 H2 c. etransitivity ; eauto.
Qed.

(** Partial order relation on [M A]. *)
Definition lessdef {A} (m m' : M A) := forall n, lessdef_ (m n) (m' n).
Notation "m ⊑ m'" := (lessdef m m') (at level 50, no associativity).

Definition lessdef1 {A B} (f f' : A -> M B) := forall x, lessdef (f x) (f' x).
Notation "f ⊑₁ g" := (lessdef1 f g) (at level 50, no associativity).

#[export] Instance lessdef_preorder A : PreOrder (@lessdef A).
Proof.
constructor.
- intros m n. reflexivity.
- intros m1 m2 m3 H1 H2 n. etransitivity ; eauto.
Qed.

(** Monotonicity. *)
Definition mono {A} (m : M A) :=
  forall n n', n <= n' -> lessdef_ (m n) (m n').

Definition mono1 {A B} (f : A -> M B) :=
  forall x, mono (f x).

(** Proving monotonicity. *)

Lemma ret_mono {A} (a : A) :
  mono (ret a).
Proof. intros n n' Hn c. cbn. constructor. Qed.

Lemma bind_mono {A B} (m : M A) (f : A -> M B) :
  mono m -> mono1 f -> mono (bind m f).
Proof.
intros Hm Hf n n' Hn c. cbn. specialize (Hm n n' Hn c).
destruct (run_ (m n) c) as [[] | |] ; destruct (run_ (m n') c) as [[] | |].
all: try solve [ constructor | now inversion Hm ].
inversion Hm ; subst. now apply Hf.
Qed.

Lemma fmap_mono {A B} (f : A -> B) (m : M A) :
  mono m -> mono (f <$> m).
Proof.
intros H. unfold fmap. apply bind_mono.
- assumption.
- intros x. apply ret_mono.
Qed.

Lemma get_ctx_mono : mono get_ctx.
Proof. intros n n' Hn c. cbn. constructor. Qed.

Lemma put_ctx_mono c : mono (put_ctx c).
Proof. intros n n' Hn c'. cbn. constructor. Qed.

Lemma fail_mono A : mono (@fail A).
Proof. intros n n' Hn c. cbn. constructor. Qed.

Lemma out_of_fuel_mono A : mono (@out_of_fuel A).
Proof. intros n n' Hn c. cbn. constructor. Qed.

Lemma fix1_mono {A B} (F : (A -> M B) -> (A -> M B)) :
  (forall f, mono1 f -> mono1 (F f)) ->
  (forall f g : A -> M B, f ⊑₁ g -> F f ⊑₁ F g) ->
  mono1 (fix1 F).
Proof.
intros H1 H2 x n n' Hn. induction n in x, n', Hn |- * ; cbn.
- constructor.
- destruct n' ; cbn ; [lia|]. transitivity (F (fun x' _ => fix1 F x' n') x n).
  + apply H2. intros y _. apply IHn. lia.
  + apply H1.
    * intros y _ _ _. reflexivity.
    * lia.
Qed.

Lemma bind_lessdef {A B} :
  Proper (lessdef ==> lessdef1 ==> lessdef) (@bind A B).
Proof.
intros m m' Hm f f' Hf n c. cbn. specialize (Hm n c).
destruct (run_ (m n) c) as [[] | |] ; destruct (run_ (m' n) c) as [[] | |].
all: try solve [ constructor | now inversion Hm ].
inversion Hm ; subst. apply Hf.
Qed.

Lemma fmap_lessdef {A B} (f : A -> B) :
  Proper (lessdef ==> lessdef) (fmap f).
Proof.
intros m m' Hm. unfold fmap. apply bind_lessdef.
- assumption.
- intros x. reflexivity.
Qed.

(** Prove goals of the form [mono _] or [_ ⊑ _]. *)
Ltac prove_mono :=
  match goal with
  (* Introduce variables. *)
  | [ |- mono1 _ ] => intro ; prove_mono
  | [ |- _ ⊑₁ _ ] => intro ; prove_mono
  (* [lessdef] rules. *)
  | [ |- ?x ⊑ ?x] => reflexivity
  | [ |- bind _ _ ⊑ bind _ _ ] => apply bind_lessdef ; [prove_mono | prove_mono]
  | [ |- fmap _ _ ⊑ fmap _ _ ] => apply fmap_lessdef ; [prove_mono]
  (* Monotonicity rules. *)
  | [ |- mono (ret _) ] => apply ret_mono
  | [ |- mono (bind _ _) ] => apply bind_mono ; [prove_mono | prove_mono]
  | [ |- mono (fmap _ _) ] => apply fmap_mono ; [prove_mono]
  | [ |- mono (fix1 _ _) ] =>
      apply fix1_mono ; [intro ; intro ; prove_mono | intro ; intro ; intro ; prove_mono]
  (* Try to use assumptions. *)
  | [ H : mono _ |- mono _ ] => exact H
  | [ H : mono1 _ |- mono _ ] => apply H
  | [ H : _ ⊑ _ |- _ ⊑ _ ] => exact H
  | [ H : _ ⊑₁ _ |- _ ⊑ _ ] => apply H
  (* Break up case expressions. *)
  | [ |- mono (match ?x with _ => _ end) ] => destruct x ; prove_mono
  | [ |- (match ?x with _ => _ end) ⊑ (match ?x with _ => _ end) ] =>
      destruct x ; prove_mono
  (* Otherwise give up. *)
  | _ => idtac
  end.

(** Example: fact is monotone. *)
Lemma fact_mono :
  mono1 fact.
Proof. unfold fact. prove_mono. Qed.

(**************************************************************************)
(** *** Termination. *)
(**************************************************************************)

Definition is_out_of_fuel {A} (m : M_ A) : Prop :=
  match m with
  | OutOfFuel => True
  | _ => False
  end.

Definition terminates {A} (m : M A) :=
  exists n, ~is_out_of_fuel (m n).

Definition diverges {A} (m : M A) :=
  forall n, is_out_of_fuel (m n).

Lemma ret_terminates {A} (a : A) :
  terminates (ret a).
Proof. exists 0. cbn. auto. Qed.

Lemma bind_terminates {A B} (m : M A) (f : A -> M B) :
  terminates (bind m f).
Proof.
intros [n Hm] Hf. eexists. cbn.