From Stdlib Require Import Bool Nat Lia Classes.Morphisms.

(** The monad. *)

Inductive result A :=
| OutOfFuel : result A
| Success : A -> result A.
Arguments OutOfFuel {A}.
Arguments Success {A}.

Definition M A :=
  nat -> result A.

Definition ret {A} (x : A) : M A :=
  fun fuel => Success x.

Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun fuel =>
    match x fuel with
    | OutOfFuel => OutOfFuel
    | Success x' => f x' fuel
    end.

Fixpoint fixpoint {A B} (F : (A -> M B) -> (A -> M B)) (x : A) (n : nat) : result B :=
  match n with
  | 0 => OutOfFuel
  | S n => F (fun x' _ => fixpoint F x' n) x n
  end.

(** Example: factorial, but _not_ by recursion on its argument! *)

Definition fact : nat -> M nat :=
  fixpoint (fun fact' k =>
    match k with
    | 0 => ret 1
    | S k =>
      (* The syntax is a bit heavy here but could easily be improved. *)
      bind (fact' k) (fun tmp => ret (S k * tmp))
    end).

(** Reasoning about non-terminating programs (without proving termination) is easy. *)

(** A weakest precondition which does not require termination. *)
Definition wp {A} (m : M A) (Q : A -> Prop) : Prop :=
  forall n, match m n with OutOfFuel => True | Success x => Q x end.

Lemma wp_ret {A} (x : A) Φ :
  Φ x -> wp (ret x) Φ.
Proof. intros H. intros n. cbn. assumption. Qed.

Lemma wp_bind {A B} (m : M A) (f : A -> M B) Φ :
  wp m (fun x => wp (f x) Φ) -> wp (bind m f) Φ.
Proof.
intros H. unfold wp in *. intros n. unfold bind. specialize (H n). destruct (m n).
- constructor.
- apply H.
Qed.

(** Hoare triples, with the consequence rule built-in. *)
Definition hoare {A} (P : Prop) (m : M A) (Q : A -> Prop) :=
  forall Q', (forall x, Q x -> Q' x) -> P -> wp m Q'.

Notation "'{{' P '}}' m '{{' v '.' Q '}}'" :=
  (hoare P m (fun v => Q))
  (at level 100, v binder).

(** Hoare specification for fixpoints. There is surely a more consice
    specification to be given (e.g. using weakest preconditions instead
    of Hoare triples), but this is already usable (see example below). *)
Lemma hoare_fixpoint {A B} (F : (A -> M B) -> (A -> M B)) P Q :
  (forall f : A -> M B,
    (forall x, {{ P x }} f x {{ y. Q x y }}) ->
    (forall x, {{ P x }} F f x {{ y. Q x y }})) ->
  forall x, {{ P x }} fixpoint F x {{ y. Q x y }}.
Proof.
intros H x Φ HΦ Hx n. induction n in x, Hx, Φ, HΦ |- * ; cbn.
- constructor.
- apply H.
  + intros y Φ' HΦ' Hy. intros _. apply IHn ; assumption.
  + assumption.
  + assumption.
Qed.

(** Example: proving a simple property of factorial. *)

Lemma fact_pos :
  forall k, {{ True }} fact k {{ res. max 1 k <= res }}.
Proof.
apply hoare_fixpoint with (P := fun _ => True).
intros f Hf k Φ HΦ _. destruct k.
- apply wp_ret. apply HΦ. lia.
- apply wp_bind. apply Hf ; [|constructor].
  intros k' Hk'. apply wp_ret. apply HΦ.
  assert (1 <= k') by lia. lia.
Qed.

(** Monotonicity. *)

Reserved Notation "x ⊑ y" (at level 50, no associativity).

(** Partial order relation on [result A]. *)
Inductive le_result {A} : result A -> result A -> Prop :=
| le_result_oof x : OutOfFuel ⊑ x
| le_result_suc a : Success a ⊑ Success a
where "x ⊑ y" := (le_result x y).

Notation "f ⊑₁ g" := (forall x, f x ⊑ g x) (at level 50, no associativity).
Notation "f ⊑₂ g" := (forall x y, f x y ⊑ g x y) (at level 50, no associativity).

Instance le_result_refl {A} : Reflexive (@le_result A).
Proof. intros x. destruct x ; constructor. Qed.

Instance le_result_trans {A} : Transitive (@le_result A).
Proof.
intros x y z H H'. destruct x.
- constructor.
- destruct y ; inversion H ; subst. assumption.
Qed.

Definition mono {A} (m : M A) :=
  forall n n', n <= n' -> m n ⊑ m n'.

Definition mono1 {A B} (f : A -> M B) :=
  forall x, mono (f x).

Lemma ret_mono {A} : mono1 (@ret A).
Proof. intros x n n' Hn. reflexivity. Qed.

Lemma bind_mono {A B} (m : M A) (f : A -> M B) :
  mono m ->
  mono1 f ->
  mono (bind m f).
Proof.
intros Hm Hf n n' Hn. unfold bind. specialize (Hm n n' Hn). inversion Hm.
- constructor.
- apply Hf ; auto.
Qed.

Lemma fixpoint_mono {A B} (F : (A -> M B) -> (A -> M B)) :
  (forall f, mono1 f -> mono1 (F f)) ->
  (forall f g, f ⊑₂ g -> F f ⊑₂ F g) ->
  mono1 (fixpoint F).
Proof.
intros H1 H2 x n n' Hn. induction n in x, n', Hn |- * ; cbn ; [constructor|].
destruct n' ; cbn ; [lia|]. apply le_S_n in Hn.
transitivity (F (fun x' _ => fixpoint F x' n') x n).
- apply H2. intros y _. now apply IHn.
- apply H1.
  + intros y _ _ _. reflexivity.
  + assumption.
Qed.

Lemma bind_proper {A B} :
  forall m m' : M A, m ⊑₁ m' ->
  forall f f' : A -> M B, f ⊑₂ f' ->
  bind m f ⊑₁ bind m' f'.
Proof.
intros m m' Hm f f' Hf n. specialize (Hm n). unfold bind.
inversion Hm ; subst ; [constructor|]. apply Hf.
Qed.

(** Back to the factorial example. *)

Lemma fact_mono : mono1 fact.
Proof.
unfold fact. apply fixpoint_mono.
- intros f Hf [|k].
  + apply ret_mono.
  + apply bind_mono.
    * apply Hf.
    * intros tmp. apply ret_mono.
- intros f g Hfg k. destruct k.
  + reflexivity.
  + apply bind_proper.
    * apply Hfg.
    * reflexivity.
Qed.