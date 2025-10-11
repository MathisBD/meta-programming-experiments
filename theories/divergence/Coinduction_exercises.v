From Stdlib Require Import Setoid Morphisms Lia List Nat Psatz.
From Coinduction Require Import all.

Import CoindNotations.
Set Primitive Projections.
Set Implicit Arguments.

Module stream.

(*|
18. Streams With [coq-coinduction]: Setup
|*)

(*|
Installation:
- < 9.0: `opam install coq-coinduction`
- >= 9.0: `opam install rocq-coinduction`
-> You may have to run
`opam repo add rocq-released https://rocq-prover.org/opam/released`
|*)

CoInductive stream := cons { hd: nat; tl: stream }.
Declare Scope stream_scope.
Bind Scope stream_scope with stream.
Open Scope stream_scope.
Infix ":::" := cons (at level 60, right associativity): stream_scope.

(* We define our monotone function as before---the library provides
   a class of complete lattices, and suitable instances for
   (possibly dependent) relations of arbitrary arities.
 *)
Program Definition bisimF : mon (stream -> stream -> Prop) :=
  {| body R s t := hd s = hd t /\ R (tl s) (tl t) |}.
Next Obligation. firstorder. Qed.

(* We use [gfp] to define the greatest fixpoint of b.
   /!\: It has to be a notation, or we will need to unfold
   the definition for the tactics to work.
 *)
Infix "~" := (gfp bisimF) (at level 70).
Check (gfp_fp bisimF).
Check (leq_gfp bisimF).

(*|
19. Streams: basic operations
|*)

CoFixpoint zeros: stream  := 0 ::: zeros.
CoFixpoint zeros': stream := 0 ::: 0 ::: zeros'.
CoFixpoint from n: stream := n ::: from (S n).
Definition nats           := from 0.
CoFixpoint zip s t        := hd s ::: hd t ::: zip (tl s) (tl t).
CoFixpoint even s         := hd s ::: even (tl (tl s)).
Definition odd s          := even (tl s).
CoFixpoint pls s t        := hd s + hd t ::: pls (tl s) (tl t).
Infix "+"                 := pls: stream_scope.

(*|
20. First Proofs with the [coinduction] Tactic
|*)

Goal zeros + zeros ~ zeros.
  coinduction R CIH.
  constructor.
  - cbn. reflexivity.
  - cbn. exact CIH.
Qed.
(*
  coinduction R CIH.
  constructor.
  - reflexivity.
  - apply CIH.

  Restart.
  now coinduction R CIH.
Qed.*)

(* Intuitively, the pairs in our coinduction candidate *)
Infix "[~]" := (`_) (at level 70).
(* Intuitively, the pairs that will be unlocked after a step *)
Infix "{~}" := (bisimF `_) (at level 70).

(* Go blind, restart, generalize. Draw on board the situation *)
Lemma pls0x s: zeros + s ~ s.
(*  coinduction R CIH.
  split.
  - reflexivity.
  - cbn.
    (* stuck *)*)

  revert s. coinduction R CIH ; intros s.
  split.
  - reflexivity.
  - cbn. apply CIH.
Qed.

(*|
Exercises 1. Proofs by (vanilla) coinduction
|*)

Lemma plsC: forall x y, x + y ~ y + x.
Proof.
coinduction R CIH ; intros x y. split ; cbn.
- lia.
- apply CIH.
Qed.

Lemma plsA: forall x y z, x + (y + z) ~ (x + y) + z.
Proof.
coinduction R CIH ; intros x y z. split ; cbn.
- lia.
- apply CIH.
Qed.

Lemma even_nats: even nats ~ nats + nats.
Proof.
enough (forall i, even (from (2 * i)) ~ from i + from i).
{ apply (H 0). }
coinduction R CIH ; intros i. split ; cbn.
- lia.
- specialize (CIH (S i)%nat).
  assert (2 * S i = S (S (i + (i + 0)))) as <- by lia.
  exact CIH.
Qed.

(*|
21. The Need for Enhanced Coinduction
|*)

Lemma bisim_refl s : s ~ s.
Proof.
revert s. coinduction R IH ; intros s. split.
- reflexivity.
- apply IH.
Qed.

Lemma unfold_stream s: s ~ hd s ::: tl s.
Proof.
(*  coinduction R CIH.
  split; cbn.
  - reflexivity.
  - Fail apply bisim_refl. Restart.*)
  (* Indeed, our candidate is _not_ a bisimulation. So we can strengthen it *)
  enough (s ~ hd s ::: tl s /\ forall s, s ~ s).
  { apply H. }
  coinduction R CIH.
  split.
  - now split.
  - split ; [reflexivity | apply CIH].
  (* But surely, there must be a better way? *)
Qed.

(*|
22. Enhanced Coinduction
|*)

(*|
Coinduction principle: "any postfixpoint of [b] is below the greatest fixpoint of [b]".

x <= y     y <= b y

-------------------

   x <= gfp b


In the previous example, y = {s , hd s ::: tl s} was not a postfixpoint, we had to enlarge it.
But perhaps we didn't have to?
|*)

(*|
Let [f : X -> X] a monotone function.
The f-enhanced coinduction principle: "any postfixpoint of [b ° f] is below the greatest fixpoint of [b]".

x <= y     y <= b (f y)

-------------------

   x <= gfp b

Of course this is completely unsound in general! Finding classes of valid [f] given a [b] has been a field of research in its own right.

In the example above, we wanted to "conclude by reflexivity". That amounts to consider the up-to function [f R = R ∪ Id]. And indeed, it is sound w.r.t. bisimulation: we will prove it in a different setup a little later.

|*)

(*|
Note: Beware, something can be valid of the [gfp], but not be a valid up-to.
Famously, weak bisimilarity is transitive, but weak bisimulation up-to weak bisimilarity is not valid.
|*)

(*|
23. Enhanced Coinduction: the Companion
|*)

(*|
Examples:
- Up-to reflexivity, symmetry, transitivity
- Up-to another relation: weak bisimulation up-to strong bisimilarity, ...
- Up-to context: for ccs, ...
|*)
(*|
Historically: (prove sound and) pick the right up-to for the right proof
|*)
(*|
Idea: Identify classes of sound principles that are closed under composition, etc..

Definition : [f] is _(b)-compatible_ if [f ° b <= b ° f].
Theorem    : if [f] compatible, then [f] is sound
Theorem    : the set of b-compatible functions forms a complete lattice.
|*)
(*|
The [companion] [t] of [b] is the greatest b-compatible function.

We have [gfp b == t ⊥].
We can always perform coinduction up-to [t], and access on the fly any function we prove to be below it!
|*)

(*|
24. Enhanced Coinduction: Tower Induction
|*)

(*|
Idea: there is a nicer, inductive, construction of the companion.

We jump to [tower.v]
|*)

(*|
25. Let's enhance!
|*)

Goal zeros + zeros ~ zeros.
  (*coinduction R cih.
  Undo.*)
  apply gfp_prop.
  intro R.
  apply tower.
  repeat intro; firstorder.
(*  Restart.*)
Abort.

Instance Reflexive_t {R : Chain bisimF} : Reflexive `R.
Proof.
  (*revert R.
  apply tower.
  - cbv. firstorder.
  - intros R HR x.
    split.
    + reflexivity.
    + reflexivity.
  (* Note: being [inf closed] does not depend on [b]! *)
  Restart.*)
  revert R.
  apply Reflexive_chain. intros R HR x. now split.
Qed.

Lemma unfold_stream'' s : s ~ hd s ::: tl s.
Proof.
  coinduction R cih.
  Show Proof.
  split.
  - reflexivity.
  - reflexivity.
  (* Note: we never used our coinduction hypothesis! *)
Qed.

Lemma unfold_stream''' s : s ~ hd s ::: tl s.
Proof.
  (* "up-to b" is always a valid principle.
     It is captured in the tactic [step]:
   *)
  step.
  split; reflexivity.
Qed.

(*|
Exercises 2.
|*)

Goal zeros ~ zeros'.
coinduction R CIH. split ; cbn.
- reflexivity.
- step. now split.
Qed.

Goal forall s, zip (even s) (odd s) ~ s.
coinduction R CIH ; intros s. split ; cbn.
- reflexivity.
- step. now split.
Qed.

Lemma plusC: forall x y, x + y ~ y + x.
Proof.
coinduction R CIH ; intros x y. split ; cbn ; [lia|]. apply CIH.
Qed.

Lemma plus_0x x: zeros + x ~ x.
Proof.
revert x. coinduction R CIH ; intros x. split ; now cbn.
Qed.

Lemma plusA: forall x y z, x + (y + z) ~ (x + y) + z.
Proof.
coinduction R CIH ; intros x y z. split ; cbn.
- lia.
- apply CIH.
Qed.

(*|
26. Let's enhance some more!
|*)

(*|
Elements of the chain are not just reflexive, they are equivalence relations!
|*)
Instance Equivalence_t {R : Chain bisimF} : Equivalence `R.
Proof.
  constructor; revert R.
  - apply @Reflexive_t.
  - apply Symmetric_chain. intros R HR x y []. now split; symmetry.
  - apply Transitive_chain. intros R HR x y z [] []. split. congruence. etransitivity; eauto.
Qed.

Lemma Equivalence_bisim : Equivalence (gfp bisimF).
Proof. apply gfp_prop. intros R. apply Equivalence_t. Qed.

(*|
27. Shuffle Product: definition
|*)

(*|
This is the following binary operation on streams [s,t]:
    [(s @ t)_k = Σ_{i+j=k} (i k) s_i t_j]
    it can be characterised by the following equations:
    [hd (s @ t) = hd s * hd t]
    [tl (s @ t) = tl s @ t  +  s @ tl t]
|*)

(* It's definition itself is a major challenge! *)
Fail CoFixpoint shuf s t :=
  (hd s * hd t) ::: (shuf (tl s) t + shuf s (tl t)).

(** Here we simply assume its existence for the sake of simplicity.
    For the curious: file [shuffle.v]
 *)
Parameter shuf: stream -> stream -> stream.
Infix "@" := shuf (at level 40, left associativity).
Axiom hd_shuf: forall s t, hd (s @ t) = (hd s * hd t)%nat.
Axiom tl_shuf: forall s t, tl (s @ t) = tl s @ t + s @ tl t.
Ltac cbn_shuf := repeat (rewrite ?hd_shuf, ?tl_shuf; simpl hd; simpl tl).

(*|
28. Up-to [pls] Context
|*)

Lemma shuf_0x: forall x, zeros @ x ~ zeros.
Proof.
  coinduction R HR. intros x. split; cbn_shuf.
  - nia.
  - Fail rewrite HR.
Abort.

(** addition context corresponds to a valid compatible function *)
Instance pls_chain_proper : forall {R: Chain bisimF}, Proper (`R ==> `R ==> `R) pls.
Proof.
  apply (Proper_chain 2).
  intros R HR x y [xy0 xy'] u v [uv0 uv'].
  split; cbn.
  - congruence.
  - now apply HR.
Qed.

Instance pls_proper : Proper (gfp bisimF ==> gfp bisimF ==> gfp bisimF) pls.
Proof. apply gfp_prop. intros R. apply pls_chain_proper. Qed.

Lemma shuf_0x: forall x, zeros @ x ~ zeros.
Proof.
  coinduction R HR. intros x. split; cbn_shuf.
  - nia.
  - rewrite !HR. (* Uses both transitivity and up-to plus context *)
    rewrite plus_0x.
    reflexivity.
Qed.

(*|
Exercises 3.
|*)

Lemma shuf_1x: forall x, zeros @ x ~ zeros.
Admitted.

Lemma shufC: forall x y, x @ y ~ y @ x.
Proof.
coinduction R CIH ; intros x y. split ; cbn_shuf.
- nia.
- rewrite (CIH (tl x) y), (CIH x (tl y)). now rewrite plsC.
Qed.

Lemma shuf_x_plus: forall x y z, x@(y + z) ~ x@y + x@z.
Proof.
coinduction R CIH. intros x y z. split ; cbn_shuf.
- nia.
- rewrite !CIH. rewrite !plsA. f_equiv. rewrite <-!plsA. f_equiv.
  rewrite plsC. reflexivity.
Qed.

Instance shuf_proper_chain {R : Chain bisimF} : Proper (`R ==> `R ==> `R) shuf.
Proof.
revert R. apply (Proper_chain 2). cbn [respectful_iter].
intros R HR x x' [Hx1 Hx2] y y' [Hy1 Hy2]. split ; cbn_shuf.
- nia.
- rewrite Hx2, Hy2. f_equiv.
  + f_equiv. now step.
  + f_equiv. now step.
Qed.

(** Not strictly needed, but might be in more complex proofs. *)
Instance shuf_proper : Proper (gfp bisimF ==> gfp bisimF ==> gfp bisimF) shuf.
Proof. apply gfp_prop. intros R. apply shuf_proper_chain. Qed.

Lemma shuf_plus_x: forall x y z, (y + z)@x ~ y@x + z@x.
Proof.
intros x y z. rewrite shufC, shuf_x_plus. rewrite (shufC x y), (shufC x z).
reflexivity.
Qed.

Lemma shufA: forall x y z, x @ (y @ z) ~ (x @ y) @ z.
coinduction R CIH. intros x y z. split ; cbn_shuf.
- nia.
- rewrite shuf_plus_x, shuf_x_plus. rewrite !plsA. f_equiv ; [f_equiv|].
  all: now rewrite CIH.
Qed.

(*|
29. Up-to [shuffle] Context
|*)

(** shuffle product preserves the final chain *)
(*Instance shuf_chain: forall {R: Chain bisimF}, Proper (`R ==> `R ==> `R) shuf.
Proof.
  apply (Proper_chain 2).
  intros R HR x y [xy xy'] u v [uv uv'].
  split; cbn_shuf.
  - congruence.
  - now rewrite xy', uv', xy, uv.
Qed.*)

(*|
30. Accumulate
|*)

(*|
One can build the coinduction candidate on the fly.

Initially introduced in paco:
G b x := gfp (λy . b (x ∪ y))

accumulate: y <= G b x <-> y <= G b (x ∪ y)

Intuition: it is sound to record pairs we have encountered as valid stopping point, if we keep going first.

|*)

Goal zeros ~ zeros'.
Proof.
  coinduction R cih.
  split; [reflexivity |].
  accumulate cih'.
  split; [reflexivity |].
  exact cih.
Qed.

(*|
Note: Once you move to a principle rich enough to support clean
up-to [b], use cases become more rare.
|*)

(*|
|*)

(** * convolution product *)

CoFixpoint c n := n ::: c n.

(** this is the following binary operation on streams [s,t]:
    [(s*t)_k = Σ_{i+j=k} s_i t_j]
    (note that the binomial coefficient has disappeared)

    it can be characterised by the following equations:
    [hd (s*t) = hd s * hd t]
    [tl (s*t) = tl s * t + hd s ** tl t]
    There [**] is pointwise multiplication by a scalar, which is a special case of convolution product:
    [x ** s = c x * s]
    (Remember that [c x] is the stream [x,0,0,...] )
 *)

(** Like before, we cannot define it as one could expect in Coq,
    because of the guard condition: *)
Fail CoFixpoint mult s t :=
  cons (hd s * hd t)%nat (mult (tl s) t + mult (c (hd s)) (tl t)).

(** Here we simply assume its existence for the sake of simplicity. *)
Parameter mult: stream -> stream -> stream.
Infix "*" := mult.
Axiom hd_mult: forall s t, hd (s * t) = (hd s * hd t)%nat.
Axiom tl_mult: forall s t, tl (s * t) = tl s * t + c (hd s) * tl t.
Ltac cbn_mult := repeat (rewrite ?hd_mult, ?tl_mult; simpl hd; simpl tl).

Lemma mult_0x: forall x, c 0 * x ~ c 0.
Proof.
Admitted.

Lemma mult_x0: forall x, x  * c 0 ~ c 0.
Proof.
Admitted.

Lemma mult_1x: forall x, c 1 * x ~ x.
Proof.
Admitted.

Lemma mult_x1: forall x, x * c 1 ~ x.
Proof.
Admitted.

Lemma mult_x_plus: forall x y z, x * (y + z) ~ x*y + x*z.
Proof.
Admitted.

Lemma c_plus n m: c (n+m) ~ c n + c m.
Proof.
Admitted.

Lemma c_mult n m: c (n*m) ~ c n * c m.
Proof.
Admitted.

(** convolution product preserves the final chain  *)
Instance mult_chain: forall {R: Chain bisimF}, Proper (`R ==> `R ==> `R) mult.
Proof.
Admitted.

Lemma mult_plus_x: forall x y z, (y + z) * x ~ y*x + z*x.
Proof.
Admitted.

Lemma multA: forall x y z, x * (y * z) ~ (x * y) * z.
Proof.
Admitted.

(** below: commutativity of convolution product, following Rutten's
    proof *)

Lemma multC_n n: forall x, c n * x ~ x * c n.
Proof.
Admitted.

Definition X := cons 0 (c 1).

Theorem expand x: x ~ c (hd x) + X * tl x.
Proof.
Admitted.

Lemma multC_11 x: tl (X * x) ~ x.
Proof.
Admitted.

Lemma multC_X: forall x, X * x ~ x * X.
Proof.
Admitted.

Lemma multC: forall x y, x * y ~ y * x.
Proof.
Admitted.

End stream.

(*|
31. Going Further
|*)

(*|
Library support for coinductive relations and proofs by coinduction!

But what about coinductive types and corecursive programming?
Some help to define the shuffle product?

You can do it smoothly in Isabelle/HOL!

~> A library of final coalgebras and up-to corecursion?
For the curious reader, some introductory elements in this direction can be found here: https://github.com/damien-pous/epit25/
|*)

(*|
More examples?

- Tutorial examples: https://github.com/damien-pous/coinduction-examples

- Real world example with [paco] : https://github.com/DeepSpec/InteractionTrees

- Real world example with [coinduction] : https://github.com/vellvm/ctrees
|*)
