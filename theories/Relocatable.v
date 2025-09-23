From Stdlib Require Import Bool Nat String Lia.

(**************************************************************************)
(** *** Lambda terms.                                                     *)
(**************************************************************************)

(** Lambda terms with de Bruijn indices. *)
Inductive term :=
| tVar : nat -> term
| tApp : term -> term -> term
| tLam : term -> term.

(** Renamings. *)
Definition ren := nat -> nat.

(** Identity renaming. *)
Definition rid : ren := fun i => i.

(** Lift a renaming through a binder. *)
Definition up_ren (r : ren) : ren :=
  fun i =>
    match i with
    | 0 => 0
    | S i => S (r i)
    end.

(** Left-to-right composition of renamings. *)
Definition rcomp (r1 r2 : ren) : ren :=
  fun i => r2 (r1 i).

(** Rename a term. *)
Fixpoint rename (r : ren) (t : term) : term :=
  match t with
  | tVar i => tVar (r i)
  | tApp t1 t2 => tApp (rename r t1) (rename r t2)
  | tLam t => tLam (rename (up_ren r) t)
  end.
Notation "t '[' r ']'" := (rename r t) (at level 20, left associativity).

(** Lifts, as a special kind of renamings. *)
Definition lift (k : nat) : ren :=
  fun i => i + k.
Notation "'↑' k" := (lift k) (at level 10, no associativity).

(**************************************************************************)
(** *** Relocatable terms                                                 *)
(**************************************************************************)

Definition rterm : Type := nat -> term.

Definition repr (t : rterm) (n : nat) (u : term) :=
  forall k, t (n + k) = u[↑k].
Notation "t '~{' n '}~>' u" := (repr t n u) (at level 40, no associativity).

Definition rvar (n i : nat) : rterm :=
  fun n' => tVar (i + (n' - n)).

Lemma rvar_repr n i :
  rvar n i ~{n}~> tVar i.
Proof. intros k. unfold rvar, lift. cbn. f_equal. lia. Qed.

Definition rapp (t1 t2 : rterm) : rterm :=
  fun n => tApp (t1 n) (t2 n).

Lemma rapp_repr t1 t2 n u1 u2 :
  t1 ~{n}~> u1 ->
  t2 ~{n}~> u2 ->
  rapp t1 t2 ~{n}~> tApp u1 u2.
Proof. intros H1 H2 k. unfold rapp. cbn. rewrite H1, H2. reflexivity. Qed.

Definition rlam (t : rterm -> rterm) : rterm :=
  fun n =>
    let x := rvar (S n) 0 in
    tLam (t x (S n)).

Lemma rlam_repr t n u :
  t (rvar (S n) 0) ~{S n}~> u ->
  rlam t ~{n}~> tLam u.
Proof.
intros H k. unfold repr in H. unfold rlam. cbn. f_equal.

(** Relocatable terms. *)
(*Definition rterm := ren -> term.

(** Representation predicate. *)
Definition repr (t : rterm) (u : term) :=
  forall θ, t θ = u[θ].
Notation "t '~~>' u" := (repr t u) (at level 40, no associativity).

(** Smart constructors. *)

Definition rvar (i : nat) : rterm :=
  fun θ => tVar (θ i).

Lemma rvar_repr i :
  rvar i ~~> tVar i.
Proof. intros θ. reflexivity. Qed.

Definition rapp (t1 t2 : rterm) : rterm :=
  fun θ => tApp (t1 θ) (t2 θ).

Lemma rapp_repr t1 t2 t1' t2' :
  t1 ~~> t1' ->
  t2 ~~> t2' ->
  rapp t1 t2 ~~> tApp t1' t2'.
Proof. intros H1 H2 k. unfold rapp. cbn. now rewrite H1, H2. Qed.

Definition rlam (t : rterm) : rterm :=
  fun θ => tLam (t (up_ren θ)).

Lemma repr_rlam t t' :
  t ~~> t' -> rlam t ~~> tLam t'.
Proof. intros H θ. unfold rlam. cbn. now rewrite H. Qed.

(** Testing. *)

Definition t : rterm := rlam (rlam (rvar 1)).

Lemma repr_t : t ~~> tLam (tLam (tVar 1)).
Proof. intros θ. reflexivity. Qed.

(** Destructors. *)

Inductive rview :=
| rVar : (ren -> nat) -> rview
| rApp : rterm -> rterm -> rview
| rLam : rterm -> rview.

Definition destruct (t : rterm) : rview :=
  match t rid with
  | tVar i => rVar (fun θ => θ i)
  | tApp t1 t2 => rApp (fun θ => t1[θ]) (fun θ => t2[θ])
  | tLam t => rLam (fun θ => t[θ])
  end.

Lemma destruct_repr_app t u t1 t2 :
  t ~~> u ->
  destruct t = rApp t1 t2 ->
  exists u1 u2,
    u = tApp u1 u2 /\
    t1 ~~> u1 /\
    t2 ~~> u2.
Proof.
intros Hrepr Hdest. destruct u.
- exfalso. unfold destruct in Hdest. rewrite Hrepr in Hdest. cbn in Hdest. inversion Hdest.
- exists u1, u2.
Admitted.

Lemma destruct_repr_lam t u t' :
  t ~~> u ->
  destruct t = rLam t' ->
  exists u', u = tLam u' /\ t' ~~> u'.
Proof.
intros Hrepr Hdest. destruct u.
- exfalso. unfold destruct in Hdest. rewrite Hrepr in Hdest. cbn in Hdest. inversion Hdest.
- exfalso. unfold destruct in Hdest. rewrite Hrepr in Hdest. cbn in Hdest. inversion Hdest.
- exists u. split ; [reflexivity|]. unfold destruct in Hdest. rewrite Hrepr in Hdest.
  cbn in Hdest. inversion Hdest ; subst. intros θ. unfold repr in Hrepr. f_equal.
Admitted. (* OK. *)*)
