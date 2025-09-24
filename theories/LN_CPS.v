From Stdlib Require Import Bool Nat List String.
From Stdlib.Classes Require Import Morphisms.
From Equations Require Import Equations.
From stdpp Require Import gmap.
Import ListNotations.

Ltac feed H :=
  match type of H with
  | ?P -> ?Q =>
    let HP := fresh "H" in
    assert P as HP ; [| specialize (H HP) ; clear HP ]
  end.

(**************************************************************************)
(** *** Names of variables. *)
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

Lemma eqb_name_true n : eqb_name n n = true.
Proof. destruct (eqb_name_spec n n) ; auto. Qed.

Lemma eqb_name_false n n' : n ≠ n' -> eqb_name n n' = false.
Proof. intros H. destruct (eqb_name_spec n n') ; auto. now exfalso. Qed.

(**************************************************************************)
(** *** Swapping names. *)
(**************************************************************************)

Definition swap_name (a b x : name) : name :=
  if eqb_name x a then b
  else if eqb_name x b then a
  else x.

Lemma swap_name_inv a b x :
  swap_name a b (swap_name a b x) = x.
Proof.
unfold swap_name. destruct (eqb_name_spec x a) ; subst.
- rewrite eqb_name_true. now destruct (eqb_name_spec b a).
- destruct (eqb_name_spec x b) ; subst.
  + now rewrite eqb_name_true.
  + now rewrite eqb_name_false, eqb_name_false by assumption.
Defined.

Lemma swap_name_inj a b x x' :
  swap_name a b x = swap_name a b x' -> x = x'.
Proof.
intros H1. apply (f_equal (swap_name a b)) in H1.
now rewrite !swap_name_inv in H1.
Qed.

Lemma swap_name_left a b : swap_name a b a = b.
Proof. cbn. unfold swap_name. now rewrite eqb_name_true. Qed.

Lemma swap_name_right a b : swap_name a b b = a.
Proof. cbn. unfold swap_name. destruct (eqb_name_spec b a) ; auto.
now rewrite eqb_name_true.
Qed.

Lemma swap_name_free a b x :
  x ≠ a -> x ≠ b -> swap_name a b x = x.
Proof. intros Ha Hb. cbn. unfold swap_name. now rewrite eqb_name_false, eqb_name_false. Qed.

(**************************************************************************)
(** *** Lambda terms and basic operations. *)
(**************************************************************************)

(** Untyped lambda terms in the locally nameless style. *)
Inductive term :=
| fvar (x : name) : term
| bvar (i : nat) : term
| app (t1 : term) (t2 : term) : term
| lam (t : term) : term.

Fixpoint swap_term (a b : name) (t : term) : term :=
  match t with
  | fvar x => fvar (swap_name a b x)
  | bvar i => bvar i
  | app t1 t2 => app (swap_term a b t1) (swap_term a b t2)
  | lam t => lam (swap_term a b t)
  end.

(** [fv t] computes the set of free variables in [t]. *)
Fixpoint fv (t : term) : gset name :=
  match t with
  | fvar x => {[ x ]}
  | bvar i => ∅
  | app t1 t2 => fv t1 ∪ fv t2
  | lam t => fv t
  end.

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

(** [subst x u t] substitutes [x] with [u] in [t].
    It assumes [u] and [t] are locally closed, so there is no need for lifting. *)
Fixpoint subst (x : name) (u : term) (t : term) : term :=
  match t with
  | fvar y => if eqb_name x y then u else fvar y
  | bvar i => bvar i
  | app t1 t2 => app (subst x u t1) (subst x u t2)
  | lam t => lam (subst x u t)
  end.

Notation "'{' x '~>' u '}' t" := (subst x u t)
  (at level 20, left associativity, format "{ x  ~>  u } t").

(** A term is locally closed iff all its de Bruijn indices have
    a corresponding binder.
    E.g. the term [lam (bvar 2)] is _not_ locally closed
    because de Bruijn index [2] is unbound. *)
Inductive lc : term -> Prop :=
| lc_fvar x :
    lc (fvar x)
| lc_app t1 t2 :
    lc t1 -> lc t2 -> lc (app t1 t2)
| lc_lam t :
    (forall x, x ∉ fv t -> lc (t ^ x)) ->
    lc (lam t).

#[export] Hint Resolve lc_fvar : lc.
#[export] Hint Resolve lc_app : lc.

(**************************************************************************)
(** *** Basic lemmas. *)
(**************************************************************************)

Lemma swap_term_inv a b t :
  swap_term a b (swap_term a b t) = t.
Proof.
induction t ; cbn ; try congruence.
now rewrite swap_name_inv.
Qed.

Lemma swap_term_inj a b t t' :
  swap_term a b t = swap_term a b t' -> t = t'.
Proof.
intros H. apply (f_equal (swap_term a b)) in H.
now rewrite !swap_term_inv in H.
Qed.

Lemma swap_term_free a b t :
  a ∉ fv t -> b ∉ fv t -> swap_term a b t = t.
Proof.
intros Ha Hb. induction t ; cbn in *.
- rewrite not_elem_of_singleton in Ha, Hb. now rewrite swap_name_free.
- reflexivity.
- rewrite not_elem_of_union in Ha, Hb. now rewrite IHt1, IHt2.
- now rewrite IHt.
Qed.

Lemma swap_term_open a b t u :
  swap_term a b (t ^^ u) = (swap_term a b t) ^^ (swap_term a b u).
Proof.
generalize 0. induction t ; intros k ; cbn.
- reflexivity.
- destruct (Nat.eqb_spec i k) ; reflexivity.
- rewrite IHt1, IHt2. reflexivity.
- rewrite IHt. reflexivity.
Qed.

Lemma swap_term_open_var a b t x :
  swap_term a b (t ^ x) = (swap_term a b t) ^ (swap_name a b x).
Proof. now rewrite swap_term_open. Qed.

Lemma swap_term_close a b t x :
  swap_term a b (t \^ x) = (swap_term a b t) \^ (swap_name a b x).
Proof.
generalize 0. induction t ; intros k ; cbn.
- destruct (eqb_name_spec x x0) ; subst ; cbn.
  + now rewrite eqb_name_true.
  + rewrite eqb_name_false.
    * reflexivity.
    * intros H. apply n. now apply swap_name_inj in H.
- reflexivity.
- rewrite IHt1, IHt2. reflexivity.
- rewrite IHt. reflexivity.
Qed.

Lemma elem_of_fv_swap x a b t :
  swap_name a b x ∈ fv (swap_term a b t) <-> x ∈ fv t.
Proof.
enough (forall x t, x ∈ fv t -> swap_name a b x ∈ fv (swap_term a b t)).
{ split ; [|apply H]. rewrite <-(swap_name_inv a b x), <-(swap_term_inv a b t) at 2.
  apply H. }
clear x t ; intros x t. induction t ; cbn ; intros H.
- rewrite elem_of_singleton in *. now subst.
- now apply elem_of_empty in H.
- rewrite elem_of_union in *. destruct H as [H1 | H2].
  + left ; now apply IHt1.
  + right ; now apply IHt2.
- now apply IHt.
Qed.

Lemma lc_swap a b t : lc (swap_term a b t) <-> lc t.
Proof.
enough (forall t, lc t -> lc (swap_term a b t)).
{ split ; [|apply H]. rewrite <-(swap_term_inv a b t) at 2. apply H. }
clear t ; intros t H. induction H ; cbn ; constructor ; auto.
intros x Hx. specialize (H0 (swap_name a b x)).
rewrite swap_term_open_var, swap_name_inv in H0. apply H0.
rewrite <-(swap_term_inv a b t). now rewrite elem_of_fv_swap.
Qed.

(** Existentially quantified version of [lc_lam]. *)
Lemma lc_lam_intro x t :
  x ∉ fv t -> lc (t ^ x) -> lc (lam t).
Proof.
intros Hx H. apply lc_lam. intros y Hy.
rewrite <-(lc_swap x y), swap_term_open_var, swap_name_left in H.
now rewrite swap_term_free in H.
Qed.

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

Lemma not_elem_of_fv_close t x :
  x ∉ fv (t \^ x).
Proof.
generalize 0. intros k. induction t in k, x |- * ; cbn.
- destruct (eqb_name_spec x x0) ; subst ; cbn.
  + apply not_elem_of_empty.
  + now apply not_elem_of_singleton.
- apply not_elem_of_empty.
- rewrite not_elem_of_union. split ; [apply IHt1 | apply IHt2].
- apply IHt.
Qed.

(*Lemma open_close x t u :
  lc t -> (t \^ x) ^^ u = [x ~> u]t.
Proof.
(*intros H. generalize 0. induction t in x, H |- * ; cbn.
- destruct (eqb_name_spec x x0) ; subst ; cbn ; reflexivity.
- inversion H.
- inversion H ; subst. now rewrite IHt1, IHt2.*)
Admitted.*)

Lemma open_close_same x t :
  lc t -> (t \^ x) ^ x = t.
Proof. Admitted.

(**************************************************************************)
(** *** Reduction relation. *)
(**************************************************************************)

Reserved Notation "t '~~>₁' u" (at level 60, no associativity).
Reserved Notation "t '~~>+' u" (at level 60, no associativity).
Reserved Notation "t '~~>*' u" (at level 60, no associativity).

Inductive red : term -> term -> Prop :=
| red_beta t u :
    app (lam t) u ~~>₁ t ^^ u
| red_app_l t t' u :
    t ~~>₁ t' -> app t u ~~>₁ app t' u
| red_app_r t u u' :
    u ~~>₁ u' -> app t u ~~>₁ app t u'
| red_lam t t' :
    (forall x, x ∉ fv t -> x ∉ fv t' -> t ^ x ~~>₁ t' ^ x) ->
    lam t ~~>₁ lam t'
where "t '~~>₁' u" := (red t u).

Inductive red_plus : term -> term -> Prop :=
| red_plus_one t1 t2 : t1 ~~>₁ t2 -> t1 ~~>+ t2
| red_plus_trans t1 t2 t3 : t1 ~~>+ t2 -> t2 ~~>+ t3 -> t1 ~~>+ t3
where "t '~~>+' u" := (red_plus t u).

Inductive red_star : term -> term -> Prop :=
| red_star_refl t : t ~~>* t
| red_star_one t1 t2 : t1 ~~>₁ t2 -> t1 ~~>* t2
| red_star_trans t1 t2 t3 : t1 ~~>* t2 -> t2 ~~>* t3 -> t1 ~~>* t3
where "t '~~>*' u" := (red_star t u).

#[local] Instance red_plus_Transitive : Transitive red_plus := red_plus_trans.
#[local] Instance red_star_Reflexive : Reflexive red_star := red_star_refl.
#[local] Instance red_star_Transitive : Transitive red_star := red_star_trans.

Lemma swap_term_red a b t t' :
  swap_term a b t ~~>₁ swap_term a b t' <-> t ~~>₁ t'.
Proof.
enough (forall t t', t ~~>₁ t' -> swap_term a b t ~~>₁ swap_term a b t').
{ split ; [|apply H]. rewrite <-(swap_term_inv a b t), <-(swap_term_inv a b t') at 2.
  apply H. }
clear t t' ; intros t t'. intros H. induction H ; cbn.
- rewrite swap_term_open. apply red_beta.
- now apply red_app_l.
- now apply red_app_r.
- apply red_lam. intros x Hx1 Hx2. specialize (H0 (swap_name a b x)).
  rewrite !swap_term_open_var, !swap_name_inv in H0. apply H0.
  + rewrite <-(swap_term_inv a b t). now rewrite elem_of_fv_swap.
  + rewrite <-(swap_term_inv a b t'). now rewrite elem_of_fv_swap.
Qed.

Lemma swap_term_red_plus a b t t' :
  swap_term a b t ~~>+ swap_term a b t' <-> t ~~>+ t'.
Proof.
enough (forall t t', t ~~>+ t' -> swap_term a b t ~~>+ swap_term a b t').
{ split ; [|apply H]. rewrite <-(swap_term_inv a b t), <-(swap_term_inv a b t') at 2.
  apply H. }
clear t t' ; intros t t' H. induction H.
- now apply red_plus_one, swap_term_red.
- etransitivity ; eauto.
Qed.

Lemma swap_term_red_star a b t t' :
  swap_term a b t ~~>* swap_term a b t' <-> t ~~>* t'.
Proof.
enough (forall t t', t ~~>* t' -> swap_term a b t ~~>* swap_term a b t').
{ split ; [|apply H]. rewrite <-(swap_term_inv a b t), <-(swap_term_inv a b t') at 2.
  apply H. }
clear t t' ; intros t t' H. induction H.
- reflexivity.
- now apply red_star_one, swap_term_red.
- etransitivity ; eauto.
Qed.

Lemma red_lam_intro x t t' :
  x ∉ fv t -> x ∉ fv t' -> t ^ x ~~>₁ t' ^ x -> lam t ~~>₁ lam t'.
Proof.
intros Hx1 Hx2 H. apply red_lam. intros y Hy1 Hy2. apply (swap_term_red x y) in H.
rewrite !swap_term_open_var, !swap_name_left in H. now rewrite !swap_term_free in H.
Qed.

Lemma red_star_lam_intro x t t' :
  x ∉ fv t -> x ∉ fv t' -> t ^ x ~~>* t' ^ x -> lam t ~~>* lam t'.
Proof.
intros Hx1 Hx2 H.
(*intros Hx1 Hx2 H. remember (t ^ x) as tx. remember (t' ^ x) as tx'. induction H. apply red_lam. intros y Hy1 Hy2. apply (swap_red x y) in H.
rewrite !swap_open_var, !swap_name_left in H. now rewrite !swap_free in H.*)
Admitted.

(**************************************************************************)
(** *** Contexts and well-scoped terms. *)
(**************************************************************************)

(* Local declaration (no body). *)
Inductive local_decl :=
| LDecl : name -> local_decl.

(** A local context stores the declarations of all free variables
    in scope. The most recent declaration is at the head of the list. *)
Definition context := list local_decl.

(** The domain of a context is the set of variables which are bound
    by the context. *)
Fixpoint domain (ctx : context) : gset name :=
  match ctx with
  | nil => ∅
  | LDecl x :: ctx => {[ x ]} ∪ domain ctx
  end.

Lemma domain_app c1 c2 :
  domain (c1 ++ c2) = domain c1 ∪ domain c2.
Proof.
induction c1 as [|[x] c1 IH] ; cbn.
- now rewrite union_empty_l_L.
- now rewrite IH, union_assoc_L.
Qed.

(** A term is well-scoped iff all of its free variables appear in the context.
    In particular [bvar i] is never well-scoped. *)
Inductive well_scoped : context -> term -> Prop :=
| well_scoped_fvar ctx x :
    x ∈ domain ctx -> well_scoped ctx (fvar x)
| well_scoped_app ctx t1 t2 :
    well_scoped ctx t1 ->
    well_scoped ctx t2 ->
    well_scoped ctx (app t1 t2)
| well_scoped_lam ctx t :
    (forall x, x ∉ fv t -> x ∉ domain ctx -> well_scoped (LDecl x :: ctx) (t ^ x)) ->
    well_scoped ctx (lam t).

#[export] Hint Resolve well_scoped_fvar well_scoped_app : well_scoped.

Lemma well_scoped_fvar_head x c :
  well_scoped (LDecl x :: c) (fvar x).
Proof.
constructor. cbn. now apply elem_of_union_l, elem_of_singleton.
Qed.
#[export] Hint Resolve well_scoped_fvar_head : well_scoped.

Lemma well_scoped_lc ctx t : well_scoped ctx t -> lc t.
Proof.
intros H. induction H.
- constructor.
- now constructor.
- destruct (exist_fresh (fv t ∪ domain ctx)) as [x Hx].
  apply not_elem_of_union in Hx. destruct Hx as [Hx1 Hx2].
  apply lc_lam_intro with x ; try assumption. apply H0 ; assumption.
Qed.
#[export] Hint Resolve well_scoped_lc : lc.

Lemma well_scoped_fv ctx t :
  well_scoped ctx t -> fv t ⊆ domain ctx.
Proof.
intros H. induction H ; cbn.
- now rewrite <-elem_of_subseteq_singleton.
- now apply union_least.
- destruct (exist_fresh (fv t ∪ domain ctx)) as [x Hx].
  apply not_elem_of_union in Hx. destruct Hx as [Hx1 Hx2].
  specialize (H0 x Hx1 Hx2). cbn in H0. intros y Hy.
  assert (y ∈ fv (t ^ x)) as Hy'. { now apply fv_open_1. }
  specialize (H0 y Hy').
  rewrite elem_of_union in H0. destruct H0.
  + rewrite elem_of_singleton in H0. subst. done.
  + assumption.
Qed.

Lemma well_scoped_weaken x c1 c2 t :
  well_scoped (c1 ++ c2) t -> well_scoped (c1 ++ LDecl x :: c2) t.
Proof.
intros H. remember (c1 ++ c2) as c eqn:Hc.
induction H in x, c1, c2, Hc |- * ; subst.
- constructor. rewrite domain_app. cbn.
  rewrite (union_comm_L {[x]}), union_assoc_L.
  rewrite domain_app in H. now apply elem_of_union_l.
- constructor.
  + now apply IHwell_scoped1.
  + now apply IHwell_scoped2.
- constructor. intros y Hy Hy'. specialize (H0 y Hy). feed H0.
  { rewrite domain_app in Hy' |- *. cbn in Hy'.
    rewrite (union_comm_L {[x]}), union_assoc_L, not_elem_of_union in Hy'.
    apply Hy'. }
  specialize (H0 x (LDecl y :: c1) c2). feed H0. { now cbn. }
  apply H0.
Qed.

Lemma well_scoped_weaken' x c t :
  well_scoped c t -> well_scoped (LDecl x :: c) t.
Proof. apply (well_scoped_weaken x [] c t). Qed.
#[export] Hint Resolve well_scoped_weaken' : well_scoped.

Fixpoint swap_context (a b : name) (c : context) : context :=
  match c with
  | nil => nil
  | LDecl x :: c => LDecl (swap_name a b x) :: swap_context a b c
  end.

Lemma swap_context_inv a b c :
  swap_context a b (swap_context a b c) = c.
Proof.
induction c as [|[x] c IH] ; cbn.
- reflexivity.
- now rewrite IH, swap_name_inv.
Qed.

Lemma swap_context_inj a b c c' :
  swap_context a b c = swap_context a b c' -> c = c'.
Proof.
intros H. apply (f_equal (swap_context a b)) in H.
now rewrite !swap_context_inv in H.
Qed.

Lemma swap_context_free a b c :
  a ∉ domain c -> b ∉ domain c -> swap_context a b c = c.
Proof.
intros Ha Hb. induction c as [|[x] c IH] ; cbn.
- reflexivity.
- cbn in Ha, Hb. rewrite not_elem_of_union, not_elem_of_singleton in Ha, Hb.
  destruct Ha as [Ha1 Ha2]. destruct Hb as [Hb1 Hb2].
  rewrite IH by assumption. now rewrite swap_name_free.
Qed.

Lemma elem_of_domain_swap a b x ctx :
  swap_name a b x ∈ domain (swap_context a b ctx) <-> x ∈ domain ctx.
Proof.
induction ctx as [|[y] ctx IH] ; cbn.
- split ; intros H ; now apply elem_of_empty in H.
- rewrite !elem_of_union, IH, !elem_of_singleton. split ; intros [H1 | H2].
  + left. now apply swap_name_inj in H1.
  + now right.
  + subst. now left.
  + now right.
Qed.

Lemma well_scoped_swap a b t ctx :
  well_scoped (swap_context a b ctx) (swap_term a b t) <-> well_scoped ctx t.
Proof.
enough (forall ctx t, well_scoped ctx t -> well_scoped (swap_context a b ctx) (swap_term a b t)).
{ split ; [|apply H]. rewrite <-(swap_context_inv a b ctx), <-(swap_term_inv a b t) at 2.
  apply H. }
clear t ctx ; intros ctx t H. induction H ; cbn.
- constructor. now rewrite elem_of_domain_swap.
- constructor ; assumption.
- constructor. intros x Hx1 Hx2. specialize (H0 (swap_name a b x)).
  feed H0. { now rewrite <-(swap_term_inv a b t), elem_of_fv_swap. }
  feed H0. { now rewrite <-(swap_context_inv a b ctx), elem_of_domain_swap. }
  cbn in H0. rewrite swap_term_open_var, !swap_name_inv in H0.
  apply H0.
Qed.

Lemma well_scoped_lam_intro x t ctx :
  x ∉ fv t -> x ∉ domain ctx -> well_scoped (LDecl x :: ctx) (t ^ x) ->
  well_scoped ctx (lam t).
Proof.
intros Hx1 Hx2 H. constructor. intros y Hy1 Hy2.
rewrite <-(well_scoped_swap x y). cbn. rewrite swap_name_right.
rewrite swap_context_free, swap_term_open_var, swap_name_right, swap_term_free by assumption.
exact H.
Qed.

Lemma well_scoped_lam_close ctx t x :
  x ∉ domain ctx -> well_scoped (LDecl x :: ctx) t -> well_scoped ctx (lam (t \^ x)).
Proof.
intros H1 H2. apply well_scoped_lam_intro with x.
- apply not_elem_of_fv_close.
- assumption.
- rewrite open_close_same ; eauto with lc.
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

(** Convenient function to build a lambda abstraction. *)
Definition mk_lambda (f : name -> M term) : M term :=
  let* x := fresh_name in
  with_decl (LDecl x)
    (let* body := f x in
     ret (lam (body \^ x))).

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

Lemma wp_fresh_name ctx Φ :
  (forall x, x ∉ domain ctx -> Φ ctx x) -> wp ctx fresh_name Φ.
Proof. Admitted.

Lemma wp_mk_lambda f ctx Φ :
  (forall x, x ∉ domain ctx ->
    wp (LDecl x :: ctx) (f x) (fun _ body => Φ ctx (lam (body \^ x)))) ->
  wp ctx (mk_lambda f) Φ.
Proof.
intros H. unfold mk_lambda. apply wp_bind, wp_fresh_name. intros x Hx.
specialize (H x Hx). apply wp_with_decl, wp_bind. cbn. apply H.
Qed.

Ltac wp_step :=
  match goal with
  | [ |- wp _ (ret _) _ ] => apply wp_ret
  | [ |- wp _ (bind _ _) _ ] => apply wp_bind
  | [ |- wp _ out_of_fuel _ ] => apply wp_out_of_fuel
  | [ |- wp _ get_ctx _ ] => apply wp_get
  | [ |- wp _ (put_ctx _) _ ] => apply wp_put
  | [ |- wp _ (with_decl _ _) _ ] => apply wp_with_decl
  | [ |- wp _ fresh_name _ ] => apply wp_fresh_name
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
  | bvar i => error
  | fvar x => ret (app k (fvar x))
  | app t1 t2 =>
    let* k1 := mk_lambda (fun x1 =>
      let* k2 := mk_lambda (fun x2 =>
        ret (app (fvar x1) (app (fvar x2) k)))
      in cps n t2 k2)
    in
    cps n t1 k1
  | lam t' =>
    let* rhs :=
      mk_lambda (fun x =>
      mk_lambda (fun k' =>
        cps n (t' ^ x) (fvar k')
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
- inversion Ht.
- inversion Ht ; subst. wp_steps. intros x Hx.
  wp_steps. intros y Hy. wp_steps.
  assert (Hxy : y ≠ x).
  { cbn in Hy. rewrite not_elem_of_union in Hy. destruct Hy as [Hy _].
    now apply not_elem_of_singleton in Hy. }
  apply IHn.
  {
    inversion Ht ; subst. split.
    - auto with well_scoped.
    - apply well_scoped_lam_intro with y.
      + cbn. rewrite eqb_name_true, eqb_name_false by assumption. cbn.
        apply not_elem_of_union. split.
        * now apply not_elem_of_singleton.
        * rewrite union_empty_l_L. apply not_elem_of_fv_close.
      + assumption.
      + rewrite open_close_same.
        * auto with well_scoped.
        * eauto with lc.
  }
  intros t' Ht'. apply IHn.
  {
    split.
    - assumption.
    - apply well_scoped_lam_intro with x.
      + apply not_elem_of_fv_close.
      + assumption.
      + rewrite open_close_same.
        * assumption.
        * eauto with lc.
  }
  intros t'' Ht''. apply HΦ. assumption.
- wp_steps. intros x Hx. wp_steps. intros y Hy. apply IHn.
  { split.
    - inversion Ht ; subst. apply well_scoped_weaken'. apply H1 ; [|assumption].
      apply well_scoped_fv in Ht. cbn in Ht. intros H'. now apply Hx, Ht.
    - auto with well_scoped.
  }
  intros t' Ht'. wp_steps. apply HΦ. apply well_scoped_app ; [assumption|].
  apply well_scoped_lam_close ; [assumption|].
  apply well_scoped_lam_close ; assumption.
Qed.
