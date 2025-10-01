From Stdlib Require Import Bool Nat List String.
From Stdlib.Classes Require Import Morphisms.
From Equations Require Import Equations.
From stdpp Require Import gmap.
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
  feed_aux H ; [by t|].

Tactic Notation "feed" ident(H) :=
  feed_aux H.

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
- by left.
- by right.
Qed.

Lemma eqb_name_true n : eqb_name n n = true.
Proof. destruct (eqb_name_spec n n) ; auto. Qed.

Lemma eqb_name_false n n' : n ≠ n' -> eqb_name n n' = false.
Proof. intros H. destruct (eqb_name_spec n n') ; auto. by exfalso. Qed.

Definition swap_name (a b x : name) : name :=
  if eqb_name x a then b
  else if eqb_name x b then a
  else x.

Lemma swap_name_left a b : swap_name a b a = b.
Proof. cbn. unfold swap_name. by rewrite eqb_name_true. Qed.

Lemma swap_name_right a b : swap_name a b b = a.
Proof.
cbn. unfold swap_name. destruct (eqb_name_spec b a) ; auto.
by rewrite eqb_name_true.
Qed.

Lemma swap_name_inv a b x :
  swap_name a b (swap_name a b x) = x.
Proof.
unfold swap_name. destruct (eqb_name_spec x a) ; subst.
- rewrite eqb_name_true. by destruct (eqb_name_spec b a).
- destruct (eqb_name_spec x b) ; subst.
  + by rewrite eqb_name_true.
  + by rewrite eqb_name_false, eqb_name_false by assumption.
Qed.

(**************************************************************************)
(** *** Nominal types. *)
(**************************************************************************)

(** A nominal type is a type which can contain names which can be renamed.
    A prototypical example is [term] the type of lambda-terms. *)
Class Nominal (T : Type) := mkNominal {
  (** [swap a b t] swaps names [a] and [b] in [t]. *)
  swap : name -> name -> T -> T ;
  (** [fv t] returns the set of free variables in [t]. *)
  fv : T -> gset name ;
  (** [swap a b] is be involutive. *)
  swap_inv a b t : swap a b (swap a b t) = t ;
  (** Swapping interacts well with free variables. *)
  swap_fv a b x t : x ∈ fv t -> swap_name a b x ∈ fv (swap a b t) ;
  (** Swapping free names does nothing. *)
  swap_free a b t : a ∉ fv t -> b ∉ fv t -> swap a b t = t
}.

(** Because [swap a b] is involutive, it is injective. *)
Lemma swap_inj {T} `{NT : Nominal T} a b (t t' : T) :
  swap a b t = swap a b t' -> t = t'.
Proof.
intros H. apply (f_equal (swap a b)) in H.
by rewrite !swap_inv in H.
Qed.

(** Slightly stronger version [swap_fv], useful for rewriting. *)
Lemma swap_fv_iff {T} `{NT : Nominal T} a b x (t : T) :
  swap_name a b x ∈ fv (swap a b t) <-> x ∈ fv t.
Proof.
split ; [|apply swap_fv].
rewrite <-(swap_name_inv a b x), <-(swap_inv a b t) at 2.
apply swap_fv.
Qed.

(**************************************************************************)
(** *** Names are a trivially nominal. *)
(**************************************************************************)

Definition fv_name (x : name) : gset name :=
  {[ x ]}.

(** This instance enables stdpp's [set_unfold] tactic to simplify
    [x ∈ fv_name y] (or [x ∈ fv y]) into [x = y]. *)
#[export] Instance set_unfold_fv_name x y :
  SetUnfoldElemOf x (fv_name y) (x = y).
Proof. constructor. unfold fv_name. set_solver. Qed.

Lemma swap_name_free a b x :
  a ∉ fv_name x -> b ∉ fv_name x -> swap_name a b x = x.
Proof.
intros Ha Hb. unfold swap_name. rewrite !eqb_name_false ; set_solver.
Qed.

Lemma swap_name_fv a b x y :
  x ∈ fv_name y -> swap_name a b x ∈ fv_name (swap_name a b y).
Proof. set_unfold. by intros ->. Qed.

#[export] Instance name_Nominal : Nominal name :=
  mkNominal name swap_name fv_name swap_name_inv swap_name_fv swap_name_free.

(**************************************************************************)
(** *** Finite sets of names are nominal. *)
(**************************************************************************)

Definition fv_gset_name (E : gset name) : gset name := E.

Definition swap_gset_name (a b : name) (E : gset name) : gset name :=
  set_map (swap a b) E.

Lemma swap_gset_name_inv a b E :
  swap_gset_name a b (swap_gset_name a b E) = E.
Proof.
unfold swap_gset_name. rewrite set_eq. intros x ; split.
- set_unfold. intros (? & -> & ? & -> & H). by rewrite (@swap_inv name name_Nominal).
- set_unfold. intros H. exists (swap_name a b x).
  rewrite (@swap_inv name name_Nominal). split ; [reflexivity|].
  exists x ; auto.
Qed.

Lemma swap_gset_name_fv a b x E :
  x ∈ fv_gset_name E -> swap_name a b x ∈ fv_gset_name (swap_gset_name a b E).
Proof. intros H. set_solver. Qed.

Lemma swap_gset_name_free a b E :
  a ∉ fv_gset_name E -> b ∉ fv_gset_name E -> swap_gset_name a b E = E.
Proof.
intros Ha Hb. unfold swap_gset_name. unfold fv_gset_name in Ha, Hb.
rewrite set_eq. intros x ; split ; intros Hx.
- set_unfold. admit.
- set_unfold. exists (swap_name a b x).
Admitted.

#[export] Instance gset_name_Nominal : Nominal (gset name) :=
  mkNominal (gset name) swap_gset_name fv_gset_name swap_gset_name_inv
    swap_gset_name_fv swap_gset_name_free.

(**************************************************************************)
(** *** Lambda terms, as a nominal type. *)
(**************************************************************************)

(** Untyped lambda terms in the locally nameless style. *)
Inductive term :=
| fvar (x : name) : term
| bvar (i : nat) : term
| app (t1 : term) (t2 : term) : term
| lam (t : term) : term
| letin (t u : term) : term.

(** [apps f xs] forms the n-ary application of [f] to arguments [xs]. *)
Fixpoint apps (f : term) (xs : list term) : term :=
  match xs with
  | [] => f
  | x :: xs => apps (app f x) xs
  end.

Fixpoint swap_term (a b : name) (t : term) : term :=
  match t with
  | fvar x => fvar (swap_name a b x)
  | bvar i => bvar i
  | app t1 t2 => app (swap_term a b t1) (swap_term a b t2)
  | lam t => lam (swap_term a b t)
  | letin t u => letin (swap_term a b t) (swap_term a b u)
  end.

Fixpoint fv_term (t : term) : gset name :=
  match t with
  | fvar x => {[ x ]}
  | bvar i => ∅
  | app t1 t2 => fv_term t1 ∪ fv_term t2
  | lam t => fv_term t
  | letin t u => fv_term t ∪ fv_term u
  end.

Lemma swap_term_inv a b t :
  swap_term a b (swap_term a b t) = t.
Proof.
induction t ; cbn ; try congruence.
by rewrite swap_name_inv.
Qed.

Lemma swap_term_fv a b x t :
  x ∈ fv_term t -> swap a b x ∈ fv_term (swap_term a b t).
Proof. induction t ; cbn ; intros H ; set_solver. Qed.

Lemma swap_term_free a b t :
  a ∉ fv_term t -> b ∉ fv_term t -> swap_term a b t = t.
Proof.
intros Ha Hb. induction t ; cbn in *.
- rewrite swap_name_free ; set_solver.
- constructor.
- rewrite IHt1, IHt2 ; set_solver.
- by rewrite IHt.
- rewrite IHt1, IHt2 ; set_solver.
Qed.

#[export] Instance term_Nominal : Nominal term :=
  mkNominal term swap_term fv_term swap_term_inv swap_term_fv swap_term_free.

(**************************************************************************)
(** *** Basic operations on lambda terms. *)
(**************************************************************************)

Fixpoint open (n : nat) (u : term) (t : term) : term :=
  match t with
  | fvar x => fvar x
  | bvar i => if i =? n then u else bvar i
  | app t1 t2 => app (open n u t1) (open n u t2)
  | lam t => lam (open (n+1) u t)
  | letin t1 t2 => letin (open n u t1) (open (n+1) u t2)
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
  | letin t1 t2 => letin (close n x t1) (close (n+1) x t2)
  end.

(** [t \^ x] replaces variable [x] with de Bruijn index [0] in [t]. *)
Notation "t '\^' x" := (close 0 x t) (at level 30, no associativity).

(** Named version of [lam]. *)
Definition named_lam (x : name) (body : term) : term :=
  lam (body \^ x).

(** Named version of [letin]. *)
Definition named_letin (x : name) (xdef : term) (body : term) : term :=
  letin xdef (body \^ x).

(*(** [subst x u t] substitutes [x] with [u] in [t].
    It assumes [u] and [t] are locally closed, so there is no need for lifting. *)
Fixpoint subst (x : name) (u : term) (t : term) : term :=
  match t with
  | fvar y => if eqb_name x y then u else fvar y
  | bvar i => bvar i
  | app t1 t2 => app (subst x u t1) (subst x u t2)
  | lam t => lam (subst x u t)
  end.

Notation "'{' x '~>' u '}' t" := (subst x u t)
  (at level 20, left associativity, format "{ x  ~>  u } t").*)

(** A term is well formed iff all its de Bruijn indices have
    a corresponding binder.
    E.g. the term [lam (bvar 2)] is _not_ well formed
    because de Bruijn index [2] is unbound. *)
Inductive wf : term -> Prop :=
| wf_fvar x :
    wf (fvar x)
| wf_app t1 t2 :
    wf t1 -> wf t2 -> wf (app t1 t2)
| wf_lam t :
    (forall x, x ∉ fv t -> wf (t ^ x)) ->
    wf (lam t)
| wf_letin t u :
    wf t ->
    (forall x, x ∉ fv u -> wf (u ^ x)) ->
    wf (letin t u).

#[export] Hint Resolve wf_fvar : wf.
#[export] Hint Resolve wf_app : wf.

(**************************************************************************)
(** *** Basic lemmas. *)
(**************************************************************************)

Lemma open_equivariant a b t u :
  swap a b (t ^^ u) = (swap a b t) ^^ (swap a b u).
Proof.
generalize 0. induction t ; intros k ; cbn.
- reflexivity.
- by destruct (Nat.eqb_spec i k).
- by rewrite IHt1, IHt2.
- by rewrite IHt.
- by rewrite IHt1, IHt2.
Qed.

Lemma open_var_equivariant a b t x :
  swap a b (t ^ x) = (swap a b t) ^ (swap a b x).
Proof. by rewrite open_equivariant. Qed.

Lemma close_equivariant a b t x :
  swap a b (t \^ x) = (swap a b t) \^ (swap a b x).
Proof.
generalize 0. induction t ; intros k ; cbn.
- destruct (eqb_name_spec x x0) ; subst ; cbn.
  + by rewrite eqb_name_true.
  + rewrite eqb_name_false.
    * reflexivity.
    * intros H. apply n. change swap_name with (@swap name name_Nominal) in H.
      by apply swap_inj in H.
- reflexivity.
- by rewrite IHt1, IHt2.
- by rewrite IHt.
- by rewrite IHt1, IHt2.
Qed.

Lemma wf_equivariant a b t : wf (swap a b t) <-> wf t.
Proof.
enough (forall t, wf t -> wf (swap a b t)).
{ split ; [|apply H]. rewrite <-(swap_inv a b t) at 2. apply H. }
clear t ; intros t H. induction H ; cbn ; constructor ; auto.
- intros x Hx. specialize (H0 (swap a b x)).
  rewrite open_var_equivariant, swap_inv in H0. apply H0.
  rewrite <-(swap_inv a b t). by rewrite swap_fv_iff.
- intros x Hx. specialize (H1 (swap a b x)).
  rewrite open_var_equivariant, swap_inv in H1. apply H1.
  rewrite <-(swap_inv a b u). by rewrite swap_fv_iff.
Qed.

(** Existentially quantified version of [wf_lam]. *)
Lemma wf_lam_intro x t :
  x ∉ fv t -> wf (t ^ x) -> wf (lam t).
Proof.
intros Hx H. apply wf_lam. intros y Hy.
rewrite <-(wf_equivariant x y), open_var_equivariant, swap_name_left in H.
by rewrite swap_free in H.
Qed.

(** Existentially quantified version of [wf_letin]. *)
Lemma wf_letin_intro x t u :
  wf t -> x ∉ fv u -> wf (u ^ x) -> wf (letin t u).
Proof.
intros Ht Hx Hu. apply wf_letin ; [assumption|]. intros y Hy.
rewrite <-(wf_equivariant x y), open_var_equivariant, swap_name_left in Hu.
by rewrite swap_free in Hu.
Qed.

Lemma fv_open_1 u t : fv t ⊆ fv (t ^^ u).
Proof. generalize 0. intros k. induction t in k, u |- * ; set_solver. Qed.

Lemma fv_open_2 u t : fv (t ^^ u) ⊆ fv t ∪ fv u.
Proof.
generalize 0. intros k. induction t in k, u |- * ; cbn ; try set_solver.
destruct (Nat.eqb_spec i k) ; set_solver.
Qed.

Lemma not_elem_of_fv_close t x :
  x ∉ fv (t \^ x).
Proof.
generalize 0. intros k. induction t in k, x |- * ; cbn ; try set_solver.
destruct (eqb_name_spec x x0) ; set_solver.
Qed.

(*Lemma open_close x t u :
  wf t -> (t \^ x) ^^ u = [x ~> u]t.
Proof.
(*intros H. generalize 0. induction t in x, H |- * ; cbn.
- destruct (eqb_name_spec x x0) ; subst ; cbn ; reflexivity.
- inversion H.
- inversion H ; subst. by rewrite IHt1, IHt2.*)
Admitted.*)

Lemma open_close_same x t :
  wf t -> (t \^ x) ^ x = t.
Proof. Admitted.

(**************************************************************************)
(** *** Reduction relation. *)
(**************************************************************************)

(*Reserved Notation "t '~~>₁' u" (at level 60, no associativity).
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
- by apply red_app_l.
- by apply red_app_r.
- apply red_lam. intros x Hx1 Hx2. specialize (H0 (swap_name a b x)).
  rewrite !swap_term_open_var, !swap_name_inv in H0. apply H0.
  + rewrite <-(swap_term_inv a b t). by rewrite elem_of_fv_swap.
  + rewrite <-(swap_term_inv a b t'). by rewrite elem_of_fv_swap.
Qed.

Lemma swap_term_red_plus a b t t' :
  swap_term a b t ~~>+ swap_term a b t' <-> t ~~>+ t'.
Proof.
enough (forall t t', t ~~>+ t' -> swap_term a b t ~~>+ swap_term a b t').
{ split ; [|apply H]. rewrite <-(swap_term_inv a b t), <-(swap_term_inv a b t') at 2.
  apply H. }
clear t t' ; intros t t' H. induction H.
- by apply red_plus_one, swap_term_red.
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
- by apply red_star_one, swap_term_red.
- etransitivity ; eauto.
Qed.

Lemma red_lam_intro x t t' :
  x ∉ fv t -> x ∉ fv t' -> t ^ x ~~>₁ t' ^ x -> lam t ~~>₁ lam t'.
Proof.
intros Hx1 Hx2 H. apply red_lam. intros y Hy1 Hy2. apply (swap_term_red x y) in H.
rewrite !swap_term_open_var, !swap_name_left in H. by rewrite !swap_term_free in H.
Qed.

Lemma red_star_lam_intro x t t' :
  x ∉ fv t -> x ∉ fv t' -> t ^ x ~~>* t' ^ x -> lam t ~~>* lam t'.
Proof.
intros Hx1 Hx2 H.
(*intros Hx1 Hx2 H. remember (t ^ x) as tx. remember (t' ^ x) as tx'. induction H. apply red_lam. intros y Hy1 Hy2. apply (swap_red x y) in H.
rewrite !swap_open_var, !swap_name_left in H. by rewrite !swap_free in H.*)
Admitted.*)

(**************************************************************************)
(** *** Contexts and well-scoped terms. *)
(**************************************************************************)

(** Local declaration. *)
Inductive ldecl :=
| LAssum : name -> ldecl
| LDef : name -> term -> ldecl.

Definition swap_ldecl (a b : name) (d : ldecl) : ldecl :=
  match d with
  | LAssum x => LAssum (swap a b x)
  | LDef x t => LDef (swap a b x) (swap a b t)
  end.

Definition fv_ldecl (d : ldecl) : gset name :=
  match d with
  | LAssum x => fv x
  | LDef x t => fv x ∪ fv t
  end.

Lemma swap_ldecl_inv a b d :
  swap_ldecl a b (swap_ldecl a b d) = d.
Proof.
destruct d ; cbn.
- by rewrite (@swap_inv _ name_Nominal).
- by rewrite (@swap_inv _ name_Nominal), (@swap_inv _ term_Nominal).
Qed.

Lemma swap_ldecl_fv a b x d :
  x ∈ fv_ldecl d -> swap a b x ∈ fv_ldecl (swap_ldecl a b d).
Proof.
intros Hx. destruct d ; cbn.
- set_solver.
- set_unfold. rewrite (@swap_fv_iff _ term_Nominal). set_solver.
Qed.

Lemma swap_ldecl_free a b d :
  a ∉ fv_ldecl d -> b ∉ fv_ldecl d -> swap_ldecl a b d = d.
Proof.
intros Ha Hb. destruct d ; cbn.
- rewrite (@swap_free _ name_Nominal) ; set_solver.
- rewrite (@swap_free _ name_Nominal), (@swap_free _ term_Nominal) ; set_solver.
Qed.

#[export] Instance ldecl_Nominal : Nominal ldecl :=
  mkNominal ldecl swap_ldecl fv_ldecl swap_ldecl_inv swap_ldecl_fv swap_ldecl_free.

(** A local context stores the declarations of all free variables
    in scope. The most recent declaration is at the head of the list. *)
Definition context := list ldecl.

Fixpoint swap_context (a b : name) (c : context) : context :=
  match c with
  | nil => nil
  | d :: c => swap a b d :: swap_context a b c
  end.

Fixpoint fv_context (ctx : context) : gset name :=
  match ctx with
  | nil => ∅
  | d :: ctx => fv d ∪ fv_context ctx
  end.

Lemma swap_context_inv a b c :
  swap_context a b (swap_context a b c) = c.
Proof.
induction c ; cbn.
- reflexivity.
- by rewrite IHc, (@swap_inv ldecl ldecl_Nominal).
Qed.

Lemma swap_context_fv a b x c :
  x ∈ fv_context c -> swap a b x ∈ fv_context (swap_context a b c).
Proof.
intros H. induction c ; cbn.
- set_solver.
- set_unfold. rewrite (@swap_fv_iff ldecl ldecl_Nominal). set_solver.
Qed.

Lemma swap_context_free a b c :
  a ∉ fv_context c -> b ∉ fv_context c -> swap_context a b c = c.
Proof.
intros Ha Hb. induction c ; cbn.
- reflexivity.
- rewrite IHc, (@swap_free ldecl ldecl_Nominal) ; set_solver.
Qed.

#[export] Instance context_Nominal : Nominal context :=
  mkNominal context swap_context fv_context swap_context_inv swap_context_fv swap_context_free.

Lemma fv_context_app (c1 c2 : context) :
  fv (c1 ++ c2) = fv c1 ∪ fv c2.
Proof. induction c1 ; set_solver. Qed.

(** Hook into stdpp's [set_unfold] tactic. *)
#[export] Instance set_unfold_fv_context_app x (c1 c2 : context) P :
  SetUnfoldElemOf x (fv c1 ∪ fv c2) P ->
  SetUnfoldElemOf x (fv (c1 ++ c2)) P.
Proof. intros H. constructor. rewrite fv_context_app. set_solver. Qed.

(** The domain of a context is the set of variables it declares. *)
Fixpoint domain (c : context) : gset name :=
  match c with
  | [] => ∅
  | LAssum x :: c => {[ x ]} ∪ domain c
  | LDef x t :: c => {[ x ]} ∪ domain c
  end.

Lemma domain_app (c1 c2 : context) :
  domain (c1 ++ c2) = domain c1 ∪ domain c2.
Proof. induction c1 as [|[|] c1 IH] ; cbn in * ; set_solver. Qed.

Lemma domain_fv c :
  domain c ⊆ fv c.
Proof. induction c as [|[|] c IH] ; cbn in * ; set_solver. Qed.

Lemma domain_equivariant x a b ctx :
  swap a b x ∈ domain (swap a b ctx) <-> x ∈ domain ctx.
Proof.
enough (forall ctx x, x ∈ domain ctx -> swap a b x ∈ domain (swap a b ctx)).
{ split ; [|apply H]. rewrite <-(swap_inv a b x), <-(swap_inv a b ctx) at 2.
  apply H. }
clear x ctx ; intros ctx x H.
induction ctx as [|[|] ctx IH] ; cbn in * ; set_solver.
Qed.

(** Hook into stdpp's [set_unfold] tactic. *)
#[export] Instance set_unfold_domain_app x (c1 c2 : context) P :
  SetUnfoldElemOf x (domain c1 ∪ domain c2) P ->
  SetUnfoldElemOf x (domain (c1 ++ c2)) P.
Proof. intros H. constructor. rewrite domain_app. set_solver. Qed.

(** A term is well-scoped iff all of its free variables appear in the context.
    In particular [bvar i] is never well-scoped. *)
Inductive scoping : gset name -> term -> Prop :=
| scoping_fvar Γ x :
    x ∈ Γ -> scoping Γ (fvar x)
| scoping_app Γ t1 t2 :
    scoping Γ t1 ->
    scoping Γ t2 ->
    scoping Γ (app t1 t2)
| scoping_lam Γ t :
    (forall x, x ∉ fv t -> x ∉ Γ -> scoping ({[ x ]} ∪ Γ) (t ^ x)) ->
    scoping Γ (lam t)
| scoping_letin Γ t u :
    scoping Γ t ->
    (forall x, x ∉ fv u -> x ∉ Γ -> scoping ({[ x ]} ∪ Γ) (u ^ x)) ->
    scoping Γ (letin t u).

#[export] Hint Extern 10 (_ ∈ _) => (pose proof domain_fv ; set_solver) : scoping.
#[export] Hint Resolve scoping_fvar scoping_app : scoping.

Lemma scoping_wf Γ t : scoping Γ t -> wf t.
Proof.
intros H. induction H.
- constructor.
- by constructor.
- destruct (exist_fresh (fv t ∪ Γ)) as [x Hx].
  apply wf_lam_intro with x ; set_solver.
- destruct (exist_fresh (fv u ∪ Γ)) as [x Hx].
  apply wf_letin_intro with x ; set_solver.
Qed.
#[export] Hint Resolve scoping_wf : wf.

Lemma scoping_vars Γ t :
  scoping Γ t -> fv t ⊆ Γ.
Proof.
intros H. induction H ; cbn.
- set_solver.
- set_solver.
- destruct (exist_fresh (fv t ∪ Γ)) as [x Hx].
  specialize (H0 x). feed H0 by set_solver. feed H0 by set_solver.
  intros y Hy. assert (y ∈ fv (t ^ x)) as Hy'. { by apply fv_open_1. }
  specialize (H0 y Hy'). set_solver.
- enough (fv_term u ⊆ Γ) by set_solver.
  destruct (exist_fresh (fv u ∪ Γ)) as [x Hx].
  specialize (H1 x). feed H1 by set_solver. feed H1 by set_solver.
  intros y Hy. assert (y ∈ fv (u ^ x)) as Hy'. { by apply fv_open_1. }
  specialize (H1 y Hy'). set_solver.
Qed.

Lemma scoping_equivariant a b Γ t :
  scoping (swap a b Γ) (swap a b t) <-> scoping Γ t.
Proof. Admitted.
(*enough (forall ctx t, scoping ctx t -> scoping (swap a b ctx) (swap a b t)).
{ split ; [|apply H]. rewrite <-(swap_inv a b Γ), <-(swap_inv a b t) at 2.
  apply H. }
clear t Γ ; intros Γ t H. induction H ; cbn.
- constructor. setoid_rewrite (@swap_fv_iff _ gset_name_Nominal). assumption.
- constructor ; assumption.
- constructor. intros x Hx1 Hx2. specialize (H0 (swap a b x)).
  feed H0 by rewrite <-(swap_inv a b t), swap_fv_iff.
  feed H0. { setoid_rewrite <-(swap_inv a b Γ). setoid_rewrite swap_fv_iff.
  cbn in H0. rewrite open_var_equivariant, !(@swap_inv name name_Nominal) in H0.
  by apply H0.
- constructor ; [by assumption|]. intros x Hx1 Hx2.
  specialize (H1 (swap a b x)).
  feed H1 by rewrite <-(swap_inv a b u), swap_fv_iff.
  feed H1 by rewrite <-(swap_inv a b ctx), swap_fv_iff.
  cbn in H1. rewrite open_var_equivariant, !(@swap_inv name name_Nominal) in H1.
  by apply H1.
Qed.*)

Lemma scoping_lam_intro x t Γ :
  x ∉ fv t -> x ∉ Γ -> scoping ({[ x ]} ∪ Γ) (t ^ x) ->
  scoping Γ (lam t).
Proof.
(*intros Hx1 Hx2 H. constructor. intros y Hy1 Hy2.
rewrite <-(scoping_equivariant x y). cbn. rewrite swap_name_right.
rewrite open_var_equivariant, swap_name_right.
rewrite (@swap_free context context_Nominal), (@swap_free term term_Nominal) by assumption.
exact H.
Qed.*)
Admitted.

Lemma scoping_letin_intro x t u Γ :
  scoping Γ t ->
  x ∉ fv u -> x ∉ Γ -> scoping ({[ x ]} ∪ Γ) (u ^ x) ->
  scoping Γ (letin t u).
Proof.
(*intros Ht Hx1 Hx2 Hu. constructor ; [assumption|]. intros y Hy1 Hy2.
rewrite <-(scoping_equivariant x y). cbn. rewrite swap_name_right.
rewrite open_var_equivariant, swap_name_right.
rewrite (@swap_free context context_Nominal), (@swap_free term term_Nominal _ _ u) by assumption.
apply scoping_vars in Ht. rewrite domain_fv in Ht.
rewrite (@swap_free term term_Nominal) by set_solver.
exact Hu.
Qed.*)
Admitted.

Lemma scoping_weaken Γ Γ' t :
  Γ ⊆ Γ' -> scoping Γ t -> scoping Γ' t.
Proof.
intros H1 H2. induction H2 in Γ', H1 |- *.
- constructor. set_solver.
- constructor ; auto.
- constructor. intros y Hy Hy'. apply H0 ; set_solver.
- constructor ; [auto|]. intros y Hy Hy'. apply H0 ; set_solver.
Qed.

(* #[export] Hint Resolve scoping_weaken_1' scoping_weaken_2' : scoping.*)

Lemma scoping_named_lam Γ t x :
  x ∉ Γ -> scoping ({[ x ]} ∪ Γ) t -> scoping Γ (named_lam x t).
Proof.
intros H1 H2. apply scoping_lam_intro with x.
- apply not_elem_of_fv_close.
- assumption.
- rewrite open_close_same ; eauto with wf.
Qed.

(*Lemma scoping_lam_close' ctx t x :
  x ∉ fv ctx -> scoping ({[ x ]} ∪ domain ctx) t -> scoping (domain ctx) (lam (t \^ x)).
Proof. Admitted.*)


Lemma scoping_named_letin Γ body x xdef :
  scoping Γ xdef ->
  x ∉ Γ ->
  scoping ({[ x ]} ∪ Γ) body ->
  scoping Γ (named_letin x xdef body).
Proof.
intros H1 H2 H3. apply scoping_letin_intro with x.
- assumption.
- apply not_elem_of_fv_close.
- assumption.
- rewrite open_close_same ; eauto with wf.
Qed.
(* #[export] Hint Resolve scoping_letin_close : scoping.*)


(*Lemma scoping_letin_close' ctx t x xdef :
  scoping (domain ctx) xdef ->
  x ∉ fv ctx ->
  scoping ({[ x ]} ∪ domain ctx) t ->
  scoping (domain ctx) (letin xdef (t \^ x)).
Proof. Admitted.*)

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

Notation "f <$> x" := (fmap f x).

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

(** [fresh_name] returns a name which is not in the current context. *)
Definition fresh_name : M name. Admitted.

(** Convenience function to build a lambda abstraction. *)
Definition mk_lambda (f : name -> M term) : M term :=
  let* x := fresh_name in
  with_decl (LAssum x)
    (named_lam x <$> f x).

(** Convenience function to build a let-expression. *)
Definition mk_letin (def : term) (f : name -> M term) : M term :=
  let* x := fresh_name in
  with_decl (LDef x def)
    (named_letin x def <$> f x).

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

Lemma wp_bind {A B} ctx (m : M A) (f : A -> M B) Φ :
  wp ctx m (fun ctx' a => wp ctx' (f a) Φ) -> wp ctx (let* x := m in f x) Φ.
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

Lemma wp_fresh_name ctx Φ :
  (forall x, x ∉ fv ctx -> Φ ctx x) -> wp ctx fresh_name Φ.
Proof. Admitted.

Lemma wp_mk_lambda f ctx Φ :
  (forall x, x ∉ fv ctx ->
    wp (LAssum x :: ctx) (f x) (fun _ body => Φ ctx (named_lam x body))) ->
  wp ctx (mk_lambda f) Φ.
Proof.
intros H. unfold mk_lambda. apply wp_bind, wp_fresh_name. intros x Hx.
specialize (H x Hx). apply wp_with_decl, wp_bind. cbn. apply H.
Qed.

Lemma wp_mk_letin def f ctx Φ :
  (forall x, x ∉ fv ctx ->
    wp (LDef x def :: ctx) (f x) (fun _ body => Φ ctx (named_letin x def body))) ->
  wp ctx (mk_letin def f) Φ.
Proof.
intros H. unfold mk_letin. apply wp_bind, wp_fresh_name. intros x Hx.
specialize (H x Hx). apply wp_with_decl, wp_bind. cbn. apply H.
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
  | [ |- wp _ fresh_name _ ] => apply wp_fresh_name
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

Fixpoint cps (n : nat) (t : term) (k : term) : M term :=
  match n with 0 => out_of_fuel | S n =>
  match t with
  | bvar i => error
  | fvar x => ret (app k (fvar x))
  | app t1 t2 =>
    cps n t1 =<< mk_lambda (fun x1 =>
    cps n t2 =<< mk_lambda (fun x2 =>
    ret (apps (fvar x1) [ fvar x2 ; k ])))
  | lam t' =>
    app k <$>
      mk_lambda (fun x =>
      mk_lambda (fun k' =>
      cps n (t' ^ x) (fvar k')))
  | letin t u =>
    cps n t =<< mk_lambda (fun v =>
    mk_letin (fvar v) (fun x =>
    cps n (u ^ x) k))
  end
  end.

(*Inductive term_view :=
| LamV : name -> term -> term_view.*)

Lemma not_elem_domain_fv x ctx :
  x ∉ fv ctx -> x ∉ domain ctx.
Proof. intros H H'. apply H. by apply domain_fv. Qed.

(** [set_solver] without any hypotheses. *)
Ltac set_solver_nohyps := set_solver +.

(** Solve a goal [scoping _ _] by applying weakening + assumption. *)
Ltac simpl_scoping_base :=
  match goal with
  | [ H : scoping ?Γ ?t |- scoping ?Γ' ?t ] =>
      by apply scoping_weaken with Γ ; [set_solver_nohyps | assumption]
  end.

(** Apply a single step of [simpl_scoping]. *)
Ltac simpl_scoping_step k :=
  lazymatch goal with
  | [ |- scoping _ (fvar _) ] => apply scoping_fvar
  | [ |- scoping _ (app _ _) ] => apply scoping_app ; k
  | [ |- scoping _ (apps _ (_ :: _)) ] => (progress cbn [apps]) ; k
  | [ |- scoping _ (named_lam _ _) ] => apply scoping_named_lam ; [| k]
  | [ |- scoping _ (named_letin _ _ _) ] => apply scoping_named_letin ; [k | | k]
  end.

(** Simplify a goal of the form [scoping Γ t]. *)
Ltac simpl_scoping :=
  (* Simplify using the rules for [scoping]. *)
  first [ simpl_scoping_base | simpl_scoping_step simpl_scoping | idtac ] ;
  (* Try to solve the remaining side conditions using fast, low-effort tactics. *)
  first [ set_solver_nohyps | eauto 4 | idtac ].

Lemma cps_safe n t k :
  {{ ctx. scoping (domain ctx) t /\ scoping (domain ctx) k }}
    cps n t k
  {{ ctx t'. scoping (domain ctx) t' }}.
Proof.
induction n in k, t |- * ; intros ctx Φ [Ht Hk] HΦ ; cbn [cps] ; [constructor|].
destruct t.
- wp_steps. apply HΦ. simpl_scoping.
- inversion Ht.
- inversion Ht ; subst. wp_steps. intros x Hx. wp_steps. intros y Hy. wp_steps.
  apply IHn.
  { split ; simpl_scoping. by apply not_elem_domain_fv. }
  intros t' Ht'. apply IHn.
  { split ; simpl_scoping. by apply not_elem_domain_fv. }
  intros t'' Ht''. apply HΦ. assumption.
- wp_steps. intros x Hx. wp_steps. intros y Hy. apply IHn.
  {
    split ; simpl_scoping.
    inversion Ht ; subst. eapply scoping_weaken ; [|apply H1].
    + set_solver.
    + apply scoping_vars in Ht. rewrite domain_fv in Ht. set_solver.
    + by apply not_elem_domain_fv.
  }
  intros t' Ht'. apply HΦ. simpl_scoping.
  + by apply not_elem_domain_fv.
  + pose proof (not_elem_domain_fv y ctx). set_solver.
- wp_steps. intros x Hx. wp_steps. intros y Hy. apply IHn.
  {
    split ; simpl_scoping.
    inversion Ht ; subst. eapply scoping_weaken ; [|apply H3].
    - set_solver.
    - apply scoping_vars in Ht. rewrite domain_fv in Ht. set_solver.
    - apply not_elem_domain_fv ; set_solver.
  }
  intros t' Ht'. apply IHn.
  {
    inversion Ht ; subst. split ; simpl_scoping.
    - by apply not_elem_domain_fv.
    - pose proof (not_elem_domain_fv y ctx). set_solver.
  }
  intros t'' Ht''. apply HΦ. assumption.
Qed.
