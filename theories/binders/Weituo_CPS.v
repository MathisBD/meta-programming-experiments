From Stdlib Require Import Bool Nat List String Lia.
From Stdlib.Classes Require Import Morphisms.
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
  | letin t u => letin (rename r t) (rename (rup r) u)
  end.

Notation "↑" := rshift.
Notation "r1 '>>' r2" := (rcomp r1 r2) (at level 40, left associativity).

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

Lemma eqb_name_false n n' : n <> n' -> eqb_name n n' = false.
Proof. intros H. destruct (eqb_name_spec n n') ; auto. now exfalso. Qed.

(**************************************************************************)
(** *** State. *)
(**************************************************************************)

Record state := mkstate {
  d_vars : list name ; (** dest variables. *)
  sd_ren : ren (** renaming from source to dest. *)
}.

Fixpoint lookup_var (i : nat) (x : name) (vars : list name) : nat :=
  match vars with
  | [] => 0 (* should not happen. *)
  | y :: vars' =>
    if eqb_name x y then i
    else lookup_var (i+1) x vars'
  end.

(** Lookup the index corresponding to [x]. *)
Definition idx_of (x : name) (s : state) : nat :=
  lookup_var 0 x (d_vars s).

Axiom fresh_name : gset name -> name.
Axiom fresh_name_spec : forall xs, fresh_name xs ∉ xs.

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
  state -> result (state * A).

Definition ret {A} (x : A) : M A :=
  fun s => Success (s, x).

Definition bind {A B} (mx : M A) (f : A -> M B) : M B :=
  fun s =>
    match mx s with
    | Success (s, x) => f x s
    | OutOfFuel => OutOfFuel
    | Error => Error
    end.

Notation "x '>>=' f" := (bind x f) (at level 50, no associativity).
Notation "f '=<<' x" := (bind x f) (at level 50, no associativity).

(** [let*] monadic notation. *)
Notation "'let*' x ':=' t 'in' u" := (bind t (fun x => u))
  (at level 100, right associativity, t at next level, x pattern).

Definition fmap {A B} (f : A -> B) (mx : M A) : M B :=
  let* x := mx in
  ret (f x).

(** Signal fuel is out. *)
Definition out_of_fuel {A} : M A := fun ctx => OutOfFuel.

(** Fail. *)
Definition error {A} : M A := fun ctx => Error.

(** Read the state. *)
Definition get : M state :=
  fun s => Success (s, s).

Definition gets {A} (f : state -> A) : M A :=
  fun s => Success (s, f s).

(** Replace the state. *)
Definition put (s : state) : M unit :=
  fun _ => Success (s, tt).

Definition mk_var : M name :=
  let* s := get in
  let x := fresh_name $ list_to_set $ d_vars s in
  let s' := mkstate (x :: d_vars s) (sd_ren s >> ↑) in
  let* _ := put s' in
  ret x.

Definition kp_var : M name :=
  let* s := get in
  let x := fresh_name $ list_to_set $ d_vars s in
  let s' := mkstate (x :: d_vars s) (rup (sd_ren s)) in
  let* _ := put s' in
  ret x.

Definition mk_lambda (f : name -> M term) : M term :=
  let* x := mk_var in f x.

Definition kp_lambda (f : name -> M term) : M term :=
  let* x := kp_var in f x.

(**************************************************************************)
(** *** CPS translation. *)
(**************************************************************************)

Fixpoint cps (n : nat) (t : term) (k : term) : M term :=
  match n with 0 => out_of_fuel | S n =>
  match t with
  | var i => ret (app k (var i))
  | app t1 t2 =>
    cps n t1 =<< mk_lambda (fun x1 =>
    (*let* r := gets sd_ren in*)
    cps n (rename (lift0 1) t2) =<< mk_lambda (fun x2 =>
    let* i1 := gets (idx_of x1) in
    let* i2 := gets (idx_of x2) in
    (*let* r := gets sd_ren in*)
    ret (apps (var i1) [ var i2 ; rename (lift0 2) k ])))
  | lam t' =>
    let* body :=
      kp_lambda (fun x =>
      mk_lambda (fun k' =>
      (*let* r := gets sd_ren in*)
      let* ik' := gets (idx_of k') in
      cps n (rename (lift0 2) t') (var ik')))
    in
    ret (app k body)
  | letin t u => ret t
    (*cps n t =<< mk_lambda (fun v =>
    let* iv := gets (idx_of v) in
    kk_letin (var iv) (fun x =>
    cps n (rename (lift 1 1) u) (rename (lift0 2) k)))*)
  end
  end.
