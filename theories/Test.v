Declare ML Module "meta-programming-experiments.plugin".

Inductive M : Type -> Type :=
| Ret {A} : A -> M A
| Bind {A B} : M A -> (A -> M B) -> M B
| FreshNat : unit -> M nat.

Definition prog : M nat :=
  FreshNat tt.

Extract prog.