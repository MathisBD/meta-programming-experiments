
type __ = Obj.t

type unit0 =
| Tt

type nat =
| O
| S of nat

type 'x m =
| Ret of 'x
| Bind of __ m * (__ -> 'x m)
| FreshNat of unit0

val prog : nat m
