Require Import Reals.
(*
Notation "x ≤ y" := (x <= y)%nat (at level 70, no associativity) : nat_scope.
Notation "x ≥ y" := (x >= y)%nat (at level 70, no associativity) : nat_scope.

Notation "x ≤ y" := (x <= y)%R (at level 70, no associativity) : R_scope.
Notation "x ≥ y" := (x >= y)%R (at level 70, no associativity) : R_scope.
*)
(*** See https://coq.inria.fr/refman/addendum/canonical-structures.html ***)
Module EQ.

Record class (T : Type) := Class { cmp : T -> T -> Prop }.

Structure type := Pack { obj : Type; class_of : class obj }.

Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class _ the_cmp) := e in the_cmp.

Check op.

Arguments op {e} x y : simpl never.
Arguments Class {T} cmp.
Module theory.

Notation "x ≤ y" := (op x y) (at level 70).
End theory.

End EQ.


Import EQ.theory.
Check forall (e : EQ.type) (a b : EQ.obj e), a ≤ b.

Fail Check 3 ≤ 4.


Definition nat_leq (x y : nat) := (x <= y).

Definition nat_EQcl : EQ.class nat := EQ.Class nat_leq.

Canonical Structure nat_EQty : EQ.type := EQ.Pack nat nat_EQcl.

Check 3 ≤ 3.

Eval compute in 3 ≤ 4.
Eval compute in 4 ≤ 3.


Definition R_leq (x y : R) := (x <= y)%R.

Definition R_EQcl : EQ.class R := EQ.Class R_leq.

Canonical Structure R_EQty : EQ.type := EQ.Pack R R_EQcl.

Variable x y : R.
Check x ≤ y.
Variable m n : nat.
Check n ≤ m.






