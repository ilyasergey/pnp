Require Import Ssreflect.ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Test.

Variable A : Type.

Theorem counterexample P : (exists x : A, ~P x) -> ~(forall x, P x).
Proof.
by case=>x H1 H2; apply: H1 (H2 x).
Qed.

Print counterexample.

End Test.
