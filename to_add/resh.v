Require Import ssreflect.

Lemma Nikov A (P : A -> A -> Prop): 
  (exists !x, exists y, P x y) -> 
  (exists !x, exists y, P y x) ->
  (exists !x, exists !y, P x y).
Proof.
case=>x1[[y1 Pxy1]] G1[x2[[y2 Pxy2]] G2]; exists y2; split.
- by exists x2; split=>// x0 Pxy0; apply: G2; exists y2.
move=>x'. move:(G1 x')=>E G3.
rewrite -E; last by case: G3=>y'; case=> Z _; exists y'.
by apply/eq_sym; apply: G1; exists x2.
Qed.


  