Require Import Ssreflect.ssreflect.

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

Require Import Ssreflect.eqtype Ssreflect.ssrbool.

Definition Q x y : Prop := 
  (x == true) && (y == true) || (x == false).

Lemma qlm : (exists !x, exists !y, Q x y).
Proof.
exists true; split; first by exists true; split=> //; case=>//.
case=>//; rewrite /Q; case; case=>/=; case=>_ G.
- by move:(G false (eqxx false)).
by move:(G true (eqxx true)). 
Qed.

Lemma Nikov2 : 
  (forall A (P : A -> A -> Prop),
   (exists !x, exists !y, P x y) ->
   (exists !x, exists y, P x y) /\ (exists !x, exists y, P y x)) ->
  False.
Proof.
move/(_ _ _ qlm); rewrite /Q/=; case=> H1 H2.
case: H1; case; case; case; case=> //= _.
- move=>G1; move:(G1 false)=>/=G2. 
  by suff: true = false by []; last by apply: G2; exists true.
- move=>G1; move:(G1 true)=>/=G2. 
  by suff: false = true by []; last by apply: G2; exists true.
- move=>G1; move:(G1 true)=>/=G2. 
  by suff: false = true by []; last by apply: G2; exists true.
Qed.


