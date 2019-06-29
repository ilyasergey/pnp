From mathcomp
Require Import ssreflect ssrfun eqtype ssrnat ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive my_eq (A : Type) (x : A) : A -> Prop :=  my_eq_refl : my_eq x x.
Notation "x === y" := (my_eq x y) (at level 70).

Lemma my_eq_sym A (x y: A) : x === y -> y === x.
Proof. by case. Qed.

Lemma disaster : 2 === 1 -> False.
Proof.
move=> H.
pose D x := if x is 2 then False else True.
have D1: D 1 by [].
by case: H D1. 
Qed.

(**
---------------------------------------------------------------------
Exercise [Discriminating [===]]
---------------------------------------------------------------------
Let us change the statement of a lemma [disaster] for a little bit:
*)

Lemma disaster2 : 1 === 2 -> False.

(**
Now, try to prove it using the same scheme. What goes wrong and how to
fix it?
*)
Proof.
(* by move=>H; move/disaster: (my_eq_sym H). *)
Proof.
move=> H.
pose D x := if x is 1 then False else True.
have D2: D 2. 
by [].
by case: H D2=> /=.
Qed.

(**
---------------------------------------------------------------------
Exercise [Fun with rewritings]
---------------------------------------------------------------------
Prove the following lemma by using the [rewrite] tactics.

*)

Lemma rewrite_is_fun T (f : T -> T -> T) (a b c : T):
  commutative f -> associative f ->
  f (f b a) c = f a (f c b).     
Proof.
move=> H1 H2.
by rewrite [(f b a)]H1 -H2 [(f c b)]H1.
Qed.


(**
---------------------------------------------------------------------
Exercise [Properties of maxn]
---------------------------------------------------------------------
Prove the following lemmas about [maxn].
*)

Lemma max_l m n: n <= m -> maxn m n = m.
Proof.
rewrite /maxn. 
by case: (leqP n m)=>//.
Qed.

Lemma succ_max_distr_r n m : (maxn n m).+1 = maxn (n.+1) (m.+1).
Proof.
rewrite /maxn.
case: leqP=>//H; case:leqP=>//.
- by rewrite -[n.+1]addn1 -[m.+1]addn1 ltn_add2r ltnNge H.
by rewrite ltnS leqNgt H.
Qed.

Lemma plus_max_distr_l m n p: maxn (p + n) (p + m) = p + maxn n m.
Proof.
rewrite /maxn.
case: leqP=>// H1; case: leqP=>//.
- suff: m <= n by rewrite ltnNge=>H; move/negP.
  by rewrite leq_add2l in H1.
suff: n < m by move=>H; rewrite leqNgt H. 
by rewrite ltn_add2l in H1.
Qed.

(** 

Hint: it might be useful to employ the lemmas [ltnNge], [leqNgt],
[ltnS] and similar to them from SSReflect's [ssrnat] module. Use the
[Search] command to find propositions that might help you to deal with
the goal.

Hint: Forward-style reasoning via [suff] and [have] might be more
intuitive.

Hint: A hypothesis of the shape [H: n < m] is a syntactic sugar for
[H: n < m = true], since [n < m] in fact has type [bool], as will be
explained in the next lecture.

*)

(**
---------------------------------------------------------------------
Exercise [More custom rewriting rules]
---------------------------------------------------------------------

Let us consider an instance of a more sophisticated custom rewriting
rule, which now encodes a three-variant truth table for the ordering
relations on natural numbers.

*)

Inductive nat_rels m n : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : nat_rels m n true false false
  | CompareNatGt of m > n : nat_rels m n false true false
  | CompareNatEq of m = n : nat_rels m n false false true.

(** 

The following rewriting lemma establishes a truth table for
[nat_rels]. Step through the proofs (splitting the combined tactics
whenever it's necessary) to see what's going on.

*)

Lemma natrelP m n : nat_rels m n (m < n) (n < m) (m == n).
Proof.
rewrite ltn_neqAle eqn_leq; case: ltnP; first by constructor.
by rewrite leq_eqVlt orbC; case: leqP; constructor; first exact/eqnP.
Qed.

(** 
Let us define the minimum function [minn] on natural numbers as
follows:
*)

Definition minn m n := if m < n then m else n.

(**
Prove the following lemma about [minm] and [maxn]:
*)

Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Proof.
rewrite /minn /maxn; by case: natrelP=>//; rewrite addnC.
Qed.
