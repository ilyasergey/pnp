From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive beautiful (n: nat) : Prop :=
| b_0 of n = 0
| b_3 of n = 3
| b_5 of n = 5
| b_sum n' m' of beautiful n' & beautiful m' & n = n' + m'.

(*******************************************************************)
(**                     * Exercices *                              *)
(*******************************************************************)

(** 
---------------------------------------------------------------------
Exercise [Integer binary division]
---------------------------------------------------------------------

Let us define the binary division function [div2] as follows.
*)

Fixpoint div2 (n: nat) := if n is p.+2 then (div2 p).+1 else 0.

(** 

Prove the following lemma directly by induction on [n], _without_
using the [nat2_ind] induction principle. Then prove it using
[nat2_ind].

*)

Lemma div2orb n : div2 (n.+2) = (div2 n).+1.
Proof. by case: n=>//. Qed.

Lemma div2_le n: div2 n <= n.
Proof.
suff: (div2 n <= n) /\ (div2 n.+1 <= n.+1) by case.
elim: n=>//[n].
case: n=>// n; rewrite !div2orb; case=>H1 H2.
split=>//.
rewrite -ltnS in H1.
by move: (ltn_trans H1 (ltnSn n.+2)).
Qed.

Lemma nat2_ind (P: nat -> Prop): 
  P 0 -> P 1 -> (forall n, P n -> P (n.+2)) -> forall n, P n.
Proof.
move=> H0 H1 H n. 
suff: (P n /\ P (n.+1)) by case.
by elim: n=>//n; case=> H2 H3; split=>//; last by apply: H.
Qed.

Lemma div2_le' n: div2 n <= n.
Proof.
elim/nat2_ind : n=>//= n Hn. 
by rewrite ltnS leqW //.
Qed.

(** 
---------------------------------------------------------------------
Exercise [Some facts about beautiful numbers]
---------------------------------------------------------------------

Proof the following theorem about beautiful numbers.

Hint: Choose wisely, what to build the induction on.
*)

Lemma b_timesm n m: beautiful n ->  beautiful (m * n).
Proof.
elim:m=>[_|m Hm Bn]; first by rewrite mul0n; apply: b_0.
move: (Hm Bn)=> H1.
by rewrite mulSn; apply: (b_sum _ n (m * n))=>//.
Qed.


(**
---------------------------------------------------------------------
Exercise [Gorgeous numbers]
---------------------------------------------------------------------

To practice with proofs by induction, let us consider yet another
inductive predicate, defining which of natural numbers are _gorgeous_.

*)

Inductive gorgeous (n: nat) : Prop :=
| g_0 of n = 0
| g_plus3 m of gorgeous m & n = m + 3
| g_plus5 m of gorgeous m & n = m + 5.

(** 
Prove by induction the following statements about gorgeous numbers.

Hint: As usual, do not hesitate to use the [Search] utility for finding the
necessary rewriting lemmas from the [ssrnat] module.
*)


Lemma gorgeous_plus13 n: gorgeous n -> gorgeous (n + 13).
Proof.
move=> H.
apply: (g_plus5 _ (n + 8))=>//; last by rewrite -addnA; congr (_ + _).
apply: (g_plus5 _ (n + 3)); last by rewrite -addnA; congr (_ + _).
by apply: (g_plus3 _ n). 
Qed.

Lemma beautiful_gorgeous (n: nat) : beautiful n -> gorgeous n.
Proof.
elim=>n'{n}=>//.
- by move=>->; apply g_0.
- by move=>->; apply: (g_plus3 _ 0)=>//; apply g_0.
- by move=>->; apply: (g_plus5 _ 0)=>//; apply g_0.
move=> n m H1 H2 H3 H4->{n'}. 
elim: H2; first by move=>_->; rewrite add0n.
by move=> n' m' H5 H6->; rewrite addnAC; apply: (g_plus3 _ (m' + m)).
by move=> n' m' H5 H6->; rewrite addnAC; apply: (g_plus5 _ (m' + m)).
Qed.

Lemma g_times2 (n: nat): gorgeous n -> gorgeous (n * 2).
Proof.
rewrite muln2.
elim=>{n}[n Z|n m H1 H2 Z|n m H1 H2 Z]; subst n; first by rewrite double0; apply g_0.
- rewrite doubleD -(addnn 3) addnA.
  by apply: (g_plus3 _ (m.*2 + 3))=>//; apply: (g_plus3 _ m.*2)=>//.
rewrite doubleD -(addnn 5) addnA.
by apply: (g_plus5 _ (m.*2 + 5))=>//; apply: (g_plus5 _ m.*2)=>//.
Qed.

Lemma gorgeous_beautiful (n: nat) : gorgeous n -> beautiful n.
Proof.
elim=>{n} -n=>//.
- by move=>->; apply: b_0.
- move=>m H1 H2->{n}.
  by move: (b_sum (m + 3) m 3 H2)=>H; apply: H=>//; apply: b_3.
- move=>m H1 H2->{n}.
  by move: (b_sum (m + 5) m 5 H2)=>H; apply: H=>//; apply: b_5.
Qed.


(** 
---------------------------------------------------------------------
Exercise [Gorgeous reflection]
---------------------------------------------------------------------

Gorgeous and beautiful numbers, defining, in fact, exactly the same
subset of [nat] are a particular case of Frobenius coin problem, which
asks for the largest integer amount of money, that cannot be obtained
using only coins of specified denominations.  In the case of
[beautiful] and [gorgeous] numbers we have two denominations
available, namely 3 and 5. An explicit formula exists for the case
of only two denominations n_1 and n_2, which allows one to compute
the Frobenius number as 

g(n_1, n_2) = n_1 * n_2 - n_1 - n_2. 

That said, for the case n_1 = 3 and n_2 = 5 the Frobenius number is 7,
which means that all numbers greater or equal than 8 are in fact
beautiful and gorgeous (since the two are equivalent, as was
established by the previous exercise).

In this exercise, we suggest the reader to prove that the efficient
procedure of "checking" for gorgeousness is in fact correct. First,
let us defined the following candidate function.

*)

Fixpoint gorgeous_b n : bool := match n with 
 | 1 | 2 | 4 | 7 => false
 | _ => true
 end. 

(** 

The ultimate goal of this exercise is to prove the proposition
[reflect (gorgeous n) (gorgeous_b n)], which would mean that the two
representations are equivalent. Let us divide the proof into two
stages:

- The first stage is proving that all numbers greater or equal than
  8 are gorgeous. To prove thism it might be useful to have the
  following two facts established:

Hint: Use the tactic [constructor i] to prove a goal, which is an
n-ary disjunction, which is satisfied if its i-th disjunct is true.

*)
Lemma repr3 n : n >= 8 -> 
  exists k, [\/ n = 3 * k + 8, n = 3 * k + 9 | n = 3 * k + 10].
Proof.
elim: n=>// n Ih.
rewrite leq_eqVlt; case/orP.
- by rewrite eqSS=>/eqP<-; exists 0; rewrite muln0 add0n; constructor.
case/Ih=>k; case=>->{n Ih}.
- by exists k; constructor 2; rewrite -addn1 -addnA addn1.
- by exists k; constructor 3; rewrite -addn1 -addnA addn1.
exists (k.+1); constructor 1.  
by rewrite mulnSr -addn1 -2!addnA; congr (_ + _).
Qed.

Lemma gorg3 n : gorgeous (3 * n).
Proof.
elim: n=>//[|n Ih]; first by apply: g_0; rewrite muln0.
by rewrite mulnSr; apply: (g_plus3 _ (3*n)).
Qed.

(** 

Next, we can establish by induction the following criteria using the
lemmas [repr3] and [gorg3] in the subgoals of the proof.

*)

Lemma gorg_criteria n : n >= 8 -> gorgeous n.
Proof.
case/repr3=>k; case=>->{n}.
- apply: (g_plus5 _ (3*k + 3)); last by rewrite -addnA.
  by apply: (g_plus3 _ (3*k))=>//; apply: gorg3.
- apply: (g_plus3 _ (3*k + 6))=>//; last by rewrite -addnA.
  apply: (g_plus3 _ (3*k + 3))=>//; last by rewrite -addnA.
  by apply: (g_plus3 _ (3*k))=>//; apply: gorg3.
apply: (g_plus5 _ (3*k + 5))=>//; last by rewrite -addnA.
by apply: (g_plus5 _ (3*k))=>//; apply: gorg3.
Qed.

(** 

This makes the proof of the following lemma trivial.

*)

Lemma gorg_refl' n: n >= 8 -> reflect (gorgeous n) true.
Proof. by move/gorg_criteria=>H; constructor. Qed.

(** 

- In the second stage of the proof of reflection, we will
  need to prove four totally boring but unavoidable lemmas.

Hint: The rewriting lemmas [addnC] and [eqSS] from the [ssrnat]
module might be particularly useful here.

*)

Lemma not_g1: ~(gorgeous 1).
Proof.
case=>//n Ih /eqP; first by rewrite addn3 eqSS. 
by rewrite addnC eqSS.  
Qed.

Lemma not_g2: ~(gorgeous 2).
Proof.
case=>//n Ih /eqP; first by rewrite addn3 eqSS. 
by rewrite addnC eqSS.  
Qed.

Lemma not_g4: ~(gorgeous 4).
Proof.
case=>//n Ih /eqP; last by rewrite addnC eqSS.  
case: n Ih=>//n Ih.
rewrite addnC !eqSS. move/eqP=>Z; subst n. 
by apply:not_g1.
Qed.

Lemma not_g7: ~(gorgeous 7).
Proof.
case=>//n Ih /eqP; case: n Ih=>//n Ih;
  rewrite addnC !eqSS; move/eqP=>Z; subst n. 
- by apply:not_g4. 
by apply:not_g2. 
Qed.

(** 

We can finally provide prove the ultimate reflection predicate,
relating [gorgeous] and [gorgeous_b].

*)
Lemma gorg_refl n : reflect (gorgeous n) (gorgeous_b n).
Proof.
case: n=>/=[|n]; first by constructor; apply:g_0.
case: n=>/=[|n]; first by constructor; apply: not_g1.
case: n=>/=[|n]; first by constructor; apply: not_g2.
case: n=>/=[|n]. 
- constructor; apply:(g_plus3 _ 0); first by apply g_0.
  by rewrite add0n.
case: n=>/=[|n]; first by constructor; apply: not_g4.
case: n=>/=[|n].
- constructor; apply:(g_plus5 _ 0); first by apply g_0.
  by rewrite add0n.
case: n=>/=[|n].
- constructor; apply:(g_plus3 _ 3)=>//.
  apply:(g_plus3 _ 0); first by apply g_0.
  by rewrite add0n.
case: n=>/=[|n]; first by constructor; apply: not_g7.
suff X: (n.+4.+4 >= 8); last by [].
by apply:(gorg_refl').
Qed.

(** 
---------------------------------------------------------------------
Exercise [Boolean element inclusion predicate for lists]
---------------------------------------------------------------------

Assuming a type [X] with the boolean equality (i.e., elements of [X]
can be compared for being equal using the [==] operator returning
[true] or [false]), define a recursive funciton [appears_in] on lists
that takes an element [a : X], a list [l : seq X] and returns a
boolean value indicating whether [a] appears in [l] or not.

*)

Section Appears_bool.
Variable X: eqType.

Fixpoint appears_in (a: X) (l: seq X) : bool :=
  if l is x::xs 
  then if x == a then true else  appears_in a xs
  else false.

(** 

Next, prove the following lemma, relating [appears_in] and list
concatenation [++].

*)

Lemma appears_in_app (xs ys : seq X) (x:X): 
     appears_in x (xs ++ ys) = appears_in x xs || appears_in x ys.
Proof.
elim: xs=>//= a ls Hi. 
case: (a == x).
by simpl.
by [].
Qed.

(** 

Let us define the functions [disjoint] and [no_repeats] using
[appears_in] as follows:

*)

Fixpoint disjoint (l1 l2: seq X): bool := 
  if l1 is x::xs then ~~(appears_in x l2) && disjoint xs l2 else true.

Fixpoint no_repeats (ls : seq X) := 
  if ls is x :: xs then ~~ (appears_in x xs) && no_repeats xs else true.

(** 

Finally, prove the following lemma, realting [no_repeats] and
[disjoint].

*)

Theorem norep_disj_app l1 l2: 
  no_repeats l1 -> no_repeats l2 -> disjoint l1 l2 -> no_repeats (l1 ++ l2).
Proof.
elim: l1=>//= x xs Hi H1 H2 H3; apply/andP; split; first last.
- by apply: Hi=>//; [case/andP: H1=>// | case/andP: H3=>//].
rewrite appears_in_app. 
by apply/norP; split; [case/andP: H1=>// | case/andP: H3=>//].
Qed.

End Appears_bool.

Eval compute in appears_in (EqType nat _) 1 [:: 1; 2; 3].
Eval compute in appears_in (EqType nat _) 1 [:: 2; 4; 3].


(** 
---------------------------------------------------------------------
Exercise [Element inclusion predicate for lists in Prop]
---------------------------------------------------------------------

For types [Y] with propositional equality, define the [appears_inP]
predicate, which returns [Prop].

*)

Section Appears_Prop.
Variable Y: Type.

Fixpoint appears_inP (a: Y) (l: seq Y) : Prop :=
  if l is x::xs 
  then x = a \/ appears_inP a xs
  else False.

(**

Prove the lemma [appears_in_appP]:

Lemma appears_in_appP (xs ys : seq Y) (x:Y): 
     appears_inP x (xs ++ ys) <-> appears_inP x xs \/ appears_inP x ys.

*)

Lemma appears_in_appP (xs ys : seq Y) (x:Y): 
     appears_inP x (xs ++ ys) <-> appears_inP x xs \/ appears_inP x ys.
Proof.
split; elim: xs=>[| a ls Hi].
- by right.
- rewrite cat_cons; case.
  - by left; left.
  by case/Hi; [left|]; right. 
- by rewrite cat0s; case.
by case=>//=; intuition.
Qed.

(** 

Finally, define the [Prop]-versions of the [disjoint] and [no_repeat]
predicates: [disjointP] and [no_repeatP] and prove the following lemma
relating them:

Theorem norep_disj_appP l1 l2: 
  no_repeatsP l1 -> no_repeatsP l2 -> disjointP l1 l2 -> no_repeatsP (l1 ++ l2).

*)

Fixpoint disjointP (l1 l2: seq Y) := 
  if l1 is x::xs then ~(appears_inP x l2) /\ disjointP xs l2 else True.

Fixpoint no_repeatsP (ls : seq Y) := 
  if ls is x :: xs then ~(appears_inP x xs) /\ no_repeatsP xs else True.

Theorem norep_disj_appP l1 l2: 
  no_repeatsP l1 -> no_repeatsP l2 -> disjointP l1 l2 -> no_repeatsP (l1 ++ l2).
Proof.
elim: l1=>//= x xs Hi H1 H2 H3; split; first last.
- by apply: Hi=>//; [case: H1=>// | case: H3=>//].
rewrite appears_in_appP. 
by case; [case: H1| case: H3].
Qed.

End Appears_Prop.

(** 
---------------------------------------------------------------------
Exercise ["All" predicate for lists]
---------------------------------------------------------------------

Define two version of version of "all-elements-satisfy" predicate for
lists. 

- The version [all] takes a type [X], a predicate [P : X -> Prop] and
  a list [ls: seq X] and returns element of sort [Prop] which carries
  a proof that all elements of ls satisfy [P].

- The decidable version [allb] takes a type [X], a predicate [test : X
  -> bool] and a list [ls: seq X], and returns a boolean result.

Prove the following lemma, stating that the two representations are
equivalent whenever [P] and [test] are equivalent:

Lemma allP T P test: 
  (forall x: T, reflect (P x) (test x)) -> 
  forall ls, reflect (all P ls) (allb test ls).
*)


Fixpoint all {X} (P : X -> Prop) (ls: seq X): Prop := 
  if ls is x::xs then P x /\ all P xs else True.

Fixpoint allb {X : Type} (test : X -> bool) (ls : seq X) : bool :=
  if ls is x::xs then test x && allb test xs else true.

Lemma allP T P test: 
  (forall x: T, reflect (P x) (test x)) -> 
  forall ls, reflect (all P ls) (allb test ls).
Proof.
move=>H; elim=>//=[| x xs Ih]; first by constructor.
case X: (test x)=>/=; last by constructor; case; move/H; rewrite X.
case Y: (allb test xs); constructor.
- by split; [apply/H | case: Ih Y]. 
by case: Ih Y=>// H1 _; case.
Qed.

