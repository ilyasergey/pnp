(** %\chapter{Inductive Reasoning in SSReflect}% *)

From mathcomp
Require Import ssreflect eqtype ssrnat ssrbool ssrfun seq.
Module SsrStyle.

(** 

In the rest of this lecture we will be constantly relying on a series
of standard SSReflect modules, such as [ssrbool], [ssrnat] and
[eqtype], which we import right away.

*)



(**  * Structuring the proof scripts

An important part of the proof process is keeping to an established
proof layout, which helps to maintain the proofs readable and restore
the intuition driving the prover's hand.  SSReflect offers a number of
syntactic primitives that help to maintain such a layout, and in this
section we give a short overview of them. As usual, the SSReflect
reference manual provides an exhaustive formal definition of each
primitive's semantics, so we will just cover the base cases here,
hoping that the subsequent proofs will provide more intuition on
typical usage scenarios.

** Bullets and terminators

*)

Lemma andb_true_elim b c: b && c -> c = true.

Proof.
case: c.

(** 
[[
true = true

subgoal 2 (ID 15) is:
 b && false -> false = true
]]
*)

- by case: b.

(** ** Using selectors and discharging subgoals

Let us restart this proof and show an alternative way to structure the
proof script, which should account for multiple cases.

*)

Restart.

case: c; first by [].

(**
[[
  b : bool
  ============================
   b && false -> false = true
]]
*)

Restart.

case:c; [by [] | by case: b].

(** 

The script above solves the first generated goal using [by []], and
then solves the second one via [by case: b].

*)

(** ** Iteration and alternatives *)

Restart.

by do ![done | apply: eqxx | case: b | case: c].

Qed.

(** * Inductive predicates that should be functions *)

Inductive isZero (n: nat) : Prop := IsZero of n = 0.

(**

Naturally, such equality can be exploited to derived paradoxes, as the
following lemma shows:

*)

Lemma isZero_paradox: isZero 1 -> False.
Proof. by case. Qed.


(** 

However, the equality on natural numbers is, decidable, so the very
same definition can be rewritten as a function employing the boolean
equality [(==)], which will make the proofs of paradoxes even shorter
than they already are:

*)

Definition is_zero n : bool := n == 0.

Lemma is_zero_paradox: is_zero 1 -> False.
Proof. done. Qed.

(** 

That is, instead of the unavoidable case-analysis with the first
[Prop]-based definition, the functional definition made Coq compute
the result for us, deriving the falsehood automatically.

The benefits of the computable definitions become even more obvious
when considering the next example, the predicate defining whether a
natural number is even or odd. Again, we define two versions, the
inductive predicate and a boolean function.

*)

Inductive evenP n : Prop :=
  Even0 of n = 0 | EvenSS m of n = m.+2 & evenP m.

Fixpoint evenb n := if n is n'.+2 then evenb n' else n == 0.

(** 

Let us now prove a simple property: that fact that [(n + 1 + n)] is
even leads to a paradox. We first prove it for the version defined in
[Prop].

*)

Lemma evenP_contra n : evenP (n + 1 + n) -> False.
Proof.
elim: n=>//[| n Hn]; first by rewrite addn0 add0n; case=>//.

(** 
[[
  n : nat
  Hn : evenP (n + 1 + n) -> False
  ============================
   evenP (n.+1 + 1 + n.+1) -> False
]]
*)

rewrite addn1 addnS addnC !addnS. 
rewrite addnC addn1 addnS in Hn.

(**
[[
  n : nat
  Hn : evenP (n + n).+1 -> False
  ============================
   evenP (n + n).+3 -> False
]] 
*)

case=>// m /eqP.

(**

[[
  n : nat
  Hn : evenP (n + n).+1 -> False
  m : nat
  ============================
   (n + n).+3 = m.+2 -> evenP m -> False
]]
*)

by rewrite !eqSS; move/eqP=><-.
Qed.

(** 

Now, let us take a look at the proof of the same fact, but with the
computable version of the predicate [evenb].

*)

Lemma evenb_contra n: evenb (n + 1 + n) -> False.
Proof. 
elim: n=>[|n IH] //.

(** 
[[
  n : nat
  IH : evenb (n + 1 + n) -> False
  ============================
   evenb (n.+1 + 1 + n.+1) -> False
]]
*)

by rewrite addSn addnS. 
Qed.

(** 

Sometimes, though, the value "orbits", which can be advantageous for
the proofs involving [bool]-returning predicates, might require a bit
trickier induction hypotheses than just the statement required to be
proved. Let us compare the two proofs of the same fact, formulated
with [evenP] and [evennb].

*)

Lemma evenP_plus n m : evenP n -> evenP m -> evenP (n + m).
Proof.
elim=>//n'; first by move=>->; rewrite add0n.

(** 

[[
  n : nat
  m : nat
  n' : nat
  ============================
   forall m0 : nat,
   n' = m0.+2 ->
   evenP m0 -> (evenP m -> evenP (m0 + m)) -> evenP m -> evenP (n' + m)
]]
*)

move=> m'->{n'} H1 H2 H3; rewrite addnC !addnS addnC.

(**

[[
  n : nat
  m : nat
  m' : nat
  H1 : evenP m'
  H2 : evenP m -> evenP (m' + m)
  H3 : evenP m
  ============================
   evenP (m' + m).+2
]]

*)

Check EvenSS.

(** 
[[
EvenSS
     : forall n m : nat, n = m.+2 -> evenP m -> evenP n
]]
*)

apply: (EvenSS _ (m' + m))=>//.

(**

[[
  n : nat
  m : nat
  m' : nat
  H1 : evenP m'
  H2 : evenP m -> evenP (m' + m)
  H3 : evenP m
  ============================
   evenP (m' + m)
]] 

*)

by apply: H2.

Qed.

(** 

In this particular case, the resulting proof was quite
straightforward, thanks to the explicit equality [n = m.+2] in the
definition of the [EvenSS] constructor.

In the case of the boolean specification, though, the induction should
be done on the natural argument itself, which makes the first attempt
of the proof to be not entirely trivial.

*)

Lemma evenb_plus n m : evenb n -> evenb m -> evenb (n + m).
Proof.
elim: n=>[|n Hn]; first by rewrite add0n.

(** 
[[
  m : nat
  n : nat
  Hn : evenb n -> evenb m -> evenb (n + m)
  ============================
   evenb n.+1 -> evenb m -> evenb (n.+1 + m)
]]

The problem now is that, if we keep building the proof by induction on
[n] or [m], the induction hypothesis and the goal will be always
"mismatched" by one, which will prevent us finishing the proof using
the hypothesis. 

There are multiple ways to escape this vicious circle, and one of them
is to _generalize_ the induction hypothesis. To do so, let us restart
the proof.

*)

Restart.

move: (leqnn n).

(**

[[
  n : nat
  m : nat
  ============================
   n <= n -> evenb n -> evenb m -> evenb (n + m)
]]

Now, we are going to proceed with the proof by _selective_ induction
on [n], such that some of its occurrences in the goal will be a
subject of inductive reasoning (namely, the second one), and some
others will be left generalized (that is, bound by a forall-quantified
variable). We do so by using SSReflect's tactics [elim] with explicit
_occurrence selectors_. 

*)

elim: n {-2}n.

(** 

[[
  m : nat
  ============================
   forall n : nat, n <= 0 -> evenb n -> evenb m -> evenb (n + m)

subgoal 2 (ID 860) is:
 forall n : nat,
 (forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)) ->
 forall n0 : nat, n0 <= n.+1 -> evenb n0 -> evenb m -> evenb (n0 + m)
]]

The same effect could be achieved by using [elim: n {1 3 4}n], that
is, indicating which occurrences of [n] _should_ be generalized,
instead of specifying, which ones should not (as we did by means of
[{-2}n]).

*)

- by case=>//.

(** 

For the second goal, we first move some of the assumptions to the context.

*)

move=>n Hn. 

(** 
[[
  m : nat
  n : nat
  Hn : forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)
  ============================
   forall n0 : nat, n0 <= n.+1 -> evenb n0 -> evenb m -> evenb (n0 + m)
]]

We then perform the case-analysis on [n0] in the goal, which results
in two goals, one of which is automatically discharged.

*)

case=>//.

(** 

[[
  m : nat
  n : nat
  Hn : forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)
  ============================
   forall n0 : nat, n0 < n.+1 -> evenb n0.+1 -> evenb m -> evenb (n0.+1 + m)
]]

Doing _one more_ case analysis will adde one more [1] to the induction
variable [n0], which will bring us to the desired [(.+2)]-orbit.

*)

case=>// n0.

(**
[[
  m : nat
  n : nat
  Hn : forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)
  n0 : nat
  ============================
   n0.+1 < n.+1 -> evenb n0.+2 -> evenb m -> evenb (n0.+2 + m)
]]

The only thing left to do is to tweak the top assumption (by relaxing
the inequality via the [ltnW] lemma), so we could apply the induction
hypothesis [Hn].

*)

by move/ltnW /Hn=>//.
Qed.

(** ** Eliminating assumptions with a custom induction hypothesis

The functions like [evenb], with specific value orbits, are not
particularly uncommon, and it is useful to understand the key
induction principles to reason about them. In particular, the above
discussed proof could have been much more straightforward if we first
proved a different induction principle [nat2_ind] for natural numbers.

*)

Lemma nat2_ind (P: nat -> Prop): 
  P 0 -> P 1 -> (forall n, P n -> P (n.+2)) -> forall n, P n.
Proof.
move=> H0 H1 H n. 

(** 
[[
  P : nat -> Prop
  H0 : P 0
  H1 : P 1
  H : forall n : nat, P n -> P n.+2
  n : nat
  ============================
   P n
]]

Unsurprisingly, the proof of this induction principle follows the same
pattern as the proof of [evenb_plus]---generalizing the hypothesis. In
this particular case, we generalize it in the way that it would
provide an "impedance matcher" between the 1-step "default" induction
principle on natural numbers and the 2-step induction in the
hypothesis [H]. We show that for the proof it is sufficient to
establish [(P n /\ P (n.+1))]:

*)

suff: (P n /\ P (n.+1)) by case.

(** 

The rest of the proof proceeds by the standard induction on [n].

*)

by elim: n=>//n; case=> H2 H3; split=>//; last by apply: H.
Qed.

(** 

Now, since the new induction principle [nat2_ind] exactly matches the
2-orbit, we can directly employ it for the proof of the previous result.

*)

Lemma evenb_plus' n m : evenb n -> evenb m -> evenb (n + m).
Proof.
by elim/nat2_ind : n.
Qed.

(** 

Notice that we used the version of the [elim] tactics with specific
_elimination view_ [nat2_ind], different from the default one, which
is possible using the view tactical [/]. In this sense, the "standard
induction" [elim: n] would be equivalent to [elim/nat_ind: n].

*)

(** * Inductive predicates that are hard to avoid *)

Inductive beautiful (n: nat) : Prop :=
| b_0 of n = 0
| b_3 of n = 3
| b_5 of n = 5
| b_sum n' m' of beautiful n' & beautiful m' & n = n' + m'.

(** 

The number is beautiful if it's either [0], [3], [5] or a sum of two
beautiful numbers. Indeed, there are many ways to decompose some
numbers into the sum $3 * n + 5 * n$. Encoding a function,
which checks whether a number is beautiful or not, although not
impossible, is not entirely trivial (and, in particular, it's not
trivial to prove the correctness of such function with respect to the
definition above). Therefore, if one decides to stick with the
predicate definition, some operations become tedious, as, even for
constants the property should be _inferred_ rather than proved:

*)

Theorem eight_is_beautiful: beautiful 8.
Proof.
apply: (b_sum _ 3 5)=>//; first by apply: b_3. 
by apply b_5.
Qed.

Theorem b_times2 n: beautiful n ->  beautiful (2 * n).
Proof.
by move=>H; apply: (b_sum _ n n)=>//; rewrite mul2n addnn.
Qed.

(** 

In particular, the negation proofs become much less straightforward
than one would expect:

*)

Lemma one_not_beautiful n:  n = 1 -> ~ beautiful n.
Proof.
move=>E H. 

(** 

[[
  n : nat
  E : n = 1
  H : beautiful n
  ============================
   False
]]
*)

elim: H E=>n'; do?[by move=>->].
move=> n1 m' _ H2 _ H4 -> {n' n}.

(** 

Notice how the assumptions [n'] and [n] are removed from the context
(since we don't need them any more) by enumerating them using [{n' n}]
notation.

*)

case: n1 H2=>// n'=> H3.
by case: n' H3=>//; case.
Qed.

(** * Working with SSReflect libraries

We conclude this chapter with a short overview of a subset of the
standard SSReflect programming and naming policies, which will,
hopefully, simplify the use of the libraries in a standalone
development.

** Notation and standard operation properties

SSReflect's module [ssrbool] introduces convenient notation for
predicate connectives, such as [/\] and [\/]. In particular, multiple
conjunctions and disjunctions are better to be written as [[ /\ P1, P2
& P3]] and [[ \/ P1, P2 | P3]], respectively, opposed to [P1 /\ P2 /\
P3] and [P1 \/ P2 \/ P3]. The specific notation makes it more
convenient to use such connectives in the proofs that proceed by case
analysis. Compare.

*)

Lemma conj4 P1 P2 P3 P4 : P1 /\ P2 /\ P3 /\ P4 -> P3.
Proof. by case=>p1 [p2][p3]. Qed.

Lemma conj4' P1 P2 P3 P4 : [ /\ P1, P2, P3 & P4] -> P3.
Proof. by case. Qed.


Locate "_ ^~ _".
(** 
[[
"f ^~ y" := fun x => f x y     : fun_scope
]]

For instance, this is how one can now express the partially applied
function, which applies its argument to the list [[:: 1; 2; 3]]:

*)

Check map ^~ [:: 1; 2; 3].

(**

[[
map^~ [:: 1; 2; 3]
     : (nat -> ?2919) -> seq ?2919
]]

Finally, [ssrfun] defines a number of standard operator properties,
such as commutativity, distributivity etc in the form of the
correspondingly defined predicates: [commutative], [right_inverse]
etc. For example, since we have now [ssrbool] and [ssrnat] imported,
we can search for left-distributive operations defined in those two
modules (such that they come with the proofs of the corresponding
predicates):

*)

Search _ (left_distributive _).

(**

[[
andb_orl  left_distributive andb orb
orb_andl  left_distributive orb andb
andb_addl  left_distributive andb addb
addn_maxl  left_distributive addn maxn
addn_minl  left_distributive addn minn
...
]]
*)

(** ** A library for lists

For instance, properties of some of the functions, such as _list
reversal_ are simpler to prove not by the standard "direct" induction
on the list structure, but rather iterating the list from its last
element, for which the [seq] library provides the necessary definition
and induction principle:

[[
Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].
]]

*)

Check last_ind.

(**

[[
last_ind
     : forall (T : Type) (P : seq T -> Type),
       P [::] ->
       (forall (s : seq T) (x : T), P s -> P (rcons s x)) ->
       forall s : seq T, P s
]]

To demonstrate the power of the library for reasoning with lists, let
us prove the following property, known as _Dirichlet's box principle_
(sometimes also referred to as _pigeonhole principle_).

*)

Variable A : eqType.

Fixpoint has_repeats (xs : seq A) :=
  if xs is x :: xs' then (x \in xs') || has_repeats xs' else false.

(** 

The following lemma states that for two lists [xs1] and [xs2], is the
size [xs2] is strictly smaller than the size of [xs1], but
nevertheless [xs1] as a set is a subset of [xs2] then there ought to
be repetitions in [xs1].

*)

Theorem dirichlet xs1 xs2 :
        size xs2 < size xs1 -> {subset xs1 <= xs2} -> has_repeats xs1.
Proof.

(** 

First, the proof scripts initiates the induction on the structure of
the first, "longer", list [xs1], simplifying and moving to the context
some hypotheses in the "step" case (as the [nil]-case is proved
automatically).

*)

elim: xs1 xs2=>[|x xs1 IH] xs2 //= H1 H2. 

(**
[[
  x : A
  xs1 : seq A
  IH : forall xs2 : seq A,
       size xs2 < size xs1 -> {subset xs1 <= xs2} -> has_repeats xs1
  xs2 : seq A
  H1 : size xs2 < (size xs1).+1
  H2 : {subset x :: xs1 <= xs2}
  ============================
   (x \in xs1) || has_repeats xs1
]]
*)

case H3: (x \in xs1) => //=.
(**
[[
  ...
  H3 : (x \in xs1) = false
  ============================
   has_repeats xs1
]]
*)

pose xs2' := filter (predC (pred1 x)) xs2.
apply: (IH xs2'); last first.

(**
[[
  ...
  H2 : {subset x :: xs1 <= xs2}
  H3 : (x \in xs1) = false
  xs2' := [seq x <- xs2 | (predC (pred1 x)) x0] : seq A
  ============================
   {subset xs1 <= xs2'}

subgoal 2 (ID 5716) is:
 size xs2' < size xs1
]]
*)

- move=>y H4; move: (H2 y); rewrite inE H4 orbT mem_filter /=.
  by move => -> //; case: eqP H3 H4 => // ->->. 

(** 

The second goal requires to prove the inequality, which states that
after removal of [x] from [xs2], the length of the resulting list
[xs2] is smaller than the length of [xs1]. 

*)

rewrite ltnS in H1; apply: leq_trans H1. 
rewrite -(count_predC (pred1 x) xs2) -addn1 addnC. 
rewrite /xs2' size_filter leq_add2r -has_count.

(**
[[
  ...
  H2 : {subset x :: xs1 <= xs2}
  H3 : (x \in xs1) = false
  xs2' := [seq x <- xs2 | (predC (pred1 x)) x0] : seq A
  ============================
   has (pred1 x) xs2
]]
*)

by apply/hasP; exists x=>//=; apply: H2; rewrite inE eq_refl.
Qed.


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

Lemma div2_le n: div2 n <= n.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 
---------------------------------------------------------------------
Exercise [Some facts about beautiful numbers]
---------------------------------------------------------------------

Proof the following theorem about beautiful numbers.

Hint: Choose wisely, what to build the induction on.
*)

Lemma b_timesm n m: beautiful n ->  beautiful (m * n).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



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

Hint: As usual, do not hesitate to use the [Search] utility for
finding the necessary rewriting lemmas from the [ssrnat] module.  
*)


Lemma gorgeous_plus13 n: gorgeous n -> gorgeous (n + 13).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma beautiful_gorgeous (n: nat) : beautiful n -> gorgeous n.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma g_times2 (n: nat): gorgeous n -> gorgeous (n * 2).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma gorgeous_beautiful (n: nat) : gorgeous n -> beautiful n.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



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
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma gorg3 n : gorgeous (3 * n).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 

Next, we can establish by induction the following criteria using the
lemmas [repr3] and [gorg3] in the subgoals of the proof.

*)

Lemma gorg_criteria n : n >= 8 -> gorgeous n.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 

This makes the proof of the following lemma trivial.

*)

Lemma gorg_refl' n: n >= 8 -> reflect (gorgeous n) true.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



(** 

- In the second stage of the proof of reflection, we will
  need to prove four totally boring but unavoidable lemmas.

Hint: The rewriting lemmas [addnC] and [eqSS] from the [ssrnat]
module might be particularly useful here.

*)

Lemma not_g1: ~(gorgeous 1).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma not_g2: ~(gorgeous 2).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma not_g4: ~(gorgeous 4).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma not_g7: ~(gorgeous 7).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 

We can finally provide prove the ultimate reflection predicate,
relating [gorgeous] and [gorgeous_b].

*)
Lemma gorg_refl n : reflect (gorgeous n) (gorgeous_b n).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


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
(* fill in your implemenation istead of the [false] stub *)
  false.

(** 

Next, prove the following lemma, relating [appears_in] and list
concatenation [++].

*)

Lemma appears_in_app (xs ys : seq X) (x:X): 
     appears_in x (xs ++ ys) = appears_in x xs || appears_in x ys.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


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
(* fill in your proof here instead of [admit] *)
Admitted.


End Appears_bool.

Eval compute in appears_in (EqType nat _) 1 [:: 1; 2; 3].
(* true *)

Eval compute in appears_in (EqType nat _) 1 [:: 2; 4; 3].
(* false *)


(** 
---------------------------------------------------------------------
Exercise [Element inclusion predicate for lists in Prop]
---------------------------------------------------------------------

For types [Y] with propositional equality, define the [appears_inP]
predicate, which returns [Prop].

*)

Section Appears_Prop.
Variable Y: Type.

Variable appears_inP : forall (a: Y) (l: seq Y), Prop.
(* Replace Variable by the actual implementation *)

(**
Prove the lemma [appears_in_appP]:
*)

Lemma appears_in_appP (xs ys : seq Y) (x:Y): 
     appears_inP x (xs ++ ys) <-> appears_inP x xs \/ appears_inP x ys.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 

Finally, define the [Prop]-versions of the [disjoint] and [no_repeat]
predicates: [disjointP] and [no_repeatP] and prove the following lemma
relating them.

*)

Variable disjointP : forall (l1 l2: seq Y), Prop.
(* Replace Variable by the actual implementation *)

Variable no_repeatsP : forall (ls : seq Y), Prop. 
(* Replace Variable by the actual implementation *)

Theorem norep_disj_appP l1 l2: 
  no_repeatsP l1 -> no_repeatsP l2 -> disjointP l1 l2 -> no_repeatsP (l1 ++ l2).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


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

Prove the lemma [allP], stating that the two representations are
equivalent whenever [P] and [test] are equivalent.

*)


Variable all : forall {X} (P : X -> Prop) (ls: seq X), Prop.
(* Replace Variable by the actual implementation *)

Variable allb : forall {X : Type} (test : X -> bool) (ls : seq X), bool.
(* Replace Variable by the actual implementation *)

Lemma allP T P test: 
  (forall x: T, reflect (P x) (test x)) -> 
  forall ls, reflect (all P ls) (allb test ls).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


End SsrStyle.


