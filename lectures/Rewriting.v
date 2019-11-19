(** %\chapter{Equality and Rewriting Principles}% *)

From mathcomp
Require Import ssreflect ssrfun eqtype ssrnat ssrbool.

Module Rewriting.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Propositional equality in Coq *)

Locate "_ = _".

(**
[[
"x = y" := eq x y    : type_scope
]]
*)

Print eq.

(**
[[
Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : eq x x
]]

The type of its only constructor [eq_refl] is a bit misleading, as it
looks like it is applied to two arguments: [x] and ... [x]. To
disambiguate it, we shall put some parentheses, so, it fact, it should
read as

[[
Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : (eq x) x
]]

That is, the constructor [eq_refl] delivers an element of type [(eq
x)], whose _parameter_ is some [x] (and [eq] is directly applied to
it), and its _index_ (which comes second) is constrained to be [x] as
well. That is, case-analysing on an instance of [eq x y] in the
process of the proof construction will inevitably lead the side
condition implying that [x] and [y] actually correspond to the _same
object_. Coq will take advantage of this fact immediately, by
performing the _unification_ and substituting all occurrences of [y]
in the subsequent goal with [x].  Let us see how it works in practice.

** Case analysis on an equality witness

To demonstrate the actual proofs on the case analysis by equality, we
will have to perform an awkward twist: define _our own_ equality
predicate. 

*)

Set Implicit Arguments.
Inductive my_eq (A : Type) (x : A) : A -> Prop :=  my_eq_refl : my_eq x x.
Notation "x === y" := (my_eq x y) (at level 70).

(** 

As we can see, this definition literally repeats the Coq's standard
definition of propositional equality. The reason for the code
duplication is that SSReflect provides a specific treatment of Coq's
standard equality predicate, so the case-analysis on its instances is
completely superseded by the powerful [rewrite] tactics, which we will
see in %Section~\ref{sec:rewriting}% of this chapter. Alas, this
special treatment also leads to a non-standard behaviour of
case-analysis on equality. This is why, for didactical purposes, we
will have to stick with or own home-brewed definition until the end of
this section.

*)

Lemma my_eq_sym A (x y: A) : x === y -> y === x.

case.

(** 

[[
  A : Type
  x : A
  y : A
  ============================
   x === x
]]
*)

done.
Qed.

(**

Our next exercise will be to show that the predicate we have just
defined implies Leibniz equality. The proof is accomplished in one
line by first moving the assumption [P x]
to the top and then case-analysing on the equality, which leads to the
automatic replacements of [y] by [x].

*)

Lemma my_eq_Leibniz A (x y: A) (P: A -> Prop) : x === y -> P x -> P y. 
Proof. by case. Qed.

(** ** Implementing discrimination

Another important application of the equality predicate family and
similar ones are _proofs by discrimination_, in which the
contradiction is reached (i.e., the falsehood is derived) out of the
fact that two clearly non-equal elements are assumed to be equal. The
next lemma demonstrates the essence of the proof by discrimination
using the [my_eq] predicate.

*)

Lemma disaster : 2 === 1 -> False.
Proof.
move=> H.

(**

[[
  H : 2 === 1
  ============================
   False
]]

*)

pose D x := if x is 2 then False else True.

(**

[[
  H : 2 === 1
  D := fun x : nat =>
       match x with
       | 0 => True
       | 1 => True
       | 2 => False
       | S (S (S _)) => True
       end : nat -> Prop
  ============================
   False
]]
*)

have D1: D 1. 
by [].

(**

[[
  H : 2 === 1
  D := ...
  D1 : D 1
  ============================
   False
]]
*)

case: H D1. 

(**

[[
  D := ...
  ============================
   D 2 -> False
]]
*)

move=>/=.

(**

The tactical [/=], coming after [=>] runs all possible simplifications
on the result obtained by the tactics, preceding [=>], finishing the
proof.

*)

done.
Qed.

(** 

** Reasoning with Coq's standard equality

Now we know what drives the reasoning by equality and discrimination,
so let us forget about the home-brewed predicate [my_eq] and use the
standard equality instead. Happily, the discrimination pattern we used
to implement "by hand" now is handled by Coq/SSReflect automatically,
so the trivially false equalities deliver the proofs right away by
simply typing [done]. 

*)

Lemma disaster3: 2 = 1 -> False.
Proof. done. Qed.

(** 

* Proofs by rewriting 

The vast majority of the steps when constructing real-life proofs in
Coq are _rewriting_ steps. The general flow of the interactive proof
is typically targeted on formulating and proving small auxiliary
hypotheses about equalities in the forward-style reasoning and then
exploiting the derived equalities by means of rewriting in the goal
and, occasionally, other assumptions in the context. All rewriting
machinery is handled by SSReflect's enhanced [rewrite]%\ssrt{rewrite}%
tactics, and in this section we focus on its particular uses.

** Unfolding definitions and in-place rewritings

One of the common uses of the [rewrite] tactic is to fold/unfold
transparent definitions. In general, Coq is capable to perform the
unfoldings itself, whenever it's required. Nevertheless, manual
unfolding of a definition might help to understand the details of the
implementation, as demonstrated by the following example.

*)

Definition double A (f: A -> A) (x: A) := f (f x).

Fixpoint nat_iter (n : nat) {A} (f : A -> A) (x : A) : A :=
  if n is S n' then f (nat_iter n' f x) else x.

Lemma double2 A (x: A) f t: 
  t = double f x -> double f t = nat_iter 4 f x.
Proof.

move=>Et; rewrite Et.

(**

[[
  A : Type
  x : A
  f : A -> A
  t : A
  Et : t = double f x
  ============================
   double f (double f x) = nat_iter 4 f x
]]

Even though the remaining goal is simple enough to be completed by
[done], let us unfold both definition to make sure that the two terms
are indeed equal structurally. Such unfoldings can be _chained_, just
as any other rewritings.

*)

rewrite /double /nat_iter.

(**
[[
  x : A
  f : A -> A
  ============================
   f (f (f (f x))) = f (f (f (f x)))
]]

An alternative way to prove the same statement would be to use the
[->] tactical, which is usually combined with
[move] or [case], but instead of moving the assumption to the top, it
makes sure that the assumption is an equality and rewrites by it.

 *)

Restart.
by move=>->.
Qed.

(** 

Notice that the tactical has a companion one [<-], which performs the
rewriting by an equality assumption from right to left, in contrast to
[->], which rewrites left to right.

The reverse operation to folding is done by using [rewrite -/...]
instead of [rewrite /...].

** Proofs by congruence and rewritings by lemmas

*)

Definition f x y :=  x + y.

Goal forall x y, x + y + (y + x) = f y x + f y x.
Proof. 
move=> x y.

rewrite /f.

(**

[[
  x : nat
  y : nat
  ============================
   x + y + (y + x) = y + x + (y + x)
]]
*)

congr (_ + _).

(** 

[[
  x : nat
  y : nat
  ============================
   x + y = y + x
]]
*)

Check addnC.

(**
[[
addnC
     : commutative addn
]]
*)

Print ssrfun.commutative.

(** 
[[
ssrfun.commutative = 
  fun (S T : Type) (op : S -> S -> T) => forall x y : S, op x y = op y x
       : forall S T : Type, (S -> S -> T) -> Prop
]]

So, after specializing the definition appropriately, the type of
[addnC] should be read as:

[[
addnC
     : forall n m: nat, n + m = m + n
]]

Now, we can take advantage of this equality and rewrite by it a part
of the goal. Notice that Coq will figure out how the
universally-quantified variables should be instantiated (i.e., with
[y] and [x], respectively):

*)

by rewrite [y + _]addnC.
Qed.

Goal forall x y z, (x + (y + z)) = (z + y + x).
Proof.
by move=>x y z; rewrite [y + _]addnC; rewrite [z + _ + _]addnC.
Qed.

(** ** Naming in subgoals and optional rewritings

When working with multiple cases, it is possible to "chain" the
execution of several tactics. Then, in the case of a script [tac1;
tac2], if the goal is replaced by several after applying [tac1], then
[tac2] will be applied to _all_ subgoals, generated by [tac1]. For
example, let us consider a proof of the following lemma from the
standard [ssrnat] %\ssrm{ssrnat}% module:

*)

Lemma addnCA: forall m n p, m + (n + p) = n + (m + p).
Proof.
move=>m n. 

(** 

[[
  m : nat
  n : nat
  ============================
   forall p : nat, m + (n + p) = n + (m + p)
]]

The proof will proceed by induction on [m]. We have already seen the
use of the [case] tactics, which just performs the case
analysis. Another SSReflect tactic [elim]  generalizes
[case] by applying the default induction principle ([nat_ind] in this
case) with the respect to the remaining goal (that is, the predicate
[[forall p : nat, m + (n + p) = n + (m + p)]]) is to be proven by
induction.  The following sequence of tactics proceeds by induction on
[m] with the default induction principle. It also names some of the
generated assumptions. 

*)

elim: m=>[ | m Hm ] p. 

(**

In particular, the following steps are performed:

- [m] is pushed as a top assumption of the goal;
- [elim] is run, which leads to generation of the two goals;

  - The first goal is of the shape
[[
forall p : nat, 0 + (n + p) = n + (0 + p)
]]

  - The second goal has the shape
[[
forall n0 : nat,
 (forall p : nat, n0 + (n + p) = n + (n0 + p)) ->
 forall p : nat, n0.+1 + (n + p) = n + (n0.+1 + p)
]]

- The subsequent structured naming [=> [ |m Hm ] p] names zero
  assumptions in the first goal and the two top assumptions, [m] and
  [Hm], in the second goal. It then next names the assumption [p] in
  _both_ goals and moves it to the top.

The first goal can now be proved by multiple rewritings via the lemma
[add0n], stating that [0] is the left unit with respect to the
addition:

*)

by rewrite !add0n.

(**

The second goal can be proved by a series of rewritings using the fact
about the [(_ + 1)] function:

*)


by rewrite !addSnnS -addnS.

(**

Notice that the conclusion of the [addnS] lemma is rewritten
right-to-left.

The whole proof could be, however, accomplished in one line using the
_optional_ rewritings. 
*)

Restart.

by move=>m n; elim: m=>[ | m Hm ] p; rewrite ?add0n ?addSnnS -?addnS.
Qed.

(** 

Notice that the optional rewritings (e.g., [?addSnnS]) are
performed as many times as they can be.

** Selective occurrence rewritings

Sometimes, instead of providing an r-pattern to specialize the
rewriting, it is more convenient to specify, which particular
syntactic occurrences in the goal term should be rewritten. This is
demonstrated by the following alternative proof of commutativity of
addition from the lemma [addnCA], which we have proved before:

*)

Lemma addnC: forall m n, m + n = n + m.
Proof.
move=> m n. 
rewrite -{1}[n]addn0.
by rewrite addnCA addn0. 
Qed.

(** 

The first rewriting with [addn0] "adds" [0] to the first occurrence of
[addn0], so the left-hand side of the equality becomes [m + (n +
0)]. The next rewriting employs the lemma [addnCA], so we get [n + (m
+ 0) = n + m] as the goal, and the last one "removes" zero, so the
result trivially follows.

*)


(** * Indexed datatype families as rewriting rules

In this chapter we have already seen how defining indexed datatype
families makes it possible for Coq to provide a convenient rewriting
machinery, which is implicitly invoked by case analysis on such
families' refined types, thanks to sophisticated Coq's unification
procedure.

Although so far this approach has been demonstrated by only one
indexed type family example---propositional equality, defined by means
of the [eq] family, in this section, concluding the chapter, we will
show how to define other client-specific rewriting rules. Let us start
from a motivating example in the form of an "obvious" lemma.

*)

Lemma huh n m: (m <= n) /\ (m > n) -> False.

(**

From now on, we will be consistently including yet another SSReflect
modules, [ssrbool] and [eqtype], %\ssrm{ssrbool}\ssrm{eqtype}% into
our development. The need for them is due to the smooth combination of
reasoning with [Prop]ositions and [bool]eans, which is a subject of
the next chapter. Even though in SSReflect's library, relations on
natural numbers, such as [<=] and [>], are defined as _boolean_
functions, so far we recommend to the reader to think of them as of
predicates defined in [Prop] and, therefore, valid arguments to the
[/\] connective.

Although the statement is somewhat obvious, in the setting of Coq's
inductive definition of natural numbers it should be no big surprise
that it is proved by induction. We present the proof here, leaving the
details aside, so the reader could figure them out on his own, as a
simple exercise.%\ssrt{elim}\ssrt{suff:}\ssrtl{//}%

*)

Proof.
suff X: m <= n -> ~(m > n) by case=>/X. 
by elim: m n => [ | m IHm ] [ | n] //; exact: IHm n.
Qed.

Definition maxn m n := if m < n then n else m.

Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.

(** 

The stated lemma [max_is_max] can be, indeed, proved by induction on
[m] and [n], which is a rather tedious exercise, so we will not be
following this path.
*)

Abort.

(* ** Encoding custom rewriting rules *)

Inductive leq_xor_gtn m n : bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.


(** 

However, this is not yet enough to enjoy the custom rewriting and case
analysis on these two variant. At this moment, the datatype family
[leq_xor_gtn], whose constructors' indices encode a truth table's
"rows", specifies two substitutions in the case when [m <= n] and [n <
m], respectively and diagrammatically looks as follows:

<<
         |   C1  |   C2
-------------------------
m <= n   | true  | false
-------------------------
n < m    | false | true
>>

The boolean values in the cells specify what the values of C1 and C2
will be substituted _with_ in each of the two cases. However, the
table does not capture, what to substitute them _for_.  Therefore, our
next task is to provide suitable variants for C1 and C2, so the table
would describe a real situation and capture exactly the "case
analysis" intuition. This values of the columns are captured by the
following lemma, which, informally speaking, states that the table
with this particular values of C1 and C2 "makes sense".
*)

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
rewrite ltnNge. 
by case X: (m <= n); constructor=>//; rewrite ltnNge X.
Qed.

(*
Moreover, the lemma [leqP], which we have just proved, delivers the
necessary instance of the "truth" table, which we can now case-analyse
against.

*)

(** ** Using custom rewriting rules  *)

Lemma huh' n m: (m <= n) /\ (m > n) -> False.
Proof.

move/andP.  

(**

[[
  n : nat
  m : nat
  ============================
   m <= n < m -> False
]]

The top assumption [m <= n < m] of the goal is just a syntactic sugar
for [(m <= n) && (n < m)]. 
*)

case:leqP.

(** 

[[
  n : nat
  m : nat
  ============================
   m <= n -> true && false -> False

subgoal 2 (ID 638) is:
 n < m -> false && true -> False
]]

Now, considering a boolean value [true && false] in a goal simply as a
proposition [(true && false) = true], the proof is trivial by
simplification of the boolean conjunction.

*)

done.
done.
Qed.

(** 

The proof of [huh'] is now indeed significantly shorter than the proof
of its predecessor, [huh]. However, it might look like the definition
of the rewriting rule [leq_xor_gtn] and its accompanying lemma [leqP]
is quite narrowly-scoped, and it is not clear how useful it might be
for other proofs.
*)

Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.
Proof.
(** 

The proof begins by unfolding the definition of [maxn].

*)
rewrite /maxn.

(** 
[[
  m : nat
  n : nat
  ============================
   n <= (if m < n then n else m) /\ m <= (if m < n then n else m)
]]

We are now in the position to unleash our rewriting rule, which,
together with simplifications by means of the [//] tactical
%\ssrtl{//}% does most of the job.

*)

case: leqP=>//. 

(** 

[[
  m : nat
  n : nat
  ============================
   m < n -> n <= n /\ m <= n
]]

The res of the proof employs rewriting by some trivial lemmas from [ssrnat],
%\ssrm{ssrnat}% but conceptually is very easy.

*)

move=>H; split.

Search _ (?X <= ?X).

by apply: leqnn.

Search _ (?x < ?y) (?x <= ?y).

by rewrite ltn_neqAle in H; case/andP: H.
Qed.

(** 

The key advantage we got out of using the custom rewriting rule,
defined as an indexed datatype family is lifting the need to prove _by
induction_ a statement, which one would intuitively prove by means of
_case analysis_. In fact, all inductive reasoning was conveniently
"sealed" by the proof of [leqP] and the lemmas it made use of, so just
the tailored "truth table"-like interface for case analysis was given
to the client.
*)


(*******************************************************************)
(**                     * Exercices *                              *)
(*******************************************************************)

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
(* fill in your proof here instead of [admit] *)
Admitted.


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
(* fill in your proof here instead of [admit] *)
Admitted.



(**
---------------------------------------------------------------------
Exercise [Properties of maxn]
---------------------------------------------------------------------
Prove the following lemmas about [maxn].
*)

Lemma max_l m n: n <= m -> maxn m n = m.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma succ_max_distr_r n m : (maxn n m).+1 = maxn (n.+1) (m.+1).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma plus_max_distr_l m n p: maxn (p + n) (p + m) = p + maxn n m.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


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
(* fill in your proof here instead of [admit] *)
Admitted.


End Rewriting.
