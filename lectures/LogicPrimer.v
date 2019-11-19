(** %\chapter{Propositional Logic}% *)

From mathcomp
Require Import ssreflect.

Module LogicPrimer.


(** 

* Propositions and the [Prop] sort

CIC as a logic is expressive enough to accommodate propositions with
quantifications of an arbitrary order and over arbitrary values. On
one hand, it makes it an extremely powerful tool to state almost any
proposition of interest in modern mathematics or computer science. On
the other hand, proving such statements (i.e., constructing their
proof terms), will require human assistance, in the same way the
"paper-and-pencil" proofs are constructed in the classical
mathematics. However, unlike the paper-and-pencil proofs, proofs
constructed in Coq are a subject of immediate _automated_ check, since
they are just programs to be verified for well-typedness. Therefore,
the process of proof construction in Coq is _interactive_ and assumes
the constant interoperation between a human prover, who constructs a
proof term for a proposition (i.e., writes a program), and Coq, the
proof assistant, which carries out the task of _verifying_ the proof
(i.e., type-checking the program). This largely defines our agenda for
the rest of this course: we are going to see how to _prove_ logical
statements by means of writing _programs_, that have the types
corresponding to these statements.

*)

(** * The truth and the falsehood in Coq *)

Print True.

(**
[[
Inductive True : Prop :=  I : True
]]
*)

Theorem true_is_true: True.

(** 
[[
1 subgoals, subgoal 1 (ID 1)
  
  ============================
   True
]]
*)

Proof.
exact: I.

(** 
[[
No more subgoals.
(dependent evars:)
]]
*)

Qed.

(**
So, our first theorem is proved. As it was hinted previously, it could
have been stated even more concisely, formulated as a mere definition,
and proved by means of providing a corresponding value, without the
need to enter a proof mode:
*)

Definition true_is_true': True := I.

(**
The difference between the two definitions of the truth's validity,
which we have just constructed, can be demonstrated by means of the
[Eval] command.
*)

Eval compute in true_is_true. 
(**
[ = true_is_true : True]
*)

Eval compute in true_is_true'. 
(**
[ = I : True]

As we can see now, the theorem is evaluated to itself, whereas the
definition evaluates to it body, i.e., the value of the constructor
[I].  

Thinking by analogy, one can now guess how the falsehood can be encoded.
*)

Print False.

(**
[[
Inductive False : Prop :=  
]]
*)

Check False_ind.

(**
[[
False_ind
     : forall P : Prop, False -> P
]]
*)

Theorem one_eq_two: False -> 1 = 2.
Proof.

exact: (False_ind (1 = 2)).

Undo.

(**

Instead of supplying the argument [(1 = 2)] to [False_ind] manually,
we can leave it to Coq to figure out, what it should be, by using the
SSReflect [apply:] tactic.

*)

apply: False_ind.

(** 

There are many more ways to prove this rather trivial statement, but
at this moment we will demonstrate just yet another one, which does
not appeal to the [False_ind] induction principle, but instead
proceeds by _case analysis_.

*)

Undo.

case.

(**

The tactic [case] makes Coq to perform the case analysis. In
particular, it _deconstructs_ the _top assumption_ of the goal. The
top assumption in the goal is such that it comes first before any
arrows, and in this case it is a value of type [False]. Then, for all
constructors of the type, whose value is being case-analysed, the
tactic [case] constructs _subgoals_ to be proved.  *)

Undo.

exact: (fun (f: False) => match f with end).

Qed.

(** * Implication and universal quantification

Unlike most of the value-level functions we have seen so far,
propositions are usually parametrized by other propositions, which
makes them instances of _polymorphic_ types, as they appear in System
F and System F_\omega. Similarly to these systems, in Coq the
universal quantifier [forall] binds a variable immediately following
it in the scope of the subsequent type. For instance, the transitivity
of implication in Coq can be expressed via the following proposition:

%\begin{center}%
[forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R]
%\end{center}%

The proposition is therefore _parametrized_ over three propositional
variables, [P], [Q] and [R], and states that from the proof term of
type [P -> Q] and a proof term of type [Q -> R] one can receive a
proof term of type [P -> R]. Let us now prove these statement in the
form of theorem.  

*)

Theorem imp_trans: forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.

move=> A B C.
(**
[[
  A : Prop
  B : Prop
  C : Prop
  ============================
   (A -> B) -> (B -> C) -> A -> C
]]
*)

move=> H1 H2 a.
(**
[[
  H1 : A -> B
  H2 : B -> C
  a : A
  ============================
   C
]]

Again, there are multiple ways to proceed now. For example, we can
recall the functional programming and get the result of type [C] just
by two subsequent applications of [H1] and [H2] to the value [a] of type [A]:

*)

exact: (H2 (H1 a)).

(**

Alternatively, we can replace the direct application of the hypotheses
[H1] and [H2] by the reversed sequence of calls to the [apply:]
tactics.

*)

Undo.

(**
The first use of [apply:] will replace the goal [C] by the goal [B],
since this is what it takes to get [C] by using [H2]:

*)

apply: H2.
(** 
[[
  H1 : A -> B
  a : A
  ============================
   B
]]
The second use of [apply:] reduces the proof of [B] to the proof of
[A], demanding an appropriate argument for [H1].

*)

apply: H1.
(**
[[
  a : A
  ============================
   A
]]
*)

exact: a. 
Qed.

(**

In the future, we will replace the use of trivial tactics, such as
[exact:] by SSReflect's much more powerful tactics [done], which
combines a number of standard Coq's tactics in an attempt to finish
the proof of the current goal and reports an error if it fails to do
so.  *)

(** ** On forward and backward reasoning

Let us check now the actual value of the proof term of theorem
[imp_trans]. 

*)

Print imp_trans. 
(** 
[[
imp_trans = 
  fun (A B C : Prop) (H1 : A -> B) (H2 : B -> C) (a : A) =>
  (fun _evar_0_ : B => H2 _evar_0_) ((fun _evar_0_ : A => H1 _evar_0_) a)
       : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R

Argument scopes are [type_scope type_scope type_scope _ _ _]
]]

Even though the proof term looks somewhat furry, this is almost
exactly our initial proof term from the first proof attempt: [H2 (H1
a)]. The only difference is that the hypotheses [H1] and [H2] are
_eta-expanded_, that is instead of simply [H1] the proof terms
features its operational equivalent [fun b: B => H2 b]. Otherwise, the
printed program term indicates that the proof obtained by means of
direct application of [H1] and [H2] is the same (modulo eta-expansion)
as the proof obtained by means of using the [apply:] tactic.

These two styles of proving: by providing a direct proof to the goal
or some part of it, and by first reducing the goal via tactics, are
usually referred in the mechanized proof community as _forward_ and
_backward_ proof styles.

  *)

(** ** Refining and bookkeeping assumptions 

Suppose, we have the following theorem to prove, which is just a
simple reformulation of the previously proved [imp_trans]:

*)

Theorem imp_trans' (P Q R: Prop) : (Q -> R) -> (P -> Q) -> P -> R.
Proof.
move=> H1 H2.

move: (imp_trans P Q R)=> H.
(** 
[[
  H1 : Q -> R
  H2 : P -> Q
  H : (P -> Q) -> (Q -> R) -> P -> R
  ============================
   P -> R
]]
*)

apply: H.
(** 
[[
  H1 : Q -> R
  H2 : P -> Q
  ============================
   P -> Q

subgoal 2 (ID 142) is:
 Q -> R
]]
*)

done. 
done.

(**

The proof is complete, although the last step is somewhat repetitive,
since we know that for two generated sub-goals the proofs are the
same. In fact, applications of tactics can be _chained_ using the [;]
connective, so the following complete proof of [imp_trans'] runs
[done] for _all_ subgoals generated by [apply: H]:

*)

Restart.

move: (imp_trans P Q R)=> H H1 H2.
apply: H; done.

(**

To conclude this section, let us demonstrate even shorter way to prove
this theorem once again.

*)

Restart.
move=>H1 H2; apply: (imp_trans P Q R)=>//.
Qed.

(** * Conjunction and disjunction *)

Module Connectives.
Variables P Q R: Prop.

Locate "_ /\ _".

(** ["A /\ B" := and A B  : type_scope] *)

Print and.

(**
[[
Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B

For conj: Arguments A, B are implicit
For and: Argument scopes are [type_scope type_scope]
For conj: Argument scopes are [type_scope type_scope _ _]
]]
*)

Goal P -> R -> P /\ R.
move=> p r. 

(** 

The proof can be completed in several ways. The most familiar one is
to apply the constructor [conj] directly. It will create two subgoals,
[P] and [Q] (which are the constructor arguments), that can be
immediately discharged.

*)

apply: conj=>//.

(** 

Alternatively, since we now know that [and] has just one constructor,
we can use the generic Coq's [constructor n] tactic, where [n] is an
(optional) number of a constructor to be applied (and in this case
it's [1])

*)

Undo.
constructor 1=>//.

(**

Finally, for propositions that have exactly one constructor, Coq
provides a specialized tactic [split], which is a synonym for
[constructor 1]: *)

Undo. split=>//.
Qed.

(** 

In order to prove something out of a conjunction, one needs to
_destruct_ it to get its constructor's arguments, and the simplest way
to do so is by the [case]-analysis on a single constructor.

*)

Goal P /\ Q -> Q.
Proof.
case.

done.
Qed.

(**

The datatype of disjunction of [P] and [Q], denoted by [P \/ Q], is
isomorphic to the [sum] datatype from the provious lecture and can be
constructed by using one of its two constructors: [or_introl] or
[or_intror].

*)

Locate "_ \/ _".

(** ["A \/ B" := or A B   : type_scope] *)

Print or.

(**

[[
Inductive or (A B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B

For or_introl, when applied to less than 1 argument:
  Arguments A, B are implicit
...
]]

In order to prove disjunction of [P] and [Q], it is sufficient to
provide a proof of just [P] or [Q], therefore appealing to the
appropriate constructor.

*)

Goal Q -> P \/ Q \/ R.
move=> q. 

by right; left.
Qed.

Goal P \/ Q -> Q \/ P.
case=>x.

(** 
[[
  P : Prop
  Q : Prop
  R : Prop
  x : P
  ============================
   Q \/ P

subgoal 2 (ID 248) is:
 Q \/ P
]]
*)

by right.

(**

[[
  P : Prop
  Q : Prop
  R : Prop
  x : Q
  ============================
   Q \/ P
]]

In the second branch the type of [x] is [Q], as it accounts for the
case of the [or_intror] constructor.

*)

by left.
Qed.

(** * Proofs with negation *)

(**

In Coq's constructive approach proving the negation of [~P] of a
proposition [P] literally means that one can derive
the falsehood from [P].

*)

Locate "~ _".

(** 
["~ x" := not x       : type_scope]
*)

Print not.
(** 
[[
  not = fun A : Prop => A -> False
       : Prop -> Prop
]]

Therefore, the negation [not] on propositions from [Prop] is just a
function, which maps a proposition [A] to the implication [A ->
False]. Calculus of Constructions lacks the axiom of double negation,
which means that the proof of [~ ~A] will not deliver the proof of
[A], as such derivation would be not constructive, as one cannot get a
value of type [A] out of a function of type [(A -> B) -> B], where [B]
is taken to be [False].

However, reasoning out of negation helps to derive the familiar proofs
by contradiction, given that we managed to construct [P] _and_ [~P],
as demonstrated by the following theorem, which states that from any
[Q] can be derived from [P] and [~P]. 

*)

Theorem absurd: P -> ~P -> Q. 
Proof. by move=>p H; move : (H p). Qed.

(** 

One extremely useful theorem from propositional logic involving
negation is _contraposition_. It states states that in an implication, the
assumption and the goal can be flipped if inverted.

*)

Theorem contraP: (P -> Q) -> ~Q -> ~P.

(** Let us see how it can be proved in Coq *)

Proof.
move=> H Hq. 
move /H.
(**
[[
  H : P -> Q
  Hq : ~ Q
  ============================
   Q -> False
]]
*)

move /Hq.
done.
Qed.

(** * Existential quantification *)

Locate "exists".

(**
[[
"'exists' x .. y , p" := ex (fun x => .. (ex (fun y => p)) ..)
                      : type_scope
]]

*)

Print ex.

(**
[[
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex A P
]]
*)

Theorem ex_imp_ex A (S T: A -> Prop): 
  (exists a: A, S a) -> (forall x: A, S x -> T x) -> exists b: A, T b.

(**

The parentheses are important here, otherwise, for instance, the scope
of the first existentially-quantified variable [a] would be the whole
subsequent statement, not just the proposition _S a_.

*)

Proof.

case=>a Hs Hst.
(** 
[[
  A : Type
  S : A -> Prop
  T : A -> Prop
  a : A
  Hs : S a
  Hst : forall x : A, S x -> T x
  ============================
   exists b : A, T b
]]

Next, we apply the [ex]'s constructor by means of the [exists]
tactic with an explicit witness value [a]: 
*)

exists a.

(** We finish the proof  by applying the weakening hypothesis [Hst]. *)

by apply: Hst.

Qed.

(** ** A conjunction and disjunction analogy

Sometimes, the universal and the existential quantifications are
paraphrased as "infinitary" conjunction and disjunction
correspondingly. This analogy comes in handy when understanding the
properties of both quantifications, so let us elaborate on it for a bit.

*)

End Connectives.

(** * Missing axioms from the classical logic *)

Require Import Classical_Prop.


(**

The most often missed axiom is the axiom of _excluded middle_, which
postulates that the disjunction of [P] and [~P] is provable. Adding
this axiom circumvents the fact that the reasoning out of the excluded
middle principle is _non-constructive_.

*)

Check classic.

(** 
[[
classic
     : forall P : Prop, P \/ ~ P
]]

Another axiom from the classical logic, which coincides with the type
of Scheme's [call/cc] operator.
*)

Definition peirce_law := forall P Q: Prop, ((P -> Q) -> P) -> P.

(** 

In Scheme-like languages, the [call/cc] operator allows one to
invoke the undelimited continuation, which aborts the
computation. Similarly to the fact that [call/cc] cannot be
implemented in terms of polymorphically-typed lambda calculus as a
function and should be added as an external operator, the Peirce's law
is an axiom in the constructive logic.
*)

Check NNPP.

(** 
[[
NNPP
     : forall P : Prop, ~ ~P -> P
]]

Finally, the classical formulation of the implication through the
disjunction is again an axiom in the constructive logic, as otherwise
from the function of type [P -> Q] one would be able to construct the
proof of [~P \/ Q], which would make the law of the excluded middle
trivial to derive.
*)

Check imply_to_or.

(**

[[
imply_to_or
     : forall P Q : Prop, (P -> Q) -> ~P \/ Q
]]

Curiously, none of these axioms, if added to Coq, makes its logic
unsound: it has been rigorously proven (although, not within Coq, due
to Godel's incompleteness result) that all classical logic axioms are
consistent with CIC, and, therefore, don't make it possible to derive
the falsehood.

*)

(** * Universes and [Prop] impredicativity

_Impredicativity_ as a property of definitions allows one to define
domains that are _self-recursive_---a feature of [Prop] that we
recently observed. Unfortunately, when restated in the classical set
theory, impredicativity immediately leads to the famous Russell's
paradox, which arises from the attempt to define a set of all sets
that do not belong to themselves. In the terms of programming, the
Russell's paradox provides a recipe to encode a fixpoint combinator in
the calculus itself and write generally-recursive programs.

** Exploring and debugging the universe hierarchy

In the light of Martin-Loef's stratification, the Coq' non-polymorphic
types, such as [nat], [bool], [unit] or [list nat] "live" at the [0]th
level of universe hierarchy, namely, in the sort [Set]. The
polymorphic types, quantifying over the elements of the [Set] universe
are, therefore located at the higher level, which in Coq is denoted as
[Type(1)], but in the displays is usually presented simply as [Type],
as well as all the higher universes. We can enable the explicit
printing of the universe levels to see how they are assigned:

*)

Set Printing Universes.

Check bool.

(**
[[
bool
     : Set
]]
*)

Check Set.


Check Prop.

(**
The following type is polymorphic over the elements of the [Set]
universe, and this is why its own universe is "bumped up" by one, so
it becomes [Type(1)].
*)

Definition S := forall T: Set, list T. 
Check S.

(**
At this moment, Coq provides a very limited version of _universe
polymorphism_. For instance, the next definition [R] is polymorphic
with respect to the universe of its parameter [A], so its result lives
in the universe, whose level is taken to be the level of [A].

*)

Definition R (A: Type) (x: A): A := x. 
Arguments R [A].

Check R tt. 

(** 
[[
R tt 
     : unit
]]
*)

(** 

If the argument of [R] is itself a universe, it means that [A]'s
level is higher than [x]'s level, and so is the level of [R]'s result.

*)

Check R Type. 

(**
However, the attempt to apply [R] to itself immediately leads to an
error reported, as the system cannot infer the level of the result, by
means of solving a system of universe level inequations, therefore,
preventing meta-circular paradoxes.

*)

(**
[[
Check R R.

Error: Universe inconsistency (cannot enforce Top.1225 < Top.1225).
]]
*)



(*******************************************************************)
(**                     * Exercices *                              *)
(*******************************************************************)

(**
---------------------------------------------------------------------
Exercise [forall-distributivity]
---------------------------------------------------------------------

Formulate and prove the following theorem in Coq, which states the
distributivity of universal quantification with respect to implication:
\[
forall P Q, 
  [(forall x, P(x) => Q(x)) => ((forall y, P(y)) => forall z, Q(z))]
\]

Be careful with the scoping of universally-quantified variables
and use parentheses to resolve ambiguities!
*)

Theorem all_imp_ist A (P Q: A -> Prop): 
  (forall x: A, P x -> Q x) -> (forall y, P y) -> forall z, Q z. 
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.

(**
---------------------------------------------------------------------
Exercise [Or-And distributivity]
---------------------------------------------------------------------
Prove the following theorems.
*)

Theorem or_distributes_over_and P Q R: 
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.

Theorem or_distributes_over_and_2 P Q R :
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.

(**
---------------------------------------------------------------------
Exercise [Home-brewed existential quantification]
---------------------------------------------------------------------

Let us define our own version [my_ex] of the existential quantifier
using the SSReflect notation for constructors: *)

Inductive my_ex A (S: A -> Prop) : Prop := my_ex_intro x of S x.

(** You invited to prove the following goal, establishing the
equivalence of the two propositions. *)

Goal forall A (S: A -> Prop), my_ex A S <-> exists y: A, S y.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.
 
(** 
Hint: the propositional equivalence [<->] is just a conjunction of
two implications, so proving it can be reduced to two separate goals
by means of [split] tactics.
*)

(**
---------------------------------------------------------------------
Exercise [Distributivity of existential quantification]
---------------------------------------------------------------------
Prove the following theorem.
*)

Theorem dist_exists_or (X : Type) (P Q : X -> Prop):
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(**
---------------------------------------------------------------------
Exercise [Two equals three]
---------------------------------------------------------------------
Prove the following  theorem. Can you explain the proof?
*)

Theorem two_is_three A: (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(**
---------------------------------------------------------------------
Exercise [Dyslexic implication and contraposition]
---------------------------------------------------------------------

The "dyslexic" implication and contrapositions are the following
propositions. 
*)

Definition dys_imp (P Q: Prop) := (P -> Q) -> (Q -> P).
Definition dys_contrap (P Q: Prop) := (P -> Q) -> (~P -> ~Q).

(**
These propositions are inhabited, as otherwise one, given a proof of
any of them, would be able to construct a proof of [False]. You are
invited to deomnstrate it by proving the following statements.
*)

Theorem di_false: (forall P Q: Prop, dys_imp P Q) -> False.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Theorem dc_false: (forall P Q: Prop, dys_contrap P Q) -> False.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(**
---------------------------------------------------------------------
Exercise [Irrefutability of the excluded middle]
---------------------------------------------------------------------

Proof the following theorem that states that the assumption of the
falsehood of the excluded middle leads to inconsistencies, as is
allows one to derive [False].
*)

Theorem excluded_middle_irrefutable: forall (P : Prop), ~~(P \/ ~ P).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(**
---------------------------------------------------------------------
Exercise [Equivalence of classical logic axioms]
---------------------------------------------------------------------

Prove that the following five axioms of the classical are equivalent.

*)

Definition peirce := peirce_law.
Definition double_neg := forall P: Prop, ~ ~ P -> P.
Definition excluded_middle := forall P: Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~ ( ~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop, (P -> Q) -> (~P \/ Q).

Lemma peirce_dn: peirce -> double_neg.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma dn_em : double_neg -> excluded_middle.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma em_dmnan: excluded_middle -> de_morgan_not_and_not.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma dmnan_ito : de_morgan_not_and_not -> implies_to_or.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma ito_peirce : implies_to_or -> peirce.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(**

Hint: Use [rewrite /d] tactics to unfold the definition of a value [d]
 and replace its name by its body. You can chain several unfoldings by
 writing [rewrite /d1 /d2 ...]  etc.

Hint: To facilitate the forward reasoning by contradiction, you can
 use the SSReflect tactic [suff: P], where [P] is an arbitrary
 proposition. The system will then require you to prove that [P]
 implies the goal _and_ [P] itself.

Hint: Stuck with a tricky proof? Use the Coq [admit] tactic as a
 "stub" for an unfinished proof of a goal, which, nevertheless will be
 considered completed by Coq. You can always get back to an admitted
 proof later.

*)


(**
---------------------------------------------------------------------
Exercise [Inifinitary de Morgan laws]
---------------------------------------------------------------------

Prove the following implication analogous to the Morgan law for
conjunctions  and disjunctions.

*)

Theorem not_forall_exists A (P : A -> Prop): 
  (forall x: A, P x) -> ~(exists y: A, ~ P y).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(**

Then, prove that the assumption of the excluded middle axiom allows one to
establish the implication from the negation of (exists) to (forall).

*)

Theorem not_exists_forall :
  excluded_middle -> forall (X: Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


End LogicPrimer.

