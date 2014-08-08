(** %\chapter{Propositional Logic}% *)

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

Require Import ssreflect.

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
SSReflect [apply:] tactic.%\ssrt{apply:}%

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

The tactic [case]%\ssrt{case}% makes Coq to perform the case
analysis. In particular, it _deconstructs_ the _top assumption_ of the
goal. The top assumption in the goal is such that it comes first
before any arrows, and in this case it is a value of type
[False]. Then, for all constructors of the type, whose value is being
case-analysed, the tactic [case] constructs _subgoals_ to be
proved. 
*)

Undo.

exact: (fun (f: False) => match f with end).

Qed.

(** * Implication and universal quantification

Unlike most of the value-level functions we have seen so far,
propositions are usually parametrized by other propositions, which
makes them instances of _polymorphic_ types, as they appear in
%\index{System $F$}%
%System~$F$% and %System $F_{\omega}$%. Similarly to these systems, in
Coq the universal quantifier [forall] (spelled <<forall>>) binds a
variable immediately following it in the scope of the subsequent
type.%\footnote{As it has been noticed in Chapter~\ref{ch:funprog} the
$\forall$-quantifier is Coq's syntactic notation for dependent
function types, sometimes also referred to a \emph{$\Pi$-types} or
\emph{dependent product types}.}%%\index{dependent function type}% For
instance, the transitivity of implication in Coq can be expressed via
the following proposition:

%\begin{center}%
[forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R]
%\end{center}%

The proposition is therefore _parametrized_ over three propositional
variables, [P], [Q] and [R], and states that from the proof term of
type [P -> Q] and a proof term of type [Q -> R] one can receive a
proof term of type [P -> R].%\footnote{Recall that the arrows have
right associativity, just like function types in Haskell and OCaml,
which allows one to apply functions partially, specifying their
arguments one by one}% Let us now prove these statement in the form of
theorem.  *)

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
[exact:] by SSReflect's much more powerful tactics [done],%\ssrt{done}% which
combines a number of standard Coq's tactics in an attempt to finish
the proof of the current goal and reports an error if it fails to do
so. 
*)

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
_backward_ proof styles%\index{forward proof style}\index{backward
proof style}%.
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
we can use the generic Coq's [constructor n]%\ttac{constructor}%
tactic, where [n] is an (optional) number of a constructor to be
applied (and in this case it's [1])

*)

Undo.
constructor 1=>//.

(**

Finally, for propositions that have exactly one constructor, Coq
provides a specialized tactic [split]%\ttac{split}%, which is a synonym for
[constructor 1]:
*)

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
isomorphic to the [sum] datatype from %Chapter~\ref{ch:funprog}% and
can be constructed by using one of its two constructors: [or_introl]
or [or_intror].

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

%\ssrd{or}%

In order to prove disjunction of [P] and [Q], it is sufficient to
provide a proof of just [P] or [Q], therefore appealing to the
appropriate constructor.

*)

Goal Q -> P \/ Q \/ R.
move=> q. 

(**  

Similarly to the case of conjunction, this proof can be completed
either by applying a constructor directly, by using [constructor 2]
tactic or by a specialised Coq's tactic for disjunction:
[left]%\ttac{left}\ttac{right}% or [right]. The notation ["_ \/ _"] is
right-associative, hence the following proof script, which first
reduces the goal to the proof of [Q \/ R], and then to the proof of
[Q], which is trivial by assumption.

*)

by right; left.
Qed.

(** 

The use of SSReflect's tactical [by]%\ssrtl{by}% makes sure that its
argument tactic ([right] in this case) succeeds and the proof of the
goal completes, similarly to the trailing [done]. If the sequence of
tactics [left; right] wouldn't prove the goal, a proof script error
would be reported.

The statements that have a disjunction as their assumption are usually
proved by case analysis on the two possible disjunction's
constructors:

*)

Goal P \/ Q -> Q \/ P.
case=>x.

(** 

Notice how the case analysis via the SSReflect's [case] tactic was
combined here with the trailing [=>]. It resulted in moving the
constructor parameter in _each_ of the subgoals from the goal
assumptions to the assumption context. The types of [x] are different
in the two branches of the proof, though. In the first branch, [x] has
type [P], as it names the argument of the [or_introl] constructor.

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

(**

It is worth noticing that the definition of disjunction in Coq is
_constructive_, whereas the disjunction in the classical propositional
logic is not. More precisely, in classical logic the proof of the
proposition [P \/ ~ P] is true by the axiom of the excluded middle
(see %Section~\ref{sec:axioms}% for a more detailed discussion),
whereas in Coq, proving [P \/ ~ P] would amount to _constructing_ the
proof of either [P] or [~ P]. Let us illustrate it with a specific
example. If [P] is a proposition stating that [P = NP], then the
classical logic's the tautology [P \/ ~ P] holds, although it does not
contribute to the proof of either of the disjuncts. In constructive
logic, which Coq is an implementation of, in the trivial assumptions
given the proof of [P \/ ~ P], we would be able to extract the proof
of either [P] or [~P].%\footnote{Therefore, winning us the Clay
Institute's award.}%

*)

(** * Proofs with negation

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
False]. With this respect the intuition of negation from the classical
logic might be misleading: as it will be discussed in
%Section~\ref{sec:axioms}%, the Calculus of Constructions lacks the
axiom of double negation, which means that the proof of [~ ~A] will not
deliver the proof of [A], as such derivation would be not
constructive, as one cannot get a value of type [A] out of a function
of type [(A -> B) -> B], where [B] is taken to be [False].

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

The syntax [move / H] (spaces in between are optional) stands for one
of the most powerful features of SSReflect, called _views_ (see
%Section~9 of~\cite{Gontier-al:TR}%), which allows one to _weaken_ the
assumption in the goal part of the proof on the fly by applying a
hypothesis [H] to the top assumption in the goal. In the script above
the first command [move=> H Hq] simply popped two assumptions from the
goal to the context. What is left is [~P], or, equivalently [P ->
False]. The view mechanism then "interpreted" [P] in the goal via [H]
and changing it to [Q], since [H] was of type [P -> Q], which results
in the modified goal [Q -> False].  Next, we apply the view [Hq] to
the goal, which switches [Q] to [False], which makes the rest of the
prof trivial.  *)

move /Hq.
done.
Qed.

(** remove printing exists *)
(** printing <-> %\texttt{<->}% *)

(** * Existential quantification
%\label{sec:exists}%

Existential quantification in Coq, which is denoted by the notation
"[exists x, P x]" is just yet another inductive predicate with exactly
one constructor:

*)

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

%\ssrd{ex}%

The notation for existentially quantified predicates conveniently
allows one to existentially quantify over several variables,
therefore, leading to a chain of enclosed calls of the constructor
[ex_intro].  

The inductive predicate [ex] is parametrized with a type [A], over
elements of which we quantify, and a predicate function of type [A ->
Prop]. What is very important is that the scope of the variable [x] in
the constructor captures [ex A P] as well. That is, the constructor
type could be written as [forall x, (P x -> ex A P)] to emphasize that
each particular instance of [ex A P] carries is defined by a
_particular_ value of [x]. The actual value of [x], which satisfies
the predicate [P] is, however, not exposed to the client, providing
the _data abstraction_ and information hiding, similarly to the
traditional existential types (see %Chapter~24
of~\cite{Pierce:BOOK02}%), which would serve as a good analogy.  Each
inhabitant of the type [ex] is therefore an instance of a
%\emph{dependent pair},\footnote{In the literature, dependent pairs
are often referred to as \emph{dependent sums} or
$\Sigma$-types.\index{dependent sum}}% whose first element is a
_witness_ for the following predicate [P], and the second one is a
result of application of [P] to [x], yielding a particular
proposition.

%\index{Sigma-type|see {dependent sum}}%

The proofs of propositions that assume existential quantification are
simply the proofs by case analysis: destructing the only constructor
of [ex], immediately provides its arguments: a witness [x] and the
predicate [P] it satisfies. The proofs, where the existential
quantification is a goal, can be completed by applying the constructor
[ex_intro] directly or by using a specialized Coq's tactic [exists z],
which does exactly the same, instantiating the first parameter of the
constructor with the provided value [z]. Let us demonstrate it on a
simple example%~\cite[\S 5.2.6]{Bertot-Casteran:BOOK}%, accounting for
the weakening of the predicate, satisfying the existentially
quantified variable.

*)

Theorem ex_imp_ex A (S T: A -> Prop): 
  (exists a: A, S a) -> (forall x: A, S x -> T x) -> exists b: A, T b.

(**

The parentheses are important here, otherwise, for instance, the scope
of the first existentially-quantified variable [a] would be the whole
subsequent statement, not just the proposition _S a_.

*)

Proof.

(** First, we decompose the first existential sum into the witness [a]
and the proposition [Hst], and also store the universally-quantified
implication assumption with the name [Hst]. *)

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

(**
%\begin{exercise}%

Let us define our own version [my_ex] of the existential quantifier
using the SSReflect notation for constructors:

*)

Inductive my_ex A (S: A -> Prop) : Prop := my_ex_intro x of S x.

(** 

The reader is invited to prove the following goal, establishing the
equivalence of the two propositions

*)

Goal forall A (S: A -> Prop), my_ex A S <-> exists y: A, S y.

(** 

%\hint% the propositional equivalence [<->] is just a conjunction of
two implications, so proving it can be reduced to two separate goals
by means of [split] tactics.

*)

(* begin hide *)
Proof.
move=> A S; split.
- by case=> x Hs; exists x.
by case=>y Hs; apply: my_ex_intro Hs.
Qed.
(* end hide *) 
 
(** 

%\end{exercise}%

** A conjunction and disjunction analogy

Sometimes, the universal and the existential quantifications are
paraphrased as "infinitary" conjunction and disjunction
correspondingly. This analogy comes in handy when understanding the
properties of both quantifications, so let us elabore on it for a bit.

In order to prove the conjunction [P1 /\ ... /\ Pn], one needs to
establish that _all_ propositions [P1 ... Pn] hold, which in the
finite case can be done by proving [n] goal, for each statement
separately (and this is what the [split] tactic helps to
do). Similarly, in order to prove the propositions [forall x: A, P x],
one needs to prove that [P x] holds for _any_ [x] of type [A]. Since
the type [A] itself can define an infinite set, there is no way to
enumerate all conjuncts, however, an explicit handle [x] gives a way
to effective _index_ them, so proving [P x] for an arbitrary [x] would
establish the validity of the universal quantification itself. Another
useful insight is that in Coq [forall x: A, P x] is a type of a
dependent function that maps [x] of type [A] to a value of type [P
x]. The proof of the quantification would be, therefore, a function
with a suitable "plot". Similarly, in the case of [n]-ary conjunction,
the function has finite domain of exactly [n] points, for each of
which an appropriate proof term should be found.

In order to prove the [n]-ary disjunction [P1 \/ ... \/ Pn] in Coq, it
is sufficient to provide a proof for just one of the disjunct _as well
as_ a "tag" --- an indicator, which disjunct exactly is being proven
(this is what tactics [left] and [right] help to achieve). In the case
of infinitary disjunction, the existential quantification "[exists x,
P x]", the existentially quantified variable plays role of the tag
indexing all possible propositions [P x]. Therefore, in order to prove
such a proposition, one needs first to deliver a witness [x] (usually,
by means of calling the tactics [exists]), and then prove that for
this witness/tag the proposition [P x] holds. Continuing the same
analogy, the disjunction in the assumption of a goal usually leads to
the proof by [case] analysis assuming that one of the disjuncts holds
at a time. Similarly, the way to destruct the existential
quantification is by case-analysing on its constructor, which results
in acquiring the witness (i.e., the "tag") and the corresponding
"disjunct".

Finally, the folklore alias "dependent product type" for dependent
function types (i.e., [forall]-quantified types) indicates its
relation to products, which are Curry-Howard counterparts of
conjunctions. In the same spirit, the term "dependent sum type" for
the dependent types, of which existential quantification is a
particular case, hints to the relation to the usual sum types, and, in
particular [sum] (discussed in %Chapter~\ref{ch:funprog}%), which is a
Curry-Howard dual of a disjunction.

*)

End Connectives.

(** * Missing axioms from the classical logic
%\label{sec:axioms}%

In the previous sections of this chapter, we have seen how a fair
amount of propositions from the higher-order propositional logics can
be encoded and proved in Coq. However, some reasoning principles,
employed in the _classical_ propositional logic, cannot be encoded in
Coq in a form of provable statements, and, hence, should be encoded as
_axioms_.

%\index{classical propositional logic}% In this section, we provide a
brief and by all means incomplete overview of the classical
propositional logic axioms that are missing in Coq, but can be added
by means of importing the appropriate libraries. %Chapter~12 of the
book~\cite{Chlipala:BOOK}% contains a detailed survey of useful axioms
that can be added into Coq development on top of CIC.

To explore some of some of the axioms, we first import that classical
logic module [Classical_Prop].

*)

Require Import Classical_Prop.


(**

The most often missed axiom is the axiom of _excluded middle_, which
postulates that the disjunction of [P] and [~P] is provable. Adding
this axiom circumvents the fact that the reasoning out of the excluded
middle principle is _non-constructive_, as discussed in
%Section~\ref{sec:conjdisj}%.

*)

Check classic.

(** 
[[
classic
     : forall P : Prop, P \/ ~ P
]]

Another axiom from the classical logic, which coincides with the type
of Scheme's [call/cc]
operator%\footnote{\url{http://community.schemewiki.org/?call-with-current-continuation}}%
(pronounced as _call with current continuation_) modulo Curry-Howard
isomorphism is _Peirce's law_:
%\index{Peirce's law}%
*)

Definition peirce_law := forall P Q: Prop, ((P -> Q) -> P) -> P.

(** 

In Scheme-like languages, the [call/cc] operator allows one to
invoke the undelimited continuation, which aborts the
computation. Similarly to the fact that [call/cc] cannot be
implemented in terms of polymorphically-typed lambda calculus as a
function and should be added as an external operator, the Peirce's law
is an axiom in the constructive logic.

The classical double negation principle is easily derivable from
Peirce's law, and corresponds to the type of [call/cc], which always
invokes its continuation parameter, aborting the current computation.

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
to %\Godel%'s incompleteness result) that all classical logic axioms
are consistent with CIC, and, therefore, don't make it possible to
derive the falsehood%~\cite{Werner:TACS97}%.

The following exercise reconcile most of the familiar axioms of the
classical logic.



%\begin{exercise}{Equivalence of classical logic axioms~\cite[\S
 5.2.4]{Bertot-Casteran:BOOK}}
\label{ex:equivax}
%

Prove that the following five axioms of the classical are equivalent.

*)

Definition peirce := peirce_law.
Definition double_neg := forall P: Prop, ~ ~ P -> P.
Definition excluded_middle := forall P: Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~ ( ~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop, (P -> Q) -> (~P \/ Q).

(* begin hide *)
Lemma peirce_dn: peirce -> double_neg.
Proof. by move=>H P Hn; apply: (H _ False)=> /Hn. Qed.

Lemma dn_em : double_neg -> excluded_middle.
Proof. 
rewrite /double_neg /excluded_middle=> Dn P. 
apply: (Dn (P \/ ~ P))=>H1; apply: (H1).
by left; apply: (Dn)=> H2; apply: H1; right.
Qed.

Lemma em_dmnan: excluded_middle -> de_morgan_not_and_not.
Proof.
rewrite /excluded_middle /de_morgan_not_and_not=> H1 P Q H2.
suff: ~P -> Q.
- move=>H3. move: (H1 P); case=>//X; first by left. 
  by right; apply: H3. 
move=> Pn.
move: (H1 Q); case=>// Qn.
suff: False=>//; apply: H2; split=>//.
Qed.

Lemma dmnan_ito : de_morgan_not_and_not -> implies_to_or.
Proof.
rewrite /de_morgan_not_and_not /implies_to_or=> H1 P Q Hi.
suff: ~P \/ P.
case=>//; first by left.
- by move/ Hi; right.
move: (H1 (~P) P)=> H2; apply: H2; case=> Hp p.
suff: (P -> False) \/ False by case=>//.
by apply: H1; case.
Qed.

Lemma ito_peirce : implies_to_or -> peirce.
Proof.
rewrite /peirce /peirce_law /implies_to_or=> H1 P Q H2.
have X: P -> P by [].
move: (H1 P P) =>/(_ X); case=>{X}// Pn.
by apply: (H2)=>p. 
Qed.

(* end hide *)

(**

%\hint% Use [rewrite /d] %\ssrt{rewrite}% tactics to unfold the
 definition of a value [d] and replace its name by its body. You can
 chain several unfoldings by writing [rewrite /d1 /d2 ...]
 etc. %\ssrt{rewrite}%

%\hint% To facilitate the forward reasoning by contradiction, you can
 use the SSReflect tactic [suff: P], %\ssrt{suff:}% where [P] is
 an arbitrary proposition. The system will then require you to prove
 that [P] implies the goal _and_ [P] itself.

%\ssrt{admit}%

%\hint% Stuck with a tricky proof? Use the Coq [admit] tactic as a
 "stub" for an unfinished proof of a goal, which, nevertheless will be
 considered completed by Coq. You can always get back to an admitted
 proof later.

%\end{exercise}%

*)

(** * Universes and [Prop] impredicativity

While solving Exercise%~\ref{ex:equivax}% from the previous section,
the reader could notice an interesting detail about the propositions
in Coq and the sort [Prop]: the propositions that quantify over
propositions still remain to be propositions, i.e., they still belong
to the sort [Prop]. This property of propositions in Coq (and, in
general, the ability of entities of some class to abstract over the
entities of the same class) is called
_impredicativity_. %\index{impredicativity}% The opposite
characteristic (i.e., the inability to refer to the elements of the
same class) is called _predicativity_. %\index{predicativity}%

One of the main challenges when designing the Calculus of
Constructions was to implement its logical component (i.e., the
fragment responsible for constructing and operating with elements of
the [Prop] sort), so it would subsume the existing impredicative
propositional calculi%~\cite{Coquand-Huet:ECCA85}%, and, in
%\index{System $F$}%
particular, %System~$F$% (which is impredicative), allowing for the
expressive reasoning in the higher-order propositional logic.

_Impredicativity_ as a property of definitions allows one to define
domains that are _self-recursive_---a feature of [Prop] that we
recently observed. Unfortunately, when restated in the classical set
theory, impredicativity immediately leads to the famous Russel's
paradox, which arises from the attempt to define a set of all sets
that do not belong to themselves. In the terms of programming, the
Russel's paradox provides a recipe to encode a fixpoint combinator in
the calculus itself and write generally-recursive programs.

%System~$F$% is not a dependently-typed calculus and it has been
proven to contain no paradoxes%~\cite{Girard:PhD}%, as it reasons only
about _types_ (or, _propositions_), which do not depend on
values. However, adding dependent types to the mix (which Coq requires
to make propositions quantify over arbitrary values, not just other
propositions, serving as a general-purpose logic) makes the design of
a calculus more complicated, in order to avoid paradoxes akin to the
Russels', which arise from mixing values and sets of values. This
necessity to "cut the knot" inevitably requires to have a sort of a
higher level, which contains all sets and propositions (i.e., the
whole sorts [Set] and [Prop]), but does not contain itself. Let us
call such sort [Type]. It turns out that the self-inclusion [Type :
Type] leads to another class of paradoxes%~\cite{Coquand:LICS86}%, and
in order to avoid them the hierarchy of higher-order sorts should be
made infinite and _stratified_. %\index{stratification}%
Stratification means that each sort has a level number, and is
contained in a sort of a higher level but not in itself. The described
approach is suggested by %Martin-\loef~\cite{Martin-Loef:84}% and
adopted literally, in particular, by
Agda%~\cite{Norell:PhD}\index{Agda}%. The stratified type sorts,
following %Martin-\loef%'s tradition, are usually referred to as
_universes_.%\index{universes}%

A similar stratification is also implemented in Coq, which has its own
universe hierarchy, although with an important twist. The two
universes, [Set] and [Prop] cohabit at the first level of the universe
hierarchy with [Prop] being impredicative. The universe containing
both [Set] and [Prop] is called [Type(1)], and it is _predicative_, as
well as all universes that are above it in the hierarchy. CIC
therefore remains consistent as a calculus, only because of the fact
that all impredicativity in it is contained at the very bottom of the
hierarchy.

** Exploring and debugging the universe hierarchy

In the light of %Martin-\loef%'s stratification, the Coq'
non-polymorphic types, such as [nat], [bool], [unit] or [list nat]
"live" at the [0]th level of universe hierarchy, namely, in the sort
[Set]. The polymorphic types, quantifying over the elements of the
[Set] universe are, therefore located at the higher level, which in
Coq is denoted as [Type(1)], but in the displays is usually presented
simply as [Type], as well as all the higher universes. We can enable
the explicit printing of the universe levels to see how they are
assigned:

%\ccom{Set Printing Universes}%

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

(**
%
\texttt{Set}

~~~~~\texttt{: Type (* (Set)+1 *)}
%
*)

Check Prop.

(**
%
\texttt{Prop}

~~~~~\texttt{: Type (* (Set)+1 *)}
%

The following type is polymorphic over the elements of the [Set]
universe, and this is why its own universe is "bumped up" by one, so
it becomes [Type(1)].

*)

Definition S := forall T: Set, list T. 
Check S.

(**

%
\textsf{S}

~~~~~\texttt{: Type (* max(Set, (Set)+1) *)}
%

At this moment, Coq provides a very limited version of _universe
polymorphism_. For instance, the next definition [R] is polymorphic
with respect to the universe of its parameter [A], so its result lives
in the universe, whose level is taken to be the level of [A].

*)

Definition R (A: Type) (x: A): A := x. 
Implicit Arguments R [A].

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

%
\textsf{R} 

~~~~~\texttt{: Type (* Top.1237 *) : Type (* Top.1238 *)}
%

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
%\begin{exercise}[$\forall$-distributivity]%

Formulate and prove the following theorem in Coq, which states the
distributivity of universal quantification with respect to implication:
\[
forall P Q, 
  [(forall x, P(x) => Q(x)) => ((forall y, P(y)) => forall z, Q(z))]
\]

Be careful with the scoping of universally-quantified variables
and use parentheses to resolve ambiguities!

%\end{exercise}%
---------------------------------------------------------------------*
*)
Theorem all_imp_dist A (P Q: A -> Prop): 
  (forall x: A, P x -> Q x) -> (forall y, P y) -> forall z, Q z. 
Proof. by move=> H1 H2 z; apply: H1; apply: H2. Qed.



Theorem excluded_middle_irrefutable: forall (P : Prop), ~~(P \/ ~ P).
Proof.
move=>P H. 
apply: (H); right=>p.
by apply: H; left.
Qed.


Theorem not_exists_dist :
  excluded_middle -> forall (X: Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
move=> Em X P H x; rewrite /excluded_middle in Em.
move: (Em (P x)); case=>// => H1.
by suff: False =>//; apply:H; exists x. 
Qed.

Theorem dist_exists_or : ∀(X:Type) (P Q : X → Prop),
  (∃x, P x ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x).
Proof.


(* begin hide *)
Definition dys_imp (P Q: Prop) := (P -> Q) -> (Q -> P).
Definition dys_contrap (P Q: Prop) := (P -> Q) -> (~P -> ~Q).

Theorem di_false: (forall P Q: Prop, dys_imp P Q) -> False.
Proof. by move/(_ _ True); apply. Qed.

Theorem dc_false: (forall P Q: Prop, dys_contrap P Q) -> False.
Proof. by move=>H; apply: (H False True)=>//. Qed.
(* end hide *)

End LogicPrimer.

