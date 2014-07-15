(** %\chapter{Propositional Logic}% *)

(* begin hide *)
Require Import ssreflect.
(* end hide *)

(** 


In the previous chapter we had an opportunity to explore Coq as a
functional programming language and learn how to define inductive
datatypes and program that operate on them, implementing the later one
directly or using the automatically-generated recursion
combinators. Importantly, most of the values that we met until this
moment, inhabited the types, which were defined as elements of the
sort [Set]. The types [unit], [empty], [nat], [nat * unit] etc. are
good examples of _first-order_ types inhabiting the sort [Set] and,
therefore , contributing to the analogy between sets and first-order
types, which we explored previously.  In this chapter, we will be
working with a new kind of entities, incorporated by Coq:
_propositions_.

* Propositions and the [Prop] sort

In Coq, propositions bear a lot of similarities with types,
demonstrated in Chapter%~\ref{ch:funprog}%, and inhabit a separate
sort [Prop], similarly to how first-order types inhabit [Set]. The
"values" that have elements of [Prop] as their types are usually
referred to as _proofs_ or _proof terms_, the naming convention which
stems out of the ide of %\emph{Curry-Howard
Correspondence}~\cite{Curry:34,Howard:80}%.%\footnote{\url{http://en.wikipedia.org/wiki/Curry-Howard_correspondence}}%
Sometimes, the Curry-Howard Correspondence is paraphrased as
_proofs-as-programs_, which is truly illuminating when it comes to the
intuition behind the formal proof construction in Coq, which, in fact,
is just programming in disguise.

The _Calculus of Inductive Constructions_
(CIC)%~\cite{Bertot-Casteran:BOOK,Coquand-Huet:IC88}%, a logical
foundation of Coq, similarly to its close relative, Martin-%\loef%'s
_Intuitionistic Type Theory_ %\cite{Martin-Loef:84}%, considers proofs
to be just regular values of the "programming" language it
defines. Therefore, the process of constructing the proofs of Coq is
very similar to the process of writing the programs. Intuitively, when
one asks a question "Whether the proposition [P] is _true_?", what is
meant in fact is "Whether the _proof_ of [P] can be constructed?" This
is an unusual twist, which is crucial for understanding the process of
understanding the concept of "truth" and proving propositions in CIC
(and, equivalently, in Coq), so we specifically outline it here:

%
\newpage
\begin{center}
Only those propositions are considered to be \emph{true}, which are
provable \emph{constructively},\\ i.e., by providing an \emph{explicit} proof term,
that inhabits them.
\end{center}
%

This formulation of "truth" is somewhat surprising at the first
encounter, comparing to the classical propositional logic, where the
propositions are considered to be true simply if they are tautologies
(i.e., reduce to the boolean value [true] for all possible
combinations of their free variables' values), therefore leading to
the common proof method in classical propositional logic: truth
tables.  While the truth table methodology immediately delivers the
recipe to prove propositions without quantifiers _automatically_ (that
is, just by checking the corresponding truth tables), it does not
quite scale when it comes to the higher-order propositions (i.e.,
quantifying over predicates) as well as of propositions quantifying
over elements of arbitrary domains. For instance, the following
proposition, in which the reader can recognize the induction principle
over natural numbers, cannot be formulated in the zeroth- or
first-order propositional logic (and, in fact, in _any_ propositional
logic):

%
\begin{center}
For any predicate $P$, if $P(0)$ holds, and for any $m$, $P(m)$
implies $P(m + 1)$, \\
then for any $n$, $P(n)$ holds.
\end{center}
%

The statement above is _second-order_ as it binds a first-order
predicate by means of universal quantification, which makes it belong
to the corresponding second-order logic (which is not even
propositional, as it quantifies over arbitrary natural values, not
just propositions). Higher-order logics%~\cite{Church:JSL40}% are
known to be undecidable in general, and, therefore, there is no
automatic way to reduce an arbitrary second-order formula to [true] or
[false].

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
proof term for a proposition (i.e., writes a program) and, Coq the
proof assistant, which carries out the task of _verifying_ the proof
(i.e., type-checking the program). This largely defines our agenda for
the rest of these notes: we are going to see how to _prove_ logical
statements by means of writing _programs_, that have the types
corresponding to these statements.

In the rest of this chapter we will focus only on the capability of
Coq as a formal system allowing one to reason about propositions,
leaving reasoning about values aside till the next chapter. It is
worth noticing that a fragment of Coq, which deals with the sort
[Prop], accommodating all the propositions, and allows the programmer
to make statements with propositions, corresponds to the logical
calculus, known as %System~$F_{\omega}$% (see Chapter 30
of%~\cite{Pierce:BOOK02}%) extending %System
$F$~\cite{Reynolds:SP74,Girard:PhD}%, mentioned in
Chapter%~\ref{ch:funprog}%. Unlike %System $F$%, which introduces
polymorphic types, and, equivalently, first-order propositions that
quantify over other propositions, %System~$F_{\omega}$% allows one to
quantify as well over _type operators_, which can be also thought of
as higher-order propositions.

* The truth and the falsehood in Coq

We start our acquaintance with propositional logic in Coq by
demonstrating how one the two simplest propositions, the truth and the
falsehood, are encoded. Once again, let us remind that, unlike in the
Propositional Logic, in Coq these two are _not_ the only possible
propositional _values_, and soon we will see how a wide range of
propositions different from mere truth or falsehood are implemented.

The truth is represented in Coq as a datatype of sort [Prop] with just
one constructor, taking no arguments:

*)

Print True.

(**
[Inductive True : Prop :=  I : True]

Such simplicity makes it trivial to construct an instance of the
[True] proposition%\footnote{In the context of propositional logic, we
will be using the words ``type'' and ``proposition'' interchangeably
without additional specification when it's clear from the context.}%:
Now we can prove the following proposition in Coq's embedded
propositional logic, essentially meaning that [True] is provable.

*)

Theorem true_is_true: True.

(** 
[[
1 subgoals, subgoal 1 (ID 1)
  
  ============================
   True
]]

The keyword [Theorem] serves two purposes. First, similarly to the
command [Definition], it defines a named entity, which is not
necessarily a proposition. In this case the name is
[true_is_true]. Next, similarly to [Definition], there might follow a
list of parameters, which is empty in this example. Finally, after the
colon [:] there is a type of the defined value, which in this case it
[True]. With this respect there is no difference between [Theorem] and
[Definition]. However, unlike [Definition], [Theorem] doesn't require
one to provide the expression of the corresponding type right
away. Instead, the interactive _proof mode_ is activated, so the proof
term could be constructed incrementally. The process of the gradual
proof construction is what makes Coq to be a _interactive proof
assistant_, in addition to being already a programming language with
dependent types. 

Although not necessary, it is considered a good programming practice
in Coq to start any interactive proof with a keyword [Proof], which
makes the final scripts easier to read and improves the general proof layout.

*)

Proof.

(**

In the interactive proof mode, the [*goals*] display shows a _goal_ of
the proof---the type of the value to be constructed ([True] in this
case), which is located below the double line. Above the line one can
usually see the context of _assumptions_, which can be used in the
process of constructing the proof. Currently, the assumption context
is empty, as theorem we stated does not make any and ventures to proof
[True] out of thin air. Fortunately, this is quite easy to do, as from
the formulation of the [True] type we already know that it is
inhabited by its only constructor [I]. The next line proved the
_exact_ value of the type of the goal.

*)

exact I.

(** 

This completes the proof, which is indicated by the display [*response*]:
[[
No more subgoals.
(dependent evars:)
]]
The only thing left to complete the proof is to inform Coq that now
the Theorem [true_is_true] is proved, which is achieved by typing the
keyword [Qed].

*)

Qed.

(**
[true_is_true is defined]

In fact, typing [Qed] invokes a series of additional checks, which
ensure the well-formedness of the constructed proof term. Although the
proof of [true_is_true] is obviously valid, in general there is a
number of proof term properties to be checked _a posteriori_ and
particularly essential in the case of proofs about infinite objects,
which we do not cover in these notes (see %Chapter~13%
of%~\cite{Bertot-Casteran:BOOK}% for a detailed discussion on such
proofs).

So, our first theorem is proved. As it was hinted previously, it could
have been stated even more concisely, formulated as a mere definition,
and proved by means of providing a corresponding value, without the
need to enter a proof mode:

*)

Definition true_is_true': True := I.

(**

Although this is a valid way to prove statements in Coq, it is not as
convenient as an interactive proof mode, when it comes to the
construction of large proofs, arising from complicated
statements. This is why, when it comes to proving propositions, we
will prefer the interactive proof mode to the "vanilla" program
definition. It is worth noticing, thought, that even though the
process of proof construction in Coq usually looks more like writing a
_script_, consisting from a number of commands (which are called
_tactics_ in Coq jargon), the result of such script, given that it
eliminates all goals, is a valid well-typed program. In comparison, in
some other dependently-typed frameworks, the construction of proof
terms does not obscure the fact that what is being constructed is a
program, so the resulting interactive proof process is formulated as
"filling the holes" in a program (i.e., a proof-term), which is being
gradually refined. We step away from the discussion on which of these
two views to the proof term construction is more appropriate.

There is one more important difference between values defined by as
[Definition]s and [Theorem]s. While both define what in fact is a
proof terms for the declared type, the value bound by [Definition] is
_transparent_: it can be executed by means of unfolding and subsequent
evaluation of its body. In contrast, a proof term bound by means of
[Theorem] is _opaque_, which means that its body cannot be evaluated
and serves the only purpose: establish the fact that the corresponding
type (the theorem's statement) is inhabited, and, therefore is true.
This distinction between definitions and theorems arises from the
notion of _proof irrelevance_, which, informally, postulates that one
shouldn't be able to distinguish between two proofs of the same
statement as long as they both are valid. Conversely, the programs
(that is what is bound by means of [Definition]) are typically of
interest by themselves, not only because of the type they return.

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
definition evaluates to it body.
*)


(**

A more practical analogy for the discussed above distinction can be
drawn if one will think of [Definition]s as of mere functions,
packaged into libraries and intended to be used by third-party
clients. In the same spirit, on can think of [Theorem]s as of facts
that need to be checked only once when established, so no one would
bother to re-prove them again, knowing that they are valid, and just
appeal to their types (statement) without exploring the
proof.%\footnote{While we consider this to be a valid analogy to the
process of functioning of the mathematical community, it is only true
in spirit. In the real life, the statements proved once, are usually
re-proved by students by didactical reasons, in order to understand
the proof principles and be able to produce other proofs. Furthermore,
the history of mathematics witnessed a number of proofs that have been
later invalidated as being non-valid. Luckily, the
mechanically-checked proofs are usually not a subject of this
problem.}% This is similar to what is happening during the oral
examinations on mathematical disciplines: a student is supposed to
remember the statements of theorems from the _previous_ courses and
semesters, but is not expected to reproduce their proofs.

At this point, an attentive reader can notice that the definition of
[True] in Coq is strikingly similar to the definition of the type
[unit] from %Chapter~\ref{ch:funprog}%. This is a fair observation,
which brings us again to the Curry-Howard analogy, at makes it
possible to claim that the trivial truth proposition is isomorphic to
the [unit] type from functional programming. Indeed, both have just
one way to be constructed and can be constructed in any context, as
their single constructor does not require any arguments.

Thinking by analogy, one can now guess how the falsehood can be encoded.
*)

Print False.

(**
[Inductive False : Prop :=  ]

Unsurprisingly, the proposition [False] in Coq is just a Curry-Howard
counterpart of the type [empty], which we have constructed in
%Chapter~\ref{ch:funprog}%. Moreover, the same intuition that was
applicable to [empty]'s recursion principle ("anything can be produced
given an element of an empty set"), is applicable to reasoning by
induction with the [False] proposition:

*)

Check False_ind.

(**
[[
False_ind
     : forall P : Prop, False -> P
]]

That is, _any_ proposition can be derived from the falsehood by means
of implication.%\footnote{In the light of Curry-Howard analogy, at
this moment it shouldn't be surprising that Coq uses the arrow
notation [->] both for function types and for propositional
implication: after all, they both are just particular cases of
functional abstraction, in sorts [Set] or [Prop], correspondingly.}%
For instance, we can prove now that [False] implies the equality [1 =
2].%\footnote{We postpone the definition of the equality till the next
chapter, and for now let us consider it just a some proposition.}%

*)

Theorem one_eq_two: False -> 1 = 2.
Proof.

(** 

One way to prove this statement is to use the [False] induction
principle, i.e., the theorem [False_ind], directly by instantiating it
with the right predicate [P]:

*)

exact (False_ind (1 = 2)).

(**

This indeed proves the theorem, but for now, let us explore a couple
of other ways to prove the same statement. For this we first Undo the
last command of the already succeeded but not yet completed proof.

*)

Undo.

(**

Instead of supplying the argument [(1 = 2)] to [False_ind] manually,
we can leave it to Coq to figure out, what it should be, by using the
SSReflect [apply:] tactic.

*)

apply: False_ind.

(** 

The following thing just happened: the tactic [apply:] supplied with
an argument [False_ind], tried to figure out whether our goal [False
-> (1 = 2)] matches any _head_ type of the theorem [False_ind]. By
_head type_ we mean a component of type (in this case, [forall P :
Prop, False -> P]), which is a type by itself and possibly contains
free variables. For instance, recalling that [->] is
right-associative, head-types of [False_ind] would be [P], [False ->
P] and [forall P : Prop, False -> P] itself. 

So, in our example, the call to the tactics [apply: False_ind] makes
Coq realise that the goal we are trying to prove matches the type
[False -> P], where [P] is taken to be [(1 = 2)]. Since in this case
there is no restrictions on what [P] can be (as it is
universally-quantified in the type of [False_ind]), Coq assigns [P] to
be [(1 = 2)], which, after such specialization, turns the type of
[False_ind] to be exactly the goal we're after, and the proof is done.

There are many more ways to prove this rather trivial statement, but
at this moment we will demonstrate just yet another one, which does
not appeal to the [False_ind] induction principle, but instead
proceeds by _case analysis_.

*)

Undo.

case.

(**

The tactic [case] makes Coq to perform the case analysis. In
particular, it _deconstructs_ the _top element_ of the goal, which is
an implication. The top element is such that it comes first before any
arrows, and in this case it is a value of type [False]. Then, for all
constructors of the type, whose value is being case-analysed, the
tactic [case] constructs _subgoals_ to be proved. Informally, in
mathematical reasoning, the invocation of the [case] tactic would
correspond to the statement "let us consider all possible cases, which
imply the top element proposition". Naturally, since [False] has _no_
constructors (as it corresponds to the [empty] type), the case
analysis on it produces _zero_ subgoals, which completes the proof
immediately. Since the result of the proof is just some program,
again, we can demonstrate the effect of [case] tactic by proving the
same theorem with an exact proof term:

*)

Undo.

exact (fun (f: False) => match f with end).

(**

As we can see, one valid proof term of [one_eq_two] is just a
function, which case-analyses on the value of type [False], and such
case-analysis has no branches.

*)

Qed.

(** * Implication and universal quantification

By this moment we have already seen how implication is represented in
Coq: it is just a functional type, represented by an "arrow" notation
[->] and familiar to all functional programmers. Indeed, if a function
of type [A -> B] is a program that takes an argument value of type [A]
and returns a result value of type [B], then the propositional
implication [P -> Q]  ...


*)

(**

TODO:

*)



(** * Logical connectives 

TODO: Present conjunction and disjunction

*)


(** * Existential quantification

TODO: Present the ex type

*)

(** * Expressing negation

TODO: Show some proofs by negation

*)


(** * Missing axioms from the classical logic

TODO: discuss axioms of the classical logics

*)


(** * Impredicativity of [Prop] and Coq's sort hierarchy 

*)

(** * [Prop] versus [bool]

TODO: Emphasize that in Prop you can use quantifiers, whereas [bool]
is as expressive as simple propositional logic (which is its strength,
thank to Coq's terminating computations)

*)


(** 

* The basics of boolean reflection

*)


(* Definition append_lm (A: eqType) (x: A) (xs ys: seq A):  *)
(*   x \in xs -> index x xs = index x (xs ++ ys). *)

(* Proof. *)
(* elim: xs=>// a ls Ih. *)
(* rewrite inE; case/orP; first by move/eqP=>->/=; rewrite !eq_refl. *)
(* by move/Ih=>/=->. *)
(* Qed. *)

(* Set Printing Universes. *)
(* Check (forall A : Set, list A) : Set. *)
