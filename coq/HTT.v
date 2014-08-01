(** %
\chapter{Case Study: Program Verification in Hoare Type Theory}
\label{ch:htt}
% *)

(* begin hide *)
Module HTT.
(* end hide *)

(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing first %\texttt{{first}}% *)
(** printing last %\texttt{\emph{last}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)
(** printing >-> %\texttt{>->}% *)
(** printing LoadPath %\texttt{\emph{LoadPath}}% *)
(** printing exists %\texttt{{exists}}% *)
(** printing do %\texttt{{do}}% *)

(** 

In this chapter, we will be working with a fairly large case study
that makes use of most of Coq's features as a programming languages
with dependent types and as a framework to build proofs and reason
about mathematical theories.

Programming language practitioners usuale elaborate on the dichotomy
between _declarative_ and _imperative_ languages, emphasizing the fact
%\index{declarative programming}\index{imperative programming}% that a
program written in declarative language is pretty much documenting
itself, as it already specifies the _result_ of a
computation. Therefore, logic and constraint programming languages
(such as Prolog and Ciao%~\cite{Hermenegildo-al:TPLP12}\index{Ciao}%)
as well as data definition/manipulation languages (e.g., SQL), whose
programs are just sets of constraints/logical clauses or queries
describing the desired result, are naturally considered to be
declarative. Very often, pure functional programming languages (e.g.,
Haskell) are considered declarative as well, The reason for this is
the _referential transparency_ property, which ensures that programs
in such language %\index{referential transparency}% are in fact
effect-free expressions, evaluating to some result (similar to
mathematical functions). Therefore, such programs, whose outcome is
only their result as an expression, but not some side effect (e.g.,
output to a file), can be replaced safely by their result, if it's
computable. This possibility provides a convenient way of algebraic
reasoning about such programs by means of equality
rewritings---precisely what we were observing and leveraging in
%Chapters~\ref{ch:eqrew} and~\ref{ch:ssrstyle}% of this course in the
context of Coq taken as a functional programming language.

%\index{specification|see {program specification}}%

That said, pure functional programs tend to be considered to be good
specifications for themselves. Of course, the term "specification" (or
simply, "spec") %\index{program specification}% is overloaded and in
some context it might mean the result of the program, its effect or
some algebraic properties. While a functional program is already a
good description of its result (due to referential transparency), its
algebraic properties (e.g., some equalities that hold over it) are
usually a subject of separate statements, which should be proved. Good
example of such properties are the commutativity and cancellation
statements, which we proved for natural numbers on
page%~\pageref{pg:addnprops} of Chapter~\ref{ch:depstruct}%. Another
classical series of examples, which we did not focus in this course,
are properties of list functions, such as appending and reversal
(e.g., that the list reversal is an inverse to itself).%\footnote{A
typical anti-pattern in dependently-typed languages and Coq in
particular is to encode such algebraic properties into the definitions
of the datatypes and functions themselves (a chrestomathic example of
such approach are length-indexed lists). While this approach looks
appealing, as it demonstrates the power of dependent types to capture
certain properties of datatypes and functions on them, it is
inherently non-scalable, as there will be always another property of
interest, which has not been foreseen by a designer of the
datatype/function, so it will have to be encoded as an external fact
anyway. This is why we advocate the approach, in which datatypes and
functions are defined as close to the way they would be defined by a
programmer as possible, and all necessary properties are proved
separately.}%

The situation is different when it comes to imperative programs, whose
outcome is typically their side-effect and is achieved by means of
manipulating mutable state or performing input/output. While some of
the modern programming languages (e.g., Scala, OCaml) allow one to mix
imperative and declarative programming styles, it is significantly
harder to reason about such programs, as now they cannot be simply
replaced by their results: one should also take into account the
effect of their execution (i.e., changes in the mutable state). A very
distinct approach to incorporating both imperative and declarative
programming is taken by Haskell, in which effectful programs can
always be distinguished from pure ones by means of enforcing the
former ones to have very specific
types%~\cite{PeytonJones-Wadler:POPL93}%---the idea we will elaborate
more on a bit further.

In the following sections of this chapter, we will learn how Coq can
be used to give specifications to imperative programs, written in a
language, similar to C. Moreover, we will observe how the familiar
proof construction machinery can be used to establish the correctness
of these specifications, therefore, providing a way to _verify_ a
program by means of checking, whether it satisfies a given spec. In
particular, we will learn how the effects of state-manipulating
programs can be specified via dependent types, and the specifications
of separate effectful programs can be _composed_, therefore allowing
us to structure the reasoning in the modular way, similarly to
mathematics, where one needs to prove a theorem only once and then can
just rely on its statement, so it can be employed in the proofs of
other facts.

* Imperative programs and their specifications
%\label{sec:imp-spec}%

The first attempts to specify the behaviour of a state-manipulating
imperative program with assignments originate in late '60s and are due
to Tony Hoare%~\cite{Hoare:CACM69}%, who considered programs in a
simple imperative language with mutable variables (but without
pointers or procedures) and suggested to give a specification to a
program $c$ in the form of the triple $\spec{P}~c~\spec{Q}$, where $P$
and $Q$ are logical propositions, describing the values of the mutable
programs and possible relations between them. $P$ and $Q$ are usually
%\index{assertions}% referred to as _assertions_; more specifically,
$P$ is called %\index{precondition}\index{postcondition}%
_precondition_ of $c$ (or just "pre"), whereas $Q$ is called
_postcondition_ (or simply "post"). The triple $\spec{P}~c~\spec{Q}$
is traditionally referred to as _Hoare triple_.%\index{Hoare
triple}%%\footnote{The initial syntax for the triples by Hoare, was
$\specK{P}~\set{c}~\specK{Q}$. The notation $\spec{P}~c~\spec{Q}$,
which is now used consistently is due to Wirth and emphasizes the
comment-like nature of the assertion in the syntax reminiscent to the
one of Pascal.}% Its intuitive semantics can be expressed as follows:
%\label{pg:triple}% "if right before the program $c$ is executed
the state of mutable variables is described by a proposition $P$,
then, _if $c$ terminates_, the resulting state satisfies the
proposition $Q$".

The reservation on termination of the program $c$ is important. In
fact, while the Hoare triples in their simple form make sense only for
terminating programs, it is possible to specify non-terminating
programs as well. This is due to the fact that the semantics of a
Hoare triple implies that a non-terminating program can be given _any_
postcondition, as one won't be able to check it anyway, as the program
will never reach the final state.%\footnote{This intuition is
consistent with the one, enforced by Coq's termination checker, which
allows only terminating programs to be written, since non-terminating
program can be given any type and therefore compromise the consistency
of the whole underlying logical framework of CIC.}% Such
interpretation of a Hoare triple "modulo termination" is referred to
as _partial correctness_, and in this chapter we will focus on it. It
is possible to give to a Hoare triple $\spec{P}~c~\spec{Q}$ a
different interpretation, which would deliver a stronger property: "if
right before the program $c$ is executed the state of mutable
variables is described by a proposition $P$, then $c$ terminates and
the resulting state satisfies the proposition $Q$". Such property is
called _total correctness_ and requires tracking some sort of "fuel"
for the program in the assertions, so it could run further. We do not
consider total correctness in this course and instead refer the reader
to the relevant research results on Hoare-style specifications with
resource bounds%~\cite{Dockins-Hobor:DS10}%.

** Specifying and verifying programs in a Hoare logic
%\label{sec:hoare-primer}%

The original Hoare logic worked over a very simplistic imperative
language with cycles, conditional operators and assignments. This is
how one can specify a program, which just assigns 3 to a specific
variable named%~\texttt{x}%:
%
\begin{alltt}
\(\spec{\True}\) x := 3 \(\spec{x = 3}\)
\end{alltt} 
%

That is, the program's precondition doesn't make any specific
assumptions, which is simply expressed by the proposition $\True$; the
postcondition ensures that the value of a mutable variable
%\texttt{x}% is equal to three. 

The formalism, which allows us to validate particular Hoare triples
for specific programs is called _program logic_ (or, equivalently,
_Hoare logic_).  
%\index{program logic}\index{program logic|see {Hoare logic}}%

Intuitively, logic in general is a formal system, which consists of
axioms (propositions, whose inhabitance is postulated) and _inference
rules_, %\index{inference rules}% which allow one to construct proofs
of larger propositions out of proofs of small ones. This is very much
of the spirit of %Chapter~\ref{ch:logic}%, where we were focusing on a
particular formalism---propositional logic. Its _inference rules_ were
encoded by means of Coq's _datatype constructors_. For instance, in
order to construct a proof of conjunction (i.e., inhabit a proposition
of type [A /\ B]), one should have provided a proof of a proposition
[A] and a proposition [B] and then _apply_ the only conjunction's
constructor [conj], as described in %Section~\ref{sec:conjdisj}%. The
logicians, however, prefer to write inference rules as "something with
a bar". Therefore, an inference rule for conjunction introduction in
the constructive logic looks as follows:

%
\begin{mathpar}
\inferrule*[Right={($\wedge$-{Intro})}]
 {A \\ B}
 {A \wedge B}
\end{mathpar}
%

That is the rule %\Rule{$\wedge$-Intro}% is just a paraphrase of the
[conj] constructor, which specifies how an instance of conjunction is
constructor. Similarly, the disjunction [or] has two inference rules,
for one constructor each. The elimination rules are converses of the
introduction rules and formalize the intuition behind the case
analysis. An alternative example of an inference rule for a
proposition encoded by means of Coq's datatype constructor is the
definition of the predicate for _beautiful_ numbers [beautiful] from
%Section~\ref{sec:cannot}%. There, the constructor [b_sum] serves as
an inference rule that, given the proofs that [n'] is beautiful and
[m'] is beautiful, constructs the proof of the fact that their sum is
beautiful.%\footnote{Actually, some courses on Coq introduce datatype
constructors exactly from this perspective---as a programming
counterpart of the introduction rules for particular kinds of
propositions~\cite{Pierce-al:SF}. We came to the same analogy by
starting from a different and exploring the datatypes in the
programming perspective first.}%

Hoare logic also suggests a number of axioms and inference rules that
specify which Hoare triple can be in fact inferred. We postpone the
description of their encoding by means of Coq's datatypes till
%Section~\ref{sec:htt-intro}% of this chapter and so far demonstrate
some of them in the logical notation "with a bar". For example, the
Hoare triple for a variable assignment is formed by the following rule:
%
\begin{mathpar}
\inferrule*[Right={(Assign)}]
 {}
 {\spec{Q[e/x]}~ x := e ~\spec{Q}}
\end{mathpar}
%

The rule %\Rule{Assign}% is in fact an axiom (since it does not assume
anything, i.e., does not take any arguments), which states that if a
proposition $Q$ is valid after substituting all occurrences of $x$ in
it with $e$ (which is denoted by $[e/x]$), then it is a valid
postcondition for the assignment. The inference rule for sequential
composition is actually a constructor, which takes the proofs of Hoare
triples for $c_1$ and $c_2$ and then delivers a composed program $c_1;
c_2$ _as well as_ the proof for the corresponding Hoare triple,
ensuring that the postcondition of $c_1$ matches the precondition of $c_2$.
%\index{sequential composition}%

%
\begin{mathpar}
\inferrule*[Right={(Seq)}]
 {\spec{P}~ c_1~\spec{R}\\
  \spec{R}~ c_2 ~\spec{Q}}
 {\spec{P}~ c_1; c_2 ~\spec{Q}}
\end{mathpar}
%

The rule %\Rule{Seq}% is in fact too "tight", as it requires the two
composed program agree exactly on their post-/preconditions. In order
to relax this restriction, on can use the _rule of consequence_, which
%\index{rule of consequence}% makes it possible to _strengthen_ the
precondition and _weaken_ the postcondition of a program. Intuitively,
such rule is adequate, since the program that is fine to be run in a
precondition $P'$, can be equivalently run in a stronger precondition
$P$ (i.e., the one that implies $P'$). Conversely, if the program
terminates in a postcondition $Q'$, it would not hurt to weaken this
postcondition to $Q$, such that $Q'$ implies $Q$.

%
\begin{mathpar}
\inferrule*[Right={(Conseq)}]
 {P \implies P' \\
  \spec{P'}~ c~ \spec{Q'}\\
  Q' \implies Q}
 {\spec{P}~ c~\spec{Q}}
\end{mathpar}
%

With this respect, we can draw the analogy between Hoare triples and
function types of the form [A -> B], such that the rule of consequence
of a Hoare triple corresponds to subtyping of function types, where
the precondition [P] is analogous to an argument type [A] and the
postcondition [Q] is analogous to a result type [B]. Similarly to the
functions with subtyping, Hoare triples are covariant with respect to
consequence with respect to their postcondition and _contravariant_
with respect to the argument type%~\cite[Chapter 15]{Pierce:BOOK02}%.
%\index{covariance}\index{contravariance}% This is the reason why,
when establishing a specification, one should strive to infer the
_weakest precondition and the strongest postcondition_ to get the
tightest possible (i.e., the most precise) spec, which can be later
weakened using the %\Rule{Conseq}% rule. 

The observed similarity between functions and commands in a Hoare
logic should serve as a good indicator that, perhaps, it would be a
good idea to implement the Hoare logic in a form of type
system. Getting a bit ahead of ourselves, this is exactly what is
going to happen (as the title of the chapter suggests).

At this point we can already see a simple paper-and-pencil proof of a
program that manipulates with mutable variables. In the Hoare logic
tradition, since most of the programs are typically compositions of
small programs, the proofs of specifications are written to follow the
structure of the program, so the first assertion corresponds to the
overall precondition, the last one is the overall postconditions, and
the intermediate assertions correspond to $R$ from the rule
%\Rule{Seq}% modulo weakening via the rule %\Rule{Conseq}%. Let us
prove the following Hoare-style specification for a program that swaps
the values of two variables $x$ and $y$.

%
\begin{alltt}
\(\spec{x = a \wedge y = b}\) t := \var{x}; \var{x} := \var{y}; \var{y} := t \(\spec{x = b \wedge y = a}\)
\end{alltt}
%

The variables are called _logical_ and are used in order to name
%\index{logical variables}% unspecified values, which are subject of
manipulation in the program, and their identity should be
preserved. The logical variables are implicitly universally quantified
over in the scope of the whole Hoare triple they appear, but usually
the quantifiers are omitted, so, in fact, the specification above
should have been read as follows.

%
\begin{alltt}
\(\forall a b, \spec{x = a \wedge y = b}\) t := \var{x}; \var{x} := \var{y}; \var{y} := t \(\spec{x = b \wedge y = a}\)
\end{alltt}
%

This universal quantification should give some hints that converting
Hoare triples into types will, presumably, require to make some use of
dependent types in order to express value-polymorphism, similarly to
how the universal quantification has been previously used in Coq. Let
us see a proof sketch of the above stated specification with
explanations of the rules applied after each assertion.

%
\begin{alltt}
\(\spec{x = a \wedge y = b}\) {\normalfont {The precondition}}
  t := \var{x}; 
\(\spec{x = a \wedge y = b \wedge t = a} \) {\normalfont{by \Rule{Assign} and equality}}
  \var{x} := \var{y}; 
\(\spec{x = b \wedge y = b \wedge t = a} \) {\normalfont{by \Rule{Assign} and equality}}
  \var{y} := t 
\(\spec{x = b \wedge y = a} \) {\normalfont{by \Rule{Assign} equality and weakening via \Rule{Conseq}}}
\end{alltt}
%

The list of program constructs and inference rules for them would be
incomplete without conditional operators.

%
\begin{mathpar}
\inferrule*[Right={(Cond)}]
 {\spec{P \wedge e}~ c_1~\spec{Q}\\
  \spec{P \wedge \neg e}~ c_2~\spec{Q}}
 {\spec{P}~ \mathtt{if}~e~\mathtt{then}~c_1~\mathtt{else}~c_2~\spec{Q}}
\\
\inferrule*[Right={(While)}]
 {\spec{I \wedge e}~ c~\spec{I}}
 {\spec{I}~ \mathtt{while}~e~\mathtt{do}~c~\spec{I \wedge \neg e }}
\end{mathpar}
%

The inference rule for a conditional statement should be intuitively
clear and reminds of a typing rule for conditionals in Haskell or
OCaml, which requires both branches of the statement to have the same
type (and here, equivalently to satisfy the same postcondition). The
rule %\Rule{While}% for the loops is more interesting, as it makes use
of the %\index{loop invariant}% proposition $I$, which is called _loop
invariant_. Whenever the body of the cycle is entered, the invariant
should hold (as well as the condition $e$, since the iteration has
just started). Upon finishing, the body $c$ should restore the
invariant, so the next iteration would start in a consistent state
again. Generally, it takes a human prover's intuition to come up with
a non-trivial resource invariant fo a loop, so it can be used in the
res of the program. Inference of the best loop invariant is an
undecidable problem in general and it has a deep relation to type
inference with polymorphically-recursive
functions%~\cite{Henglein:TOPLAS93}%. This should not be very
surprising, since every loop can be encoded as a recursive function,
and, since as we have already started guessing, Hoare triples are
reminiscent to types, automatic inferring of loop invariants
corresponds to type inference for recursive functions. In the
subsequent sections we will see examples of looping/recursive programs
with loop invariants and exercise in establishing some of them.

** Adequacy of a Hoare logic

The original Hoare logic is often referred to as _axiomatic semantics_
of imperative programs. This term is only partially accurate, as it
implies that the Hoare triples describe precisely what is the program
and how it behaves. Even though Hoare logic can be seen as a program
semantics as a way to describe the program's behaviour, it is usually
not the only semantics, which imperative programs are given. In
particular, it does not say how a program should be executed---a
question answered by operational
semantics%~\cite{Winskel:BOOK}%. Rather, Hoare logic allows one to
make statements about the effect the program takes to the mutable
state, and, what is more important, construct finite proofs of these
statements. With this respect, Hoare logic serves the same purpose as
type systems in many programming languages---determine statically
(i.e., without _executing_ the program), whether the program is
well-behave or not. In other words, it serves as an "approximation" of
another, more low-level semantics of a program, which is also implied
by the very definition of a hoare triple on
page%~\pageref{pg:triple}%, which relies to the fact that a program
can be executed.

That said, in order to use a Hoare logic for specifying and verifying
a program's behaviour, a _soundness_ result should be first
%\index{soundness of a logic}% established. In the case of a program
logic, soundness means the logic rules allow one to infer only those
statements that do not contradict the definition of a Hoare triple
(page%~\pageref{pg:triple}%). This result can be proven in many
different ways, and the nature of the proof usually depend on the
underlying operational/denotational semantics, which is typically not
questioned, being self-obvious, and defines precisely what does it
mean for a program _to be executed_. Traditional ways of proving
soundness of a program logic are reminiscent to the approaches for
establishing soundness of type
systems%~\cite{Pierce:BOOK02,Wright-Felleisen:IC94}%. Of course, all
program logics discussed in this chapter have been proven to be sound
with respect to some reasonable operational/denotational semantics.

* Basics of Separation Logic
%\label{sec:seplog}%

The original Hoare logic has many limitations. It works only with
mutable variables and does not admit procedures or first-order
code. But the most its sever limitation becomes evident when it comes
to specifying programs that manipulate with _pointers_, i.e., the most
interesting imperative cases of imperative code. %\index{pointers}%
In the presence of pointers and a heap, mutable variables become
somewhat redundant, so for now by _local variables_ we will be
assuming immutable assigned once variables, akin to those bound by the
%\texttt{let}%-expression. Such variables can, however, have pointers
as their values.

Let us first enrich the imperative programming language of interest to
account for the presence of heap and pointers. We will be using the
syntax %\texttt{x ::= e}% to denote the assignment of a value
%\texttt{e}% to the pointer bound by %\texttt{x}%. Similarly, the
syntax %\texttt{!e}% stands for dereferencing a pointer, whose address
is a value obtained by evaluating a _pure_ expression %\texttt{e}%. We
will assume that every program returns a result (and the result of a
pointer assignment is of type [unit]). To account for this, we will be
using the syntax %\texttt{x~<-~c1;~c2}% (pronounced "bind") as a
generalization of the sequential composition from
%Section~\ref{sec:hoare-primer}%. The bind first executes the program
%\texttt{c1}%, _binds_ this %\index{binding}% result to an immutable
variable %\texttt{x}% and proceeds to the execution of the program
%\texttt{c2}%, which can possibly make use of the variable
%\texttt{x}%, so all the occurrences of %\texttt{x}% in it are
replaced by its value before it starts evaluating. If the result of
%\texttt{c1}% is not used by %\texttt{c2}%, we will use the
abbreviation %\texttt{c1;; c2}% to denote this case.

Specifications in the simple Hoare logic for mutable variables,
demonstrated in %Section~\ref{sec:hoare-primer}% are stated over
mutable _local_ variables, which are implicitly supposed to be all
distinct, as they have distinct names. In a language with a heap and
pointers, the state is no longer a set of mutable variables, but the
heap itself, which %\index{heap}% can be thought of as a partial map
from natural numbers to arbitrary values. In a program, operating with
a heap, two pointer variables, $x$ and $y$ can in fact be _aliases_,
%\index{aliasing}% i.e., refer to the same memory entry, and,
therefore, changing a value of a pointer, referenced by $x$ will
affect the value, pointed to by $y$. An aliasing is what renders
reasoning in the standard Hoare logic tedious and unbearable. To
illustrate the problem, let us consider the following program, which
runs in the assumption that the heap, which is being available to the
program, has only two entries with addresses, referred to by local
variables $x$ and $y$ correspondingly, so does the specification
states by means of the "points-to" assertions $x \mapsto -$, where $x$
is assumed to be a pointer value.  %\index{points-to assertions}%

%
\begin{alltt}
\(\spec{x \mapsto - \wedge y \mapsto Y}\) \var{x} ::= 5 \(\spec{ x \mapsto 5 \wedge y \mapsto Y }\)
\end{alltt}
%

The logical variable $Y$ is of importance, as it is used to state that
the value of the pointer $y$%\footnote{We will abuse the terminology
and refer to the values and immutable local variables uniformly, as,
unlike the setting of Section~\ref{sec:imp-spec}, the later ones are
assumed to substituted by the former ones during the evaluation
anyway.}% remains unchanged after the program has terminated. Alas,
this specification is not correct, as the conjunction of the two does
not distinguish between the case when $x$ and $y$ are the same pointer
and when they are not, which is precisely the aliasing problem. It is
not difficult to fix the specification for this particular problem by
adding a conditional statement (or, equivalently, a disjunction) into
the postcondition that would describe two different outcomes of the
execution with respect to the value of $y$, depending on the fact
whether $x$ and $y$ are aliases or not. However, if a program
manipulates with a large number of pointers, or, even worse, with an
array (which is obviously just a sequential batch of pointers), things
will soon go wild, and the conditionals with respect to equality or
non-equality of certain pointers pollute all the specifications,
rendering them unreadable and eventually useless. This was precisely
the reason, why after being discovered in late '60s and investigated
for a decade, Hoare-style logics we soon almost dismissed as a
specification and verification method, due to the immense complexity
of the reasoning process nad overwhelming proof obligations.

The situation has changed when in 2002 John C. Reynolds, Peter
%\index{separation logic|textbf}% O'Hearn, Samin Ishtiaq and Hongseok
Yang suggested an alternative way to state Hoare-style assertions
about heap-manipulating programs with
pointers%~\cite{Reynolds:LICS02}%. The key idea was to make _explicit_
the fact of disjuntion (or, _separation_) between different parts of a
heap in the pre- and postconditions. This insight made it possible to
reason about disjointness of heaps and absence of aliasing without the
need to emit side conditions about equality of pointers. The resultgin
formal system received the name _separation logic_, and below we
consider a number of examples to specify and verify programs in it.

For instance, the program, shown above, which assigns $5$ to a pointer
$x$ can now be given the following specification in the separation
logic:

%
\begin{alltt}
\(\spec{h | h = x \mapsto - \join y \mapsto Y}\) \var{x} ::= 5 \(\spec{\res, h | h = x \mapsto 5 \join y \mapsto Y}\)
\end{alltt}
%

We emphasize the fact that the heaps, being just partial maps from
natural numbers to arbitrary values are elements of a PCM
%(Section~\ref{sec:pcms})% with the operation $\join$ taken to be a
disjoint union and the unit element to be an empty heap (denoted
$\hempty$). %\index{PCM}% The above assertions therefore ensure that,
before the program starts, it operates in a heap $h$, such that $h$ is
a partial map, consisting of two _different_ pointers, $x$ and $y$,
such that $y$ points to some universally-quantified value $Y$, and the
content of $x$ is of no importance (which is denoted by [-]). The
postcondition makes it explicit that only the value of the pointer $x$
has not changed, and the value of $y$ remained the same. The
postcondition also mentions the result $\res$ of the whole
ooperations, which is, however not constrained anyhow, since, as it
has been stated, it is just a value of type [unit].%\footnote{The
classical formulation of Separation Logic~\cite{Reynolds:LICS02}
introduce the logical operator $\sep$, dubbed \emph{separating
conjunction}, \index{separating conjunction} which allows to describe
the split of a heap $h$ into two disjoin parts, without mentioning $h$
explicitly. That is, the assertion $P \sep Q$ holds over a heap $h$,
if there exist heaps $h_1$ and $h_2$, such that $h = h_1 \join h_2$,
$P$ is satisfied by $h_1$ and $Q$ is satisfied by $h_2$. We will stick
to the ``explicit'' notation, though, as it allows for greater
flexibility when stating the assertions, mixing both heaps and
values.}%

** Selected rules of Separation Logic

Let us now revise some of the rules of Hoare logic and see how they
will look in separation logic. The rules, stated over the heap, are
typically given in the _small footprint_ %\index{small footprint}%,
meaning that they are stated with the smalles possible heap and assume
that the "rest" of the heap, which is unaffected by the program
specified, can be safely assumed. The rules for assigning and reading
the pointers are natural.

%
\begin{mathpar}
\inferrule*[Right={(Assign)}]
 {}
 {\spec{h ~|~ h = x \mapsto -}~ x ::= e ~\spec{\res, h ~|~ h = x \mapsto e}}
\and
\inferrule*[Right={(Read)}]
 {}
 {\spec{h ~|~ h = x \mapsto v}~ !x ~\spec{\res, h ~|~ h = x \mapsto v \wedge \res = v}}
\end{mathpar}
%

Notice, though, that, unlike the original Hoare logic for mutable
variables, the rule for writing explicitly requires the pointer $x$ to
be present in the heap. In other words, the corresponding memory cell
should be already _allocated_. This is why the traditional separation
logic assumes presence of an allocator, which can allocate new memory
cells and dispose them via the effectful functions %\texttt{alloc()}%
and %\texttt{dealloc()}%, correspondingly.

%
\begin{mathpar}
\inferrule*[Right={(Alloc)}]
 {}
 {\spec{h ~|~ h = h'}~ \com{alloc}(v) ~\spec{\res, h ~|~ h = \res \mapsto v \join h'}}
\and
\inferrule*[Right={(Dealloc)}]
 {}
 {\spec{h ~|~ h = x \mapsto - \join h'}~ \com{dealloc}(x) ~\spec{\res, h ~|~ h = h'}}
\end{mathpar}
%

For the sake of demonstration, the rules for $\com{alloc}()$ and
$\com{dealloc}()$ are given in a _large footprint_, which, incontrast
with %\index{large footprint}% small fottprint-specifications mentions
the "additional" heap $h'$ in the pre- and pos-conditions, which can
be arbitrarily instantiated, emphasizing that it remains unchanged
(recall that $h'$ is implicitly universally-quantified over, and its
scope is the whole triple), so the resulting is just being
"increased"/"decreadsed" by a memory entry that has been
allocated/deallocated.%\footnote{The classical separation logic
provides a so-called \emph{frame rule}, which allows for the switch
between the two flavours of footprint by attaching/removing the
additional heap $h'$. In our reasoning we will be assuming it
implicitly.}%

The rule for binding is similar to the rule for sequential composition
of programs $c_1$ and $c_2$ from the standard Hoare logic, although it
specifies that the immutable variables can substituted in $c_2$.

%
\begin{mathpar}
\inferrule*[Right={(Bind)}]
 {\spec{h ~|~ P(h) }~c_1~\spec{\res, h ~|~ Q(\res, h)} \\
 \spec{h ~|~ Q(x, h) }~c_2~\spec{\res, h ~|~ R(\res, h)}}
 {\spec{h ~|~ P(h)}~ x \asgn c_1; c_2 ~\spec{\res, h ~|~ R(\res, h)}}
\end{mathpar}
%

The predicates $P$, $Q$ and $R$ in the rule %\Rule{Bind}% are
considered to be functions of the heap and result,
correspondingly. This is why for the second program, $c_2$, the
predicate $Q$ in a precondition is instantiated with $x$, which can
occur as a free variable in $c_2$. The rule of weakening
%\Rule{Conseq}% is similar to the one from Hoare logic module the
technical details on how to weaken heap/result parametrized functions,
so we omit it here as an intuitive one. The rule for conditional
operator is the same one as in %Section~\ref{sec:hoare-primer}%, as
well.

In order to support functions in separation logic, we need to consider
two additional rules---for function invocation and returning a value. 

%
\begin{mathpar}
\inferrule*[Right={(Return)}]
 {} 
 {\spec{h ~|~ P(h)}~ \ret e ~\spec{\res, h ~|~ P(h) \wedge \res = e}}
\and
\inferrule*[Right={(Hyp)}]
 {\forall x, \spec{h ~|~ P(x, h)}~f(x)~\spec{\res, h ~|~ Q(x, \res, h)} \in \Gamma}
 {\Gamma \vdash \forall x, \spec{h ~|~ P(x, h)}~f(x)~\spec{\res, h ~|~ Q(x, \res, h)}}
\and
\inferrule*[Right={(App)}]
 {\forall x, \spec{h ~|~ P(x, h) }~f(x)~\spec{\res, h ~|~ Q(x, \res, h)} \in \Gamma}
 {\Gamma \vdash \spec{h ~|~ P(e, h) }~f(e)~\spec{\res, h ~|~ Q(e, \res, h)}}
\end{mathpar}
%

The rule for returning simply constrants the dedicated variable $\res$
to be equal to the expression $e$. The rule %\Rule{Hyp}% (for
"hypothesis") introduce the assumption context $\Gamma$ that contains
%\index{assumption context}\index{typing context}% specifications of
available "library" functions (similarly to the typing context in
typing relations%~\cite[Chapter~9]{Pierce:BOOK02}%) and until now was
assumed to be empty. Notice that, similarly to dependently-type
functions, in the rule %\Rule{Hyp}% the pre- and postcondition in the
spec of the assumed function can depend on the value of its argument
$x$. The rule %\Rule{App}% accounts for the function application and
instantiates all occurrences of $x$ with the argument expression $e$.

Finally, sometimes we might be able to infer two different
specifications about the same program. In this case we should be able
to combine them intor one, which is stronger, and this is what the
rule of conjunction %\Rule{Conj}% serves for:

%
\begin{mathpar}
\inferrule*[Right={(Conj)}]
 {\spec{h ~|~ P_1(h) }~c~\spec{\res, h ~|~ Q_1(\res, h)} \\
 \spec{h ~|~ P_2(h) }~c~\spec{\res, h ~|~ Q_2(\res, h)}}
 {\spec{h ~|~ P_1(h) \wedge P_2(h)}~ c~\spec{\res, h ~|~ Q_1(\res, h) \wedge Q_2(\res, h)}}
\end{mathpar}
%



** On loops and recursive functions

It is well-known in a programming language folklore that every
imperative loop can be rewritten as a recursive function, which is
tail-recursive, i.e., it performs the call of itself only as the very
last statement in some possible execution branches and doesn't call
itself at all in all other branches. Therefore, recursive functions
%\index{tail recursion}% are a more expressive mechanism, as they also
allow one to write non-tail recursive programs, in which recursive
calls occur in any position.%\footnote{Although, such programs can be
made tail-recursive via the continuation-passing style transformation
(CPS)~\cite{Danvy:CPS}. They can be also converted into imperative
loops via the subsequent transformation, known as
\emph{defunctionalization}~\cite{Reynolds:ACM72}.}% Therefore, an
imperative program of the form 

%
\begin{center}
\texttt{while (e) do c}
\end{center}
% 

%\noindent% can be rewritten using a recursive function, defined via
the in-place fixport operator as

%
\begin{center}
\texttt{(fix f(x: unit). if e then c ;; f(tt) else ret tt)(tt)}
\end{center}
% 

That is, the function %\texttt{f}% is defined with an arumet of the
unit type and is immediately invoked. If the condition %\texttt{e}% is
satisfied, the body %\texttt{c}% is executed and the function calls
itself recursively; otherwise the function just returns a unit result.

Given this relation between imperative loops and effectful recursive
functions, we won't be providing a rule for loops in separation logic,
and rather provide one for recursive definitions.

%
{\small
\hspace{-10pt}
\begin{mathpar}
\inferrule*[Right={(Fix)}]
 {\Gamma, \forall x, \spec{h ~|~ P(x, h)}~f(x)~\spec{\res, h ~|~ Q(x, \res, h)} \vdash \spec{h ~|~ P(x, h)}~c~\spec{\res, h ~|~ Q(x, \res, h)}}
 {\Gamma \vdash \forall y, \spec{h ~|~ P(y, h)}~(\fix~f(x).c)(y)~\spec{\res, h ~|~ Q(y, \res, h)}}
\end{mathpar}
}
%

The premise of the rule %\Rule{Fix}% already _assumes_ the
specification of a function $f$ (i.e., its _loop invariant_)
%\index{loop invariant}% in the context $\Gamma$ and requires one to
verify its body $c$ for the same specification, similarly to how
recursive functions in some programming languges (e.g.,
Scala%~\cite[\S~4.1]{Scala-spec}%) require explicit type annotations
to be type-checked.

In the remainder of this chapter we will be always implementing
imperative loops via effectful recursive functions, whose
specifications are stated explicitly, so the rule about would be
directly applicable.

** Verifying heap-manipulating programs

Let us now see how a simple imperative program with conditionals and
recursion would be verified in a version of separation logic that we
presented here. A subject of our experiment will be an efficient
imperative implementation of the factorial-computing function, which
_accumulates_ the factorial value in a specific variable, while
decreasing its argument in a loop, end returns the value of the
accumulator when the iteration veriable becomse zero. In the
pseudocode, the %\texttt{fact}% program is implemented as follows:

%
\begin{alltt}
fun fact (\var{N}: nat): Nat = {
  n   <- alloc(\var{N});
  acc <- alloc(1); 
  res <-- 
    (fix loop (_: unit). 
      a' <-- !acc;
      n' <-- !n;
      if n' == 0 then ret a'
      else acc ::= a' * n';;
           n   ::= n' - 1;;
           loop(tt) 
    )(tt);
  dealloc(n);;
  dealloc(acc);;
  ret res
}
\end{alltt}
%

The funciont %\texttt{fact}% first allocates two ponters, %\texttt{n}%
and %\texttt{acc}% for the iteration variable and the accumulator,
correspondingly. It will then initiate the loop, implemented by the
recursive function %\texttt{loop}%, that reads the values of
%\texttt{n}% and %\texttt{acc}% into local immutable variables
%\texttt{n'}% and %\texttt{a'}%, correspondingly and then checks
whether %\texttt{n'}% is zero, in which case it returns the value of
the accumulator. Otherwise it stores into the accumulator the old
value multiplied by %\texttt{n'}%, decreases %\texttt{n}% and
re-iterates. After the loop terminates, the two pointers are
deallocated and the function returns the result.

Our goal for the reas of this section will to be verify this program
semi-formally, using the rules for separation logic presented above,
agains its _functional_ specification. In other words, we will have to
check that the program %\texttt{fact}% returns precisely the factorial
of its argument value $N$. To give such specification to
%\texttt{fact}%, we define two auxiliary mathematical functions, $F$
and $\finv$:

%
\[
f(N) = \textsf{if}~N = N'+1~\textsf{then}~N \times f(N')~\textsf{else}~1
\]
\[
\finv(n, acc, N, h) = \exists n', a', (h = n \mapsto n' \join acc \mapsto a') \wedge (f(n') \times a' = f(N))
\]
%

It is not difficult to see that $f$ define exactly the factorial
function as one would define it in a pure functional language (not
very efficiently, though, but in the most declarative form). The
$\finv$ second function is in fact a predicate, which we will use to
give the loop invariant to the loop function %\texttt{loop}%. Now, the
function %\texttt{fact}% can be given the following specification in
separation logic, stating that it does not _leak_ memory and its
result is the factorial of its argument $N$.

%
\[
\spec{h ~|~ h = \empty} ~\com{fact}(N)~ \spec{\res, h ~|~ h = \empty \wedge \res = f(N)}
\]
%

In the course of the proof of the above stated spec of $\com{fact}$,
in order to apply the rule %\Rule{Fix}% we pose the specification of
$\com{loop}$ (in the explicit assumption context $\Gamma$ from the
rules) to be the following one. The specification states that the body
of the loop preserves the invariant $\finv$, and, moreover its result
is the factorial of $N$.

%
\[
\spec{h ~|~ \finv(\com{n}, \com{acc}, N, h)} ~\com{loop}(\com{tt})~ \spec{\res, h ~|~ \finv(\com{n}, \com{acc}, N, h) \wedge \res = f(N)}
\]
%

Below, we demonstrate a proof sketch of verification of the body of
$\com{fact}$ against its specification by systematically applying all
of the presented logic rules.

%
\begin{alltt}
\(\spec{h | h = \hempty}\) {\normalfont ({by precondition})}
 n   <- alloc(\var{N});
\(\spec{h | h = \com{n} \mapsto N}\) {\normalfont ({by \Rule{Alloc} and PCM properties})}
 acc <- alloc(1); 
\(\spec{h | h = \com{n} \mapsto N \join \com{acc} \mapsto 1}\) {\normalfont ({by \Rule{Alloc}})}
\(\spec{h | \finv(\com{n}, \com{acc}, N, h)}\) {\normalfont ({by definition of \(\finv\) and \Rule{Conseq}})}
 res <-- 
  (fix loop (_: unit). 
\(\spec{h | \finv(\com{n}, \com{acc}, N, h)}\) {\normalfont (precondition)}
     a' <-- !acc;
\(\spec{h | \exists{n'}, (h=\com{n}\mapsto{n'}\join\com{acc}\mapsto\com{a'})\wedge(f(n')\times{a'}=f(N))}\) {\normalfont (\(\finv\), \Rule{Read} and \Rule{Conj})}
     n' <-- !n;
\(\spec{h | (h=\com{n}\mapsto{\com{n'}}\join\com{acc}\mapsto\com{a'})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (\Rule{Read} and \Rule{Conj})}
     if n' == 0 then ret a'
\(\spec{\res, h | (h=\com{n}\mapsto{0}\join\com{acc}\mapsto{f(N)})\wedge(\res=f(N))}\) {\normalfont (defn. \(f\), (=) and \Rule{Return})}
\(\spec{\res, h | \finv(\com{n}, \com{acc}, N, h)\wedge(\res=f(N))}\) {\normalfont (defn. of \(\finv\))}
     else 
\(\spec{ h | (h=\com{n}\mapsto\com{n'}\join\com{acc}\mapsto{\com{a'}})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (by \Rule{Cond})}
          acc ::= a' * n';;
\(\spec{ h | (h=\com{n}\mapsto\com{n'}\join\com{acc}\mapsto{\com{a'}\times\com{n'}})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (by \Rule{Assign})}
          n   ::= n' - 1;;
\(\spec{ h | (h=\com{n}\mapsto\com{n'}-1\join\com{acc}\mapsto{\com{a'}\times\com{n'}})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (by \Rule{Assign})}
\(\spec{ h | (h=\com{n}\mapsto\com{n'}-1\join\com{acc}\mapsto{\com{a'}\times\com{n'}})\wedge(f(\com{n'}-1)\times{\com{a'}\times\com{n'}}=f(N))}\) {\normalfont (by defn. of \(f\))}
\(\spec{ h | \finv(\com{n}, \com{acc}, N, h)}\) {\normalfont (by defn. of \(f\))}
          loop(tt) 
\(\spec{\res, h | \finv(\com{n}, \com{acc}, N, h)\wedge(\res=f(N))}\) {\normalfont (by assumption and \Rule{Fix})}
  )(tt);
\(\spec{h | \finv(\com{n}, \com{acc}, N, h)}\wedge(\com{res}=f(N))\) {\normalfont (by \Rule{Bind})}
\(\spec{h | (h=\com{n}\mapsto{-}\join\com{acc}\mapsto{-})\wedge(\com{res}=f(N))}\) {\normalfont (by defn. of \(f\))}
 dealloc(n);;
\(\spec{h | (h=\com{acc}\mapsto{-}) \wedge (\com{res}=f(N))}\) {\normalfont (by \Rule{Dealloc})}
 dealloc(acc);;
\(\spec{h | (h=\hempty)\wedge \wedge (\com{res}=f(N))}\) {\normalfont (by \Rule{Dealloc})}
 ret res
\(\spec{\res, h | (h=\hempty)\wedge \wedge (\res=f(N))}\) {\normalfont (by \Rule{Ret})}
\end{alltt}
%

Probably, the most tricky parts of the proof, which indeed require a
human prover are (b) "decomposition" of the loop invariant $\finv$ at
the beginning of the loop, when it falls into the components,
constraining the values of $\com{n}$ and $\com{acc}$ in the heap and
(b) the "re-composition" of the same invariant immediately before the
recursive call of $\com{loop}$ in order to ensure its
precondition. The later is possible because of algebraic properties of
the factorial function $f$, namely the fact that if $n > 0$ then
$f(n)\times a = f(n-1) \times n \times a$, the insight we have used in
order to "re-distribute" the values between the two pointers,
$\com{n}$ and $\com{acc}$ so the invariant $\finv$ could be restored.

It should be clear by this moment that, even though the proof is
proportional to the size of the program, it has combined some
mathematical reasoning with a machinery of consistent rule
application, until the postcondition has been reached. This proof
process is very reminiscent to the proofs that we have seen so far in
Coq, when one gradually applies the lemmas, assumptions and performs
rewritings until the final goal is proved. This is why using Coq seems
like a good idea to mechanize the process of proofs in separation
logic, so one can be sure that there is nothing missed during the
reasoning process and the specification is indeed correct. Employing
Coq for this purpose is indeed our ultimate goal and the topic of this
chapter, but before we reach that point, let us make a short detour to
the world of pure functional programming and representations of
effects in it by means of _types_.

* Reperesenting effectful computations using monads

It has been a long-standing problem for the functional programming
community to reconcile the _pure_ functions, enjoying referential
transparency, with effectful computations (e.g., mutating references,
throwing exceptions, performing output or reading from input), until
Eugenio Moggi suggested to use the mechanism of _monads_ to separate
the results of pure computations from the possible effects they can
produce%~\cite{Moggi:IC91}% and Phlip Wadler popularized this idea
with a large number of examples%~\cite{Wadler:POPL92}%. There is a
countless number of tutorials written and available on the Web that
are targeted to help building the intuition about the "monad
magic". Althogh, grasping some essense of monadic computations is
desired for understanding how verification of the imperative programs
can be structured in Coq, providing the reader with yet another "monad
tutorial" is not the task of this course.  Luckily, in order to
proceed to the verification, which is the topic of this chapter, we
need only very basic intuition on what monads are and how are they
typically used.

** Programming with "passing-styles"

Before the notion has been brought to the world of programmed to be
soon main-streamed by Haskell, the programmers already required to
combine effects with a functional paradigm. At ths time, such programs
have been written in "passing styless". %\index{passing style}% 

For instance, if someone needed to have a mutable _state_ around in a
program, such state could be represented by an immutable record, which
then would be passed from one function to another as an extra
component. Every time the state was mutated (e.g., using a dedicated
[put] function), a _new_ record describing it (with a change adopted)
would be created and passed further instead of the aold version, which
would be no longer used. Every time one woulod need to read from the
state, it could be done via a dedicated [get] function, which would
then return the value of the state, which is always present. Such
programming style, which would allow one tor _emulate_ state with
immutable records without the need to have mutable store and pointers,
just by passing an extra value around and modifying it consistently,
would be therefore referred to as a "state-passing style". 

As another example, one can imagine of emulating exceptions by means
of passing an extra argument to each function, which is checked at
each "step" of the execution. Such argument would carry information
about whether an exception has been thrown or not. And if it is thrown
(so the argument is an exception value), the rest of the computation
would be discarded and exception would be returned. Alternatively, the
evaluation should proceed in a normal order. Such programming model
can be, therefore, referred to as an "exception-passing style",
stressing the pattern of constant passing of the exception pattern and
checking it at each step of the program execution.

It is not difficult to com up with more examples of passing style that
would refere some programming concepts that have to do with
computation in the presence of an "additional effect". For instance,
continuation-passing style (CPS) assumes the presence of a
%\index{continuation-passing style}%
%\index{CPS|see{continuation-passing style}}% continuation value
available, which is just an extra function, which can be inworke at an
arbitrary moment, therefore interruption current execution
flow. Input/output can be represented by passing around a "handler",
to which the program can write and from which it can read via
dedicated functions.

Monads have been introduced to the world of programming as a way to
unify the diversity of the "passing style" paradigm has been,
essentially providing a solution of solving two problems:

- providing a uniform interface to for the passing-style, eliminating
  the need to implement the different machinery of "passing" the
  "effectful" entity from one computation to the "next" one in each
  particular case, as well as the need to instantiate the "effect"
  with a default value;

- implementing a programming language mechanism to statically
  determine, which particular "effect" (or effects) is being passed
  around in a particular program and resolve the calls to the
  effect-specific functions (such as, for example, [put] and [get] in
  the case of state-passing style).

** Examples of monads

Immediately after their introduction by Moggi and Wadler, monads were
adopted by Haskell, and currently many dosens of them exist,
facilitating programming with all kinds of effects and removing the
need for programming in passing style. The common interface, provided
by monads is implemented as a Haskell, which, slightly simplified,
looks as follows.

%
\begin{alltt}
class Monad m where
    (>>=)            :: m a -> (a -> m b) -> m b
    return           :: a -> m a
\end{alltt}
%

The signature specifies that each instance of <<Monad m>> is
parametrized by one type and requires two functions to be implemented.
The %\texttt{>>=}% function is pronounced as _bind_ and describes how
particular monad instance combines two computations, such that the
second one, whose type is <<m b>>, may depend on the value of result
of the first one, whose type is <<m a>>. The result of overall
computation is then the one of the second component, namely, <<m
b>>. The function <<return>> specifies how to provide a "default"
value for an effectful computation, i.e., how to "pair" a value of
type <<a>> with an "effect" entity in order to receive an element of
%\texttt{m a}%. 

Implementing monads for basic passing-styles is not particularly
difficult. For instance, the "state-passing style" corresponds to a
_state monad_, which pairs the result of the computation with a
current state. This state can be, therefore, updated using the
function [put] and queried via the function [get]. Internally, such
monad's implementation is isomorphic to a space of functions of types
[s -> (a, s)], where [s] is a type of the current state, and [a] is a
type of the current value of the computation. 

Haskell provides convenient [do]-notation to write programs in a
%\index{do-notation}% monadic style (as an alternative for passing
style), such that the invocation of the bind function in the
expression of the form <<c1 >>= (\x -> c2)>> (such that <<x>> might
occur in <<c2>>) can be written as <<do x <- c1; c2>>. For instance,
using [do]-notation, in Haskell a computation <<fiddle>> with a state monad,
which first reads from <<a>>, then computes the value of <<f a>>, then
stores it back to the state and finally returns what was put, can be
written as follows:

TODO

*)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import pred pcm unionmap heap heaptac stmod stsep stlog stlogR.  



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**

* Basics of Hoare Type Theory
%\label{sec:htt-intro}%

** Encoding program specifications as types

TODO: repeat the factorial example

** The Hoare monad

** Verifying the factorial in HTT

*)

Fixpoint fact_pure n := if n is n'.+1 then n * (fact_pure n') else 1.

Definition fact_inv (n acc : ptr) (N : nat) h : Prop := 
  exists n' a': nat, 
  [/\ h = n :-> n' \+ acc :-> a' & 
      (fact_pure n') * a' = fact_pure N].

Definition fact_tp n acc := 
  unit -> {N}, 
     STsep (fact_inv n acc N, 
           [vfun (res : nat) h => fact_inv n acc N h /\ res = fact_pure N]).

Program Definition fact_acc (n acc : ptr): fact_tp n acc := 
  Fix (fun (loop : fact_tp n acc) (_ : unit) => 
    Do (a1 <-- !acc;
        n' <-- !n;
        if n' == 0 then ret a1
        else acc ::= a1 * n';;
             n ::= n' - 1;;
             loop tt)).

Next Obligation. 
(* Q: what ghR does precisely? 
   A: It pulls out all the logical variables to the top level
*)
apply: ghR=>i N. 
case=>n' [a'][->{i}] Hi V. 
heval. (* TODO: Some automation - explain *)
case X: (n' == 0)=>//.
(* TODO: explain search for tactics *)
- apply: val_ret=>/= _; move/eqP: X=>Z; subst n'.
  split; first by exists 0, a'=>//.
  by rewrite mul1n in Hi.
heval. 
apply: (gh_ex N); apply: val_doR=>// V1.
- exists (n'-1), (a' * n'); split=>//=. 
rewrite -Hi=>{Hi V1 V}; rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
case: n' X=>//= n' _.
by rewrite subn1 -pred_Sn. 
Qed.

Program Definition fact (N : nat) : 
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fact_pure N /\ h = Unit]) := 
  Do (
    n   <-- alloc N;
    acc <-- alloc 1;
    res <-- fact_acc n acc tt;
    dealloc n;;
    dealloc acc;;
    ret res).

Next Obligation.
rewrite /conseq.
move=>h /= Z; subst h.
heval=>n; heval=>acc; rewrite joinC unitR.
(* 

Intuition behind bnd_seq: decomposing sequential composition with a
user-defined function.

 *)
apply: bnd_seq; apply: (gh_ex N).
(* 
Replace the call by its spec (substitution principle)
val_doR preserves the heap.
*)
apply: val_doR=>//; first by exists N, 1; rewrite muln1.
by move=>_ _ [[n'][a'][->] _ ->] _; heval.
Qed.


Fixpoint fib_pure n := 
  if n is n'.+1 then
    if n' is n''.+1 then fib_pure n' + fib_pure n'' else 1
  else 0.

Definition fib_inv (n x y : ptr) (N : nat) h : Prop := 
  exists n' x' y': nat, 
  [/\ h = n :-> n'.+1 \+ x :-> x' \+ y :-> y',
      x' = fib_pure n' & y' = fib_pure (n'.+1)].

Definition fib_tp n x y N := 
  unit ->
     STsep (fib_inv n x y N, 
           [vfun (res : nat) h => fib_inv n x y N h /\ res = fib_pure N]).

(*
Program Definition fib_acc (n x y : ptr) N: fib_tp n x y N := 
  Fix (fun (loop : fib_tp n x y N) (_ : unit) => 
    Do (n' <-- !n;
        y' <-- !y;
        if n' == N then ret y'
        else tmp <-- !x;
             x ::= y';;
             x' <-- !x;
             y ::= x' + tmp;;
             n ::= n' + 1;;
             loop tt)).

Next Obligation.
move=>h /=[n'][_][_][->{h}]->->.
heval; case X: (n'.+1 == N)=>//.
- by apply: val_ret=>_; move/eqP: X=><-/=.
heval; apply: val_doR=>//. (* This line takes a while due to automation. *)
move=>_.
exists (n'.+1), (fib_pure (n'.+1)), (fib_pure n'.+1.+1).
by rewrite addn1.
Qed.

Program Definition fib N : 
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fib_pure N /\ h = Unit]) := 
  Do (
   if N == 0 then ret 0
   else if N == 1 then ret 1
   else n   <-- alloc 2;
        x <-- alloc 1;
        y <-- alloc 1;
        res <-- fib_acc n x y N tt;
        dealloc n;;
        dealloc x;;
        dealloc y;;
       ret res    
).
Next Obligation.
move=>_ /= ->.
case N1: (N == 0)=>//; first by move/eqP: N1=>->; apply:val_ret. 
case N2: (N == 1)=>//; first by move/eqP: N2=>->; apply:val_ret. 
heval=>n; heval=>x; heval=>y; rewrite unitR joinC [x:->_ \+ _]joinC.
apply: bnd_seq=>/=.
apply: val_doR; last first=>//[res h|].
- case; case=>n'[_][_][->{h}]->->->_.
  by heval; rewrite !unitR.
by exists 1, 1, 1.
Qed.
*)

(**

* Specifying and verifying single-linked lists

* Further reading 

*)

(* begin hide *)
End HTT.
(* end hide *)