(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing is %\texttt{\emph{is}}% *)
(** printing first %\texttt{{first}}% *)
(** printing last %\texttt{\emph{last}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)
(** printing >-> %\texttt{>->}% *)
(** printing LoadPath %\texttt{\emph{LoadPath}}% *)
(** printing exists %\texttt{{exists}}% *)
(** printing :-> %\texttt{:->}% *)
(** printing <-- $\mathtt{<--}$ *)
(** printing vfun %\texttt{\emph{vfun}}% *)
(** printing do %\texttt{{do}}% *)
(** printing putStrLn %\texttt{\emph{putStrLn}}% *)
(** printing getChar %\texttt{\emph{getChar}}% *)
(** printing heval %\textsf{\emph{heval}}% *)
(** printing write %\textsf{\emph{write}}% *)
(** printing From %\textsf{{From}}% *)


(** %
\chapter{Case Study: Program Verification in Hoare Type Theory}
\label{ch:htt}
% *)

(**

In this chapter, we will consider a fairly large case study that makes
use of most of Coq's features as a programming language with dependent
types and as a framework to build proofs and reason about mathematical
theories.

%\index{declarative programming}\index{imperative programming}%

Programming language practitioners usually elaborate on the dichotomy
between _declarative_ and _imperative_ languages, emphasizing the fact
that a program written in a declarative language is pretty much
documenting itself, as it already specifies the _result_ of a
computation. Therefore, logic and constraint programming languages
(such as Prolog%~\cite{Lloyd:87}% %\index{Prolog}% or
Ciao%~\cite{Hermenegildo-al:TPLP12}\index{Ciao}%) as well as data
definition/manipulation languages (e.g., SQL), whose programs are just
sets of constraints/logical clauses or queries describing the desired
result, are naturally considered to be declarative. Very often, pure
functional programming languages (e.g., Haskell) are considered as
declarative as well. The reason for this is the _referential
transparency_ property, which ensures that programs in such languages
%\index{referential transparency}% are in fact effect-free
expressions, evaluating to some result (similar to mathematical
functions) or diverging. Therefore, such programs, whose outcome is
only a value, but not some side effect (e.g., output to a file), can
be replaced safely by their result, if it is computable. This
possibility provides a convenient way of reasoning algebraically about
such programs by means of equality rewritings---precisely what we were
observing and leveraging in %Chapters~\ref{ch:eqrew}
and~\ref{ch:ssrstyle}% of this course in the context of Coq taken as a
functional programming language.

%\index{specification|see {program specification}}%

That said, pure functional programs tend to be considered to be good
specifications for themselves. Of course, the term "specification" (or
simply, "spec") %\index{program specification}% is overloaded and in
some context it might mean the result of the program, its effect or
some of the program's algebraic properties. While a functional program
is already a good description of its result (due to referential
transparency), its algebraic properties (e.g., some equalities that
hold over it) are usually a subject of separate statements, which
should be proved%~\cite{Bird:BOOK}%. Good examples of such properties
are the commutativity and cancellation properties, which we proved for
natural numbers with addition, considered as an instance of PCM on
page%~\pageref{pg:addnprops} of Chapter~\ref{ch:depstruct}%. Another
classical series of examples, which we did not focus on in this course,
are properties of list functions, such as appending and reversal
(e.g., that the list reversal is an inverse to itself).%\footnote{A
common anti-pattern in dependently-typed languages and Coq in
particular is to encode such algebraic properties into the definitions
of the datatypes and functions themselves (a canonical example of such
approach are length-indexed lists). While this approach looks
appealing, as it demonstrates the power of dependent types to capture
certain properties of datatypes and functions on them, it is
inherently non-scalable, as there will be always another property of
interest, which has not been foreseen by a designer of the
datatype/function, so it will have to be encoded as an external fact
anyway. This is why we advocate the approach, in which datatypes and
functions are defined as close to the way they would be defined by a
programmer as possible, and all necessary properties of them are
proved separately.}%

The situation is different when it comes to imperative programs, whose
outcome is typically their side-effect and is achieved by means of
manipulating mutable state, throwing an exception or performing
input/output. While some of the modern programming languages (e.g.,
Scala, OCaml) allow one to mix imperative and declarative programming
styles, it is significantly harder to _reason_ about such programs, as
now they cannot be simply replaced by their results: one should also
take into account the effect of their execution (i.e., changes in the
mutable state). A very distinct approach to incorporating both
imperative and declarative programming is taken by Haskell, in which
effectful programs can always be distinguished from pure ones by means
of enforcing the former ones to have very specific
types%~\cite{PeytonJones-Wadler:POPL93}%---the idea we will elaborate
more on a bit further.

In the following sections of this chapter, we will learn how Coq can
be used to give specifications to imperative programs, written in a
domain-specific language, similar to C, but in fact being a subset of
Coq itself. Moreover, we will observe how the familiar proof
construction machinery can be used to establish the correctness of
these specifications, therefore, providing a way to _verify_ a program
by means of checking, whether it satisfies a given spec. In
particular, we will learn how the effects of state-manipulating
programs can be specified via dependent types, and the specifications
of separate effectful programs can be _composed_, therefore allowing
us to structure the reasoning in a modular way, similarly to
mathematics, where one needs to prove a theorem only once and then can
just rely on its statement, so it can be employed in the proofs of
other facts.

* Imperative programs and their specifications %\label{sec:imp-spec}%

The first attempts to specify the behaviour of state-manipulating
imperative programs with assignments originated in late '60s and are
due to Tony Hoare and Robert Floyd%~\cite{Hoare:CACM69,Floyd:67}%, who
considered programs in a simple imperative language with mutable
variables (but without pointers or procedures) and suggested to give a
specification to a program $c$ in the form of a triple
$\spec{P}~c~\spec{Q}$, where $P$ and $Q$ are logical propositions,
describing the values of the mutable variables and possible relations
between them. $P$ and $Q$ are usually %\index{assertions}% referred to
as _assertions_; more specifically, $P$ is called
%\index{precondition}\index{postcondition}% _precondition_ of $c$ (or
just "pre"), whereas $Q$ is called _postcondition_ (or simply
"post"). The triple $\spec{P}~c~\spec{Q}$ is traditionally referred to
as _Hoare triple_.%\index{Hoare triple}%%\footnote{The initial syntax
for the triples used by Hoare was $\specK{P}~\set{c}~\specK{Q}$. The
notation $\spec{P}~c~\spec{Q}$, which is used now consistently, is due
to Niklaus Wirth and emphasizes the comment-like nature of the
assertions in the syntax reminiscent to the one of Pascal.}% Its
intuitive semantics can be expressed as follows: %\label{pg:triple}%
"if right before the program $c$ is executed the state of mutable
variables is described by the proposition $P$, then, _if $c$
terminates_, the resulting state satisfies the proposition $Q$".

%\index{partial program correctness}% 
%\index{total program correctness}%

The reservation on termination of the program $c$ is important. In
fact, while the Hoare triples in their simple form make sense only for
terminating programs, it is possible to specify non-terminating
programs as well. This is due to the fact that the semantics of a
Hoare triple implies that a non-terminating program can be given _any_
postcondition, as one won't be able to check it anyway, because the
program will never reach the final state.%\footnote{This intuition is
consistent with the one, enforced by Coq's termination checker, which
allows only terminating programs to be written, since non-terminating
program can be given any type and therefore compromise the consistency
of the whole underlying logical framework of CIC.}% Such
interpretation of a Hoare triple "modulo termination" is referred to
as _partial correctness_, and in this chapter we will focus on it. It
is possible to give to a Hoare triple $\spec{P}~c~\spec{Q}$ a
different interpretation, which would deliver a stronger property: "if
right before the program $c$ is executed the state of mutable
variables is described by a proposition $P$, _then $c$ terminates_ and
the resulting state satisfies the proposition $Q$". Such property is
called _total correctness_ and requires tracking some sort of "fuel"
for the program in the assertions, so it could run further. We do not
consider total correctness in this course and instead refer the reader
to the relevant research results on Hoare-style specifications with
resource bounds%~\cite{Dockins-Hobor:DS10}%.

** Specifying and verifying programs in a Hoare logic
%\label{sec:hoare-primer}%

The original Hoare logic worked over a very simplistic imperative
language with loops, conditional operators and assignments. This is
how one can specify a program, which just assigns 3 to a specific
variable named%~\texttt{x}%: 

% \begin{alltt} \(\spec{\True}\) x := 3 \(\spec{x = 3}\) \end{alltt} %

That is, the program's precondition doesn't make any specific
assumptions, which is expressed by the proposition $\True$; the
postcondition ensures that the value of a mutable variable
%\texttt{x}% is equal to three.

The formalism, which allows us to validate particular Hoare triples
for specific programs is called _program logic_ (or, equivalently,
_Hoare logic_). 

%\index{program logic}%
%\index{program logic|see {Hoare logic}}%

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
a bar", rather than as constructors. Therefore, an inference rule for
conjunction introduction in the constructive logic looks as follows:

%\index{inference rules|seealso {Hoare/Separation Logic rules}}%

%
\begin{mathpar}
\inferrule*[Right={($\wedge$-{Intro})}]
 {A \\ B}
 {A \wedge B}
\end{mathpar}
%


That is, the rule %\Rule{$\wedge$-Intro}% is just a paraphrase of the
[conj] constructor, which specifies how an instance of conjunction can
be created. Similarly, the disjunction [or] has two inference rules,
for each of its constructors. The elimination rules are converses of
the introduction rules and formalize the intuition behind the case
analysis. An alternative example of an inference rule for a
proposition encoded by means of Coq's datatype constructor is the
definition of the predicate for beautiful numbers [beautiful] from
%Section~\ref{sec:cannot}%. There, the constructor [b_sum] serves as
an inference rule that, given the proofs that [n'] is beautiful and
[m'] is beautiful, constructs the proof of the fact that their sum is
beautiful.%\footnote{Actually, some courses on Coq introduce datatype
constructors exactly from this perspective---as a programming
counterpart of the introduction rules for particular kinds of logical
propositions~\cite{Pierce-al:SF}. We came to the same analogy by
starting from an opposite side and exploring the datatypes in the
programming perspective first.}%

Hoare logic also suggests a number of axioms and inference rules that
specify which Hoare triple can in fact be inferred. We postpone the
description of their encoding by means of Coq's datatypes till
%Section~\ref{sec:htt-intro}% of this chapter and so far demonstrate
some of them in the logical notation "with a bar". For example, the
Hoare triple for a variable assignment is formed by the following
rule:

%
\begin{mathpar}
\inferrule*[Right={(Assign)}]
 {}
 {\spec{Q[e/x]}~ x := e ~\spec{Q}}
\end{mathpar}
\spr{Assign}
%


The rule %\Rule{Assign}% is in fact an axiom (since it does not assume
anything, i.e., does not take any arguments), which states that if a
proposition $Q$ is valid after substituting all occurrences of $x$ in
it with $e$ (which is denoted by $[e/x]$), then it is a valid
postcondition for the assignment $x := e$.

The inference rule for sequential composition is actually a
constructor, which takes the proofs of Hoare triples for $c_1$ and
$c_2$ and then delivers a composed program $c_1; c_2$ _as well as_ the
proof for the corresponding Hoare triple, ensuring that the
postcondition of $c_1$ matches the precondition of $c_2$.
%\index{sequential composition}%

%
\begin{mathpar}
\inferrule*[Right={(Seq)}]
 {\spec{P}~ c_1~\spec{R}\\
  \spec{R}~ c_2 ~\spec{Q}}
 {\spec{P}~ c_1; c_2 ~\spec{Q}}
\end{mathpar}
\spr{Seq}
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
\spr{Conseq}
\begin{mathpar}
\inferrule*[Right={(Conseq)}]
 {P \implies P' \\
  \spec{P'}~ c~ \spec{Q'}\\
  Q' \implies Q}
 {\spec{P}~ c~\spec{Q}}
\end{mathpar}
%

With this respect, we can make the analogy between Hoare triples and
function types of the form [A -> B], such that the rule of consequence
of a Hoare triple corresponds to subtyping of function types, where
the precondition [P] is analogous to an argument type [A] and the
postcondition [Q] is analogous to a result type [B]. Similarly to the
functions with subtyping, Hoare triples are covariant with respect to
consequence in their postcondition and _contravariant_ in the
precondition%~\cite[Chapter 15]{Pierce:BOOK02}%.
%\index{covariance}\index{contravariance}% This is the reason why,
when establishing a specification, one should strive to infer the
_weakest precondition and the strongest postcondition_ to get the
tightest possible (i.e., the most precise) spec, which can be later
weakened using the %\Rule{Conseq}% rule.

The observed similarity between functions and commands in a Hoare
logic should serve as an indicator that, perhaps, it would be a good
idea to implement the Hoare logic in a form of a type system. Getting
a bit ahead of ourselves, this is exactly what is going to happen soon
in this chapter (as the title of the chapter suggests).

At this point, we can already see a simple paper-and-pencil proof of a
program that manipulates mutable variables. In the Hoare logic
tradition, since most of the programs are typically compositions of
small programs, the proofs of specifications are written to follow the
structure of the program, so the first assertion corresponds to the
overall precondition, the last one is the overall postcondition, and
the intermediate assertions correspond to $R$ from the rule
%\Rule{Seq}% modulo weakening via the rule of consequence
%\Rule{Conseq}%. Let us prove the following Hoare-style specification
for a program that swaps the values of two variables $x$ and $y$.

%
\begin{alltt}
\(\spec{x = a \wedge y = b}\) t := \var{x}; \var{x} := \var{y}; \var{y} := t \(\spec{x = b \wedge y = a}\)
\end{alltt}
%

The variables [a] and [b] are called _logical_ and are used in order
to name %\index{logical variables}% unspecified values, which are a
subject of manipulation in the program, and their identity should be
preserved. The logical variables are implicitly universally quantified
over in the scope of the _whole_ Hoare triple they appear, but usually
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

The list of program constructs and inference rules for them would be incomplete without conditional operators and loops.

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
\spr{Cond}\spr{While}
%

The inference rule for a conditional statement should be intuitively
clear and reminds of a typing rule for conditional expressions in
Haskell or OCaml, which requires both branches of the statement to
have the same type (and here, equivalently, to satisfy the same
postcondition). The rule %\Rule{While}% for the loops is more
interesting, as it makes use of the %\index{loop invariant}%
proposition $I$, which is called _loop invariant_. Whenever the body
of the cycle is entered, the invariant should hold (as well as the
condition $e$, since the iteration has just started). Upon finishing,
the body $c$ should restore the invariant, so the next iteration would
start in a consistent state again. Generally, it takes a human
prover's intuition to come up with a non-trivial resource invariant
for a loop, so it can be used in the rest of the program. Inference of
the best loop invariant is an undecidable problem in general and it
has a deep relation to type inference with polymorphically-recursive
functions%~\cite{Henglein:TOPLAS93}%. This should not be very
surprising, since every loop can be encoded as a recursive function,
and, since, as we have already started guessing, Hoare triples are
reminiscent of types, automatic inferring of loop invariants would
correspond to type inference for recursive functions. In the
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
semantics%~\cite[Chapter~2]{Winskel:BOOK}%. Rather, Hoare logic allows
one to make statements about the effect the program takes to the
mutable state, and, what is more important, construct finite proofs of
these statements. With this respect, Hoare logic serves the same
purpose as type systems in many programming languages---determine
statically (i.e., without _executing_ the program), whether the
program is well-behaved or not. In other words, it serves as an
"approximation" of another, more low-level semantics of a program.
This intuition is also implied by the very definition of a hoare
triple on page%~\pageref{pg:triple}%, which relies to the fact that a
program can be executed.

That said, in order to use a Hoare logic for specifying and verifying
a program's behaviour, a _soundness_ result should be first
%\index{soundness of a logic}% established. In the case of a program
logic, soundness means the logic rules allow one to infer only those
statements that do not contradict the definition of a Hoare triple
(page%~\pageref{pg:triple}%). This result can be proven in many
different ways, and the nature of the proof usually depends on the
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
code. But its most severe shortcoming becomes evident when it
comes to specifying programs that manipulate _pointers_, i.e.,
the most interesting imperative cases of imperative
code. %\index{pointers}% In the presence of pointers and a heap,
mutable variables become somewhat redundant, so for now by _local
variables_ we will be assuming immutable, once-assigned variables,
akin to those bound by the %\texttt{let}%-expression. Such variables
can, of course, have pointers as their values.
Let us first enrich the imperative programming language of interest to
account for the presence of heap and pointers. We will be using the
syntax %\texttt{x ::= e}% to denote the assignment of a value
%\texttt{e}% to the pointer bound by %\texttt{x}%. Similarly, the
syntax %\texttt{!e}% stands for dereferencing a pointer, whose address
is a value obtained by evaluating a _pure_ expression %\texttt{e}%. We
will assume that every program returns a value as a result (and the
result of a pointer assignment is of type [unit]). To account for
this, we will be using the syntax %\texttt{x~<-~c1;~c2}% (pronounced
"bind") as a generalization of the sequential composition from
%Section~\ref{sec:hoare-primer}%. The bind first executes the program
%\texttt{c1}%, then _binds_ this %\index{binding}% result to an
immutable variable %\texttt{x}% and proceeds to the execution of the
program %\texttt{c2}%, which can possibly make use of the variable
%\texttt{x}%, so all the occurrences of %\texttt{x}% in it are
replaced by its value before it starts evaluating. If the result of
%\texttt{c1}% is not used by %\texttt{c2}%, we will use the
abbreviation %\texttt{c1~;;~c2}% to denote this specific case.
Specifications in the simple Hoare logic demonstrated in
%Section~\ref{sec:hoare-primer}% are stated over mutable local
variables, which are implicitly supposed to be all distinct, as they
have distinct "abstract" names. In a language with a heap and
pointers, the state is no longer a set of mutable variables, but the
heap itself, which %\index{heap}% can be thought of as a partial map
from natural numbers to arbitrary values. In a program, operating with
a heap, two pointer variables, $x$ and $y$ can in fact be _aliases_,
%\index{aliasing}% i.e., refer to the same memory entry, and,
therefore, changing a value of a pointer, referenced by $x$ will
affect the value, pointed to by $y$. Aliasing is an aspect that
renders reasoning in the standard Hoare logic tedious and
unbearable. To illustrate the problem, let us consider the following
program, which runs in the assumption that the heap, which is being
available to the program, has only two entries with addresses,
referred to by local variables $x$ and $y$ correspondingly, so the
specification states it by means of the "points-to" assertions $x
\mapsto -$, where $x$ is assumed to be a pointer value.
%\index{points-to assertions}%
%
\begin{alltt}
\(\spec{x\mapsto{-}\wedge{y}\mapsto{Y}}\) \var{x} ::= 5 \(\spec{x\mapsto{5}\wedge{y}\mapsto{Y}}\)
\end{alltt}
%
The logical variable $Y$ is of importance, as it is used to state that
the value of the pointer $y$ remains unchanged after the program has
terminated.%\footnote{We will abuse the terminology and refer to the
values and immutable local variables uniformly, as, unlike the setting
of Section~\ref{sec:imp-spec}, the latter ones are assumed to be
substituted by the former ones during the evaluation anyway.}% Alas,
this specification is not correct, as the conjunction of the two does
not distinguish between the case when $x$ and $y$ are the same pointer
and when they are not, which is precisely the aliasing problem. It is
not difficult to fix the specification for this particular example by
adding a conditional statement (or, equivalently, a disjunction) into
the postcondition that would describe two different outcomes of the
execution with respect to the value of $y$, depending on the fact
whether $x$ and $y$ are aliases or not. However, if a program
manipulates with a large number of pointers, or, even worse, with an
array (which is obviously just a sequential batch of pointers), things
will soon go wild, and the conditionals with respect to equality or
non-equality of certain pointers will pollute all the specifications,
rendering them unreadable and eventually useless. This was precisely
the reason, why after being discovered in late '60s and investigated
for a decade, Hoare-style logics were soon almost dismissed as a
specification and verification method, due to the immense complexity
of the reasoning process and overwhelming proof obligations.
%\index{Separation Logic|textbf}% 
The situation has changed when in 2002 John C. Reynolds, Peter
O'Hearn, Samin Ishtiaq and Hongseok Yang suggested an alternative way
to state Hoare-style assertions about heap-manipulating programs with
pointers%~\cite{Reynolds:LICS02}%. The key idea was to make _explicit_
the fact of disjointness (or, _separation_) between different parts of
a heap in the pre- and postconditions. This insight made it possible
to reason about disjointness of heaps and absence of aliasing without
the need to emit side conditions about equality of pointers. The
resulting formal system received the name _separation logic_, and
below we consider a number of examples to specify and verify programs
in it.
For instance, the program, shown above, which assigns $5$ to a pointer
$x$ can now be given the following specification in the separation
logic:
%
\label{pg:alterx}
\begin{alltt}
\(\spec{h | h = x \mapsto - \join y \mapsto Y}\) \var{x} ::= 5 \(\spec{\res, h | h = x \mapsto 5 \join y \mapsto Y}\)
\end{alltt}
%
We emphasize the fact that the heaps, being just partial maps from
natural numbers to arbitrary values, are elements of a PCM
%(Section~\ref{sec:pcms})% with the operation $\join$ taken to be a
disjoint union and the unit element to be an empty heap (denoted
$\hempty$). %\index{PCM}% The above assertions therefore ensure that,
before the program starts, it operates in a heap $h$, such that $h$ is
a partial map, consisting of two _different_ pointers, $x$ and $y$,
such that $y$ points to some universally-quantified value $Y$, and the
content of $x$ is of no importance (which is denoted by [-]). The
postcondition makes it explicit that only the value of the pointer $x$
has changed, and the value of $y$ remained the same. The
postcondition also mentions the result $\res$ of the whole operations,
which is, however, not constrained anyhow, since, as it has been
stated, it is just a value of type [unit].%\footnote{The classical
formulation of Separation Logic~\cite{Reynolds:LICS02} introduces the
logical connective $\sep$, dubbed \emph{separating conjunction},
\index{separating conjunction} which allows to describe the split of a
heap $h$ into two disjoint parts without mentioning $h$
explicitly. That is, the assertion $P~\sep~Q$ holds for a heap $h$, if
there exist heaps $h_1$ and $h_2$, such that $h = h_1 \join h_2$, $P$
is satisfied by $h_1$ and $Q$ is satisfied by $h_2$. We will stick to
the ``explicit'' notation, though, as it allows for greater
flexibility when stating the assertions, mixing both heaps and
values.}%
** Selected rules of Separation Logic
%\label{sec:seplog-rules}%
Let us now revise some of the rules of Hoare logic and see how they
will look in separation logic. The rules, stated over the heap, are
typically given in the _small footprint_, %\index{small footprint}%
meaning that they are stated with the smallest possible heap and assume
that the "rest" of the heap, which is unaffected by the program
specified, can be safely assumed. The rules for assigning and reading
the pointers are natural.
%
\spr{Write}\spr{Read}
\begin{mathpar}
\inferrule*[Right={(Write)}]
 {}
 {\spec{h ~|~ h = x \mapsto -}~ x ::= e ~\spec{\res, h ~|~ h = x \mapsto e \wedge \res = \com{tt}}}
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
\spr{Alloc}\spr{Dealloc}
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
$\com{dealloc}()$ are given in a _large footprint_ that, in contrast
with %\index{large footprint}% small footprint-like specifications,
mentions the "additional" heap $h'$ in the pre- and post-conditions,
which can be arbitrarily instantiated, emphasizing that it remains
unchanged (recall that $h'$ is implicitly universally-quantified over,
and its scope is the whole triple), so the resulting heap is just being
"increased"/"decreased" by a memory entry that has been
allocated/deallocated.%\footnote{The classical separation logic
provides a so-called \emph{frame rule},\index{frame rule} which allows
for the switch between the two flavours of footprint by
attaching/removing the additional heap $h'$. In our reasoning we will
be assuming it implicitly.}%
The rule for binding is similar to the rule for sequential composition
of programs $c_1$ and $c_2$ from the standard Hoare logic, although it
specifies that the immutable variables can be substituted in $c_2$.
%
\spr{Bind}
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
%\Rule{Conseq}% is similar to the one from Hoare logic modulo the
technical details on how to weaken heap/result parametrized functions,
so we omit it here as an intuitive one. The rule for conditional
operator is the same one as in %Section~\ref{sec:hoare-primer}%, and,
hence, is omitted as well.
In order to support procedures in separation logic, we need to
consider two additional rules---for function invocation and returning
a value.
%
\begin{mathpar}
\spr{Return}\spr{Hyp}\spr{App}
\inferrule*[Right={(Return)}]
 {} 
 {\spec{h ~|~ P(h)}~ \ret~e ~\spec{\res, h ~|~ P(h) \wedge \res = e}}
\and
\inferrule*[Right={(Hyp)}]
 {\forall x, \spec{h ~|~ P(x, h)}~f(x)~\spec{\res, h ~|~ Q(x, \res, h)} \in \Gamma}
 {\Gamma \vdash \forall x, \spec{h ~|~ P(x, h)}~f(x)~\spec{\res, h ~|~ Q(x, \res, h)}}
\and
\inferrule*[Right={(App)}]
 {\Gamma \vdash \forall x, \spec{h ~|~ P(x, h)}~f(x)~\spec{\res, h ~|~ Q(x, \res, h)}}
 {\Gamma \vdash \spec{h ~|~ P(e, h) }~f(e)~\spec{\res, h ~|~ Q(e, \res, h)}}
\end{mathpar}
%
%\index{assumption context}\index{typing context}%
The rule for returning simply constraints the dedicated variable
$\res$ to be equal to the expression $e$. The rule %\Rule{Hyp}% (for
"hypothesis") introduces the assumption context $\Gamma$ that contains
specifications of available "library" functions (bearing the
reminiscence with the typing context in typing
relations%~\cite[Chapter~9]{Pierce:BOOK02}%) and until now was assumed
to be empty. Notice that, similarly to dependently-typed functions, in
the rule %\Rule{Hyp}% the pre- and postcondition in the spec of the
assumed function can depend on the value of its argument $x$. The rule
%\Rule{App}% accounts for the function application and instantiates
all occurrences of $x$ with the argument expression $e$.
Finally, sometimes we might be able to infer two different
specifications about the same program. In this case we should be able
to combine them into one, which is stronger, and this is what the
rule of conjunction %\Rule{Conj}% serves for:
%
\spr{Conj}
\begin{mathpar}
\inferrule*[Right={(Conj)}]
 {\spec{h ~|~ P(h) }~c~\spec{\res, h ~|~ Q_1(\res, h)} \\
 \spec{h ~|~ P(h) }~c~\spec{\res, h ~|~ Q_2(\res, h)}}
 {\spec{h ~|~ P(h)}~ c~\spec{\res, h ~|~ Q_1(\res, h) \wedge Q_2(\res, h)}}
\end{mathpar}
%
** Representing loops as recursive functions
%\label{sec:loops}%
It is well-known in a programming language folklore that every
imperative loop can be rewritten as a function, which is
tail-recursive, i.e., it performs the call of itself only as the very
last statement in some possible execution branches and doesn't call
itself at all in all other branches. Therefore, recursive functions in
general %\index{tail recursion}% are a more expressive mechanism, as
they also allow one to write non-tail recursive programs, in which
recursive calls occur in any position.%\footnote{Although, such
programs can be made tail-recursive via the continuation-passing style
transformation (CPS)~\cite{Danvy:CPS}. They can be also converted into
imperative loops via the subsequent transformation, known as
\emph{defunctionalization}~\cite{Reynolds:ACM72}.}% Therefore, an
imperative program of the form
%
\begin{center}
\texttt{while (e) do c}
\end{center}
% 
%\noindent% can be rewritten using a recursive function, defined via
the in-place fixpoint operator as
%
\begin{center}
\texttt{(fix~f (x~:~bool).~if~x~then~c;;~f(e')~else~ret~tt)(e)}
\end{center}
% 
That is, the function %\texttt{f}% is defined with an argument of the
bool type and is immediately invoked. If the condition argument
$\com{x}$ is satisfied, the body $\com{c}$ is executed and the
function calls itself recursively with a new argument $\com{e'}$;
otherwise the function just returns a unit result. For the first time,
the function is invoked with some initial argument $\com{e}$.
Given this relation between imperative loops and effectful recursive
functions, we won't be providing a rule for loops in separation logic
at all, and rather provide one for recursive definitions.
%
\spr{Fix}
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
recursive functions in some programming languages (e.g.,
Scala%~\cite[\S~4.1]{Scala-spec}%) require explicit type annotations
to be type-checked.
In the remainder of this chapter we will be always implementing
imperative loops via effectful recursive functions, whose
specifications are stated explicitly, so the rule above would be
directly applicable.
** Verifying heap-manipulating programs
%\label{sec:fact-logic}%
Let us now see how a simple imperative program with conditionals and
recursion would be verified in a version of separation logic that we
presented here. A subject of our experiment will be an efficient
imperative implementation of a factorial-computing function, which
_accumulates_ the factorial value in a specific variable, while
decreasing its argument in a loop, and returns the value of the
accumulator when the iteration variable becomes zero. In the
pseudocode, the %\texttt{fact}% program is implemented as follows:
%
\label{ref:facto}
\begin{alltt}
fun fact (\var{N} : nat): nat = \{
  n   <-- alloc(\var{N});
  acc <-- alloc(1); 
  res <-- 
    (fix loop (_ : unit). 
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
\}
\end{alltt}
%
The function %\texttt{fact}% first allocates two pointers,
%\texttt{n}% and %\texttt{acc}% for the iteration variable and the
accumulator, correspondingly. It will then initiate the loop,
implemented by the recursive function %\texttt{loop}%, that reads the
values of %\texttt{n}% and %\texttt{acc}% into local immutable
variables %\texttt{n'}% and %\texttt{a'}%, correspondingly and then
checks whether %\texttt{n'}% is zero, in which case it returns the
value of the accumulator. Otherwise it stores into the accumulator the
old value multiplied by %\texttt{n'}%, decrements %\texttt{n}% and
re-iterates. After the loop terminates, the two pointers are
deallocated and the main function returns the result.
Our goal for the rest of this section will be to verify this program
semi-formally, using the rules for separation logic presented above,
against its _functional_ specification. In other words, we will have
to check that the program %\texttt{fact}% returns precisely the
factorial of its argument value $N$. To give such specification to
%\texttt{fact}%, we define two auxiliary mathematical functions, $f$
and $\finv$:
%
\[
\begin{array}{rcl}
f(N) & \eqdef & \textsf{if}~N = N'+1~\textsf{then}~N \times f(N')~\textsf{else}~1 
\\[5pt]
\finv(n, acc, N, h) & \eqdef &  \exists n', a', (h = n \mapsto n' \join acc \mapsto a') \wedge (f(n') \times a' = f(N))
\end{array}
\]
%
It is not difficult to see that $f$ defines exactly the factorial
function as one would define it in a pure functional language (not
very efficiently, though, but in the most declarative form). The
second function $\finv$ is in fact a predicate, which we will use to
give the loop invariant to the loop function %\texttt{loop}%. Now, the
function %\texttt{fact}% can be given the following specification in
separation logic, stating that it does not _leak_ memory and its
result is the factorial of its argument $N$.
%
\[
\spec{h ~|~ h = \hempty} ~\com{fact}(N)~ \spec{\res, h ~|~ h = \hempty \wedge \res = f(N)}
\]
%
In the course of the proof of the above stated spec of $\com{fact}$,
in order to apply the rule %\Rule{Fix}%, we pose the specification of
$\com{loop}$ (in an implicit assumption context $\Gamma$ from the
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
 n   <-- alloc(\var{N});
\(\spec{h | h = \com{n} \mapsto N}\) {\normalfont ({by \Rule{Alloc} and PCM properties})}
 acc <-- alloc(1); 
\(\spec{h | h = \com{n} \mapsto N \join \com{acc} \mapsto 1}\) {\normalfont ({by \Rule{Alloc}})}
\(\spec{h | \finv(\com{n}, \com{acc}, N, h)}\) {\normalfont ({by definition of \(\finv\) and \Rule{Conseq}})}
 res <-- 
  (fix loop (_ : unit). 
\(\spec{h | \finv(\com{n}, \com{acc}, N, h)}\) {\normalfont (precondition)}
     a' <-- !acc;
\(\spec{h | \exists{n'}, (h=\com{n}\mapsto{n'}\join\com{acc}\mapsto\com{a'})\wedge(f(n')\times{a'}=f(N))}\) {\normalfont (\(\finv\), \Rule{Read} and \Rule{Conj})}
     n' <-- !n;
\(\spec{h | (h=\com{n}\mapsto{\com{n'}}\join\com{acc}\mapsto\com{a'})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (\Rule{Read} and \Rule{Conj})}
     if n' == 0 then ret a'
\(\spec{\res, h | (h=\com{n}\mapsto{0}\join\com{acc}\mapsto{f(N)})\wedge(\res=f(N))}\) {\normalfont (defn. \(f\), (=) and \Rule{Return})}
\(\spec{\res, h | \finv(\com{n}, \com{acc}, N, h)\wedge(\res=f(N))}\) {\normalfont (defn. of \(\finv\))}
     else 
\(\spec{h | (h=\com{n}\mapsto\com{n'}\join\com{acc}\mapsto{\com{a'}})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (by \Rule{Cond})}
          acc ::= a' * n';;
\(\spec{h | (h=\com{n}\mapsto\com{n'}\join\com{acc}\mapsto{\com{a'}\times\com{n'}})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (by \Rule{Write})}
          n   ::= n' - 1;;
\(\spec{h | (h=\com{n}\mapsto\com{n'}-1\join\com{acc}\mapsto{\com{a'}\times\com{n'}})\wedge(f(\com{n'})\times{\com{a'}}=f(N))}\) {\normalfont (by \Rule{Write})}
\(\spec{h | (h=\com{n}\mapsto\com{n'}-1\join\com{acc}\mapsto{\com{a'}\times\com{n'}})\wedge(f(\com{n'}-1)\times{\com{a'}\times\com{n'}}=f(N))}\) {\normalfont (by defn. of \(f\))}
\(\spec{h | \finv(\com{n}, \com{acc}, N, h)}\) {\normalfont (by defn. of \(f\))}
          loop(tt) 
\(\spec{\res, h | \finv(\com{n}, \com{acc}, N, h)\wedge(\res=f(N))}\) {\normalfont (by assumption and \Rule{Fix})}
  )(tt);
\(\spec{h | \finv(\com{n}, \com{acc}, N, h) \wedge (\com{res}=f(N))}\) {\normalfont (by \Rule{Bind})}
\(\spec{h | (h=\com{n}\mapsto{-}\join\com{acc}\mapsto{-})\wedge(\com{res}=f(N))}\) {\normalfont (by defn. of \(f\))}
 dealloc(n);;
\(\spec{h | (h=\com{acc}\mapsto{-}) \wedge (\com{res}=f(N))}\) {\normalfont (by \Rule{Dealloc})}
 dealloc(acc);;
\(\spec{h | (h=\hempty)\wedge(\com{res}=f(N))}\) {\normalfont (by \Rule{Dealloc})}
 ret res
\(\spec{\res, h | (h=\hempty)\wedge(\res=f(N))}\) {\normalfont (by \Rule{Ret})}
\end{alltt}
%
Probably, the most tricky parts of the proof, which indeed require a
human prover's insight, are (a) "decomposition" of the loop invariant
$\finv$ at the beginning of the loop, when it falls into the
components, constraining the values of $\com{n}$ and $\com{acc}$ in
the heap and (b) the "re-composition" of the same invariant
immediately before the recursive call of $\com{loop}$ in order to
ensure its precondition. The latter is possible because of algebraic
properties of the factorial function $f$, namely the fact that for any
$n$, if $n > 0$ then $f(n)\times a = f(n-1) \times n \times a$, the
insight we have used in order to "re-distribute" the values between
the two pointers, $\com{n}$ and $\com{acc}$ so the invariant $\finv$
could be restored.
It should be clear by this moment, that, even though the proof is
proportional to the size of the program, it has combined some
mathematical reasoning with a machinery of consistent rule
application, until the postcondition has been reached, which, when
done by a human solely, might be an error-prone
procedure. Nevertheless, this proof process is very reminiscent to the
proofs that we have seen so far in Coq, when one gradually applies the
lemmas, assumptions and performs rewritings until the final goal is
proved. This is why using Coq seems like a good idea to mechanize the
process of proofs in separation logic, so one can be sure that there
is nothing missed during the reasoning process and the specification
is certainly correct. Employing Coq for this purpose is indeed our
ultimate goal and the topic of this chapter. However, before we reach
that point, let us recall that in a nutshell Coq is in fact a
_functional_ programming language and make yet another short detour to
the world of pure functional programming, to see how effects might be
specified by means of _types_.
* Specifying effectful computations using types
%\index{computational effects}%
%\index{effects|see{computational effects}}%
In imperative programs there is a significant distinction between
_expressions_ and _programs_ (or _commands_). While the former ones
are _pure_, i.e., will always evaluate to the same result, by which
they can be safely replaced, the latter ones are _effectful_, as their
result and the ultimate outcome may produce some irreversible effect
(e.g., mutating references, throwing exceptions, performing output or
reading from input), which one should account for. Hoare logics, and,
in particular, separation logic focus on specifying effectful programs
taking expressions for granted and assuming their referential
transparency, which makes it not entirely straightforward to embed
such reasoning into the purely functional setting of the Coq
framework.
It has been a long-standing problem for the functional programming
community to reconcile the _pure_ expressions, enjoying referential
transparency, with effectful computations, until Eugenio Moggi
suggested to use the mechanism of _monads_ to separate the _results_
of computations from the possible _effects_ they can
produce%~\cite{Moggi:IC91}%, and Philip Wadler popularized this idea
with a large number of examples%~\cite{Wadler:POPL92}%, as it was
adopted in the same time by the Haskell programming language. There is
a countless number of tutorials written and available on the Web that
are targeted to help building the intuition about the "monad
magic". Although grasping some essence of monadic computations is
desirable for understanding how verification of the imperative
programs can be structured in Coq, providing the reader with yet
another "monad tutorial" is not the task of this course. Luckily, in
order to proceed to the verification in separation logic, which is the
topic of this chapter, we need only very basic intuition on what
monads are, and how they are typically used to capture the essence of
computations and their effects.
** On monads and computations
%\index{monads}%
While presenting rules for Hoare and separation logic, we have seen a
number of operators, allowing to construct larger programs from
smaller ones: conditionals, loops, binding, etc. However, only two of
the connectives are inherent to imperative programming and make it
distinct from the programming with pure functions:
%\index{imperative commands}%
%\index{commands|see {imperative commands}}%
%\index{binding}%
- _Binding_ (i.e., a program of the form $x \asgn c_1; c_2$) is a way
  to specify that the effect of the computation $c_1$ takes place
  strictly _before_ the computation $c_2$ is executed. Following its
  name this program constructor also performs binding of the (pure)
  result of the first computation, so it can be substituted to all
  occurrences of $x$ in the second command, $c_2$. In this sense,
  binding is different from expressions of the form [let x = e1 in
  e2], omnipresent in functional programs, as the latter ones might allow
  for both strict and lazy evaluation of the right-hand side
  expression [e1] depending on a semantics of the language (e.g.,
  call-by-value in Standard ML vs. call-by-need in Haskell). This
  flexibility does not affect the result of a pure program (modulo
  divergence), since [e1] and [e2] are expressions, and, hence, are
  pure. However, in the case of computations, the order should be
  fixed and this is what the binding construct serves for.
- _Returning_ a value is a command constructor (which we typeset as
  $\ret$), which allows one to embed a pure expression into the realm
  of computations. Again, intuitively, this is explained by the fact
  that expressions and commands should be distinguished
  semantically,%\footnote{Although some mainstream languages prefer to
  blur the distinction between commands and expressions in order to
  save on syntax~\cite{Scala-spec}, at the price of losing the ability
  to differentiate statically between the effectful and pure code.}%
  but sometimes an expression should be treated as a command (with a
  trivial effect or none of it at all), whose result is the very same
  expression.
These two connectives, allowing one to construct the programs by means
of binding and embedding expressions into them are captured precisely
by the $\com{Monad}$ interface, expressed, for instance, in Haskell
via the following type class:
%
\begin{alltt}
class Monad m where
    (>>=)            :: m a -> (a -> m b) -> m b
    return           :: a -> m a
\end{alltt}
%
The signature specifies that each instance of %\texttt{Monad m}% is
parametrized by one type and requires two functions to be implemented.
The %\texttt{>>=}% function is pronounced as _bind_ and describes how
a particular monad instance _combines_ two computations, such that the
second one, whose type is %\texttt{m b}%, may depend on the value of
result of the first one, whose type is %\texttt{m a}%. The result of
the overall computation is then the one of the second component, namely,
%\texttt{m b}%. The function %\texttt{return}% specifies how to
provide a "default" value for an effectful computation, i.e., how to
"pair" a value of type %\texttt{a}% with an "effect" entity in order
to receive an element of %\texttt{m a}%.
%\index{computational effects}%
%\index{Haskell}%
In this specification, the type $\com{m}$ serves as a generic
placeholder of the effect, whose nature is captured by the monad. As it
has been already pointed out, such effect might be a mutable state,
exceptions, explicit control, concurrency or input/output (all
captured by specific instances of monads in
Haskell%~\cite{PeytonJones:squad}%), as well as the fact of program
%\index{divergence}% non-termination (i.e., _divergence_), which
Haskell deliberately does not capture. In a more informal language,
the monadic type $\com{m}$ indicates that in the program "something
fishy is going on, besides the result being computed", so this type
serves as a mechanism, which is used by the type checker to make sure
that only programs with the _same_ effect are composed together by
means of binding (hence the type of the bind operator in the
$\com{Monad}$ type class). This is an important insight, which will be
directly used in the design of the verification methodology of
imperative programs using dependent types, as we will see in
%Section~\ref{sec:htt-intro}%.
** Monadic do-notation
Since composing effectful/monadic computations is a very common
operation in Haskell, the language provides a convenient [do]-notation
to write programs in a %\index{do-notation}% monadic style, such that
the invocation of the bind function in the expression of the form
%\texttt{c1 >>= (\textbackslash x -> c2)}%, where %\texttt{x}% might
occur in %\texttt{c2}%, can be written as %\texttt{\{do x <- c1;
c2\}}%.
%\index{IO monad@\texttt{IO} monad}%
For example, the program below is composed of several computations
within the %\texttt{IO}% monad, which indicates that the possible
effect of the program, which has %\texttt{IO}% in its type, can be
reading from input or writing into the output
stream%~\cite{PeytonJones-Wadler:POPL93}%.
%\newpage%
<<
main = do putStrLn "Enter a character"
          c <- getChar 
          putStrLn $ "\nThe character was: " ++ [c] 
          return ()
>>
The computations involved in the program, are represented, in
particular, by the Haskell commands (i.e., monadically-typed function
call) [putStrLn "Enter a character"], which prints a string to the
output stream, and the call to [getChar], which reads a caracter from
the input stream. All these computations are bound using the
%\texttt{<-}% syntax and [do]-notation, and the last one returns an
embedded unit value %\texttt{()}%, so the type of the whole program
$\com{main}$ is inferred to be %\texttt{IO~()}%.
* Elements of Hoare Type Theory
%\label{sec:htt-intro}%
At this point we have acquired a number of important insights that
should lead us to the idea of implementing verification of effectful
imperative programs in Coq:
- Hoare specifications in separation logic behave like types of the
  computations they specify, which is witnessed by the rules of
  weakening %\Rule{Conseq}%, function and application specification
  inference %\Rule{Hyp}% and %\Rule{App}% and recursive functions
  %\Rule{Fix}% %(Section~\ref{sec:seplog-rules}).% Moreover, since
  pre- and postconditions can depend on the values of logical
  universally-quantified variables as well as on the values of the
  command's arguments, Hoare-style specs are in fact instances of
  _dependent_ types.
- Hoare triples in separation logic specify _effectful_ computations
  that are composed using the _binding_ mechanism, with pure
  expressions being injected into them by means of "wrapping" them
  with a $\ret$ operator. This makes Hoare triples behave exactly like
  instances of _monads_ from functional programming, whose composition
  is described by, e.g., the $\com{Monad}$ type class from Haskell.
- Effectful computations can take effects, which should be accounted
  for in their specifications. The effects (or observation of an
  effectful state) are due to some dedicated operations, such as
  _pointer assignment_, _pointer reading_, _allocation_ or
  _deallocation_. These operations come with dedicated specifications,
  similarly to how operations $\com{putStrLn}$ and $\com{getChar}$ in
  Haskell are typed with respect to the $\com{IO}$ monad, whose state
  they modify.
- Another important effect, which has no explicit handling in the
  mainstream programming languages like Haskell, but should be dealt
  with in the context of pure, strongly-normalizing language of Coq,
  is _divergence_. We cannot allow one to have potentially
  non-terminating computations as expressions in Coq (i.e., those
  implemented by means of the general recursion operator $\fix$ from
  %Section~\ref{sec:loops}%), but we can afford having a monadic type
  of computations such that they might possibly diverge _if_ they are
  executed (and, even though, they will not be executed within Coq,
  they can still be type-checked, and, hence, verified). Therefore,
  monadic encoding of the fixpoint operator provides a way to escape
  the termination-checking conundrum and encode nonterminating
  programs in Coq.
%\index{Hoare Type Theory}%
%\index{HTT|see {Hoare Type Theory}}%
All these observation resulted in a series of works on _Hoare Type
Theory_ (or just HTT), which defines a notion of an _indexed Hoare
monad_ (or, _Hoare type_) as a mechanism to encode Hoare-style
specifications as dependent types and reduce the verification of
effectful progress to proving propositions in
Coq%~\cite{Nanevski-al:ICFP06,Nanevski-al:JFP08,Nanevski-al:POPL10}%.
In the rest of this chapter we will consider a number of important
concepts of HTT, so the necessary modules should be imported from the
library folder [htt], which contains the compiled files (see
Section%~\ref{sec:get-files}% for the instructions on obtaining and
building HTT from the sources).
*)

(** 
%\ccom{Add LoadPath}%
*) 

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.

Module HTT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
** The Hoare monad
%\index{Hoare type}%
%\index{Hoare monad|see {Hoare type}}%
The Hoare monad (also dubbed as Hoare type), which is a type of
result-returning effectful computations with pre- and postconditions
is represented in HTT by the type [STsep], which is, in fact, just a
notation for a more general but less tractable type [STspec], whose
details we do not present here, as they are quite technical and are
not necessary in order to verify programs in HTT.%\footnote{A curious
reader can take a look at the definitions in the module %[stmod]% of
the HTT library.}%
%\httn{STsep}%
The Hoare type is usually specified using the HTT-provided notation as
[{x1 x2 ...}, STsep (p, q)], where [p] and [q] are the predicates,
corresponding to the pre and postcondition with [p] being of type
[heap -> Prop] and [q] of type [A -> heap -> Prop], such that [A] is
the type of the result of the command being specified. The identifiers
[x1], [x2] etc. bind the logical variables that are assumed to be
universally quantified and can appear freely in [p] and [q], similarly
to the free variables in the specifications in Hoare logics
(%Section~\ref{sec:imp-spec}%). For example, the $\com{alloc}$
function has the following (simplified compared to the original one)
small footprint specification in the [STsep]-notation:
[[
alloc : forall (A : Type) (v : A),
           STsep (fun h => h = Unit,
                 [vfun (res : ptr) h => h = res :-> v])
]]
%\httn{vfun}%
That is, alloc is a procedure, which starts in an empty heap [Unit]
and whose argument [v] of type [A] becomes referenced by the pointer
(which is also the [alloc]'s result) in the resulting
singleton-pointer heap. The notation [x :-> y] corresponds to the
points-to assertion $x \mapsto y$ in the mathematical representation
of separation logic, and [[vfun x => ...]] notation accounts for the
fact that the computation can throw an
exception%~\cite{Nanevski-al:JFP08}%, the possibility we do not
discuss in this course.
** Structuring program verification in HTT
Let us now consider how the examples from %Section~\ref{sec:seplog}%
can be given specifications and verified in Coq. The program on
page%~\pageref{pg:alterx}%, which modifies a pointer [x] and keeps a
different pointer [y] intact can be given the following spec:
*)

(* Note to self: the current implementation of HTT does not support
value/type dependencies in the logical variables (e.g., {T (x: T)}),
so such cases won't be properly handled by the ghR lemma. *)

Program Definition alter_x A (x : ptr) (v : A): 
  {y (Y : nat)}, 
  STsep (fun h => exists B (w : B), h = x :-> w \+ y :-> Y,
        [vfun (_: unit) h => h = x :-> v \+ y :-> Y]) := 
  Do (x ::= v).

(**
%\ccom{Program Definition}%
The Coq command %\texttt{Program}% [Definition] is similar to the
standard definition [Definition] except for the fact that it allows
the expression being defined to have a type, some of whose components
haven't yet been type-checked and remain to be filled by the
programmer, similarly to Agda's %\index{Agda}% incremental
development%~\cite{Sozeau:TYPES06}%. That is, based on the expression
itself ([Do (x ::= v)]), Coq will infer _the most general type_ that
the expression can be allowed to have, and then it becomes a
programmer's _obligation_ to show that the declared type is actually a
specialization of the inferred type. In the context of HTT,
the type, inferred by Coq based on the definition, can be seen
as a specification with the _weakest pre_ and _strongest
postconditions_, which can then be weakened via the %\Rule{Conseq}%
rule. The program itself is wrapped into the [Do]-notation, which is
provided by the HTT library and indicates that the computations inside
always deal with the [STsep] type, similar to the Haskell's treatment
of [do]-notation.
%\httn{Do}%
The type of the program [alter_x] is specified explicitly via the
[STsep]-notation. There are two logical variables: the pointer [y] and
the value [Y] of type [nat], which is referenced by [y]. The
precondition states the existence of some type [B] and value [w], such
that [x] points to it. The postcondition specifies that the result is
of type [unit] (and, therefore, is unconstrained), and the content of
the pointer [x] became [v], while the content of the pointer [y]
remained unchanged. Notice that we make explicit use of the PCM
notation (%Section~\ref{sec:pcms}%) for the empty heap, which is
paraphrased as [Unit] and for the disjoint union of heaps, which is
expressed through the join operator [\+].
After stating the definition, Coq generates a series of obligations to
prove in order to establish the defined program well-typed with
respect to the stated type.
[[
alter_x has type-checked, generating 1 obligation(s)
Solving obligations automatically...
1 obligation remaining
Obligation 1 of alter_x:
forall (A : Type) (x : ptr) (v : A),
conseq (x ::= v)
  (logvar
     (fun y : ptr =>
      logvar
        (fun Y : nat =>
         binarify
           (fun h : heap => exists (B : Type) (w : B), h = x :-> w \+ y :-> Y)
           [vfun _ h => h = x :-> v \+ y :-> Y]))).
]]
The statement looks rather convoluted due to a number of type
definitions and notations used and essentially postulates that from
the proposition, corresponding to the specification inferred by Coq
from the program definition, we should be able to prove the
specification that we have declared explicitly. Instead of explaining
each component of the goal, we will proceed directly to the proof and
will build the necessary intuition as we go.
The proof mode for each of the remaining obligations is activated by
the Vernacular command [Next Obligation], which automatically moves
some of the assumptions to the context.
%\ccom{Next Obligation}%
*)

Next Obligation.

(**
[[
  A : Type
  x : ptr
  v : A
  ============================
   conseq (x ::= v)
     (logvar
        (fun y : ptr =>
         logvar
           (fun Y : nat =>
            binarify
              (fun h : heap =>
               exists (B : Type) (w : B), h = x :-> w \+ y :-> Y)
              [vfun _ h => h = x :-> v \+ y :-> Y])))
]]
A usual first step in every HTT proof, which deals with a spec with
logical variables is to "pull them out", so they would just become
simple assumptions in the goal, allowing one to get rid of the
[logvar] and [binarify] calls in the goal.%\footnote{In fact, the
proper handling of the logical variables is surprisingly tricky in a
type-based encoding, which is what HTT delivers. It is due to the fact
that the \emph{same} variables can appear in both pre- and
postconditions. Earlier implementations of HTT used \emph{binary}
postconditions for this
purpose~\cite{Nanevski-al:JFP08,Nanevski-al:POPL10}, which was a cause
of some code duplication in specifications and made the spec look
differently from those that someone familiar with the standard Hoare
logic would expect. Current implementation uses an encoding with
recursive notations to circumvent the code duplication problem. This
encoding is a source of the observed occurrences of %[logvar]% and
%[binarify]% definitions in the goal.}% This is what is done by
applying the lemma [ghR] %\httl{ghR}% to the goal.
*)

apply: ghR. 

(**
[[
  A : Type
  x : ptr
  v : A
  ============================
   forall (i : heap) (x0 : ptr * nat),
   (exists (B : Type) (w : B), i = x :-> w \+ x0.1 :-> x0.2) ->
   valid i -> verify i (x ::= v) [vfun _ h => h = x :-> v \+ x0.1 :-> x0.2]
]]
We can now move a number of assumptions, arising from the "brushed"
specification, to the context, along with some rewriting by equality
and simplifications.
*)

move=>h1 [y Y][B][w]->{h1} _ /=.

(**
[[
  ...
  B : Type
  w : B
  ============================
   verify (x :-> w \+ y :-> Y) (x ::= v) [vfun _ h => h = x :-> v \+ y :-> Y]
]]
%\httn{verify}%
The resulting goal is stated using the [verify]-notation, which means
that in this particular case, in the heap of the shape [x :-> w \+ y
:-> Y] we need to be able to prove that the result and the produced
heap of the command [x ::= v] satisfy the predicate [[vfun _ h => h =
x :-> v \+ y :-> Y]]. This goal can be proved using one of the
numerous [verify]-lemmas that HTT provides (try executing [Search _
(verify _ _ _)] to see the full list), however in this particular case
the program and the goal are so simple and are obviously correct that
the statement can be proved by means of proof automation, implemented
in HTT by a brute-force tactic [heval], which just tries a number of
[verify]-lemmas applicable in this case modulo the shape of the heap.
%\httt{heval}%
*)

by heval.
Qed.

(**
** Verifying the factorial procedure mechanically
%\label{sec:factver}%
Proving an assignment for two non-aliased pointers was a simple
exercise, so now we can proceed to a more interesting program, which
features loops and conditional expressions, namely, imperative
implementation of the factorial function.
Our specification and verification process will follow precisely the
story of %Section~\ref{sec:fact-logic}%. We start by defining the
factorial in the most declarative way---as a pure recursive function
in Coq itself.
*)

Fixpoint fact_pure n := if n is n'.+1 then n * (fact_pure n') else 1.

(** 
Next, we define the loop invariant [fact_inv], which constraints the
heap shape and the values of the involved pointers, [n] and [acc],
mimicking precisely the definition of $\finv$:
*)

Definition fact_inv (n acc : ptr) (N : nat) h : Prop := 
  exists n' a': nat, 
  [/\ h = n :-> n' \+ acc :-> a' & 
      (fact_pure n') * a' = fact_pure N].

(** 
To show how separation logic, in general and its particular
implementation in HTT, allows one to build the reasoning
_compositionally_ (i.e., by building the proofs about large programs
from the facts about their components), we will first provide and
prove a specification for the internal factorial loop, which, in fact,
performs all of the interesting computations, so the rest of the
"main" function only takes care of allocation/deallocation of the
pointers [n] and [acc]. The loop will be just a function, taking an
argument of the type unit and ensuring the invariant [fact_inv] in its
pre- and postcondition, as defined by the following type [fact_tp],
parametrized by the pointers [n] and [acc].
*)

Definition fact_tp n acc := 
  unit -> {N}, 
     STsep (fact_inv n acc N, 
           [vfun (res : nat) h => fact_inv n acc N h /\ res = fact_pure N]).

(** 
The type [fact_tp] ensures additionally that the resulting value is in
fact a factorial of [N], which is expressed by the conjunct [res =
fact_pure N]. 
%\index{fixed-point combinator}%
%\index{Y-combinator|see {fixed-point combinator}}%
The definition of the factorial "accumulator" loop is then represented
as a recursive function, taking as arguments the two pointers, [n] and
[acc], and also a unit value. The body of the function is defined
using the monadic fixpoint operator [Fix]%\httn{Fix}%, whose semantics
is similar to the semantics of the classical _Y-combinator_, defined
usually by the equation [Y f = f (Y f)], where [f] is a fixpoint
operator argument that should be thought of as a recursive function
being defined. Similarly, the fixpoint operator [Fix], provided by
HTT, takes as arguments a function, which is going to be called
recursively ([loop], in this case), its argument and _body_. The named
function (i.e., [loop]) can be then called from the body recursively.
In the similar spirit, one can define nested loops in HTT as nested
calls of the fixpoint operator.
*)

Program Definition fact_acc (n acc : ptr): fact_tp n acc := 
  Fix (fun (loop : fact_tp n acc) (_ : unit) => 
    Do (a1 <-- read nat acc;
        n' <-- read nat n;
        if n' == 0 then ret a1
        else acc ::= a1 * n';;
             n ::= n' - 1;;
             loop tt)).

(** 
The body of the accumulator loop function reproduces precisely the
factorial implementation in pseudocode from page%~\pageref{ref:facto}%. It first reads the values of
the pointers [acc] and [n] into the local variables [a1] and
[n']. Notice that the binding of the local immutable variables is
represented by the [<--] notation, which corresponds to the _bind_
operation of the Hoare monad [STsep]. The function then uses Coq's
standard conditional operator and returns a value of [a1] if [n'] is
zero using the monadic [ret] operator. %\httl{ret}% In the case of
[else]-branch, the new values are written to the pointers [acc] and
[n], after which the function recurs.
Stating the looping function like this leaves us with one obligation
to prove.
*)

Next Obligation. 

(** 
As in the previous example, we start by transforming the goal, so the
logical variable [N], coming from the specification of [fact_tp] would
be exposed as an assumption. We immediately move it to the context
along with the initial heap [i].%\httl{ghR}%
*)

apply: ghR=>i N. 

(**
[[
  ...
  i : heap
  N : nat
  ============================
   fact_inv n acc N i ->
   valid i ->
   verify i
     (a1 <-- ! acc;
      n' <-- ! n;
      (if n' == 0 then ret a1 else acc ::= a1 * n';; n ::= n' - 1;; loop tt))
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]
We next case-analyse on the top assumption with the invariant
[fact_inv] to acquire the equality describing the shape of the heap
[i]. We then rewrite [i] in place and move a number of hypotheses to
the context.
*)

case=>n' [a'][->{i}] Hi _. 

(**
Now the goal has the shape [verify (n :-> n' \+ acc :-> a') ...],
which is suitable to be hit with the automation by means of the
[heval] %\httt{heval}% tactic, progressing the goal to the state when
we should reason about the conditional operator.
*)

heval. 

(**
[[
  ...
  n' : nat
  a' : nat
  Hi : fact_pure n' * a' = fact_pure N
  ============================
   verify (n :-> n' \+ acc :-> a')
     (if n' == 0 then ret a' else acc ::= a' * n';; n ::= n' - 1;; loop tt)
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]
The goal, containing a use of the conditional operator, is natural to
be proved on case analysis on the condition [n' == 0].
*)

case X: (n' == 0). 

(** 
Now, the first goal has the form 
[[
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = true
  ============================
   verify (n :-> n' \+ acc :-> a') (ret a')
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]
To prove it, we will need one of the numerous [val]-lemmas, delivered
as a part of HTT libraries and directly corresponding to the rules of
separation logic (%Section~\ref{sec:seplog-rules}%). The general
recipe on acquiring intuition for the lemmas applicable for each
particular [verify]-goal is to make use of Ssreflect's [Search]
machinery. For instance, in this particular case, given that the
command to be verified (i.e., the second argument of [verify]) is [ret
a'], let us try the following query.
*)

Search _ (verify _ _ _) (ret _).

(**
The request results report, in particular, on the following lemma
found:
[[
val_ret
   forall (A : Type) (v : A) (i : heapPCM) (r : cont A),
   (valid i -> r (Val v) i) -> verify i (ret v) r
]]
The lemma has a statement in its conclusion, which seems like it can
be unified with our goal, so we proceed by applying it.
%\httl{val\_ret}%
*)

- apply: val_ret=>/= _. 

(** 
The remaining part of the proof of this goal has absolutely nothing to
do with program verification and separation logic and accounts to
combining a number of arithmetical facts in the goal via the
hypotheses [Hi] and [X]. We proceed by first turning boolean
equality in [X] into propositional via the view [eqP] and then
substituting all occurrences of [n'] in the goal and other assumptions
via Coq's tactic [subst]. The rest of the proof is by providing
existential witnesses and rewriting [1 * a'] to [a'] in [Hi].
%\ssrt{subst}% 
*)

  move/eqP: X=>Z; subst n'.
  split; first by exists 0, a'=>//.
  by rewrite mul1n in Hi.

(** 
The second goal requires satisfying the specification of a sequence of
assignments, which can be done automatically using the [heval] tactic.
*)

heval. 

(** 
[[
  loop : fact_tp n acc
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = false
  ============================
   verify (n :-> (n' - 1) \+ acc :-> (a' * n')) (loop tt)
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]
The next step is somewhat less obvious, as we need to prove the
specification of the recursive call to [loop], whose spec is also
stored in our assumption context. Before we can apply a lemma, which
is an analogue of the %\Rule{App}%, we need to _instantiate_ the
logical variables of [loop]'s specification (which is described by the
type [fact_tp]). The spec [fact_tp] features only one logical variable,
namely [N], so we provide it using the HTT lemma [gh_ex].%\footnote{In
a case of several logical variables, the lemma should have been
applied the corresponding number of times with appropriate
arguments.}%%\httl{gh\_ex}%
*)

apply: (gh_ex N). 

(**
Now to verify the call to [loop], we can apply the lemma [val_doR],
corresponding to the rule %\Rule{App}%, which will replace the goal by
the precondition from the spec [fact_tp n acc]. In HTT there are
several lemmas tackling this kind of a goal, all different in the way
they treat the postconditions, so in other cases it is recommended to
run [Search "val_do"] to see the full list and chose the most
appropriate one.
%\httl{val\_doR}%
*)

apply: val_doR=>// _.

(**
[[
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = false
  ============================
   fact_inv n acc N (n :-> (n' - 1) \+ acc :-> (a' * n'))
]]
As in the case of the previous goal, the remaining proof is focused on
proving a statement about a heap and natural numbers, so we just
present its proof below without elaborating on the details, as they
are standard and mostly appeal to propositional reasoning
(Chapter%~\ref{ch:logic}%) and rewriting by lemmas from Ssreflect's
[ssrnat] module.
*)

exists (n'-1), (a' * n'); split=>//=. 
rewrite -Hi=>{Hi}; rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
by case: n' X=>//= n' _; rewrite subn1 -pred_Sn. 
Qed.

(** 
We can now implement the main body of the factorial function, which
allocates the necessary pointers, calls the accumulator loop and then
frees the memory.
*)

Program Definition fact (N : nat) : 
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fact_pure N /\ h = Unit]) := 
  Do (n   <-- alloc N;
      acc <-- alloc 1;
      res <-- fact_acc n acc tt;
      dealloc n;;
      dealloc acc;;
      ret res).

(** 
The specification of [fact] explicitly states that its execution
starts and terminates in the empty heap; it also constraints its
result to be a factorial of [N].
*)

Next Obligation.

(** 
Since the spec of [fact] does not have any logical variables (its
postcondition only mentions its argument [N]), there is no need to
make use of the [ghR] lemma. However, the current goal is somewhat
obscure, so to clarify it let us unfold the definition of [conseq]
(which simply states that the consequence between the inferred type of
the program and the stated spec should be proved) and simplify the goal.
*)

rewrite /conseq =>/=.

(** 
[[
  N : nat
  ============================
   forall i : heap,
   i = Unit ->
   verify i
     (n <-- alloc N;
      acc <-- alloc 1;
      res <-- fact_acc n acc tt; dealloc n;; dealloc acc;; ret res)
     (fun (y : ans nat) (m : heap) =>
      i = Unit -> [vfun res h => res = fact_pure N /\ h = Unit] y m)
]]
Next, we can rewrite the equality on the heap (which is [Unit]) and
proceed by two runs of the [heval] tactic, which will take care of the
allocated pointers yielding new assumptions [n] and [acc], arising
from the implicit application of the %\Rule{Bind}% rule.
*)

move=>_ ->.
heval=>n; heval=>acc; rewrite joinC unitR.

(**
We have now came to the point when the function [fact_acc], which we
have previously verified, is going to be invoked, so we need to make
use of what corresponds to the rule %\Rule{App}% again. In this case,
however, the tactic [val_doR] will not work immediately, so we will
first need to reduce the program to be verified from the binding
command to a mere function call by means of HTT's [bnd_seq] lemma,
which tackles the binding _combined_ with a call to a user-defined
function, and this is exactly our case. Next, we instantiate the
[fact_acc] specification's logical variable [N] by applying [gh_ex]
and proceed with the application of [val_doR].
%\httl{bnd\_seq}%
*)

apply: bnd_seq=>/=; apply: (gh_ex N); apply: val_doR=>//.

(** 
The first of the resulting two goals is an obligation arising from the
need to prove [fact_acc]'s precondition.
*)

 - by exists N, 1; rewrite muln1.

(**
The second goal is the remainder of the program's body, which performs
deallocation, so the proof for it is accomplished mostly by applying
[heval] tactic.
*)

by move=>_ _ [[n'][a'][->] _ ->] _; heval.  
Qed.

(** 
%\begin{exercise}[Swapping two values] \label{ex:swap}%
Implement in HTT a function that takes as arguments two pointers, [x]
and [y], which point to natural numbers, and swaps their
values. Reflect this effect in the function's specification and verify
it.

%\hint% Instead of reading the value of a pointer into a variable [t]
 using the [t <-- !p] notation, you might need to specify the _type_
 of the expected value explicitly by using the "de-sugared" version of
 the command [t <-- read T p], where [T] is the expected type. This
 way, the proof will be more straightforward.
%\end{exercise}%
*)

(* begin hide *)
Program Definition swap (x y : ptr):
  {(a b : nat)},
  STsep (fun h => h = x :-> a \+ y :-> b,
        [vfun (_: unit) h => h = x :-> b \+ y :-> a]) :=
  Do (vx <-- read nat x;
      vy <-- read nat y;
      x ::= vy;;
      y ::= vx).
Next Obligation.
apply:ghR=>_ [a b]->/= V.
apply: bnd_seq; apply: val_read=>_.
apply: bnd_seq; apply: val_readR =>/= _.
apply: bnd_writeR=>/=.
by apply: val_writeR=>/=.
Qed.
(* end hide *)

(**
%\begin{exercise}%
Try to redo the exercise%~\ref{ex:swap}% _without_ using the
automation provided by the [heval] tactic. The goal of this exercise
is to explore the library of HTT lemmas, mimicking the rules of the
separation logic. You can always display the whole list of the
available lemmas by running the command [Search _ (verify _ _ _)] and
then refine the query for specific programs (e.g., [read] or [write]).
%\end{exercise}%
*)


(** 
%
\begin{figure}[t!]
\begin{alltt}
    fun fib (\var{N} : nat): nat = \{
      if \var{N} == 0 then ret 0
       else if \var{N} == 1 then ret 1
       else n <-- alloc 2;
            x <-- alloc 1;
            y <-- alloc 1;
            res <-- 
              (fix loop (_ : unit). 
                 n' <-- !n;
                 y' <-- !y;
                 if n' == \var{N} then ret y'
                 else tmp <-- !x;
                      x ::= y';;
                      x' <-- !x;
                      y ::= x' + tmp;;
                      n ::= n' + 1;;
                      loop(tt))(tt).
            dealloc n;;
            dealloc x;;
            dealloc y;;
            ret res    
    \}
\end{alltt}
\caption{An imperative procedure computing the $N$th Fibonacci
number.}
\label{fig:fibcode}
\end{figure}
%
%\begin{exercise}[Fibonacci numbers]%
%\index{Fibonacci numbers}%
Figure%~\ref{fig:fibcode}% presents the pseudocode listing of an
efficient imperative implementation of the function $\com{fib}$ that
computes the [N]th Fibonacci number.  Your task will be to prove its
correctness with respect to the "pure" function [fib_pure] (which you
should define in plain Coq) as well as the fact that it starts and
ends in an empty heap.

%\hint% What is the loop invariant of the recursive computation
 defined by means of the [loop] function?

%\hint% Try to decompose the reasoning into verification of several
 code pieces as in the factorial example and then composing them
 together in the "main" function.
%\end{exercise}%
*)


(* begin hide *)
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
(* end hide *)

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
* On shallow and deep embeddings
%\label{sec:shallowdeep}%
A noteworthy trait of HTT's approach to verification of effectful
programs is its use of _shallow embedding_ of the imperative language
%\index{shallow embedding}% into the programming language of Coq. In
fact, the imperative programs that we have written, e.g., the
factorial procedure, are mere Coq programs, written in Coq syntax with
a number of HTT-specific notations. Moreover, the Hoare triples, by
means of which we have provided the specifications to the
heap-manipulating programs are nothing but specific types defined in
Coq. This is what makes the way effectful programs encoded _shallow_:
the new programming language of imperative programs and their
Hoare-style specifications has been defined as a subset of Coq
programming language, so most of the Coq's infrastructure for parsing,
type-checking, name binding and computations could be reused off the
shelf. In particular, shallow embedding made it possible to represent
the variables in imperative programs as Coq's variables, make use of
Coq's conditional operator and provide specifications to higher-order
procedures without going into the need to design a higher-order
version of a separation logic first (since the specifications in HTT
are just types of monadically-typed expressions). Furthermore, shallow
embedding provided us with a benefit of reusing Coq's name binding
machinery, so we could avoid the problem of _name capturing_ by means
using the approach known as %\emph{Higher-Order Abstract
Syntax}~\cite{Pfenning-Elliott:PLDI88}%, representing immutable
variables by Coq's native variables (disguised by the binding notation
[<--]).
%\index{DSL|see{domain-specific language}}% 
%\index{domain-specific language}% 
%\index{internal DSL}%
%\index{embedded DSL}%
To summarize, shallow embedding is an approach of implementing
programming languages (not necessarily in Coq) characterized by
representation of the language of interest (usually called a
_domain-specific language_ or DSL) as a subset of another
general-purpose _host_ language, so the programs in the former one are
simply the programs in the latter one. The idea of shallow embedding
originated in early '60s with the beginning of the era of the Lisp
programming language%~\cite{Graham:BOOK}\index{Lisp}%, which, thanks
to its macro-expansion system, serves as a powerful platform to
implement DSLs by means of shallow embedding (such DSLs are sometimes
called _internal_ or _embedded_). Shallow embedding in the world of
practical programming is advocated for a high speed of language
prototyping and the ability to re-use most of the host language
infrastructure.
An alternative approach of implementing and encoding programming
languages in general and in Coq in particular is called _deep
embedding_, and amounts to the implementation of a language of
interest from scratch, essentially, writing its parser, interpreter
and type-checker in a general-purpose language. In practice, deep
embedding is preferable when the overall performance of the
implemented language runtime is of more interest than the speed of DSL
implementation, since then a lot of intermediate abstractions, which
are artefacts of the host language, can be avoided.
In the world of mechanized program verification, both approaches, deep
and shallow embedding, have their own strengths and weaknesses.
Although implementations of deeply embedded languages and calculi
naturally tend to be more verbose, design choices in them are usually
simpler to explain and motivate. Moreover, the deep embedding approach
makes the problem of name binding to be explicit, so it would be
appreciated as an important aspect in the design and reasoning about
programming
languages%~\cite{Aydemir-al:POPL08,Weirich-al:ICFP11,Chargueraud:JAR12}%. We
believe, these are the reasons why this approach is typically chosen as
a preferable one when teaching program specification and verification in
Coq%~\cite{Pierce-al:SF}%.
Importantly, deep embedding gives the programming language implementor
the _full control_ over its syntax and semantics.%\footnote{This
observation is reminiscent to the reasons of using deep embedding in
the practical world.}% In particular, the expressivity limits of a
defined logic or a type system are not limited by expressivity of
Coq's (or any other host language's) type system. Deep embedding makes
it much more straightforward to reason about _pairs_ of programs by
means of defining the relations as propositions on pairs of syntactic
trees, which are implemented as elements of corresponding datatypes.
This point, which we deliberately chose not to discuss in detail in
this course, becomes crucial when one needs to reason about the
correctness of program transformations and optimizing
compilers%~\cite{Appel:BOOK14}%. In contrast, the choice of shallow
embedding, while sparing one the labor of implementing the parser,
name binder and type checker, may limit the expressivity of the
logical calculus or a type system to be defined. In the case of HTT,
for instance, it amounts to the impossibility of specifying programs that
store _effectful functions_ and their specifications into a
heap.%\footnote{This limitation can be, however, overcome by
postulating necessary \emph{axioms} on top of CIC.}%
In the past decade Coq has been used in a large number of projects
targeting formalization of logics and type systems of various
programming languages and proving their soundness, with most of them
preferring the deep embedding approach to the shallow one. We believe
that the explanation of this phenomenon is the fact that it is much
more straightforward to define semantics of a deeply-embedded
"featherweight" calculus%~\cite{Igarashi-al:TOPLAS01}% and prove
soundness of its type system or program logic, given that it is the
_ultimate goal_ of the research project. However, in order to use the
implemented framework to specify and verify realistic programs, a
significant implementation effort is required to extend the deep
implementation beyond the "core language", which makes shallow
embedding more preferable in this case---a reason why this way has
been chosen by HTT.
* Soundness of Hoare Type Theory
Because of shallow embedding, every valid Coq program is also a valid
HTT program. However, as it has been hinted at the beginning of
%Section~\ref{sec:htt-intro}%, imperative programs written in HTT
cannot be simply executed, as, due to presence of general loops and
recursion, they simply may not terminate. At this point, a reader may
wonder, what good is verification of programs that cannot be run and
what is it that we have verified?
To answer this question, let us revise how the _soundness_ of a Hoare
logic is defined. HTT takes definition of a Hoare triple (or, rather,
a Hoare type, since in HTT specs are types) from
page%~\pageref{pg:triple}% literally but implements it not via an
operational semantics, i.e., defining how a program _should be run_,
but using a denotational semantics%~\cite[Chapter~5]{Winskel:BOOK}%,
i.e., defining what a program _is_. The HTT library comes with a
module [stmod] that defines denotational semantics of HTT
commands%\footnote{I.e., monadic values constructed by means of the
write/alloc/dealloc/read/return commands and standard Coq connectives,
such as conditional expression or pattern matching.}% and Hoare
triples, defined as types. Each command is represented by a function,
which is sometimes referred to as a _state transformer_, in the sense that
it takes a particular heap and transforms it to another heap, also
returning some result. The denotational semantics of HTT commands in
terms of state-transforming functions makes it also possible to define
what is a semantics of a program resulting from the use of the [Fix]
operator (%Section~\ref{sec:factver}%).%\footnote{In fact, a standard
construction from the domain theory is used, namely, employing
Knaster-Tarski theorem on a lattice of monotone functions. This
subject is, however, outside of the scope of this course, so we
redirect the reader to the relevant literature: Glynn Winskel's book
for the theoretical construction~\cite[Chapters~8--10]{Winskel:BOOK}
or Adam Chlipala's manuscript covering a similar
implementation~\cite[\S~7.2]{Chlipala:BOOK}.}% The semantics of Hoare
types $\spec{h~|~P(h)}-\spec{\res, h~|~Q(\res, h)}$ is defined as
_sets_ of state transforming functions, taking a heap satisfying $P$
to the result and heap satisfying $Q$. Therefore, the semantic account
of the verification (which is implemented by means of type-checking in
Coq) is checking that semantics of a particular HTT program (i.e., a
state-transforming function) lies _within_ the semantics of its type
as a set.
%\index{extraction}%
If execution of programs verified in HTT is of interest, it can be
implemented by means of _extraction_ of HTT commands into programs
in an external language, which supports general recursion natively
(e.g., Haskell). In fact, such extraction has been implemented in the
first release of HTT%~\cite{Nanevski-al:JFP08}%, but was not ported to
the latest release.
* Specifying and verifying programs with linked lists
We conclude this chapter with a _tour de force_ of separation logic in
HTT by considering specification and verification of programs
operating with single-linked lists. Unlike the factorial example, an
implementation of single-linked lists truly relies on pointers, and
specifying such datatypes and programs is an area where separation
logic shines.
%\index{single-linked lists}%
On the surface, a single-linked list can be represented by a pointer,
which points to its head.
*)

Definition llist (T : Type) := ptr.

Section LList.
Variable T : Type.
Notation llist := (llist T).

(** 
However, in order to specify and prove interesting facts about
imperative lists, similarly to the previous examples, we need to
establish a connection between what is stored in a list heap and a
purely mathematical sequence of elements. This is done using the
_recursive predicate_ [lseg], which relates two pointers, [p] and [q],
pointing correspondingly to the head and to the tail of the list and a
logical sequence [xs] of elements stored in the list.
*)

Fixpoint lseg (p q : ptr) (xs : seq T): Pred heap := 
  if xs is x::xt then 
    [Pred h | exists r h', 
       h = p :-> x \+ (p .+ 1 :-> r \+ h') /\ h' \In lseg r q xt]
  else [Pred h | p = q /\ h = Unit].

(** 
The notation [[Pred h | ...]] is just an abbreviation for a function
of type [heap -> Prop], where [h] is assumed to be of the type [heap]. The
notation [h \In f] is a synonym for [f h] assuming [f] is a predicate
of type [heap -> Prop].
The following lemma [lseg_null] states a fact, which is almost
obvious: given that the heap [h], corresponding to a linked list, is a
valid one (according to its notion of validity as a PCM) and the head
pointer of a list structure is [null], then its tail pointer is [null]
as well, and the overall list is empty.
*)

Lemma lseg_null xs q h : 
         valid h -> h \In lseg null q xs -> 
         [/\ q = null, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] D /= H; first by case: H=><- ->.
case: H D=>r [h'][->] _. 
(**
[[
  ...
  r : ptr
  h' : heap
  ============================
   valid (null :-> x \+ (null.+1 :-> r \+ h')) ->
   [/\ q = null, x :: xs = [::] & null :-> x \+ (null.+1 :-> r \+ h') = Unit]
]]

In the process of the proof we are forced to use the validity of a
heap in order to derive a contradiction. In the case of heap's
validity, one of the requirements is that every pointer in it is not
[null]. We can make it explicit by rewriting the top assumption with
one of the numerous HTT lemmas about heap validity (use the [Search]
machinery to find the others).

%\httl{hvalidPtUn}%

*)

rewrite validPtUn. 
(**
[[
  ...
  ============================
   [&& null != null, valid (null.+1 :-> r \+ h')
     & null \notin dom (null.+1 :-> r \+ h')] ->
   [/\ q = null, x :: xs = [::] & null :-> x \+ (null.+1 :-> r \+ h') = Unit]
]]

The conjunct [null != null] in the top assumption is enough to
complete the proof by implicit discrimination.

*)

done.
Qed. 

(**  
We can now define a particular case of linked
lists---_null-terminating_ lists and prove the specification of a
simple insertion program, which allocates a new memory cell for an
element [x] and makes it to be a new head of a list pointed by
[p]. The allocation is performed via the primitive [allocb], which
allocates a number of subsequent heap pointers (two in this case, as
defined by its second argument) and sets all of them to point to the
value provided.
%\httl{allocb}%
*)

Definition lseq p := lseg p null.

Program Definition insert p x : 
  {xs}, STsep (lseq p xs, [vfun y => lseq y (x::xs)]) :=
  Do (q <-- allocb p 2; 
      q ::= x;;
      ret q). 
Next Obligation. 
apply: ghR=>i xs H _; heval=>x1; rewrite unitR -joinA; heval. 
Qed.

(** 
Next, we are going to give a specification to the list
"beheading"---removing the head element of a list. For this, we will
need a couple of auxiliary lemmas involving the list heap predicate
[lseg_neq]. The first one, [lseq_null] is just a specialization of the
previously proved [lseg_null.]
*)


Lemma lseq_null xs h : valid h -> h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

(** 
The next lemma, [lseq_pos], states that if [p] is a head of a linked list,
defined by a heap [h], is not [null], then it can be "beheaded". That
is, there will exist a head value [x], a "next" [r] and a residual
heap [h'], such that the heap [h'] corresponds to the list's tail,
which is expressed by Ssreflect's [behead] function.
*)

Lemma lseq_pos xs p h : 
        p != null -> h \In lseq p xs -> 
        exists x r h', 
          [/\ xs = x :: behead xs, 
              p :-> x \+ (p .+ 1 :-> r \+ h') = h & h' \In lseq r (behead xs)].
Proof.
case: xs=>[|x xs] /= H []; first by move=>E; rewrite E eq_refl in H.
by move=>y [h'][->] H1; heval.
Qed.

(** 
We can finally define and specify the HTT procedure [remove], which
removes the current head of the list and returns the pointer to its
next element or [null] if the list is empty.
*)


Program Definition 
remove p : {xs}, STsep (lseq p xs, [vfun y => lseq y (behead xs)]) :=
  Do (if p == null then ret p 
      else pnext <-- !(p .+ 1);
           dealloc p;; 
           dealloc p .+ 1;;
           ret pnext). 

(** 
The proof is straightforward and employs both lemmas: [lseq_null] to
prove the "[null]" case and [lseq_pos] for the case when the list has
at least one element.
*)

Next Obligation.
apply: ghR=>i xs H V; case: ifP H=>H1.
- by rewrite (eqP H1); case/(lseq_null V)=>->->; heval. 
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by heval; rewrite 2!unitL.
Qed.

(** 
%\begin{exercise}%
Define and verify function [remove_val] which is similar to [remove],
but also returns the _value_ of the last "head" of the list before
removal, in addition to the "next" pointer. Use Coq's [option] type to
account for the possibility of an empty list in the result.
%\ssrd{option}%
%\end{exercise}%
*)

(* begin hide *)
Program Definition remove_val p : {xs}, 
  STsep (lseq p xs, 
         [vfun y h => lseq y.1 (behead xs) h /\ 
                      y.2 = (if xs is x::xs' then Some x else None)]) := 
  Do (if p == null then ret (p, None) 
      else x <-- read T p;
           pnext <-- !(p .+ 1);
           dealloc p;; 
           dealloc p .+ 1;;
           ret (pnext, Some x)). 
Next Obligation.
apply: ghR=>i xs H V; case: ifP H=>H1.
- by rewrite (eqP H1); case/(lseq_null V)=>->->; heval. 
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by heval; rewrite 2!unitL.
Qed.
(* end hide *)

End LList.

(** 
%\begin{exercise}[Imperative in-place map]% 
Define, specify and verify the imperative higher-order function
[list_map] that takes as arguments two types, [S] and [T], a function [f
: T -> S] and a head [p] of a single-linked list, described by a
predicate [lseq], and changes the list in place by applying [f] to
each of its elements, while preserving the list's structure. The
specification should reflect the fact that the new "logical" contents
of the single-linked list are an [f] map-image of the old content.

%\hint% The lemmas [lseq_null] and [lseq_pos], proved previously,
 might be useful in the proof of the established specification.

%\hint% A tail-recursive call can be verified via HTT's [val_do]
 lemma, reminiscent to the rule %\Rule{App}%. However, the heap it
 operates with should be "massaged" appropriately via PCM's lemmas
 [joinC] and [joinA].

%\end{exercise}%
*)

(* begin hide *)
Definition mapT T S (f : T -> S) : Type := 
  forall p, {xs}, STsep (@lseq T p xs, 
                         [vfun y h => y = tt /\ @lseq S p (map f xs) h]).

Program Definition list_map T S p (f : T -> S) :
   {xs}, STsep (@lseq T p xs, 
                [vfun y h => y = tt /\ @lseq S p (map f xs) h]) :=
    Fix (fun (loop : mapT f) (p : ptr) =>      
      Do (if p == null 
          then ret tt 
          else x <-- read T p;
               next <-- (read ptr p .+ 1);
               p ::= f x;;
               loop next)) p.
Next Obligation.
apply: ghR=>h xs H V. 
case X: (p == null).
- apply: val_ret=>_ /=;  split=>//. 
  by move/eqP: X H=>-> /=; case/(lseq_null V)=>->->. 
case/negbT /lseq_pos /(_ H): X=>x[next][h'][Z1] Z2 H1; subst h.
heval.
move/validR: V=> V1; apply: (gh_ex (behead xs)).
rewrite [_ \+ h']joinC joinC -joinA; apply: val_do=>//=.
case=>m[_]H2 V2; split=>//.
rewrite [_ \+ p :-> _]joinC joinC. 
by rewrite Z1 /=; exists next, m; rewrite joinA.
Qed.
(* end hide *)

(**
%\begin{exercise}[In-place list reversal]%
Let us define the following auxiliary predicates, where [shape_rev]
splits the heap into two disjoint linked lists (by means of the
separating conjunction [#]).
*)

Definition shape_rev T p s := [Pred h | h \In @lseq T p.1 s.1 # @lseq T p.2 s.2].

(** 
%\noindent%
Then the in-place list reversal is implemented by means of the
recursive function [reverse] with a loop invariant expressed using the
type [revT].
*)

Definition revT T : Type := 
  forall p, {ps}, STsep (@shape_rev T p ps, [vfun y => lseq y (rev ps.1 ++ ps.2)]).

Program Definition 
reverse T p : {xs}, STsep (@lseq T p xs, [vfun y => lseq y (rev xs)]) :=
  Do (let: reverse := Fix (fun (reverse : revT T) p => 
                        Do (if p.1 == null then ret p.2 
                            else xnext <-- !p.1 .+ 1;
                                 p.1 .+ 1 ::= p.2;;
                                 reverse (xnext, p.1)))
      in reverse (p, null)).

(** 
%\noindent%
We invite the reader to conduct the verification of [reverse], proving
that it satisfies the given specification.

%\hint% It might be a good idea to make use of the previously proved
 lemmas [lseq_null] and [lseq_pos].

%\hint% Be careful with the logical values of variables passed to the
[gh_ex] lemma before verifying a recursive call of [reverse].

%\hint% A verification goal to a function defined via [Fix] can be
reduced via the [val_doR] lemma or similar ones.

%\hint% The [shape_rev] predicate is in fact an existential in
disguise: it can be proved by providing appropriate witnesses.

%\hint% Rewriting [rev_cons], [cat_rcons] and [cats0] from the [seq]
library will be useful for establishing equalities between lists.
*)

(* begin hide *)
Next Obligation.
apply:ghR=>i[xs1 xs2]; case=>h1[h2][->{i}]/=[H1 H2] V1.
case X: (p == null) H1=>H1.
- apply: val_ret=>/=_; move/eqP: X=>X; subst p.
  move/validL: (V1)=>V3; case:(lseq_null V3 H1)=>Z1 Z2; subst xs1 h1=>/=.
  by rewrite unitL. 
case/negbT /(lseq_pos) /(_ H1): X=>x[next][h'][Exs]Z H3; subst h1.
heval; rewrite -!joinA -!(joinCA h'); apply: (gh_ex (behead xs1, x::xs2)).
apply: val_doR=>//=[V2|].
 - exists h', (p :-> x \+ (p .+ 1 :-> p1 \+ h2)); split=>//; split=>//.
   by exists p1, h2; rewrite !joinA.
by move=> z m H4 _; rewrite Exs rev_cons cat_rcons.
Qed.

Next Obligation.
apply: ghR=>i xs H V /=; apply: (gh_ex (xs, [::])).
apply: val_doR=>//=[_|]; first by exists i, Unit; rewrite unitR. 
by rewrite cats0.
Qed.
(* end hide *)

(** %\end{exercise}% *)


(* begin hide *)
End HTT.
(* end hide *)
