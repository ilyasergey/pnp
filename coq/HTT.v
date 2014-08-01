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
us see a proof sketch of the above stated specification.

%
\begin{alltt}
\(\spec{x = a \wedge y = b}\) 
  t := \var{x}; 
\(\spec{x = a \wedge y = b \wedge t = a} \text{\texttt{by \Rule{Assign} and equality}} \) 
  \var{x} := \var{y}; 
\(\spec{x = b \wedge y = b \wedge t = a} \text{\texttt{by \Rule{Assign} and equality}} \) 
  \var{y} := t 
\(\spec{x = b \wedge y = a} \text{\texttt{by \Rule{Assign} equality and weakening via \Rule{Conseq}}}\)
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
\(\spec{x \mapsto - \wedge y \mapsto Y}\) \var{x} ::= 5 \(\spec{ x \mapsto 3 \wedge y \mapsto Y }\)
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
O'Hearn, Samin Ishtiaq and Hongseok Yang suggested an alternative way
to state assertions 

TODO






Main motto: logic about heaps and aliasing (a an b can in fact point
to the same thing)

TODO: example -- returning value of a pointer

** Selected rules of Separation Logic

** On loops and recursive functions

** Verifying heap-manipulating programs

* Monads in functional programming

** IO monad

** State monad

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