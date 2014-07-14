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
stems out of the ide of _Curry-Howard
Correspondence_.%\footnote{\url{http://en.wikipedia.org/wiki/Curry-Howard_correspondence}}%
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
known to be undecidable in general (and, therefore, there is no
automatic way to reduce an arbitrary second-order formula to [true] or
[false]).

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
polymorphic types (and, equivalently, first-order propositions),
%System~$F_{\omega}$% allows one to quantify as well over type
operators that can be seen as higher-order propositions.

* The truth and the falsehood in Coq

We start by showing how the two simplest propositions, the truth and
the falsehood, are encoded in Coq. Once again, let us remind that,
unlike in the Propositional Logic, in Coq these two are _not_ the only
possible propositional values, and we will see how a wide range of
propositions different from mere truth or falsehood can be encoded.


TODO: present the types of True and False here

*)


(** * Logical connectives 

TODO: Present conjunction and disjunction

*)


(** * Universal and existential quantification

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


(** * The basics of boolean reflection

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
