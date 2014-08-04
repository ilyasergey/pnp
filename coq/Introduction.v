(** %

\chapter{Introduction}% *)

(* begin hide *)
Module Intro.
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
(** printing :-> %\texttt{:->}% *)
(** printing <-- $\mathtt{<--}$ *)
(** printing vfun %\texttt{\emph{vfun}}% *)
(** printing do %\texttt{{do}}% *)
(** printing putStrLn %\texttt{\emph{putStrLn}}% *)
(** printing getChar %\texttt{\emph{getChar}}% *)
(** printing heval %\textsf{\emph{heval}}% *)

(**

These lecture notes offer a brief and comprehensive introduction to
the basic concepts of mechanized reasoning and interactive theorem
proving using the Coq proof assistant.

The primary audience of this text are the readers with solid
background in software development and programming and a knowledge of
mathematic disciplines on the level of an undergraduate university
program. The high-level goal of the course, thus, is to demonstrate
how much the rigorous mathematical reasoning and development of robust
and intellectually manageable programs have in common, and how
understanding of common programming language concepts provides a solid
background for building mathematical abstractions and proving theorems
formally. The low-level goal of this course is to provide an overview
of the Coq proof assistant, taken in its both incarnations: as an
expressive functional programming language with dependent types and as
a proof assistant providing support for mechanized interactive theorem
proving.

By aiming these these two goals, this manuscript, thus is intended to
provide a demonstration how the concepts familiar from the mainstream
programming languages and employed in as parts of good programming
practices can provide illuminating insights about the nature of
reasoning in Coq's logical foundations and make it possible to reduce
the burden of mechanical theorem proving. These insighsts will
eventually give the reader a freedom to focus solely on the
_essential_ part of the formal development instead of fighting with a
proof assistant in futile attempts to encode the "obvious"
mathematical intuition---a reason that made many of the new-comers
abandon their attempts to apply the machine-assisted appropach for
formal reasoning as an everyday practice.

* Why yet another course on Coq?

The Coq proof assistant%~\cite{Coq-manual}% has been developed since
1983, and by now there is a number of courses that provide excellent
introductions into Coq-powered interactive theorem proving and
software development. Among the others publicly available manuscripts,
the author finds the following three to be the most suitable for
teaching purposes.

- The classical book _Interactive Theorem Proving and Program
  Development. Coq'Art: The Calculus of Inductive Constructions_ by
  Yves Bertot and Pierre %Cast\'{e}ran~\cite{Bertot-Casteran:BOOK}% is
  a great and exhaustive overview of Coq as formal system and a tool,
  covering both logical foundations, reasoning methodologies,
  automation tools and offering large number of examples and exercises
  (from which this course borrows some).

- Benjamin Pierce et al.'s _Software Foundations_ electronic
  book%~\cite{Pierce-al:SF}% introduces Coq development from an angle
  of the basic research in programming language, focusing on
  formalization of program language semantics and type systems, which
  serve both as main motivating examples of Coq usage and a source of
  intuition for explaining Coq's logical foundations.

- The most recent book, _Certified Programming with Dependent Types_
  by Adam Chlipala%~\cite{Chlipala:BOOK}% provides a gentle
  introduction to Coq from the perspective of writing programs that
  manipulate with _certificates_, i.e., first-class proofs of the
  program's correctness. The idea of certified programming is a
  natural fit for a programming language with dependent types, which
  Coq offers, and the book is structured as a series of examples that
  make the dependently-typed aspect of Coq shine along with intuition
  behind these examples and an exhaustive overview of state of the art
  _proof automation_ techniques.

Although all the three books have been used in numerous introductory
courses for Coq with a large success, it is the author's opinion that
there are still some topics essential for grasping the intuition
behind rigorous and boilerplate-free mathematical reasoning via a
proof assistant that are left underrepresented, and this is a gap,
which this course is targeted to fill, while giving the reader enough
background to proceed as a Coq hacker on her own. In particular, this
manuscript describes in detail the following aspects of proof
engineering, most of which are enabled or empowered by Georges
Gonthier et al.'s _small-scale reflection_ extension (SSReflect) to
Coq%~\cite{Gontier-al:TR}%.

- Special treatment is given to the _computational_ nature of
  inductive reasoning of decidable propositions, which makes it
  possible to _compute_ a vast majority of them (as opposed to prove
  them constructively), given that they are formulated as computable
  recursive Coq functions, rather than inductive predicates (which is
  more the spirit of the traditional Coq school).

- Instead of supplying the reader with a large vocabulary of tactics
  necessary for everyday Coq hacking, this course focuses on a _very
  small_ but powerful and _complete_ set (about a dozen) of proof
  constructing primitives, supplied by SSReflect or inherited from
  the vanilla Coq with notable enhancements.

- Advocating inductive types' _parameters_ as an alternative to
  _indices_ as a way of reasoning about explicit equalities.

- Presenting the reasoning by rewriting from the perspective of Coq's
  definition of propositional equality and elaborating on the idea of
  using _datatype indices_ as a tool to define client-specific
  conditional _rewriting rules_.

- Explaining the essentials of SSReflect's _boolean reflection_
  between the sort [Prop] and the datatype [bool] as a particular case
  of conditional rewriting, following the spirit of the computational
  approach to the proofs of decidable propositions.

- Formulating familiar mathematical structures (e.g., monoids and
  lattices) by means of Coq's _dependent records_ and overloading
  mathematical operations using the mechanism of _canonical instances_.

- Explaining the basics of type-based reasoning about imperative
  programs by means of _shallow embedding_, introducing the readers
  to the concepts of Hoare Type Theory.

** What this course is about

Besides the enumerated above list of topics, which are described in
detail and supported by a number of examples, this course supplies som
amount of "standard" material, necessary to introduce a reader with a
background in programming and classical mathematical disciplines to
proof engineering and program development in Coq. It starts from
explaining how simple functional programs can be written in the
programming environment of Coq, proceeding to the definition of
propositional logic connectives and elements of interactive proof
construction. Building further on the programming intuitions of
algebraic datatype definitions, this manuscript introduces the
definition equality and the way to encode custom rewriting rules,
which the culminates with a discussion on the boolean reflection and
reasoning by means of computation. This discussion is continued by
revising important principles of reasoning by induction in Coq and
providing pointers to the standard SSReflect libraries, which should
be used as a main component for basic mathematical reasoning. The
course concludes by reconciling all of the described concepts and
Coq/SSReflect reasoning principles by tacking a large case
study---verifying imperative programs within the framework of Nanevski
et al.'s Hoare Type
Theory%~\cite{Nanevski-al:ICFP06,Nanevski-al:JFP08}%.

** What this course is not about

TODO

** Why using SSReflect on top of Coq?

* Prerequisites

* Course overview and Setup

** Outline and contents

** Naming conventions

TODO: elaborate on difference between Vernacular, Gallina, Coq and CIC

TODO: explain different fonts used

** Installing Coq, SSReflect and HTT libaries

TODO

** Emacs set-up

TODO

* Accompanying files

*)

(* begin hide *)
End Intro.
(* end hide *)
