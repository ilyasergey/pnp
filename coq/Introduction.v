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

Unlike other courses on machine-assisted theorem proving in Coq, these
notes focus on _computational_ nature of inductive reasoning, which
makes it possible to compute a vast majority of the desired results,
given that they are formulated as computable properties, rather than
inductive predicates, which is the spirit of the traditional Coq school. 

In this course, we rely on the SSReflect extension of Coq, as a tool,
which takes the computational reasoning to the whole new level by
means of employing _small-scale reflection_ when it comes to reasoning
about computable properties, which therefore can be considered as
terminating functions, returning [true] or [false].

%\emph{(Ilya: more to be said here.)}%

** What this course is about

More specifically, these notes focus on the following concepts and
topics, to the best of our knowledge, not covered in other course on Coq:

  - Structuring the reasoning with a small but complete set of
    tactics: [move], [elim], [case], [have], [apply], [set], [rewrite]
    and [congr].

  - Explaining the essentials of boolean reflection and relation
    between the type [bool] and the sort [Prop];

  - Leveraging inductive type's _parameters_ as an alternative to
    _indices_ by means of reasoning about explicit equalities;

  - Using datatype indices as a tool to define conditional rewriting
    rules;

  - Formulating familiar mathematical structures (e.g., monoids and
    lattices) by means of Coq's dependent records;

  - Reducing the clutter when reasoning with the mathematical
    structures be means of employing Coq's _canonical constructions_;

  - Explaining the basics of type-based reasoning about imperative
    programs, introducing the readers to the concepts of Hoare Type
    Theory.

** What this course is not about

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
