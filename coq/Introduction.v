(** %\chapter{Introduction}% *)

(**

The goal of this short course is to demonstrate how mathematical
reasoning can benefit from the recent advances in computer science and. 

In particular, we are demonstrating how the concepts familiar from the
mainstream programming languages and employed in everyday programming
practice provide illuminating insights about the nature of reasoning
in constructive logic and make it possible to reduce the burden of mechanical theorem
proving.

%\emph{Ilya: I'm planning to expand this section further by providing
 more historical background to strengthen the motivation.}%

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

 *)

(**

* Setup

TODO

** Building Coq from sources

TODO

** Emacs set-up

TODO

** Installing and using SSReflect

TODO

*)