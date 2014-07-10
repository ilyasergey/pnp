(** %\chapter{Functional Programming in Coq}% *)

(** 

We start our short journey with observing the capabilities of Coq as
programming language. 

Coq is often described as a functional programming language, since its
programs are always pure, possibly higher-order functions, which means
that they might take other functions as parameters and return
functions as results. Similarly to other functional programming
languages, such as Haskell, OCaml or Scala, Coq makes heavy use of
algebraic datatypes, represented by a number of possibly recursive
constructors. 

Very soon, we will see how programming with inductive algebraic data
types incorporates reasoning about definitions, but for now let us
take a short tour of Coq's syntax and define a couple of simple
programs.

*)

(** * Enumeration datatypes *)

(** 

The simplest datatype once can imagine is [unit], a type
inhabited by exactly one element. In Coq, one can define such a type
in the following manner: 

*)

Inductive unit : Set := tt.

(** 

The definition above postulates the type [unit] that has _exactly_ one
constructor, namely, [tt]. In the type theory jargon, which we will
adopt, it is said that the expression [tt] _inhabits_ the [unit]
type. Naturally, it is the only inhabitant of the set, corresponding
to the [unit] type. We can now check the [tt]'s affiliation via the
[Check] command:

*)

Check tt.

(**
Moreover, we can make sure that the [unit] datatype itself defines a set:
*)

Check unit.

(**

In fact, since Coq makes the analogy between sets and types so
transparent, it is not difficult to define a type, describing the
_empty_ set:

*)

Inductive empty : Set := .

(**

That is the empty set is precisely described by the type, values of
which we simply _cannot construct_, as the type iteslf does _not_
provide any constructors! 
In fact, this observation about inhabitance of types/sets and the
definition of an empty type will come in quite handy very soon when we
will be talking about the truth and falsehood in the setting of
Curry-Howard correspondnce.
Unfortunately, at this moment there is not so much we can do with such simple types as [unit] or
[empty], so we procced by defining some more interesting datatypes.

The type [bool] is familiar to every programmer. In Coq, it is
unsurprisingly defined by providing exactly two constructors: [true]
and [false]. Since [bool] is already provided by the standard
Coq/SSReflect library, we do not need to define it ourselves. Instead,
we include the following modules into our file using the [Require
Import] keywords:

*)

Require Import ssreflect ssrbool.

(** Now, we can inspect the definition of the [bool] type by simply
printing it: *)

Print bool.
(** [Inductive bool : Set :=  true : bool | false : bool] *)

(** 

Let us now try to define some functions that operate with the bool
datatype ignoring for a moment the fact that most of them, if not all,
are already defined in the standard Coq/SSReflect library.  Our first
function will simply negate the boolean value and return its opposite:

*)

Definition negate b := 
  match b with 
    true  => false
  | flase => true
  end.

(**

The syntax of Coq as programming language is very similar to Standard
ML. The keyword [Definition] us used to define non-reqursive values,
including functions. In the example above, we defined a function with
one argument [b], which is being scrutinized agains two possibles
value patterns ([true] and [false]), respectively, and the results are
returned. Notice that thanks to its very powerful type inference
algorithm, Coq didn't require us to annotate neither the argument [b]
with its type, nor the function itself with its result type: these
types were soundly inferred, which might be confirmed by checking the
overall type of [negate], which states that it is a function from
[bool] to [bool]:

*)

Check negate.
(**
[negate : bool -> bool
]

* Simple recursive datatypes and programs

At this point we have seen only very simple forms of inductive types,
such that all their inhabitants are explicitly enumerated (e.g.,
[unit] and [bool]). The next type used ubiquitously in the
computations and mathematical resoning are natural numbers, the first
_truly_ inductive datatype. Following the Peano axioms the type [nat]
natural numbers are defined by induction, i.e., via the following two
constructors: *)

Print nat.

(**
[Inductive nat : Set :=  O : nat | S : nat -> nat]

The definition of the type [nat] is _recursive_.  It postulates that
[O] is a natural number (hence, the first constructor), and, if [n] is
a natural number then [S n] is a natural number as well (hence, the
name [S], which is a shortcut for _successor_). At this point, the
reader can recall the notion of _mathematical induction_, usually
introduced in school and postulating that if a statement [P] has to be
proven to hold over all natural numbers, it should be proven to hold
on zero _and_ if it holds for [n], then it should hold for [n +
1]. The very same principle is put into the definition of the natural
numbers themselves. In the future, we will see many other interesting
data structures going far beyond natural numbers and each equipped
with its own _induction principle_.  Moreover, quite soon we will see
that in Coq recursive definitions/computations and inductive proofs
are in fact two sides of the same coin.

For now, let us write some functions dealing with natural numbers.  In
order to work conveniently with naturals, we will import yet another
SSReflect library: *)

Require Import ssrnat.

(** 

Probably, the most basic function working on natural numbers is their
addition. Even though such function is already implemented in the vast
majority of the programming languages (including Coq), let us do it
from scratch using the defitinon of [nat] from above. Since [nat] is a
recursive type, the addition of two natural numbers [n] and [m] should
be defined recursively as well. In Coq, recursive functions are
defined via the keyword [Fixpoint]. In the following definition of the
[my_plus] function, we will make use of SSReflect's infix notation
[.+1] (with no spaces between the characters) as an alternative to the
standard [nat]'s recursive constructor [S].  Also, Coq provides a
convinient notation [0] to the _zero_ constructor [O].

*)

Fixpoint my_plus n m := 
 match n with 
   0     => m   
 | n'.+1 => let: tmp := my_plus n' m in tmp.+1
 end.

(** 

Here, we deliberately used less concise notation in order to
demonstrate the syntax [let: ... := ... in ...] construct, which,
similarly to Haskell and OCaml allows, one to bind intermediate
computations within expressions.%\footnote{The same example also
demonstrates the use of SSReflect alternative to Coq's standard
\texttt{let} command, not trailed with a colon. We will be making use
of SSReflect's \texttt{let:} consistently, as it provides additional
benefits with respect to in-place pattern matchin, which we will show
further.}% The function [my_plus] is recursive on its _first_
argument, which is being decreased in the body, so [n'] is a
predecessor of [n] is passed to the recursive call. We can now check
the result of evaluation of [my_plus] via Coq's [Eval compute in]
command:%\footnote{The command in evaluation might look a bit verbose
in this form, but it is only because of its great flexibility, as it
allows for different evaluation strategies. In this case we employed
\texttt{compute}, as it performs all possible reductions.}%

*)

Eval compute in my_plus 5 7. 
(** 
[ = 12 : nat] 

The same function could be written quite a bit shorter via SSReflect's
pattern-matching [if-is]-notation, which is a convenient alternative
to pattern matching with only two alternatives:

*)

Fixpoint my_plus' n m := if n is n'.+1 then (my_plus n' m).+1 else m.

(**

At this point, the reader might have an impression that the
computational language of Coq is the same as of OCaml and Haskell, so
all usual tricks from the functional programming might be directly
applicable. Unfortunately, it is not so, and the main difference
between Coq and other general-purpose programming languages stems from
the way it treats recursion. For instance, let us try to define the
following "buggy" addition function, which goes into an infinite
recursion instead of producing the value, due to the fact that the
recursion argument is not decreasing and remains to be [n]:

[Fixpoint my_plus_buggy n m := if n is n'.+1 then (my_plus_buggy n m).+1 else m.]

we immediately get the following error out of the Coq interpreter:

[Error: Cannot guess decreasing argument of fix.]

This is due to the fact that the recursion in [my_plus_buggy] is not
_primitive_: that is there is a recursive call, whose argument is not
"smaller" comparing to the initial function's argument, which makes
this procedure to fall into a larger class of _generally recursive_
programs. Unlike primitively-recursive programs, generally-recursive
programs may not terminate or terminate only on a subset of their
inputs, and checking termination statically in general is an
undecidable problem (that is, such checking will not terminate by
itself, which is known under the name of Turing's _halting
problem_).%\footnote{The computability properties of primitively and
generally recursive functions is a large topic, which is essentially
orthogonal to our development, so we omit a detailed discussion on the
theory of recursion and address an interested reader to the literature~\cite{???}}%

The check for primitive recursion, which implies termination, is
performed by Coq _syntactically_, and the system makes sure that there
is least one argument of an inductively-defined datatype, which is
being consistently decreased at each function call. This criteria is
sufficient to insure the termination of all functions in Coq. Of
course, such termination check is a severe restriction to the
computation power of Coq, which therefore is not Turing-complete as a
programming language (as it supports only primitive recursion).

Although Coq is equipped with a number of machinery to _reason_ about
potentially non-terminating programs and prove some usefult facts
about them%\footnote{Typically, this is done by supplying a
user-specific termination argument, which "strictly reduces" at each
function call, or defining a function, so it would take a
\emph{co-inductive} datatype as its argument.}% (for example, Chapter
7 of Adam Chlipala's book%~\cite{Chlipala:BOOK}% provides a broad
overview of methods to encode potentially non-terminating programs in
Coq and reason about them), it usually requires some ingenuity to
execute generally-recursive computations withit Coq. Fortunatelly,
even without the possibility to _execute_ any possible program in the
system, Coq provides a reach tool-set to _encode_ such programs, so a
number of statements could be proved about them, and the encoded
programs themselves could be later _extracted_ into a general-purpose
language, such as Haskell or OCaml in order to be executed
(see%~\cite[Chapter 10]{Bertot-Casteran:BOOK}% for detailed
description of the extraction).

So, why ensuring termination in Coq is so important? The reason for
this will be better understood once we introduce the way Coq works
with logical statements and propositions. For now, it should be enough
to accept the fact that in order to ensure the logical calculus
underlying Coq sound, all values in it (even possibly infinite,
e.g., streams defined co-inductively) should be computable in a
finite number of steps. A bit further we will see that the proofs of
propositions in Coq are just ordinary values in its computational
language, and the construction of the proofs naturally should
terminate, hence computation of _any_ value in Coq should terminate,
since each value can be involved into a proof of some statement.

Postponing the discussion on the nature of propositions and proofs in
Coq, we will continue our overview of programming principles in Coq.

With the example of the addition function, we have already seen how
the recursive functions are defined. However, using the [Fixpoint]
command is not the only way to provide definitions to functions
similar to [my_sum]. When defining the types [unit] or [empty], we
could have noticed the following output produced by the interactive
interpreter:
[[
unit is defined
unit_rect is defined
unit_ind is defined
unit_rec is defined
]]
These three lines indicate that along with the new datatype ([unit] in
this case) three additional entities have been generated by the
system. These are the companion _induction_ and _recursion_
principles, which are named using the simple convention basing on the
name of the datatype. For example, the [nat] datatype comes
accompannied by [nat_rect], [nat_ind] and [nat_rec], correspondingly.

Continuing playing with natural numbers and leaving the [nat_rect] and
[nat_ind] aside for a moment, we focus on the recurision primitive
[nat_rec], which is a _higher-order_ function with the following type

*)

Check nat_rec.
(** 
[[
nat_rec : forall P : nat -> Set,
          P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
]]

The type of [nat_rec] requires a bit of explanation. 

TODO
*)



(** * More datatypes *)



(* Fixpoint is_even n :=  *)
(*  match n with  *)
(*   | 0  => true *)
(*   | 1  => false *)
(*   | n'.+2  => is_even n' *)
(*  end.  *)

(* Check nat_rec. *)

(* Definition is_even' := nat_rec (fun _ => bool) true (fun _ => negate).  *)

(* Eval compute in is_even' 140. *)


(* Check list_rec. *)

(* Program Definition sum (l: seq nat): nat :=  *)
(*   list_rec (fun _ => nat) 0 (fun x l res => x + res) l. *)

(* Definition my_list := 1 :: 2 :: 3 :: nil. *)

(* Eval compute in sum my_list. *)



(* Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path. *)






(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

(* Inductive isZero n : Prop := IsZero of (n = 0) & (n = 1). *)


(* Theorem blah: forall n, isZero n -> False. *)
(* move=> n. case. *)
(* move=>->.  *)

(* Theorem isZero_contra : isZero 1 -> False. *)
(* Proof. *)
(* case.  *)
(* have X1: if 0 == 1 then False else True by case Y: (0 == 1)=>//.  *)
(* by rewrite eq_sym=>X; rewrite X in X1. *)



(* case Y: (0 == 1)=>//. *)
(* have Z: isZero 1 -> 0 == 1. *)


(* by rewrite Y in X1 =>/=. *)

(*    move=> Z; rewrite -Z in X1. *)
