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
  | true  => false
  | false => true
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
 | 0     => m   
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
similar to [my_plus]. When defining the types [unit] or [empty], we
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
[nat_rec], which is a _higher-order_ function with the following type:

*)

Check nat_rec.
(** 
[[
nat_rec : forall P : nat -> Set,
          P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
]]

The type of [nat_rec] requires a bit of explanation. It is a
polymorphic in the sence of Haskell and OCaml (i.e., it is parametrize
over another type). More precisely, its first parameter, bound by the
[forall] quantifier is a function, which maps natural numbers to types
(hence the typo if this parameter is [nat -> Set]). The second
parameter is a result of type described by application of the function
[P] to zero. The third parameter is a _family_ of functions, indexed
by a natural number [n]. Each function from such a family takes an
argument of type [P n] and returns a result of type [P n.+1]. The
default recursion principle for natural numbers is therefore a
higher-order function (i.e., a combinator). If the three discussed
arguments are provided, the result of [nat_rec] will be a function,
mapping a natural number [n] to a value of type [P n].

To see how [nat_rec] is implemented, let us explore its generalized
version, [nat_rect]:

*)

Print nat_rect.
(** 
[[
nat_rect = 
fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P n.+1) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | n0.+1 => f0 n0 (F n0)
  end
     : forall P : nat -> Type,
       P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
]]

Abstracting away from the details, we can see that [nat_rect] is
indeed a function with three parameters (the keyword [fun] is similar
the lambda notation and is common in the family of ML-like languages).
The body of [nat_rect] is implemented as a recursive function (defined
via the keyword [fix]) taking an argument [n] of type
[nat]. Internally, it proceeds similaly to our implementation of
[my_plus]: if the argument [n] is zero, then the "default" value [f] of
type [P 0] is returned. Otherwise, the function proceeds recursively
with a smaller argument [n0] by applying the "step" function [f0] to
the [n0] and the result of recursive call [F n0].

Therefore, the summing function can be implemented via the [nat]'s
recursion combinator as follows:
*)

Definition my_plus1 n m := nat_rec (fun _ => nat) m (fun n' m' => m'.+1) n.

Eval compute in my_plus1 16 12.

(** 
[  = 28 : (fun _ : nat => nat) 16]

The result of invoking [my_plus1] is expectable. Notice, however, that
when defining it we didn't have to use the keyword [Fixpoint] (or,
equivalently, [fix]), since all recursion has been "sealed" within the
definition of the combinator [nat_rect].

** A note on dependent pattern matching

An important thing to notice is the fact that the type of [P] in the
definition of [nat_rec] is a function that maps _values_ of type [nat]
into arbitrary types. This gives us a possibility to define
_dependently-typed_ functions, whose return type depends on their
input argument value. A simple example of such a function is below:

*)

Definition three_to_unit n := 
 let: P := (fun n => if n is 3 then unit else nat) in
 nat_rec P 0 (fun n' _ => match n' return P n'.+1 with
               | 2 => tt
               | _ => n'.+1
               end) n.

Eval compute in three_to_unit 0.
(** [  = 0 : nat] *)
Eval compute in three_to_unit 5.
(** [  = 5 : nat] *)
Eval compute in three_to_unit 3.
(** [  = tt : unit] *)

(** 

The toy function [three_to_unit] maps every natural number to itself
except for [3], which is being mapped into the value [tt] of type
[unit]. We define it via the [nat_rec] combinator by providing it a
function [P], which defines the type contract described just above.
Importantly, as the first parameter.  The "step" function, which is a
third parameter, of this [nat_rec] call, makes use of the _dependent_
pattern matching, which now specifies explicit return type [P (n'.+1)]
of the whole [match ... with ... end] expression. This small addition
allows the Coq type checker to relate the expected type of the final
result [P n] to the result of the pattern matching expression. Without
the explicit [return] in the patternt matching, in some cases when its
result type depends on the value of the scrutinee, the Coq type
checking engine will fail to unify the type of the branch and the
overall type.%\footnote{However, in this example Coq 8.4 does just
fine even without the \texttt{return} annotation, we nevertheless
presented it to outline the possible problem.}%

In general, dependent pattern matching is quite powerful tool, which,
however, should be used with a great caution, as it makes assisting
Coq type checker to be a rather non-trivial task. In the was majority
of the cases dependent pattern matching can be avoided. We address the
curious reader to the Chapter 8 of Adam Chlipala's book for more
examples on the subject%~\cite{Chlipala:BOOK}%.

*)

(** * More datatypes 

While programming with natural numbers is fun, it is time for us to
take a brief look at other datatypes familiar from functional
programming, as they appear in Coq.


The type of pairs is parametrized by two arbitrary types [A] and
[B] (by now let us think of its sort [Type] as of a generalization of
a generalization of [Set], which we have seen before). As in Haskell
or OCaml, [prod] can also be seen as a type-level constructor with two
parameters that can be possibly curried:
*)

Check prod.
(**
[ prod : Type -> Type -> Type]

Pairs in Coq are defined as a higher-order datatype [prod] with just
one constructor [pair]:

*)
Print prod.
(** 
[[
Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B

For pair: Arguments A, B are implicit and maximally inserted
For prod: Argument scopes are [type_scope type_scope]
For pair: Argument scopes are [type_scope type_scope _ _]
]]

The display above, besides showing how [prod] is defined, specifies
that the type arguments of [prod] are _implicit_, in the sence that
they will be inferred by the type-checker when enough information is
provided, e.g., the arguments of the constructor [pair] are
instantiated with particular values. For instance, type arguments can
be omitted in the following expression: *)

Check pair 1 tt.

(** 
[ (1, tt) : nat * unit]

If one wants to explicitly specify the type arguments of a
constructor, the [@]-prefixed notation can be used:

*)

Check @pair nat unit 1 tt.

(** 
[ (1, tt) : nat * unit]

Notice that the parameters of the datatype come first in the order
they are declared, followed by the arguments of the constructor (often
also referred to as _indices_).

The last two lines following the definition of [prod] specify that the
notation for pairs is overloaded (in particular, the "[_ * _]"
notation is also used by Coq to denote the multiplication of natural
numbers), so it is given a specific _interpretation scope_. That is,
when the expression [nat * unit] will appear in the type position, it
will be interpreted as a type [pair nat unit] rather than like an
(erroneous) attempt to "multiply" two types as they were integers. 

Coq comes with a number of functions for manipulating datatypes, such
as pair. For instance, the first and second components of a pair:
*)

Check fst.
(**
[fst : forall A B : Type, A * B -> A]
*)

Check snd.
(**
[fst : forall A B : Type, A * B -> A]

Curiously, the notation "[_ * _]" is not hard-coded into Coq, but
rather is defined as a lightweight syntactic sugar on top of standard
Coq syntax. Very soon we will see how one can easily extend Coq's
syntax by defining their own notations. We will also see how is it
possible to find what a particular notation means.

The arsenal of a functional programmer in Coq would be incomplete
without proper sum and list datatypes:
*)

Print sum.
(**
[Inductive sum (A B : Type) : Type :=  inl : A -> A + B | inr : B -> A + B]
*)

Print list.

(** 
[Inductive list (A : Type) : Type := nil : list A | cons : A -> list A -> list A]
*)

(** * Searching for definitions and notations

Of course, we could keep enumerating datatypes and operations on them
from the standard Coq/SSReflect library (which is quite large), but
it's always better for a starting Coq hacker to have a way to find
necessary definitions on her own. Fortunately, Coq provides a very
powerful search tool, whose capabilities are greatly amplified by
SSReflect. Its use is better demonstrated by examples.

*)

Search "filt".
(** 
[[
List.filter  forall A : Type, (A -> bool) -> list A -> list A
List.filter_In
   forall (A : Type) (f : A -> bool) (x : A) (l : list A),
   List.In x (List.filter f l) <-> List.In x l /\ f x = true
]]
*)

Search "filt" (_ -> list _).
(** 
[[
List.filter  forall A : Type, (A -> bool) -> list A -> list A
]]

That is, the first [Search] query just takes a string and looks for
definitions of functions and propositions that have it as a part of
their name. The second pattern elaborates the first by adding a
requirement that the type of the function should include [(_ -> list
_)] as a part of its return type, which narrows the search scope. As usual the
underscores [_] denote a wildcard in the pattern and can be used both
in the name or type component. Moreover, one can use named patterns of
the form [?id] to bind free identifiers in the sub-types of a sought
expression. For instance, the next query will list all function with
map-like types (notice how the higher-order constructor types are
abstracted over using wildcards):
*)

Search _ ((?X -> ?Y) -> _ ?X -> _ ?Y).
(**
[[
option_map  forall A B : Type, (A -> B) -> option A -> option B
List.map  forall A B : Type, (A -> B) -> list A -> list B
...
]]

If necessary, the type patterns in the query can have their types
explicitly specified in order to avoid ambiguities due to notation
overloading. For instance, the folowing search will return all
functions and propositions that make use of the [_ * _] notation and
operate with natural numbers: *)

Search _ (_ * _ : nat).

(** 

In contrast, the next query will only list the functions/propositions,
where [_ * _] is treated as a notation for the pair datatype
(including [fst] and [snd], which we have already seen):

*)

Search _ (_ * _: Type).

(**

A detailed explanation of the syntax of [Search] tool as well as
additional examples can be found in Chapter 10 of SSReflect
documentation%~\cite{Gontier-al:TR}%.

When working with someone's Coq development, sometimes it might be not
entirely obvious what particular notation means: Coq's extensible
parser is very simple to abuse by defining completely intractable
abbreviations, which might say a lot to the library developer, but not
to its client. Coq provide the [Locate] to help in demistifying
notations as well as locating the position of particular definitions.
For example, the following query will show all the definitions of the
notation "[_ + _]" as well as the scopes they defined in.

*)

Locate "_ + _".

(** 
[[
Notation            Scope     
"x + y" := sum x y   : type_scope
                      
"m + n" := addn m n  : nat_scope
                      (default interpretation)
...
]]

We can see now that the plsu-notation is used in particular for the
addition of natural nubmers (in [nat_scope]) and the declaration of a
sum type (in [type_scope]). Similarly to the notations, the [Locate]
command can help finding the definition in the source modules they
defined:%\footnote{The module system of Coq is similar to OCaml and
will be discussed further in this chapter.}% *)

Locate map.

(**
[[
Constant Coq.Lists.List.map
  (shorter name to refer to it in current context is List.map)
Constant Ssreflect.ssrfun.Option.map
  (shorter name to refer to it in current context is ssrfun.Option.map)
...
]]
*)

(** * An alternative way to define inductive datatypes

*)


Inductive prod1 (A B : Type) : Type :=  pair1 of A & B.
Implicit Arguments pair1 [A B].

Open Scope type_scope.


Check pair1 3 5.

(** * Modules and sections

 *)



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
