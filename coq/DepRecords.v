(** 
%
\chapter{Encoding Mathematical Structures}
\label{ch:depstruct}
% 
*)

(* begin hide *)
Module DepRecords.
(* end hide *)

(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing first %\texttt{{first}}% *)
(** printing last %\texttt{{last}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)


(**  

Long before programming has been established as a discipline,
matchematics became to be perceived as a science to build abstractions
and summarize important properties of various entities necessary for
describing nature's phenonemnons.%\footnote{In addition to being a
science of rewriting, as we have already covered in
Chapter~\ref{ch:eqrew}.}% From the basic course of algebra, we are
familiar with a number of mathematical structures, such as monoids,
groups, rings, fields etc., coupling a set (or a number of sets), a
number of operations on it (them), and a collection of properties of
the set itself and operations on them. 

From a working programmer's perspective, a notion of an mathematical
abstract structure is reminiscent to a notion of class from
object-oriented programming, modules from Standard ML and type classes
%\index{type classes}\index{Haskell}% from Haskell: all these
mechanisms are targeted to solve the same goal: _package_ a number of
operations operationg on some data, while abstracting of a particular
implementation of this data itself. What neither of these programming
mechanisms is capable of doing is enforcing the requirement for one to
provide the _proofs_ of properties, which restrict the operations on
the data structure. For insnace, one can implement a type class for a
_lattice_ in Haskell as follows:

<<
class Lattice a where
  bot :: a
  top :: a
  pre :: a -> a -> Bool
  lub :: a -> a -> a
  glb :: a -> a -> a
>>

That is, the class %\texttt{Lattice}% is parametrized by a _carrier_
type %\texttt{a}%, and provides the abstract interfaces for top and
bottom elements of the lattice, as well as for the ordering predicate
%\texttt{pre}% and the binary _least-upper-bound_ and
_greates-low-bound_ operations. What this class cannot capture is the
restriction on the operation that, for instance, the %\texttt{pre}%
relation should be transitive, reflexive and antisymmetric. That said,
one can instantiate the %\texttt{Lattice}% class, e.g., for integers,
%\index{lattice}% providing an implementation of %\texttt{pre}%, which
is _not_ a partial order (e.g., just constant %\texttt{true}%). While
this relaxed approach is supposedly fine for the programming needs, as
the type classes are used solely for computing, not the reasoning
about the correctness of the computations, this is certainly not
satisfactory from the mathematical perspective. Whithout the
possibility to establish and enforse the necessary properties of a
mathematical structure's operation, we would not be able to carry out
any sort of sound formal reasoning, as we simply could not distinguis
a "correct" implementation from a flawed one.

Luckily, Coq's ability to work with dependent types and combine
programs and propositions about them in the same language, as we've
already witnessed in the previous chapters, makes it possible to
define mathematical structures with a necessary degree of rigour and
describe their properties precisely by means of stating them as
_types_ (i.e., propositions) of the appropriate implementation's
parameters. Therefore, any faithful instance of an abstract
mathematical structure implemented this way, would be enforced to
provide not just the _carrier_ and implementations of the declared
operations but also _proofs_ of propositions that constrain these
operations and the carrier.

In this chapter we will learn how to encode the reasoning about common
algebraic data structures in Coq in a way very similar to how data
structures are encoded in languages like C (with a bit of Haskell's
type class-like machinery). In the process, we will meet some old
friends from the course of abstract algebra: partial commutative
monoids, and implement them using Coq's native constructs: dependent
records and canonical structures.

As usual, we will require a number of SSReflect package imported.

*)

Require Import ssreflect ssrbool ssrnat eqtype ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** 

* Encoding partial commutative monoids

TODO: describe what a PCM is

%\index{partial commutative monoid}%
%\index{PCM|see {partial commutative monoid}}%


** Describing basic structure via mixins

TODO: recall sigma-types




%\index{mixins}%


%\ccom{Record}%
*)

Record mixin_of (T : Type) := Mixin {
    valid_op : T -> bool;
    join_op : T -> T -> T;
    unit_op : T;
    _ : commutative join_op;
    _ : associative join_op;
    _ : left_id unit_op join_op;
    _ : forall x y, valid_op (join_op x y) -> valid_op x; 
    _ : valid_op unit_op }.

(**

We can now prove a number of facts about the structure, very much in
the spirit of the facts that re being proven in the algebra course.
For instance, the following lemma states that [unit_op] is alse the
_right unit_. %\index{right unit}%

*)

Lemma r_unit T (pcm: mixin_of T) (t: T) : (join_op pcm t (unit_op pcm)) = t.
Proof.
case: pcm=>_ join unit Hc _ Hlu _ _ /=.

(** 
[[
  T : Type
  t : T
  jo : T -> T -> T
  uo : T
  Hc : commutative jo
  Hlu : left_id uo jo
  ============================
   jo t uo = t
]]

*)

by rewrite Hc Hlu.
Qed.

(** TODO: emphasize the [:>] coercion *)
Structure pack_type : Type := Pack {sort :> Type; _ : mixin_of sort; _ : Type}.


(**

TODO

** Packaging the structure


*)

Section Blah.
Variables (T : Type) (cT : pack_type).
Definition class : mixin_of cT := let: Pack _ c _ as cT' := cT return mixin_of cT' in c.

Check class.

Definition pack c := @Pack T c T.

Definition valid := valid_op class.
Definition join := join_op class.
Definition unit := unit_op class.
End Blah.

Print join.

(**

Here, we define the monoids and prove a number of properties about
them. We will take natural numbers and lists as instances.

** Implementing inheritance hierarchies via telescopes
%\index{telescopes}%

TODO: notice that no multiple inheritance is possible (easily)

*)

(** 

* Properties of partial commutative monoids 


*)

Notation "x \+ y" := (join x y) (at level 43, left associativity).

Section Tada.
Definition pcm := pack_type.
Variable U V : pcm.

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof. by case: U x y=>tp [v j z Cj *]; apply: Cj. Qed.
End Tada.


(** * Introducing canonical structures  

TODO: show first definition withou equality.

%\ccom{Canonical}%

** Defining arbitrary PCM instances with overloaded operations

*)

Definition natPCMMixin := 
  Mixin addnC addnA add0n (fun x y => @id true) (erefl _).
Canonical natPCM := Eval hnf in pack natPCMMixin.

Variables a b: nat.

(** 

TODO: can I use [+] here instead of [\+] ?

*)

Goal a \+ b = a \+ b.
by rewrite joinC.
Qed.


(**

** Types with computable equalities

*)



(**

* Summary of encoding patterns


We recommend the interested authors to take a look at Chapter 1 of
%Fran\c{c}ois% Garillot's PhD dissertation for more examples of
mathematical data structure encoding in Coq/SSReflect%~\cite{Garillot:PhD}%. 

More examples in%~\cite{Garillot-al:TPHOL09}%.

*)


(* begin hide *)
End DepRecords.
(* end hide *)
