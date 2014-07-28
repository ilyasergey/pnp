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
object-oriented programming, modules from Standard ML and type
classes%~\cite{Wadler-Blott:POPL89}% %\index{type
classes}\index{Haskell}% from Haskell: all these mechanisms are
targeted to solve the same goal: _package_ a number of operations
operationg on some data, while abstracting of a particular
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

In this chapter we will learn how to encode common algebraic data
structures in Coq in a way very similar to how data structures are
encoded in languages like C (with a bit of Haskell's type class-like
machinery), so the represintation, unlike the one in C or Haskell,
would allow for flexible and generic reasoning about the structures'
properties. In the process, we will meet some old friends from the
course of abstract algebra: partial commutative monoids, and implement
them using Coq's native constructs: dependent records and canonical
structures.

As usual, we will require a number of SSReflect package imported.

*)

Require Import ssreflect ssrbool ssrnat eqtype ssrfun.

(** 

We will also require a number of commands, specific for SSReflect and
simplifying the handling of implicit datatype arguments.

%\ccom{Set Implicit Arguments}%
%\ccom{Unset Strict Implicit}%
%\ccom{Unset Printing Implicit}%

*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

* Encoding partial commutative monoids

We will be using partical commutative monoids (PCMs) as an
illustrative example of a simple algebraic data structure, a subject
of encoding and formalization.%\index{partial commutative monoid}
\index{PCM|see {partial commutative monoid}}% A PCM is defined as an
algebraic structure with a carrier set [U], abstract binary "join"
operation $\join$ and a unit element $\unit$.%\footnote{Sometimes also
referred to as an \emph{identity} or \emph{neutral}
element.}%%\index{unit element}% %\index{join operation}% The join
operation is required to be associative and commutative, and for the
unit element the left and right identity equalities should
hold. Moreover, partiality means that the operation $\join$ might be
undefined for some pairs of elements $a$ and [b] (and in this case it
is denoted as $a \join b = \bot$). PCMs are fairly ubiquitous: in
particular, natural numbers with addition and multiplication, sets
with a disjoin union, partially-defined functions with a point-wise
union, form PCM. Furthermore, partial commutative monoids are
omnipresent in program verification%~\cite{Nanevski-al:POPL10}%, as
they capture exactly the properties of _heaps_, as well as the effect
of programs that can be executed in
parallel%~\cite{Nanevski-al:ESOP14}%. Therefore, it is useful to have
PCMs formalized as a structure, so they could be employed for future
reasoning.

%\index{identity element|see {unit element}}%

** Describing algebraic data structures via dependent records

*)

Section PCMDef.

(**

In %Section~\ref{sec:exists} of Chapter~\ref{ch:logic}% we have
already seen a use of dependent pair type, exemlpified by the Coq's
definition of the universal quantification.

*)

Print ex.

(**
[[
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
]]

The only constructor [ex_intro] of the predicate [ex], whose type is a
dependent function type, is a way to encode a $\Sigma$-type of a
dependent pair, whose second component's type _depends_ on the value
of the first one.%\index{dependent pair}% More specifically, the
result of the existential quantification's encoding in Coq is a
dependendent pair $\Sigma x:A, (P x)$, such that the proposition in
the second component is determined by the value of the first component
[x].

Coq provides an alternative way to encode _iterated_ dependent pairs
via the mechanism of _dependent records_,%\index{dependent record}%
also allowing one to give names to the subsequent
components. Dependent records are defined using the [Record]
command. getting back to our PCM example, we illustrate the use of
dependent records below.

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
    _ : valid_op unit_op 
}.

(**

[[
mixin_of is defined
mixin_of_rect is defined
mixin_of_ind is defined
mixin_of_rec is defined
valid_op is defined
join_op is defined
unit_op is defined
]]


The syntax of Coq's dependent records is reminiscent to the one of
records in C. Following SSReflect's naming
pattern~\cite{Garillot-al:TPHOL09}, we call the record type (defined
in a dedicated section) [mixin_of] and its only constructor
[Mixin]. The reasons for such naming convention will be explained
soon, and for now let's discuss the definition. The PCM record type is
parametrized over the carrier type [T], which determines the carrier
set of a PCM. It then lists three _named_ fields. [join_op] describes
an implementation of the PCM's binary operation. [unit_op] defines the
unit element. Finally, the [valid_op] predicate determines whether a
particular element of the carrier set [T] is valid or not, and, thus,
serves as a way to express the partiality of the [join_op] operation
(the result is undefined, whenever the corresponding value of [T] is
non-valid). Next, the PCM record lists five unnamed PCM _properties_,
which should be satisfied whenever the recor is instantiated and are
defined using the standard propositions from SSReflect's [ssrfun]
%\ssrm{ssrfun}% module (see %Section~\ref{sec:funprops}%). In
particular, the PCM type definition requires the operation to be
[commutative] and [associative]. It also states that if $a \join b
\neq \bot$ then $a \neq \bot$ (the same statement about $b$ can be
proved by commutativity), and that the unit element is valid. 

Upon describing the record, a number of auxiliary definitions has been
generated by coq automatically. Along with the usual recursin and
induction principles, the system also generated three _getters_,
[valid_op], [join_op] and [unit_op] %\index{getters}% for the record's
named fields. That is, similarly to Haskell's syntax, given an
instance of a PCM, one can extract, for instance, its operation, via
the following getter function.

*)

Check valid_op.

(**
[[
valid_op
     : forall T : Type, mixin_of T -> T -> bool
]]

Coq supports the syntax for anonymous record fields (via the the
underscore [_]), so getters for them are not generated. We have
decided to make the property fileds of [mixin_of] to be anonymous,
since they will usually appear only in the proofs, where the structure
is going to be decomposed by case analysis anyway, as we will soon
see.

We can now prove a number of facts about the structure, very much in
the spirit of the facts that re being proven in the algebra course.
For instance, the following lemma states that [unit_op] is also the
_right unit_, in addition to it bein the left unit, as encoded by the
structure's definition.

%\index{right unit}%
%\index{left unit}%

*)


Lemma r_unit T (pcm: mixin_of T) (t: T) : (join_op pcm t (unit_op pcm)) = t.
Proof.
case: pcm=>_ join unit Hc _ Hlu _ _ /=.

(** 
[[
  T : Type
  t : T
  join : T -> T -> T
  unit : T
  Hc : commutative join
  Hlu : left_id unit join
  ============================
   join t unit = t
]]

The first line of the proof demonstrates that dependent records in Coq
are actually just product types in disguise, so the proof about them
should be done by case analysis. In this particular case, we decompose
the [pcm] argument of the lemma into its component, replacing those of
no iterest with wildcards [_]. The [join] and [unit], therefore, bind
the operation and the identity element, whereace [Hc] and [Hlu] are
the commutativity and left-unit properties, named explicitly for the
scope of the proof. The trailing SSReflect's simplification tactical
%\texttt{/=}\ssrtl{/=}% replaces the calls to the getters in the goal
(e.g., [join_op pcm]) by the bound identifiers. The proof can be now
accomplished by a series of rewritings by the [Hc] and [Hlu]
hypotheses.

*)

by rewrite Hc Hlu.
Qed.


(**

** An alternative definition

The PCM structure could be alternatively defined using the familiar
syntax for inductive types, as a datatype with precisely one
constructor:

*)

Inductive mixin_of' (T: Type) := 
  Mixin' (valid_op: T -> bool) (join_op : T -> T -> T) (unit_op: T) of
    commutative join_op &
    associative join_op &
    left_id unit_op join_op &
    forall x y, valid_op (join_op x y) -> valid_op x &
    valid_op unit_op.




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

(**

TODO

** Packaging the structure

*)

(** TODO: emphasize the [:>] coercion *)

Structure pack_type : Type := Pack {sort :> Type; _ : mixin_of sort; _ : Type}.

Variables (T : Type) (cT : pack_type).

Definition class : mixin_of cT := let: Pack _ c _ as cT' := cT return mixin_of cT' in c.

Check class.

Definition pack c := @Pack T c T.

Definition valid := valid_op class.
Definition join := join_op class.
Definition unit := unit_op class.

End PCMDef.

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
