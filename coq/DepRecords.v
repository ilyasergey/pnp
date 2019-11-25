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
(** printing bot $\bot$ *)
(** printing <== $\pre$ *)
(** printing From %\textsf{{From}}% *)


(** 
%
\chapter{Encoding Mathematical Structures}
\label{ch:depstruct}
% 
*)


(**  

Long before programming has been established as a discipline,
mathematics came to be perceived as a science of building
abstractions and summarizing important properties of various entities
necessary for describing nature's phenomenons.%\footnote{In
addition to being a science of rewriting, as we have already covered
in Chapter~\ref{ch:eqrew}.}% From the basic course of algebra, we are
familiar with a number of mathematical structures, such as monoids,
groups, rings, fields etc., which couple a _carrier_ set (or a number of
sets), a number of operations on it (them), and a collection of
properties of the set itself and operations on them.

From a working programmer's perspective, a notion of a mathematical
abstract structure is reminiscent to a notion of a class from
object-oriented programming, modules from Standard ML and type
classes%~\cite{Wadler-Blott:POPL89}% from Haskell: all these
mechanisms are targeted to solve the same goal: _package_ a number of
operations manipulating with some data, while abstracting of a
particular implementation of this data itself. What neither of these
programming mechanisms is capable of doing, comparing to mathematics,
is enforcing the requirement for one to provide the _proofs_ of
properties, which restrict the operations on the data structure. For
instance, one can implement a type class for a _lattice_ in Haskell as
follows: %\index{type classes}\index{Haskell}%

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
_greatest-lower-bound_ operations. What this class cannot capture is a
number of restrictions, for instance, that the %\texttt{pre}% relation
should be transitive, reflexive and antisymmetric. That said, one can
instantiate the %\texttt{Lattice}% class, e.g., for integers,
%\index{lattice}% providing an implementation of %\texttt{pre}%, which
is _not_ a partial order (e.g., just constant %\texttt{true}%). While
this relaxed approach is supposedly fine for the programming needs, as
the type classes are used solely for computing, not the reasoning
about the correctness of the computations, this is certainly
unsatisfactory from the mathematical perspective. Without the
possibility to establish and enforce the necessary properties of a
mathematical structure's operations, we would not be able to carry out
any sort of sound formal reasoning, as we simply could not distinguish
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
encoded in languages like C (with a bit of Haskell-ish type class-like
machinery), so the representation, unlike the one in C or Haskell,
would allow for flexible and generic reasoning about the structures'
properties. In the process, we will meet some old friends from the
course of abstract algebra---partial commutative monoids, and implement
them using Coq's native constructs: dependent records and canonical
structures.

As usual, we will require a number of Ssreflect package imported.

*)

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun.

(* begin hide *)
Module DepRecords.
(* end hide *)



(** 

We will also require to execute a number of Vernacular commands
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
%\label{sec:pcms}%

%\index{partial commutative monoid}%
%\index{PCM|see {partial commutative monoid}}%

We will be using partial commutative monoids (PCMs) as an illustrative
example of a simple algebraic data structure, a subject of encoding
and formalization. A PCM is defined as an algebraic structure with a
carrier set [U], abstract binary "join" operation $\join$ and a unit
element $\unit$.%\footnote{Sometimes also referred to as an
\emph{identity} or \emph{neutral} element.}%%\index{unit element}%
%\index{join operation}% The join operation is required to be
associative and commutative, and for the unit element the left and
right identity equalities should hold. Moreover, partiality means that
the operation $\join$ might be undefined for some pairs of elements
[a] and [b] (and in this case it is denoted as $a \join b =
\bot$). PCMs are fairly ubiquitous: in particular, natural numbers
with addition and multiplication, sets with a disjoin union,
partially-defined functions with a point-wise union, are all PCM
instances. Furthermore, partial commutative monoids are omnipresent in
program verification%~\cite{Nanevski-al:POPL10}%, as they capture
exactly the properties of _heaps_, as well as the effect of programs
that can be executed in
parallel%~\cite{Nanevski-al:ESOP14}%. Therefore, it is useful to have
PCMs formalized as a structure, so they could be employed for future
reasoning.

%\index{identity element|see {unit element}}%

%\newpage%

** Describing algebraic data structures via dependent records

*)

Module PCMDef.

(**

In %Section~\ref{sec:exists} of Chapter~\ref{ch:logic}% we have
already seen a use of a dependent pair type, exemplified by the Coq's
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
dependent pair, such that its second component's type _depends_ on the
value of the first one.%\index{dependent pair}% More specifically, the
result of the existential quantification's encoding in Coq is a
dependent pair $(\Sigma x:A, P~x)$, such that the proposition in
the second component is determined by the value of the first
component%~%[x].

%\index{dependent records}%

Coq provides an alternative way to encode _iterated_ dependent pairs
via the mechanism of _dependent records_, also allowing one to give
names to the subsequent components. Dependent records are defined
using the [Record] command. Getting back to our PCM example, we
illustrate the use of dependent records by the following definition of
the abstract PCM structure.

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

%\index{record types|see {dependent records}}%

The syntax of Coq's dependent records is reminiscent to the one of
records in C. Following Ssreflect's naming
pattern%~\cite{Garillot-al:TPHOL09}%, we call the record type (defined
in a dedicated module for the reasons explained further) [mixin_of]
and its only constructor [Mixin]. The reasons for such naming
convention will be explained soon, and for now let us discuss the
definition. The PCM record type is parametrized over the carrier type
[T], which determines the carrier set of a PCM. It then lists three
_named_ fields: [join_op] describes an implementation of the PCM's
binary operation, [unit_op] defines the unit element, finally, the
[valid_op] predicate determines whether a particular element of the
carrier set [T] is valid or not, and, thus, serves as a way to express
the partiality of the [join_op] operation (the result is undefined,
whenever the corresponding value of [T] is non-valid). Next, the PCM
record lists five unnamed PCM _properties_, which should be satisfied
whenever the record is instantiated and are defined using the standard
propositions from Ssreflect's [ssrfun] %\ssrm{ssrfun}% module (see
%Section~\ref{sec:funprops}%). In particular, the PCM type definition
requires the operation to be [commutative] and [associative]. It also
states that if $a \join b \neq \bot$ then $a \neq \bot$ (the same
statement about $b$ can be proved by commutativity), and that the unit
element is a valid one.

Notice that in the definition of the [mixin_of] record type, the types
of some of the later fields (e.g., any of the properties) depend on
the values of fields declared earlier (e.g., [unit_op] and [join_op]),
which makes [mixin_of] to be a truly dependent type.

Upon describing the record, a number of auxiliary definitions have been
generated by Coq automatically. Along with the usual recursion and
induction principles, the system also generated three _getters_,
[valid_op], [join_op] and [unit_op] %\index{getters}% for the record's
named fields. That is, similarly to Haskell's syntax, given an
instance of a PCM, one can extract, for example, its operation, via
the following getter function.

*)

Check valid_op.

(**
[[
valid_op
     : forall T : Type, mixin_of T -> T -> bool
]]

Coq supports the syntax for anonymous record fields (via the
underscore [_]), so getters for them are not generated. We have
decided to make the property fields of [mixin_of] to be anonymous,
since they will usually appear only in the proofs, where the structure
is going to be decomposed by case analysis anyway, as we will soon
see.

We can now prove a number of facts about the structure, very much in
the spirit of the facts that are being proven in the algebra course.
For instance, the following lemma states that [unit_op] is also the
_right unit_, in addition to it being the left unit, as encoded by the
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
are actually just product types in disguise, so the proofs about them
should be done by case analysis. In this particular case, we decompose
the [pcm] argument of the lemma into its components, replacing those
of no interest with wildcards [_]. The [join] and [unit], therefore,
bind the operation and the identity element, whereas [Hc] and [Hlu]
are the commutativity and left-unit properties, named explicitly in
the scope of the proof. The trailing Ssreflect's simplification
tactical %\texttt{/=}\ssrtl{/=}% replaces the calls to the getters in
the goal (e.g., [join_op pcm]) by the bound identifiers. The proof can
be now accomplished by a series of rewritings by the [Hc] and [Hlu]
hypotheses.

*)

by rewrite Hc Hlu.
Qed.


(**

** An alternative definition

In the previous section we have seen how to define the algebraic
structure of PCMs using Coq's dependent record mechanism. The same PCM
structure could be alternatively defined using the familiar syntax for
inductive types, as a datatype with precisely one constructor:

*)

Inductive mixin_of' (T: Type) := 
  Mixin' (valid_op: T -> bool) (join_op : T -> T -> T) (unit_op: T) of
    commutative join_op &
    associative join_op &
    left_id unit_op join_op &
    forall x y, valid_op (join_op x y) -> valid_op x &
    valid_op unit_op.

(**

Although this definition seems more principled and is closer to what
we have seen in previous chapters, the record notation is more
convenient in this case, as it defined getters automatically as well
as allows one to express inheritance between data structures by means
of the coercion operator %\texttt{:>}%
operator%~\cite{Garillot-al:TPHOL09}%.%\footnote{In the next section
will show a different way to encode implicit inheritance, though.}%

** Packaging the structure from mixins
%\label{sec:packaging}%

*)

Section Packing.

(** 

%\index{packaging}%

By now, we have defined a structure of a PCM "interface" in a form of
a set of the components (i.e., the carrier set and operations on it)
and their properties. However, it might be the case that the same
carrier set (which we represented by the type parameter [T]), should
be given properties from other algebraic data structures (e.g.,
lattices), which are essentially orthogonal to those of a
PCM. Moreover, at some point one might be interested in implementing
the proper inheritance of the PCM structure with respect to the
carrier type [T]. More precisely, if the type [T] comes with some
additional operations, they should be available from it, even if it's
seen as being "wrapped" into the PCM structure. That said, if [T] is
proven to be a PCM, one should be able to use this fact as well as the
functions, defined on [T] separately.

%\index{packed classes}%

These two problems, namely, (a) combining together several structures
into one, and (b) implementing inheritance and proper mix-in
composition, can be done in Coq using the description pattern, known
as "packed classes"%~\cite{Garillot-al:TPHOL09}%. The idea of the
approach is to define a "wrapper" record type, which would "pack"
several mix-ins together, similar to how it is done in object-oriented
languages with implicit trait composition, e.g.,
Scala%~\cite{Odersky-Zenger:OOPSLA05}%.%\footnote{Using this mechanism
will, however, afford us a greater degree of flexibility, as it is up
to the Coq programmer to define the resolution policy of the combined
record's members, rather than to rely on an implicit mechanism of
field linearization.}%

%\index{Scala}\index{traits}%
%\label{ref:pack_type}%
*)

Structure pack_type : Type := Pack {type : Type; _ : mixin_of type}.

(** 

The dependent data structure [pack_type] declares two fields: the
field [type] of type [Type], which described the carrier type of the
PCM instance, and the actual PCM structure (without an explicit name
given) of type ([mixin_of type]). That is, in order to construct an
instance of [pack_type], one will have to provide _both_ arguments:
the carrier set and a PCM structure for it.

Next, we specify that the field [type] of the [pack_type] should be
also considered as a _coercion_, that is, whenever we have a value of
type [pack_type], whose field [type] is some [T], it can be implicitly
seen as an element of type [T]. The coercion is specified locally, so
it will work only in the scope of the current section (i.e.,
[Packing]) by using Coq's [Local Coercion] command. We address the
reader to Chapter 18 of the Coq Reference Manual%~\cite{Coq-manual}%
for more details of the implicit coercions.

%\ccom{Local Coercion}%
*)

Local Coercion type : pack_type >-> Sortclass.

(**

%\index{Sortclass@\emph{Sortclass}}%

The [>->] simply specifies the fact of the coercion, whereas
[Sortclass] is an abstract class of sorts, so the whole command
postulates that whenever an instance of [pack_type] should be coerced
into an element of an arbitrary sort, it should be done via referring
to is [type] field.

Next, in the same section, we provide a number of abbreviations to
simplify the work with the PCM packed structure and prepare it to be
exported by clients.

*)
Variable cT: pack_type.

Definition pcm_struct : mixin_of cT := 
    let: Pack _ c := cT return mixin_of cT in c.

(** 

The function [pcm_struct] extracts the PCM structure from the "packed"
instance. Notice the use of dependent pattern matching
%\index{dependent pattern matching}% in the [let:]-statement with the
explicit [return]-statement, so Coq would be able to refine the result
of the whole expression basing on the dependent type of the [c]
component of the data structure [cT], which is being scrutinized. With
the help of this definition, we can now define three aliases for the
PCM's key components, "lifted" to the packed data structure.

*)

Definition valid := valid_op pcm_struct.
Definition join := join_op pcm_struct.
Definition unit := unit_op pcm_struct.

End Packing.

(** 

Now, as the packaging mechanism and the aliases are properly defined,
we come to the last step of the PCM package description: preparing the
batch of definitions, notations and facts to be exported to the
client. Following the pattern of nesting modules, presented in
%Section~\ref{sec:secmod}%, we put all the entities to be exported
into the inner module [Exports].

*)

Module Exports.

Notation pcm := pack_type.
Notation PCMMixin := Mixin.
Notation PCM T m := (@Pack T m).

Notation "x \+ y" := (join x y) (at level 43, left associativity).
Notation valid := valid.
Notation Unit := unit.


(** 

We will have to define the coercion from the PCM structure with
respect to its [type] field once again, as the previous one was
defined locally for the section [Packing], and, hence, is invisible in
this submodule.

*)

Coercion type : pack_type >-> Sortclass.


(** 

* Properties of partial commutative monoids 

Before we close the [Exports] module of the [PCMDef] package, it makes
sense to supply as many properties to the clients, as it will be
necessary for them to build the reasoning involving PCMs. In the
traditions of proper encapsulation, %\index{encapsulation}% requiring
to expose only the relevant and as abstract as possible elements of
the interface to its clients, it is undesirable for users of the [pcm]
datatype to perform any sort of analysis on the structure of the
[mixin_of] datatype, as it will lead to rather tedious and cumbersome
proofs, which will first become a subject of massive changes, once we
decide to change the implementation of the PCM mixin structure.

This is why in this section we supply a number of properties of PCM
elements and operations, derived from its structure, which we observe
to be enough to build the reasoning with arbitrary PCM instances.

*)

Section PCMLemmas.
Variable U : pcm.

(** 

For instance, the following lemma re-establishes the commutativity of
the [\+] operation:

*)

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof.
by case: U x y=> tp [v j z Cj *]; apply Cj.
Qed.


(** 

Notice that in order to make the proof to go through, we had to "push"
the PCM elements [x] and [y] to be the assumption of the goal before
case-analysing on [U]. This is due to the fact that the structure of
[U] affects the type of [x] and [y], therefore destructing it by means
of [case] would change the representation of [x] and [y] as well,
doing some rewriting and simplifications. Therefore, when [U] is being
decomposed, all values, whose type depends on it (i.e., [x] and [y])
should be in the scope of decomposition. The naming pattern $*$ helped
us to give automatic names to all remaining assumptions, appearing
from decomposition of [U]'s second component before moving it to the
context before finishing the proof by applying the commutativity
"field" [Cj].

*)

Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
Proof. 
by case: U x y z=>tp [v j z Cj Aj *]; apply: Aj. 
Qed.

(** 

%\begin{exercise}[PCM laws]% 
Prove the rest of the PCM laws.

*)

Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
(* begin hide *)
Proof. by rewrite -joinA (joinC y) joinA. Qed.
(* end hide *)

Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
(* begin hide *)
Proof. by rewrite joinA (joinC x) -joinA. Qed.
(* end hide *)

Lemma validL (x y : U) : valid (x \+ y) -> valid x.
(* begin hide *)
Proof. case: U x y=>tp [v j z Cj Aj Uj /= Mj inv f]; apply: Mj. Qed.
(* end hide *)

Lemma validR (x y : U) : valid (x \+ y) -> valid y.
(* begin hide *)
Proof. by rewrite joinC; apply: validL. Qed.
(* end hide *)

Lemma unitL (x : U) : (@Unit U) \+ x = x.
(* begin hide *)
Proof. by case: U x=>tp [v j z Cj Aj Uj *]; apply: Uj. Qed.
(* end hide *)

Lemma unitR (x : U) : x \+ (@Unit U) = x.
(* begin hide *)
Proof. by rewrite joinC unitL. Qed.
(* end hide *)

Lemma valid_unit : valid (@Unit U).
(* begin hide *)
Proof. by case: U=>tp [v j z Cj Aj Uj Vm Vu *]. Qed.
(* end hide *)

(**

%\end{exercise}%

*)

End PCMLemmas.

End Exports.

End PCMDef.

Export PCMDef.Exports.

(** 

* Implementing inheritance hierarchies

%\index{inheritance}%

By packaging an arbitrary type [T] into one record with the PCM
structure in %Section~\ref{sec:packaging}% and supplying it with a
specific implicit coercion, we have already achieved some degree of
inheritance: any element of a PCM can be also perceived by the system
in an appropriate context, as an element of its carrier type. 

In this section, we will go even further and show how to build
hierarchies of mathematical structures using the same way of encoding
inheritance. We will use a _cancellative PCM_ as a running example.

*)

Module CancelPCM.

(**

PCMs with cancellation %\index{cancellativity}% extend ordinary PCMs
with an extra property, that states that the equality $a \join b = a
\join c$ for any $a$, $b$ and $c$, whenever $a \join b$ is defined,
implies $b = c$. We express such property via an additional mixin
record type, parametrized over an arbitrary PCM [U].

*)

Record mixin_of (U : pcm) := Mixin {
  _ : forall a b c: U, valid (a \+ b) -> a \+ b = a \+ c -> b = c
}.

(** 

Notice that the validity of the sum [a \+ c] is not imposed, as it can
be proven from propositional equality and the validity of [a \+ b].

We continue the definition by describing the standard packaging data
structure.

*)

Structure pack_type : Type := Pack {pcmT : pcm; _ : mixin_of pcmT}.

Module Exports.

Notation cancel_pcm := pack_type.
Notation CancelPCMMixin := Mixin.
Notation CancelPCM T m:= (@Pack T m).

(** 

There is a tiny twist in the definition of the specific coercion,
though, as now we it specifies that the instance of the packed data
structure, describing the cancellative PCM, can be seen as an instance
of the underlying PCM. The coercions are transitive, which means that
the same instance can be coerced even further to [U]'s carrier type
[T].

*)

Coercion pcmT : pack_type >-> pcm.

(** 

We finish the definition of the cancellative PCM by providing its only
important law, which is a direct consequence of the newly added
property.

*)

Lemma cancel (U: cancel_pcm) (x y z: U): 
  valid (x \+ y) -> x \+ y = x \+ z -> y = z.
Proof.
by case: U x y z=>Up [Hc] x y z; apply: Hc.
Qed.

End Exports.
End CancelPCM. 

Export CancelPCM.Exports.

(** 

The proof of the following lemma, combining commutativity and
cancellativity, demonstrates how the properties of a cancellative PCM
work in combination with the properties of its base PCM structure.

*)

Lemma cancelC (U: cancel_pcm) (x y z : U) :
  valid (y \+ x \+ z) -> y \+ x = x \+ z -> y = z.
Proof.
by move/validL; rewrite ![y \+ _]joinC; apply: cancel.
Qed.


(**

* Instantiation and canonical structures

Now, as we have defined a PCM structure along with its specialized
version, a cancellative PCM, it is time to see how to _instantiate_
these abstract definitions with concrete datatypes, i.e., _prove_ the
latter ones to be instances of a PCM.

%\index{instantiation}%

** Defining arbitrary PCM instances

Natural numbers form a PCM, in particular, with addition as a join
operation and zero as a unit element. The validity predicate is
constant true, because the addition of two natural numbers is again a
valid natural number. Therefore, we can instantiate the PCM structure
for [nat] as follows, first by constructing the appropriate mixin.

*)

Definition natPCMMixin := 
  PCMMixin addnC addnA add0n (fun x y => @id true) (erefl _).

(**

The constructor [PCMMixin], defined in %Section~\ref{sec:packaging}%
is invoked with five parameters, all of which correspond to the
properties, ensured by the PCM definition. The rest of the arguments,
namely, the validity predicate, the join operation and the zero
element are implicit and are soundly inferred by Coq's type inference
engine from the types of lemmas, provided as propositional
arguments. For instance, the first argument [addnC], whose type is
[commutative addn] makes it possible to infer that the join operation
is the addition. In the same spirit, the third argument, [add0n] makes
it unambiguous that the unit element is zero.

After defining the PCM mixin, we can instantiate the PCM packed class
for [nat] by the following definition:

*)

Definition NatPCM := PCM nat natPCMMixin.

(** 

This definition will indeed work, although, being somewhat
unsatisfactory. For example, assume we want to prove the following
lemma for natural numbers treated as elements of a PCM, which should
trivially follow from the PCM properties of [nat] with addition and
zero:

[[
Lemma add_perm (a b c : nat) : a \+ (b \+ c) = a \+ (c \+ b).
]]


[[
The term "a" has type "nat" while it is expected to have type "PCMDef.type ?135".
]]

This error is due to the fact that Coq is unable to recognize natural
numbers to be elements of the corresponding PCM, and one possible way
to fix it is to declare the parameters of the lemma [add_perm], [a],
[b] and [c] to be of type [NatPCM] rather than [nat]. This is still
awkward: it means that the lemmas cannot be just applied to mere
natural numbers, instead they need to be _coerced_ to the [NatPCM]
type explicitly whenever we need to apply this lemma. Coq suggests a
better solution to this problem by providing a mechanism of _canonical
structures_ as a flexible way to specify _how exactly_ each concrete
datatype should be embedded into an abstract mathematical
structure%~\cite{Saibi:PhD}%.

%\index{canonical structures}% 

The Vernacular syntax for defining canonical structures is similar to
the one of definitions and makes use of the %\texttt{Canonical}%
command.%\footnote{The command \texttt{Canonical Structure}
\ccom{Canonical Structure} serves the same purpose.}\ccom{Canonical}%
The following definition defines [natPCM] to be a canonical instance
of the PCM structure for natural numbers.

*)

Canonical natPCM := PCM nat natPCMMixin.

(** 

To see what kind of effect it takes, we will print all _canonical
projections_, currently available in the context of the module. 

*)

Print Canonical Projections.

(**

[[
...
nat <- PCMDef.type ( natPCM )
pred_of_mem <- topred ( memPredType )
pred_of_simpl <- topred ( simplPredType )
sig <- sub_sort ( sig_subType )
number <- sub_sort ( number_subType )
...
]]

%\index{canonical projections}%
The displayed list enumerates all _canonical projections_ that specify,
which implicit canonical instances are currently available and will be
picked implicitly for appropriate types (on the left of the arrow
[<-]). That is, for example, whenever an instance of [nat] is
available, but in fact it should be treated as the [type] field of the
[PCM] structure (with all getters typed properly), the canonical
instance [natPCM] will be automatically picked by Coq for such
embedding. In other words, the machinery of canonical structures
allows us to define the policy for finding an appropriate _dictionary_
of functions and propositions for an arbitrary concrete datatype,
whenever it is supposed to have them. In fact, upon declaring the
canonical structure [natPCM], the canonical projections are
registered by Coq for all _named_ fields of the record [PCM], which is
precisely just the [type] field, since [PCM]'s second component of
type ([mixin_of type]) was left unnamed (see the definition of
the record [pack_type] on page%~\pageref{ref:pack_type}%).

The mechanism of defining canonical structures for concrete data types
is reminiscent of the resolution of type class constraints in
Haskell%~\cite{Wadler-Blott:POPL89}%. However, unlike Haskell, where
the resolution algorithm for type class instances is _hard-coded_, in
the case of Coq one can actually _program_ the way the canonical
instances are resolved.%\footnote{In addition to canonical structures,
Coq also provides mechanism of type classes, which are even more
reminiscent of the ones from Haskell, and, similar to the latter
ones, do not provide a way to program the resolution
policy~\cite{Sozeau-Oury:TPHOL08}.}% This leads to a very powerful
technique to automate the process of theorem proving by encoding the
way to find and apply necessary lemmas, whenever it is required. These
techniques are, however, outside of the scope of this course, so we
direct the interested reader to the relevant research papers that
describe the patterns of programming with canonical
structures%~\cite{Gontier-al:ICFP11,Mahboubi-Tassi:ITP13,Garillot:PhD}%.

Similarly to the way we have defined a canonical instance of PCM for
[nat], we can define a canonical instance of a PCM with
cancellativity. In order to instantiate it, we will, however, need to
prove the following lemma, which states that the addition on natural
numbers is indeed cancellative, so this fact will be used as an
argument for the [CancelPCMMixin] constructor.

*)


Lemma cancelNat : forall a b c: nat, true -> a + b = a + c -> b = c.
Proof.
move=> a b c; elim: a=>// n /(_ is_true_true) Hn _ H.
by apply: Hn; rewrite !addSn in H; move/eq_add_S: H.
Qed.

(** 

Notice the first assumption [true] of the lemma. Here it serves as a
placeholder for the general validity hypothesis [valid (a \+ b)],
which is always [true] in the case of natural numbers.

*)

Definition cancelNatPCMMixin := CancelPCMMixin cancelNat.

Canonical cancelNatPCM := CancelPCM natPCM cancelNatPCMMixin.

(** 

Let us now see the canonical instances in action, so we can prove a
number of lemmas about natural numbers employing the general PCM
machinery.

*)

Section PCMExamples.

(** %\label{pg:addnprops}% *)

Variables a b c: nat.

Goal a \+ (b \+ c) =  c \+ (b \+ a).
by rewrite joinA [c \+ _]joinC [b \+ _]joinC.
Qed.

(** 

The next goal is proved by using the combined machinery of [PCM] and
[CancelPCM].

*)

Goal c \+ a = a \+ b -> c = b.
by rewrite [c \+ _]joinC; apply: cancel.
Qed.

(** 

It might look a bit cumbersome, though, to write the PCM join
operation [\+] instead of the boolean addition when specifying the
facts about natural numbers (even though they are treated as elements
of the appropriate PCM). Unfortunately, it is not trivial to encode
the mechanism, which will perform such conversion implicitly. Even
though Coq is capable of figuring out what PCM is necessary for a
particular type (if the necessary canonical instance is defined),
e.g., when seeing [(a b : nat)] being used, it infers the [natPCM],
alas, it's not powerful enough to infer that by writing the
addition function [+] on natural numbers, we mean the PCM's
join. However, if necessary, in most of the cases the conversion like
this can be done by manual rewriting using the following trivial
"conversion" lemma.

*)

Lemma addn_join (x y: nat): x + y = x \+ y. 
Proof. by []. Qed.

End PCMExamples.

(**
%\begin{exercise}[Partially ordered sets]%

%\index{partially ordered set}%

A partially ordered set order is a pair $(T, \pre)$, such that $T$ is
a set and $\pre$ is a (propositional) relation on $T$, such that

%
\begin{enumerate}
\item $\forall x \in T, x \pre x$ (reflexivity);

\item $\forall x, y \in T, x \pre y \wedge y \pre x \implies x = y$ (antisymmetry);

\item $\forall x, y, z \in T, x \pre y \wedge y \pre z \implies x \pre z$ (transitivity).
\end{enumerate}
%

%\noindent%
Implement a data structure for partially-ordered sets using mixins and
packed classes. Prove the following laws:

[[
Lemma poset_refl (x : T) : x <== x.
Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
]]

%\end{exercise}%

%\begin{exercise}[Canonical instances of partially ordered sets]%

Provide canonical instances of partially ordered sets for the
following types:

- [nat] with [<=] as a partial order;
- [prod], whose components are partially-ordered sets;
- functions [A -> B], whose codomain (range) [B] is a partially
  ordered set.

In order to provide a canonical instance for functions, you will need
to assume and make use of the following axiom of functional
extensionality:

%\index{extensionality}%

*)

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x), 
               (forall x, f1 x = f2 x) -> f1 = f2.

(**
%\end{exercise}%

** Types with decidable equalities
%\index{decidable equality}%

When working with Ssreflect and its libraries, one will always come
across multiple canonical instances of a particularly important
dependent record type---a structure with decidable equality. As it has
been already demonstrated in %Section~\ref{sec:eqrefl}%, for concrete
datatypes, which enjoy the decidable boolean equality [(==)], the
"switch" to Coq's propositional equality and back can be done
seamlessly by means of using the view lemma [eqP], leveraging the
[reflect] predicate instance of the form [reflect (b1 = b2) (b1 ==
b2)].%\ssrd{reflect}% Let us now show how the decidable equality is
defined and instantiated.

The module [eqtype]%\ssrm{eqtype}% of Ssreflect's standard library
provides a definition of the equality mixin and packaged class of the
familiar shape, which, after some simplifications, boil to the
following ones:

[[
Module Equality.

Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).

Structure mixin_of T := Mixin {op : rel T; _ : axiom op}.
Structure type := Pack {sort; _ : mixin_of sort}.

...

Notation EqMixin := Mixin.
Notation EqType T m := Pack T m.

End Equality.
]]

That is, the mixin for equality is a dependent record, whose first
field is a relation [op] on a particular carrier type [T] (defined
internally as a function [T * T -> bool]), and the second argument is
a proof of the definition [axiom], which postulates that the relation
is in fact equivalent to propositional equality (which is
established by means of inhabiting the [reflect] predicate
instance). Therefore, in order to make a relation [op] to be a
decidable equality on [T], one needs to prove that, in fact, it is
equivalent to the standard, propositional equality.

Subsequently, Ssreflect libraries deliver the canonical instances of
the decidable equality structure to all commonly used concrete
datatypes. For example, the decidable equality for natural numbers is
implemented in the [ssrnat]%\ssrm{ssrnat}% module by the following
recursive function:%\footnote{Coq's %[{struct n}]% annotation
explicitly specifies, which of the two arguments should be considered
by the system as a decreasing one, so the recursion would be
well-founded and %[eqn]% would terminate.}%

[[
Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => eqn m' n'
  | _, _ => false
  end.
]]

%\noindent%
The following lemma ensures that [eqn] correctly reflects the
propositional equality.

[[
Lemma eqnP : Equality.axiom eqn.
Proof.
move=> n m; apply: (iffP idP) => [ | <- ]; last by elim n.
by elim: n m => [ | n IHn] [| m ] //= /IHn ->.
Qed.
]]
%\ssrtl{//=}%

%\noindent%
Finally, the following two definitions establish the canonical instance
of the decidable equality for [nat], which can be used whenever
[ssrnat] is imported.

[[
Canonical nat_eqMixin := EqMixin eqnP.
Canonical nat_eqType := EqType nat nat_eqMixin.
]]

*)

(* begin hide *)
End DepRecords.
(* end hide *)
