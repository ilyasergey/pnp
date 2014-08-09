(** %\chapter{Encoding Mathematical Structures}% *)

Module DepRecords.

Require Import ssreflect ssrbool ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Encoding partial commutative monoids *)

Module PCMDef.

(**

We have already seen a use of a dependent pair type, exemplified by
the Coq's definition of the universal quantification.

*)

Print ex.

(**
[[
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
]]

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
*)

Check valid_op.

(**
[[
valid_op
     : forall T : Type, mixin_of T -> T -> bool
]]
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
*)

by rewrite Hc Hlu.
Qed.


(** ** An alternative definition *)

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

Structure pack_type : Type := Pack {type : Type; _ : mixin_of type}.

(** 

The dependent data structure [pack_type] declares two fields: the
field [type] of type [Type], which described the carrier type of the
PCM instance, and the actual PCM structure (without an explicit name
given) of type [mixin_of type]. That is, in order to construct an
instance of [pack_type], one will have to provide _both_ arguments:
the carrier set and a PCM structure for it.

*)

Local Coercion type : pack_type >-> Sortclass.

(**

Next, in the same section, we provide a number of abbreviations to
simplify the work with the PCM packed structure and prepare it to be
exported by clients.

*)
Variable cT: pack_type.

Definition pcm_struct : mixin_of cT := 
    let: Pack _ c := cT return mixin_of cT in c.

Definition valid := valid_op pcm_struct.
Definition join := join_op pcm_struct.
Definition unit := unit_op pcm_struct.

End Packing.

Module Exports.

Notation pcm := pack_type.
Notation PCMMixin := Mixin.
Notation PCM T m := (@Pack T m).

Notation "x \+ y" := (join x y) (at level 43, left associativity).
Notation valid := valid.
Notation Unit := unit.


Coercion type : pack_type >-> Sortclass.


(** * Properties of partial commutative monoids *)

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
decomposed, al values, whose type depends on it (i.e., [x] and [y])
should be in the scope of decomposition. The naming pattern [*] helped
us to give automatic names to all remaining assumptions, appearing
from decomposition of [U]'s second component before moving it to the
context before finishing the proof by applying the commutativity
"field" [Cj].

*)

Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
Proof. 
by case: U x y z=>tp [v j z Cj Aj *]; apply: Aj. 
Qed.

(*******************************************************************)
(**                     * Exercices 1 *                            *)
(*******************************************************************)

(** 
---------------------------------------------------------------------
Exercise [PCM Laws]
---------------------------------------------------------------------

Proove the rest of the PCM laws.
*)

Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
Proof.
(* fill in your proof here instead of [admit] *)
admit.
Qed.


Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof.
(* fill in your proof here instead of [admit] *)
admit.
Qed.


Lemma validL (x y : U) : valid (x \+ y) -> valid x.
Proof.
(* fill in your proof here instead of [admit] *)
admit.
Qed.


Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof.
(* fill in your proof here instead of [admit] *)
admit.
Qed.


Lemma unitL (x : U) : (@Unit U) \+ x = x.
Proof.
(* fill in your proof here instead of [admit] *)
admit.
Qed.


Lemma unitR (x : U) : x \+ (@Unit U) = x.
Proof.
(* fill in your proof here instead of [admit] *)
admit.
Qed.


Lemma valid_unit : valid (@Unit U).
Proof.
(* fill in your proof here instead of [admit] *)
admit.
Qed.


(*******************************************************************)
(**                 * End of Exercices 1 *                         *)
(*******************************************************************)

End PCMLemmas.

End Exports.

End PCMDef.

Export PCMDef.Exports.

(** * Implementing inheritance hierarchies

We will now go even further and show how to build hierarchies of
mathematical structures using the same way of encoding inheritance. We
will use a _cancellative PCM_ as a running example.

*)

Module CancelPCM.

Record mixin_of (U : pcm) := Mixin {
  _ : forall a b c: U, valid (a \+ b) -> a \+ b = a \+ c -> b = c
}.

Structure pack_type : Type := Pack {pcmT : pcm; _ : mixin_of pcmT}.

Module Exports.

Notation cancel_pcm := pack_type.
Notation CancelPCMMixin := Mixin.
Notation CancelPCM T m:= (@Pack T m).

Coercion pcmT : pack_type >-> pcm.

Lemma cancel (U: cancel_pcm) (x y z: U): 
  valid (x \+ y) -> x \+ y = x \+ z -> y = z.
Proof.
by case: U x y z=>Up [Hc] x y z; apply: Hc.
Qed.

End Exports.
End CancelPCM. 

Export CancelPCM.Exports.

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
later ones to be instances of a PCM.

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

The constructor [PCMMixin], defined in Section~%\ref{sec:packaging}%
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
the one of definitions and makes use of the [Canonical]
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

The displayed list specifies, which implicit canonical instances are
currently available and will be triggered implicitly. That is, for
example, whenever an instance of [nat] is available, but in fact it
should be treated as the [type] field of the [PCM] structure (with all
getters typed properly), the canonical instance [natPCM] will be
automatically picked by Coq for such embedding. In other words, the
machinery of canonical structures allows us to define the policy for
finding an appropriate _dictionary_ of functions and propositions for
an arbitrary concrete datatype, whenever it is supposed to have
them. The mechanism of defining canonical structures for concrete data
types is reminiscent to the resolution of type class constraints in
Haskell%~\cite{Wadler-Blott:POPL89}%. However, unlike Haskell, where
the resolution algorithm for type class instances is _hard-coded_, in
the case of Coq one can actually _program_ the way the canonical
instances are resolved.%\footnote{In addition to canonical structures,
Coq also provides mechanism of type classes, which are even more
reminiscent to the ones from Haskell, and, similarly to the later
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
alas, it's not powerful enough to infer that the by writing the
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

A partially ordered set order is a triple $(T, \pre, \bot)$, such that
$T$ is a set, $\pre$ is a relation on $T$ and $\bot$ is an element of
$T$, such that

%
\begin{enumerate}
\item $\forall x \in T, \bot \pre x$ ($\bot$ is a bottom element);

\item $\forall x \in T, x \pre x$ (reflexivity);

\item $\forall x, y \in T, x \pre y \wedge y \pre x \implies x = y$ (antisymmetry);

\item $\forall x, y, z \in T, x \pre y \wedge y \pre z \implies x \pre z$ (transitivity).
\end{enumerate}
%

Implement a data structure for partially-ordered sets using mixins and
packed classes. Prove the following laws:

[[
Lemma botP (x : T) : bot <== x.
Lemma poset_refl (x : T) : x <== x.
Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
]]

Provide canonical instances of partially ordered sets for types [nat]
and [pair] and functions, whose codomain (range) is a partially
ordered set.

%\end{exercise}%

** Types with decidable equalities
%\index{decidable equality}%

When working with SSReflect and its libraries, one will always come
across multiple canonical instances of a particularly important
dependent record type---a structure with decidable equality. As it has
been already demonstrated in %Section~\ref{sec:eqrefl}%, for concrete
datatypes, which enjoy the decidable boolean equality [(==)], the
"switch" to Coq's propositional equality and back can be done
seamlessly by means of using the view lemma [eqP], leveraging the
[reflect] predicate instance of the form [reflect (b1 = b2) (b1 ==
b2)].%\ssrd{reflect}% Let us now show how the decidable equality is
defined and instantiated.

The module [eqtype]%\ssrm{eqtype}% of SSReflect's standard library
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
is in fact equivalent to the propositional equality (which is
established by means of inhabiting the [reflect] predicate
instance). Therefore, in order to make a relation [op] to be a
decidable equality on [T], one needs to prove that, in fact, it is
equivalent to the standard, propositional equality.

Subsequently, SSReflect libraries deliver the canonical instances of
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
The following lemma establishes that [eqn] correctly reflects the
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
Finally the following two definitions establish the canonical instance
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
