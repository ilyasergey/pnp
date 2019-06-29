(** %\chapter{Encoding Mathematical Structures}% *)

From mathcomp
Require Import ssreflect ssrbool ssrnat ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DepRecords.

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
Admitted.



Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



Lemma validL (x y : U) : valid (x \+ y) -> valid x.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



Lemma unitL (x : U) : (@Unit U) \+ x = x.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



Lemma unitR (x : U) : x \+ (@Unit U) = x.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



Lemma valid_unit : valid (@Unit U).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



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

*)

Canonical natPCM := PCM nat natPCMMixin.

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
*)


Lemma cancelNat : forall a b c: nat, true -> a + b = a + c -> b = c.
Proof.
move=> a b c; elim: a=>// n /(_ is_true_true) Hn _ H.
by apply: Hn; rewrite !addSn in H; move/eq_add_S: H.
Qed.

Definition cancelNatPCMMixin := CancelPCMMixin cancelNat.

Canonical cancelNatPCM := CancelPCM natPCM cancelNatPCMMixin.

(** 

Let us now see the canonical instances in action, so we can prove a
number of lemmas about natural numbers employing the general PCM
machinery.

*)

Section PCMExamples.

Variables a b c: nat.

Goal a \+ (b \+ c) =  c \+ (b \+ a).
by rewrite joinA [c \+ _]joinC [b \+ _]joinC.
Qed.

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

(** ** Types with decidable equalities

The module [eqtype] of SSReflect's standard library provides a
definition of the equality mixin and packaged class of the familiar
shape, which, after some simplifications, boil to the following ones:

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

DEMO: check the corresponding files ssreflect-1.4/theories/eqtype.v
and ssreflect-1.4/theories/ssrnat.v

*)

(*******************************************************************)
(**                     * Exercices 2 *                            *)
(*******************************************************************)

(** 
---------------------------------------------------------------------
Exercise [Partially-ordered sets]
---------------------------------------------------------------------

A partially ordered set order is a pair (T, <==), where T is a carrier
set and <== is a relation on T, such that

- forall x in T, x <== x (reflexivity);

- forall x, y in T, x <== y /\ y <== x \implies x = y (antisymmetry);

- forall x, y, z in T, x <== y /\ y <== z \implies x <== z (transitivity).

Implement a data structure for partially-ordered sets using mixins and
packed classes. Prove the following laws:

Lemma poset_refl (x : T) : x <== x.
Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
*)

(**
---------------------------------------------------------------------
Exercise [Canonical instances of partially ordered sets]
---------------------------------------------------------------------

Provide canonical instances of partially ordered sets for the
following types:

- [nat] and [<=];

- [prod], whose components are posets;

- functions [A -> B], whose codomain (range) [B] is a partially
  ordered set.

In order to provide a canonical instance for functions, you will need
to assume and make use of the following axiom of functional
extensionality:

*)

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x), 
               (forall x, f1 x = f2 x) -> f1 = f2.


(*******************************************************************)
(**                 * End of Exercices 2 *                         *)
(*******************************************************************)

End DepRecords.
