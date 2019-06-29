From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PCMDef.

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

Section Packing.

Structure pack_type : Type := Pack {type : Type; _ : mixin_of type}.
Local Coercion type : pack_type >-> Sortclass.
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

Section PCMLemmas.
Variable U : pcm.

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof.
by case: U x y=> tp [v j z Cj *]; apply Cj.
Qed.

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
Proof. by rewrite -joinA (joinC y) joinA. Qed.

Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof. by rewrite joinA (joinC x) -joinA. Qed.

Lemma validL (x y : U) : valid (x \+ y) -> valid x.
Proof. 
case: U x y=>tp [v j z Cj Aj Uj /= Mj inv f]. 
by apply: Mj. 
Qed.

Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof. by rewrite joinC; apply: validL. Qed.

Lemma unitL (x : U) : (@Unit U) \+ x = x.
Proof. by case: U x=>tp [v j z Cj Aj Uj *]; apply: Uj. Qed.

Lemma unitR (x : U) : x \+ (@Unit U) = x.
Proof. by rewrite joinC unitL. Qed.

Lemma valid_unit : valid (@Unit U).
Proof. by case: U=>tp [v j z Cj Aj Uj Vm Vu *]. Qed.

(*******************************************************************)
(**                 * End of Exercices 1 *                         *)
(*******************************************************************)

End PCMLemmas.

End Exports.

End PCMDef.

Export PCMDef.Exports.

(*******************************************************************)
(**                     * Exercices 2 *                            *)
(*******************************************************************)

(** 
---------------------------------------------------------------------
Exercise [Partially-ordered sets]
---------------------------------------------------------------------

A partially ordered set order is a triple (T, \pre, \bot), such that T
is a carrier set, \pre is a relation on T and \bot is an element of T,
such that

- forall x in T, \bot \pre x (\bot is a bottom element);

- forall x in T, x \pre x (reflexivity);

- forall x, y in T, x \pre y \wedge y \pre x \implies x = y (antisymmetry);

- forall x, y, z in T, x \pre y \wedge y \pre z \implies x \pre z (transitivity).

Implement a data structure for partially-ordered sets using mixins and
packed classes. Prove the following laws:

Lemma botP (x : T) : bot <== x.
Lemma poset_refl (x : T) : x <== x.
Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.

*)

Module Poset.
Section RawMixin.

Record mixin_of (T : Type) := Mixin {
  mx_leq : T -> T -> Prop;
  _ : forall x, mx_leq x x; 
  _ : forall x y, mx_leq x y -> mx_leq y x -> x = y; 
  _ : forall x y z, mx_leq x y -> mx_leq y z -> mx_leq x z}.

End RawMixin.
Section ClassDef.

Record class_of T := Class {mixin : mixin_of T}.

Structure pack_type : Type := Pack {sort : Type; _ : mixin_of sort}.
Local Coercion sort : pack_type >-> Sortclass.

Variables (cT : pack_type).
Definition poset_struct := let: Pack _ c := cT return mixin_of cT in c.

Definition leq := mx_leq poset_struct.

End ClassDef.

Module Exports.
Coercion sort : pack_type >-> Sortclass.
Notation poset := pack_type.
Notation PosetMixin := Mixin.
Notation Poset T m := (@Pack T m).

Notation "x <== y" := (Poset.leq x y) (at level 70).

Section Laws.
Variable T : poset.

Lemma poset_refl (x : T) : x <== x.
Proof. by case: T x=>S [leq B R]. Qed.

Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Proof. by case: T x y=>S [l R A Tr] *; apply: (A). Qed.

Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
Proof. by case: T y x z=>S [l R A Tr] ? x y z; apply: (Tr). Qed.
End Laws.
End Exports.
End Poset.

Export Poset.Exports.

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

Section NatPoset.
Lemma nat_refl x : x <= x. Proof. by []. Qed.

Lemma nat_asym x y : x <= y -> y <= x -> x = y.
Proof. by move=>H1 H2; apply: anti_leq; rewrite H1 H2. Qed. 

Lemma nat_trans x y z : x <= y -> y <= z -> x <= z.
Proof. by apply: leq_trans. Qed.

Definition natPosetMixin := PosetMixin nat_refl nat_asym nat_trans.
Canonical natPoset := Eval hnf in Poset nat natPosetMixin.
End NatPoset.


Section PairPoset. 
Variable (A B : poset). 
Local Notation tp := (A * B)%type. 

Definition pair_leq (p1 p2 : tp) := p1.1 <== p2.1 /\ p1.2 <== p2.2.

Lemma pair_refl x : pair_leq x x.
Proof. by split; apply: poset_refl. Qed.

Lemma pair_asym x y : pair_leq x y -> pair_leq y x -> x = y.
Proof.
move: x y=>[x1 x2][y1 y2][/= H1 H2][/= H3 H4].
by congr (_, _); apply: poset_asym.
Qed.

Lemma pair_trans x y z : pair_leq x y -> pair_leq y z -> pair_leq x z.
Proof. 
move: x y z=>[x1 x2][y1 y2][z1 z2][/= H1 H2][/= H3 H4]; split=>/=.
- by apply: poset_trans H3.
by apply: poset_trans H4.
Qed.

Definition pairPosetMixin := 
  PosetMixin pair_refl pair_asym pair_trans.
Canonical pairPoset := Eval hnf in Poset tp pairPosetMixin.

End PairPoset.

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x), 
               (forall x, f1 x = f2 x) -> f1 = f2.

Section FunPoset. 
Variable (A : Type) (B : poset).
Local Notation tp := (A -> B). 

Definition fun_leq (p1 p2 : tp) := forall x, p1 x <== p2 x.

Lemma fun_refl x : fun_leq x x.
Proof. by move=>z; apply: poset_refl. Qed. 

Lemma fun_asym x y : fun_leq x y -> fun_leq y x -> x = y.
Proof. 
move=>H1 H2. apply: fext=>z; 
by apply: poset_asym; [apply: H1 | apply: H2]. 
Qed.

Lemma fun_trans x y z : fun_leq x y -> fun_leq y z -> fun_leq x z.
Proof. by move=>H1 H2 t; apply: poset_trans (H2 t). Qed.

Definition funPosetMixin := PosetMixin fun_refl fun_asym fun_trans.
Canonical funPoset := Eval hnf in Poset tp funPosetMixin.

End FunPoset.


(*******************************************************************)
(**                 * End of Exercices 2 *                         *)
(*******************************************************************)
