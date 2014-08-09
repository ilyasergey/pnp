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
Proof. case: U x y=>tp [v j z Cj Aj Uj /= Mj inv f]; apply: Mj. Qed.

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
