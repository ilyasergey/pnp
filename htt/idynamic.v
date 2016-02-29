From mathcomp.ssreflect
Require Import ssreflect ssrfun.
Require Import Eqdep prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*************************************************************************)
(* A new variant of dynamic type, which doesn't directly quantify over a *)
(* type. Rather, we quantify over an index I and a function sort : I ->  *)
(* Type, which determines the type. By choosing I = Type and sort = id,  *)
(* we recover the old dynamic.                                           *)
(*                                                                       *)
(* The new dynamic makes it possible to produce small dynamic types by   *)
(* choosing the index I to be the type of codes. Hence, this approach is *)
(* more flexible when compared to the old type dynamic.                  *)
(* Also, it seems we don't need jmeq on pairs                            *)
(*************************************************************************)

(* Eventually get rid of the old dynamic, and work with this new type *)
(* But for now, to avoid conflict, I'll call this one idynamic, for   *)
(* indexed dynamic *)

Section IndexedDynamic.
Variable (I : Type) (sort : I -> Type).

Structure idynamic := idyn (A : I) of sort A.

Definition idyn_tp (x : idynamic) : I := let: idyn A _ := x in A.

Definition idyn_val (x : idynamic) : sort (idyn_tp x) :=
  let: idyn _ v := x in v.

Lemma idyn_eta (x : idynamic) : idyn (idyn_val x) = x.
Proof. by case: x. Qed.

Lemma idyn_injT (A1 A2 : I) (v1 : sort A1) (v2 : sort A2) :
         idyn v1 = idyn v2 -> A1 = A2.
Proof. by case. Qed.

Lemma idyn_inj (A : I) (v1 v2 : sort A) : idyn v1 = idyn v2 -> v1 = v2.
Proof. by case=>H; apply: inj_pairT2 H. Qed.

Definition icoerce A B (v : sort A) : A = B -> sort B :=
  [eta eq_rect A [eta sort] v B].

Lemma ieqc A (v : sort A) (pf : A = A) : icoerce v pf = v.
Proof. by move: pf; apply: Streicher_K. Qed.

Definition ijmeq A B (v1 : sort A) (v2 : sort B) :=
  forall pf, icoerce v1 pf = v2.

Lemma ijmeq_refl A (v : sort A) : ijmeq v v.
Proof. by move=>pf; rewrite ieqc. Qed.

Hint Resolve ijmeq_refl.

Lemma ijmE A (v1 v2 : sort A) : ijmeq v1 v2 <-> v1 = v2.
Proof. by split=>[|->]; first by move/(_ (erefl _)). Qed.

Lemma idynE (A1 A2 : I) (v1 : sort A1) (v2 : sort A2) :
        A1 = A2 -> ijmeq v1 v2 -> idyn v1 = idyn v2.
Proof. by move=>E; rewrite -{A2}E in v2 *; move/ijmE=>->. Qed.

End IndexedDynamic.

Prenex Implicits idyn_tp idyn_val idyn_injT idyn_inj.

Implicit Arguments icoerce [I A B].

Hint Resolve ijmeq_refl.



