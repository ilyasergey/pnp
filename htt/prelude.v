From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import pred.
Require Import Eqdep ClassicalFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*****************************)
(* Axioms and extensionality *)
(*****************************)

(* extensionality is needed for domains *)
Axiom pext : forall p1 p2 : Prop, (p1 <-> p2) -> p1 = p2.
Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

Lemma proof_irrelevance (P : Prop) (p1 p2 : P) : p1 = p2.
Proof. by apply: ext_prop_dep_proof_irrel_cic; apply: pext. Qed.

Lemma eta A (B : A -> Type) (f : forall x, B x) : f = [eta f].
Proof. by apply: fext. Qed.

Lemma ext A (B : A -> Type) (f1 f2 : forall x, B x) :
        f1 = f2 -> forall x, f1 x = f2 x.
Proof. by move=>->. Qed.

(*******************)
(* Setoid renaming *)
(*******************)

(* Setoid library takes up some important arrow notations *)
(* used by ssreflect and elsewhere; so we must rename *)
Ltac add_morphism_tactic := SetoidTactics.add_morphism_tactic.
Notation " R ===> R' " := (@Morphisms.respectful _ _ R R')
  (right associativity, at level 55) : signature_scope.

(***********)
(* Prelude *)
(***********)

(* often used notation definitions and lemmas that are *)
(* not included in the other libraries *)

Definition inj_pair2 := @inj_pair2.
Implicit Arguments inj_pair2 [U P p x y].
Prenex Implicits inj_pair2.

Lemma inj_sval A P : injective (@sval A P).
Proof.
move=>[x Hx][y Hy] /= H; move: Hx Hy; rewrite H=>*.
congr exist; apply: proof_irrelevance.
Qed.

Lemma svalE A (P : A -> Prop) x H : sval (exist P x H) = x.
Proof. by []. Qed.

(* rewrite rule for propositional symmetry *)
Lemma sym A (x y : A) : x = y <-> y = x.
Proof. by []. Qed.

(* inferrable reflexivity axiom *)
Definition erefli A (x : A) := erefl x.
Arguments erefli [A x].

(* selecting a list element *)
(* should really be in seq.v *)

Section HasSelect.
Variables (A : eqType) (p : pred A).

CoInductive has_spec (s : seq A) : bool -> Type :=
| has_true x of x \in s & p x : has_spec s true
| has_false of (all (predC p) s) : has_spec s false.

Lemma hasPx : forall s, has_spec s (has p s).
Proof.
elim=>[|x s IH] /=; first by apply: has_false.
rewrite orbC; case: IH=>/=.
- by move=>k H1; apply: has_true; rewrite inE H1 orbT.
case E: (p x)=>H; last by apply: has_false; rewrite /= E H.
by apply: has_true E; rewrite inE eq_refl.
Qed.

End HasSelect.

(***************************)
(* operations on functions *)
(***************************)

Lemma compA A B C D (h : A -> B) (g : B -> C) (f : C -> D) :
        (f \o g) \o h = f \o (g \o h).
Proof. by []. Qed.

Lemma compf1 A B (f : A -> B) : f = f \o id.
Proof. by apply: fext. Qed.

Lemma comp1f A B (f : A -> B) : f = id \o f.
Proof. by apply: fext. Qed.

Definition fprod A1 A2 B1 B2 (f1 : A1 -> B1) (f2 : A2 -> B2) :=
  fun (x : A1 * A2) => (f1 x.1, f2 x.2).

Notation "f1 \* f2" := (fprod f1 f2) (at level 42, left associativity).

(************************)
(* extension to ssrbool *)
(************************)

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").

Reserved Notation "[ \/ P1 , P2 , P3 , P4 & P5 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  &  P5 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.

Inductive or5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  Or51 of P1 | Or52 of P2 | Or53 of P3 | Or54 of P4 | Or55 of P5.
Inductive or6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  Or61 of P1 | Or62 of P2 | Or63 of P3 | Or64 of P4 | Or65 of P5 | Or66 of P6.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" := (or5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" := (or6 P1 P2 P3 P4 P5 P6) : type_scope.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 b6 : bool.
Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; constructor; try by case.
Qed.

Lemma or5P : reflect [\/ b1, b2, b3, b4 | b5] [|| b1, b2, b3, b4 | b5].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
by constructor; case.
Qed.

Lemma or6P : reflect [\/ b1, b2, b3, b4, b5 | b6] [|| b1, b2, b3, b4, b5 | b6].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
case b6; first by constructor; constructor 6.
by constructor; case.
Qed.

End ReflectConnectives.

Implicit Arguments and6P [b1 b2 b3 b4 b5 b6].
Implicit Arguments or5P [b1 b2 b3 b4 b5].
Implicit Arguments or6P [b1 b2 b3 b4 b5 b6].
Prenex Implicits and6P or5P or6P.


