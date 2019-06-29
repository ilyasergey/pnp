From mathcomp
Require Import ssreflect ssrfun eqtype ssrnat ssrbool.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
---------------------------------------------------------------------
Exercise [Reflecting exclusive disjunction]
---------------------------------------------------------------------

Let us define a propositional version of the _exclusive or_ predicate
as well as its boolean version (in a curried form, so it takes just
one argument and returns a function):

*)

Definition XOR (P Q: Prop) := (P \/ Q) /\ ~(P /\ Q).

Definition xorb b := if b then negb else fun x => x.

(** 

Now, prove the following _generalized_ reflection lemma [xorP_gen] and
its direct consequence, the usual reflection lemma [xorP]:

Hint: recall that the _reflect_ predicate is just a rewriting rule, so
one can perform a case analysis on it.

*)

Lemma xorP_gen (b1 b2 : bool)(P1 P2: Prop): 
  reflect P1 b1 -> reflect P2 b2 -> reflect (XOR P1 P2) (xorb b1 b2).
Proof.
case=>H1; case=>H2; constructor; rewrite /XOR. 
- by case; case=>H; apply.
- split; first by left. 
  by case=>_ H; apply: H2.
- split; first by right.
  by case=>H _; apply: H1.
- intuition.
Qed.

Lemma xorP (b1 b2 : bool): reflect (XOR b1 b2) (xorb b1 b2).
(* begin hide *)
by apply: xorP_gen; case:b1=>//=; case:b2=>//=; constructor.
Qed.

(** 
---------------------------------------------------------------------
Exercise [Alternative formulation of exclusive disjunction]
---------------------------------------------------------------------

Let us consider an alternative version of exclusive or, defined by
means of the predicate [XOR']:

*)

Definition XOR' (P Q: Prop) := (P /\ ~Q) \/ (~P /\ Q).

(** 

Prove the following equivalence lemma between to versions of [XOR]:

*)

Lemma XORequiv P Q: XOR P Q <-> XOR' P Q.
Proof.
split. 
- case; case=>[p|q] H. 
  - by left; split=>// q; apply: H.
  by right; split=>// p; apply H.
case; case=>p q.
- split=>[| H]; first by left.
  by apply: q; case: H.
split; first by right. 
by case=>/p.
Qed.

(** 
The final step is to use the equivalence we have just proved in order
to establish an alternative version of the reflective correspondence
of exclusive disjunction.

Hint: use the [Search] machinery to look for lemmas that might help to
leverage the equivalence between two predicates and make the
following proof to be a one-liner.

*)

Lemma xorP' (b1 b2 : bool): reflect (XOR' b1 b2) (xorb b1 b2).
Proof.
by apply: (equivP (xorP b1 b2) (XORequiv _ _)).
Qed.
 
(** 
---------------------------------------------------------------------
Exercise [Reasoning with boolean xor]
---------------------------------------------------------------------

Unsurprisingly, every statement about exclusive or, e.g., its
commutativity and associativity, is extremely easy to prove when it is
considered as a boolean function. Demonstrate it by proving the
following lemmas in one line each.

*)

Lemma xorbC (b1 b2: bool) : (xorb b1 b2) = (xorb b2 b1). 
Proof. by case: b1; case: b2=>//. Qed.

Lemma xorbA (b1 b2 b3: bool) : (xorb (xorb b1 b2) b3) = (xorb b1 (xorb b2 b3)). 
Proof. by case: b1; case: b2; case: b3=>//. Qed.

(** 

It is also not difficult to prove the propositional counterparts of
the above lemmas for decidable propositions, reflected by them, hence
the following exercise.

*)

(**
---------------------------------------------------------------------
Exercise [Commutativity and associativity of specialized XOR]
---------------------------------------------------------------------

Prove the following specialized lemmas for decidable propositions
represented y booleans (without using the [intuition] tactic):

*)

Lemma xorCb (b1 b2: bool) : (XOR b1 b2) <-> (XOR b2 b1). 
Proof.
by split; move/xorP; rewrite xorbC; move/xorP.
Qed.

Lemma xorAb (b1 b2 b3: bool) : (XOR (XOR b1 b2) b3) <-> (XOR b1 (XOR b2 b3)). 
Proof.
by rewrite /XOR; case: b1; case: b2; case: b3; intuition.
Qed.

(** 

Hint: in the proof of [xorAb] the generalized reflection lemma
[xorP_gen] might come in handy.

Hint: A redundant assumption [H] in the context can be erased by
typing [clear H] or [move => {H}]. The latter form can be combined
with any bookkeeping sequence, not only with [move] tactics.

Hint: The Coq's embedded tactic [intuition] can be helpful for
automatically solving goals in propositional logic.

*)

