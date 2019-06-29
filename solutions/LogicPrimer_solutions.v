From mathcomp
Require Import ssreflect.

Require Classical_Prop.

Module LogicPrimer.

Import Classical_Prop.
Definition peirce_law := forall P Q: Prop, ((P -> Q) -> P) -> P.

(**
---------------------------------------------------------------------
Exercise [forall-distributivity]
---------------------------------------------------------------------

Formulate and prove the following theorem in Coq, which states the
distributivity of universal quantification with respect to implication:
\[
forall P Q, 
  [(forall x, P(x) => Q(x)) => ((forall y, P(y)) => forall z, Q(z))]
\]

Be careful with the scoping of universally-quantified variables
and use parentheses to resolve ambiguities!
*)

Theorem all_imp_ist A (P Q: A -> Prop): 
  (forall x: A, P x -> Q x) -> (forall y, P y) -> forall z, Q z. 
Proof. by move=> H1 H2 z; apply: H1; apply: H2. Qed.

(**
---------------------------------------------------------------------
Exercise [Or-And distributivity]
---------------------------------------------------------------------
Prove the following theorems.
*)

Theorem or_distributes_over_and P Q R: 
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
split.
- case; first by split; [left | left].
- by case=>q r; split; [right | right].
intuition.
Qed.

Theorem or_distributes_over_and_2 P Q R :
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
case; case=>q; first by left.
case=>[p|r]; first by left.
right; split=>//.
Qed.

(**
---------------------------------------------------------------------
Exercise [Home-brewed existential quantification]
---------------------------------------------------------------------

Let us define our own version [my_ex] of the existential quantifier
using the SSReflect notation for constructors: *)

Inductive my_ex A (S: A -> Prop) : Prop := my_ex_intro x of S x.

(** You invited to prove the following goal, establishing the
equivalence of the two propositions. *)

Goal forall A (S: A -> Prop), my_ex A S <-> exists y: A, S y.
Proof.
move=> A S; split.
- by case=> x Hs; exists x.
by case=>y Hs; apply: my_ex_intro Hs.
Qed.
 
(** 
Hint: the propositional equivalence [<->] is just a conjunction of
two implications, so proving it can be reduced to two separate goals
by means of [split] tactics.
*)

(**
---------------------------------------------------------------------
Exercise [Distributivity of existential quantification]
---------------------------------------------------------------------
Prove the following theorem.
*)

Theorem dist_exists_or (X : Type) (P Q : X -> Prop):
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
split; first by case=>x; case=>H; [left | right]; exists x=> //.
by case; case=>x H; exists x; [left | right].
Qed.

(**
---------------------------------------------------------------------
Exercise [Two equals three]
---------------------------------------------------------------------
Prove the following  theorem. Can you explain the proof?
*)

Theorem two_is_three A: (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
Proof.
by case=>x H; apply: H.
Qed.

(**
---------------------------------------------------------------------
Exercise [Dyslexic implication and contraposition]
---------------------------------------------------------------------

The "dyslexic" implication and contrapositions are the following
propositions. 
*)

Definition dys_imp (P Q: Prop) := (P -> Q) -> (Q -> P).
Definition dys_contrap (P Q: Prop) := (P -> Q) -> (~P -> ~Q).

(**
These propositions are inhabited, as otherwise one, given a proof of
any of them, would be able to construct a proof of [False]. You are
invited to deomnstrate it by proving the following statements.
*)

Theorem di_false: (forall P Q: Prop, dys_imp P Q) -> False.
Proof. by move/(_ _ True); apply. Qed.

Theorem dc_false: (forall P Q: Prop, dys_contrap P Q) -> False.
Proof. by move=>H; apply: (H False True)=>//. Qed.

(**
---------------------------------------------------------------------
Exercise [Irrefutability of the excluded middle]
---------------------------------------------------------------------

Proof the following theorem that states that the assumption of the
falsehood of the excluded middle leads to inconsistencies, as is
allows one to derive [False].
*)

Theorem excluded_middle_irrefutable: forall (P : Prop), ~~(P \/ ~ P).
Proof.
move=>P H. 
apply: (H); right=>p.
by apply: H; left.
Qed.

(**
---------------------------------------------------------------------
Exercise [Equivalence of classical logic axioms]
---------------------------------------------------------------------

Prove that the following five axioms of the classical are equivalent.

*)

Definition peirce := peirce_law.
Definition double_neg := forall P: Prop, ~ ~ P -> P.
Definition excluded_middle := forall P: Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~ ( ~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop, (P -> Q) -> (~P \/ Q).

Lemma peirce_dn: peirce -> double_neg.
Proof. by move=>H P Hn; apply: (H _ False)=> /Hn. Qed.

Lemma dn_em : double_neg -> excluded_middle.
Proof. 
rewrite /double_neg /excluded_middle=> Dn P. 
apply: (Dn (P \/ ~ P))=>H1; apply: (H1).
by left; apply: (Dn)=> H2; apply: H1; right.
Qed.

Lemma em_dmnan: excluded_middle -> de_morgan_not_and_not.
Proof.
rewrite /excluded_middle /de_morgan_not_and_not=> H1 P Q H2.
suff: ~P -> Q.
- move=>H3. move: (H1 P); case=>//X; first by left. 
  by right; apply: H3. 
move=> Pn.
move: (H1 Q); case=>// Qn.
suff: False=>//; apply: H2; split=>//.
Qed.

Lemma dmnan_ito : de_morgan_not_and_not -> implies_to_or.
Proof.
rewrite /de_morgan_not_and_not /implies_to_or=> H1 P Q Hi.
suff: ~P \/ P.
case=>//; first by left.
- by move/ Hi; right.
move: (H1 (~P) P)=> H2; apply: H2; case=> Hp p.
suff: (P -> False) \/ False by case=>//.
by apply: H1; case.
Qed.

Lemma ito_peirce : implies_to_or -> peirce.
Proof.
rewrite /peirce /peirce_law /implies_to_or=> H1 P Q H2.
have X: P -> P by [].
move: (H1 P P) =>/(_ X); case=>{X}// Pn.
by apply: (H2)=>p. 
Qed.

(**

Hint: Use [rewrite /d] tactics to unfold the definition of a value [d]
 and replace its name by its body. You can chain several unfoldings by
 writing [rewrite /d1 /d2 ...]  etc.

Hint: To facilitate the forward reasoning by contradiction, you can
 use the SSReflect tactic [suff: P], where [P] is an arbitrary
 proposition. The system will then require you to prove that [P]
 implies the goal _and_ [P] itself.

Hint: Stuck with a tricky proof? Use the Coq [admit] tactic as a
 "stub" for an unfinished proof of a goal, which, nevertheless will be
 considered completed by Coq. You can always get back to an admitted
 proof later.

*)


(**
---------------------------------------------------------------------
Exercise [Inifinitary de Morgan laws]
---------------------------------------------------------------------

Prove the following implication analogous to the Morgan law for
conjunctions  and disjunctions.

*)

Theorem not_forall_exists A (P : A -> Prop): 
  (forall x: A, P x) -> ~(exists y: A, ~ P y).
Proof.
by move=>H G; case: G=>y G; apply: G; apply: H.
Qed.

(**

Then, prove that the assumption of the excluded middle axiom allows one to
establish the implication from the negation of (exists) to (forall).

*)

Theorem not_exists_forall :
  excluded_middle -> forall (X: Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
move=> Em X P H x; rewrite /excluded_middle in Em.
move: (Em (P x)); case=>// => H1.
by suff: False =>//; apply:H; exists x. 
Qed.


End LogicPrimer.
