(* Dirichlet *)
Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Set Implicit Arguments. 
Unset Strict Implicit. 
Set Automatic Coercions Import.
Unset Printing Implicit Defensive. 

Section Dirichlet.
Variable A : eqType.

Fixpoint has_repeat (xs : seq A) :=
  if xs is x :: xs' then (x \in xs') || has_repeat xs' else false.

Lemma dirichlet xs1 xs2 :
        size xs2 < size xs1 -> {subset xs1 <= xs2} -> has_repeat xs1.
Proof.
elim: xs1 xs2=>[|x xs1 IH] xs2 //= H1 H2. 
pose xs2' := filter (predC (pred1 x)) xs2.
case H3: (x \in xs1) => //=.
apply: (IH xs2'); last first.
- move=>y H4; move: (H2 y); rewrite inE H4 orbT mem_filter /=.
  by move => -> //; case: eqP H3 H4 => // ->->. 
rewrite ltnS in H1; apply: leq_trans H1. 
rewrite -(count_predC (pred1 x) xs2) -count_filter.
rewrite -addn1 addnC leq_add2r -has_count.
by apply/hasP; exists x=>//=; apply: H2; rewrite inE eq_refl.
Qed.

End Dirichlet.
