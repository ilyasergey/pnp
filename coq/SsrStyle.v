(** %\chapter{Inductive Reasoning in SSReflect}
\label{ch:ssrstyle}
% *)

(* begin hide *)
Module SsrStyle.
(* end hide *)

(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing first %\texttt{{first}}% *)
(** printing last %\texttt{{last}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)


(** 

In the previous chapter we made an acquaintance with the main concepts
of constructive logic, Coq and SSReflect. However, the proofs we have
seen so far are mostly done by case analysys, application of
hypotheses and various forms of rewriting. In this chapter we will
consider in more details the proofs that employ inductive reasoning as
their main component. We will see how such proofs are typically
structure in SSReflect, so the corresponding scripts would become very
concise and yet readable and maintainable. We will also learn a few
common tricks that help to adapt the induction hypothesis for the
goal.

In the rest of the chapter we will be constantly relying on a series
of standard SSReflect modules, such as [ssrbool], [ssrnat] and
[eqtype], which we import right away.

*)

Require Import ssreflect ssrbool ssrnat eqtype.

(** 

%\section{Structuring the proof scripts}%

An important part of the proof process is keeping to an established
proof layout, which helps to maintain the proofs readable and restore
the intuition dribing the prover's hand.  SSReflect offers a number of
syntactic primitives that help to maintain such a layout, and in this
section we give a short overview of them. As usual, the SSReflect
reference manual%~\cite{Gontier-al:TR}% (Chapter 6) provides an
exhaustive formal definition of each primitive's semantics, so we will
just cover the base cases here, hoping that the subsequent proof will
provide more intuition on typical use-cases.

** Bullets and terminators

Typically the proofs proceeding by induction and case analysis require
to prove several goals, one by one in a sequence picked by the system.
It is considered to be a good practice to indent the subgoals (except
for the last one) whene there are several to prove. For instance, let
us consider the following almost trivial lemma:

*)

Lemma andb_true_elim b c: b && c -> c = true.

(**

Indeed, the reflection machinery presented in
%Section~\ref{sec:reflect} of Chapter~\ref{ch:boolrefl}%, makes this
proof to be a one liner ([by case/andP.]). However, for the sake of
demonstration, let us not appeal to it this time and do the proof as
it would be done in traditional Coq style: by mere case analysis.

 *)

Proof.
case: c.

(** 
[[
true = true

subgoal 2 (ID 15) is:
 b && false -> false = true
]]

Case analysis on [c] (which is firs moved to the bottom to become an
assumption) immediately gives us two goals to prove. Each of them can
be subsequently proved by the _inner_ cases analysis on [b], so we do,
properly indenting the goals.
 *)

- by case: b.

(** 

The proof script above successfully solves the first goal, which is
ensured by the _terminator_ tactical %\index{terminators}\ssrtl{by}%
[by], which we have seen previously. More precisely, [by tac.] first
runs the script [tac] and then applies a number of simplifications and
discriminations to see if the proof can be completed. If the current
goal is solved, [by tac.] simply terminates and proceeds to the next
goal; otherwise it reports a proof script error. Alternative
equivalent uses of the same principle would be [tac; by [].] or [tac;
done], %\ssrt{done}%, which do exactly the same. 

Notice that the first goal was indented and preceded by the _bullet_
[-]. %\index{bullets}% The bullet token, preceding a tactic
invocation, has no operational effect to the proof and servers solely
for the readability purposes. Alternative forms of tokens are
%\texttt{+}% and %\texttt{*}%.

** Selectors and discharging subgoals

Let us restart this proof and show an alternative way to structure the
proof script, which should account for multiple cases.

*)

Restart.
case: c; first by [].

(**

[[
  b : bool
  ============================
   b && false -> false = true
]]


%\index{selectors}%
Now, right after case-analysing on [c], the proof script specifies
that the _first_ of the generated subgoals should be solved using [by
[].]. In this case [first] is called _selector_, and its counterpart
[last] would specify that the last goal should be taken care of
instead, before proceeding.

Finally, if several simple goals can be foreseen as a result of case
analysis, Coq provides a convenient way to discharge them in a
structured way using %\ssrtl{[|...|]}% the [[|...|]] tactical:

*)

Restart.
case:c; [by [] | by case: b].

(** 

The script above solves the first generated goal using [by []], and
then solves the second one via [by case: b].

*)

(** 

** Iteration and alternatives

Yet another possible way to prove the statement of our subject lemma
is by employing Coq/SSReflect's _repetition_ tactical
[do]%\ssrtl{do}%. The script of the form [do !tac.] tries to apply the
tactic [tac] as many times as possible, as long as new goals are
generated or no more goals is left to prove.%\footnote{Be careful,
though, as such proof script might never terminate is more and more
new goals will be generated.  That said, while Coq itselfs enjoys the
strong normalization property (i.e., the programs in it always
terminate), its tactic meta-language is genuinely Turing-complete, so
the tactics, while constructing Coq programs/proofs, might never in
fact terminate. Specifying the behavior of tactics and their possible
effects (including non-termination and failures) is a topic of an
ungoing active
research~\cite{Ziliani-al:ICFP13,Stampoulis-Shao:ICFP10}.}% The
[do]-tactical can be also combined with the [[|...|]] tactical, so it
will try to apply all of the enumerated tactics as alternatives. The
following script finishes the proof of the whole lemma.


*)

Restart.
by do ![done | apply: eqxx | case: b | case: c].

(** 

Notice that we have added two tactics into the alternative list,
[done] and [apply: eqxx], which were deemed to fail. The script,
nevertheless, has succeeded, as the remaining two tactics, [case: b]
and [case: c], did all the job. Lastly, notice that the [do]-tactical
can be specified _how many_ times should it try to run each tactic
from the list by using the restricted form [do n!tac], where [n] is
the number of attempts. The lemma above could be completed by the
script of the form [by do 2![...]] with the same list of alternatives.

*)

Qed.

(** 

%\section{Inductive predicates that should be functions}%

It has been already discussed in this manuscript that, even though, a
lot of interesting propositions are inherently undecidable and should
be, therefore, represented in Coq as instances of the sort [Prop], one
should strive to implement as many of _decidable_ propositions as
possible as [bool]-returning function. Such "computational" approach
to the propositions turns out to pay off drastically in the long-term
persepective, as most of the usual proof burdent will be carried out
by Coq's computational component. In this section we will browse
through a series of predicates defined both as inductive datatypes and
boolean functions and compare the proofs of various properties stated
over the alternative representations.

*)

(** 

Let's have a look at this hell below:

*)

Inductive isZero : nat -> Prop := IsZero : isZero 0.

Theorem blah: isZero 1 -> False.
Proof.
move=> z.
move: (isZero_ind (fun n => if n is 0 then True else False))=> Z.
by apply (Z I 1).
Qed.

Inductive evenP1 n : Prop :=
  Even01 of n = 0 | EvenSs1 m of n = m.+2 & evenP1 m.

Fixpoint evenb n := if n is n'.+2 then evenb n' else n == 0.

Lemma even_4: evenb 4.
Proof. done. Qed.

Theorem even_3_contra: ~evenb 3.
Proof. done. Qed.

(* TODO: How to build induction on recursive function? *)
Lemma evenb_plus m n : evenb m -> evenb n -> evenb (m + n).
Proof.
(* Generalize all but the second occurrence of [m]. *)
elim: m {-2}m (leqnn m)=>[|m IH]; case=>//.
by case=>// m' /ltnW /IH.
Qed.

(*Proof by induction on the rule (for evenP) *)
Lemma evenP1_plus n m : evenP1 n -> evenP1 m -> evenP1 (n + m).
Proof.
elim=>//n'; first by move=>->; rewrite add0n.
move=> m'->{n'} H1 H2 H3; rewrite addnC !addnS addnC.
by apply: (EvenSs1 (m' + m).+2 (m' + m))=>//; apply: H2.
Qed.


Lemma evenP1_contra n : evenP1 (n + 1 + n) -> False.
Proof.
elim: n=>//[| n Hn].
- by rewrite addn0 add0n; case=>//.
rewrite addn1 addnS addnC !addnS; case=>//.
move=>m /eqP; rewrite !eqSS; move/eqP=><-.
by rewrite addnC addn1 addnS in Hn.
Qed.

Lemma evenb_contra n: evenb (n + 1 + n) -> False.
Proof. by elim: n=>[|n IH] //; rewrite addSn addnS. Qed.

(**

%\section{Inductive predicates that cannot be avoided}%

*)

Inductive beautiful (n: nat) : Prop :=
  b_0 of n = 0
| b_3 of n = 3
| b_5 of n = 5
| b_sum n' m' of beautiful n' & beautiful m' & n = n' + m'.

Theorem eight_is_beautiful: beautiful 8.
Proof.
apply: (b_sum _ 3 5)=>//. 
- by apply: b_3.
by apply b_5.
Qed.

Theorem b_times2 n: beautiful n ->  beautiful (n * 2).
Proof.
elim=>m.
- by move=>->; apply:b_0.
- move=>->; rewrite mulnC mul2n -addnn. 
  by apply: (b_sum _ 3 3)=>//=; apply: b_3=>//=.
- move=>->; rewrite mulnC mul2n -addnn. 
  by apply: (b_sum _ 5 5)=>//=; apply: b_5=>//=.
- move=> n' m' H1 H2 H3 H4=>->{m}.
rewrite mulnC mul2n -addnn.
rewrite addnAC addnA addnn -addnA addnn.
apply: (b_sum _ n'.*2 m'.*2)=>//.
 - by rewrite mulnC mul2n in H2.
by rewrite mulnC mul2n in H4.
Qed.

Theorem b_timesm n m: beautiful n ->  beautiful (m * n).
Proof.
elim:m=>[_|m Hm Bn]; first by rewrite mul0n; apply: b_0.
move: (Hm Bn)=> H1.
by rewrite mulSn; apply: (b_sum _ n (m * n))=>//.
Qed.

Lemma one_not_beautiful n:  n = 1 -> ~ beautiful n.
Proof.
move=>E H; elim: H E=>n'; do?[by move=>->].
move=> n1 m' _ H2 _ H4->{n' n}.
case: n1 H2=>// n'=> H3.
by case: n' H3=>//; case.
Qed.


Inductive gorgeous (n: nat) : Prop :=
  g_0 of n = 0
| g_plus3 m of gorgeous m & n = m + 3
| g_plus5 m of gorgeous m & n = m + 5.

Require Import ssrbool.

Fixpoint gorgeous_b (n: nat) : bool := 
 match n with 
 | 0 => true
 | m.+3 => (gorgeous_b m) || 
              (match m with 
                m'.+2 => gorgeous_b m'
              | _ => false
              end)
 | _ => false
 end.

Theorem gorgeous_plus13 n:
  gorgeous n -> gorgeous (n + 13).
Proof.
move=> H.
apply: (g_plus5 _ (n + 8))=>//; last by rewrite -addnA; congr (_ + _).
apply: (g_plus5 _ (n + 3)); last by rewrite -addnA; congr (_ + _).
by apply: (g_plus3 _ n). 
Qed.

Require Import eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal forall n m, n + 2 == m + 1 + 1 -> n == m.
Proof.
move=> n m.
by rewrite -addnA eqn_add2r. 
Qed.

(*
Theorem gorgeous_plus13' n:
  gorgeous_b n -> gorgeous_b (n + 13).
Proof.
elim: n=>// n IH.
simpl in IH.
rewrite addSnnS. 
simpl.
rewrite addnC /= in IH.
rewrite addnC /=.
move=>
simpl.
case: n=>//=.  simpl.
move=>n.
*)

Theorem beautiful_gorgeous (n: nat) : beautiful n -> gorgeous n.
Proof.
elim=>n'{n}=>//.
- by move=>->; apply g_0.
- by move=>->; apply: (g_plus3 _ 0)=>//; apply g_0.
- by move=>->; apply: (g_plus5 _ 0)=>//; apply g_0.
move=> n m H1 H2 H3 H4->{n'}. 
elim: H2; first by move=>_->; rewrite add0n.
by move=> n' m' H5 H6->; rewrite addnAC; apply: (g_plus3 _ (m' + m)).
by move=> n' m' H5 H6->; rewrite addnAC; apply: (g_plus5 _ (m' + m)).
Qed.

Theorem g_times2 (n: nat): gorgeous n -> gorgeous (n * 2).
Proof.
rewrite muln2.
elim=>{n}[n Z|n m H1 H2 Z|n m H1 H2 Z]; subst n; first by rewrite double0; apply g_0.
- rewrite doubleD -(addnn 3) addnA.
  by apply: (g_plus3 _ (m.*2 + 3))=>//; apply: (g_plus3 _ m.*2)=>//.
rewrite doubleD -(addnn 5) addnA.
by apply: (g_plus5 _ (m.*2 + 5))=>//; apply: (g_plus5 _ m.*2)=>//.
Qed.


(**

%\section{Generalizing induction hypotheses}%

TODO: Example from Section 9.3.1 from Coq'Art book.

*)

Fixpoint div2 (n: nat) := if n is p.+2 then (div2 p).+1 else 0.

Lemma div2orb n : div2 (n.+2) = (div2 n).+1.
Proof. by case: n=>//. Qed.

Lemma div2_le n: div2 n <= n.
Proof.
suff: (div2 n <= n) /\ (div2 n.+1 <= n.+1) by case.
elim: n=>//[n].
case: n=>// n; rewrite !div2orb; case=>H1 H2.
split=>//. Search _ (_ < _.+1). 
rewrite -ltnS in H1.
by move: (ltn_trans H1 (ltnSn n.+2)).
Qed.




(**

TODO: show a different induction principle

%\section{Working with SSReflect libraries}%

TODO: General naming policies.

*)


(* begin hide *)
End SsrStyle.
(* end hide *)


