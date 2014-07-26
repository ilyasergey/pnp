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

One can defined the fact that the only natural number which is equalt
to zero is the zero itself, as shown below:

*)


Inductive isZero (n: nat) : Prop := IsZero of n = 0.

(**

Naturally, such equality can be exploited to derived paradoxes, as the
following lemma shows:

*)

Lemma isZero_paradox: isZero 1 -> False.
Proof. by case. Qed.


(** 

However, the equality on natural numbers is, decidable, so the very
same definition can be rewritten as a function employing the boolean
equality [(==)] (see %Section~\ref{sec:eqrefl} of
Chapter~\ref{ch:boolrefl}%), which will make the proofs of paradoxes
even shorter than they already are:

*)

Definition is_zero n : bool := n == 0.

Lemma is_zero_paradox: is_zero 1 -> False.
Proof. done. Qed.

(** 

That is, instead of the unavoidable case-analysis with the first
[Prop]-based definition, the functional definition made Coq compute
the result for us, deriving the falsehood automatically.

The benefits of the computable definitions become even more obvious
when considering the next example, the predicate defining whether a
natural number is even or odd. Again, we define two versions, the
inductive predicate and a boolean function.

*)

Inductive evenP n : Prop :=
  Even0 of n = 0 | EvenSS m of n = m.+2 & evenP m.

Fixpoint evenb n := if n is n'.+2 then evenb n' else n == 0.

(** 

Let us now prove a simple property: that fact that [(n + 1 + n)] is
even leads to a paradox. We first prove it for the version defined in
[Prop].

*)

Lemma evenP_contra n : evenP (n + 1 + n) -> False.
Proof.
elim: n=>//[| n Hn]; first by rewrite addn0 add0n; case=>//.

(** 

We start the proof by induction on [n], which is triggered by [elim:
n].%\footnote{Remember that the [elim], \ssrt{elim} as most of other
SSReflect's tactics operates on the top assumption.}% The subsequent
two goals (for the zero and the successor cases) are then simplified
via %\texttt{//}% and the induction variable and hypothesis are given
the names [n] and [Hn], respectively, in the second goal (as described
in %Section~\ref{sec:naming-subgoals}%). Then, the first goal (the
[0]-case) is discharged by simplified the sum via two rewritings by
[addn0] and [add0n] lemmas from the [ssrnat] module and case-analysis
on the assumption of the form [evenP 1], which delivers the
contradiction.

The second goal is annoyingly trickier.

[[
  n : nat
  Hn : evenP (n + 1 + n) -> False
  ============================
   evenP (n.+1 + 1 + n.+1) -> False
]]

First, let us do some rewritings that make the hypothesis and the goal
look alike.%\footnote{Recall that% [n.+1] %stands for the
\emph{value} of the successor of% [n] %, whereas% [n + 1] % is a
function call, so the whole expression in the goal cannot be just
trivially simplified and requires some rewritings to be done.}% *)

rewrite addn1 addnS addnC !addnS. 
rewrite addnC addn1 addnS in Hn.

(**
[[
  n : nat
  Hn : evenP (n + n).+1 -> False
  ============================
   evenP (n + n).+3 -> False
]] 

Now, even though the hypothesis [Hn] and the goal are almost the same
module the natural "[(.+2)]-orbit" of the [evenP] predicate and some
rewritings, we cannot take an advantage of it right away, and instead
are required to case-analysed on the assumption of the form [evenP (n
+ n).+3]:


*)

case=>// m /eqP.

(**

[[
  n : nat
  Hn : evenP (n + n).+1 -> False
  m : nat
  ============================
   (n + n).+3 = m.+2 -> evenP m -> False
]]

Only now we can make use of the rewriting lemma to "strip off" the
constant summands from the equality in the assumption, so it could be
employed for brushing the goal, so it would match the hypothesis
exactly.

*)

by rewrite !eqSS; move/eqP=><-.
Qed.

(** 

Now, let us take a look at the proof of the same fact, but with the
computable version of the predicate [evenb].

*)

Lemma evenb_contra n: evenb (n + 1 + n) -> False.
Proof. 
elim: n=>[|n IH] //.

(** 
[[
  n : nat
  IH : evenb (n + 1 + n) -> False
  ============================
   evenb (n.+1 + 1 + n.+1) -> False
]]

In the case of zero, the proof by induction on [n] is automatically
carried out by computation, since [evenb 1 = false]. The inductive
step is not significantly more complicated, and it takes only two
rewriting to get it into the shape, so the computation of [evenb]
could finish the proof.

*)

by rewrite addSn addnS. 
Qed.

(** 

Sometimes, though, the value "orbits", which can be advantageous for
the proofs involving [bool]-returning predicates, might require a bit
trickier induction hypotheses than just the statement required to be
proved. Let us compare the two proofs of the same fact, formulated
with [evenP] and [evennb].

*)

Lemma evenP_plus n m : evenP n -> evenP m -> evenP (n + m).
Proof.
elim=>//n'; first by move=>->; rewrite add0n.

(** 

[[
  n : nat
  m : nat
  n' : nat
  ============================
   forall m0 : nat,
   n' = m0.+2 ->
   evenP m0 -> (evenP m -> evenP (m0 + m)) -> evenP m -> evenP (n' + m)
]]

The induction here is on the predicate [evenP], so the first case is
discharged by rewriting.

*)

move=> m'->{n'} H1 H2 H3; rewrite addnC !addnS addnC.

(**

[[
  n : nat
  m : nat
  m' : nat
  H1 : evenP m'
  H2 : evenP m -> evenP (m' + m)
  H3 : evenP m
  ============================
   evenP (m' + m).+2
]]



In order to proceed with the inductive case, again a few rewritings
are required.

*)

apply: (EvenSS _ _)=>//.

(**

[[
  n : nat
  m : nat
  m' : nat
  H1 : evenP m'
  H2 : evenP m -> evenP (m' + m)
  H3 : evenP m
  ============================
   evenP (m' + m)
]] 

The proof script is continued by explicitly applying the constructor
[EvenSS] of the [evenP] datatype. Notice the use of the wildcard
underscores %\index{wildcards}% in the application of [EvenSS]. Let us
check its type:

*)

Check EvenSS.

(** 
[[
EvenSS
     : forall n m : nat, n = m.+2 -> evenP m -> evenP n
]]

By using the underscores, we allowed Coq to _infer_ the two necessary
arguments for the [EvenSS] constructor, namely, the values of [n] and
[m]. The system was able to do it basing on the goal, which was
reduced by applying it. After the simplification and automatic
discharging the of the trivial subgoals (e.g., [(m' + m)+.2 = (m' +
m)+.2]) via the %\texttt{//}% tactical, the only left obligation can
be proved by applying the hypothesis [H2].

*)

by apply: H2.

Qed.

(** 

In this particular case, the resulting proof was quite
straightforward, thanks to the explicit equality [n = m.+2] in the
definition of the [EvenSS] constructor.

In the case of the boolean specification, though, the induction should
be done on the natural argument itself, which makes the first attempt
of the proof to be not entirely trivial.

*)

Lemma evenb_plus n m : evenb n -> evenb m -> evenb (n + m).
Proof.
elim: n=>[|n Hn]; first by rewrite add0n.

(** 
[[
  m : nat
  n : nat
  Hn : evenb n -> evenb m -> evenb (n + m)
  ============================
   evenb n.+1 -> evenb m -> evenb (n.+1 + m)
]]

The problem now is that, if we keep building the proof by induction on
[n] or [m], the induction hypothesis and the goal will be always
"mismatched" by one, which will prevent us finishing the proof using
the hypothesis. 

There are multiple ways to escape this vicious circle, and one of them
is to _generalize_ the induction hypothesis. To do so, let us restart
the proof.

*)

Restart.
move: (leqnn n).

(**

[[
  n : nat
  m : nat
  ============================
   n <= n -> evenb n -> evenb m -> evenb (n + m)
]]

Now, we are going to proceed with the proof by _selective_ induction
on [n], such that some of its occurrences in the goal will be a
subject of inductive reasoning (namely, the second one), and some
others will be left generalized (that is, bound by a forall-quantified
variable). We do so by using SSReflect's tactics [elim] with explicit
_occurrence selectors_.  %\index{occurrence selectors}%

*)

elim: n {-2}n.

(** 

[[
  m : nat
  ============================
   forall n : nat, n <= 0 -> evenb n -> evenb m -> evenb (n + m)

subgoal 2 (ID 860) is:
 forall n : nat,
 (forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)) ->
 forall n0 : nat, n0 <= n.+1 -> evenb n0 -> evenb m -> evenb (n0 + m)
]]

The same effect could be achieved by using [elim: n {1 3 4}n], that
is, indicating which occurrences of [n] _should_ be generalized,
instead of specifying, which ones should not (as we did by means of
[{-2}n]).

Now, the first goal can be solved by case-analysis on the top
assumption (that is, [n]).

*)

- by case=>//.

(** 

For the second goal, we first move some of the assumptions to the context.

*)

move=>n Hn. 

(** 
[[
  m : nat
  n : nat
  Hn : forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)
  ============================
   forall n0 : nat, n0 <= n.+1 -> evenb n0 -> evenb m -> evenb (n0 + m)
]]

And then perform the case-analysis on [n0] in the goal, which results
in two goals, one of which is automatically discharged.

*)

case=>//.

(** 

[[
  m : nat
  n : nat
  Hn : forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)
  ============================
   forall n0 : nat, n0 < n.+1 -> evenb n0.+1 -> evenb m -> evenb (n0.+1 + m)
]]

Doing _one more_ case analysis will adde one more [1] to the induction
variable [n0], which will bring us to the desired [(.+2)]-orbit.

*)

case=>// n0.

(**
[[
  m : nat
  n : nat
  Hn : forall n0 : nat, n0 <= n -> evenb n0 -> evenb m -> evenb (n0 + m)
  n0 : nat
  ============================
   n0.+1 < n.+1 -> evenb n0.+2 -> evenb m -> evenb (n0.+2 + m)
]]

The only thing left to do is to tweak the top assumption (by relaxing
the inequality via the [ltnW] lemma), so we could apply the induction
hypothesis [Hn].

*)

by move/ltnW /Hn=>//.
Qed.

(** 

It is fair to notice that this proof was far less direct that one
could expect, but it taught us an important trick---selective
generalization of the induction hypothesis. In particular, by
introducing an extra assumption [n <= n] in the beginning, we later
exploited it, so we could apply the induction hypothesis, which was
otherwise general enough to match the ultimate goal at the last step
of the proof.

*)

(**

** Eliminating assumptions with a custom induction hypothesis

The functions like [evenb], with specific value orbits, are not
particularly uncommon, and it is useful to understand the key
induction principles to reason about them. In particular, the above
discussed proof could have been much more straightforward if we first
proved a different induction principle [nat2_ind] for natural numbers.

*)

Lemma nat2_ind (P: nat -> Prop): 
  P 0 -> P 1 -> (forall n, P n -> P (n.+2)) -> forall n, P n.
Proof.
move=> H0 H1 H n. 

(** 
[[
  P : nat -> Prop
  H0 : P 0
  H1 : P 1
  H : forall n : nat, P n -> P n.+2
  n : nat
  ============================
   P n
]]

Unsurprisingly, the proof of this induction principle follows the same
pattern as the proof of [evenb_plus]---generalizing the hypothesis. In
this particular case, we generalize it in the way that it would
provide an "impedance matcher" between the 1-step of the defaul
induction on natural numbers and the 2-step induction in the
hypothesis [H]. We show that for the proof it is sufficient to
establish [(P n /\ P (n.+1))]:

*)

suff: (P n /\ P (n.+1)) by case.

(** 

The rest of the proof proceeds by the standard induction on [n].

*)

by elim: n=>//n; case=> H2 H3; split=>//; last by apply: H.
Qed.

(** 

Now, since the new induction principle [nat2_ind] exactly matches the
2-orbit, we can directly employ it for the proof of the previous result.

*)

Lemma evenb_plus' n m : evenb n -> evenb m -> evenb (n + m).
Proof.
by elim/nat2_ind : n.
Qed.

(** 

Notice that we used the version of the [elim] tactics with specific
_elimination view_ [nat2_ind], different from the default one, which
is possible using the view tactical %\texttt{/}\ssrtl{/}\ssrt{elim}%.
%\index{elimination view}% In this sense, the "standard induction"
[elim: n] would be equivalent to [elim/nat_ind: n].

%\begin{exercise}%

Let us define the binary division function [div2] as follows.

*)


Fixpoint div2 (n: nat) := if n is p.+2 then (div2 p).+1 else 0.

(** 

Prove the following lemma directly, _without_ using the [nat2_ind]
induction principle.

*)

(* begin hide *)
Lemma div2orb n : div2 (n.+2) = (div2 n).+1.
Proof. by case: n=>//. Qed.
(* end hide *)

Lemma div2_le n: div2 n <= n.
(* begin hide *)
Proof.
suff: (div2 n <= n) /\ (div2 n.+1 <= n.+1) by case.
elim: n=>//[n].
case: n=>// n; rewrite !div2orb; case=>H1 H2.
split=>//. Search _ (_ < _.+1). 
rewrite -ltnS in H1.
by move: (ltn_trans H1 (ltnSn n.+2)).
Qed.
(* end hide *)

(** 

%\end{exercise}%

* Inductive predicates that cannot be avoided

Although formulating predicates as boolean functions is often
preferable, it is not always trivial to do. Sometimes, it is much
simpler to come up with an inductive predicate, which witnesses the
property of interest. As an example for such property, let us consider
the notion of _beautiful_ and _gorgeous_ numbers, which we borrow from
%Pierce et al.'s electronic book~\cite{Pierce-al:SF} (Chapter
\textsf{MoreInd})%.

*)

Inductive beautiful (n: nat) : Prop :=
| b_0 of n = 0
| b_3 of n = 3
| b_5 of n = 5
| b_sum n' m' of beautiful n' & beautiful m' & n = n' + m'.

(** 

The number is beautiful %\index{beautiful numbers}% if it's either
[0], [3], [5] or a sum of two beautiful numbers. Indeed, there are
many ways to decompose some numbers into the sum $3 \times n + 5
\times n$.%\footnote{In fact, the solution of this simple Diophantine 
equation are all natural numbers, greater than $7$.}% Encoding a
function, which checks whether a number is beautiful or not, although,
not impossible, is not entirely trivial (and, in particular, it's not
trivial to prove the correctness of such function with respect to the
definition above). Therefore, if one decides to stick with the
predicate definition, some operations become tedious, as, even for
constants the property should be _inferred_ rather than proved:

*)

Theorem eight_is_beautiful: beautiful 8.
Proof.
apply: (b_sum _ 3 5)=>//; first by apply: b_3. 
by apply b_5.
Qed.

Theorem b_times2 n: beautiful n ->  beautiful (2 * n).
Proof.
by move=>H; apply: (b_sum _ n n)=>//; rewrite mul2n addnn.
Qed.

(** 

In particular, the negation proofs become much less straightforward
than one would expect:

*)

Lemma one_not_beautiful n:  n = 1 -> ~ beautiful n.
Proof.
move=>E H. 

(** 

[[
  n : nat
  E : n = 1
  H : beautiful n
  ============================
   False
]]

The way to infer the falsehood will be to proceed by induction on the
hypothesis [H]:

*)

elim: H E=>n'; do?[by move=>->].
move=> n1 m' _ H2 _ H4->{n' n}.

(** 

Notice how the assumptions [n'] and [n] are removed from the context
(since we don't need them any more) by enumerating them using [{n' n}]
notation.

*)

case: n1 H2=>// n'=> H3.
by case: n' H3=>//; case.
Qed.

(** 

%\begin{exercise}%

Proof the following theorem about beautiful and gorgeous numbers.

*)

Lemma b_timesm n m: beautiful n ->  beautiful (m * n).
(* begin hide *)
Proof.
elim:m=>[_|m Hm Bn]; first by rewrite mul0n; apply: b_0.
move: (Hm Bn)=> H1.
by rewrite mulSn; apply: (b_sum _ n (m * n))=>//.
Qed.
(* end hide *)

(** 

%\hint% Choose wisely, what to build the induction on.

%\end{exercise}%

To practice with proofs by induction, let us consider yet another
inductive predicate, borrowed fro Pierce et al.'s course and defining
which of natural numbers are _gorgeous_.  
%\index{gorgeous numbers}%

*)

Inductive gorgeous (n: nat) : Prop :=
| g_0 of n = 0
| g_plus3 m of gorgeous m & n = m + 3
| g_plus5 m of gorgeous m & n = m + 5.

(*
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

Lemma nat3_ind (P: nat -> Prop): 
  P 0 -> P 1 -> P 2 -> (forall n, P n -> P (n.+3)) -> forall n, P n.
Proof.
move=> H0 H1 H2 H n. 
suff: (P n /\ P (n.+1) /\ P (n.+2)) by case.
elim: n=>//n; case=>H3 [H4 H5]; split=>//; split=>//. 
by apply: H.
Qed.
*)

(** 

%\begin{exercise}%

Prove the following statements about gorgeous numbers:

*)


Lemma gorgeous_plus13 n: gorgeous n -> gorgeous (n + 13).
(* begin hide *)
Proof.
move=> H.
apply: (g_plus5 _ (n + 8))=>//; last by rewrite -addnA; congr (_ + _).
apply: (g_plus5 _ (n + 3)); last by rewrite -addnA; congr (_ + _).
by apply: (g_plus3 _ n). 
Qed.
(* end hide *)

Lemma beautiful_gorgeous (n: nat) : beautiful n -> gorgeous n.
(* begin hide *)
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
(* end hide *)

Lemma g_times2 (n: nat): gorgeous n -> gorgeous (n * 2).
(* begin hide *)
Proof.
rewrite muln2.
elim=>{n}[n Z|n m H1 H2 Z|n m H1 H2 Z]; subst n; first by rewrite double0; apply g_0.
- rewrite doubleD -(addnn 3) addnA.
  by apply: (g_plus3 _ (m.*2 + 3))=>//; apply: (g_plus3 _ m.*2)=>//.
rewrite doubleD -(addnn 5) addnA.
by apply: (g_plus5 _ (m.*2 + 5))=>//; apply: (g_plus5 _ m.*2)=>//.
Qed.
(* end hide *)

(**

As usual, do not hesitate to use the [Search] utility for finding the
necessary rewriting lemmas from the [ssrnat] module.

%\end{exercise}%

* Working with SSReflect libraries

TODO: General naming policies.

*)


(* begin hide *)
End SsrStyle.
(* end hide *)


