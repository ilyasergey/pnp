(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing From %\textsf{{From}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing is %\texttt{\emph{is}}% *)
(** printing first %\texttt{{first}}% *)
(** printing last %\texttt{{last}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)


(** %\chapter{Inductive Reasoning in Ssreflect}
\label{ch:ssrstyle}
% *)

(** 

In the previous chapters of this course, we have become acquainted
with the main concepts of constructive logic, Coq and
Ssreflect. However, the proofs we have seen so far are mostly done by
case analysis, application of hypotheses and various forms of
rewriting. In this chapter we will consider in more detail the proofs
that employ inductive reasoning as their main component. We will see
how such proofs are typically structured in Ssreflect, making the
corresponding scripts very concise, yet readable and maintainable. We
will also learn a few common techniques that will help to adapt an
induction hypothesis to become more suitable for a goal.

In the rest of the chapter we will be constantly relying on a series
of standard Ssreflect modules, such as [ssrbool], [ssrnat] and
[eqtype], which we import right away.

*)

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.

(* begin hide *)
Module SsrStyle.
(* end hide *)



(** 

%\section{Structuring the proof scripts}%

An important part of the proof process is keeping to an established
proof layout, which helps to maintain the proofs readable and restore
the intuition driving the prover's hand.  Ssreflect offers a number of
syntactic primitives that help to maintain such a layout, and in this
section we give a short overview of them. As usual, the Ssreflect
reference manual%~\cite{Gontier-al:TR}% (Chapter 6) provides an
exhaustive formal definition of each primitive's semantics, so we will
just cover the base cases here, hoping that the subsequent proofs will
provide more intuition on typical usage scenarios.

** Bullets and terminators

The proofs proceeding by induction and case analysis typically require
us to prove several goals, one by one, in a sequence picked by the
system.  It is considered to be a good practice to indent the subgoals
(except for the last one) when there are several to prove. For
instance, let us consider the following almost trivial lemma:

*)

Lemma andb_true_elim b c: b && c -> c = true.

(**

Indeed, the reflection machinery, presented in
%Section~\ref{sec:reflect} of Chapter~\ref{ch:boolrefl}%, makes this
proof a one liner ([by case/andP.]). However, for the sake of
demonstration, let us not appeal to it this time and do the proof as
it would be done in a traditional Coq style: by mere case analysis.

 *)

Proof.
case: c.

(** 
[[
true = true

subgoal 2 (ID 15) is:
 b && false -> false = true
]]

Case analysis on [c] (which is first moved down to the goal to become
an assumption) immediately gives us two subgoals to prove. Each of
them can be subsequently proved by the _inner_ cases analysis on [b],
so we do, properly indenting the goals.

*)

- by case: b.

(** 

The proof script above successfully solves the first goal, as ensured
by the _terminator_ tactical %\index{terminators}\ssrtl{by}% [by],
which we have seen previously. More precisely, [by tac.] first runs
the script [tac] and then applies a number of simplifications and
discriminations to see if the proof can be completed. If the current
goal is solved, [by tac.] simply terminates and proceeds to the next
goal; otherwise it reports a proof script error. Alternative
equivalent uses of the same principle would be [tac; by [].] or [tac;
done],%\ssrt{done}% which do exactly the same.

Notice that the first goal was indented and preceded by the _bullet_
[-]. %\index{bullets}% The bullet token, preceding a tactic
invocation, has no operational effect on the proof and serves solely
for the readability purposes. Alternative forms of tokens are
%\texttt{+}% and %\texttt{*}%.

** Using selectors and discharging subgoals

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
%\ssrtl{first}%
%\ssrtl{last}%

Now, right after case-analysing on [c], the proof script specifies
that the _first_ of the generated subgoals should be solved using [by
[]]. In this case %\texttt{first}% is called _selector_, and its
counterpart %\texttt{last}% would specify that the last goal should be
taken care of instead, before proceeding.

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
is by employing Coq's _repetition_ tactical [do]%\ssrtl{do}%. The
script of the form [do !tac.] tries to apply the tactic [tac] as many
times as possible, as long as new goals are generated or no more goals
are left to prove.%\footnote{Be careful, though, as such proof script
might never terminate if more and more new goals will be generated
after each application of the iterated tactic. That said, while Coq
itself enjoys the strong normalization property (i.e., the programs in
it always \index{strong normalization} terminate), its tactic
meta-language is genuinely Turing-complete, so the tactics, while
constructing Coq programs/proofs, might never in fact
terminate. Specifying the behaviour of tactics and their possible
effects (including non-termination and failures) is a topic of an
ongoing active
research~\cite{Ziliani-al:ICFP13,Stampoulis-Shao:ICFP10}.}% The
[do]-tactical can be also combined with the [[|...|]] tactical, so it
will try to apply all of the enumerated tactics as alternatives. The
following script finishes the proof of the whole lemma.


*)

Restart.
by do ![done | apply: eqxx | case: b | case: c].

(** 

Notice that we have added two tactics into the alternative list,
[done] and [apply: eqxx], which were doomed to fail. The script,
nevertheless, has succeeded, as the remaining two tactics, [case: b]
and [case: c], did all the job. Lastly, notice that the [do]-tactical
can be specified _how many_ times it should try to run each tactic
from the list by using the restricted form [do n!tac], where [n] is
the number of attempts (similarly to iterating the [rewrite]
tactics). The lemma above could be completed by the script of the form
[by do 2![...]] with the same list of alternatives.

*)

Qed.

(** 

%\section{Inductive predicates that should be functions}%

It has been already discussed in %Chapter~\ref{ch:boolrefl}% that,
even though a lot of interesting propositions are inherently
undecidable and should be, therefore, represented in Coq as instances
of the sort [Prop], one should strive to implement as many 
_decidable_ propositions as possible as [bool]-returning
function. Such "computational" approach to the propositions turns out
to pay off drastically in the long-term perspective, as most of the
usual proof burden will be carried out by Coq's computational
component. In this section we will browse through a series of
predicates defined both as inductive datatypes and boolean functions
and compare the proofs of various properties stated over the
alternative representations.

One can define the fact that the only natural number which is equal
to zero is the zero itself, as shown below:

%\ssrd{isZero}%

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

%\ssrd{evenP}%

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
n].%\footnote{Remember that the %[elim]%, \ssrt{elim} as most of other
Ssreflect's tactics operates on the top assumption.}% The subsequent
two goals (for the zero and the successor cases) are then simplified
via %\texttt{//}% and the induction variable and hypothesis are given
the names [n] and [Hn], respectively, in the second goal (as described
in %Section~\ref{sec:naming-subgoals}%). Then, the first goal (the
[0]-case) is discharged by simplifying the sum via two rewritings by
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
look alike.%\footnote{Recall that% [n.+1] %stands for the \emph{value}
of the successor of% [n], % whereas% [n + 1] % is a function call, so
the whole expression in the goal cannot be just trivially simplified
by Coq's computation and requires some rewritings to take the
convenient form.}% *)

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
(modulo the natural "[(.+2)]-orbit" of the [evenP] predicate and some
rewritings), we cannot take an advantage of it right away, and instead
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
employed for brushing the goal, which would then match the hypothesis
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
with [evenP] and [evenb].

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
%\label{pg:evenbplus}%

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
variable). We do so by using Ssreflect's tactics [elim] with explicit
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

We then perform the case-analysis on [n0] in the goal, which results
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

Doing _one more_ case analysis will add one more [1] to the induction
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
provide an "impedance matcher" between the 1-step "default" induction
principle on natural numbers and the 2-step induction in the
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

* Inductive predicates that are hard to avoid
%\label{sec:cannot}%

Although formulating predicates as boolean functions is often
preferable, it is not always trivial to do so. Sometimes, it is
(seemingly) much simpler to come up with an inductive predicate, which
explicitly witnesses the property of interest. As an example for such
property, let us consider the notion of _beautiful_ and _gorgeous_
numbers, which we borrow from %Pierce et al.'s electronic
book~\cite{Pierce-al:SF} (Chapter \textsf{MoreInd})%.

%\ssrd{beautiful}%

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
function, which checks whether a number is beautiful or not, although
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
move=> n1 m' _ H2 _ H4 -> {n' n}.

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

Prove the following theorem about beautiful numbers.

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
inductive predicate, borrowed from Pierce et al.'s course and defining
which of natural numbers are _gorgeous_.  %\index{gorgeous numbers}%

%\ssrd{gorgeous}%

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

%\begin{exercise}\label{ex:gb}%

Prove by induction the following statements about gorgeous numbers:

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

Lemma gorgeous_beautiful (n: nat) : gorgeous n -> beautiful n.
(* begin hide *)
Proof.
elim=>{n} -n=>//.
- by move=>->; apply: b_0.
- move=>m H1 H2->{n}.
  by move: (b_sum (m + 3) m 3 H2)=>H; apply: H=>//; apply: b_3.
- move=>m H1 H2->{n}.
  by move: (b_sum (m + 5) m 5 H2)=>H; apply: H=>//; apply: b_5.
Qed.
(* end hide *)


(**
%\noindent%
As usual, do not hesitate to use the [Search] utility for finding the
necessary rewriting lemmas from the [ssrnat] module.

%\end{exercise}%

*)


(** 
%\begin{exercise}[Gorgeous reflection]%

%\index{Frobenius problem}%
%\index{coin problem|see {Frobenius problem}}%

Gorgeous and beautiful numbers, defining, in fact, exactly the same
subset of [nat] are a particular case of Frobenius coin problem, which
asks for the largest integer amount of money, that cannot be obtained
using only coins of specified
denominations.%\footnote{\url{http://en.wikipedia.org/wiki/Frobenius_problem}}%
In the case of [beautiful] and [gorgeous] numbers we have two
denominations available, namely [3] and [5]. An explicit formula
exists for the case of only two denominations $n_1$ and $n_2$, which
allows one to compute the Frobenius number as $g(n_1, n_2) = n_1
\times n_2 - n_1 - n_2$. That said, for the case $n_1 = 3$ and $n_2 =
5$ the Frobenius number is $7$, which means that all numbers greater
or equal than $8$ are in fact beautiful and gorgeous (since the two
are equivalent, as was established by Exercise%~\ref{ex:gb}%).

In this exercise, we suggest the reader to prove that the efficient
procedure of "checking" for gorgeousness is in fact correct. First,
let us defined the following candidate function.

*)

Fixpoint gorgeous_b n : bool := match n with 
 | 1 | 2 | 4 | 7 => false
 | _ => true
 end. 

(** 

%\noindent%
The ultimate goal of this exercise is to prove the statement [reflect
(gorgeous n) (gorgeous_b n)], which would mean that the two
representations are equivalent. Let us divide the proof into two stages:

- The first stage is proving that all numbers greater or equal than
  [8] are gorgeous. To prove this it might be useful to have the
  following two facts established:

%\hint% Use the tactic [constructor i] to prove a goal, which is an
 [n]-ary disjunction, which is satisfied if its [i]th disjunct is
 true.

*)

Lemma repr3 n : n >= 8 -> 
  exists k, [\/ n = 3 * k + 8, n = 3 * k + 9 | n = 3 * k + 10].
(* begin hide *)
Proof.
elim: n=>// n Ih.
rewrite leq_eqVlt; case/orP.
- by rewrite eqSS=>/eqP<-; exists 0; rewrite muln0 add0n; constructor.
case/Ih=>k; case=>->{n Ih}.
- by exists k; constructor 2; rewrite -addn1 -addnA addn1.
- by exists k; constructor 3; rewrite -addn1 -addnA addn1.
exists (k.+1); constructor 1.  
by rewrite mulnSr -addn1 -2!addnA; congr (_ + _).
Qed.
(* end hide *)

Lemma gorg3 n : gorgeous (3 * n).
(* begin hide *)
Proof.
elim: n=>//[|n Ih]; first by apply: g_0; rewrite muln0.
by rewrite mulnSr; apply: (g_plus3 _ (3*n)).
Qed.
(* end hide *)

(** 

%\noindent%
Next, we can establish by induction the following criteria using the
lemmas [repr3] and [gorg3] in the subgoals of the proof.

*)

Lemma gorg_criteria n : n >= 8 -> gorgeous n.
(* begin hide *)
Proof.
case/repr3=>k; case=>->{n}.
- apply: (g_plus5 _ (3*k + 3)); last by rewrite -addnA.
  by apply: (g_plus3 _ (3*k))=>//; apply: gorg3.
- apply: (g_plus3 _ (3*k + 6))=>//; last by rewrite -addnA.
  apply: (g_plus3 _ (3*k + 3))=>//; last by rewrite -addnA.
  by apply: (g_plus3 _ (3*k))=>//; apply: gorg3.
apply: (g_plus5 _ (3*k + 5))=>//; last by rewrite -addnA.
by apply: (g_plus5 _ (3*k))=>//; apply: gorg3.
Qed.
(* end hide *)

(** 

%\noindent%
This makes the proof of the following lemma trivial.

*)

Lemma gorg_refl' n: n >= 8 -> reflect (gorgeous n) true.
(* begin hide *)
Proof. by move/gorg_criteria=>H; constructor. Qed.
(* end hide *)

(** 

- In the second stage of the proof of reflection, we will
  need to prove four totally boring but unavoidable lemmas.

%\hint% The rewriting lemmas [addnC] and [eqSS] from the [ssrnat]
 module might be particularly useful here.

*)


Lemma not_g1: ~(gorgeous 1).
(* begin hide *)
Proof.
case=>//n Ih /eqP; first by rewrite addn3 eqSS. 
by rewrite addnC eqSS.  
Qed.
(* end hide *)

Lemma not_g2: ~(gorgeous 2).
(* begin hide *)
Proof.
case=>//n Ih /eqP; first by rewrite addn3 eqSS. 
by rewrite addnC eqSS.  
Qed.
(* end hide *)

Lemma not_g4: ~(gorgeous 4).
(* begin hide *)
Proof.
case=>//n Ih /eqP; last by rewrite addnC eqSS.  
case: n Ih=>//n Ih.
rewrite addnC !eqSS. move/eqP=>Z; subst n. 
by apply:not_g1.
Qed.
(* end hide *)

Lemma not_g7: ~(gorgeous 7).
(* begin hide *)
Proof.
case=>//n Ih /eqP; case: n Ih=>//n Ih;
  rewrite addnC !eqSS; move/eqP=>Z; subst n. 
- by apply:not_g4. 
by apply:not_g2. 
Qed.
(* end hide *)

(** 

%\noindent% We can finally provide prove the ultimate reflection
predicate, relating [gorgeous] and [gorgeous_b].

*)
Lemma gorg_refl n : reflect (gorgeous n) (gorgeous_b n).
(* begin hide *)
Proof.
case: n=>/=[|n]; first by constructor; apply:g_0.
case: n=>/=[|n]; first by constructor; apply: not_g1.
case: n=>/=[|n]; first by constructor; apply: not_g2.
case: n=>/=[|n]. 
- constructor; apply:(g_plus3 _ 0); first by apply g_0.
  by rewrite add0n.
case: n=>/=[|n]; first by constructor; apply: not_g4.
case: n=>/=[|n].
- constructor; apply:(g_plus5 _ 0); first by apply g_0.
  by rewrite add0n.
case: n=>/=[|n].
- constructor; apply:(g_plus3 _ 3)=>//.
  apply:(g_plus3 _ 0); first by apply g_0.
  by rewrite add0n.
case: n=>/=[|n]; first by constructor; apply: not_g7.
suff X: (n.+4.+4 >= 8); last by [].
by apply:(gorg_refl').
Qed.
(* end hide *)

(** 

%\end{exercise}%

*)


(**
%\begin{exercise}[Complete trees]%

In this exercise, we will consider a binary tree datatype and
several functions on such trees.

*)

Inductive tree : Set :=
| leaf
| node of tree & tree.

(**

%\noindent%
A tree is either a leaf or a node with two branches.
The height of a leaf is zero, and height of a node is
the maximum height of its branches plus one.

*)

Fixpoint height t :=
if t is node t1 t2 then (maxn (height t1) (height t2)).+1 else 0.

(**

%\noindent%
The number of leaves in a node is
the total number of leaves in both its branches.

*)

Fixpoint leaves t :=
if t is node t1 t2 then leaves t1 + leaves t2 else 1.

(**

%\noindent%
A node is deemed a _complete_ tree if both its branches
are complete and have the same height; a leaf is
considered a complete tree.

*)

Fixpoint complete t :=
if t is node t1 t2 then complete t1 && complete t2 && (height t1 == height t2)
else true.

(**

%\noindent%
We can now prove by induction that in a complete tree, the number of leaves
is two to the power of the tree's height.

*)

Theorem complete_leaves_height t : complete t -> leaves t = 2 ^ height t.
(* begin hide *)
Proof.
elim: t => //= t1 IH1 t2 IH2.
move/andP => [H_c H_h].
move/andP: H_c => [H_c1 H_c2].
move/eqP: H_h => H_h.
rewrite IH1 // IH2 // H_h /maxn.
case: ifP; last by rewrite expnS mulSn mul1n.
by rewrite ltnNge; move/negP.
Qed.
(* end hide *)

(**

%\end{exercise}%

*)

(**

* Working with Ssreflect libraries

As it was mentioned in %Chapter~\ref{ch:intro}%, Ssreflect extension
to Coq comes with an impressive number of libraries for reasoning
about the large collection of discrete datatypes and structures,
including but not limited to booleans, natural numbers, sequences,
finite functions and sets, graphs, algebras, matrices, permutations
etc. As discussed in this and previous chapters, all these libraries
give preference to the computable functions rather than inductive
predicates and leverage the reasoning via rewriting by equality. They
also introduce a lot of notations that are worth being re-used in
order to make the proof scripts tractable, yet concise.

We would like to conclude this chapter with a short overview of a
subset of the standard Ssreflect programming and naming policies,
which will, hopefully, simplify the use of the libraries in a
standalone development.

** Notation and standard properties of algebraic operations
%\label{sec:funprops}%

Ssreflect's module [ssrbool] introduces convenient notation for
predicate connectives, such as [/\] and [\/]. In particular, multiple
conjunctions and disjunctions are better to be written as [[ /\ P1, P2
& P3]] and [[ \/ P1, P2 | P3]], respectively, opposed to [P1 /\ P2 /\
P3] and [P1 \/ P2 \/ P3]. The specific notation makes it more
convenient to use such connectives in the proofs that proceed by case
analysis. Compare.

*)

Lemma conj4 P1 P2 P3 P4 : P1 /\ P2 /\ P3 /\ P4 -> P3.
Proof. by case=>p1 [p2][p3]. Qed.

Lemma conj4' P1 P2 P3 P4 : [ /\ P1, P2, P3 & P4] -> P3.
Proof. by case. Qed.

(** 

In the first case, we had progressively decompose binary
right-associated conjunctions, which was done by means of the _product
naming_ pattern [[...]],%\footnote{The same introduction pattern works
in fact for \emph{any} product type with one constructor, e.g., the
existential quantification (see Chapter~\ref{ch:logic}).}% so
eventually all levels were "peeled off", and we got the necessary
hypothesis [p3]. In the second formulation, [conj4'], the case
analysis immediately decomposed the whole 4-conjunction into the
separate assumptions.

For functions of arity bigger than one, Ssreflect's module [ssrfun]
also introduces convenient notation, allowing them to be curried with
respect to the second argument:%\index{currying}%

*) 

Locate "_ ^~ _".
(** 
[[
"f ^~ y" := fun x => f x y     : fun_scope
]]

For instance, this is how one can now express the partially applied
function, which applies its argument to the list [[:: 1; 2; 3]]:

*)

Check map ^~ [:: 1; 2; 3].

(**

[[
map^~ [:: 1; 2; 3]
     : (nat -> ?2919) -> seq ?2919
]]

Finally, [ssrfun] defines a number of standard operator properties,
such as commutativity, distributivity etc in the form of the
correspondingly defined predicates: [commutative], [right_inverse]
etc. For example, since we have now [ssrbool] and [ssrnat] imported,
we can search for left-distributive operations defined in those two
modules (such that they come with the proofs of the corresponding
predicates):

*)

Search _ (left_distributive _).

(**

[[
andb_orl  left_distributive andb orb
orb_andl  left_distributive orb andb
andb_addl  left_distributive andb addb
addn_maxl  left_distributive addn maxn
addn_minl  left_distributive addn minn
...
]]

A number of such properties is usually defined in a generic way, using
Coq's canonical structures, which is a topic of
%Chapter~\ref{ch:depstruct}%.

** A library for lists
%\label{sec:liblists}%

Lists, being one of the most basic inductive datatypes, are usually a
subject of a lot of exercises for the fresh Coq hackers. Ssreflect's
modules [seq] %\ssrm{seq}% collect a number of the most commonly used
procedures on lists and their properties, as well as some non-standard
induction principles, drastically simplifying the reasoning.

For instance, properties of some of the functions, such as _list
reversal_ are simpler to prove not by the standard "direct" induction
on the list structure, but rather iterating the list from its last
element, for which the [seq] library provides the necessary definition
and induction principle:

[[
Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].
]]

*)

Check last_ind.

(**

[[
last_ind
     : forall (T : Type) (P : seq T -> Type),
       P [::] ->
       (forall (s : seq T) (x : T), P s -> P (rcons s x)) ->
       forall s : seq T, P s
]]

That is, [last_ind] is very similar to the standard list induction
principle [list_ind], except for the fact that its "induction step" is
defined with respect to the [rcons] function, rather than the list's
constructor [cons]. We encourage the reader to check the proof of the
list function properties, such as [nth_rev] or [foldl_rev] to see the
reasoning by the [last_ind] induction principle.

%\index{Dirichlet's box principle}%
%\index{pigeonhole principle|see{Dirichlet's box principle}}%

To demonstrate the power of the library for reasoning with lists, let
us prove the following property, known as _Dirichlet's box principle_
(sometimes also referred to as _pigeonhole principle_), the
formulation of which we have borrowed from
%Chapter~\textsc{MoreLogic}% of Pierce et al.'s
course%~\cite{Pierce-al:SF}%.

*)

Variable A : eqType.

Fixpoint has_repeats (xs : seq A) :=
  if xs is x :: xs' then (x \in xs') || has_repeats xs' else false.

(**

The property [has_repeats] is stated over the lists with elements that
have decidable equality, which we have considered in
%Section~\ref{sec:eqrefl}%. Following the computational approach, it
is a boolean function, which makes use of the boolean disjunction [||]
and Ssreflect's element inclusion predicate [\in], which is defined in
the module [seq].

The following lemma states that for two lists [xs1] and [xs2], is the
size [xs2] is strictly smaller than the size of [xs1], but
nevertheless [xs1] as a set is a subset of [xs2] then there ought to
be repetitions in [xs1].

*)

Theorem dirichlet xs1 xs2 :
        size xs2 < size xs1 -> {subset xs1 <= xs2} -> has_repeats xs1.

(** 

Let us go through the proof of this statement, as it is interesting by
itself in its intensive use of Ssreflect's library lemmas from the
[seq] module.

*)

Proof.

(** 

First, the proof scripts initiates the induction on the structure of
the first, "longer", list [xs1], simplifying and moving to the context
some hypotheses in the "step" case (as the [nil]-case is proved
automatically).

*)

elim: xs1 xs2=>[|x xs1 IH] xs2 //= H1 H2. 

(**
[[
  x : A
  xs1 : seq A
  IH : forall xs2 : seq A,
       size xs2 < size xs1 -> {subset xs1 <= xs2} -> has_repeats xs1
  xs2 : seq A
  H1 : size xs2 < (size xs1).+1
  H2 : {subset x :: xs1 <= xs2}
  ============================
   (x \in xs1) || has_repeats xs1
]]

Next, exactly in the case of a paper-and-pencil proof, we perform the
case-analysis on the fact [(x \in xs1)], i.e., whether the "head"
element [x] occurs in the remainder of the list [xs1]. If it is,
the proof is trivial and automatically discharged.

*)

case H3: (x \in xs1) => //=.
(**
[[
  ...
  H3 : (x \in xs1) = false
  ============================
   has_repeats xs1
]]

Therefore, we are considering now the situation when [x] was the
_only_ representative of its class in the original "long" list.  For
the further inductive reasoning, we will have to remove the same
element from the "shorter" list [xs2], which is done using the
following filtering operation ([pred1 x] checks every element for
equality to [x] and [predC] constructs the negation of the passed
predicate), resulting in the list [xs2'], to which the induction
hypothesis is applied, resulting in two goals

*)

pose xs2' := filter (predC (pred1 x)) xs2.
apply: (IH xs2'); last first.

(**
[[
  ...
  H2 : {subset x :: xs1 <= xs2}
  H3 : (x \in xs1) = false
  xs2' := [seq x <- xs2 | (predC (pred1 x)) x0] : seq A
  ============================
   {subset xs1 <= xs2'}

subgoal 2 (ID 5716) is:
 size xs2' < size xs1
]]

The first goal is discharged by first "de-sugaring" the [{subset ...}]
notation and moving a universally-quantified variable to the top, and
then performing a number of rewriting with the lemmas from the
[seq] library, such as [inE] and [mem_filter] (check their types!).
*)

- move=>y H4; move: (H2 y); rewrite inE H4 orbT mem_filter /=.
  by move => -> //; case: eqP H3 H4 => // ->->. 

(** 

The second goal requires to prove the inequality, which states that
after removal of [x] from [xs2], the length of the resulting list
[xs2] is smaller than the length of [xs1]. This is accomplished by the
transitivity of [<] and several rewritings by lemmas from the [seq]
and [ssrnat] modules, mostly targeted to relate the [filter] function
and the size of the resulting list.

*)

rewrite ltnS in H1; apply: leq_trans H1. 
rewrite -(count_predC (pred1 x) xs2) -addn1 addnC. 
rewrite /xs2' size_filter leq_add2r -has_count.

(**
[[
  ...
  H2 : {subset x :: xs1 <= xs2}
  H3 : (x \in xs1) = false
  xs2' := [seq x <- xs2 | (predC (pred1 x)) x0] : seq A
  ============================
   has (pred1 x) xs2
]]

The remaining goal can be proved by _reflecting_ the boolean
proposition [has] into its [Prop]-counterpart [exists2] from Ssreflect
library. The switch is done using the view [hasP], and the proof is
completed by supplying explicitly the existential witness%~%[x].

*)

by apply/hasP; exists x=>//=; apply: H2; rewrite inE eq_refl.
Qed.


(* begin hide *)
End SsrStyle.
(* end hide *)









