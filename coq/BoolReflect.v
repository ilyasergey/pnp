(** 

%\chapter{Views and Boolean Reflection}
\label{ch:boolrefl}%

*)

(* begin hide *)
Module BoolReflect.
(* end hide *)

(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)

(** 

In %Chapter~\ref{ch:eqrew}% we have seen how custom rewriting rules
and truth tables can be encoded in Coq using its support for indexed
datatype families, so they offer great support for constructing the
proofs by case analysis and rewriting. In this chapter, we will show
how the custom rewriting machinery can be taken to the whole new level
and be used to facilitate the reasoning about _computable_ properties
and predicates. We will consider a series of insights that lead to the
idea of the _small-scale reflection_, the %\index{small-scale
reflection|textbf}% heart of the SSReflect framework, which blurs the
boundaries between computable predicates defined in the sort [Prop]
(see %Chapter~\ref{ch:logic}%) and Coq's recursive functions returning
a result of type [bool] (in the spirit of the definitions that we have
seen in %Chapter~\ref{ch:funprog}%). That said, in the vast number of
cases these two are just two sides of the same coin and, hence, should
be treated uniformly, serving to facilitate the reasoning in two
different directions: %\index{reflection|see {small-scale
reflection}}%

- expressing quantifications and building the proofs by means of
  _constructive reasoning_ with logical connectives as datatypes
  defined in the sort [Prop];

- employing brute-force computations for quantifier-free goals within
  the Coq framework itself, taken as a programming language, in order
  to reduce the goals to be proved by means of simply _computing_
  them.

We will elaborate more on the differences between predicates stated by
means of [Prop] and [bool] in %Section~\ref{sec:propbool}%. The term
_small-scale reflection_, which gives the name to the whole framework
of SSReflect, emphasizes the two complementary ways of building
proofs: by means of intuitionistic inference (i.e., using the
constructors of datatypes defined in [Prop]) and by means of mere
computation (i.e., with [bool]-returning function). These two ways,
therefore, serve as each other's "reflections" and, moreover, both are
implemented within the same system, without the need to appeal to
Coq's meta-object protocol,%\footnote{In contrast, reflection in Java,
Python or Ruby actually does appeal to the meta-object protocol, e.g.,
\index{meta-object protocol} the structure of the classes, which lies
beyond the formally defined semantics of the language itself and,
hence, allow one to modify the program's behaviour at runtime.}% which
makes this reflection _small_scale_.

Unfortunately, the proper explanation of the implementation of the
reflection mechanism between [Prop] and [bool] in SSReflect strongly
relies on the _views_ machinery, so let us begin by describing it
first.

%\newpage%

* Proving with views in SSReflect
%\label{sec:views}\index{views|textbf}%

*)

Require Import ssreflect.

(** 

Let us assume we have the following implication to prove:

*)

Lemma imp_trans4 P Q R S: (P -> Q) -> (R -> S) -> (Q -> R) -> P -> S.
Proof.
move=>H1 H2 H3.

(** 
[[
  P : Type
  Q : Type
  R : Type
  S : Type
  H1 : P -> Q
  H2 : R -> S
  H3 : Q -> R
  ============================
   P -> S
]]

Since we are proficient in the proofs via implications, it is not
difficult to construct the explicit proof term by a series of [apply:]
tactic calls or via the [exact:] tactic, as it has been show in
%Chapter~\ref{ch:logic}%. Let us do something different, though,
namely _weaken_ the top assumption of the goal by means of applying
the hypothesis [H1] to it, so the overall goal will become [Q -> S].

*)

move=>p; move: (H1 p).

(** 

This proof pattern of "switching the view" turns out to be so frequent
that SSReflect introduces a special _view_ tactical %\texttt{/}% for
it, which is typically combined with the standard [move] or [case]
tactics. In particular, the last proof line could be replaced by the
following:

*)

Undo.
move/H1.

(** 

The assumption [H1] used for weakening is usually referred to as a
%\index{view lemma}% _view lemma_. The spaces before and after
%\texttt{/}% are optional. One can also _chain_ the views into one
series, so the current proof can be completed as follows:

*)

by move/H3 /H2.
Qed.

(** 

** Combining views and bookkeeping

The view tactical can be also combined with the standard bookkeeping
machinery, so it will apply the specified view lemma to the
corresponding assumption of the goal, as demonstrated by the following
proof script, which use the partially-applied assumption [H p] as a
view lemma:

*)

Goal forall P Q R, P -> (P -> Q -> R) -> Q -> R.
Proof.
by move=>P Q R p H /(H p).

(**

In fact, this prove can be shortened even further by using the view
notation for the _top_ assumption:

*)

Undo.
move=> P Q R p. 
by move/(_ p). 
Qed.

(** 

The last proof script first moved for assumptions to the context, so
the goal became [(P -> Q -> R) -> R]. Next, it partially applied the
top assumption [(P -> Q -> R)] to [p : P] from the context and moved
the result back to the goal, so it became [(P -> Q) -> P -> Q], which
is trivially provable.

It is also possible to use views in combination with the [case]
tactics, which first performs the "view switch" via the view lemma
provided and then case-analyses on the result, as, demonstrated by the
following proof script:

*)

Goal forall P Q R, (P -> Q /\ R) -> P -> R.
Proof.
move=> P Q R H.
by case/H. 
Qed.

(** 

What is happened is that the combined tactic [case/H] first switched
the top assumption of the goal from [P] to [Q /\ R] and then
case-analyses on it, which gave the proof of [R] right away, allowing
us to conclude the proof.

** Using views with equivalences
%\label{seq:viewseq}%

So far we have explored only views that help to weaken the hypothesis
using the view lemma, which is an implication. In fact, SSReflect's
view mechanism is elaborated enough to deal with view lemmas defined
by means of equivlance (double implication) %\texttt{<->}%, and the
system can figure out itself, "in which direction" the view lemma
should be applied. Let us demonstrate it with the following example,
which makes use of the hypothesis [PQequiv],%\footnote{The Coq's
command \texttt{Hypothesis} is a synonym for \texttt{Axiom} and
\texttt{Variable}.\ccom{Hypothesis}\ccom{Variable}\ccom{Axiom}}% whose
nature is irrelevant for the illustration purposes:

*)

Variables S T: bool -> Prop.
Hypothesis STequiv : forall a b, T a <-> S (a || b). 

Lemma ST_False a b: (T a -> False) -> S (a || b) -> False.
Proof.
by move=>H /STequiv.
Qed.

(**

** Declaring view hints

Let us get back to the example from %Section~\ref{seq:viewseq}%, in
which we have seen how views can deal with equalities. The mentioned
elaboration, which helped the system to recognize, in which direction
the double implication hypothesis [STequiv] should have been used, is
not hard-coded into SSReflect. Instead, it is provided by a flexible
mechanism of %\index{view hints}% _view hints_, which allows one to
specify view lemmas that should be applied _implicitly_ whenever it is
necessary and can be figured out unambiguously.

In the case of the proof of the [ST_False] lemma the view hint [iffRL]
from the included module [ssreflect]%\footnote{Implicit view hints are
defined by means of \texttt{View Hint}\ccom{View Hint} command, added
to Coq by SSReflect.}% %\ssrm{ssreflect}% has been "fired" in order to
adapt the hypothesis [STequiv], so the adapted variant could be
applied as a view lemma to the argument of type [S (a || b)].

*)

Check iffRL.

(** 

The type of [iffRL] reveals that what it does is simply switching the
equivalence to the implication, which works right-to-left, as captured
by the name. Let us now redo the proof of the [ST_False] lemma to see
what is happening under the hood:

*)

Lemma ST_False' a b: (T a -> False) -> S (a || b) -> False.
Proof.
move=> H.
move/(iffRL (STequiv a b)).
done.
Qed.

(**

The view switch on the second line of the proof is what has been done
automatically in the previous case: the implicit view [iffRL] has been
applied to the call of [STequiv], which was in its turn supplied the
necessary arguments [a] and [b], inferred by the system from the goal,
so the type of [(STequiv a b)] would match the parameter type of
[iffRL], and the whole application would allow to make a view switch
in the goal.  What is left behind the scenes is the rest of the
attempts made by Coq/SSReflect in its search for a suitable implicit
view, which ended when the system has finally picked [iffRL].

In general, the design of powerful view hints is non-trivial, as they
should capture precisely the situation when the "view switch" is
absolutely necessary and the implicit views will not "fire"
spuriously. In the same time, implicit view hints is what allows for
the smooth implementation of the boolean reflection, as we will
discuss in %Section~\ref{sec:reflect}%.


** Applying view lemmas to the goal

Similarly to how they are used for _assumptions_, views can be udes to
interpret the goal by means of combiningy the Coq's standard [apply]
and [exact] tactics with the view tactical %\texttt{/}%. In the case
is [H] is a view lemma, which is just an implication [P -> Q], where
[Q] is the statement of the goal, the enhanced tactic [apply/ P] will
work exactly as the standard SSReflect's [apply:], that is, it will
replace the goal [Q] with [H]'s assumption [P] to prove.

However, interpreting goals via views turns out to be very beneficial
in the presence of implicit view hints. For example, let us consider
the following proposition to prove.

*)

Definition TS_neg: forall a, T (negb a) -> S ((negb a) || a).
Proof.
move=>a H. 
apply/STequiv.
done.
Qed.

(** 

The view switch on the goal by via [apply/STequiv] changes the goal
from [S ((negb a) || a)] to [T (negb a)], so the rest of the proof
becomes trivial. Again, notice that the system managed to infer the
right arguments for the [STequiv] hypothesis by analysing the goal.

Now, if we print the body of [TS_neg] (we can do it since it has been
defined via [Definition] rather than [Theorem]), we will be able to
see how an application of the implicit application of the view lemma
[iffLR] of type [forall P Q : Prop, (P <-> Q) -> P -> Q] has been
inserted, allowing for the construction of the proof term:

*)

Print TS_neg.

(**

[[
TS_neg = 
  fun (a : bool) (H : T (negb a)) =>
  (fun F : T (negb a) =>
     iffLR (Q:=S (negb a || a)) (STequiv (negb a) a) F) H
     : forall a : bool, T (negb a) -> S (negb a || a)
]]

*)


(** * %\texttt{Prop} versus \emph{bool}%
%\label{sec:propbool}%


TODO: Emphasize that in Prop you can use quantifiers, whereas [bool]
is as expressive as simple propositional logic (which is its strength,
thank to Coq's terminating computations)

*)

(*
Goal forall a b : bool, a && b.
move=> a b. 
have X: a /\ b -> a && b. by move/andP.
apply:X.
*)

Require Import ssrbool.

(** * %The \textsf{\textbf{reflect}} type family%
%\label{sec:reflect}%



Construct a simple reflection procedure for some simple user-specific
connective.

*)

(* begin hide *)
Module Inner.
(* end hide *)
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT  of   P : reflect P true
  | ReflectF of ~ P : reflect P false.
(* begin hide *)
End Inner.
(* end hide *)

Lemma andl_b a b: a && b -> a.
Proof.
by case/andP.
Show Proof.

(**
[[
(fun (a b : bool) (top : a && b) =>
 (fun F: forall (a0 : a) (b0 : b),
         (fun _ : a /\ b => is_true a) (conj a0 b0) =>
  match elimTF andP top 
  as a0 return ((fun _ : a /\ b => is_true a) a0)
  with
  | conj x x0 => Fx x0
  end) (fun (a0 : a) (_ : b) => a0))
]]

*)

Qed.

Goal forall a b c : bool, [|| false, false, true | false].
move=> a b c.
done.
Qed.





(** * Using conditionals in predicates


*)


(** * Case analysing on a boolean assumption


*)



(** * Types with decidable equalities

TODO: Emphasize that in Prop you can use quantifiers, whereas [bool]
is as expressive as simple propositional logic (which is its strength,
thank to Coq's terminating computations)

*)

(* begin hide *)
End BoolReflect.
(* end hide *)
