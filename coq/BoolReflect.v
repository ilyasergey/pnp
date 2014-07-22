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

TODO: now present views

*)

admit. Qed.


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
