(** printing \in %\ensuremath{\in}% #\in# *)

(** %\chapter{Propositional Logic and SSReflect}% *)

(** The following directive enables SSReflect.  *)

Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.

(** The following three are explained in the SSReflect tutorial%~\cite[Section 3.3]{Gontier-al:TR}%. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Proving with SSReflect *)


Definition append_lm (A: eqType) (x: A) (xs ys: seq A): 
  x \in xs -> index x xs = index x (xs ++ ys).

(** ** A simple proof example *)

Proof.
elim: xs=>// a ls Ih.
rewrite inE; case/orP; first by move/eqP=>->/=; rewrite !eq_refl.
by move/Ih=>/=->.
Qed.

