(** %\chapter{Propositional Logic}% *)

(* begin hide *)
Require Import ssreflect.
(* end hide *)

(** 

In the previous chapter we had an opportunity to explore Coq as a
functional programming language and learn how to define inductive
datatypes and program that operate on them, implementing the later one
directly or using the automatically-generated recursion
combinators. Importantly, most of the values that we met until this
moment, inhabited the types, which were defined as elements of the
sort [Set]. The types [unit], [empty], [nat], [nat * unit] etc. are
good examples of _first-order_ types inhabiting the sort [Set].

* Propositions and the [Prop] sort

In this chapter, we will be exploring a new kind of entities,
incorporated by Coq: _propositions_.

TODO: present the types of True and False here

*)

(** * Logical connectives 

TODO: Present conjunction and disjunction

*)


(** * Universal and existential quantification

TODO: Present the ex type

*)

(** * Expressing negation

TODO: Show some proofs by negation

*)


(** * Missing axioms

TODO: discuss axioms of the classical logics

*)


(** * Higher-order types and Coq's sort hierarchy 

*)


(* Definition append_lm (A: eqType) (x: A) (xs ys: seq A):  *)
(*   x \in xs -> index x xs = index x (xs ++ ys). *)

(* Proof. *)
(* elim: xs=>// a ls Ih. *)
(* rewrite inE; case/orP; first by move/eqP=>->/=; rewrite !eq_refl. *)
(* by move/Ih=>/=->. *)
(* Qed. *)

