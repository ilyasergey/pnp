(** %
\chapter{Equality and Rewriting Principles}
\label{ch:eqrew}

In the previous chapter we have seen how main connectives from Propositional Logic

% *)

(* begin hide *)
Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* end hide *)

(** * Propositional equality in Coq


 *)




(** * Proofs by rewriting


 *)

(* Inductive people : Set := me | pope.  *)

(* Definition discr p : Prop :=  *)
(*   if p is me then True else False. *)

(* Lemma me_pope: 1 = 2 -> me = pope. *)
(* Proof. *)
(* move=> E. *)
(* pose discr := fun n => if n is 1 then pope else me. *)
(* rewrite -/(discr 2).  *)
(* rewrite -E=>/=.  *)
(* move: (eq_refl pope)=> H; assumption. *)
(* Qed. *)

Inductive my_eq (A : Type) (x : A) : A -> Prop :=  my_eq_refl : my_eq x x.

(* Goal 1 = 2 -> False. *)

Goal my_eq 1 2 -> my_eq 5 2.
pose Discr := fun x => if x is 2 then False else True.
have X1: Discr 1 by [].
have X2: Discr 2 -> False by [].
by move=> H; case: H X2=>X2; move/X2: X1. 
Qed.



(* Goal forall x y: Type, my_eq x y -> my_eq y x. *)
(* move=> x y. *)

(** * Encoding custom rewriting rules


 *)


(** * Axioms about equality

TODO: K and friends

 *)



(* Goal forall n m, n <= m. *)
(* move=> n m. *)
(* elim n. *)

(* Goal forall x y: Type, x = y -> y = x. *)
(* Proof. *)
(* move=>x y. *)
(* elim:  /eq_ind. *)

(* move:(eq_ind x)=>H H1. *)
(* move: (H _ eq_refl y H1). *)


(* Print eq. *)
(* Check eq_ind. *)
(* move:(eq_ind x)=>H H1. *)
(* apply: H; last by apply: eq_refl. *)
(* elim: H1. *)

