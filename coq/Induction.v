(** %\chapter{More Inductive Predicates}% *)

Require Import ssreflect ssrbool ssrnat.

(** * Definitional equality in Coq


 *)


(** * Proofs by rewriting


 *)

Inductive people : Set := me | pope. 

Definition discr p : Prop := 
  if p is me then True else False.

Lemma me_pope: 1 = 2 -> me = pope.
Proof.
move=> E.
pose discr := fun n => if n is 1 then pope else me.
rewrite -/(discr 2). 
rewrite -E=>/=. 
move: (eq_refl pope)=> H; assumption.
Qed.


(** * Axioms about equality

TODO: K and friends

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


(* Fixpoint is_even n :=  *)
(*  match n with  *)
(*   | 0  => true *)
(*   | 1  => false *)
(*   | n'.+2  => is_even n' *)
(*  end.  *)

(* Check nat_rec. *)

(* Definition is_even' := nat_rec (fun _ => bool) true (fun _ => negate).  *)

(* Eval compute in is_even' 140. *)


(* Check list_rec. *)

(* Program Definition sum (l: seq nat): nat :=  *)
(*   list_rec (fun _ => nat) 0 (fun x l res => x + res) l. *)

(* Definition my_list := 1 :: 2 :: 3 :: nil. *)

(* Eval compute in sum my_list. *)



(* Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path. *)






(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

(* Inductive isZero n : Prop := IsZero of (n = 0) & (n = 1). *)


(* Theorem blah: forall n, isZero n -> False. *)
(* move=> n. case. *)
(* move=>->.  *)

(* Theorem isZero_contra : isZero 1 -> False. *)
(* Proof. *)
(* case.  *)
(* have X1: if 0 == 1 then False else True by case Y: (0 == 1)=>//.  *)
(* by rewrite eq_sym=>X; rewrite X in X1. *)



(* case Y: (0 == 1)=>//. *)
(* have Z: isZero 1 -> 0 == 1. *)


(* by rewrite Y in X1 =>/=. *)

(*    move=> Z; rewrite -Z in X1. *)
