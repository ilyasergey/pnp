(** %\chapter{Reasoning with Equalities and Rewriting}% *)

Require Import ssreflect ssrbool ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
