(** %\chapter{Elements of SSReflect Proof Style}
\label{ch:ssrstyle}
% *)

(** 

In this chapter we will continute employing the enhancements
intorduced into Coq by means of SSReflect, so for the next sections we
will have the [ssreflect] module imported.

*)

Require Import ssreflect ssrbool ssrnat eqtype.

(** 

%\section{Inductive predicates that should be functions}%

*)

(** 

Let's have a look at this hell below:

*)

(* Inductive isZero : nat -> Prop := IsZero : isZero 0. *)

(* Theorem blah: isZero 1 -> False. *)
(* Proof. *)
(* move=> z. *)
(* move: (isZero_ind (fun n => if n is 0 then True else False))=> Z. *)
(* by apply (Z I 1). *)
(* Qed. *)


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

%\section{On non-standard induction principles}%

TODO: Example from Section 9.3.1 from Coq'Art book.

%\section{Structuring the proof scripts}%

TODO: bullets, indentation, selectors, terminators etc.

%\section{Working with SSReflect libraries}%

TODO: General naming policies.

*)



