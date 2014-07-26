(** 
%
\chapter{Encoding Mathematical Structures}
\label{ch:depstruct}
% 
*)

(* begin hide *)
Module DepRecords.
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

In this chapter we will learn how to encode the reasoning about common
algebraic data structures in Coq. In particular, we will meet some old
friends from the course of abstract algebra: monoids and PCMs. 

TODO: recall sigma-types

*)

Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** 

* A simple mathematical structure: partial commutative monoid 

%\index{partial commutative monoid}%
%\index{PCM|see {partial commutative monoid}}%


** Describing basic structure via mixins

%\index{mixins}%

*)

Record mixin_of (T : Type) := Mixin {
    valid_op : T -> bool;
    join_op : T -> T -> T;
    unit_op : T;
    _ : commutative join_op;
    _ : associative join_op;
    _ : left_id unit_op join_op;
    _ : forall x y, valid_op (join_op x y) -> valid_op x; 
    _ : valid_op unit_op }.

Lemma r_unit T (pcm: mixin_of T) (t: T) : (join_op pcm t (unit_op pcm)) = t.
Proof.
case: pcm=>_ jo uo Hc _ Hlu _ _ /=.

(** 
[[
  T : Type
  t : T
  jo : T -> T -> T
  uo : T
  Hc : commutative jo
  Hlu : left_id uo jo
  ============================
   jo t uo = t
]]

*)

by rewrite Hc Hlu.
Qed.

(** TODO: emphasize the [:>] coercion *)
Structure pack_type : Type := Pack {sort :> Type; _ : mixin_of sort; _ : Type}.


(**

TODO

** Packaging the structure


*)

Section Blah.
Variables (T : Type) (cT : pack_type).
Definition class : mixin_of cT := let: Pack _ c _ as cT' := cT return mixin_of cT' in c.

Check class.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c. 

Definition valid := valid_op class.
Definition join := join_op class.
Definition unit := unit_op class.
End Blah.


(**

Here, we define the monoids and prove a number of properties about
them. We will take natural numbers and lists as instances.

*)

(** * Properties of partial commutative monoids *)

Notation "x \+ y" := (join x y) (at level 43, left associativity).

Section Tada.
Definition pcm := pack_type.
Variable U V : pcm.

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof. by case: U x y=>tp [v j z Cj *]; apply: Cj. Qed.
End Tada.


(** * Introducing canonical structures  

TODO: show first definition withou equality.

%\ccom{Canonical}%

** Defining arbitrary PCM instances

*)

Definition natPCMMixin := 
  Mixin addnC addnA add0n (fun x y => @id true) (erefl _).
Canonical natPCM := Eval hnf in pack natPCMMixin.

Variables a b: nat.

(** 

TODO: can I use [+] here instead of [\+] ?

*)

Goal a \+ b = a \+ b.
by rewrite joinC.
Qed.


(**

** Types with computable equalities

*)



(**

* Summary of encoding patterns


We recommend the interested authors to take a look at Chapter 1 of
%Fran\c{c}ois% Garillot's PhD dissertation for more examples of
mathematical data structure encoding in Coq/SSReflect%~\cite{Garillot:PhD}%. 

More examples in%~\cite{Garillot-al:TPHOL09}%.

*)


(* begin hide *)
End DepRecords.
(* end hide *)
