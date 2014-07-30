(** %
\chapter{Case Study: Program Verification in Hoare Type Theory}
\label{ch:htt}
% *)

(* begin hide *)
Module HTT.
(* end hide *)

(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing first %\texttt{{first}}% *)
(** printing last %\texttt{\emph{last}}% *)
(** printing suff %\texttt{\emph{suff}}% *)
(** printing have %\texttt{\emph{have}}% *)
(** printing View %\texttt{\emph{View}}% *)
(** printing >-> %\texttt{>->}% *)

(** 

* Specifications of imperative programs and Hoare triples

** Verifying programs in Hoare-style logic

** Basics of Separation Logic

** Selected rules of separation logic

* Monads in functional programming

** State monad

*)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import pred pcm unionmap heap heaptac stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**

* Basics of Hoare Type Theory

** Encoding program specifications as types

** The Hoare monad

* Specifying and verifying single-linked lists

* Further reading 

*)

(* begin hide *)
End HTT.
(* end hide *)