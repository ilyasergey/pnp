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

Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

* Specifications of imperative programs and Hoare triples

* Basics of Separation Logic

* Encoding program specifications as types

** The Hoare monad

* Specifying and verifying single-linked lists

* Further reading 

*)

(* begin hide *)
End HTT.
(* end hide *)