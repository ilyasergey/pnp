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

Require Import ssreflect ssrbool.

(** * Views in SSReflect
%\label{sec:views}%

TODO: demonstrate interpreting assumptions, goals and hypotheses.

*)

(** * %\texttt{Prop} versus \emph{bool}%

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
