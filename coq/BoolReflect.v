(** remove printing ~ *)
(** printing ~ %\textasciitilde% *)
(** printing R $R$ *)
(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing suff %\texttt{\emph{suff}}% *)


(** 

%\chapter{The Basics of Boolean Reflection}
\label{ch:boolrefl}%

*)


(** * %\texttt{Prop} versus \emph{bool}%

TODO: Emphasize that in Prop you can use quantifiers, whereas [bool]
is as expressive as simple propositional logic (which is its strength,
thank to Coq's terminating computations)

*)


(** * %The \emph{reflect} type family%

Construct a simple reflection procedure for some simple user-specific
connective.


*)


(*
Lemma max_r x y : x <= y -> maxn x y = y.
Proof.
rewrite /maxn; case: leqP=>// H1 H2.
suff: y <= x <= y by rewrite -eqn_leq; move/eqP. 
by apply/andP; split=>//. Qed.
*)


(** * Using conditionals in predicates


*)


(** * Case analysing on a boolean assumption


*)



(** * Types with decidable equalities

TODO: Emphasize that in Prop you can use quantifiers, whereas [bool]
is as expressive as simple propositional logic (which is its strength,
thank to Coq's terminating computations)

*)
