Require Import ssreflect ssrbool ssrnat.

Module FunProg.

(**
---------------------------------------------------------------------
%\begin{exercise}%

Write the function [two_power] of type [nat -> nat], such that
[two_power n = 2^n]. Use the functions that we have defined earlier.

%\end{exercise}%
---------------------------------------------------------------------

*)

Fixpoint two_power n := match n with 
  | 0 => 1
  | m.+1 => my_mult 2 (two_power m)
  end.

(** 
---------------------------------------------------------------------
%\begin{exercise}[Fun with lists in Coq]%

Implement the recursive function [alternate] of type [seq nat -> seq
nat -> seq nat], so it would construct the alternation of two
sequences.

%\hint% The reason why the "obvious" elegant solution might fail is
 that the argument is not strictly decreasing.

%\end{exercise}%
---------------------------------------------------------------------
*)

Fixpoint alternate (l1 l2 : seq nat) : seq nat := 
match (l1, l2) with 
  | ([::], [::]) => [::]
  | ([::], ys) => ys
  | (xs, [:: ]) => xs
  | (x::xs, y::ys) => x :: y :: (alternate xs ys)
  end. 

(**
---------------------------------------------------------------------
%\begin{exercise}%[Functions with dependently-typed result type]

Write a function that has a dependent result type and whose result is
[true] for natural numbers of the form [4n + 1], [false] for numbers
of the form [4n + 3] and [n] for numbers of the from [2n].

%\end{exercise}%
---------------------------------------------------------------------
*)

Fixpoint dep_type (n : nat) : Set := match n with 
  | 0 => nat
  | 1 => bool
  | n'.+2 => dep_type n'
  end. 

Fixpoint dep_value_aux (n: nat): dep_type n -> dep_type n := 
  match n return dep_type n -> dep_type n with 
  | 0 => fun x => x.+1
  | 1 => fun x => ~~x
  | n'.+2 => dep_value_aux n'
  end.

Fixpoint dep_value (n: nat): dep_type n := 
  match n return dep_type n with 
  | 0 => 0
  | 1 => true
  | n'.+2 => dep_value_aux n' (dep_value n')
  end.

Eval compute in dep_value 6.

End FunProg.