From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq.

Module FunProg.

(**
---------------------------------------------------------------------
Exercise [Power of two]
---------------------------------------------------------------------
Write the function [two_power] of type [nat -> nat], such that
[two_power n = 2^n]. Use the functions that we have defined earlier.
*)

Fixpoint two_power n := match n with 
  | 0 => 1
  | m.+1 => 2 * (two_power m)
  end.

(**
---------------------------------------------------------------------
Exercise [Even numbers]
---------------------------------------------------------------------

Define the function [evenB] of type [nat -> bool], such that it
returns [true] for even numbers and [false] otherwise. Use the
function we have already defined.
*)

Fixpoint evenB n := if n is m.+1 then ~~ (evenB m) else true.


(**
---------------------------------------------------------------------
Exercise [Division by 4]
---------------------------------------------------------------------

Define the function [div4] that maps any natural number [n] to the
integer part of [n/4].
*)

Fixpoint div4 n := if n is m.+4 then (div4 m).+1 else 0.

(**
---------------------------------------------------------------------
Exercise [Representing rational numbers]
---------------------------------------------------------------------

Every strictly positive rational number can be obtained in aunique
manned by a succession of applications of functions [N] nad [D] on the
number one, where [N] and [D] defined as follows:

[[
N(x) = 1 + x

D(x) = 1/(1 + 1/x)
]]

Define an inductive type (with three constructors), such that it
uniquely defines strictly positive rational using the representation
above.

Then, define the function that takes an element of the defined type
nad returns a numerator and denominator of the corresponding fraction.
*)

Inductive rational : Set :=
 One | N of rational | D of rational.

Fixpoint rat_to_frac (r: rational) : nat * nat :=
  match r with 
  | One => (1, 1)
  | N x => let: (a, b) := rat_to_frac x 
           in (b + a, b)
  | D x => let (a, b) := rat_to_frac x 
           in (a, a + b)
  end. 

(**
---------------------------------------------------------------------
Exercise [Infinitely-branching trees]
---------------------------------------------------------------------

Define an inductive type of infinitely-branching trees (parametrized
over a type [T]), whose leafs are represented by a constructor that
doesn't take parameters and a non-leaf nodes contain a value _and_ a
function that takes a natural number and returns a child of the node
with a corresponding natural index.

Define a boolean function that takes such a tree (instantiated with a
type [nat]) and an argument of [n] type [nat] and checks whether the
zero value occurs in it at a node reachable only by indices smaller
than a number [n]. Then write some "test-cases" for the defined
function.

Hint: You might need to define a couple of auxiliary functions for
this exercise.

Hint: Sometimes you might need to provide the type arguments to
constructors explicitly.

*)

Inductive inf_tree {T: Set} := Leaf | Node of T & (nat -> @inf_tree T).

Fixpoint check_subtrees (checker: nat -> bool) n :=
  if n is m.+1 
  then checker n || check_subtrees checker m
  else checker 0.

Fixpoint has_zero (t: @inf_tree nat) n {struct t} : bool :=
  match t with 
  | Leaf => false
  | Node x f => (x == 0) || 
                check_subtrees (fun s => has_zero (f s) n) n
  end.

Eval compute in 
  has_zero (Node 2 (fun x => if x == 3 then Node 0 (fun x => Leaf) else Leaf)) 3.

(**
---------------------------------------------------------------------
Exercise [List-find]
---------------------------------------------------------------------

Write a function that take a type [A], a function [f] of type [A ->
bool] and a list [l], and return the first element [x] in [l], such
that [f x == true]. 

%\hint% Use Coq's [option] type to account for the fact that the
 function of interest is partially-defined.
*)

Fixpoint first_elt A (f: A -> bool) (l : seq A) : option A := 
  if l is x::xs 
  then if f x then Some x else first_elt A f xs
  else None.

(**
---------------------------------------------------------------------
Exercise [Generate a range]
---------------------------------------------------------------------

Implement a function that takes a number [n] and returns the list
containing the natural numbers from [1] to [n], _in this order_.
*)

Fixpoint nns n z :=
  if n is m.+1 
  then z :: (nns m (z.+1))
  else [::].

Definition Nns n := nns n 1.

(**
---------------------------------------------------------------------
Exercise [Standard list combinators]
---------------------------------------------------------------------

Implement the following higher-order functions on lists

- map
- filter
- fold_left
- fold_right
- tail-recursive list reversal
*)

Fixpoint fold_left {A B} (f: B -> A -> B) z (l: seq A): B :=
  if l is x::xs 
  then fold_left f (f z x) xs
  else z.

Eval compute in fold_left (fun x y => x + y) 0 [::1;2;4].

Fixpoint fold_right {A B} (f: A -> B -> B) z (l: seq A): B :=
  if l is x::xs 
  then (f x (fold_right f z xs))
  else z.

Eval compute in fold_left (fun x y => x + y) 5 [::1;2;4].

(** 
---------------------------------------------------------------------
Exercises [No-stuttering lists]
---------------------------------------------------------------------

We say that a list of numbers "stutters" if it repeats the same number
consecutively. The predicate "nostutter ls" means that ls does not
stutter. Formulate an inductive definition for nostutter. Write some
"unit tests" for this function.

*)

Fixpoint eqn m n {struct m} :=
  match (m, n) with
  | (0, 0) => true
  | (m'.+1, n'.+1) => eqn m' n'
  | (_, _) => false
  end.

Fixpoint nostutter (l : seq nat): bool := 
  if l is x1::xs1 
  then if xs1 is x2::xs2 then ~~(eqn x1 x2) && nostutter xs1
                         else true
  else true.

Eval compute in nostutter [:: 1;2;3;4;5].

Eval compute in nostutter [:: 1;2;3;3;4;5].

(** 
---------------------------------------------------------------------
Exercise [List alternation]
---------------------------------------------------------------------

Implement the recursive function [alternate] of type [seq nat -> seq
nat -> seq nat], so it would construct the alternation of two
sequences.

%\hint% The reason why the "obvious" elegant solution might fail is
 that the argument is not strictly decreasing.
*)

Fixpoint alternate (l1 l2 : seq nat) : seq nat := 
match (l1, l2) with 
  | ([::], ys) => ys
  | (xs, [::]) => xs
  | (x::xs, y::ys) => x :: y :: (alternate xs ys)
  end. 

Eval compute in alternate [:: 1;2;3;4;5] [:: 1;2;3;4;6].

(**
---------------------------------------------------------------------
Exercise [Functions with dependently-typed result type]
---------------------------------------------------------------------

Write a function that has a dependent result type and whose result is
[true] for natural numbers of the form [4n + 1], [false] for numbers
of the form [4n + 3] and [n] for numbers of the from [2n].

%\hint% Again, you might need to define a number of auxiliary
 (possibly, higher-order) functions to complete this exercise.
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
  match n  with 
  | 0 => 0
  | 1 => true
  | n'.+2 => dep_value_aux n' (dep_value n')
  end.

Eval compute in dep_value 6.

End FunProg.
