(** %\chapter{Functional Programming in Coq}% *)

Module FunProg.

(** printing done %\texttt{\emph{done}}% *)
(** printing congr %\texttt{\emph{congr}}% *)
(** printing of %\texttt{\emph{of}}% *)
(** printing is %\texttt{\emph{is}}% *)

(** * Enumeration datatypes *)

Inductive unit : Set := tt.

Check tt.

Check unit.

Inductive empty : Set := .

Require Import ssreflect ssrbool.

Print bool.

Definition negate b := 
  match b with 
  | true  => false
  | false => true
  end.

Check negate.

(** * Simple recursive datatypes and programs *)

Print nat.

Require Import ssrnat.

Fixpoint my_plus n m := 
 match n with 
 | 0     => m   
 | n'.+1 => let: tmp := my_plus n' m in tmp.+1
 end.

Eval compute in my_plus 5 7. 

Fixpoint my_plus' n m := if n is n'.+1 then (my_plus' n' m).+1 else m.

Print nat_rect.

Definition my_plus1 n m := nat_rec (fun _ => nat) m (fun n' m' => m'.+1) n.

Eval compute in my_plus1 16 12.

(** ** Dependent function types and pattern matching *)

Check nat_rec.

Definition sum_no_zero n := 
 let: P := (fun n => if n is 0 then unit else nat) in
 nat_rec P tt (fun n' m => 
match n' return P n' -> _ with
   | 0 => fun _ => 1
   | n1.+1 => fun m => my_plus m (n'.+1) 
end m) n.

Eval compute in sum_no_zero 0.

Eval compute in sum_no_zero 5.

(** ** Recursion principle and non-inhabited types *)

Check empty_rect.

Inductive strange : Set :=  cs : strange -> strange.

Check strange_rect.

(** * More datatypes *)

(* Pairs *)

Check prod.

Print prod.

Check pair 1 tt.

Check @pair nat unit 1 tt.

Check fst.

Check snd.

(* Products  *)

Print sum.

(* Lists *)

Require Import seq.
Print seq.

Print list.

(**
[[
Inductive list (A : Type) : Type := nil : list A | cons : A -> list A -> list A
]]
*)

(**
%\begin{exercise}[Fun with lists in Coq]%

Implement the recursive function [alternate] of type [seq nat -> seq
nat -> seq nat], so it would construct the alternation of two
sequences according to the following "test cases".

Eval compute in alternate [:: 1;2;3] [:: 4;5;6].
[[
     = [:: 1; 4; 2; 5; 3; 6]
     : seq nat
]]

Eval compute in alternate [:: 1] [:: 4;5;6].
[[
     = [:: 1; 4; 5; 6]
     : seq nat
]]
Eval compute in alternate [:: 1;2;3] [:: 4].
[[
     = [:: 1; 4; 2; 3]
     : seq nat
]]

%\hint% The reason why the "obvious" elegant solution might fail is
 that the argument is not strictly decreasing.

%\end{exercise}%

*)

(** * Searching for definitions and notations *)

Search "filt".
(** 
[[
List.filter  forall A : Type, (A -> bool) -> list A -> list A
List.filter_In
   forall (A : Type) (f : A -> bool) (x : A) (l : list A),
   List.In x (List.filter f l) <-> List.In x l /\ f x = true
]]
*)

Search "filt" (_ -> list _).
(** 
[[
List.filter  forall A : Type, (A -> bool) -> list A -> list A
]]
*)

Search _ ((?X -> ?Y) -> _ ?X -> _ ?Y).
(**
[[
option_map  forall A B : Type, (A -> B) -> option A -> option B
List.map  forall A B : Type, (A -> B) -> list A -> list B
...
]]
*)

Search _ (_ * _ : nat).

Search _ (_ * _: Type).

(* Locate machinery *)

Locate "_ + _".

(** 
[[
Notation            Scope     
"x + y" := sum x y   : type_scope
                      
"m + n" := addn m n  : nat_scope
]]
*)

Locate map.

(**
[[
Constant Coq.Lists.List.map
  (shorter name to refer to it in current context is List.map)
Constant Ssreflect.ssrfun.Option.map
  (shorter name to refer to it in current context is ssrfun.Option.map)
...
]]
*)

(** * An alternative syntax to define inductive datatypes *)

Inductive my_prod (A B : Type) : Type :=  my_pair of A & B.

(** 
[[
Check my_pair 1 tt.

Error: The term "1" has type "nat" while it is expected to have type "Type".
]]
*)

(* Declaring implicit arguments *)

Implicit Arguments my_pair [A B].

(* Defining custom notation *)

Notation "X ** Y" := (my_prod X Y) (at level 2).
Notation "( X ,, Y )" := (my_pair X Y).

Check (1 ,, 3).

(** 
[[
(1,, 3)
     : nat ** nat
]]

*)

Check nat ** unit ** nat.

(** 
[[
(nat ** unit) ** nat
     : Set
]]
*)

(** * Sections and modules *)

Section NatUtilSection.

Variable n: nat.

Fixpoint my_mult m := match (n, m) with
 | (0, _) => 0
 | (_, 0) => 0
 | (_, m'.+1) => my_plus (my_mult m') n
 end. 

End NatUtilSection.

Print my_mult.

(** 

[[
my_mult = 
fun n : nat =>
fix my_mult (m : nat) : nat :=
  let (n0, y) := (n, m) in
  match n0 with
  | 0 => 0
  | _.+1 => match y with
            | 0 => 0
            | m'.+1 => my_plus (my_mult m') n
            end
  end
     : nat -> nat -> nat
]]
*)

Module NatUtilModule.

Fixpoint my_fact n :=
  if n is n'.+1 then my_mult n (my_fact n') else 1.

Module Exports.
Definition fact := my_fact.
End Exports.

End NatUtilModule.

Export NatUtilModule.Exports.

(** 
[[
Check my_fact.

Error: The reference my_fact was not found in the current environment.
]]
*)

Check fact.

(**
[[
fact
     : nat -> nat
]]
*)

(** 

TODO: more exercises

- More standard list functions

- Define a predecessor function

- Dependent function types in Coq (from Coq'Art)

*)

End FunProg.
