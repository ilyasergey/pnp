Require Import ssreflect ssrbool ssrnat.

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
