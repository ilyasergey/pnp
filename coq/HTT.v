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

- simple imperative program

- loop invariant

- conditionals

** Basics of Separation Logic

Main motto logic about heaps and aliasing (a an b can in fact point to the same thing)

TODO: example -- returning value of a pointer

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

TODO: repeat the factorial example

** The Hoare monad

** Verifying the factorinal in HTT

*)

Fixpoint fact_pure n := if n is n'.+1 then n * (fact_pure n') else 1.

Definition fact_inv (n acc : ptr) (N : nat) h : Prop := 
  exists n' a': nat, 
  [/\ h = n :-> n' \+ acc :-> a',
      n' <= N & (fact_pure n') * a' = fact_pure N].

Definition fact_tp n acc := 
  unit -> {N}, 
     STsep (fact_inv n acc N, 
           [vfun (res : nat) h => fact_inv n acc N h /\ res = fact_pure N]).

Program Definition fact_acc (n acc : ptr): fact_tp n acc := 
  Fix (fun (loop : fact_tp n acc) (_ : unit) => 
    Do (a1 <-- !acc;
        n' <-- !n;
        if n' == 0 then ret a1
        else acc ::= a1 * n';;
             n ::= n' - 1;;
             loop tt)).

Next Obligation. 
(* Q: what ghR does precisely? 
   A: It pulls out all the logical variables to the top level
*)
apply: ghR=>i N. 
case=>n' [a'][->{i}]Ne Hi V. 
heval. (* TODO: Some automation - explain *)
case X: (n' == 0)=>//.
(* TODO: explain search for tactics *)
- apply: val_ret=>/= _; move/eqP: X=>Z; subst n'.
  split; first by exists 0, a'=>//.
  by rewrite mul1n in Hi.
heval. 
apply: (gh_ex N); apply: val_doR=>// V1.
- exists (n'-1), (a' * n'); split=>//=. 
- by apply: (leq_trans (leq_subr 1 n') Ne).
rewrite -Hi=>{Hi Ne V1 V}; rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
case: n' X=>//= n' _.
by rewrite subn1 -pred_Sn. 
Qed.

Program Definition fact (N : nat) : 
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fact_pure N /\ h = Unit]) := 
  Do (
    n   <-- alloc N;
    acc <-- alloc 1;
    res <-- fact_acc n acc tt;
    dealloc n;;
    dealloc acc;;
    ret res).

Next Obligation.
rewrite /conseq.
move=>h /= Z; subst h.
heval=>n; heval=>acc; rewrite joinC unitR.
(* 

Intuition behind bnd_seq: decomposing sequential composition with a
user-defined function.

 *)
apply: bnd_seq; apply: (gh_ex N).
(* 
Replace the call by its spec (substitution principle)
val_doR preserves the heap.
*)
apply: val_doR=>//; first by exists N, 1; rewrite muln1.
by move=>_ _ [[n'][a'][->] _ _ ->] _; heval.
Qed.


Fixpoint fib_pure n := 
  if n is n'.+1 then
    if n' is n''.+1 then fib_pure n' + fib_pure n'' else 1
  else 0.

Definition fib_inv (n x y : ptr) (N : nat) h : Prop := 
  exists n' x' y': nat, 
  [/\ h = n :-> n'.+1 \+ x :-> x' \+ y :-> y',
      n'.+1 <= N,
      x' = fib_pure n' & y' = fib_pure (n'.+1)].

Definition fib_tp n x y N := 
  unit ->
     STsep (fib_inv n x y N, 
           [vfun (res : nat) h => fib_inv n x y N h /\ res = fib_pure N]).

Program Definition fib_acc (n x y : ptr) N: fib_tp n x y N := 
  Fix (fun (loop : fib_tp n x y N) (_ : unit) => 
    Do (n' <-- !n;
        y' <-- !y;
        if n' == N then ret y'
        else tmp <-- !x;
             x ::= y';;
             x' <-- !x;
             y ::= x' + tmp;;
             n ::= n' + 1;;
             loop tt)).

Next Obligation.
move=>h /=[n'][_][_][->{h}]Ne->->.
heval; case X: (n'.+1 == N)=>//.
- by apply: val_ret=>_; move/eqP: X=><-/=.
heval; apply: val_doR=>//. (* This line takes a while due to automation. *)
move=>_.
exists (n'.+1), (fib_pure (n'.+1)), (fib_pure n'.+1.+1).
rewrite addn1; split=>//.
rewrite ltnNge; apply/negP; rewrite leq_eqVlt.
case/orP=>//; first by rewrite eq_sym X.
rewrite ltnS leq_eqVlt; case/orP.
- by move/eqP=>Z; subst N; rewrite ltnn in Ne.
by move/(ltn_trans Ne); rewrite ltnn.
Qed.

Program Definition fib N : 
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fib_pure N /\ h = Unit]) := 
  Do (
   if N == 0 then ret 0
   else if N == 1 then ret 1
   else n   <-- alloc 2;
        x <-- alloc 1;
        y <-- alloc 1;
        res <-- fib_acc n x y N tt;
        dealloc n;;
        dealloc x;;
        dealloc y;;
       ret res    
).
Next Obligation.
move=>_ /= ->.
case N1: (N == 0)=>//; first by move/eqP: N1=>->; apply:val_ret. 
case N2: (N == 1)=>//; first by move/eqP: N2=>->; apply:val_ret. 
heval=>n; heval=>x; heval=>y; rewrite unitR joinC [x:->_ \+ _]joinC.
apply: bnd_seq=>/=.
apply: val_doR; last first=>//[res h|].
- case; case=>n'[_][_][->{h}]Ne->->->_.
  by heval; rewrite !unitR.
- exists 1, 1, 1; split=>//=.  
by case: N N1 N2=>//; case=>//.
Qed.

(**

* Specifying and verifying single-linked lists

* Further reading 

*)

(* begin hide *)
End HTT.
(* end hide *)