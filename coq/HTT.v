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
(** printing LoadPath %\texttt{\emph{LoadPath}}% *)
(** printing exists %\texttt{{exists}}% *)

(** 

In this chapter, we present a fairly large case study that makes use
of many of Coq and SSReflect's features, which we have observed by
this moment,---specification and verification of imperative programs.

Programming language practitioners usuale elaborate on the dichotomy
between _declarative_ and _imperative_ languages, emphasizing the fact
%\index{declarative programming}\index{imperative programming}% that a
program written in declarative language is pretty much documenting
itself, as it already specifies the _result_ of a
computation. Therefore, logic and constraint programming languages
(such as Prolog and Ciao%~\cite{Hermenegildo-al:TPLP12}\index{Ciao}%)
as well as data definition/manipulation languages (e.g., SQL), whose
programs are just sets of constraints/logical clauses or queries
describing the desired result, are naturally considered to be
declarative. Very often, pure functional programming languages (e.g.,
Haskell) are considered declarative as well, The reason for this is
the _referential transparency_ property, which ensures that programs
in such language %\index{referential transparency}% are in fact
effect-free expressions, evaluating to some result (similar to
mathematical functions). Therefore, such programs, whose outcome is
only their result as an expression, but not some side effect (e.g.,
output to a file), can be replaced safely by their result, if it's
computable. This possibility provides a convenient way of algebraic
reasoning about such programs by means of equality
rewritings---precisely what we were observing and leveraging in
%Chapters~\ref{ch:eqrew} and~\ref{ch:ssrstyle}% of this course in the
context of Coq taken as a functional programming language.

%\index{specification|see {program specification}}%

That said, pure functional programs tend to be considered to be good
specifications for themselves. Of course, the term "specification" (or
simply, "spec") %\index{program specification}% is overloaded and in
some context it might mean the result of the program, its effect or
some algebraic properties. While a functional program is already a
good description of its result (due to referential transparency), its
algebraic properties (e.g., some equalities that hold over it) are
usually a subject of separate statements, which should be proved. Good
example of such properties are the commutativity and cancellation
statements, which we proved for natural numbers on
page%~\pageref{pg:addnprops} of Chapter~\ref{ch:depstruct}%. Another
classical series of examples, which we did not focus in this course,
are properties of list functions, such as appending and reversal
(e.g., that the list reversal is an inverse to itself).%\footnote{A
typical anti-pattern in dependently-typed languages and Coq in
particular is to encode such algebraic properties into the definitions
of the datatypes and functions themselves (a chrestomathic example of
such approach are length-indexed lists). While this approach looks
appealing, as it demonstrates the power of dependent types to capture
certain properties of datatypes and functions on them, it is
inherently non-scalable, as there will be always another property of
interest, which has not been foreseen by a designer of the
datatype/function, so it will have to be encoded as an external fact
anyway. This is why we advocate the approach, in which datatypes and
functions are defined as close to the way they would be defined by a
programmer as possible, and all necessary properties are proved
separately.}%

The situation is different when it comes to imperative programs, whose
outcome is typically their side-effect and is achieved by means of
manipulating mutable state or performing input/output. While some of
the modern programming languages (e.g., Scala, OCaml) allow one to mix
imperative and declarative programming styles, it is significantly
harder to reason about such programs, as now they cannot be simply
replaced by their results: one should also take into account the
effect of their execution (i.e., changes in the mutable state). A very
distinct approach to incorporating both imperative and declarative
programming is taken by Haskell, in which effectful programs can
always be distinguished from pure ones by means of enforcing the
former ones to have very specific
types%~\cite{PeytonJones-Wadler:POPL93}%---the idea we will elaborate
more on a bit further.

In the following sections of this chapter, we will learn how Coq can
be used to give specifications to imperative programs, written in a
language, similar to C. Moreover, we will observe how the familiar
proof construction machinery can be used to establish the correctness
of these specifications, therefore, providing a way to _verify_ a
program by means of checking, whether it satisfies a given spec. In
particular, we will learn how the effects of state-manipulating
programs can be specified via dependent types, and the specifications
of separate effectful programs can be _composed_, therefore allowing
us to structure the reasoning in the modular way, similarly to
mathematics, where one needs to prove a theorem only once and then can
just rely on its statement, so it can be employed in the proofs of
other facts.

* Imperative programs and their specifications

The first attempts to specify the behaviour of a state-manipulating
imperative program with assignments originate in late '60s and are due
to Tony Hoare%~\cite{Hoare:CACM69}%, who considered programs in a
simple imperative language with mutable variables (but without
pointers or procedures) and suggested to give a specification to a
program $c$ in the form of the triple $\spec{P}~c~\spec{Q}$, where $P$
and $Q$ are logical propositions, describing the values of the mutable
programs and possible relations between them. $P$ and $Q$ are usually
%\index{assertions}% referred to as _assertions_; more specifically,
$P$ is called %\index{precondition}\index{postcondition}%
_precondition_ of $c$ (or just "pre"), whereas $Q$ is called
_postcondition_ (or simply "post"). The triple $\spec{P}~c~\spec{Q}$
is traditionally referred to as _Hoare triple_.%\index{Hoare
triple}%%\footnote{The initial syntax for the triples by Hoare, was
$\specK{P}~\set{c}~\specK{Q}$. The notation $\spec{P}~c~\spec{Q}$,
which is now used consistently is due to Wirth and emphasizes the
comment-like nature of the assertion in the syntax reminiscent to the
one of Pascal.}% Its intuitive semantics can be expressed as follows:
"if right before the program $c$ is executed the state of mutable
variables is described by a proposition $P$, then, _if $c$
terminates_, the resulting state satisfies the proposition $Q$".

The reservation on termination of the program $c$ is important. In
fact, while the Hoare triples in their simple form make sense only for
terminating programs, it is possible to specify non-terminating
programs as well. This is due to the fact that the semantics of a
Hoare triple implies that a non-terminating program can be given _any_
postcondition, as one won't be able to check it anyway, as the program
will never reach the final state.%\footnote{This intuition is
consistent with the one, enforced by Coq's termination checker, which
allows only terminating programs to be written, since non-terminating
program can be given any type and therefore compromise the consistency
of the whole underlying logical framework of CIC.}% Such
interpretation of a Hoare triple "modulo termination" is referred to
as _partial correctness_, and in this chapter we will focus on it. It
is possible to give to a Hoare triple $\spec{P}~c~\spec{Q}$ a
different interpretation, which would deliver a stronger property: "if
right before the program $c$ is executed the state of mutable
variables is described by a proposition $P$, then $c$ terminates and
the resulting state satisfies the proposition $Q$". Such property is
called _total correctness_ and requires tracking some sort of "fuel"
for the program in the assertions, so it could run further. We do not
consider total correctness in this course and instead refer the reader
to the relevant research results on Hoare-style specifications with
resource bounds%~\cite{Dockins-Hobor:DS10}%.

** Specifying and verifying programs in the Hoare logic

- simple imperative program assignment

- rules

- loop invariant

- conditionals

** Basics of Separation Logic

Main motto logic about heaps and aliasing (a an b can in fact point to the same thing)

TODO: example -- returning value of a pointer

** Selected rules of Separation Logic

** Verifying programs in Separation Logic

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

** On loops and recursive functions

** Verifying the factorial in HTT

*)

Fixpoint fact_pure n := if n is n'.+1 then n * (fact_pure n') else 1.

Definition fact_inv (n acc : ptr) (N : nat) h : Prop := 
  exists n' a': nat, 
  [/\ h = n :-> n' \+ acc :-> a' & 
      (fact_pure n') * a' = fact_pure N].

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
case=>n' [a'][->{i}] Hi V. 
heval. (* TODO: Some automation - explain *)
case X: (n' == 0)=>//.
(* TODO: explain search for tactics *)
- apply: val_ret=>/= _; move/eqP: X=>Z; subst n'.
  split; first by exists 0, a'=>//.
  by rewrite mul1n in Hi.
heval. 
apply: (gh_ex N); apply: val_doR=>// V1.
- exists (n'-1), (a' * n'); split=>//=. 
rewrite -Hi=>{Hi V1 V}; rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
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
by move=>_ _ [[n'][a'][->] _ ->] _; heval.
Qed.


Fixpoint fib_pure n := 
  if n is n'.+1 then
    if n' is n''.+1 then fib_pure n' + fib_pure n'' else 1
  else 0.

Definition fib_inv (n x y : ptr) (N : nat) h : Prop := 
  exists n' x' y': nat, 
  [/\ h = n :-> n'.+1 \+ x :-> x' \+ y :-> y',
      x' = fib_pure n' & y' = fib_pure (n'.+1)].

Definition fib_tp n x y N := 
  unit ->
     STsep (fib_inv n x y N, 
           [vfun (res : nat) h => fib_inv n x y N h /\ res = fib_pure N]).

(*
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
move=>h /=[n'][_][_][->{h}]->->.
heval; case X: (n'.+1 == N)=>//.
- by apply: val_ret=>_; move/eqP: X=><-/=.
heval; apply: val_doR=>//. (* This line takes a while due to automation. *)
move=>_.
exists (n'.+1), (fib_pure (n'.+1)), (fib_pure n'.+1.+1).
by rewrite addn1.
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
- case; case=>n'[_][_][->{h}]->->->_.
  by heval; rewrite !unitR.
by exists 1, 1, 1.
Qed.
*)

(**

* Specifying and verifying single-linked lists

* Further reading 

*)

(* begin hide *)
End HTT.
(* end hide *)