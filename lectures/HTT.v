(** %\chapter{Case Study: Program Verification in Hoare Type Theory}% *)

Module HTT.

(** * Elements of Hoare Type Theory *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Structuring the program verification in HTT *)

(* NOTE: the current implementation of HTT does not support
value/type dependencies in the logical variables (e.g., {T (x: T)}),
so such cases won't be properly handled by the ghR lemma. *)

Program Definition alter_x A (x : ptr) (v : A): 
  {y (Y : nat)}, 
  STsep (fun h => exists B (w : B), h = x :-> w \+ y :-> Y,
        [vfun (_: unit) h => h = x :-> v \+ y :-> Y]) := 
  Do (x ::= v).

(**

The Coq's command [Program Definition] is similar to the standard
definition [Definition] except for the fact that it allows the
expression being defined to have a type, whose some components haven't
yet been type-checked and remain to be filled by the programmer.

After stating the definition, Coq generates a series of obligations to
prove in order to establish the defined program well-typed with
respect to the stated type.

[[
alter_x has type-checked, generating 1 obligation(s)
Solving obligations automatically...
1 obligation remaining
Obligation 1 of alter_x:
forall (A : Type) (x : ptr) (v : A),
conseq (x ::= v)
  (logvar
     (fun y : ptr =>
      logvar
        (fun Y : nat =>
         binarify
           (fun h : heap => exists (B : Type) (w : B), h = x :-> w \+ y :-> Y)
           [vfun _ h => h = x :-> v \+ y :-> Y]))).
]]

The proof mode for each of the remaining obligations is activated by
the Vernacular command [Next Obligation], which automatically moves
some of the assumptions to the context.

*)

Next Obligation.

(**
[[
  A : Type
  x : ptr
  v : A
  ============================
   conseq (x ::= v)
     (logvar
        (fun y : ptr =>
         logvar
           (fun Y : nat =>
            binarify
              (fun h : heap =>
               exists (B : Type) (w : B), h = x :-> w \+ y :-> Y)
              [vfun _ h => h = x :-> v \+ y :-> Y])))
]]
*)

apply: ghR. 

(**
[[
  A : Type
  x : ptr
  v : A
  ============================
   forall (i : heap) (x0 : ptr * nat),
   (exists (B : Type) (w : B), i = x :-> w \+ x0.1 :-> x0.2) ->
   valid i -> verify i (x ::= v) [vfun _ h => h = x :-> v \+ x0.1 :-> x0.2]
]]

We can now move a number of assumptions, arising from the "brushed"
specification, to the context, along with some rewriting by equality
and simplifications.

*)

move=>h1 [y Y][B][w]->{h1} _ /=.

(**

[[
  ...
  B : Type
  w : B
  ============================
   verify (x :-> w \+ y :-> Y) (x ::= v) [vfun _ h => h = x :-> v \+ y :-> Y]
]]

*)

by heval.

(*
Alternatively:
 apply: val_write. 
*)

Qed.

(** ** Verifying the factorial procedure mechanically

Proving an assignment for two non-aliased pointers was a simple
exercise, so now we can proceed to a more interesting program, which
features loops and conditional expressions, namely, imperative
implementation of the factorial function.
*)

Fixpoint fact_pure n := if n is n'.+1 then n * (fact_pure n') else 1.

(** 

Next, we define the loop invariant [fact_inv], which constraints the
heap shape and the values of the involved pointers, [n] and [acc].

*)

Definition fact_inv (n acc : ptr) (N : nat) h : Prop := 
  exists n' a': nat, 
  [/\ h = n :-> n' \+ acc :-> a' & 
      (fact_pure n') * a' = fact_pure N].

Definition fact_tp n acc := 
  unit -> {N}, 
     STsep (fact_inv n acc N, 
           [vfun (res : nat) h => fact_inv n acc N h /\ res = fact_pure N]).

(** 

The definition of the factorial "accumulator" loop is then represented
as a recursive function, taking as arguments the two pointers, [n] and
[acc], and also a unit value. 

*)


Program Definition fact_acc (n acc : ptr): fact_tp n acc := 
  Fix (fun (loop : fact_tp n acc) (_ : unit) => 
    Do (a1 <-- !acc;
        n' <-- !n;
        if n' == 0 then ret a1
        else acc ::= a1 * n';;
             n ::= n' - 1;;
             loop tt)).

(** 

The body of the accumulator loop function reproduces precisely the
factorial implementation in pseudocode. It first reads the values of
the pointers [acc] and [n] into the local variables [a1] and
[n']. Notice that the binding of the local immutable variables is
represented by the [<--] notation, which corresponds to the _bind_
operation of the Hoare monad [STsep]. The function then uses Coq's
standard conditional operator and returns a value of [a1] if [n'] is
zero using the monadic [ret] operator. In the case of [else]-branch,
the new values are written to the pointers [acc] and [n], after which
the function recurs.

Stating the looping function like this leaves us with one obligation
to prove.


*)

Next Obligation. 

(** 

As in the previous example, we start by transforming the goal, so the
logical variable [N], coming from the specification of [fact_tp] would
be exposed as an assumption. We immediately move it to the context
along with the initial heap [i].

*)

apply: ghR=>i N. 

(**
[[
  ...
  i : heap
  N : nat
  ============================
   fact_inv n acc N i ->
   valid i ->
   verify i
     (a1 <-- !acc;
      n' <-- !n;
      (if n' == 0 then ret a1 else acc ::= a1 * n';; n ::= n' - 1;; loop tt))
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

We next case-analyse on the top assumption with the invariant
[fact_inv] to acquire the equality describing the shape of the heap
[i]. We then rewrite [i] in place and move a number of hypotheses to
the context.

*)

case=>n' [a'][->{i}] Hi _. 

(**

Now the goal has the shape [verify (n :-> n' \+ acc :-> a') ...],
which is suitable to be hit with the automation by means of the
[heval].

*)

heval. 

(**
[[
  ...
  n' : nat
  a' : nat
  Hi : fact_pure n' * a' = fact_pure N
  ============================
   verify (n :-> n' \+ acc :-> a')
     (if n' == 0 then ret a' else acc ::= a' * n';; n ::= n' - 1;; loop tt)
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

The goal, containing a use of the conditional operator, is natural to
be proved on case analysis on the condition [n' == 0].

*)

case X: (n' == 0). 

(** 

[[
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = true
  ============================
   verify (n :-> n' \+ acc :-> a') (ret a')
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

To prove it, we will need one of the numerous [val]-lemmas, delivered
as a part of HTT libraries and directly corresponding to the rules of
separation logic. The general recipe on acquiring intuition for the
lemmas applicable for each particular [verify]-goal is to make use of
SSReflect's [Search] machinery. For instance, in this particular case,
given that the command to be verified (i.e., the second argument of
[verify]) is [ret a'], let us try the following query.

*)

Search _ (verify _ _ _) (ret _).

(**

The request results report, in particular, on the following lemma
found:

[[
val_ret
   forall (A : Type) (v : A) (i : heapPCM) (r : cont A),
   (valid i -> r (Val v) i) -> verify i (ret v) r
]]

*)

- apply: val_ret=>/= _. 

(** 

The remaining part of the proof of this goal has absolutely nothing to
do with program verification and separation logic and accounts to
combining a number of arithmetical facts in the goal via the
hypotheses [Hi] and [X]. 
*)

  move/eqP: X=>Z; subst n'.
  split; first by exists 0, a'=>//.
  by rewrite mul1n in Hi.

(** 

The second goal requires to satisfy the specification of a sequence of
assignments, which can be done automatically using the [heval] tactic.

*)

heval. 

(** 
[[
  loop : fact_tp n acc
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = false
  ============================
   verify (n :-> (n' - 1) \+ acc :-> (a' * n')) (loop tt)
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

*)

apply: (gh_ex N). 

(**

Now to verify the call to [loop], we can apply the lemma [val_doR],
corresponding to the rule %\Rule{App}%, which will replace the goal by
the precondition from the spec [fact_tp n acc]. In HTT there are
several lemmas tackling this kind of a goal, all different in the way
they treat the postconditions, so in other cases it is recommended to
run [Search "val_do"] to see the full list and chose the most
appropriate one.

%\httl{val\_doR}%

*)

apply: val_doR=>// _.

(**
[[
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = false
  ============================
   fact_inv n acc N (n :-> (n' - 1) \+ acc :-> (a' * n'))
]]

As in the case of the previous goal, the remaining proof is focused on
proving a statement about a heap and natural numbers, so we just
present its proof below without elaborating on the details, as they
are standard and mostly appeal to propositional reasoning and
rewriting by lemmas from SSReflect's [ssrnat] module.

*)

exists (n'-1), (a' * n'); split=>//=. 
rewrite -Hi=>{Hi}; rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
by case: n' X=>//= n' _; rewrite subn1 -pred_Sn. 
Qed.

(** 

We can now implement the main body of the factorial function, which
allocates the necessary pointers, calls the accumulator loop and then
frees the memory.

*)

Program Definition fact (N : nat) : 
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fact_pure N /\ h = Unit]) := 
  Do (n   <-- alloc N;
      acc <-- alloc 1;
      res <-- fact_acc n acc tt;
      dealloc n;;
      dealloc acc;;
      ret res).

Next Obligation.

(** 

Since the spec of [fact] does not have any logical variables (its
postcondition only mentions its argument [N]), there is no need to
make use of the [ghR] lemma. 

*)

rewrite /conseq =>/=.

(** 
[[
  N : nat
  ============================
   forall i : heap,
   i = Unit ->
   verify i
     (n <-- alloc N;
      acc <-- alloc 1;
      res <-- fact_acc n acc tt; dealloc n;; dealloc acc;; ret res)
     (fun (y : ans nat) (m : heap) =>
      i = Unit -> [vfun res h => res = fact_pure N /\ h = Unit] y m)
]]
*)

move=>_ ->.
heval=>n; heval=>acc; rewrite joinC unitR.

(**

We have now came to the point when the function [fact_acc], which we
have previously verified, is going to be invoked. In this case,
however, the tactic [val_doR] will not work immediately, so we will
first need to reduce the program to be verified from the binding
command to a mere function call be means of HTT's [bnd_seq] lemma,
which tackles the binding _combined_ with a call to a user-defined
function, and this is exactly our case. Next, we instantiate the
[fact_acc] specification's logical variable [N] by applying [gh_ex]
and proceed with the application of [val_doR].

*)

apply: bnd_seq=>/=; apply: (gh_ex N); apply: val_doR=>//.

(** 

The first of the resulting two goals is an obligation arising from the
need to prove [fact_acc]'s precondition.

*)

 - by exists N, 1; rewrite muln1.

(**

The second goal is the remainder of the program's body, which performs
deallocation, so the proof for it is accomplished mostly by applying
[heval] tactic.

*)

by move=>_ _ [[n'][a'][->] _ ->] _; heval.  
Qed.

(**

* On shallow and deep embedding
%\label{sec:shallowdeep}%

A noteworthy trait of HTT's approach to verification of effectful
programs is its use of _shallow embedding_ of the imperative language
%\index{shallow embedding}% to the programming language of Coq. In
fact, the imperative programs that we have written, e.g., the
factorial procedure, are mere Coq programs, written in Coq syntax with
a number of HTT-specific notations. Moreover, the Hoare triples, by
means of which we have provided the specifications to the
heap-manipulating programs are nothing but specific types defined in
Coq. This is what makes the way effectful programs encoded _shallow_:
the new programming language of imperative programs and their
Hoare-style specifications has been defined as a subset of Coq
programming language, so most of the Coq's infrastructure for parsing,
type-checking, name binding and computations could be reused off the
shelf. In particular, shallow embedding made it possible to represent
the variables in imperative programs as Coq's variables, make use of
Coq's conditional operator and provide specifications to higher-order
procedures without going into the need to design a higher-order
version of a separation logic first (since the specifications in HTT
are just types of monadically-typed expressions). Furthermore, shallow
embedding provided us with a benefit of reusing Coq's name binding
machinery, so we could avoid the problem of _name capturing_ by means
using the approach known as %\emph{Higher-Order Abstract
Syntax}~\cite{Pfenning-Elliott:PLDI88}%, representing immutable
variables by Coq's native variables (disguised by the binding notation
[<--]).

%\index{DSL|see{domain-specific language}}% 
%\index{domain-specific language}% 
%\index{internal DSL}%
%\index{embedded DSL}%

To summarize, shallow embedding is an approach of implementing
programming languages (not necessarily in Coq), characterized by
representation of the language of interest (usually called a
_domain-specific language_ or DSL) as a subset of another
general-purpose _host_ language, so the programs in the former one are
simply the programs in the latter one. The idea of shallow embedding
originates at early '60s with the beginning of era of the Lisp
programming language%~\cite{Graham:BOOK}\index{Lisp}%, which, thanks
to its macro-expansion system, serves as a powerful platform to
implement DSLs by means of shallow embedding (such DSLs are sometimes
called _internal_ or _embedded_). Shallow embedding in the world of
practical programming is advocated for a high speed of language
prototyping and the ability to re-use most of the host language
infrastructure.

An alternative approach of implementing and encoding programming
languages in general and in Coq in particular is called _deep
embedding_, and amounts to the implementation of a language of
interest from scratch, essentially, writing its parser, interpreter
and type-checker in a general-purpose language. In practice, deep
embedding is preferable when the overall performance of the
implemented language runtime is of more interest than the speed of DSL
implementation, since then a lot of intermediate abstractions, which
are artefacts of the host language, can be avoided.

In the world of mechanized program verification, both approaches, deep
and shallow embedding, have their own strengths and weaknesses.

Although implementations of deeply embedded languages and calculi
naturally tend to be more verbose, design choices in them are usually
simpler to explain and motivate. Moreover, the deep embedding approach
makes the problem of name binding to be explicit, so it would be
appreciated as an important aspect in the design and reasoning about
programming
languages%~\cite{Aydemir-al:POPL08,Weirich-al:ICFP11,Chargueraud:JAR12}%. We
believe, these are the reason why this approach is typically chosen as
a preferable one when teaching program specification and verification in
Coq%~\cite{Pierce-al:SF}%.

Importantly, deep embedding gives the programming language implementor
the _full control_ over its syntax and semantics.%\footnote{This
observation is reminiscent to the reasond of using deep embedding in
the practical world.}% In particular, the expressivity limits of a
defined logic or a type system are not limited by expressivity of
Coq's (or any other host language's) type system. Deep embedding makes
it much more straightforward to reason about _pairs_ of programs by
means of defining the relations as propositions on pairs of syntactic
trees, which are implemented as elements of corresponding datatypes.
This point, which we deliberately chose not to discuss in detail in
this course, becomes crucial when one needs to reason about the
correctness of program transformations and optimizing
compilers%~\cite{Appel:BOOK14}%. In contrast, the choice of shallow
embedding, while sparing one the labor of implementing the parser,
name binder and type checker, may limit the expressivity of the
logical calculus or a type system to be defied. In the case of HTT,
for instance, it amounts to the impossibility to specify programs that
store _effectful functions_ and their specifications into a
heap.%\footnote{This limitation can be, however, overcome by
postulating necessary \emph{axioms} on top of CIC.}%

In the past decade Coq has been used in a large number of projects
targeting formalization of logics and type systems of various
programming languages and proving their soundness, with most of them
preferring the deep embedding approach to the shallow one. We believe
that the explanation of this phenomenon is the fact that it is much
more straightforward to define semantics of a deeply-embedded
"featherweight" calculus%~\cite{Igarashi-al:TOPLAS01}% and prove
soundness of its type system or program logic, given that it is the
_ultimate goal_ of the research project. However, in order to use the
implemented framework to specify and verify realistic programs, a
significant implementation effort is required to extend the deep
implementation beyond the "core language", which makes shallow
embedding more preferable in this case---a reason why this way has
been chosen by HTT.

* Soundness of Hoare Type Theory

Because of shallow embedding, every valid Coq program is also a valid
HTT program. However, as it has been hinted at the beginning of
%Section~\ref{sec:htt-intro}%, imperative programs written in HTT
cannot be simply executed, as, due to presence of general loops and
recursion, they simply may not terminate. At this point, a reader may
wonder, what good is verification of programs that cannot be run and
what is it that we have verified?

To answer this question, let us revise how the _soundness_ of a Hoare
logic is defined. HTT takes definition of a Hoare triple (or, rather,
a Hoare type, since in HTT specs are types) from
page%~\pageref{pg:triple}% literally but implements it not via an
operational semantics, i.e., defining how a program _should be run_,
but using a denotational semantics%~\cite[Chapter~5]{Winskel:BOOK}%,
i.e., defining what a program _is_. The HTT library comes with a
module [stmod] that defines denotational semantics of HTT
commands%\footnote{I.e., monadic values constructed by means of the
write/alloc/dealloc/read/return commands and standard Coq connectives,
such as conditional expression or pattern matching.}% and Hoare
triples, defined as types. Each command is represented by a function,
which sometimes referred to as _state transformer_, in the sense that
it takes a particular heap and transforms it to another heap, also
returning some result. The denotational semantics of HTT commands in
terms of state-transforming functions makes it also possible to define
what is a semantics of a program resulting from the use of the [Fix]
operator (%Section~\ref{sec:factver}%).%\footnote{In fact, a standard
construction from the domain theory is used: employing Knaster-Tarski
theorem on a lattice of monotone functions, which is, however, outside
of the scope of these notes, so we redirect the reader to the relevant
literature: Glynn Winskel's book for the theoretical
construction~\cite[Chapters~8--10]{Winskel:BOOK} or Adam Chlipala's
manuscript covering a similar
implementation~\cite[\S~7.2]{Chlipala:BOOK}.}% The semantics of Hoare
types $\spec{h~|~P(h)}-\spec{\res, h~|~Q(\res, h)}$ is defined as
_sets_ of state transforming functions, taking a heap satisfying $P$
to the result and heap satisfying $Q$. Therefore, the semantic account
of the verification (which is implemented by means of type-checking in
Coq) is checking that semantics of a particular HTT program (i.e., a
state-transforming function) lies _within_ the semantics of its type
as a set.

%\index{extraction}%

If execution of programs verified in HTT is of interest, it can be
implemented by means of _extraction_ of HTT commands into programs
into an external language, which supports general recursion natively
(e.g., Haskell). In fact, such extraction has been implemented in the
first release of HTT%~\cite{Nanevski-al:JFP08}%, but was not ported to
the latest release.

* Specifying and verifying programs with linked lists

We conclude this chapter with a _tour de force_ of separation logic in
HTT by considering specification verification of programs operating
with single-linked lists. Unlike the factorial example, an
implementation of single-linked lists truly relies on pointers, and
specifying such datatypes and programs is an area where separation
logic shines.

%\index{single-linked lists}%

On a surface, a single-linked list can be represented by a pointer,
which points to its head.

*)

Definition llist (T : Type) := ptr.

Section LList.
Variable T : Type.
Notation llist := (llist T).

(** 

However, in order to specify and prove interesting facts about
imperative lists, similarly to the previous examples, we need to
establish a connection between what is stored in a list heap and a
purely mathematical sequence of elements. This is done using the
_recursive predicate_ [lseg], which relates two pointers, [p] and [q],
pointing correspondingly to the head and to the tail of the list and a
logical sequence [xs] of elements stored in the list.

*)

Fixpoint lseg (p q : ptr) (xs : seq T): Pred heap := 
  if xs is x::xt then 
    [Pred h | exists r h', 
       h = p :-> x \+ (p .+ 1 :-> r \+ h') /\ h' \In lseg r q xt]
  else [Pred h | p = q /\ h = Unit].

(** 

The notation [[Pred h | ...]] is just an abbreviation for a function
of type [heap -> Prop], where [h] is assumed to be of type [heap]. The
notation [h \In f] is a synonym for [f h] assuming [f] is a predicate
of type [heap -> Prop].

The following lemma [lseg_null] states a fact, which is almost
obvious: given that the heap [h], corresponding to a linked list, is a
valid one (according to its notion of validity as a PCM) and the head
pointer of a list structure is [null], then its tail pointer is [null]
as well, and the overall list is empty.

*)

Lemma lseg_null xs q h : 
         valid h -> h \In lseg null q xs -> 
         [/\ q = null, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] D /= H; first by case: H=><- ->.
case: H D=>r [h'][->] _. 
(**
[[
  ...
  r : ptr
  h' : heap
  ============================
   valid (null :-> x \+ (null.+1 :-> r \+ h')) ->
   [/\ q = null, x :: xs = [::] & null :-> x \+ (null.+1 :-> r \+ h') = Unit]
]]

In the process of the proof we are forced to use the validity of a
heap in order to derive a contradiction. In the case of heap's
validity, one of the requirements is that every pointer in it is not
[null]. We can make it explicit by rewriting the top assumption with
one of numerous HTT's lemmas about heap validity (use the [Search]
machinery to find the others).

%\httl{hvalidPtUn}%

*)

rewrite hvalidPtUn. 
(**
[[
  ...
  ============================
   [&& null != null, valid (null.+1 :-> r \+ h')
     & null \notin dom (null.+1 :-> r \+ h')] ->
   [/\ q = null, x :: xs = [::] & null :-> x \+ (null.+1 :-> r \+ h') = Unit]
]]

The conjunct [null != null] in the top assumption is enough to
complete the proof by implicit discrimination.

*)

done.
Qed. 

(**  

We can now define a particular case of linked
lists---_null-terminating_ lists and prove the specification of a
simple insertion program, which allocates a new memory cell for an
element [x] and makes it to be a new head of a list pointed by
[p]. The allocation is performed via the primitive [allocb], which
allocates a number of subsequent heap pointers (two in this case, as
defined by its second argument) and sets all of them to point to the
value provided.

%\httl{allocb}%
*)

Definition lseq p := lseg p null.

Program Definition insert p x : 
  {xs}, STsep (lseq p xs, [vfun y => lseq y (x::xs)]) :=
  Do (q <-- allocb p 2; 
      q ::= x;;
      ret q). 
Next Obligation. 
apply: ghR=>i xs H _; heval=>x1; rewrite unitR -joinA; heval. 
Qed.

(** 

Next, we are going to give a specification to the list
"beheading"---removing the head element of a list. For this, we will
need a couple of auxiliary lemmas involving the list heap predicate
[lseg_neq]. The first one, [lseq_null] is just a specialization of the
previously proved [lseg_null.]

*)


Lemma lseq_null xs h : valid h -> h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

(** 

The next lemma, [lseq_pos], states that is a head of a linked list,
defined by a heap [h], is not [null], then it can be "beheaded". That
is, there will exist a head value [x], a "next" [r] and a residual
heap [h'], such that the heap [h'] corresponds to the list's tail,
which is expressed by SSReflect's [behead] function.

*)

Lemma lseq_pos xs p h : 
        p != null -> h \In lseq p xs -> 
        exists x, exists r, exists h', 
          [/\ xs = x :: behead xs, 
              p :-> x \+ (p .+ 1 :-> r \+ h') = h & h' \In lseq r (behead xs)].
Proof.
case: xs=>[|x xs] /= H []; first by move=>E; rewrite E eq_refl in H.
by move=>y [h'][->] H1; heval.
Qed.

(** 

We can finally define and specify the HTT procedure [remove], which
returns the current head of the list and returns the pointer to its
next element (or [null]) if the list is empty.

%\newpage%

*)


Program Definition 
remove p : {xs}, STsep (lseq p xs, [vfun y => lseq y (behead xs)]) :=
  Do (if p == null then ret p 
      else pnext <-- !(p .+ 1);
           dealloc p;; 
           dealloc p .+ 1;;
           ret pnext). 

(** 

The proof is straightforward and employs both lemmas [lseq_null] to
prove the "[null]" case and [lseq_pos] for the case when the list has
at least one element.

*)

Next Obligation.
apply: ghR=>i xs H V; case: ifP H=>H1.
- by rewrite (eqP H1); case/(lseq_null V)=>->->; heval. 
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by heval; rewrite 2!unitL.
Qed.

End LList.

(*******************************************************************)
(**                     * Exercices *                              *)
(*******************************************************************)

(** 
---------------------------------------------------------------------
Exercise [Swapping two values]
---------------------------------------------------------------------

Implement in HTT a function that takes as arguments two pointers, [x]
and [y], which point to natural numbers, and swaps their
values. Reflect this effect in the function's specification and verify
it.

Hint: Instead of reading the value of a pointer into a variable [t]
using the [t <-- !p] notation, you might need to specify the _type_ of
the expected value explicitly by using the "de-sugared" version of the
command [t <-- read T p], where [T] is the expected type. This way,
the proof will be more straightforward.

*)

Program Definition swap (x y : ptr):
  {(a b : nat)},
  STsep (fun h => h = x :-> a \+ y :-> b,
        [vfun (_: unit) h => h = x :-> b \+ y :-> a]) :=
  Do (vx <-- read nat x;
      vy <-- read nat y;
      x ::= vy;;
      y ::= vx).
Next Obligation.
apply:ghR=>_ [a b]->/= V.
by heval.
Qed.

(**
---------------------------------------------------------------------
Exercise [Swapping two values without heval]
---------------------------------------------------------------------

Try to redo the previous exercise _without_ using the automation
provided by the [heval] tactic. The goal of this exercise is to
explore the library of HTT lemmas, mimicking the rules of the
separation logic. You can alway displat the whole list of the
available lemmas by running the command [Search _ (verify _ _ _)] and
then refine the query for specific programs (e.g., [read] or [write]).
*)

Program Definition swap' (x y : ptr):
  {(a b : nat)},
  STsep (fun h => h = x :-> a \+ y :-> b,
        [vfun (_: unit) h => h = x :-> b \+ y :-> a]) :=
  Do (vx <-- read nat x;
      vy <-- read nat y;
      x ::= vy;;
      y ::= vx).
Next Obligation.
apply:ghR=>_ [a b]->/= V.
apply: bnd_seq; apply: val_read=>_.
apply: bnd_seq; apply: val_readR =>/= _.
apply: bnd_writeR=>/=.
by apply val_writeR=>/=.
Qed.


(** 
---------------------------------------------------------------------
Exercise [Imperative procedure for Fibonacci numbers]
---------------------------------------------------------------------

The following program is an implementation in pseudocode of an
efficient imperative implementation of the function [fib] that
computes the [N]th Fibonacci number.  

    fun fib (N : nat): nat = {
      if N == 0 then ret 0
       else if N == 1 then ret 1
       else n <-- alloc 2;
            x <-- alloc 1;
            y <-- alloc 1;
            res <-- 
              (fix loop (_ : unit). 
                 n' <-- !n;
                 y' <-- !y;
                 if n' == N then ret y'
                 else tmp <-- !x;
                      x ::= y';;
                      x' <-- !x;
                      y ::= x' + tmp;;
                      n ::= n' + 1;;
                      loop(tt))(tt).
            dealloc n;;
            dealloc x;;
            dealloc y;;
            ret res    
    }

Your task will be to prove its correctness with respect to the "pure"
function [fib_pure] (which you should define in plain Coq) as well as
the fact that it starts and ends in an empty heap.

Hint: What is the loop invariant of the recursive computation defined
by means of the [loop] function?

Hint: Try to decompose the reasoning into verification of several code
pieces as in the factorial example and then composing them together in
the "main" function.

*)

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
        ret res).

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


(** 
%\begin{exercise}%

Define and verify function [remove_val] which is similar to remove,
but also returns the value of the last "head" of the list before
removal, in addition to the "next" pointer. Use Coq's [option] type to
account for the possibility of an empty list in the result.

%\end{exercise}%
*)

(* begin hide *)
Program Definition remove_val T p : {xs}, 
  STsep (lseq p xs, 
         [vfun y h => lseq y.1 (behead xs) h /\ 
                      y.2 = (if xs is x::xs' then Some x else None)]) := 
  Do (if p == null then ret (p, None) 
      else x <-- read T p;
           pnext <-- !(p .+ 1);
           dealloc p;; 
           dealloc p .+ 1;;
           ret (pnext, Some x)). 
Next Obligation.
apply: ghR=>i xs H V; case: ifP H=>H1.
- by rewrite (eqP H1); case/(lseq_null V)=>->->; heval. 
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by heval; rewrite 2!unitL.
Qed.
(* end hide *)



(** 

%\begin{exercise}[Imperative in-place map]% 

Define, specify and verify the imperative higher-order function
[list_map] that takes arguments two types, [S] and [T], a function [f
: T -> S] and a head [p] of a single-linked list, described by a
predicate [lseq], and changes the list in place by applying [f] to
each of its elements, while preserving the list's structure. The
specification should reflect the fact that the new "logical" contents
of the single-linked list are an [f] map-image of the old content.

%\hint% The lemmas [lseq_null] and [lseq_pos], proved previously,
 might be useful in the proof of the established specification.

%\hint% A tail-recursive call can be verified via HTT's [val_do]
 lemma, reminiscent to the rule %\Rule{App}%. However, the heap it
 operates with should be "massaged" appropriately via PCM's lemmas
 [joinC] and [joinA].

%\end{exercise}%

*)

Definition mapT T S (f : T -> S) : Type := 
  forall p, {xs}, STsep (@lseq T p xs, 
                         [vfun y h => y = tt /\ @lseq S p (map f xs) h]).

Program Definition list_map T S p (f : T -> S) :
   {xs}, STsep (@lseq T p xs, 
                [vfun y h => y = tt /\ @lseq S p (map f xs) h]) :=
    Fix (fun (loop : mapT f) (p : ptr) =>      
      Do (if p == null 
          then ret tt 
          else x <-- read T p;
               next <-- (read ptr p .+ 1);
               p ::= f x;;
               loop next)) p.
Next Obligation.
apply: ghR=>h xs H V. 
case X: (p0 == null).
- apply: val_ret=>_ /=;  split=>//. 
  by move/eqP: X H=>-> /=; case/(lseq_null V)=>->->. 
case/negbT /lseq_pos /(_ H): X=>x[next][h'][Z1] Z2 H1; subst h.
heval.
move/validR: V=> V1; apply: (gh_ex (behead xs)).
rewrite [_ \+ h']joinC joinC -joinA; apply: val_do=>//=.
case=>m[_]H2 V2; split=>//.
rewrite [_ \+ p0 :-> _]joinC joinC. 
by rewrite Z1 /=; exists next, m; rewrite joinA.
Qed.


(**

%\begin{exercise}%

Let us define the following auxiliary predicates, where [shape_rev]
splits the heap into two disjoint linked lists (by means of the
separating conjunction [#]).

*)

Definition shape_rev T p s := [Pred h | h \In @lseq T p.1 s.1 # @lseq T p.2 s.2].

(** 

Then the in-place list reversal is implemented by means of the
recursive function [reverse] with a loop invariant expressed using the
type [revT].

*)

Definition revT T : Type := 
  forall p, {ps}, STsep (@shape_rev T p ps, [vfun y => lseq y (rev ps.1 ++ ps.2)]).

Program Definition 
reverse T p : {xs}, STsep (@lseq T p xs, [vfun y => lseq y (rev xs)]) :=
  Do (let: reverse := Fix (fun (reverse : revT T) p => 
                        Do (if p.1 == null then ret p.2 
                            else xnext <-- !p.1 .+ 1;
                                 p.1 .+ 1 ::= p.2;;
                                 reverse (xnext, p.1)))
      in reverse (p, null)).
(** 
We invite the reader to conduct the verification of [reverse], proving
that it satisfies the given specification.

%\hint% Try to design the proof on a paper first.

%\hint% It might be a good idea to make use of the previously proved
 lemmas [lseq_null] and [lseq_pos], used as _views_.

*)

(* begin hide *)
Next Obligation. 
apply: ghR=>i [x1 x2][i1][i2][->] /= [H1 H2] V; case: eqP H1=>[->|E].
- by case/(lseq_null (validL V))=>->->; rewrite unitL; heval. 
case/lseq_pos=>[|xd [xn][h'][->] <- /= H1]; first by case: eqP.
heval; rewrite -!joinA -!(joinCA h'); apply: (gh_ex (behead x1, xd::x2)).
by apply: val_doR=>//; [heval | move=>x m; rewrite rev_cons cat_rcons]. 
Qed.
Next Obligation.
apply: ghR=>i xs H _; apply: (gh_ex (xs, Nil T)).
by apply: val_doR=>//; [exists i; heval | move=>x m /=; rewrite cats0]. 
Qed.
(* end hide *)

(** %\end{exercise}% *)


End HTT.
