(**  %\chapter{Views and Boolean Reflection}% *)

From mathcomp
Require Import ssreflect ssrfun eqtype ssrnat ssrbool prime eqtype.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BoolReflect.

(**  * Proving with views in SSReflect

*)

Lemma imp_trans4 P Q R S: (P -> Q) -> (R -> S) -> (Q -> R) -> P -> S.
Proof.
move=>H1 H2 H3.

(** 
[[
  P : Type
  Q : Type
  R : Type
  S : Type
  H1 : P -> Q
  H2 : R -> S
  H3 : Q -> R
  ============================
   P -> S
]]

Since we are proficient in the proofs via implications, it is not
difficult to construct the explicit proof term by a series of [apply:]
tactic calls or via the [exact:] tactic. Let us do something
different, though, namely _weaken_ the top assumption of the goal by
means of applying the hypothesis [H1] to it, so the overall goal will
become [Q -> S].

*)

move=>p; move: (H1 p).

(** 

This proof pattern of "switching the view" turns out to be so frequent
that SSReflect introduces a special _view_ tactical [/] for it, which
is typically combined with the standard [move] or [case] tactics. In
particular, the last proof line could be replaced by the following:

*)

Undo.
move/H1.

(** 

[[
  ...
  H1 : P -> Q
  H2 : R -> S
  H3 : Q -> R
  ============================
   Q -> S
]]
*)

by move/H3 /H2.
Qed.

(** ** Combining views and bookkeeping *)

Goal forall P Q R, P -> (P -> Q -> R) -> Q -> R.
Proof.
by move=>P Q R p H /(H p).

(**

In fact, this prove can be shortened even further by using the view
notation for the _top_ assumption (denoted using the underscore):

*)

Undo.
move=> P Q R p. 
by move/(_ p). 
Qed.

(** 

The last proof script first moved for assumptions to the context, so
the goal became [(P -> Q -> R) -> R]. Next, it partially applied the
top assumption [(P -> Q -> R)] to [p : P] from the context and moved
the result back to the goal, so it became [(P -> Q) -> P -> Q], which
is trivially provable.

It is also possible to use views in combination with the [case]
tactics, which first performs the "view switch" via the view lemma
provided and then case-analysed on the result, as demonstrated by the
following proof script:

*)

Goal forall P Q R, (P -> Q /\ R) -> P -> R.
Proof.
move=> P Q R H.
by case/H. 
Qed.

(** ** Using views with equivalences *)

Variables S T: bool -> Prop.
Hypothesis STequiv : forall a b, T a <-> S (a || b). 

Lemma ST_False a b: (T a -> False) -> S (a || b) -> False.
Proof.
by move=>H /STequiv.
Qed.

(**

** Declaring view hints

*)

Check iffRL.

(** 
[[
iffRL
     : forall P Q : Prop, (P <-> Q) -> Q -> P
]]
*)

Lemma ST_False' a b: (T a -> False) -> S (a || b) -> False.
Proof.
move=> H.
move/(iffRL (STequiv a b)).
done.
Qed.

(**

The view switch on the second line of the proof is what has been done
implicitly in the previous case: the implicit view [iffRL] has been
applied to the call of [STequiv], which was in its turn supplied the
necessary arguments [a] and [b], inferred by the system from the goal,
so the type of [(STequiv a b)] would match the parameter type of
[iffRL], and the whole application would allow to make a view switch
in the goal.  What is left behind the scenes is the rest of the
attempts made by Coq/SSReflect in its search for a suitable implicit
view, which ended when the system has finally picked [iffRL].

In general, the design of powerful view hints is non-trivial, as they
should capture precisely the situation when the "view switch" is
absolutely necessary and the implicit views will not "fire"
spuriously. In the same time, implicit view hints is what allows for
the smooth implementation of the boolean reflection.

*)

(** ** Applying view lemmas to the goal

Similarly to how they are used for _assumptions_, views can be used to
interpret the goal by means of combining the Coq's standard [apply]
and [exact] tactics with the view tactical [/]. In the case
if [H] is a view lemma, which is just an implication [P -> Q], where
[Q] is the statement of the goal, the enhanced tactic [apply/ H] will
work exactly as the standard SSReflect's [apply:], that is, it will
replace the goal [Q] with [H]'s assumption [P] to prove.

*)

Definition TS_neg: forall a, T (negb a) -> S ((negb a) || a).
Proof.
move=>a H. 
apply/STequiv.
done.
Qed.

(** 

The view switch on the goal via [apply/STequiv] immediately changed
the goal from [S ((negb a) || a)] to [T (negb a)], so the rest of the
proof becomes trivial. Again, notice that the system managed to infer
the right arguments for the [STequiv] hypothesis by analysing the
goal.

*)

Print TS_neg.

(**

[[
TS_neg = 
  fun (a : bool) (H : T (negb a)) =>
  (fun F : T (negb a) =>
     iffLR (Q:=S (negb a || a)) (STequiv (negb a) a) F) H
     : forall a : bool, T (negb a) -> S (negb a || a)
]]

*)


(** * [Prop] versus [bool] *)

Inductive isPrime n : Prop := 
 | IsOne of n = 1
 | IsOther of forall n1 n2, n = n1 * n2 -> (n1 = 1 /\ n2 = n) \/ (n1 = n /\ n2 = 1).

(** 

Such definition, although correct, is quite inconvenient to use, as it
does not provide a direct way to _check_ whether some particular
number (e.g., 239) is prime or not. Instead, it requires on to
construct a proof of primality for _each_ particular case using the
constructors (or the contradiction, which would imply that the number
is not prime). *)

Eval compute in prime 239.
(** 
[[
     = true
     : bool
]]

The [bool]-returning functions (i.e., decidable predicates) can be
naturally _injected_ into propositions of sort [Prop] by simply
comparing their result with [true] via propositional equality. This is
what is done by SSReflect automatically using the implicit _coercion_,
imported by the [ssrbool] module:

[[
Coercion is_true (b: bool) := b = true
]]

This coercion can be seen as an implicit type conversion, familiar
from the languages like Scala or Haskell, and it inserted by Coq
automatically every time it expects to see a proposition of sort
[Prop], but instead encounters a boolean value. Let us consider the
following goal as an example:

*)

Goal prime (16 + 14) -> False.
Proof. done. Qed.

(** 

As we can see, the proof is rather short, and, in fact, done by
Coq/SSReflect fully automatically. In fact, the system first
_computes_ the value of [prime (16 + 14)], which is, obviously
[false]. Then the boolean value [false] is coerced into the
propositional equality [false = true], as previously described. The
equality is then automatically discriminated (%see
Section~\ref{sec:discr}%), which allows the system to infer the
falsehood, completing the proof.

*)

(** ** Using conditionals in predicates

The ternary conditional operator [if-then-else] is something that
programmers use on a regular basis. However, when it comes to the
specifications in the form of Coq's standard propositions it turns out
one cannot simply employ the [if-then-else] connective in them, as it
expects its conditional argument to be of type [bool]. This
restriction is, again, a consequence of the fact that the result of
[if-then-else] expression should be computable, which conflicts with
the fact that not every proposition is decidable and, hence, there is
no sound way overload the conditional operator, so it would rely on
the existence of the proof of its conditional (or its negation).

[[
Definition prime_spec_bad n m : Prop := m = (if isPrime n then 1 else 2).

Error: In environment
m : nat
n : nat
The term "isPrime n" has type "Prop" while it is expected to have type "bool".
]]

Fortunately, the computable predicates are free from this problem, so
on can freely use them in the conditionals:

*)

Definition prime_spec n m : Prop := m = (if prime n then 1 else 2).

(** ** Case analysing on a boolean assumption *)

Definition discr_prime n := (if prime n then 0 else 1) + 1.

(** 

Let us now prove that the definition [prime_spec] gives a precise
specification of the function [discr_prime]:

*)

Lemma discr_prime_spec : forall n, prime_spec n (discr_prime n).
Proof.
move=>n. rewrite /prime_spec /discr_prime.

(**

[[
  n : nat
  ============================
   (if prime n then 0 else 1) + 1 = (if prime n then 1 else 2)
]]

*)
by case: (prime n)=>//.
Qed.

(** * The reflect type family

Being able to state all the properties of interest in a way that they
are decidable is a true blessing. However, even though encoding
everything in terms of [bool]-returning functions and connectives
comes with the obvious benefits, reasoning in terms of [Prop]s might
be more convenient when the information of the structure of the proofs
matters. For instance, let us consider the following situation:

*)

Variables do_check1 do_check2 : nat -> bool.
Hypothesis H: forall n, do_check2 n -> prime n.

Lemma check_prime n : (do_check1 n) && (do_check2 n) -> prime n.

(** 

The lemma [check_prime] employs the boolean conjunction [&&] from the
[ssrbool] module in its assumption, so we know that its result is some
boolean value. However simply case-analysing on its component does not
bring any results. What we want indeed is a way to _decompose_ the
boolean conjunction into the components and then use the hypothesis
[H]. This is what could be accomplished easily had we employed the
_propositional conjunction_ [/\] instead, as it comes with a
case-analysis principle.


*)

Abort.

(**

This is why we need a mechanism to conveniently switch between two
possible representation. SSReflect solves this problem by employing
the familiar rewriting machinery and introducing the inductive predicate
family [reflect], which connects propositions an booleans:

*)

Module Inner.

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT  of   P : reflect P true
  | ReflectF  of ~ P : reflect P false.

End Inner.

(**

Similarly to the custom rewriting rules, the [reflect] predicate is
nothing but a convenient way to encode a "truth" table with respect to
the predicate [P], which is [reflect]'s only parameter. In other
words, the propositions [(reflect P b)] ensures that [(is_true b)] and
[P] are logically equivalent and can be replaced one by another. For
instance, the following rewriting lemmas %\index{rewriting lemma}% can
be proved for the simple instances of [Prop].

*)

Lemma trueP : reflect True true.
Proof. by constructor. Qed.

Lemma falseP : reflect False false.
Proof. by constructor. Qed.

(** 

The proofs with boolean truth and falsehood can be then completed by
case analysis, as with any other rewriting rules:

*)

Goal false -> False.
Proof. 
case:falseP. 
- done.
done.
Qed.

(** ** Reflecting logical connectives

The true power of the [reflect] predicate, though, is that it might be
put to work with arbitrary logical connectives and user-defined
predicates, therefore delivering the rewriting principles, allowing
one to switch between [bool] and [Prop] (in the decidable case) by
means of rewriting lemmas. SSReflect comes with a number of such
lemmas, so let us consider one of them, [andP].

*)

Lemma andP (b1 b2 : bool) : reflect (b1 /\ b2) (b1 && b2).
Proof. by case b1; case b2; constructor=> //; case. Qed.

(** 

Notice that [andP] is stated over two boolean variables, [b1] and
[b2], which, nevertheless, are treated as instances of [Prop] in the
conjunction [/\], being implicitly coerced. 

We can now put this lemma to work and prove our initial example:

*)

Lemma check_prime n : (do_check1 n) && (do_check2 n) -> prime n.
Proof.
case: andP=>//.

(**
[[
  n : nat
  ============================
   do_check1 n /\ do_check2 n -> true -> prime n
]]

Case analysis on the rewriting rule [andP] generates two goals, and
the second one has [false] as an assumption, so it is discharged
immediately by using [//]. The remaining goal has a
shape that we can work with, so we conclude the proof by applying the
hypothesis [H] declared above.

*)

by case=>_ /H.
Qed.

(** 

Although the example above is a valid usage of the reflected
propositions, SSReflect leverages the rewriting with respect to
boolean predicates even more by defining a number of _hint views_ for
the rewriting lemmas that make use of the [reflect] predicates. This
allows one to use the rewriting rules (e.g., [andP]) in the form of
_views_ , which can be applied directly to an assumption or a goal, as
demonstrated by the next definition.

*)

Definition andb_orb b1 b2: b1 && b2 -> b1 || b2.
Proof.
case/andP=>H1 H2.
by apply/orP; left.
Qed.

Print andb_orb.


(**

Let us take a brief look to the obtained proof term for [andb_orb].

[[
andb_orb = 
fun (b1 b2 : bool) (goal : b1 && b2) =>
(fun F : forall (a : b1) (b : b2),
                (fun _ : b1 /\ b2 => is_true (b1 || b2)) (conj a b) =>
 match
   elimTF (andP b1 b2) goal as a return ((fun _ : b1 /\ b2 => is_true (b1 || b2)) a)
 with
 | conj x x0 => F x x0
 end)
  (fun (H1 : b1) (_ : b2) =>
   (fun F : if true then b1 \/ b2 else ~ (b1 \/ b2) =>
    introTF (c:=true) orP F) (or_introl H1))
     : forall b1 b2 : bool, b1 && b2 -> b1 || b2
]]
*)

Check elimTF.

(** 
[[
elimTF
     : forall (P : Prop) (b c : bool),
       reflect P b -> b = c -> if c then P else ~ P
]]


** Reflecting decidable equalities

Logical connectives are not the only class of inductive predicates
that is worth building a [reflect]-based rewriting principle for.
Another useful class of decidable propositions, which are often
reflected, are equalities.

Let us see how switching between decidable [bool]-returning equality
[==] (defined in the SSReflect's module [eqtype]) and the familiar
propositional equality can be beneficial.

*)

Definition foo (x y: nat) := if x == y then 1 else 0.

(** 

The function [foo] naturally uses the natural numbers' boolean
equality [==] in its body, as it is the only one that can be used in
the conditional operator. The next goal, though, assumes the
propositional equality of [x] and [y], which are passed to [foo] as
arguments.

*)

Goal forall x y, x = y -> foo x y = 1.
Proof.
move=>x y; rewrite /foo.

(** 

[[
  x : nat
  y : nat
  ============================
   x = y -> (if x == y then 1 else 0) = 1
]]

*)

by move/eqP=>->.
Qed.

(*******************************************************************)
(**                     * Exercices *                              *)
(*******************************************************************)

(**
---------------------------------------------------------------------
Exercise [Reflecting exclusive disjunction]
---------------------------------------------------------------------

Let us define a propositional version of the _exclusive or_ predicate
as well as its boolean version (in a curried form, so it takes just
one argument and returns a function):

*)

Definition XOR (P Q: Prop) := (P \/ Q) /\ ~(P /\ Q).

Definition xorb b := if b then negb else fun x => x.

(** 

Now, prove the following _generalized_ reflection lemma [xorP_gen] and
its direct consequence, the usual reflection lemma [xorP]:

Hint: recall that the _reflect_ predicate is just a rewriting rule, so
one can perform a case analysis on it.

*)

Lemma xorP_gen (b1 b2 : bool)(P1 P2: Prop): 
  reflect P1 b1 -> reflect P2 b2 -> reflect (XOR P1 P2) (xorb b1 b2).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma xorP (b1 b2 : bool): reflect (XOR b1 b2) (xorb b1 b2).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 
---------------------------------------------------------------------
Exercise [Alternative formulation of exclusive disjunction]
---------------------------------------------------------------------

Let us consider an alternative version of exclusive or, defined by
means of the predicate [XOR']:

*)

Definition XOR' (P Q: Prop) := (P /\ ~Q) \/ (~P /\ Q).

(** 

Prove the following equivalence lemma between to versions of [XOR]:

*)

Lemma XORequiv P Q: XOR P Q <-> XOR' P Q.
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 
The final step is to use the equivalence we have just proved in order
to establish an alternative version of the reflective correspondence
of exclusive disjunction.

Hint: use the [Search] machinery to look for lemmas that might help to
leverage the equivalence between two predicates and make the
following proof to be a one-liner.

*)

Lemma xorP' (b1 b2 : bool): reflect (XOR' b1 b2) (xorb b1 b2).
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.

 
(** 
---------------------------------------------------------------------
Exercise [Reasoning with boolean xor]
---------------------------------------------------------------------

Unsurprisingly, every statement about exclusive or, e.g., its
commutativity and associativity, is extremely easy to prove when it is
considered as a boolean function. Demonstrate it by proving the
following lemmas in one line each.

*)

Lemma xorbC (b1 b2: bool) : (xorb b1 b2) = (xorb b2 b1). 
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



Lemma xorbA (b1 b2 b3: bool) : (xorb (xorb b1 b2) b3) = (xorb b1 (xorb b2 b3)). 
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.



(** 

It is also not difficult to prove the propositional counterparts of
the above lemmas for decidable propositions, reflected by them, hence
the following exercise.

*)

(**
---------------------------------------------------------------------
Exercise [Commutativity and associativity of specialized XOR]
---------------------------------------------------------------------

Prove the following specialized lemmas for decidable propositions
represented y booleans (without using the [intuition] tactic):

*)

Lemma xorCb (b1 b2: bool) : (XOR b1 b2) <-> (XOR b2 b1). 
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


Lemma xorAb (b1 b2 b3: bool) : (XOR (XOR b1 b2) b3) <-> (XOR b1 (XOR b2 b3)). 
Proof.
(* fill in your proof here instead of [admit] *)
Admitted.


(** 

Hint: in the proof of [xorAb] the generalized reflection lemma
[xorP_gen] might come in handy.

Hint: A redundant assumption [H] in the context can be erased by
typing [clear H] or [move => {H}]. The latter form can be combined
with any bookkeeping sequence, not only with [move] tactics.

Hint: The Coq's embedded tactic [intuition] can be helpful for
automatically solving goals in propositional logic.

*)

(**
---------------------------------------------------------------------
Exercise [Uniquely existing pairs of elements]
---------------------------------------------------------------------

Sometimes, the statement ``there exists unique $x$ and $y$, such that
$P(x, y)$ holds'' is mistakingly formalized as $\exists ! x \exists !
y P(x, y)$. In fact, the latter assertion is much weaker than the
previous one. The goal of this exercise is to demonstrate this
formally.

First, prove the following lemma, stating that the first assertion can
be weakened from the second one.

*)

Lemma ExistsUnique1 A (P : A -> A -> Prop): 
  (exists !x, exists y, P x y) -> 
  (exists !x, exists y, P y x) ->
  (exists !x, exists !y, P x y).

(**

The notation [exists ! x, P x] is an abbreviation for the sigma-type,
whose second component is the higher-order predicate unique, defined
as follows:

*)

Print unique.

(**
[[
unique = 
fun (A : Type) (P : A -> Prop) (x : A) =>
P x /\ (forall x' : A, P x' -> x = x')
     : forall A : Type, (A -> Prop) -> A -> Prop
]]

As we can see, the definition [unique] not just ensures that [P x]
holds (the left conjunct), but also that any [x'] satisfying [P] is,
in fact, equal to [x]. As on the top level [unique] is merely a
conjunction, it can be decomposed by [case] and proved using the
[split] tactics.

*)

Proof.
Admitted.

(**

Next, let us make sure that the statement in the conclusion of lemma
[ExistsUnique1], in fact, admits predicates, satisfied by non-uniquely
defined pair [(x, y)]. You goal is to prove that the following
predicate [Q], which obviously satisfied by [(true, true)], [(false,
true)] and [(false, false)] is nevertheless a subject of the second
statement.

*)

Definition Q x y : Prop := 
  (x == true) && (y == true) || (x == false).

Lemma qlm : (exists !x, exists !y, Q x y).
Proof.
Admitted.

(**

%hint% The following lemma [eqxx], stating that the boolean equality
 [x == x] always holds, might be useful for instantiating arguments
 for hypotheses you will get during the proof.

*)

Check eqxx.

(**
[[
eqxx
     : forall (T : eqType) (x : T), x == x
]]

Finally, you are invited to prove that the second statement is
_strictly_ weaker than the first one by proving the following lemma,
which states that the reversed implication of the two statements for
an arbitrary predicate [P] implies falsehood.

*)

Lemma ExistsUnique2 : 
  (forall A (P : A -> A -> Prop),
   (exists !x, exists !y, P x y) ->
   (exists !x, exists y, P x y) /\ (exists !x, exists y, P y x)) ->
  False.
Proof.
Admitted.


(**
%\end{exercise}%
*)


End BoolReflect.
