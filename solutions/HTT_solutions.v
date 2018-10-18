From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition llist (T : Type) := ptr.

Section LList.
Variable T : Type.
Notation llist := (llist T).

Fixpoint lseg (p q : ptr) (xs : seq T): Pred heap := 
  if xs is x::xt then 
    [Pred h | exists r h', 
       h = p :-> x \+ (p .+ 1 :-> r \+ h') /\ h' \In lseg r q xt]
  else [Pred h | p = q /\ h = Unit].

Lemma lseg_null xs q h : 
         valid h -> h \In lseg null q xs -> 
         [/\ q = null, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] D /= H; first by case: H=><- ->.
case: H D=>r [h'][->] _. 
by rewrite validPtUn. 
Qed. 

Definition lseq p := lseg p null.

Program Definition insert p x : 
  {xs}, STsep (lseq p xs, [vfun y => lseq y (x::xs)]) :=
  Do (q <-- allocb p 2; 
      q ::= x;;
      ret q). 
Next Obligation. 
apply: ghR=>i xs H _. 
heval=>x1. 
rewrite unitR -joinA. 
heval. 
Qed.

Lemma lseq_null xs h : valid h -> h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

Lemma lseq_pos xs p h : 
        p != null -> h \In lseq p xs -> 
        exists x, exists r, exists h', 
          [/\ xs = x :: behead xs, 
              p :-> x \+ (p .+ 1 :-> r \+ h') = h & h' \In lseq r (behead xs)].
Proof.
case: xs=>[|x xs] /= H []. 
 - move=>E. 
   by rewrite E eq_refl in H.
by move=>y [h'][->] H1; heval.
Qed.

Program Definition 
remove p : {xs}, STsep (lseq p xs, [vfun y => lseq y (behead xs)]) :=
  Do (if p == null then ret p 
      else pnext <-- !(p .+ 1);
           dealloc p;; 
           dealloc p .+ 1;;
           ret pnext). 

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
by apply:ghR=>_ [a b]->/= _; heval.
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
        [vfun _ h => h = x :-> b \+ y :-> a]) :=
  Do (vx <-- read nat x;
      vy <-- read nat y;
      x ::= vy;;
      y ::= vx).
Next Obligation.
apply:ghR=>_ [a b]-> _.
apply: bnd_seq; apply: val_read => _.
apply: bnd_seq; apply: val_readR => _.
apply: bnd_seq; apply: val_write => _.
by apply: val_writeR.
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
    Do (n' <-- read nat n;
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
---------------------------------------------------------------------
Exercise [Value-returning list beheading]
---------------------------------------------------------------------

Define and verify function [remove_val] which is similar to remove,
but also returns the value of the last "head" of the list before
removal, in addition to the "next" pointer. Use Coq's [option] type to
account for the possibility of an empty list in the result.

*)

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

(** 
---------------------------------------------------------------------
Exercise [Imperative in-place map]
---------------------------------------------------------------------

Define, specify and verify the imperative higher-order function
[list_map] that takes arguments two types, [S] and [T], a pure
function [f : T -> S] and a head [p] of a single-linked list,
described by a predicate [lseq], and changes the list in place by
applying [f] to each of its elements, while preserving the list's
structure. The specification should reflect the fact that the new
"logical" contents of the single-linked list are an [f] map-image of
the old content.

Hint: The lemmas [lseq_null] and [lseq_pos], proved previously, might
be useful in the proof of the established specification.

Hint: A tail-recursive call can be verified via HTT's [val_do] lemma,
reminiscent to the rule %\Rule{App}%. However, the heap it operates
with should be "massaged" appropriately via PCM's lemmas [joinC] and
[joinA].

Hint: A boolean lemma [negbT] can be useful to switch between
different representations of inequality.

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
case X: (p == null).
- apply: val_ret=>_ /=;  split=>//. 
  by move/eqP: X H=>-> /=; case/(lseq_null V)=>->->. 
case/negbT /lseq_pos /(_ H): X=>x[next][h'][Z1] Z2 H1; subst h.
heval.
move/validR: V=> V1; apply: (gh_ex (behead xs)).
rewrite [_ \+ h']joinC joinC -joinA; apply: val_do=>//=.
case=>m[_]H2 V2; split=>//.
rewrite [_ \+ p :-> _]joinC joinC. 
by rewrite Z1 /=; exists next, m; rewrite joinA.
Qed.


(**
---------------------------------------------------------------------
Exercise [In-place list reversal]
---------------------------------------------------------------------

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

You're invited to conduct the verification of [reverse], proving
that it satisfies the given specification.

Hint: It might be a good idea to make use of the previously proved
lemmas [lseq_null] and [lseq_pos].

Hint: Be careful with the logical values of variables passed to the
[gh_ex] lemma before verifying a recursive call of [reverse].

Hint: A verification goal to a function defined via [Fix] can be
reduced via the [val_doR] lemma or similar ones.

Hint: The [shape_rev] predicate is in fact an existential in disguise:
it can be proved by providing appropriate witnesses.

Hint: Lemmas [rev_cons], [cat_rcons] and [cats0] from the [seq]
library will be useful for establishing equalities between lists.

*)

Next Obligation.
apply:ghR=>i[xs1 xs2]; case=>h1[h2][->{i}]/=[H1 H2] V1.
case X: (p == null) H1=>H1.
- apply: val_ret=>/=_; move/eqP: X=>X; subst p.
  move/validL: (V1)=>V3; case:(lseq_null V3 H1)=>Z1 Z2; subst xs1 h1=>/=.
  by rewrite unitL. 
case/negbT /(lseq_pos) /(_ H1): X=>x[next][h'][Exs]Z H3; subst h1.
heval; rewrite -!joinA -!(joinCA h'); apply: (gh_ex (behead xs1, x::xs2)).
apply: val_doR=>//=[V2|].
 - exists h', (p :-> x \+ (p .+ 1 :-> p1 \+ h2)); split=>//; split=>//.
   by exists p1, h2; rewrite !joinA.
by move=> z m H4 _; rewrite Exs rev_cons cat_rcons.
Qed.

Next Obligation.
apply: ghR=>i xs H V /=; apply: (gh_ex (xs, [::])).
apply: val_doR=>//=[_|]; first by exists i, Unit; rewrite unitR. 
by rewrite cats0.
Qed.
