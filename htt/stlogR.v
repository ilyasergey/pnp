Set Automatic Coercions Import.
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import pred prelude pcm unionmap heap heaptac stmod stsep stlog. 
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**************************************************************************)
(* This file implements two different automations related to Hoare logic. *)
(*                                                                        *)
(* First automation concerns selection of Hoare-style rule for symbolic   *)
(* evaluation. The first command of the program determines the applicable *)
(* rule uniquely. The implemented automation picks out this rule, and     *)
(* applies it, while using AC-theory of heaps to rearrange the goal, if   *)
(* necessary for the rule to apply.                                       *)
(*                                                                        *)
(* Second automation concerns pulling ghost variables out of a Hoare      *)
(* type. The non-automated lemmas do this pulling one variable at a       *)
(* time. The automation pulls all the variable at once.                   *)
(**************************************************************************)

(****************************************************************)
(* First, the reflection mechanism for search-and-replace       *)
(* pattern-matching on heap expressions; the AC theory of heaps *)
(****************************************************************)

Structure tagged_heap := Tag {untag :> heap}.

Definition right_tag := Tag.
Definition left_tag := right_tag.
Canonical Structure found_tag i := left_tag i.

Definition form_axiom k r (h : tagged_heap) := untag h = k \+ r.

Structure form (k r : heap) :=
  Form {heap_of :> tagged_heap; 
        _ : form_axiom k r heap_of}.

Implicit Arguments Form [].

Lemma formE r k (f : form k r) : untag f = k \+ r.
Proof. by case: f=>[[j]] /=; rewrite /form_axiom /= => ->. Qed.

Lemma found_pf k : form_axiom k Unit (found_tag k). 
Proof. by rewrite /form_axiom unitR. Qed.
 
Canonical Structure heap_found k := Form k Unit (found_tag k) (found_pf k).

Lemma left_pf h r (f : forall k, form k r) k : 
        form_axiom k (r \+ h) (left_tag (untag (f k) \+ h)).
Proof. by rewrite formE /form_axiom /= joinA. Qed.

Canonical Structure search_left h r (f : forall k, form k r) k :=
  Form k (r \+ h) (left_tag (untag (f k) \+ h)) (left_pf h f k).

Lemma right_pf h r (f : forall k, form k r) k :
        form_axiom k (h \+ r) (right_tag (h \+ f k)).
Proof. by rewrite formE /form_axiom /= joinCA. Qed.

Canonical Structure search_right h r (f : forall k, form k r) k := 
  Form k (h \+ r) (right_tag (h \+ f k)) (right_pf h f k).

(**********************************************************)
(* Reflective lemmas that apply module AC-theory of heaps *)
(**********************************************************)

Notation cont A := (ans A -> heap -> Prop).

Section EvalDoR.
Variables (A B : Type) (p : heap -> Prop) (q : ans A -> heap -> Prop).

Lemma val_doR e i j (f : forall k, form k j) (r : cont A) :
        (valid i -> p i) -> 
        (forall x m, q (Val x) m -> 
           valid (untag (f m)) -> r (Val x) (f m)) ->
        (forall x m, q (Exn x) m -> 
           valid (untag (f m)) -> r (Exn x) (f m)) -> 
        verify (f i) (with_spec (binarify p q) e) r.
Proof.
move=>H1 H2 H3; rewrite formE; apply: (val_do H1).
- by move=>x m; move: (H2 x m); rewrite formE.
by move=>x m; move: (H3 x m); rewrite formE.
Qed.

End EvalDoR.

(* We maintain three different kinds of lemmas *)
(* in order to streamline the stepping *)
(* The only important ones are the val lemmas, the bnd and try *)
(* are there just to remove some spurious hypotheses about validity, and make the *)
(* verification flow easier *)

(* Each call to some bnd_* or try_* lemma is really a call to bnd_seq or try_seq *)
(* followed by a val_* lemma. Except that doing things in such a sequence *)
(* actually gives us some additional, spurious, valididity hypotheses, which we *)
(* always discard anyway. However the discarding interrupts automation, so we want to avoid it *)
 
(* However, we only need only val_doR lemma *)
(* This one is always applied by hand, not automatically, so *)
(* if we need to prefix it with a call to bnd_seq or try_seq, we can *)
(* do that by hand *)

(* If we were to do this by hand, whenever *)
(* there should be a nicer way to do this *)
(* e.g., suppress all the spruious validity as a default *)
(* and let the user generate them by hand at the leaves, when necessary *)


Section EvalRetR.
Variables (A B : Type). 

Definition val_retR := val_ret.

Lemma try_retR e1 e2 (v : A) i (r : cont B) :
        verify i (e1 v) r -> verify i (ttry (ret v) e1 e2) r.
Proof. by move=>H; apply: try_seq; apply: val_ret. Qed.

Lemma bnd_retR e (v : A) i (r : cont B) : 
        verify i (e v) r -> verify i (bind (ret v) e) r.
Proof. by move=>H; apply: bnd_seq; apply: val_ret. Qed. 

End EvalRetR.


Section EvalReadR.
Variables (A B : Type).

Lemma val_readR v x i (f : form (x :-> v) i) (r : cont A) : 
        (valid (untag f) -> r (Val v) f) -> 
        verify f (read A x) r.
Proof. by rewrite formE; apply: val_read. Qed.

Lemma try_readR e1 e2 v x i (f : form (x :-> v) i) (r : cont B) : 
        verify f (e1 v) r -> 
        verify f (ttry (read A x) e1 e2) r. 
Proof. by move=>H; apply: try_seq; apply: val_readR. Qed.

Lemma bnd_readR e v x i (f : form (x :-> v) i) (r : cont B) : 
        verify f (e v) r -> 
        verify f (bind (read A x) e) r.
Proof. by move=>H; apply: bnd_seq; apply: val_readR. Qed.

End EvalReadR.


Section EvalWriteR. 
Variables (A B C : Type).

Lemma val_writeR (v : A) (w : B) x i (f : forall k, form k i) (r : cont unit) : 
        (valid (untag (f (x :-> v))) -> r (Val tt) (f (x :-> v))) -> 
        verify (f (x :-> w)) (write x v) r.
Proof. by rewrite !formE; apply: val_write. Qed.

Lemma try_writeR e1 e2 (v : A) (w : B) x i 
                 (f : forall k, form k i) (r : cont C) : 
        verify (f (x :-> v)) (e1 tt) r -> 
        verify (f (x :-> w)) (ttry (write x v) e1 e2) r. 
Proof. by move=>H; apply: try_seq; apply: val_writeR. Qed.

Lemma bnd_writeR e (v : A) (w : B) x i (f : forall k, form k i) (r : cont C) : 
        verify (f (x :-> v)) (e tt) r -> 
        verify (f (x :-> w)) (bind (write x v) e) r. 
Proof. by move=>H; apply: bnd_seq; apply: val_writeR. Qed.

End EvalWriteR.


Section EvalAllocR.
Variables (A B : Type). 

Definition val_allocR := val_alloc.

Lemma try_allocR e1 e2 (v : A) i (r : cont B) : 
        (forall x, verify (x :-> v \+ i) (e1 x) r) ->
        verify i (ttry (alloc v) e1 e2) r.
Proof. by move=>H; apply: try_seq; apply: val_alloc. Qed.

Lemma bnd_allocR e (v : A) i (r : cont B) : 
        (forall x, verify (x :-> v \+ i) (e x) r) ->
        verify i (bind (alloc v) e) r.
Proof. by move=>H; apply: bnd_seq; apply: val_alloc. Qed.

End EvalAllocR. 


Section EvalAllocbR.
Variables (A B : Type). 

Definition val_allocbR := val_allocb. 

Lemma try_allocbR e1 e2 (v : A) n i (r : cont B) : 
        (forall x, verify (updi x (nseq n v) \+ i) (e1 x) r) ->
        verify i (ttry (allocb v n) e1 e2) r.
Proof. by move=>H; apply: try_seq; apply: val_allocb. Qed.

Lemma bnd_allocbR e (v : A) n i (r : cont B) : 
        (forall x, verify (updi x (nseq n v) \+ i) (e x) r) ->
        verify i (bind (allocb v n) e) r.
Proof. by move=>H; apply: bnd_seq; apply: val_allocb. Qed.

End EvalAllocbR. 


Section EvalDeallocR.
Variables (A B : Type).

Lemma val_deallocR (v : A) x i (f : forall k, form k i) (r : cont unit) : 
        (valid (untag (f Unit)) -> r (Val tt) (f Unit)) -> 
        verify (f (x :-> v)) (dealloc x) r.
Proof. by rewrite !formE unitL; apply: val_dealloc. Qed.

Lemma try_deallocR e1 e2 (v : A) x i (f : forall k, form k i) (r : cont B) :
        verify (f Unit) (e1 tt) r -> 
        verify (f (x :-> v)) (ttry (dealloc x) e1 e2) r.
Proof. by move=>H; apply: try_seq; apply: val_deallocR. Qed.

Lemma bnd_deallocR e (v : A) x i (f : forall k, form k i) (r : cont B) : 
        verify (f Unit) (e tt) r -> 
        verify (f (x :-> v)) (bind (dealloc x) e) r.
Proof. by move=>H; apply: bnd_seq; apply: val_deallocR. Qed.

End EvalDeallocR.


Section EvalThrowR.
Variables (A B : Type).

Definition val_throwR := val_throw. 

Lemma try_throwR e e1 e2 i (r : cont B) : 
        verify i (e2 e) r -> 
        verify i (ttry (throw A e) e1 e2) r.
Proof. by move=>H; apply: try_seq; apply: val_throw. Qed.
 
Lemma bnd_throwR e e1 i (r : cont B) : 
        (valid i -> r (Exn e) i) -> 
        verify i (bind (throw A e) e1) r.
Proof. by move=>H; apply: bnd_seq; apply: val_throw. Qed.

End EvalThrowR.


(****************************************************)
(* Automating the selection of which lemma to apply *)
(* (reflective implementation of the hstep tactic)  *)
(****************************************************)

(* Need to case-split on bnd_, try_, or a val_ lemma. *)
(* Hence, three classes of canonical structures.      *)

Structure val_form A i r (p : Prop):=
  ValForm {val_pivot :> ST A;
           _ : p -> verify i val_pivot r}.

Structure bnd_form A B i (e : A -> ST B) r (p : Prop) :=
  BndForm {bnd_pivot :> ST A;
           _ : p -> verify i (bind bnd_pivot e) r}.

Structure try_form A B i (e1 : A -> ST B) 
                         (e2 : exn -> ST B) r (p : Prop) :=
  TryForm {try_pivot :> ST A;
           _ : p -> verify i (ttry try_pivot e1 e2) r}.

(* The main lemma which triggers the selection. *)

Lemma hstep A i (r : cont A) p (e : val_form i r p) :
        p -> verify i e r.
Proof. by case:e=>[?]; apply. Qed.

(* First check if matching on bnd_ or try_. If so, switch to searching *)
(* for bnd_ or try_form, respectively. Otherwise, fall through, and    *)
(* continue searching for a val_form. *)

Lemma bnd_case_pf A B i (s : A -> ST B) r p (e : bnd_form i s r p) :
        p -> verify i (bind e s) r.
Proof. by case:e=>[?]; apply. Qed.

Canonical Structure 
  bnd_case_form A B i (s : A -> ST B) r p (e : bnd_form i s r p) := 
  ValForm (bnd_case_pf e).

Lemma try_case_pf A B i (s1 : A -> ST B) (s2 : exn -> ST B) r p
                        (e : try_form i s1 s2 r p) : 
        p -> verify i (ttry e s1 s2) r.
Proof. by case:e=>[?]; apply. Qed.

(* After that, find the form in the following list.  Notice that the list *)
(* can be extended arbitrarily in the future. There is no centralized     *)
(* tactic to maintain. *)

Canonical Structure val_ret_form A v i r := 
  ValForm (@val_retR A v i r).
Canonical Structure bnd_ret_form A B s v i r := 
  BndForm (@bnd_retR A B s v i r).
Canonical Structure try_ret_form A B s1 s2 v i r :=
  TryForm (@try_retR A B s1 s2 v i r).

Canonical Structure val_read_form A v x r j f := 
  ValForm (@val_readR A v x j f r).
Canonical Structure bnd_read_form A B s v x r j f := 
  BndForm (@bnd_readR A B s v x j f r).
Canonical Structure try_read_form A B s1 s2 v x r j f := 
  TryForm (@try_readR A B s1 s2 v x j f r).  

Canonical Structure val_write_form A B v w x r j f := 
  ValForm (@val_writeR A B v w x j f r).
Canonical Structure bnd_write_form A B C s v w x r j f := 
  BndForm (@bnd_writeR A B C s v w x j f r).
Canonical Structure try_write_form A B C s1 s2 v w x r j f := 
  TryForm (@try_writeR A B C s1 s2 v w x j f r).

Canonical Structure val_alloc_form A v i r := 
  ValForm (@val_allocR A v i r).
Canonical Structure bnd_alloc_form A B s v i r := 
  BndForm (@bnd_allocR A B s v i r).
Canonical Structure try_alloc_form A B s1 s2 v i r := 
  TryForm (@try_allocR A B s1 s2 v i r).

Canonical Structure val_allocb_form A v n i r := 
  ValForm (@val_allocbR A v n i r).
Canonical Structure bnd_allocb_form A B s v n i r := 
  BndForm (@bnd_allocbR A B s v n i r).
Canonical Structure try_allocb_form A B s1 s2 v n i r := 
  TryForm (@try_allocbR A B s1 s2 v n i r).

Canonical Structure val_dealloc_form A v x r j f := 
  ValForm (@val_deallocR A v x j f r).
Canonical Structure bnd_dealloc_form A B s v x r j f := 
  BndForm (@bnd_deallocR A B s v x j f r).
Canonical Structure try_dealloc_form A B s1 s2 v x r j f := 
  TryForm (@try_deallocR A B s1 s2 v x j f r).

(* Second automation *)

(**************************************************************************)
(* A simple canonical structure program to automate applying ghE and gh.  *)
(*                                                                        *)
(* The gh_form pivots on a spec, and computes as output the following.    *)
(* - rT is a product of types of all encounted ghost vars.                *)
(* - p and q are pre and post parametrized by rT that should be output by *)
(*   the main lemma.                                                      *)
(*                                                                        *)
(* In the future, rT should be a list of types, rather than a product,    *)
(* but that leads to arity polimorphism, and dependent programming, which *)
(* I want to avoid for now.                                               *)
(**************************************************************************)

Section Automation.
Structure tagged_spec A := gh_step {gh_untag :> spec A}.
Canonical Structure gh_base A (s : spec A) := gh_step s.

Definition gh_axiom A rT p q (pivot : tagged_spec A) := 
  gh_untag pivot = logvar (fun x : rT => binarify (p x) (q x)).

Structure gh_form A rT (p : rT -> pre) (q : rT -> cont A) := GhForm {
   gh_pivot :> tagged_spec A;
   _ : gh_axiom p q gh_pivot}. 

(* the main lemma that automates the applications of ghE and gh *)

Lemma ghR A e rT p q (f : @gh_form A rT p q) : 
        (forall i x, p x i -> valid i -> verify i e (q x)) ->
        conseq e f. 
Proof. by case: f=>p' ->; apply: gh. Qed.

(* base case; check if we reached binarify *)

Lemma gh_base_pf A rT (p : rT -> pre) (q : rT -> cont A) :
        gh_axiom p q (gh_base (logvar (fun x => binarify (p x) (q x)))).
Proof. by []. Qed.

Canonical gh_base_struct A rT p q := GhForm (@gh_base_pf A rT p q).
                 
(* inductive case; merge adjacent logvars and continue *)

Lemma gh_step_pf A B rT p q (f : forall x : A, @gh_form B rT (p x) (q x)) : 
        gh_axiom (fun xy => p xy.1 xy.2) (fun xy => q xy.1 xy.2)
                 (gh_step (logvar (fun x => f x))).
Proof. 
congr (_, _).
- apply: fext=>i; apply: pext; split. 
  - by case=>x; case: (f x)=>[_ ->] /= [y H]; exists (x, y). 
  by case; case=>x y; exists x; case: (f x)=>[_ ->]; exists y.  
apply: fext=>y; apply: fext=>i; apply: fext=>m; apply: pext; split.
- by move=>H [x z] /= H1; case: (f x) (H x)=>[_ ->]; apply.  
by move=>H x; case: (f x)=>[_ ->] z; apply: (H (x, z)).
Qed.

Canonical gh_step_struct A B rT p q f := GhForm (@gh_step_pf A B rT p q f). 

End Automation.


(* we keep some tactics to kill final goals, which *)
(* are usually full of existentials *)
Ltac vauto := (do ?econstructor=>//).
Ltac step := (apply: hstep=>/=).

Ltac hhauto := (vauto; try by [heap_congr])=>//.
Ltac heval := do ![step | by hhauto].

