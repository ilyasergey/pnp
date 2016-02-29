Set Automatic Coercions Import.
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import pred domain pcm unionmap heap stmod stsep. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation cont A := (ans A -> heap -> Prop).

Lemma vrf_mono A (e : ST A) i (r1 r2 : cont A) : 
        r1 <== r2 -> verify i e r1 -> verify i e r2. 
Proof. 
by move=>H H1 /H1 {H1} [H1 H2]; split=>// y m H3 /(H2 _ _ H3); apply: H. 
Qed.

Lemma vrfV A (e : ST A) i (r : cont A) : 
       (valid i -> verify i e r) -> verify i e r. 
Proof. by move=>H V; apply: H. Qed.

Lemma bnd_is_try (A B : Type) (e1 : ST A) (e2 : A -> ST B) i r : 
        verify i (ttry e1 e2 (throw B)) r ->
        verify i (bind e1 e2) r.
Proof.
move=>H; apply: frame0=>D.
case: {H D} (H D) (D)=>[[i1]][i2][->][[H1 [H2 H3]]] _ T D.
split=>[|y m].
- split=>[|x m]; first by apply: fr_pre H1.
  by case/(locality D H1)=>m1 [->][_]; move/H2; apply: fr_pre.
move=>{D} H; apply: T=>h1 h2 E.
rewrite {i1 i2 H1 H2 H3}E in H * => D1 [H1][H2] H3.
case: H=>[[x][h][]|[e][->]]; move/(locality D1 H1);
case=>[m1][->][D2] T1; move: (T1); [move/H2 | move/H3]=>H4.
- move=>T2; case/(locality D2 H4): (T2)=>m3 [->][D3].
  by exists m3; do !split=>//; left; exists x; exists m1.
exists m1; do !split=>//; right; exists e; exists m1; split=>//. 
move=>j1 j2 E D _; rewrite {m1 D2}E in T1 D H4 *.
by exists j1; do !split=>//; move=>k1 k2 -> D2 ->.
Qed. 

Lemma val_do' A (e : ST A) i j (r : cont A) :
        (valid i -> pre_of e i) -> 
        (forall x m, post_of e (Val x) i m -> 
                       valid (m \+ j) -> r (Val x) (m \+ j)) ->
        (forall x m, post_of e (Exn x) i m -> 
                       valid (m \+ j) -> r (Exn x) (m \+ j)) ->
        verify (i \+ j) e r.
Proof.
move=>H1 H2 H3; apply: frame; apply: frame0=>D; split; first by apply: H1.
by case=>x m H4 D1 D2; [apply: H2 | apply: H3].
Qed.

Lemma val_ret A v i (r : cont A) : 
       (valid i -> r (Val v) i) -> verify i (ret v) r. 
Proof. by rewrite -[i]unitL=>H; apply: val_do'=>// x m [->] // [->]. Qed.

Lemma val_read A v x i (r : cont A) : 
        (valid (x :-> v \+ i) -> r (Val v) (x :-> v \+ i)) -> 
        verify (x :-> v \+ i) (read A x) r.
Proof.
move=>*; apply: val_do'; first by [exists v];
by move=>y m [<-]; move/(_ v (erefl _))=>// [->].
Qed.

Lemma val_write A B (v : A) (w : B) x i (r : cont unit) : 
        (valid (x :-> v \+ i) -> r (Val tt) (x :-> v \+ i)) -> 
        verify (x :-> w \+ i) (write x v) r.
Proof.
move=>*; apply: val_do'; first by [exists B, w];
by move=>y m [// [->] ->].
Qed.

Lemma val_alloc A (v : A) i (r : cont ptr) : 
        (forall x, valid (x :-> v \+ i) -> r (Val x) (x :-> v \+ i)) -> 
        verify i (alloc v) r.
Proof.
move=>H; rewrite -[i]unitL; apply: val_do'=>//; 
by move=>y m [x][//][-> ->]; apply: H.
Qed.

Lemma val_allocb A (v : A) n i (r : cont ptr) : 
        (forall x, valid (updi x (nseq n v) \+ i) -> 
           r (Val x) (updi x (nseq n v) \+ i)) -> 
        verify i (allocb v n) r.
Proof.
move=>H; rewrite -[i]unitL; apply: val_do'=>//;
by move=>y m [x][//][->->]; apply: H.
Qed.

Lemma val_dealloc A (v : A) x i (r : cont unit) : 
        (valid i -> r (Val tt) i) -> 
        verify (x :-> v \+ i) (dealloc x) r.
Proof.
move=>H; apply: val_do'; first by [exists A; exists v];
by move=>y m [//][->] ->; rewrite unitL.
Qed.

Lemma val_throw A x i (r : cont A) : 
        (valid i -> r (Exn x) i) -> verify i (throw A x) r.
Proof.
move=>H; rewrite -[i]unitL; apply: val_do'=>//;
by move=>y m [->] // [->]; rewrite unitL.
Qed.

(* sequential composition: try e e1 e2 or bind e1 e2 can be reduced to *)
(* a verify e1 followed by verify of the continuations. *)

Lemma try_seq A B e (e1 : A -> ST B) e2 i (r : cont B) :
        verify i e (fun y m => 
          match y with 
            Val x => verify m (e1 x) r
          | Exn x => verify m (e2 x) r
          end) ->
        verify i (ttry e e1 e2) r. 
Proof.
have L P Q j k : valid j -> (P # top) j -> (P --o Q) j k -> valid k.
- move=>V H1; rewrite -[j]unitR in V *.
  by case/(locality V H1)=>k' [->][]; rewrite unitR.
move=>H Vi; case: (H Vi)=>H1 H2 {H}; split.
- exists i, Unit; rewrite unitR; do !split=>//;
  move=>x m H; move: (L _ _ _ _ Vi H1 H)=>Vm;
  by case: (H2 _ _ H Vm Vm).
move=>x m H Vm; case: {H} (H i Unit)=>//; first by rewrite unitR.
- do !split=>//; move=>x' m' H; move: (L _ _ _ _ Vi H1 H)=>Vm';
  by case: (H2 _ _ H Vm' Vm'). 
move=>m'; rewrite unitR; case=><-{m'} [_]; case;
case=>y [m'][H]; move: (L _ _ _ _ Vi H1 H)=>Vm';
by case: (H2 _ _ H Vm' Vm')=>T1 T2 T3; apply: T2.
Qed.

Lemma bnd_seq A B e1 (e2 : A -> ST B) i (r : cont B) :
        verify i e1 (fun y m => 
          match y with 
            Val x => verify m (e2 x) r
          | Exn x => valid m -> r (Exn x) m
          end) ->
        verify i (bind e1 e2) r. 
Proof.
move=>H; apply: bnd_is_try; apply: try_seq.
by apply: vrf_mono H=>y m; case: y=>// e; apply: val_throw. 
Qed.


(***********************************************)
(* Specialized lemmas for instantiating ghosts *)
(* and doing sequential composition            *)
(***********************************************)

Lemma gh_conseq A C t (s : C -> spec A) (e : STbin (logvar s)) :  
        conseq e (s t).
Proof.
case E: (s t)=>[a b] /= h H; rewrite -[h]unitR.
apply: val_do'=>[|x m|x m]; try by move/(_ t); rewrite E !unitR.
by exists t; rewrite E. 
Qed.

(* a lemma for instantiating a ghost *)

Lemma gh_ex A C (t : C) i (s : C -> spec A) e (r : cont A) : 
        verify i (do' (gh_conseq (t:=t) e)) r ->
        verify i (with_spec (logvar s) e) r.
Proof.
move=>H /H /=; case E: (s t)=>[a b] /= [H1 H2]; split=>[|y m].
- case: H1=>h1 [h2][->][T1 T2]. 
  by exists h1, h2; do !split=>//; exists t; rewrite E.
move=>H3; apply: H2=>h1 h2 E1 Vi E2.
have: exists x, let '(p, _) := s x in p h1. 
- by exists t; rewrite E.
case/(H3 _ _ E1 Vi)=>m1 [->][Vm] /(_ t). 
by rewrite E; exists m1.
Qed.

Implicit Arguments gh_ex [A C i s e r].


(* Two val_do lemmas which simplify binary posts *)
(* The first lemma applies framing as well; the second is frameless *)
(* We shoudn't need bnd_do or ttry_do, as these can be obtained *)
(* by first calling vrf_seq *)

Section ValDoLemmas.
Variables (A B : Type) (p : Pred heap) (q : ans A -> Pred heap).

Lemma val_do i j {e} (r : cont A) : 
        (valid i -> i \In p) -> 
        (forall x m, q (Val x) m -> valid (m \+ j) -> r (Val x) (m \+ j)) ->
        (forall x m, q (Exn x) m -> valid (m \+ j) -> r (Exn x) (m \+ j)) ->            
        verify (i \+ j) (with_spec (binarify p q) e) r.
Proof. 
move=>H1 H2 H3 V; apply: val_do' (V)=>//=;
move=>x m /(_ (H1 (validL V))); [apply: H2 | apply: H3].
Qed.

Lemma val_do0 i {e} (r : cont A) : 
        (valid i -> i \In p) -> 
        (forall x m, q (Val x) m -> valid m -> r (Val x) m) ->
        (forall x m, q (Exn x) m -> valid m -> r (Exn x) m) ->            
        verify i (with_spec (binarify p q) e) r.
Proof. 
move=>H1 H2 H3; rewrite -[i]unitR; apply: val_do=>// x m;
by rewrite unitR; eauto.
Qed.

End ValDoLemmas.


(******************************************)
(* Lemmas for pulling out ghost variables *)
(******************************************)

Section Ghosts.
Variables (A B C : Type) (e : ST A).

Lemma ghE (s : B -> C -> spec A) : 
        conseq e (logvar (fun x => logvar (s x))) <->
        conseq e (logvar (fun xy => s xy.1 xy.2)).
Proof.
split.
- move=>/= H1 i [[x y]] H2.
  have: exists x1 y1, let '(p, _) := s x1 y1 in p i by exists x, y. 
  by move/H1; apply: vrf_mono=>y1 m1 T1 [x2 y2]; apply: (T1 x2 y2). 
move=>/= H1 i [x][y] H2.  
have: exists x, let '(p, _) := s x.1 x.2 in p i by exists (x, y). 
by move/H1; apply: vrf_mono=>y1 m1 T1 x2 y2; apply: (T1 (x2, y2)).
Qed.

Lemma gh (p : B -> pre) (q : B -> ans A -> pre) :
        (forall i x, p x i -> valid i -> verify i e (q x)) ->
        conseq e (logvar (fun x => binarify (p x) (q x))).
Proof.
move=>H1 i /= [x] H2 V; case: (H1 _ _ H2 V V)=>H3 _.
by split=>// y m H5 H6 z H7; case: (H1  _ _ H7 V V)=>_; apply. 
Qed.

End Ghosts.

(* some additional stuff *)

Definition pull (A : Type) x (v:A) := (joinC (x :-> v), joinCA (x :-> v)).
Definition push (A : Type) x (v:A) := (joinCA (x :-> v), joinC (x :-> v)).

(* some notation for writing posts that signify no exceptions are raised *)

Definition vfun' A (f : A -> heap -> Prop) : cont A := 
  fun y i => if y is Val v then f v i else false.

Notation "[ 'vfun' x => p ]" := (vfun' (fun x => p)) 
  (at level 0, x ident, format "[ 'vfun'  x  =>  p ]") : fun_scope.

Notation "[ 'vfun' x : aT => p ]" := (vfun' (fun (x : aT) => p)) 
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'vfun' x i => p ]" := (vfun' (fun x i => p)) 
  (at level 0, x ident, format "[ 'vfun'  x  i  =>  p ]") : fun_scope.

Notation "[ 'vfun' ( x : aT ) i => p ]" := (vfun' (fun (x : aT) i => p)) 
  (at level 0, x ident, only parsing) : fun_scope.




