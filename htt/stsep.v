Set Automatic Coercions Import.
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Require Import pred pcm unionmap heap stmod.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Delimit Scope stsep_scope with stsep. 
Open Scope stsep_scope.

Definition star (p1 p2 : Pred heap) : Pred heap :=
  [Pred h | exists h1, exists h2, h = h1 \+ h2 /\ h1 \In p1 /\ h2 \In p2].
Definition emp : Pred heap := eq^~ Unit. 
Definition top : Pred heap := PredT.

Notation "p1 '#' p2" := (star p1 p2) 
  (at level 57, right associativity) : rel_scope.

Definition lolli (p : _ -> Prop) q (i m : heap) := 
  forall i1 h, i = i1 \+ h -> valid i -> p i1 -> 
    exists m1, m = m1 \+ h /\ valid m /\ q i1 m1.

Notation "p '--o' q"   := (lolli p q) (at level 75) : stsep_scope.

Lemma antiframe p q i m h : 
        valid (i \+ h) -> (p --o q) (i \+ h) (m \+ h) -> (p --o q) i m.
Proof.
move=>D1 H i2 m2 E D2 H1; rewrite {i}E in H D1 D2 *.
move: (H i2 (m2 \+ h)); rewrite joinA; case/(_ (erefl _) D1 H1)=>h2 [E][D3].
rewrite joinA in E; exists h2; rewrite (joinKf D3 E).
by rewrite E in D3; rewrite (validL D3).
Qed.

(* p --o q is local *)
Lemma locality p q i1 m h : 
        valid (i1 \+ h) -> (p # top) i1 -> (p --o q) (i1 \+ h) m -> 
          exists m1, m = m1 \+ h /\ valid m /\ (p --o q) i1 m1.
Proof.
move=>D [h1][h2][E][H1] _ H2; rewrite {i1}E in D H2 *.
move: (H2 h1 (h2 \+ h)); rewrite joinA; case/(_ (erefl _) D H1)=>m1 [E][D2].
rewrite {m}E joinA in H2 D2 *; exists (m1 \+ h2); do !split=>//.
by apply: antiframe D H2.
Qed.

Lemma fr_pre p i j : (p # top) i -> (p # top) (i \+ j).
Proof. by case=>i1 [i2][->][H] _; rewrite -joinA; exists i1, (i2 \+ j). Qed.

(********************)
(* Separation monad *)
(********************)

Definition fr A (s : spec A) : spec A := 
  (s.1 # top, fun x => s.1 --o s.2 x).

Prenex Implicits fr.

Notation "[ s ]" := (fr s).

Definition STbin A (s : spec A) := STspec [s]. 

(* hide the spec *)
Structure ST A := with_spec (s : spec A) of STbin s.

Definition spec_of A (e : ST A) := let: with_spec s _ := e in s.
Definition pre_of A := [fun e : ST A => (spec_of e).1]. 
Definition post_of A := [fun e : ST A => (spec_of e).2]. 
Definition code_of A (e : ST A) := 
  let: with_spec _ c := e return STbin (spec_of e) in c.

Implicit Arguments pre_of [A].
Implicit Arguments post_of [A].
Implicit Arguments with_spec [A].
Prenex Implicits pre_of post_of.

Coercion with_spec : STbin >-> ST.

Section SepReturn.
Variable (A : Type) (x : A).
 
Definition ret_s : spec A := (emp, fun y i m => m = i /\ y = Val x). 

Lemma retP : Model.conseq (Model.ret_s x) [ret_s].
Proof.
move=>i /= H1 D1; split=>// y m [->] -> _ i1 i2 -> D ->.
by exists Unit; rewrite unitL (validR D).
Qed.

Definition ret := with_spec _ (Model.Do (Model.ret x) retP).

End SepReturn.


Section SepBind. 
Variables (A B : Type) (e1 : ST A) (e2 : A -> ST B). 
Notation s1 := (spec_of e1). 
Notation s2 := (fun x => spec_of (e2 x)). 

Definition bind_s : spec B := 
  (Model.bind_pre [s1] (fr \o s2), Model.bind_post [s1] (fr \o s2)).

Lemma bindP : Model.conseq (Model.bind_s [s1] (fr \o s2)) [bind_s].
Proof.
move=>i H D; split=>[|{H D}].
- case: H D=>i1 [i2][->][[H S]] _ D.
  split=>[|y m]; first by apply: fr_pre.
  by case/(locality D H)=>m1 [->][_]; move/S; apply: fr_pre.
move=>y m H _ i1 i2 E D1 [H1 S1]; rewrite {i}E in H D1 *.
case: H=>[[x][h][]|[e][->]]; case/(locality D1 H1)=>h1 [->][D2] T2.
- move/S1: (T2)=>H2; case/(locality D2 H2)=>m1 [->][D3] T3.
  by exists m1; do !split=>//; left; exists x; exists h1.
by exists h1; do !split=>//; right; exists e.
Qed.
  
Definition bind := 
  with_spec _ (Model.Do (Model.bind (code_of e1) (fun x => code_of (e2 x))) bindP).

End SepBind.


Definition verify'' A (s : spec A) i (r : ans A -> heap -> Prop) :=
  valid i -> s.1 i /\ forall y m, s.2 y i m -> valid m -> r y m.

Definition verify' A (e : ST A) i r := verify'' [spec_of e] i r. 

Notation verify i e r := (@verify' _ e i r).

Section SepFrame.
Variables (A : Type) (e : ST A). 

Lemma frame i j (r : ans A -> heap -> Prop) : 
        verify i e (fun y m => valid (m \+ j) -> r y (m \+ j)) ->
        verify (i \+ j) e r.
Proof.
move=>H D; case: (H (validL D))=>H1 H2.
split=>[|y m]; first by apply: fr_pre.
case/(locality D H1)=>m1 [->][D1]; move/H2.
by apply; apply: validL D1.
Qed.

Lemma frame0 i r : verify'' (spec_of e) i r -> verify i e r.
Proof.
move=>H D; case: (H D)=>H1 H2.
split=>[|y m]; first by exists i, Unit; rewrite unitR. 
move/(_ i Unit); rewrite unitR; case/(_ (erefl _) D H1)=>m1.
by rewrite unitR=>[[<-]][_]; apply: H2.
Qed.

Lemma frame1 i (r : ans A -> heap -> Prop) :
        verify'' (spec_of e) Unit (fun y m => valid (m \+ i) -> r y (m \+ i)) -> 
        verify i e r.
Proof. by move=>H; rewrite -[i]unitL; apply: frame; apply: frame0. Qed.

End SepFrame.

Definition conseq A (e : ST A) (s : spec A) := 
  forall i, s.1 i -> verify i e (fun y m => s.2 y i m).

(*
Local Notation conseq1 e s := 
  (conseq e (let 'pair x _ := s in x) 
            (let 'pair _ x := s in x)).
*)

Lemma conseq_refl A (e : ST A) : conseq e (spec_of e). 
Proof. by case: e=>s e i H; apply: frame0. Qed.

Hint Resolve conseq_refl. 

Section SepConseq.
Variables (A : Type) (s2 : spec A) (e : ST A) (pf : conseq e s2).

Lemma doP : Model.conseq [spec_of e] [s2].
Proof.
move=>i H D; split=>[|y m {H D} /=].
- case: H D=>i1 [i2][->][H] _ D.
  by case: (@pf i1 H (validL D))=>H1 _; apply: fr_pre. 
move=>S D i1 i2 E D2 H2; rewrite {i}E in D S D2 H2.
case: (@pf i1 H2 (validL D2))=>H1 T1.
case: (locality D2 H1 S)=>m1 [->][D3] {S}.
by move/T1; move/(_ (validL D3))=>T2; exists m1.
Qed.

Definition do' : STbin s2 := Model.Do (code_of e) doP.

End SepConseq.

Notation "'Do' e" := (@do' _ _ e _) (at level 80).

Section SepRead.
Variables (A : Type) (x : ptr). 

Definition read_s : spec A := 
  (fun i => exists v : A, i = x :-> v,
   fun y i m => i = m /\ forall v, i = x :-> v -> y = Val v).

Lemma readP : Model.conseq (Model.read_s A x) [read_s].
Proof.
move=>i H D; split=>[|{H D} y _ [->] H _ i1 h E1 D E2].
- case: H D=>i1 [i2][->][[v]] -> _ D /=. 
  rewrite hdomPtUn inE /= D eq_refl; split=>//.
  by exists v; rewrite hfindPtUn.
move: E1 E2 H D=>-> [v ->] H D; exists (x :-> v); do 3!split=>//.
move=>w /(hcancelPtV (validL D)) <-; apply: H.
by rewrite hfindPtUn.
Qed.

Definition read := with_spec _ (Model.Do (Model.read A x) readP).

End SepRead.


Section SepWrite. 
Variables (A : Type) (x : ptr) (v : A).
 
Definition write_s : spec unit := 
  (fun i => exists B : Type, exists y : B, i = x :-> y,
   fun y i m => y = Val tt /\ m = x :-> v).

Lemma writeP : Model.conseq (Model.write_s x v) [write_s].
Proof.
move=>i H D; split=>[|{H D} y m [->] <- D1 i1 h E1 D2 [B][w] E2].
- case: H D=>i1 [i2][->][[B]][y] -> _ D /=.
  by rewrite hdomPtUn inE /= D eq_refl.
move: E1 E2 D1 D2=>->->-> D; exists (x :-> v).
by rewrite updUnL hdomPt inE /= eq_refl (hvalidPt_cond D) /= updU eq_refl.
Qed.

Definition write := with_spec _ (Model.Do (Model.write x v) writeP).

End SepWrite. 


Section SepAlloc.
Variables (A : Type) (v : A).
  
Definition alloc_s : spec ptr :=  
  (emp, fun y i m => exists x, y = Val x /\ m = x :-> v).

Lemma allocP : Model.conseq (Model.alloc_s v) [alloc_s].
Proof.
move=>i H D; split=>[|{H D} y m [x][H1][->][H2] <- D1 i1 h E1 D E2].
- by case: H D=>i1 [i2][->][->].
move: E1 E2 H2 D D1=>-> ->; rewrite {1 2}unitL=>H2 D D1.
exists (x :-> v); rewrite updUnR (negbTE H2) hvalidPtUn H1 H2 D.
by do !split=>//; exists x.
Qed.

Definition alloc := with_spec _ (Model.Do (Model.alloc v) allocP).

End SepAlloc.


Section SepBlockAlloc.  
Variables (A : Type) (v : A) (n : nat). 

Definition allocb_s : spec ptr := 
  (emp, fun y i m => exists x:ptr, y = Val x /\ m = updi x (nseq n v)).

Lemma allocbP : Model.conseq (Model.allocb_s v n) [allocb_s].
Proof.
move=>i H D; split=>[|y m].
- by case: H D=>i1 [i2][->][->][]; rewrite joinC.
case=>x [->] -> D1 i1 h E1 D2 E2.
move: E1 E2 D1 D2=>->->; rewrite unitL {2}joinC=>D1 D2.
by exists (updi x (nseq n v)); do !split=>//; exists x.
Qed.

Definition allocb := with_spec _ (Model.Do (Model.allocb v n) allocbP).

End SepBlockAlloc.


Section SepDealloc.
Variable x : ptr.

Definition dealloc_s : spec unit := 
  (fun i => exists A : Type, exists v:A, i = x :-> v,
   fun y i m => y = Val tt /\ m = Unit).

Lemma deallocP : Model.conseq (Model.dealloc_s x) [dealloc_s].
Proof.
move=>i H D; split=>[|{H D} y m [->] <- D1 i1 h E1 D2 [A][v] E2].
- case: H D=>i1 [i2][->][[A]][v] -> _ D /=.
  by rewrite hdomPtUn inE /= D eq_refl.
move: E1 E2 D1 D2=>->->->; rewrite hvalidPtUn; case/and3P=>H1 _ H2.
by exists Unit; rewrite freeUnR // freeU eq_refl /cond /= H1 free0.
Qed.

Definition dealloc := with_spec _ (Model.Do (Model.dealloc x) deallocP).

End SepDealloc.


Section SepThrow.
Variables (A : Type) (e : exn).
 
Definition throw_s : spec A := 
  (emp, fun y i m => m = i /\ y = Exn e). 

Lemma throwP : Model.conseq (Model.throw_s A e) [throw_s].
Proof.
move=>i H D; split=>{H D} // y m [->] -> _ i1 h -> D ->.
by exists Unit; rewrite unitL; do !split=>//; apply: validR D.
Qed.

Definition throw := with_spec _ (Model.Do (Model.throw A e) throwP).

End SepThrow.


Section SepTry.
Variables (A B : Type) (e : ST A) (e1 : A -> ST B) (e2 : exn -> ST B). 
Notation s := (spec_of e).
Notation s1 := (fun x => spec_of (e1 x)).
Notation s2 := (fun x => spec_of (e2 x)).

Definition try_s : spec B := 
  (Model.try_pre [s] (fr \o s1) (fr \o s2),
   Model.try_post [s] (fr \o s1) (fr \o s2)).

Lemma tryP : Model.conseq (Model.try_s [s] (fr \o s1) (fr \o s2)) [try_s].
Proof.
move=>i H D; split=>[|{H D} y m H1 D1 i1 h E1 D2 /= [H2][H3] H4].
- case: H D=>i1 [i2][->][[H [S1 S2]]] _ D.
  split; first by apply: fr_pre.
  split=>y m; case/(locality D H)=>m1 [->][_]; [move/S1 | move/S2];
  by apply: fr_pre.
rewrite {i}E1 /= in H1 D2.
case: H1=>[[x]|[x]][h1][];
case/(locality D2 H2)=>m1 [->][D3] T1; move: (T1); 
[move/H3 | move/H4]=>T'; case/(locality D3 T')=>m2 [->][D4] T2; 
exists m2; do 2!split=>//; [left | right]; 
by exists x, m1.
Qed.

Definition ttry := 
  with_spec _ (Model.Do (Model.try (code_of e) 
                                   (fun x => code_of (e1 x)) 
                                   (fun x => code_of (e2 x))) tryP).

End SepTry.

Section SepFix.
Variables (A : Type) (B : A -> Type) (s : forall x, spec (B x)).
Notation tp := (forall x, STbin (s x)).

Definition Fix (f : tp -> tp) : tp := Model.ffix f.

End SepFix.

(****************************************************)
(* Notation to move from binary posts to unary ones *)
(****************************************************)

Definition logvar {B A} (s : A -> spec B) : spec B := 
  (fun i => exists x : A, let 'pair p _ := s x in p i, 
   fun y i m => forall x : A, let 'pair _ q := s x in q y i m).

Definition binarify {A} (p : pre) (q : ans A -> pre) : spec A := 
  (p, fun y i m => p i -> q y m).

Notation "'STsep' ( p , q ) " := (STbin (binarify p q)) (at level 0).  

Notation "{ x .. y }, 'STsep' ( p , q ) " :=
  (STbin (logvar (fun x => .. (logvar (fun y => binarify p q)) .. )))
   (at level 0, x binder, y binder, right associativity).


Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2)) 
  (at level 78, right associativity) : stsep_scope.
Notation "c1 ';;' c2" := (bind c1 (fun _ => c2)) 
  (at level 78, right associativity) : stsep_scope.
Notation "'!' x" := (read _ x) (at level 50) : stsep_scope.
Notation "e1 '::=' e2" := (write e1 e2) (at level 60) : stsep_scope.





