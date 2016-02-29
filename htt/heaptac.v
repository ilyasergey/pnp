From mathcomp.ssreflect
Require Import ssrbool ssreflect ssrfun ssrnat div seq path eqtype.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(**************************************************************************)
(* Several tactics for canceling common terms in disjoint unions          *)
(* Currently, they don't deal with weak pointers. I.e.  they only if they *)
(* see iterms like x :-> v1 and x :-> v2, they will reduce to v1 = v2     *)
(* only if v1, v2 are of the same type A more general tactic would emit   *)
(* obligation dyn v1 = dyn v2, but I don't bother with this now.          *)
(**************************************************************************)

(* These are really brittle, but I didn't get around yet to substitute them *)
(* all with Mtacs or overloaded lemmas. So for now, let's stick with the hack *)
(* in order to support the legacy proofs *)

(* First cancelation in hypotheses *)

Section Cancellation.
Implicit Type (h : heap).

Lemma injUh A h1 h2 x (v1 v2 : A) : 
        valid (h1 \+ (x :-> v1)) -> 
        h1 \+ (x :-> v1) = h2 \+ (x :-> v2) -> 
          valid h1 /\ h1 = h2 /\ v1 = v2. 
Proof. by rewrite -!(joinC (x :-> _))=>D /(hcancelV D) [->]. Qed.  

Lemma eqUh h1 h2 h : 
        valid (h1 \+ h) -> h1 \+ h = h2 \+ h -> valid h1 /\ h1 = h2. 
Proof. by move=>D E; rewrite {2}(joinKf D E) (validL D). Qed.

Lemma exit1 h1 h2 h : valid (h1 \+ h) -> h1 \+ h = h \+ h2 -> valid h1 /\ h1 = h2.
Proof. by move=>D; rewrite (joinC h); apply: eqUh. Qed.

Lemma exit2 h1 h : valid (h1 \+ h) -> h1 \+ h = h -> valid h1 /\ h1 = Unit.
Proof. by move=>H1; rewrite -{2}(unitR h)=>H2; apply: exit1 H2. Qed.

Lemma exit3 h1 h : valid h -> h = h \+ h1 -> valid (Unit : heap) /\ Unit = h1.
Proof.
move=>H1 H2; split=>//; rewrite -{1}(unitR h) in H2.
by move/joinfK: H2; rewrite unitR; apply.
Qed.

Lemma exit4 h : valid h -> h = h -> valid (Unit : heap) /\ Unit = Unit :> heap. 
Proof. by []. Qed. 

Lemma cexit1 h1 h2 h : h1 = h2 -> h1 \+ h = h \+ h2.
Proof. by move=>->; rewrite joinC. Qed.

Lemma cexit2 h1 h : h1 = Unit -> h1 \+ h = h.
Proof. by move=>->; rewrite unitL. Qed.

Lemma cexit3 h1 h : Unit = h1 -> h = h \+ h1.
Proof. by move=><-; rewrite unitR. Qed.

Lemma congUh A h1 h2 x (v1 v2 : A) : 
        h1 = h2 -> v1 = v2 -> h1 \+ (x :-> v1) = h2 \+ (x :-> v2).
Proof. by move=>-> ->. Qed.

Lemma congeqUh h1 h2 h : h1 = h2 -> h1 \+ h = h2 \+ h.
Proof. by move=>->. Qed. 

End Cancellation.


Ltac cancelator t H :=
  match goal with 
  (* we exit when we hit the terminator on the left *)
  | |- ?h1 \+ t = ?h2 -> _ => 
     let j := fresh "j" in
     set j := {1}(h1 \+ t); 
     rewrite -1?joinA /j {j};
     (move/(exit1 H)=>{H} [H] || move/(exit2 H)=>{H} [H]) 
  | |- t = ?h2 -> _ => 
     rewrite -?joinA;
     (move/(exit3 H)=>{H} [H] || move/(exit4 H)=>{H} [H])
  | |- (?h1 \+ (?x :-> ?v) = ?h2) -> _ => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(joinC (x :-> _)) -?(joinAC _ _ (x :-> _)) /j {j}; 
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    (move/(injUh H)=>{H} [H []] ||
    (* if not, rotate x in the first union *)
     rewrite (joinC h1) ?joinA in H * );
    (* and proceed *)
    cancelator t H
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- (?h1 \+ ?h = ?h2) -> _ => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(joinC h) -?(joinAC _ _ h) /j {j}; 
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (move/(eqUh H)=>{H} [H []] ||
    (* if not, rotate h in the first union *)
    rewrite (joinC h1) ?joinA in H * );
    (* and proceed *)
    cancelator t H
  | |- _ => idtac 
  end.


Ltac heap_cancel := 
  match goal with 
  | |- ?h1 = ?h2 -> ?GG =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in 
    let t := fresh "t" in
    let H := fresh "H" in
    let G := fresh "hidden_goal"
    in
      (* generate the obligation to prove that the left heap is defined *)
      suff : valid h1; first (
       (* make sure no sharing of expressions in the goal *)
       set t1 := {1 2}h1; set t2 := {1}h2; set G := GG;
       (* introduce terminators *)
       rewrite -(unitL t1) -(unitL t2) [Unit]lock;
       set t := locked Unit; rewrite /t1 /t2 {t1 t2}; 
       move=>H; 
       (* flatten the goal *)
       rewrite ?joinA in H *; 
       (* call the cancelation routine *)
       cancelator t H; 
       (* remove the terminator and push H onto the goal *)
       move: H {t}; rewrite /G {G})
  | |- _ => idtac
  end.


(* Then cancelation in conclusions *)

Ltac congruencer t :=
  match goal with 
  | |- ?h1 \+ t = ?h2 => 
     let j := fresh "j" in
     set j := {1}(h1 \+ t); 
     rewrite -1?joinA /j {j};
     (apply: cexit1 || apply: cexit2)
  | |- t = ?h2 => 
     rewrite -1?joinA;
     (apply: cexit3 || apply: refl_equal)
  | |- (?h1 \+ (?x :-> ?v) = ?h2) => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(joinC (x :-> _)) -?(joinAC _ _ (x :-> _)) /j {j}; 
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    ((apply: congUh; [congruencer t | idtac]) || 
    (* if not, rotate x in the first union *)
     (rewrite (joinC h1) ?joinA; congruencer t))
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- (?h1 \+ ?h = ?h2) => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(joinC h) -?(joinAC _ _ h) /j {j}; 
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (apply: congeqUh || 
    (* if not, rotate h in the first union *)
    rewrite (joinC h1) ?joinA);
    (* and proceed *)
    congruencer t
  | |- _ => idtac 
  end.

Ltac heap_congr := 
  match goal with 
  | |- ?h1 = ?h2 =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in 
    let t := fresh "t" in
      set t1 := {1}h1; set t2 := {1}h2; 
      (* introduce terminators *)
      rewrite -(unitL t1) -(unitL t2) [Unit]lock;
      set t := locked Unit; rewrite /t1 /t2 {t1 t2}; 
      (* flatten the goal *)
      rewrite ?joinA; 
      (* call the congruence routine and remove the terminator *)
      congruencer t=>{t}
  | |- _ => idtac
  end.

Lemma test h1 h2 h3 x (v1 v2 : nat) : 
        h3 = h2 -> v1 = v2 -> 
        h1 \+ (x :-> v1) \+ h3= h2 \+ h1 \+ (x :-> v2).
Proof. by move=>H1 H2; heap_congr. Qed.


(* and a tactic for computing the subdom relation *)

Section Defcheck.
Local Notation idyn v := (@idyn _ id _ v).

Implicit Type h : heap. 

Definition subdom h1 h2 := 
  if (h1, h2) is (Heap.Def hs1 _, Heap.Def hs2 _) then 
    all (fun x => x \in supp hs2) (supp hs1)
  else false.

Lemma subdom_def h1 h2 : subdom h1 h2 -> valid h1 && valid h2. 
Proof. by case: h1 h2=>[|h1 H1] // [|h2 H2]. Qed.

Lemma subdomR h1 h2 : 
        valid h1 -> valid h2 -> 
        reflect (forall x, x \in dom h1 -> x \in dom h2) 
                (subdom h1 h2).
Proof. by case: h1 h2=>[|h1 H1] // [|h2 H2] //= _ _; apply: allP. Qed. 

Lemma subdomP h1 h2 : 
        valid h1 -> ~~ empb h1 -> 
        reflect (forall x, x \in dom h1 -> x \in dom h2) 
                (subdom h1 h2). 
Proof.
case: h1 h2=>[|h1 H1] // [|h2 H2] //= _ H3; last by apply: allP.
apply: ReflectF.
suff H: head null (supp h1) \in supp h1 by move/(_ _ H).
rewrite /empb /= in H3.
by case: (supp h1) H1 H3=>[|x xs] //=; rewrite !inE eq_refl.
Qed.

Lemma subdomQ x h1 h2 : subdom h1 h2 -> x \in dom h1 -> x \in dom h2.
Proof.
move=>S H; case: subdomP S=>//. 
- by apply: dom_valid H.
- by case: empbP=>// E; rewrite E dom0 in H.
by move=>H2 _; apply: H2.
Qed.

Lemma subdom_refl h : valid h -> subdom h h.
Proof. by case: h=>[//|h H _]; apply/allP. Qed.

Lemma subdomD h1 h2 h : subdom h1 h2 -> valid (h2 \+ h) -> valid (h1 \+ h).
Proof.
case: h1 h2 h=>[|h1 H1]; case=>[|h2 H2]; case=>[|h H] //=.
rewrite /subdom /valid /PCM.join /= !umE /UM.valid /UM.union /=.
case: ifP=>E1 //; case: ifP=>E2 // E _.
case: disjP E2=>// x H3 H4 _; case: disjP E1=>// X1 _.
by case: (allP (s := supp h1)) E=>//; move/(_ _ H3); move/X1; rewrite H4.
Qed.
  
Lemma subdomE h1 h2 h : 
        valid (h2 \+ h) -> subdom h1 h2 -> subdom (h1 \+ h) (h2 \+ h).
Proof.
case: h1 h2 h=>[|h1 H1]; case=>[|h2 H2]; case=>[|h H] //=.
rewrite /subdom /valid /PCM.join /= !umE /UM.valid /UM.union /=.
case: ifP=>E1 // _; case: ifP=>E2 /=; 
case: (allP (s:=supp h1))=>// E _; last first.
- case: disjP E2=>// x H3 H4; move/E: H3.
  by case: disjP E1=>// X _; move/X; rewrite H4.
case: (allP (s:=supp (fcat h1 h)))=>//; case=>x.
rewrite !supp_fcat !inE /= inE/=.
by case/orP; [move/E=>->| move=>->; rewrite orbT].
Qed.

Lemma subdomUE h1 h2 h1' h2' : 
        valid (h2 \+ h2') -> subdom h1 h2 -> subdom h1' h2' ->
        subdom (h1 \+ h1') (h2 \+ h2').
Proof.
case: h1 h2 h1' h2'=>[|h1 H1]; case=>[|h2 H2]; 
case=>[|h1' H1']; case=>[|h2' H2'] //.
rewrite /subdom /valid /PCM.join /= !umE /UM.valid /UM.union /=.
case: ifP=>E1 // _; case: ifP=>E2 //= T1 T2; last first.
- case: disjP E2=>// x; case: allP T1=>// X _; move/X=>{X}. 
  case: disjP E1=>// X _; move/X=>{X}.
  by case: allP T2=>// X _ H3 H4; move/X: H4 H3=>->.
case: allP=>//; case=>x.
rewrite !supp_fcat !inE; case/orP=>E.
- by case: allP T1=>//; move/(_ _ E)=>->.
by case: allP T2=>//; move/(_ _ E)=>->; rewrite orbT.
Qed.

Lemma subdom_emp h : valid h -> subdom Unit h.
Proof. by case: h. Qed.

Lemma subdom_emp_inv h : subdom h Unit -> h = Unit.
Proof. 
case: h=>[|h H] //; rewrite /subdom /=.
case: (allP (s:=supp h))=>// E _; apply/Heap.heapE; apply: fmapP=>x.
by case: suppP (E x)=>// v E2; move/(_ (erefl _)); rewrite supp_nil.
Qed.

Lemma subdomPE A B x (v1 : A) (v2 : B) : 
        x != null -> subdom (x :-> v1) (x :-> v2).
Proof. 
move=>H.
rewrite /subdom /heap_pts /pts /= /Heap.pts /Heap.upd /=.
case: decP=>//= _.
rewrite (_ : FinMap _ = ins x (idyn v2) (finmap.nil _ _)) //.
by rewrite supp_ins inE /= eq_refl.
Qed.

Lemma subdom_trans h2 h1 h3 : subdom h1 h2 -> subdom h2 h3 -> subdom h1 h3.
Proof.
move=>H1 H2; move: (subdom_def H1) (subdom_def H2).
case/andP=>D1 _; case/andP=>_ D2. 
case E: (empb h1).
- by move/empbP: E => ->; rewrite subdom_emp.
apply/subdomP=>[//||x in1]; first by apply negbT.
by apply: (subdomQ H2) (subdomQ H1 in1).
Qed.

Hint Resolve subdom_emp subdomPE.


(* swap the arguments *)

Definition supdom h2 h1 := subdom h1 h2.

Lemma sexit1 h1 h2 h : 
        valid (h2 \+ h) -> 
          (valid h2 -> supdom h2 h1) -> supdom (h2 \+ h) (h \+ h1).
Proof.
move=>H1 H2; rewrite (joinC h); apply: subdomE=>//.
by apply: H2; apply: validL H1.
Qed.

Lemma sexit2 h1 h : 
        valid (h1 \+ h) -> (valid h1 -> supdom h1 Unit) -> 
        supdom (h1 \+ h) h.
Proof.
move=>H1 H2; rewrite -{2}(unitL h); apply: subdomE=>//.
by apply: H2; apply: validL H1.
Qed.

Lemma sexit3 h1 h : 
        valid h -> (valid (Unit : heap) -> supdom Unit h1) -> 
        supdom h (h \+ h1).
Proof.
move=>H1 H2; rewrite joinC -{1}(unitL h).
by apply: subdomE; [rewrite unitL | apply: H2].
Qed.

Lemma sexit4 h : valid h -> (valid (Unit : heap) -> 
                   Unit = Unit :> heap) -> supdom h h.
Proof. by move=>*; rewrite -(unitL h); apply: subdomE=>//; rewrite unitL. Qed.

Lemma supdomUh A B h1 h2 x (v1 : A) (v2 : B) : 
        valid (h2 \+ (x :-> v2)) -> 
          (valid h2 -> supdom h2 h1) -> 
            supdom (h2 \+ (x :-> v2)) (h1 \+ (x :-> v1)).
Proof.
move=>H1 H2.
apply: subdomUE=>//; first by apply: H2; apply: validL H1.
by apply: subdomPE; apply: (@hvalidPt_cond _ x v2 h2); rewrite joinC.
Qed.

Lemma supdomeqUh h1 h2 h : 
        valid (h2 \+ h) -> (valid h2 -> supdom h2 h1) -> supdom (h2 \+ h) (h1 \+ h).
Proof. by rewrite (joinC h1); apply: sexit1. Qed.    

Lemma sup_defdef h1 h2 : valid h2 -> supdom h2 h1 -> valid h1.
Proof. by move=>H1; rewrite /supdom; move/subdom_def; rewrite H1 andbT. Qed.

End Defcheck.

(* now the ltac *)

Ltac supdom_checker t H :=
  match goal with 
  | |- is_true (supdom (?h1 \+ t) ?h2) => 
     let j := fresh "j" in
     set j := {1}(h1 \+ t); 
     rewrite -1?joinA /j {j};
     (apply: (sexit1 H)=>{H} H || apply: (sexit2 H)=>{H} H)
  | |- is_true (supdom t ?h1) => 
     rewrite -1?joinA;
     (apply: (sexit3 H)=>{H} H || apply: (sexit4 H)=>{H} H)
  | |- is_true (supdom (?h1 \+ (?x :-> ?v)) ?h2) => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(joinC (x :-> _)) -?(joinAC _ _ (x :-> _)) /j {j}; 
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    (apply: (supdomUh _ H)=>{H} H || 
    (* if not, rotate x in the first union *)
     (rewrite (joinC h1) ?joinA in H * )); supdom_checker t H
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- is_true (supdom (?h1 \+ ?h) ?h2) => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(joinC h) -?(joinAC _ _ h) /j {j}; 
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (apply: (supdomeqUh H)=>{H} H || 
    (* if not, rotate h in the first union *)
    (rewrite (joinC h1) ?joinA in H * )); 
    (* and proceed *)
    supdom_checker t H
  | |- _ => idtac 
  end.


Ltac defcheck := 
  match goal with 
  | |- is_true (valid ?h2) -> is_true (valid ?h1) =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in 
    let t := fresh "t" in
    let H := fresh "H" in
      set t2 := {1}h2; set t1 := {1}h1; 
      (* introduce terminators *)
      rewrite -(unitL t1) -(unitL t2) [Unit]lock;
      set t := locked Unit; rewrite /t1 /t2 {t1 t2}; 
      (* flatten the goal *)
      rewrite ?joinA; 
      move=>H; 
      apply: (sup_defdef H); 
      (* call the subdom_cheker routine and remove the terminator *)
      supdom_checker t H; move: H {t}; rewrite /supdom
  | |- _ => idtac
  end.


Lemma test2 h1 h2 x (v1 v2 : nat) : subdom h1 h2 ->
        valid (h2 \+ (x :-> v2)) -> valid (h1 \+ (x :-> v1)).
Proof. by move=>H; defcheck. Qed.

