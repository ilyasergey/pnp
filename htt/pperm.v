From mathcomp.ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp
Require Import path.
Require Import pred.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(****************************************************)
(* A theory of permutations over non-equality types *)
(****************************************************)

Section Permutations.
Variable A : Type.

Lemma in_split (x : A) (s : seq A) :
        x \In s -> exists s1, exists s2, s = s1 ++ x :: s2.
Proof.
elim:s=>[|y s IH] //=; rewrite InE.
case=>[<-|]; first by exists [::]; exists s.
by case/IH=>s1 [s2] ->; exists (y :: s1); exists s2.
Qed.

Inductive perm (s1 s2 : seq A) : Prop :=
| permutation_nil of s1 = [::] & s2 = [::]
| permutation_skip x t1 t2 of s1 = x :: t1 & s2 = x :: t2 & perm t1 t2
| permutation_swap x y t of s1 = x :: y :: t & s2 = y :: x :: t
| permutation_trans t of perm s1 t & perm t s2.

Lemma perm_nil (s : seq A) : perm [::] s <-> s = [::].
Proof.
split=>[H|]; last by move=>->; apply: permutation_nil.
move: {1 2}[::] s H (erefl (Nil A)).
apply: perm_ind=>[|s1 s2 x t1 t2 ->|s1 s2 x y t ->|s1 s2 t _ IH1 _ IH2] //.
by move/IH1; move/IH2.
Qed.

Lemma perm_refl (s : seq A) : perm s s.
Proof.
elim:s=>[|e s IH]; first by apply: permutation_nil.
by apply: (permutation_skip (x:=e)) IH.
Qed.

Hint Resolve perm_refl.

Lemma perm_sym s1 s2 : perm s1 s2 <-> perm s2 s1.
Proof.
suff L: forall s1 s2, perm s1 s2 -> perm s2 s1 by split; apply: L.
apply: perm_ind=>s1' s2'.
- by move=>->->; apply: permutation_nil.
- by move=>x t1 t2 -> -> H1; apply: permutation_skip.
- by move=>x y t -> ->; apply: permutation_swap.
by move=>t _ H1 _ H2; apply: permutation_trans H2 H1.
Qed.

Lemma perm_trans s2 s1 s3 : perm s1 s2 -> perm s2 s3 -> perm s1 s3.
Proof. by apply: permutation_trans. Qed.

Lemma perm_in s1 s2 x : perm s1 s2 -> x \In s1 -> x \In s2.
Proof.
move: s1 s2; apply: perm_ind=>s1 s2.
- by move=>->->.
- move=>y t1 t2 -> -> H; rewrite !InE; tauto.
- by move=>y z t -> ->; rewrite !InE; tauto.
by move=>t _ IH1 _ IH2; move/IH1; move/IH2.
Qed.

Lemma perm_cat2lL s s1 s2 : perm s1 s2 -> perm (s ++ s1) (s ++ s2).
Proof. by elim:s=>[|e s IH] //=; move/IH; apply: permutation_skip. Qed.

Lemma perm_cat2rL s s1 s2 : perm s1 s2 -> perm (s1 ++ s) (s2 ++ s).
Proof.
move=>H; move: s1 s2 H s; apply: perm_ind=>s1 s2.
- by move=>->->.
- by move=>x t1 t2 -> -> H IH s /=; apply: permutation_skip.
- by move=>x y t -> -> s /=; apply: permutation_swap.
by move=>t H1 IH1 H2 IH2 s; apply: permutation_trans (IH2 s).
Qed.

Lemma perm_catL s1 t1 s2 t2 :
        perm s1 s2 -> perm t1 t2 -> perm (s1 ++ t1) (s2 ++ t2).
Proof.
move=>H; move: s1 s2 H t1 t2; apply: perm_ind=>s1 s2.
- by move=>->->.
- move=>x t1 t2 -> -> H IH r1 r2.
  by move/IH; apply: permutation_skip.
- move=>x y t -> -> t1 t2 H.
  by apply: (permutation_trans (t:=[:: x, y & t] ++ t2));
     [apply: perm_cat2lL | simpl; apply: permutation_swap].
move=>t H1 IH1 H2 IH2 t1 t2 H.
by apply: permutation_trans (IH2 _ _ H); apply: IH1.
Qed.

Lemma perm_cat_consL s1 t1 s2 t2 x :
        perm s1 s2 -> perm t1 t2 -> perm (s1 ++ x :: t1) (s2 ++ x :: t2).
Proof.
by move=>H1 H2; apply: perm_catL H1 _; apply: permutation_skip H2.
Qed.

Lemma perm_catC s1 s2 : perm (s1 ++ s2) (s2 ++ s1).
Proof.
elim:s1 s2=>[|x s1 IH1] s2 /=; first by rewrite cats0.
apply: (@perm_trans (x::s2++s1)); first by apply: permutation_skip (IH1 s2).
elim: s2=>[|y s2 IH2] //=.
apply: (@perm_trans (y::x::s2++s1)); first by apply: permutation_swap.
by apply: permutation_skip IH2.
Qed.

Hint Resolve perm_catC.

Lemma perm_cons_catCA s1 s2 x : perm (x :: s1 ++ s2) (s1 ++ x :: s2).
Proof.
rewrite -cat_rcons -cats1 -cat_cons -cat1s.
by apply: perm_cat2rL; apply: perm_catC.
Qed.

Lemma perm_cons_catAC s1 s2 x : perm (s1 ++ x :: s2) (x :: s1 ++ s2).
Proof. by apply/perm_sym; apply: perm_cons_catCA. Qed.

Hint Resolve perm_cons_catCA perm_cons_catAC.

Lemma perm_cons_cat_consL s1 s2 s x :
        perm s (s1 ++ s2) -> perm (x :: s) (s1 ++ x :: s2).
Proof.
case: s1=>[|a s1] /= H; first by apply: permutation_skip.
apply: (@perm_trans (x::a::s1++s2)); first by apply: permutation_skip.
apply: (@perm_trans (a::x::s1++s2)); first by apply: permutation_swap.
by apply: permutation_skip=>//; apply: perm_catCA.
Qed.

(* a somewhat generalized induction principle *)
Lemma perm_ind2 (P : seq A -> seq A -> Prop) :
        P [::] [::] ->
        (forall x s1 s2, perm s1 s2 -> P s1 s2 ->
           P (x :: s1) (x :: s2)) ->
        (forall x y s1 s2, perm s1 s2 -> P s1 s2 ->
           P (y :: x :: s1) (x :: y :: s2)) ->
        (forall s2 s1 s3, perm s1 s2 -> P s1 s2 ->
           perm s2 s3 -> P s2 s3 -> P s1 s3) ->
        forall s1 s2, perm s1 s2 -> P s1 s2.
Proof.
move=>H1 H2 H3 H4; apply: perm_ind=>s1 s2; last 1 first.
- by move=>t; apply: H4.
- by move=>->->.
- by move=>x t1 t2 -> ->; apply: H2.
move=>x y t -> ->.
have R : forall t, P t t by elim=>[|e t1 IH] //; apply:  H2.
apply: (H4 (y :: x :: t))=>//; last by apply: H3.
by apply: permutation_swap.
Qed.

Lemma perm_size l1 l2: perm l1 l2 -> size l1 = size l2.
Proof.
move: l1 l2; apply: perm_ind=>s1 s2=>[|x t1 t2|x y t|t]; first by move=>->->.
- by move=>->->{s1 s2} _ /=->.
- by move=>->->{s1 s2}/=.
- by move=>_->_->.
Qed.

(* Now the hard part; the opposite implications *)
Lemma perm_cat_consR s1 t1 s2 t2 x :
        perm (s1 ++ x :: t1) (s2 ++ x :: t2) -> perm (s1 ++ t1) (s2 ++ t2).
Proof.
move: s1 t1 s2 t2 x.
suff H:
  forall r1 r2, perm r1 r2 -> forall x s1 t1 s2 t2,
    r1 = s1 ++ x :: t1 -> r2 = s2 ++ x :: t2 -> perm (s1 ++ t1) (s2 ++ t2).
- by move=>s1 t1 s2 t2 x; move/H; apply.
apply: perm_ind2; last 1 first.
- move=>s2 s1 s3 H1 IH1 H2 IH2 x r1 t1 r2 t2 E1 E2.
  case: (@in_split x s2).
  - apply: perm_in H1 _; rewrite E1; apply: (@perm_in (x::r1++t1))=>//.
  by rewrite InE; left.
  move=>s4 [s5] E; apply: (@perm_trans (s4++s5)); first by apply: IH1 E1 E.
  by apply: IH2 E E2.
- by move=>x [].
- move=>x t1 t2 H IH y s1 s2 p1 p2 E1 E2.
  case: s1 E1=>[|b s1] /=; case: p1 E2=>[|c p1] /= E1 E2.
  - by case: E1 E2=><- <- [<-].
  - apply: (@perm_trans (p1 ++ c :: p2))=>//.
    by case: E1 H=><- ->; case: E2=><- ->.
  - case: E1 E2 H=><- <- [<-] ->; apply: (@perm_trans (s1 ++ x:: s2)).
    by apply: perm_cons_cat_consL.
  case: E1 E2 H IH=><- -> [<-] -> H IH.
  by apply: permutation_skip=>//; apply: IH.
move=>x y p1 p2 H IH z s1 t1 s2 t2 E1 E2.
case: s1 E1 H IH=>[|b s1]; case: s2 E2=>[|c s2]=>/=.
- by case=><- <- [<-] <- H IH; apply: permutation_skip.
- case=><-; case: s2=>[|b s2] /=.
  - by case=><- <-; case=><- H IH; apply: permutation_skip H.
  case=><- -> [<-] <- H IH.
  by apply: permutation_skip=>//; apply: perm_trans H _.
- case=><- <- [<-]; case: s1=>[|a s1] /=.
  - by case=><- H IH; apply: permutation_skip.
  by case=><- -> H IH; apply: permutation_skip=>//; apply: perm_trans H.
case=><-; case: s2=>[|a s2] /=; case: s1=>[|d s1] /=.
- by case=><- <- [<-] <- <- H IH; apply: permutation_skip.
- case=><- <- [<-] <- -> H IH.
  apply: (@perm_trans (x::y::s1 ++ t1)); first by apply: permutation_swap.
  by apply: permutation_skip=>//; apply: perm_trans H.
- case=><- -> [<-] <- <- H IH.
  apply: (@perm_trans (y::x::s2++t2)); last by apply: permutation_swap.
  by apply: permutation_skip=>//; apply: perm_trans H _.
case=><- -> [<-] <- -> H IH.
apply: (@perm_trans (x::y::s1++t1)); first by apply: permutation_swap.
by apply: permutation_skip=>//; apply: permutation_skip=>//; apply: IH.
Qed.

Lemma perm_cons x s1 s2 : perm (x :: s1) (x :: s2) <-> perm s1 s2.
Proof.
split; last by apply: permutation_skip.
by move/(@perm_cat_consR [::] s1 [::] s2 x).
Qed.

Lemma perm_cons_cat_cons x s1 s2 s :
        perm (x :: s) (s1 ++ x :: s2) <-> perm s (s1 ++ s2).
Proof.
split=>[|H]; first by by move/(@perm_cat_consR [::] s s1 s2 x).
by apply: (@perm_trans (x :: s1++s2))=>//; apply: permutation_skip.
Qed.

Lemma perm_cat_cons x s1 s2 t1 t2 :
        perm (s1 ++ x :: t1) (s2 ++ x :: t2) <-> perm (s1 ++ t1) (s2 ++ t2).
Proof.
split=>[|H]; first by apply: perm_cat_consR.
apply: (@perm_trans (x::s1++t1))=>//; apply: (@perm_trans (x::s2++t2))=>//.
by apply/perm_cons.
Qed.

Lemma perm_cat2l s1 s2 s3: perm (s1 ++ s2) (s1 ++ s3) <-> perm s2 s3.
Proof.
split; last by apply: perm_cat2lL.
elim: s1 s2 s3=>[|x s1 IH] s2 s3 //= H.
by apply: IH; move/perm_cons: H.
Qed.

Lemma perm_cat2r s1 s2 s3 : perm (s2 ++ s1) (s3 ++ s1) <-> perm s2 s3.
Proof.
split; last by apply: perm_cat2rL.
elim: s1 s2 s3=>[|x s1 IH] s2 s3 /=; first by rewrite !cats0.
by move=>H; apply: IH; apply: perm_cat_consR H.
Qed.

Lemma perm_catAC s1 s2 s3 : perm ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Proof. by move=>*; rewrite -!catA perm_cat2l. Qed.

Lemma perm_catCA s1 s2 s3 : perm (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof. by move=>*; rewrite !catA perm_cat2r. Qed.

End Permutations.

Hint Resolve perm_refl perm_catC perm_cons_catCA
             perm_cons_catAC perm_catAC perm_catCA.


(* perm and map *)

Lemma perm_map A B (f : A -> B) (s1 s2 : seq A) :
        perm s1 s2 -> perm (map f s1) (map f s2).
Proof.
set P := fun s1 s2 => perm (map f s1) (map f s2).
suff {s1 s2} L: forall s1 s2, perm s1 s2 -> P s1 s2 by apply: L.
apply: perm_ind2=>//; last 1 first.
- move=>s2 s1 s3 _ IH1 _ IH2.
  by apply: perm_trans IH1 IH2.
- by move=>x s1 s2 H IH; rewrite /P perm_cons.
move=>x1 x2 s1 s2 H IH.
have L: perm [:: f x2, f x1 & map f s1] ([:: f x1] ++ [:: f x2 & map f s1]).
- by apply/perm_cons_cat_cons.
by apply: perm_trans L _; rewrite !perm_cons.
Qed.

(* mapping to ssreflect decidable perm *)

Lemma perm_eq_perm (A : eqType) (s1 s2 : seq A) :
        reflect (perm s1 s2) (perm_eq s1 s2).
Proof.
apply: (iffP idP); last first.
- elim: s1 s2 /; last 1 first.
  - by move=>s1 s2 t _ H2 _; apply: perm_eq_trans H2.
  - by move=>s1 s2 ->->.
  - by move=>s1 s2 x t1 t2 ->-> H1 H2; rewrite seq.perm_cons.
  move=>s1 s2 x y t ->->.
  by rewrite -(perm_rot 1) /rot /= seq.perm_cons seq.perm_catC.
elim: s1 s2=>[|x s1 IH] /= s2.
- move/perm_eq_mem=>H; apply/perm_nil.
  by case: s2 H=>// a s2 /(_ a); rewrite inE eq_refl.
move=>H; move: (perm_eq_mem H x); rewrite inE eq_refl; move/esym=>/= H'.
move/(perm_eq_trans H): {H} (perm_to_rem H'); rewrite seq.perm_cons.
move/IH/(perm_cons x)=>H; apply: perm_trans H _.
elim: s2 x H'=>[|y s2 IH2] //= x.
rewrite inE; case/orP; first by move/eqP=><-; rewrite eq_refl.
case: eqP=>[->//|_ H]; move/(perm_cons y): (IH2 _ H).
by apply: perm_trans; apply: permutation_swap.
Qed.

