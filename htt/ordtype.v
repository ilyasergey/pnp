From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Module Ordered. 

Section RawMixin.

Structure mixin_of (T : eqType) := 
  Mixin {ordering : rel T; 
         _ : irreflexive ordering;
         _ : transitive ordering;
         _ : forall x y, [|| ordering x y, x == y | ordering y x]}.

End RawMixin.

(* the class takes a naked type T and returns all the *)
(* relatex mixins; the inherited ones and the added ones *)
Section ClassDef.

Record class_of (T : Type) := Class {
   base : Equality.class_of T; 
   mixin : mixin_of (Equality.Pack base T)}.

Local Coercion base : class_of >-> Equality.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.

(* produce an ordered type out of the inherited mixins *)
(* equalize m0 and m by means of a phantom; will be exploited *)
(* further down in the definition of OrdType *)
Definition pack b (m0 : mixin_of (EqType T b)) := 
  fun m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := Equality.Pack class cT.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Notation ordType := Ordered.type.
Notation OrdMixin := Mixin.
Notation OrdType T m := (@pack T _ m _ id).
Definition ord T : rel (sort T) := (ordering (mixin (class T))).
Notation "[ 'ordType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'ordType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ordType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ordType'  'of'  T ]") : form_scope.
End Exports.
End Ordered.
Export Ordered.Exports.

Definition oleq (T : ordType) (t1 t2 : T) := ord t1 t2 || (t1 == t2).

Prenex Implicits ord oleq.

Section Lemmas.
Variable T : ordType.

Lemma irr : irreflexive (@ord T). 
Proof. by case: T=>s [b [m]]. Qed.

Lemma trans : transitive (@ord T). 
Proof. by case: T=>s [b [m]]. Qed.

Lemma total (x y : T) : [|| ord x y, x == y | ord y x]. 
Proof. by case: T x y=>s [b [m]]. Qed. 

Lemma nsym (x y : T) : ord x y -> ord y x -> False.
Proof. by move=>E1 E2; move: (trans E1 E2); rewrite irr. Qed. 

Lemma otrans : transitive (@oleq T).
Proof.
move=>x y z /=; case/orP; last by move/eqP=>->.
rewrite /oleq; move=>T1; case/orP; first by move/(trans T1)=>->.
by move/eqP=><-; rewrite T1. 
Qed.

Lemma sorted_oleq s : sorted (@ord T) s -> sorted (@oleq T) s.
Proof. by elim: s=>[|x s IH] //=; apply: sub_path=>z y; rewrite /oleq=>->. Qed.

End Lemmas. 

Section Totality.
Variable K : ordType.  
 
CoInductive total_spec (x y : K) : bool -> bool -> bool -> Type :=
| total_spec_lt of ord x y : total_spec x y true false false
| total_spec_eq of x == y : total_spec x y false true false
| total_spec_gt of ord y x : total_spec x y false false true.

Lemma totalP x y : total_spec x y (ord x y) (x == y) (ord y x).
Proof.
case H1: (x == y).
- by rewrite (eqP H1) irr; apply: total_spec_eq.
case H2: (ord x y); case H3: (ord y x). 
- by case: (nsym H2 H3). 
- by apply: total_spec_lt H2.
- by apply: total_spec_gt H3.
by move: (total x y); rewrite H1 H2 H3.
Qed.
End Totality. 


(* Monotone (i.e. strictly increasing) functions for Ord Types *)
Section Mono.
Variables (A B :ordType).

Definition strictly_increasing f x y := @ord A x y -> @ord B (f x) (f y).

Structure mono : Type := Mono 
           {fun_of: A -> B; _: forall x y, strictly_increasing fun_of x y}.

End Mono.
Arguments strictly_increasing {A B} f x y.
Arguments Mono {A B _} _.

Section NatOrd.
Lemma irr_ltn_nat : irreflexive ltn. Proof. by move=>x; rewrite /= ltnn. Qed.
Lemma trans_ltn_nat : transitive ltn. Proof. by apply: ltn_trans. Qed.
Lemma total_ltn_nat : forall x y, [|| x < y, x == y | y < x]. 
Proof. by move=>*; case: ltngtP. Qed.

Definition nat_ordMixin := OrdMixin irr_ltn_nat trans_ltn_nat total_ltn_nat.
Canonical Structure nat_ordType := OrdType nat nat_ordMixin.
End NatOrd.

Section ProdOrd.
Variables K T : ordType.

(* lexicographic ordering *)
Definition lex : rel (K * T) := 
  fun x y => if x.1 == y.1 then ord x.2 y.2 else ord x.1 y.1.

Lemma irr_lex : irreflexive lex.
Proof. by move=>x; rewrite /lex eq_refl irr. Qed.

Lemma trans_lex : transitive lex.
Proof.
move=>[x1 x2][y1 y2][z1 z2]; rewrite /lex /=.
case: ifP=>H1; first by rewrite (eqP H1); case: eqP=>// _; apply: trans.
case: ifP=>H2; first by rewrite (eqP H2) in H1 *; rewrite H1.
case: ifP=>H3; last by apply: trans. 
by rewrite (eqP H3)=>R1; move/(nsym R1).
Qed.

Lemma total_lex : forall x y, [|| lex x y, x == y | lex y x].
Proof.
move=>[x1 x2][y1 y2]; rewrite /lex /=.
case: ifP=>H1.
- rewrite (eqP H1) eq_refl -pair_eqE /= eq_refl /=; exact: total.
rewrite (eq_sym y1) -pair_eqE /= H1 /=.
by move: (total x1 y1); rewrite H1.
Qed.

Definition prod_ordMixin := OrdMixin irr_lex trans_lex total_lex.
Canonical Structure prod_ordType := Eval hnf in OrdType (K * T) prod_ordMixin.
End ProdOrd.

Section FinTypeOrd.
Variable T : finType.

Definition ordf : rel T :=
  fun x y => index x (enum T) < index y (enum T). 

Lemma irr_ordf : irreflexive ordf.
Proof. by move=>x; rewrite /ordf ltnn. Qed.

Lemma trans_ordf : transitive ordf.
Proof. by move=>x y z; rewrite /ordf; apply: ltn_trans. Qed.

Lemma total_ordf : forall x y, [|| ordf x y, x == y | ordf y x].
Proof.
move=>x y; rewrite /ordf; case: ltngtP=>//= H; rewrite ?orbT ?orbF //.
have [H1 H2]: x \in enum T /\ y \in enum T by rewrite !mem_enum.
by rewrite -(nth_index x H1) -(nth_index x H2) H eq_refl.
Qed.

Definition fin_ordMixin := OrdMixin irr_ordf trans_ordf total_ordf.
End FinTypeOrd.

(* notation to let us write I_n instead of (ordinal_finType n) *)
Notation "[ 'fin_ordMixin' 'of' T ]" :=
  (fin_ordMixin _ : Ordered.mixin_of [eqType of T]) (at level 0).

Definition ordinal_ordMixin n := [fin_ordMixin of 'I_n].
Canonical Structure ordinal_ordType n := OrdType 'I_n (ordinal_ordMixin n).

Section SeqOrd.
Variable (T : ordType).

Fixpoint ords x  : pred (seq T) :=
  fun y => match x , y with
                 | [::] , [::] => false
                 | [::] ,  t :: ts => true
                 | x :: xs , y :: ys => if x == y then ords xs ys 
                                        else ord x y
                 | _ :: _ , [::] => false  
             end.

Lemma irr_ords : irreflexive ords.
Proof. by elim=>//= a l ->; rewrite irr; case:eqP=> //=. Qed.

Lemma trans_ords : transitive ords.
Proof.
elim=>[|y ys IHy][|x xs][|z zs]//=.
case:eqP=>//[->|H0];case:eqP=>//H; first by move/IHy; apply.
- by case:eqP=>//; rewrite -H; first (by move/H0).
case:eqP=>//[->|H1] H2; first by move/(nsym H2).
by move/(trans H2).
Qed.
 
Lemma total_ords : forall x y, [|| ords x y, x == y | ords y x].
Proof.
elim=>[|x xs IH][|y ys]//=; case:eqP=>//[->|H1]; 
 (case:eqP=>//= H; first (by rewrite orbT //=)). 
- by case:eqP=>//H3 ; case: (or3P (IH ys))=> [-> | /eqP H0 | ->];
 [ rewrite orTb // | apply: False_ind; apply: H; rewrite H0 | rewrite orbT //].
case:eqP; first by move/(esym)/H1. 
by move=>_ ;case: (or3P (total x y))=>[-> //| /eqP /H1 //| -> //=]; rewrite orbT.
Qed.

Definition seq_ordMixin := OrdMixin irr_ords trans_ords total_ords.
Canonical Structure seq_ordType := Eval hnf in OrdType (seq T) seq_ordMixin.
End SeqOrd.

(* A trivial total ordering for Unit *)
Section unitOrd.
Let ordtt (x y : unit ) := false.

Lemma irr_tt : irreflexive ordtt.
Proof. by []. Qed.

Lemma trans_tt : transitive ordtt.
Proof. by []. Qed.

Lemma total_tt : forall x y, [|| ordtt x y, x == y | ordtt y x ].
Proof. by []. Qed.

Let unit_ordMixin := OrdMixin irr_tt trans_tt total_tt.
Canonical Structure unit_ordType := Eval hnf in OrdType unit unit_ordMixin.
End unitOrd.