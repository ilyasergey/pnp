Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.ssrfun Ssreflect.seq.
Require Import idynamic ordtype finmap pcm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* reference implementation of finite maps *)
(* with keys satisfying condition p *)
(* and supporting disjoint union via a top element *)

Module UM.
Section UM.
Variables (K : ordType) (V : Type) (p : pred K).

Inductive base := 
  Undef | Def (f : {finMap K -> V}) of all p (supp f).

Section FormationLemmas.
Variable (f g : {finMap K -> V}). 

Lemma all_supp_insP k v : p k -> all p (supp f) -> all p (supp (ins k v f)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_ins inE /=.
by case: eqP=>[->|_] //=; move/(allP H2). 
Qed.

Lemma all_supp_remP k : all p (supp f) -> all p (supp (rem k f)). 
Proof. 
move=>H; apply/allP=>x; rewrite supp_rem inE /=.
by case: eqP=>[->|_] //=; move/(allP H).
Qed.

Lemma all_supp_fcatP : 
        all p (supp f) -> all p (supp g) -> all p (supp (fcat f g)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_fcat inE /=.
by case/orP; [move/(allP H1) | move/(allP H2)].
Qed.

Lemma all_supp_kfilterP q : 
        all p (supp f) -> all p (supp (kfilter q f)). 
Proof.
move=>H; apply/allP=>x; rewrite supp_kfilt mem_filter. 
by case/andP=>_ /(allP H).
Qed.

End FormationLemmas.

Implicit Types (k : K) (v : V) (f g : base).

Lemma umapE (f g : base) : 
        f = g <-> match f, g with
                     Def f' pf, Def g' pg => f' = g'
                  | Undef, Undef => true
                  | _, _ => false
                  end.
Proof.
split; first by move=>->; case: g.
case: f; case: g=>// f pf g pg E; rewrite {g}E in pg *.
by congr Def; apply: bool_irrelevance.
Qed.

Definition valid f := if f is Def _ _ then true else false.

Definition empty := @Def (finmap.nil K V) is_true_true.

Definition upd k v f := 
  if f is Def fs fpf then 
    if decP (@idP (p k)) is left pf then 
      Def (all_supp_insP v pf fpf)
    else Undef
  else Undef.

Definition dom f : pred K := 
  if f is Def fs _ then fun x => x \in supp fs else pred0.

Definition dom_eq f1 f2 :=
 (valid f1 == valid f2) && 
  match f1, f2 with
    Def fs1 _, Def fs2 _ => supp fs1 == supp fs2
  | Undef, Undef => true
  | _, _ => false
  end.

Definition free k f := 
  if f is Def fs pf then Def (all_supp_remP k pf)
  else Undef.

Definition find k f := if f is Def fs _ then fnd k fs else None. 

Definition union f1 f2 := 
  if (f1, f2) is (Def fs1 pf1, Def fs2 pf2) then  
    if disj fs1 fs2 then 
      Def (all_supp_fcatP pf1 pf2)
    else Undef
  else Undef.

Definition um_filter q f := 
  if f is Def fs pf then Def (all_supp_kfilterP q pf) else Undef.

Definition empb f := if f is Def fs _ then supp fs == [::] else false. 

Definition pts k v := upd k v empty.

Lemma base_ind' (P : base -> Prop) : 
         P Undef -> P empty ->
         (forall k v f, P f -> valid (union (pts k v) f) -> 
                        P (union (pts k v) f)) ->
         forall f, P f.
Proof.
rewrite /empty => H1 H2 H3; apply: base_ind=>//. 
apply: fmap_ind'=>[|k v f S IH] H. 
- by set f := Def _ in H2; rewrite (_ : Def H = f) // /f umapE.
have N : k \notin supp f by apply: notin_path S.
have [T1 T2] : p k /\ all p (supp f).
- split; first by apply: (allP H k); rewrite supp_ins inE /= eq_refl.
- apply/allP=>x T; apply: (allP H x).  
  by rewrite supp_ins inE /= T orbT. 
have E : FinMap (sorted_ins' k v (sorted_nil K V)) = ins k v (@nil K V) by [].
have: valid (union (pts k v) (Def T2)).
- rewrite /valid /union /pts /upd /=.
  case: decP; last by rewrite T1.
  by move=>T; case: ifP=>//; rewrite E disjC disj_ins N disj_nil.
move/(H3 k v _ (IH T2)).
rewrite (_ : union (pts k v) (Def T2) = Def H) //.
rewrite umapE /union /pts /upd /=.
case: decP=>// T; case: ifP=> D.
- by rewrite E fcat_inss // fcat0s.
by rewrite E disjC disj_ins N disj_nil in D.
Qed.

End UM.
End UM.

(* a class of union_map types *)

Module UMC.
Section MixinDef.
Variables (K : ordType) (V : Type) (p : pred K).

Structure mixin_of (T : Type) := Mixin {
  defined_op : T -> bool;
  empty_op : T;
  undef_op : T;
  upd_op : T -> K -> V -> T;
  dom_op : T -> pred K;
  dom_eq_op : T -> T -> bool;
  free_op : T -> K -> T;
  find_op : T -> K -> option V;
  union_op : T -> T -> T;
  um_filter_op : T -> pred K -> T;
  empb_op : T -> bool;
  pts_op : K -> V -> T;

  from_op : T -> UM.base V p;
  to_op : UM.base V p -> T;
  _ : forall b, from_op (to_op b) = b;
  _ : forall f, to_op (from_op f) = f;
  _ : forall f, defined_op f = UM.valid (from_op f);
  _ : undef_op = to_op (UM.Undef V p);
  _ : empty_op = to_op (UM.empty V p);
  _ : forall k v f, upd_op f k v = to_op (UM.upd k v (from_op f));
  _ : forall f, dom_op f = UM.dom (from_op f);
  _ : forall f1 f2, dom_eq_op f1 f2 = UM.dom_eq (from_op f1) (from_op f2);
  _ : forall k f, free_op f k = to_op (UM.free k (from_op f));
  _ : forall k f, find_op f k = UM.find k (from_op f);
  _ : forall f1 f2, 
        union_op f1 f2 = to_op (UM.union (from_op f1) (from_op f2));
  _ : forall q f, um_filter_op f q = to_op (UM.um_filter q (from_op f));
  _ : forall f, empb_op f = UM.empb (from_op f);
  _ : forall k v, pts_op k v = to_op (UM.pts p k v)}.
End MixinDef.

Section ClassDef.

Structure class_of (T : Type) := Class {
  K : ordType;
  V : Type;
  p : pred K;
  mixin : mixin_of V p T}.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Definition pack (K : ordType) V p (m : @mixin_of K V p T) := 
  @Pack T (@Class T K V p m) T.

Notation keys := (K class).
Notation vals := (V class).
Definition cond : pred keys := @p _ class.
Definition from := from_op (mixin class).
Definition to := to_op (mixin class).
Definition defined := defined_op (mixin class).
Definition um_undef := undef_op (mixin class).
Definition empty := empty_op (mixin class).
Definition upd : cT -> keys -> vals -> cT := upd_op (mixin class).
Definition dom : cT -> pred keys := dom_op (mixin class).
Definition dom_eq := dom_eq_op (mixin class).
Definition free : cT -> keys -> cT := free_op (mixin class).
Definition find : cT -> keys -> option vals := find_op (mixin class).
Definition union := union_op (mixin class).
Definition um_filter : cT -> pred keys -> cT := um_filter_op (mixin class).
Definition empb := empb_op (mixin class).
Definition pts : keys -> vals -> cT := pts_op (mixin class).

End ClassDef.

Implicit Arguments um_undef [cT].
Implicit Arguments empty [cT].
Prenex Implicits to um_undef empty.

Section Lemmas.
Variable U : type.
Local Coercion sort : type >-> Sortclass.
Implicit Type f : U.

Notation keys U := (@K _ (class U)).
Notation vals U := (@V _ (class U)).

Lemma ftE (b : UM.base (vals U) (@cond U)) : from (to b) = b.
Proof. by case: U b=>x [K V p][*]. Qed.

Lemma tfE f : to (from f) = f.
Proof. by case: U f=>x [K V p][*]. Qed.

Lemma eqE (b1 b2 : UM.base (vals U) (@cond U)) : 
        to b1 = to b2 <-> b1 = b2. 
Proof. by split=>[E|-> //]; rewrite -[b1]ftE -[b2]ftE E. Qed.

Lemma defE f : defined f = UM.valid (from f).
Proof. by case: U f=>x [K V p][*]. Qed.

Lemma undefE : um_undef = to (UM.Undef (vals U) (@cond U)).
Proof. by case: U=>x [K V p][*]. Qed.

Lemma emptyE : empty = to (UM.empty (vals U) (@cond U)).
Proof. by case: U=>x [K V p][*]. Qed.

Lemma updE k v f : upd f k v = to (UM.upd k v (from f)).
Proof. by case: U k v f=>x [K V p][*]. Qed.

Lemma domE f : dom f = UM.dom (from f).
Proof. by case: U f=>x [K V p][*]. Qed.

Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by case: U f1 f2=>x [K V p][*]. Qed.

Lemma freeE k f : free f k = to (UM.free k (from f)).
Proof. by case: U k f=>x [K V p][*]. Qed.

Lemma findE k f : find f k = UM.find k (from f).
Proof. by case: U k f=>x [K V p][*]. Qed.

Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by case: U f1 f2=>x [K V p][*]. Qed.

Lemma um_filterE q f : um_filter f q = to (UM.um_filter q (from f)).
Proof. by case: U q f=>x [K V p][*]. Qed.

Lemma empbE f : empb f = UM.empb (from f).
Proof. by case: U f=>x [K V p][*]. Qed.

Lemma ptsE k v : pts k v = to (UM.pts (@cond U) k v).
Proof. by case: U k v=>x [K V p][*]. Qed.

End Lemmas.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation union_map_class := type.
Notation UMCMixin := Mixin.
Notation UMC T m := (@pack T _ _ _ m).

Notation "[ 'umcMixin' 'of' T ]" := (mixin (class _ : class_of T))
  (at level 0, format "[ 'umcMixin'  'of'  T ]") : form_scope.
Notation "[ 'um_class' 'of' T 'for' C ]" := (@clone T C _ id)
  (at level 0, format "[ 'um_class'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'um_class' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'um_class'  'of'  T ]") : form_scope.

(* switching the order or arguments at a few operators *)
(* in the semantics f has to lead the arguments, as f's type *)
(* provides the types for keys and values *)
(* but in the printint, i like f to appear last *)
Notation keys U := (@K _ (class U)).
Notation vals U := (@V _ (class U)). 
Notation cond := cond.
Notation um_undef := um_undef.
Notation upd k v f := (upd f k v).
(* we will have a better dom operator soon *)
(* so name this one dom' *)
Notation dom' := dom.
Notation dom_eq := dom_eq.
Notation free k f := (free f k).
Notation find k f := (find f k).
Notation um_filter q f := (um_filter f q).
Notation empb := empb.
Notation pts := pts.

Definition umE := 
  (ftE, tfE, eqE, undefE, defE, emptyE, updE, domE, dom_eqE, 
   freeE, findE, unionE, um_filterE, empbE, ptsE, UM.umapE).

End Exports.

End UMC.

Export UMC.Exports.

(* new dom, which switches the unification order of k and f arguments *)
(* so that the type of k can be picked up from f *)

Definition dom2 (U : union_map_class) (f : U) (A : ordType) (pf : A = keys U) := 
  fun k : A => (@icoerce ordType id A (keys U) k pf) \in dom' f.

(* in application, we never use new dom, only dom2, where the check for A = keys U *)
(* is enforced by erefl *)
Notation dom f := (@dom2 _ f _ (erefl _)).

(***********************)
(* monoidal properties *)
(***********************)

Module UnionMapClassPCM.
Section UnionMapClassPCM.
Variable U : union_map_class.
Implicit Type f : U.

Local Notation "f1 \+ f2" := (@UMC.union _ f1 f2) 
  (at level 43, left associativity).
Local Notation valid := (@UMC.defined U).
Local Notation unit := (@UMC.empty U).

Lemma joinC f1 f2 : f1 \+ f2 = f2 \+ f1.
Proof.
rewrite !umE /UM.union.
case: (UMC.from f1)=>[|f1' H1]; case: (UMC.from f2)=>[|f2' H2] //.
by case: ifP=>E; rewrite disjC E // fcatC.
Qed.

Lemma joinCA f1 f2 f3 : f1 \+ (f2 \+ f3) = f2 \+ (f1 \+ f3).
Proof.
rewrite !umE /UM.union /=.
case: (UMC.from f1) (UMC.from f2) (UMC.from f3)=>[|f1' H1][|f2' H2][|f3' H3] //.
case E1: (disj f2' f3'); last first.
- by case E2: (disj f1' f3')=>//; rewrite disj_fcat E1 andbF.
rewrite disj_fcat andbC.
case E2: (disj f1' f3')=>//; rewrite disj_fcat (disjC f2') E1 /= andbT.
by case E3: (disj f1' f2')=>//; rewrite fcatAC // E1 E2 E3.
Qed.

Lemma joinA f1 f2 f3 : f1 \+ (f2 \+ f3) = (f1 \+ f2) \+ f3.
Proof. by rewrite (joinC f2) joinCA joinC. Qed.

Lemma validL f1 f2 : valid (f1 \+ f2) -> valid f1.
Proof. by rewrite !umE; case: (UMC.from f1). Qed.

Lemma unitL f : unit \+ f = f.
Proof. 
rewrite -[f]UMC.tfE !umE /UM.union /UM.empty.
by case: (UMC.from f)=>[//|f' H]; rewrite disjC disj_nil fcat0s.
Qed.

Lemma validU : valid unit. 
Proof. by rewrite !umE. Qed.

End UnionMapClassPCM.

Module Exports.
Section Exports.
Variable U : union_map_class.

(* generic structure for PCM for *all* union maps *)
(* I will add specific ones too for individual types *)
(* so that the projections can match against a concrete type *)
(* not against another projection, as is the case *)
(* with the generic class here *)
Definition union_map_classPCMMixin := 
  PCMMixin (@joinC U) (@joinA U) (@unitL U) (@validL U) (validU U).
Canonical union_map_classPCM := Eval hnf in PCM U union_map_classPCMMixin.

End Exports.
End Exports.

End UnionMapClassPCM.

Export UnionMapClassPCM.Exports.


(*****************)
(* Cancelativity *)
(*****************)

Section Cancelativity.
Variables U : union_map_class.
Implicit Type f : U.

Lemma joinKf f f1 f2 : valid (f1 \+ f) -> f1 \+ f = f2 \+ f -> f1 = f2.
Proof.
rewrite -{3}[f1]UMC.tfE -{2}[f2]UMC.tfE !pcmE /= !umE /UM.valid /UM.union.
case: (UMC.from f) (UMC.from f1) (UMC.from f2)=>
[|f' H]; case=>[|f1' H1]; case=>[|f2' H2] //;
case: ifP=>//; case: ifP=>// D1 D2 _ E.  
by apply: fcatsK E; rewrite D1 D2.
Qed.

Lemma joinfK f f1 f2 : valid (f \+ f1) -> f \+ f1 = f \+ f2 -> f1 = f2.
Proof. by rewrite !(joinC f); apply: joinKf. Qed.

End Cancelativity.


(*********************************************************)
(* if V is an equality type, then union_map_class is too *)
(*********************************************************)                               

Module UnionMapEq. 
Section UnionMapEq. 
Variables (K : ordType) (V : eqType) (p : pred K).
Variables (T : Type) (m : @UMC.mixin_of K V p T).

Definition unionmap_eq (f1 f2 : UMC T m) := 
  match (UMC.from f1), (UMC.from f2) with 
  | UM.Undef, UM.Undef => true
  | UM.Def f1' pf1, UM.Def f2' pf2 => f1' == f2'
  | _, _ => false
  end. 

Lemma unionmap_eqP : Equality.axiom unionmap_eq.
Proof.
move=>x y; rewrite -{1}[x]UMC.tfE -{1}[y]UMC.tfE /unionmap_eq.
case: (UMC.from x)=>[|f1 H1]; case: (UMC.from y)=>[|f2 H2] /=.
- by constructor. 
- by constructor; move/(@UMC.eqE (UMC T m)). 
- by constructor; move/(@UMC.eqE (UMC T m)). 
case: eqP=>E; constructor; rewrite (@UMC.eqE (UMC T m)).
- by rewrite UM.umapE.
by case.
Qed.

End UnionMapEq.

Module Exports.
Section Exports.
Variables (K : ordType) (V : eqType) (p : pred K).
Variables (T : Type) (m : @UMC.mixin_of K V p T).

Definition union_map_class_eqMixin := EqMixin (@unionmap_eqP K V p T m).
(* don't declare canonical here, but do so for every type individually *)
(* we don't have a generic theory of decidable equality for union_maps *)
(* so this is not needed here *)
(* unlike pcm notation, which we use in all the lemmas *)
(* so we need a generic projection from union_map to pcm *)
(*
Canonical union_map_class_eqType := 
  Eval hnf in EqType (UMC T m) union_map_class_eqMixin.
*)

End Exports.
End Exports.

End UnionMapEq.

Export UnionMapEq.Exports.

(********)
(* dom' *)
(********)

Section DomPrimeLemmas.
Variable U : union_map_class. 
Implicit Types (k : keys U) (v : vals U) (f g : U).

Lemma dom0' : dom' (Unit : U) = pred0.
Proof. by rewrite pcmE /= !umE. Qed.

Lemma dom0E' f : valid f -> dom' f =i pred0 -> f = Unit. 
Proof.
rewrite !pcmE /= !umE /UM.valid /UM.dom /UM.empty -{3}[f]UMC.tfE.
case: (UMC.from f)=>[|f' S] //= _; rewrite !umE fmapE /= {S}.
by case: f'; case=>[|kv s] //= P /= /(_ kv.1); rewrite inE eq_refl. 
Qed.

Lemma domU' k v f : 
        dom' (upd k v f) =i 
        [pred x | cond k & if x == k then valid f else x \in dom' f].
Proof.
rewrite pcmE /= !umE /UM.dom /UM.upd /UM.valid /= /cond.
case: (UMC.from f)=>[|f' H] /= x.
- by rewrite !inE /= andbC; case: ifP.
case: decP; first by move=>->; rewrite supp_ins.
by move/(introF idP)=>->. 
Qed.

Lemma domF' k f : 
        dom' (free k f) =i 
        [pred x | if k == x then false else x \in dom' f].
Proof.
rewrite !umE; case: (UMC.from f)=>[|f' H] x; rewrite -!topredE /=;
by case: ifP=>// E; rewrite supp_rem inE /= eq_sym E.
Qed.

Lemma domUn' f1 f2 :
        dom' (f1 \+ f2) =i
        [pred x | valid (f1 \+ f2) & (x \in dom' f1) || (x \in dom' f2)].
Proof.
rewrite !pcmE /= !umE /UM.dom /UM.valid /UM.union.
case: (UMC.from f1) (UMC.from f2)=>[|f1' H1] // [|f2' H2] // x.
by case: ifP=>E //; rewrite supp_fcat.
Qed.

Lemma dom_valid' k f : k \in dom' f -> valid f.
Proof. by rewrite pcmE /= !umE; case: (UMC.from f). Qed.

Lemma dom_cond' k f : k \in dom' f -> cond k.
Proof. by rewrite !umE; case: (UMC.from f)=>[|f' F] // /(allP F). Qed.

Lemma dom_free' k f : k \notin dom' f -> free k f = f.
Proof. 
rewrite -{3}[f]UMC.tfE !umE /UM.dom /UM.free.
by case: (UMC.from f)=>[|f' H] //; apply: rem_supp.
Qed.

CoInductive dom_find_spec' k f : bool -> Type := 
| dom_find_none' : find k f = None -> dom_find_spec' k f false
| dom_find_some' v : find k f = Some v -> 
    f = upd k v (free k f) -> dom_find_spec' k f true.

Lemma dom_find' k f : dom_find_spec' k f (k \in dom' f).
Proof.
rewrite !umE /UM.dom -{1}[f]UMC.tfE.
case: (UMC.from f)=>[|f' H]. 
- by apply: dom_find_none'; rewrite !umE.
case: suppP (allP H k)=>[v|] H1 I; last first.
- by apply: dom_find_none'; rewrite !umE. 
apply: (dom_find_some' (v:=v)); rewrite !umE // /UM.upd /UM.free.
case: decP=>H2; last by rewrite I in H2.
apply/fmapP=>k'; rewrite fnd_ins.
by case: ifP=>[/eqP-> //|]; rewrite fnd_rem => ->. 
Qed.

Lemma find_some' k v f : find k f = Some v -> k \in dom' f.
Proof. by case: dom_find'=>// ->. Qed.

Lemma find_none' k f : find k f = None -> k \notin dom' f.
Proof. by case: dom_find'=>// v ->. Qed.

Lemma dom_um_filt' p f : dom' (um_filter p f) =i [predI p & dom' f].
Proof.
rewrite !umE /UM.dom /UM.um_filter.
case: (UMC.from f)=>[|f' H] x; first by rewrite !inE /= andbF. 
by rewrite supp_kfilt mem_filter. 
Qed.

Lemma dom_prec' f1 f2 g1 g2 : 
        valid (f1 \+ g1) -> 
        f1 \+ g1 = f2 \+ g2 -> 
        dom' f1 =i dom' f2 -> f1 = f2.
Proof.
rewrite -{4}[f1]UMC.tfE -{3}[f2]UMC.tfE !pcmE /= !umE.
rewrite /UM.valid /UM.union /UM.dom; move=>D E.
case: (UMC.from f1) (UMC.from f2) (UMC.from g1) (UMC.from g2) E D=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //;
case: ifP=>// D1; case: ifP=>// D2 E _ E1; apply/fmapP=>k.
move/(_ k): E1; rewrite -!topredE /= => E1.
case E2: (k \in supp f2') in E1; last first.
- by move/negbT/fnd_supp: E1=>->; move/negbT/fnd_supp: E2=>->.
suff L: forall m s, k \in supp m -> disj m s -> 
          fnd k m = fnd k (fcat m s) :> option (vals U).
- by rewrite (L _ _ E1 D1) (L _ _ E2 D2) E. 
by move=>m s S; case: disjP=>//; move/(_ _ S)/negbTE; rewrite fnd_fcat=>->. 
Qed.

Lemma domK' f1 f2 g1 g2 : 
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        dom' (f1 \+ g1) =i dom' (f2 \+ g2) ->
        dom' f1 =i dom' f2 -> dom' g1 =i dom' g2.
Proof.
rewrite !pcmE /= !umE /UM.valid /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2) (UMC.from g1) (UMC.from g2)=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //.
case: disjP=>// D1 _; case: disjP=>// D2 _ E1 E2 x. 
move: {E1 E2} (E2 x) (E1 x).
rewrite -!topredE /= !supp_fcat !inE /= => E.
move: {D1 D2} E (D1 x) (D2 x)=><- /implyP D1 /implyP D2.
case _ : (x \in supp f1') => //= in D1 D2 *.
by move/negbTE: D1=>->; move/negbTE: D2=>->.
Qed.

Lemma um_filt_dom' f1 f2 : 
        valid (f1 \+ f2) -> um_filter (dom' f1) (f1 \+ f2) = f1.
Proof.
rewrite -{4}[f1]UMC.tfE !pcmE /= !umE.
rewrite /UM.valid /UM.union /UM.um_filter /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// D _; rewrite kfilt_fcat /=.
have E1: {in supp f1', supp f1' =i predT} by [].
have E2: {in supp f2', supp f1' =i pred0}.
- by move=>x; rewrite disjC in D; case: disjP D=>// D _ /D /negbTE ->. 
rewrite (eq_in_kfilter E1) (eq_in_kfilter E2).
by rewrite kfilter_predT kfilter_pred0 fcats0.
Qed.

End DomPrimeLemmas.

Prenex Implicits find_some' find_none'.

(*************************************)
(* repeating the dom' lemmas for dom *)
(*************************************)

Section GoodDomLemmas.
Variables (U : union_map_class) (A : ordType) (pf : A = keys U).
Notation retype k := (@icoerce ordType id _ _ k pf).
Implicit Types (k : keys U) (v : vals U) (f : U).

Lemma dom0 : dom (Unit : U) = pred0.
Proof. by apply: dom0'. Qed.

Lemma dom0E f : valid f -> dom f =i pred0 -> f = Unit. 
Proof. by apply: dom0E'. Qed.

Lemma domU k v f : 
        dom2 (upd k v f) pf =i 
        [pred x | cond k & if retype x == k then valid f 
                           else x \in dom2 f pf].
Proof.
move: (pf); rewrite pf => pf' x; rewrite /dom2.
by rewrite -!topredE /= ieqc domU' -!topredE /= !ieqc. 
Qed.

Lemma domF k f : 
        dom2 (free k f) pf =i
        [pred x | if k == retype x then false else x \in dom2 f pf].
Proof.
move: (pf); rewrite pf => pf' x; rewrite /dom2.
by rewrite -topredE /= ieqc domF' -!topredE /= -!topredE /= !ieqc.
Qed. 

Lemma domUn f1 f2 : 
        dom2 (f1 \+ f2) pf =i 
        [pred x | valid (f1 \+ f2) & (x \in dom2 f1 pf) || (x \in dom2 f2 pf)].
Proof.
move: (pf); rewrite pf => pf' x; rewrite /dom2.
by rewrite -topredE /= ieqc domUn'; rewrite -!topredE /= -!topredE /= ieqc.
Qed.

Lemma dom_valid x f : x \in dom f -> valid f.
Proof. by move/dom_valid'. Qed.

Lemma dom_cond x f : x \in dom f -> cond x.
Proof. by move/dom_cond'. Qed.

Lemma dom_free x f : x \notin dom f -> free x f = f.
Proof. by move/dom_free'. Qed.

CoInductive dom_find_spec f x : bool -> Type := 
| dom_find_none : find (retype x) f = None -> dom_find_spec f x false
| dom_find_some v : find (retype x) f = Some v -> 
    f = upd (retype x) v (free (retype x) f) -> dom_find_spec f x true.

(* proof for dom_find_spec has to be done outside the section *)
(* because needs to abstract over section variables *)

Lemma dom_um_filt p f : 
        dom2 (um_filter p f) pf =i 
        [predI (@icoerce ordType pred _ _ p (esym pf)) & dom2 f pf].
Proof.
move: (pf); rewrite pf => pf' x; rewrite /dom2.
by rewrite -topredE /= ieqc dom_um_filt' -!topredE /= -!topredE /= !ieqc.
Qed.

(*
Lemma dom_um_filt p f : 
        dom2 (um_filter p f) pf =i 
        [predI [pred x | icoerce x \in p] & dom2 f pf].
Proof.
move: (pf); rewrite pf => pf' x; rewrite /dom2.
by rewrite -topredE /= ieqc dom_um_filt' -!topredE /= -!topredE /= ieqc.
Qed.
*)

Lemma dom_prec f1 f2 g1 g2 : 
        valid (f1 \+ g1) -> 
        f1 \+ g1 = f2 \+ g2 -> 
        dom2 f1 pf =i dom2 f2 pf -> f1 = f2.
Proof.
move: (pf); rewrite pf => pf' V E; rewrite /dom2 => H.
by apply: dom_prec' V E _ => x; move: (H x); rewrite -!topredE /= ieqc. 
Qed.

Lemma domK f1 f2 g1 g2 : 
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        dom2 (f1 \+ g1) pf =i dom2 (f2 \+ g2) pf ->
        dom2 f1 pf =i dom2 f2 pf -> dom2 g1 pf =i dom2 g2 pf.
Proof.
move: (pf); rewrite pf => pf' V1 V2; rewrite /dom2 => E1 E2 x.
rewrite -!topredE /= ieqc; apply: (domK' V1 V2).
- by move=>{x} x; move: (E1 x); rewrite -!topredE /= ieqc.
by move=>{x} x; move: (E2 x); rewrite -!topredE /= ieqc.
Qed.

Lemma um_filt_dom f1 f2 : 
        valid (f1 \+ f2) -> um_filter (dom f1) (f1 \+ f2) = f1.
Proof. by apply: um_filt_dom'. Qed.

End GoodDomLemmas.

Section DomFind.
Variable U : union_map_class.

Lemma dom_find (A : ordType) f x (pf : A = keys U) : 
        dom_find_spec pf f x (x \in dom2 f pf).
Proof.
move: (pf) x; rewrite pf /dom2 => {pf} pf x; rewrite -topredE /= ieqc.
rewrite !umE /UM.dom -{1}[f]UMC.tfE.
case: (UMC.from f)=>[|f' H]. 
- by apply: dom_find_none; rewrite !umE.
case: suppP (allP H x)=>[v|] H1 I; last first.
- by apply: dom_find_none; rewrite !umE ieqc. 
apply: (dom_find_some (v:=v)); rewrite !umE ieqc // /UM.upd /UM.free.
case: decP=>H2; last by rewrite I in H2.
apply/fmapP=>k'; rewrite fnd_ins.
by case: ifP=>[/eqP-> //|]; rewrite fnd_rem => ->. 
Qed.

Lemma find_some k v (f : U) : find k f = Some v -> k \in dom f.
Proof. by case: dom_find=>// ->. Qed.

Lemma find_none k (f : U) : find k f = None -> k \notin dom f.
Proof. by case: dom_find=>// v ->. Qed.

End DomFind.


(**********)
(* filter *)
(**********)

Section FilterLemmas.
Variable U : union_map_class.
Implicit Type f : U.

Lemma um_filtUn q f1 f2 : 
        valid (f1 \+ f2) -> 
        um_filter q (f1 \+ f2) = um_filter q f1 \+ um_filter q f2.
Proof.
rewrite !pcmE /= !umE /UM.valid /UM.union.
case: (UMC.from f1)=>[|f1' H1]; case: (UMC.from f2)=>[|f2' H2] //=. 
by case: ifP=>D //= _; rewrite kfilt_fcat disj_kfilt.
Qed.

Lemma um_filt0 q : um_filter q Unit = Unit :> U.
Proof. by rewrite !pcmE /= !umE /UM.um_filter /UM.empty kfilt_nil. Qed.

Lemma um_filt_pred0 f : valid f -> um_filter pred0 f = Unit.
Proof.
rewrite !pcmE /= !umE /UM.valid /UM.empty.
case: (UMC.from f)=>[|f' H] //= _; case: f' H=>f' P H.
by rewrite fmapE /= /kfilter' filter_pred0.
Qed.

Lemma um_filt_predT f : um_filter predT f = f.
Proof. 
rewrite -[f]UMC.tfE !umE /UM.um_filter.
by case: (UMC.from f)=>[|f' H] //; rewrite kfilter_predT.
Qed.

Lemma um_filt_predI p1 p2 f : 
        um_filter (predI p1 p2) f = um_filter p1 (um_filter p2 f).
Proof. 
rewrite -[f]UMC.tfE !umE /UM.um_filter.
by case: (UMC.from f)=>[|f' H] //; rewrite kfilter_predI.
Qed.

Lemma um_filt_predU p1 p2 f : 
        um_filter (predU p1 p2) f = 
        um_filter p1 f \+ um_filter (predD p2 p1) f.
Proof.
rewrite pcmE /= !umE /UM.um_filter /UM.union /=.
case: (UMC.from f)=>[|f' H] //=. 
rewrite in_disj_kfilt; last by move=>x _; rewrite /= negb_and orbA orbN. 
rewrite -kfilter_predU.
by apply: eq_in_kfilter=>x _; rewrite /= orb_andr orbN.
Qed.

Lemma eq_in_um_filt p1 p2 f : 
        {in dom f, p1 =1 p2} -> um_filter p1 f = um_filter p2 f.
Proof.
rewrite /dom2 !umE /UM.dom /UM.um_filter /= /dom2.
by case: (UMC.from f)=>[|f' H] //=; apply: eq_in_kfilter.
Qed.

Lemma um_filtUnK p f1 f2 : 
        valid (f1 \+ f2) ->    
        um_filter p (f1 \+ f2) = f1 -> 
        um_filter p f1 = f1 /\ um_filter p f2 = Unit. 
Proof.
move=>V. rewrite (um_filtUn _ V) => E.
have {V} V : valid (um_filter p f1 \+ um_filter p f2). 
- by rewrite E; move/validL: V.
have F : dom (um_filter p f1) =i dom f1.
- move=>x; rewrite dom_um_filt inE /=.
  apply/andP/idP=>[[//]| H1]; split=>//; move: H1.
  rewrite -{1}E domUn inE /= !dom_um_filt inE /= inE /=.
  by case: (x \in p)=>//=; rewrite andbF.
rewrite -{2}[f1]unitR in E F; move/(dom_prec V E): F=>X.
by rewrite X in E V; move/(joinfK V): E. 
Qed.

Lemma um_filtU p k v f : 
        um_filter p (upd k v f) = 
        if p k then upd k v (um_filter p f) else 
          if cond k then um_filter p f else um_undef.
Proof. 
rewrite !umE /UM.um_filter /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by case: ifP=>H1 //; case: ifP.
case: ifP=>H1; case: decP=>H2 //.
- by rewrite !umE kfilt_ins H1.
- by rewrite H2 !umE kfilt_ins H1.
by case: ifP H2.
Qed.

Lemma um_filtF p k f : 
        um_filter p (free k f) = 
        if p k then free k (um_filter p f) else um_filter p f.
Proof. 
rewrite !umE /UM.um_filter /UM.free.
by case: (UMC.from f)=>[|f' F]; case: ifP=>// E; rewrite !umE kfilt_rem E.
Qed.

End FilterLemmas.


(*********)
(* valid *)
(*********)

Section ValidLemmas.
Variable U : union_map_class. 
Implicit Types (k : keys U) (v : vals U) (f g : U).

Lemma invalidE f : ~~ valid f <-> f = um_undef.
Proof. by rewrite !pcmE /= !umE -2![f]UMC.tfE !umE; case: (UMC.from f). Qed.

Lemma validU k v f : valid (upd k v f) = cond k && valid f.
Proof. 
rewrite !pcmE /= !umE /UM.valid /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by rewrite andbF.
by case: decP=>[|/(introF idP)] ->. 
Qed.

Lemma validF k f : valid (free k f) = valid f.
Proof. by rewrite !pcmE /= !umE; case: (UMC.from f). Qed.

CoInductive validUn_spec f1 f2 : bool -> Type :=
| valid_false1 of ~~ valid f1 : validUn_spec f1 f2 false
| valid_false2 of ~~ valid f2 : validUn_spec f1 f2 false
| valid_false3 k of k \in dom f1 & k \in dom f2 : validUn_spec f1 f2 false
| valid_true of valid f1 & valid f2 & 
    (forall x, x \in dom f1 -> x \notin dom f2) : validUn_spec f1 f2 true.

Lemma validUn f1 f2 : validUn_spec f1 f2 (valid (f1 \+ f2)).
Proof.
rewrite !pcmE /= !umE -{1}[f1]UMC.tfE -{1}[f2]UMC.tfE.
rewrite /UM.valid /UM.union /=.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] /=.
- by apply: valid_false1; rewrite pcmE /= !umE.
- by apply: valid_false1; rewrite pcmE /= !umE. 
- by apply: valid_false2; rewrite pcmE /= !umE. 
case: ifP=>E.
- apply: valid_true; try by rewrite !pcmE /= !umE.
  by move=>k; rewrite /dom2 /= !umE => H; case: disjP E=>//; move/(_ _ H).
case: disjP E=>// k T1 T2 _.
by apply: (valid_false3 (k:=k)); rewrite /dom2 /= !umE.
Qed.

Lemma validFUn k f1 f2 : 
        valid (f1 \+ f2) -> valid (free k f1 \+ f2).
Proof.
case: validUn=>// V1 V2 H _; case: validUn=>//; last 1 first.
- by move=>k'; rewrite domF inE; case: eqP=>// _ /H/negbTE ->.
by rewrite validF V1.
by rewrite V2.
Qed.

Lemma validUnF k f1 f2 : 
        valid (f1 \+ f2) -> valid (f1 \+ free k f2).
Proof. by rewrite !(joinC f1); apply: validFUn. Qed.

Lemma validUnU k v f1 f2 : 
        k \in dom f2 -> valid (f1 \+ upd k v f2) = valid (f1 \+ f2).
Proof.
move=>D; apply/esym; move: D; case: validUn.
- by move=>V _; apply/esym/negbTE; apply: contra V; move/validL. 
- move=>V _; apply/esym/negbTE; apply: contra V; move/validR. 
  by rewrite validU; case/andP. 
- move=>k' H1 H2 _; case: validUn=>//; rewrite validU => D1 /andP [H D2].
  by move/(_ k' H1); rewrite domU !inE H /= D2 H2; case: ifP.
move=>V1 V2 H1 H2; case: validUn=>//.
- by rewrite V1. 
- by rewrite validU V2 (dom_cond H2). 
move=>k'; rewrite domU !inE /= (dom_cond H2) V2; move/H1=>H3. 
by rewrite (negbTE H3); case: ifP H2 H3=>// /eqP ->->.
Qed.

Lemma validUUn k v f1 f2 : 
        k \in dom f1 -> valid (upd k v f1 \+ f2) = valid (f1 \+ f2).
Proof. by move=>D; rewrite -!(joinC f2); apply: validUnU D. Qed.

Lemma valid_um_filter p f : valid (um_filter p f) = valid f.
Proof. by rewrite !pcmE /= !umE; case: (UMC.from f). Qed.

End ValidLemmas.


(**********)
(* dom_eq *)
(**********)

Section DomEqLemmas.
Variable U : union_map_class.
Implicit Type f : U.

Lemma domeqP f1 f2 : 
        reflect (valid f1 = valid f2 /\ dom f1 =i dom f2) (dom_eq f1 f2).
Proof.
rewrite !pcmE /= /dom2 !umE /UM.valid /UM.dom /UM.dom_eq /in_mem.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] /=.
- by constructor.
- by constructor; case.
- by constructor; case.
by case: eqP=>H; constructor; [rewrite H | case=>_ /suppE].
Qed.

Lemma domeq0E f : dom_eq f Unit -> f = Unit.
Proof. by case/domeqP; rewrite valid_unit dom0; apply: dom0E. Qed.

Lemma domeq_refl f : dom_eq f f.
Proof. by case: domeqP=>//; case. Qed.

Hint Resolve domeq_refl.

Lemma domeq_sym f1 f2 : dom_eq f1 f2 = dom_eq f2 f1.
Proof. 
suff L f f' : dom_eq f f' -> dom_eq f' f by apply/idP/idP; apply: L.
by case/domeqP=>H1 H2; apply/domeqP; split.
Qed.

Lemma domeq_trans f1 f2 f3 : 
        dom_eq f1 f2 -> dom_eq f2 f3 -> dom_eq f1 f3.
Proof.
case/domeqP=>E1 H1 /domeqP [E2 H2]; apply/domeqP=>//.
by split=>//; [rewrite E1 E2 | move=>x; rewrite H1 H2]. 
Qed.

Lemma domeq_validUn f1 f2 f1' f2' : 
        dom_eq f1 f2 -> dom_eq f1' f2' -> 
        valid (f1 \+ f1') = valid (f2 \+ f2').
Proof.
have L f f' g : dom_eq f f' -> valid (f \+ g) -> valid (f' \+ g).
- case/domeqP=>E F; case: validUn=>// Vg1 Vf H _; case: validUn=>//.
  - by rewrite -E Vg1. 
  - by rewrite Vf.
  by move=>x; rewrite -F; move/H/negbTE=>->. 
move=>H H'; case X: (valid (f1 \+ f1')); apply/esym. 
- by move/(L _ _ _ H): X; rewrite !(joinC f2); move/(L _ _ _ H').
rewrite domeq_sym in H; rewrite domeq_sym in H'.
apply/negbTE; apply: contra (negbT X); move/(L _ _ _ H). 
by rewrite !(joinC f1); move/(L _ _ _ H').
Qed.

Lemma domeqUn f1 f2 f1' f2' : 
        dom_eq f1 f2 -> dom_eq f1' f2' -> 
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
suff L f f' g : dom_eq f f' -> dom_eq (f \+ g) (f' \+ g).
- move=>H H'; apply: domeq_trans (L _ _ _ H).
  by rewrite !(joinC f1); apply: domeq_trans (L _ _ _ H').
move=>F; case/domeqP: (F)=>E H.
apply/domeqP; split; first by apply: domeq_validUn F _.
move=>x; rewrite !domUn /= inE.
by rewrite (domeq_validUn F (domeq_refl g)) H.
Qed.

Lemma domeqK f1 f2 f1' f2' : 
        valid (f1 \+ f1') ->
        dom_eq (f1 \+ f1') (f2 \+ f2') ->
        dom_eq f1 f2 -> dom_eq f1' f2'.
Proof.
move=>V1 /domeqP [E1 H1] /domeqP [E2 H2]; move: (V1); rewrite E1=>V2.
apply/domeqP; split; first by rewrite (validR V1) (validR V2). 
by apply: domK V1 V2 H1 H2.
Qed.

End DomEqLemmas.

Hint Resolve domeq_refl.


(**********)
(* update *)
(**********)

Section UpdateLemmas.
Variable U : union_map_class.
Implicit Types (k : keys U) (v : vals U) (f : U).

Lemma upd_invalid k v : upd k v um_undef = um_undef.
Proof. by rewrite !umE. Qed.

Lemma upd_inj k v1 v2 f : 
        valid f -> cond k -> upd k v1 f = upd k v2 f -> v1 = v2.
Proof.
rewrite !pcmE /= !umE /UM.valid /UM.upd /cond. 
case: (UMC.from f)=>[|f' F] // _; case: decP=>// H _ E.
have: fnd k (ins k v1 f') = fnd k (ins k v2 f') by rewrite E.
by rewrite !fnd_ins eq_refl; case.
Qed.

Lemma updU k1 k2 v1 v2 f : 
        upd k1 v1 (upd k2 v2 f) = 
        if k1 == k2 then upd k1 v1 f else upd k2 v2 (upd k1 v1 f).
Proof.
rewrite !umE /UM.upd. 
case: (UMC.from f)=>[|f' H']; case: ifP=>// E; 
case: decP=>H1; case: decP=>H2 //; rewrite !umE.
- by rewrite ins_ins E.
- by rewrite (eqP E) in H2 *. 
by rewrite ins_ins E. 
Qed.

Lemma updF k1 k2 v f : 
        upd k1 v (free k2 f) = 
        if k1 == k2 then upd k1 v f else free k2 (upd k1 v f).
Proof.
rewrite !umE /UM.dom /UM.upd /UM.free.
case: (UMC.from f)=>[|f' F] //; case: ifP=>// H1;
by case: decP=>H2 //; rewrite !umE ins_rem H1. 
Qed.

Lemma updUnL k v f1 f2 : 
        upd k v (f1 \+ f2) = 
        if k \in dom f1 then upd k v f1 \+ f2 else f1 \+ upd k v f2. 
Proof.
rewrite !pcmE /= /dom2 !umE /UM.upd /UM.union /UM.dom -!topredE.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //=.
- by case: ifP=>//; case: decP.
case: ifP=>// D; case: ifP=>// H1; case: decP=>// H2.
- rewrite disjC disj_ins disjC D !umE; case: disjP D=>// H _. 
  by rewrite (H _ H1) /= fcat_inss // (H _ H1).
- by rewrite disj_ins H1 D /= !umE fcat_sins.
- by rewrite disjC disj_ins disjC D andbF.
by rewrite disj_ins D andbF.
Qed.

Lemma updUnR k v f1 f2 : 
        upd k v (f1 \+ f2) = 
        if k \in dom f2 then f1 \+ upd k v f2 else upd k v f1 \+ f2.
Proof. by rewrite joinC updUnL (joinC f1) (joinC f2). Qed.

End UpdateLemmas.


(********)
(* free *)
(********)

Section FreeLemmas.
Variable U : union_map_class.
Implicit Types (k : keys U) (v : vals U) (f : U).

Lemma free0 k : free k Unit = Unit.
Proof. by rewrite !pcmE /= !umE /UM.free /UM.empty rem_empty. Qed.

Lemma freeU k1 k2 v f : 
        free k1 (upd k2 v f) = 
        if k1 == k2 then         
          if cond k2 then free k1 f else um_undef 
        else upd k2 v (free k1 f).
Proof.
rewrite !umE /UM.free /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by case: ifP=>H1 //; case: ifP.
case: ifP=>H1; case: decP=>H2 //.
- by rewrite H2 !umE rem_ins H1.
- by case: ifP H2.
by rewrite !umE rem_ins H1.
Qed.

Lemma freeF k1 k2 f : 
        free k1 (free k2 f) = 
        if k1 == k2 then free k1 f else free k2 (free k1 f).
Proof. 
rewrite !umE /UM.free.
by case: (UMC.from f)=>[|f' F]; case: ifP=>// E; rewrite !umE rem_rem E.
Qed.

Lemma freeUn k f1 f2 : 
        free k (f1 \+ f2) = 
        if k \in dom (f1 \+ f2) then free k f1 \+ free k f2 
        else f1 \+ f2.
Proof.
rewrite !pcmE /= /dom2 !umE /UM.free /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// E1; rewrite supp_fcat inE /=.
case: ifP=>E2; last by rewrite !umE rem_supp // supp_fcat inE E2.
rewrite disj_rem; last by rewrite disjC disj_rem // disjC.
rewrite !umE; case/orP: E2=>E2.
- suff E3: k \notin supp f2' by rewrite -fcat_rems // (rem_supp E3).
  by case: disjP E1 E2=>// H _; move/H.
suff E3: k \notin supp f1' by rewrite -fcat_srem // (rem_supp E3).
by case: disjP E1 E2=>// H _; move/contra: (H k); rewrite negbK.
Qed.

Lemma freeUnV k f1 f2 : 
        valid (f1 \+ f2) -> free k (f1 \+ f2) = free k f1 \+ free k f2.
Proof.
move=>V; rewrite freeUn domUn V /=; case: ifP=>//.
by move/negbT; rewrite negb_or; case/andP=>H1 H2; rewrite !dom_free.
Qed.

Lemma freeUnL k f1 f2 : k \notin dom f1 -> free k (f1 \+ f2) = f1 \+ free k f2.
Proof.
move=>V1; rewrite freeUn domUn inE (negbTE V1) /=.
case: ifP; first by case/andP; rewrite dom_free.
move/negbT; rewrite negb_and; case/orP=>V2; last by rewrite dom_free.
suff: ~~ valid (f1 \+ free k f2) by move/invalidE: V2=>-> /invalidE ->. 
apply: contra V2; case: validUn=>// H1 H2 H _.
case: validUn=>//; first by rewrite H1.
- by move: H2; rewrite validF => ->.
move=>x H3; move: (H _ H3); rewrite domF inE /=.
by case: ifP H3 V1=>[|_ _ _]; [move/eqP=><- -> | move/negbTE=>->].
Qed.

Lemma freeUnR k f1 f2 : k \notin dom f2 -> free k (f1 \+ f2) = free k f1 \+ f2.
Proof. by move=>H; rewrite joinC freeUnL // joinC. Qed.

Lemma free_um_filt p k f : 
        free k (um_filter p f) = 
        if p k then um_filter p (free k f) else um_filter p f.
Proof.
rewrite !umE /UM.free /UM.um_filter.
case: (UMC.from f)=>[|f' F]; case: ifP=>// E; rewrite !umE. 
- by rewrite kfilt_rem E.
by rewrite rem_kfilt E.
Qed.

End FreeLemmas.


(********)
(* find *)
(********)

Section FindLemmas.
Variable U : union_map_class.
Implicit Types (k : keys U) (v : vals U) (f : U).

Lemma findU k1 k2 v f : 
        find k1 (upd k2 v f) = 
        if k1 == k2 then
          if cond k2 && valid f then Some v else None
        else if cond k2 then find k1 f else None.
Proof.
rewrite pcmE /= !umE /UM.valid /UM.find /UM.upd /cond.
case: (UMC.from f)=>[|f' F]; first by rewrite andbF !if_same. 
case: decP=>H; first by rewrite H /= fnd_ins.
by rewrite (introF idP H) /= if_same.
Qed.

Lemma findF k1 k2 f : 
        find k1 (free k2 f) = if k1 == k2 then None else find k1 f. 
Proof. 
rewrite !umE /UM.find /UM.free.
case: (UMC.from f)=>[|f' F]; first by rewrite if_same.
by rewrite fnd_rem.
Qed.

Lemma findUnL k f1 f2 : 
        valid (f1 \+ f2) -> 
        find k (f1 \+ f2) = if k \in dom f1 then find k f1 else find k f2.
Proof.
rewrite !pcmE /= /dom2 !umE /UM.valid /UM.find /UM.union /UM.dom.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// D _; case: ifP=>E1; last first.
- rewrite fnd_fcat; case: ifP=>// E2.
  by rewrite fnd_supp ?E1 // fnd_supp ?E2.
suff E2: k \notin supp f2' by rewrite fnd_fcat (negbTE E2).
by case: disjP D E1=>// H _; apply: H.
Qed.

Lemma findUnR k f1 f2 : 
        valid (f1 \+ f2) ->
        find k (f1 \+ f2) = if k \in dom f2 then find k f2 else find k f1.
Proof. by rewrite joinC=>D; rewrite findUnL. Qed.

Lemma find_eta f1 f2 :  
        valid f1 -> valid f2 ->
        (forall k, find k f1 = find k f2) -> f1 = f2.
Proof. 
rewrite !pcmE /= !umE /UM.valid /UM.find -{2 3}[f1]UMC.tfE -{2 3}[f2]UMC.tfE.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] // _ _ H.
by rewrite !umE; apply/fmapP=>k; move: (H k); rewrite !umE. 
Qed.

Lemma find_um_filt p k f : 
        find k (um_filter p f) = if p k then find k f else None.
Proof. 
rewrite !umE /UM.find /UM.um_filter.
case: (UMC.from f)=>[|f' F]; first by rewrite if_same.
by rewrite fnd_kfilt.
Qed.

End FindLemmas.


(********)
(* empb *)
(********)

Section EmpbLemmas.
Variable U : union_map_class.
Implicit Types (k : keys U) (v : vals U) (f : U).

Lemma empbP f : reflect (f = Unit) (empb f).
Proof.
rewrite pcmE /= !umE /UM.empty /UM.empb -{1}[f]UMC.tfE.
case: (UMC.from f)=>[|f' F]; first by apply: ReflectF; rewrite !umE.
case: eqP=>E; constructor; rewrite !umE.
- by move/supp_nilE: E=>->. 
by move=>H; rewrite H in E.
Qed.

Lemma empbU k v f : empb (upd k v f) = false. 
Proof. 
rewrite !umE /UM.empb /UM.upd.
case: (UMC.from f)=>[|f' F] //; case: decP=>// H.
suff: k \in supp (ins k v f') by case: (supp _).
by rewrite supp_ins inE /= eq_refl.
Qed. 

Lemma empbUn f1 f2 : empb (f1 \+ f2) = empb f1 && empb f2.
Proof.
rewrite !pcmE /= !umE /UM.empb /UM.union.
case: (UMC.from f1) (UMC.from f2)=>[|f1' F1][|f2' F2] //.
- by rewrite andbF.
case: ifP=>E; case: eqP=>E1; case: eqP=>E2 //; last 2 first.
- by move: E2 E1; move/supp_nilE=>->; rewrite fcat0s; case: eqP.
- by move: E1 E2 E; do 2![move/supp_nilE=>->]; case: disjP.
- by move/supp_nilE: E2 E1=>-> <-; rewrite fcat0s eq_refl.
have [k H3]: exists k, k \in supp f1'.
- case: (supp f1') {E1 E} E2=>[|x s _] //.
  by exists x; rewrite inE eq_refl.
suff: k \in supp (fcat f1' f2') by rewrite E1.
by rewrite supp_fcat inE /= H3.
Qed.

(* some transformation lemmas *)

Lemma empbE f : f = Unit <-> empb f.
Proof. by case: empbP. Qed.

Lemma join0E f1 f2 : f1 \+ f2 = Unit <-> f1 = Unit /\ f2 = Unit.
Proof. by rewrite !empbE empbUn; case: andP. Qed.

Lemma validEb f : reflect (valid f /\ forall k, k \notin dom f) (empb f).
Proof.
case: empbP=>E; constructor; first by rewrite E valid_unit dom0. 
case=>V H; apply: E; move: V H.
rewrite !pcmE /= /dom2 !umE /UM.valid /UM.dom /UM.empty -{3}[f]UMC.tfE.
case: (UMC.from f)=>[|f' F] // _ H; rewrite !umE.
apply/supp_nilE; case: (supp f') H=>// x s /(_ x). 
by rewrite inE eq_refl. 
Qed.

Lemma validUnEb f : valid (f \+ f) = empb f. 
Proof.
case E: (empb f); first by move/empbE: E=>->; rewrite unitL valid_unit. 
case: validUn=>// V _ L; case: validEb E=>//; case; split=>// k.
by case E: (k \in dom f)=>//; move: (L k E); rewrite E. 
Qed.

Lemma empb_um_filt p f : empb f -> empb (um_filter p f).
Proof. 
rewrite !umE /UM.empb /UM.um_filter.
case: (UMC.from f)=>[|f' F] //.
by move/eqP/supp_nilE=>->; rewrite kfilt_nil.
Qed.

End EmpbLemmas.


(****************************)
(* Generic points-to lemmas *)
(****************************)

(* Instances of union_maps have different definition of points-to, so
they need separate intances of each of following lemmas. I give the
lemmas complicated names prefixed by gen, because they are not
supposed to be used in applications *)

Section PointsToLemmas.
Variable U : union_map_class.
Implicit Types (k : keys U) (v : vals U) (f : U).

Lemma gen_ptsU k v : pts k v = upd k v Unit.
Proof. by rewrite !pcmE /= !umE /UM.pts /UM.upd; case: decP. Qed.

Lemma gen_domPt k v : dom (pts k v) =i [pred x | cond k & k == x].
Proof. 
by move=>x; rewrite gen_ptsU domU !inE eq_sym valid_unit dom0; case: eqP.
Qed.

Lemma gen_validPt k v : valid (pts k v) = cond k. 
Proof. by rewrite gen_ptsU validU valid_unit andbT. Qed.

Lemma gen_domeqPt k v1 v2 : dom_eq (pts k v1) (pts k v2). 
Proof. 
by apply/domeqP; rewrite !gen_validPt; split=>// x; rewrite !gen_domPt.
Qed.

Lemma gen_cancelPt k v1 v2 : 
        valid (pts k v1) -> pts k v1 = pts k v2 -> v1 = v2.
Proof. by rewrite gen_validPt !gen_ptsU; apply: upd_inj. Qed.

Lemma gen_updPt k v1 v2 : upd k v1 (pts k v2) = pts k v1.
Proof. by rewrite !gen_ptsU updU eq_refl. Qed.

Lemma gen_empbPt k v : empb (pts k v) = false.
Proof. by rewrite gen_ptsU empbU. Qed.

(* valid *)

Lemma gen_validPtUn k v f :
        valid (pts k v \+ f) = [&& cond k, valid f & k \notin dom f].
Proof. 
case: validUn=>//; last 1 first.
- rewrite gen_validPt=>H1 -> H2; rewrite H1 (H2 k) //.
  by rewrite gen_domPt inE /= eq_refl H1. 
- by rewrite gen_validPt; move/negbTE=>->.
- by move/negbTE=>->; rewrite andbF.
move=>x; rewrite gen_domPt inE /=.
by case/andP=>-> /eqP <- ->; rewrite !andbF.
Qed.

(* the projections from validPtUn are often useful *)

Lemma gen_validPt_cond k v f : valid (pts k v \+ f) -> cond k.
Proof. by rewrite gen_validPtUn; case/and3P. Qed.

Lemma gen_validPtV k v f : valid (pts k v \+ f) -> valid f.
Proof. by rewrite gen_validPtUn; case/and3P. Qed.

Lemma gen_validPtD k v f : valid (pts k v \+ f) -> k \notin dom f.
Proof. by rewrite gen_validPtUn; case/and3P. Qed.

(* dom *)

Lemma gen_domPtUn k v f : 
        dom (pts k v \+ f) =i 
        [pred x | valid (pts k v \+ f) & (k == x) || (x \in dom f)].
Proof. 
move=>x; rewrite domUn !inE !gen_validPtUn gen_domPt !inE.
by rewrite -!andbA; case: (cond k).
Qed.

(* find *) 

Lemma gen_findPtUn k v f : 
        valid (pts k v \+ f) -> find k (pts k v \+ f) = Some v.
Proof.
move=>V; rewrite findUnL // gen_domPt inE /=.
by rewrite gen_ptsU findU eq_refl valid_unit (gen_validPt_cond V).
Qed.

(* free *)

Lemma gen_freePtUn k v f : 
        valid (pts k v \+ f) -> free k (pts k v \+ f) = f.
Proof.
move=>V; rewrite (freeUnR _ (gen_validPtD V)) gen_ptsU freeU eq_refl.
by rewrite (gen_validPt_cond V) free0 unitL.
Qed.

(* upd *)

Lemma gen_updPtUn k v1 v2 f : upd k v1 (pts k v2 \+ f) = pts k v1 \+ f.
Proof.
case V1 : (valid (pts k v2 \+ f)).
- by rewrite updUnL gen_domPt inE eq_refl gen_updPt (gen_validPt_cond V1).
have V2 : valid (pts k v1 \+ f) = false.
- by rewrite !gen_validPtUn in V1 *.
move/negbT/invalidE: V1=>->; move/negbT/invalidE: V2=>->.
by apply: upd_invalid.
Qed.

Lemma gen_eta k f : 
        k \in dom f -> exists v, find k f = Some v /\ f = pts k v \+ free k f.
Proof.
case: dom_find=>// v E1 E2 _; exists v; split=>//.
by rewrite {1}E2 -{1}[free k f]unitL updUnR domF inE /= eq_refl gen_ptsU. 
Qed.

Lemma gen_cancel k v1 v2 f1 f2 : 
        valid (pts k v1 \+ f1) ->
        pts k v1 \+ f1 = pts k v2 \+ f2 -> [/\ v1 = v2, valid f1 & f1 = f2].
Proof.
move=>V E.
have: find k (pts k v1 \+ f1) = find k (pts k v2 \+ f2) by rewrite E.
rewrite !gen_findPtUn -?E //; case=>X.
by rewrite -{}X in E *; rewrite -(joinfK V E) (validR V).
Qed.

Lemma gen_umfiltPt p k v : 
        um_filter p (pts k v) = 
        if p k then pts k v else if cond k then Unit else um_undef.
Proof. by rewrite gen_ptsU um_filtU um_filt0. Qed.

(* induction over union maps, expressed with pts and \+ *)

Lemma gen_ind' (P : U -> Prop) : 
         P um_undef -> P Unit ->
         (forall k v f, P f -> valid (pts k v \+ f) -> P (pts k v \+ f)) ->
         forall f, P f.
Proof.
rewrite !pcmE /= !umE => H1 H2 H3 f; rewrite -[f]UMC.tfE.
apply: (UM.base_ind' (P := (fun b => P (UMC.to b))))=>//.
by move=>k v g; move/(H3 k v); rewrite !pcmE /= !umE.
Qed.

End PointsToLemmas.

(*******************************)
(*******************************)
(* Main instance of union maps *)
(*******************************)
(*******************************)

(* We build it over the base type with a trival condition on keys. We
seal the definition to avoid any slowdowns (just in case). *)

Module Type UMSig.
Parameter tp : ordType -> Type -> Type.

Section Params.
Variables (K : ordType) (V : Type).
Notation tp := (tp K V).

Parameter um_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : K -> V -> tp -> tp.
Parameter dom : tp -> pred K.
Parameter dom_eq : tp -> tp -> bool.
Parameter free : K -> tp -> tp. 
Parameter find : K -> tp -> option V.
Parameter union : tp -> tp -> tp.
Parameter um_filter : pred K -> tp -> tp.
Parameter empb : tp -> bool.
Parameter pts : K -> V -> tp.

Parameter from : tp -> @UM.base K V predT.
Parameter to : @UM.base K V predT -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : um_undef = to (@UM.Undef K V predT). 
Axiom defE : forall f, defined f = UM.valid (from f). 
Axiom emptyE : empty = to (@UM.empty K V predT). 
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)). 
Axiom domE : forall f, dom f = UM.dom (from f). 
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2). 
Axiom freeE : forall k f, free k f = to (UM.free k (from f)). 
Axiom findE : forall k f, find k f = UM.find k (from f). 
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom umfiltE : forall q f, um_filter q f = to (UM.um_filter q (from f)).
Axiom empbE : forall f, empb f = UM.empb (from f). 
Axiom ptsE : forall k v, pts k v = to (@UM.pts K V predT k v).

End Params.

End UMSig.


Module UMDef : UMSig.
Section UMDef.
Variables (K : ordType) (V : Type).

Definition tp : Type := @UM.base K V predT.

Definition um_undef := @UM.Undef K V predT.
Definition defined f := @UM.valid K V predT f.
Definition empty := @UM.empty K V predT.
Definition upd k v f := @UM.upd K V predT k v f.
Definition dom f := @UM.dom K V predT f.
Definition dom_eq f1 f2 := @UM.dom_eq K V predT f1 f2.
Definition free k f := @UM.free K V predT k f.
Definition find k f := @UM.find K V predT k f.
Definition union f1 f2 := @UM.union K V predT f1 f2.
Definition um_filter q f := @UM.um_filter K V predT q f.
Definition empb f := @UM.empb K V predT f.
Definition pts k v := @UM.pts K V predT k v.

Definition from (f : tp) : @UM.base K V predT := f.
Definition to (b : @UM.base K V predT) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : um_undef = to (@UM.Undef K V predT). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty K V predT). Proof. by []. Qed.
Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). Proof. by []. Qed.
Lemma domE f : dom f = UM.dom (from f). Proof. by []. Qed.
Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2). 
Proof. by []. Qed.
Lemma freeE k f : free k f = to (UM.free k (from f)). Proof. by []. Qed.
Lemma findE k f : find k f = UM.find k (from f). Proof. by []. Qed.
Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by []. Qed.
Lemma umfiltE q f : um_filter q f = to (UM.um_filter q (from f)).
Proof. by []. Qed.
Lemma empbE f : empb f = UM.empb (from f). Proof. by []. Qed.
Lemma ptsE k v : pts k v = to (@UM.pts K V predT k v).
Proof. by []. Qed.

End UMDef.
End UMDef.

Notation union_map := UMDef.tp.

Definition unionmapMixin K V := 
  UMCMixin (@UMDef.ftE K V) (@UMDef.tfE K V) (@UMDef.defE K V) 
           (@UMDef.undefE K V) (@UMDef.emptyE K V) (@UMDef.updE K V) 
           (@UMDef.domE K V) (@UMDef.dom_eqE K V) (@UMDef.freeE K V)
           (@UMDef.findE K V) (@UMDef.unionE K V) (@UMDef.umfiltE K V)
           (@UMDef.empbE K V) (@UMDef.ptsE K V).

Canonical union_mapUMC K V := 
  Eval hnf in UMC (union_map K V) (@unionmapMixin K V).

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition union_mapPCMMixin K V := union_map_classPCMMixin (union_mapUMC K V).
Canonical union_mapPCM K V := 
  Eval hnf in PCM (union_map K V) (@union_mapPCMMixin K V).

Definition union_map_eqMixin K (V : eqType) := 
  @union_map_class_eqMixin K V _ _ (unionmapMixin K V).
Canonical union_map_eqType K (V : eqType) := 
  Eval hnf in EqType (union_map K V) (@union_map_eqMixin K V).

Definition um_pts (K : ordType) V (k : K) (v : V) := 
  @UMC.pts (union_mapUMC K V) k v. 

Notation "x \\-> v" := (@um_pts _ _ x v) (at level 30).

(* Finite sets are just union maps with unit range *)
Notation fset T := (@union_map T unit).
Notation "# x" := (x \\-> tt) (at level 20).

(* Does the notation work? *)
Lemma xx : 1 \\-> true = 1 \\-> false.
Abort.

(* does the pcm and the equality type work? *)
Lemma xx : ((1 \\-> true) \+ (2 \\-> false)) == (1 \\-> false).
simpl.
rewrite joinC. 
Abort.

(* can we use the base type? *)
Lemma xx (x : union_map nat_ordType nat) : x \+ x == x \+ x. 
Abort.

(* the default dom' lemmas don't work nicely *)
Lemma xx (f : union_map nat_ordType nat) : 3 \in dom' (free 2 f).
try by rewrite domF' /=.  
rewrite (@domF' (union_mapUMC _ _)).
Abort.

(* but the dom lemmas do work nicely *)
Lemma xx (f : union_map nat_ordType nat) : 3 \in dom (free 2 f).
rewrite domF /=.  
Abort.

(* can i store maps into maps without universe inconsistencies? *)
Lemma xx : 1 \\-> (1 \\-> 3) = 2 \\-> (7 \\-> 3).
Abort.

(*************************************************)
(* Points-to lemmas specific to plain union maps *)
(*************************************************)

Section UMPointsToLemmas.
Variables (K : ordType) (V : Type).
Notation U := (union_mapUMC K V).
Implicit Types (k : K) (v : V) (f : U).

Lemma um_ptsU k v : k \\-> v = upd k v (Unit : U).
Proof. exact: gen_ptsU. Qed.

Lemma um_domPt k v : dom (k \\-> v) =i [pred x | k == x]. 
Proof. exact: gen_domPt. Qed.

Lemma um_validPt k v : valid (k \\-> v) = @cond U k. 
Proof. exact: gen_validPt. Qed.

Lemma um_domeqPt k v1 v2 : dom_eq (k \\-> v1) (k \\-> v2). 
Proof. exact: gen_domeqPt. Qed.

Lemma um_cancelPt k v1 v2 : k \\-> v1 = k \\-> v2 -> v1 = v2.
Proof. by move/gen_cancelPt; rewrite gen_validPt; apply. Qed.

Lemma um_updPt k v1 v2 : upd k v1 (k \\-> v2) = k \\-> v1.
Proof. exact: gen_updPt. Qed.

Lemma um_empbPt k v : empb (k \\-> v) = false.
Proof. exact: gen_empbPt. Qed.

Lemma um_validPtUn k v f : 
       valid (k \\-> v \+ f) = valid f && (k \notin dom f).
Proof. exact: gen_validPtUn. Qed.

Lemma um_validPtV k v f : valid (k \\-> v \+ f) -> valid f.
Proof. exact: gen_validPtV. Qed.

Lemma um_validPtD k v f : valid (k \\-> v \+ f) -> k \notin dom f.
Proof. exact: gen_validPtD. Qed.

Lemma um_domPtUn k v f : 
        dom (k \\-> v \+ f) =i 
        [pred x | valid (k \\-> v \+ f) & (k == x) || (x \in dom f)].
Proof. exact: gen_domPtUn. Qed.

Lemma um_findPtUn k v f : 
        valid (k \\-> v \+ f) -> find k (k \\-> v \+ f) = Some v.
Proof. exact: gen_findPtUn. Qed.

Lemma um_freePtUn k v f : 
        valid (k \\-> v \+ f) -> free k (k \\-> v \+ f) = f.
Proof. exact: gen_freePtUn. Qed.

Lemma um_updPtUn k v1 v2 f : upd k v1 (k \\-> v2 \+ f) = k \\-> v1 \+ f.
Proof. exact: gen_updPtUn. Qed.

Lemma um_eta k f : 
        k \in dom f -> 
        exists v, find k f = Some v /\ f = k \\-> v \+ free k f.
Proof. exact: gen_eta. Qed.

Lemma um_cancel k v1 v2 f1 f2 : 
        valid (k \\-> v1 \+ f1) ->
        k \\-> v1 \+ f1 = k \\-> v2 \+ f2 -> [/\ v1 = v2, valid f1 & f1 = f2].
Proof. exact: gen_cancel. Qed.

Lemma um_umfiltPt p k v : 
        um_filter p (k \\-> v) = if p k then k \\-> v else Unit. 
Proof. exact: gen_umfiltPt. Qed.

Lemma um_ind' (P : U -> Prop) : 
         P um_undef -> P Unit ->
         (forall k v f, P f -> valid (k \\-> v \+ f) -> P (k \\-> v \+ f)) ->
         forall f, P f.
Proof. by move=>H1 H2 H3; apply: gen_ind'. Qed.

End UMPointsToLemmas.



