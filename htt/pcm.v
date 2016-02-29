From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import pred prelude ordtype finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************)
(* Partial Commutative Monoids *)
(*******************************)

Module PCM.

Record mixin_of (T : Type) := Mixin {
    valid_op : T -> bool;
    join_op : T -> T -> T;
    unit_op : T;
    _ : commutative join_op;
    _ : associative join_op;
    _ : left_id unit_op join_op;
    (* monotonicity of valid *)
    _ : forall x y, valid_op (join_op x y) -> valid_op x;
    (* unit is valid *)
    _ : valid_op unit_op}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

Definition valid := valid_op class.
Definition join := join_op class.
Definition unit := unit_op class.

End ClassDef.

Implicit Arguments unit [cT].

Definition morph_axiom (A B : type) (f : sort A -> sort B) :=
  f unit = unit /\ forall x y, f (join x y) = join (f x) (f y).

Module Exports.
Coercion sort : type >-> Sortclass.
Notation pcm := type.
Notation PCMMixin := Mixin.
Notation PCM T m := (@pack T m).

Notation "[ 'pcmMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'pcmMixin'  'of'  T ]") : form_scope.
Notation "[ 'pcm' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'pcm'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'pcm' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'pcm'  'of'  T ]") : form_scope.

Notation "x \+ y" := (join x y) (at level 43, left associativity).
Notation valid := valid.
Notation Unit := unit.

Implicit Arguments unit [cT].
Prenex Implicits join unit.

Section Morphism.
Variables A B : pcm.

Structure pcm_morph_type := PCMMorph {
  pcm_func :> A -> B;
  _ : morph_axiom pcm_func}.

Definition pcm_morph_for of phant (A -> B) := pcm_morph_type.
Identity Coercion type_of_pcm_morph : pcm_morph_for >-> pcm_morph_type.

End Morphism.

Notation "{ 'pcm_morph' fT }" := (pcm_morph_for (Phant fT))
  (at level 0, format "{ 'pcm_morph'  '[hv' fT ']' }") : type_scope.

(* Restating the laws, with the notation. *)
(* Plus some additional derived lemmas.   *)

Section Laws.
Variable U V : pcm.

Lemma joinC (x y : U) : x \+ y = y \+ x.
Proof. by case: U x y=>tp [v j z Cj *]; apply: Cj. Qed.

Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
Proof. by case: U x y z=>tp [v j z Cj Aj *]; apply: Aj. Qed.

Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
Proof. by rewrite -joinA (joinC y) joinA. Qed.

Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
Proof. by rewrite joinA (joinC x) -joinA. Qed.

Lemma validL (x y : U) : valid (x \+ y) -> valid x.
Proof. case: U x y=>tp [v j z Cj Aj Uj /= Mj inv f]; apply: Mj. Qed.

Lemma validR (x y : U) : valid (x \+ y) -> valid y.
Proof. by rewrite joinC; apply: validL. Qed.

Lemma unitL (x : U) : Unit \+ x = x.
Proof. by case: U x=>tp [v j z Cj Aj Uj *]; apply: Uj. Qed.

Lemma unitR (x : U) : x \+ Unit = x.
Proof. by rewrite joinC unitL. Qed.

Lemma valid_unit : valid (@Unit U).
Proof. by case: U=>tp [v j z Cj Aj Uj Vm Vu *]. Qed.

Variable f : {pcm_morph U -> V}.

Lemma fjoin x y : f (x \+ y) = f x \+ f y.
Proof. by case: f=>? []. Qed.

Lemma funit : f Unit = Unit.
Proof. by case: f=>? []. Qed.

End Laws.

Hint Resolve valid_unit.

Section UnfoldingRules.
Variable U : pcm.

Lemma pcm_joinE (x y : U) : x \+ y = join_op (class U) x y.
Proof. by []. Qed.

Lemma pcm_validE (x : U) : valid x = valid_op (class U) x.
Proof. by []. Qed.

Lemma pcm_unitE : unit = unit_op (class U).
Proof. by []. Qed.

Definition pcmE := (pcm_joinE, pcm_validE, pcm_unitE).

End UnfoldingRules.

End Exports.

End PCM.

Export PCM.Exports.

(* definition of precision for an arbitrary PCM U *)

Definition precise (U : pcm) (P : Pred U) :=
  forall s1 s2 t1 t2,
    valid (s1 \+ t1) ->
    s1 \+ t1 = s2 \+ t2 ->
    s1 \In P -> s2 \In P -> s1 = s2.


(****************************************************)
(* Sometimes we want to construct PCM's by lifting. *)
(* We need a structure which by lifting becomes PCM *)
(* This will give us uniform notation for lifting   *)
(****************************************************)

Module Unlifted.

Record mixin_of (T : Type) := Mixin {
  ounit_op : T;
  ojoin_op : T -> T -> option T;
  ojoinC_op : forall x y, ojoin_op x y = ojoin_op y x;
  ojoinA_op : forall x y z,
    obind (ojoin_op x) (ojoin_op y z) = obind (ojoin_op^~ z) (ojoin_op x y);
  ounitL_op : forall x, ojoin_op ounit_op x = Some x}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

Definition ounit := ounit_op class.
Definition ojoin := ojoin_op class.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation unlifted := type.
Notation UnliftedMixin := Mixin.
Notation Unlifted T m := (@pack T m).

Notation "[ 'unliftedMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'unliftedMixin'  'of'  T ]") : form_scope.
Notation "[ 'unlifted' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'unlifted'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'unlifted' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'unlifted'  'of'  T ]") : form_scope.

Notation ounit := ounit.
Notation ojoin := ojoin.

Implicit Arguments ounit [cT].

Lemma ojoinC (U : unlifted) (x y : U) : ojoin x y = ojoin y x.
Proof. by case: U x y=>T [ou oj ojC]. Qed.

Lemma ojoinA (U : unlifted) (x y z : U) :
        obind (ojoin x) (ojoin y z) = obind (@ojoin U^~ z) (ojoin x y).
Proof. by case: U x y z=>T [ou oj ojC ojA]. Qed.

Lemma ounitL (U : unlifted) (x : U) : ojoin ounit x = Some x.
Proof. by case: U x=>T [ou oj ojC ojA ojL]. Qed.

End Exports.

End Unlifted.

Export Unlifted.Exports.

(**************************************************)
(* Lifting turns an unlifted structure into a PCM *)
(**************************************************)

Module Lift.
Section Lift.
Variable A : unlifted.

Structure lift : Type := Undef | Up of A.

Let unit := Up ounit.

Let valid :=
  [fun x : lift => if x is Up _ then true else false].

Let join :=
  [fun x y : lift =>
     if (x, y) is (Up v, Up w) then
       if ojoin v w is Some u then Up u
       else Undef
     else Undef].

Lemma joinC (x y : lift) : join x y = join y x.
Proof. by case: x y=>[|x][|y] //=; rewrite ojoinC. Qed.

Lemma joinA (x y z : lift) : join x (join y z) = join (join x y) z.
Proof.
case: x y z =>[|x][|y][|z] //=; first by case: (ojoin x y).
case E1: (ojoin y z)=>[v1|].
- case E2: (ojoin x y)=>[v2|];
  by move: (ojoinA x y z); rewrite E1 E2 /=; move=>->.
case E2: (ojoin x y)=>[v2|] //.
by move: (ojoinA x y z); rewrite E1 E2 /= =><-.
Qed.

Lemma unitL x : join unit x = x.
Proof. by case: x=>[|x] //=; rewrite ounitL. Qed.

Lemma validL x y : valid (join x y) -> valid x.
Proof. by case: x y=>[|x][|y]. Qed.

Lemma validU : valid unit.
Proof. by []. Qed.

End Lift.
End Lift.

Notation lift A := (@Lift.lift A).
Notation undef := (@Lift.Undef _).
Notation up a := (@Lift.Up _ a).

(* A view for pattern-matching lifted pcm's *)

CoInductive lift_spec A : lift A -> Type :=
| undef_spec : lift_spec undef
| up_spec : forall a : A, lift_spec (up a).

Lemma liftP A (x : lift A) : lift_spec x.
Proof. by case: x=>[|a]; [apply: undef_spec | apply: up_spec]. Qed.

Definition liftPCMMixin A :=
  PCMMixin (@Lift.joinC A) (@Lift.joinA A)
           (@Lift.unitL A) (@Lift.validL A) (@Lift.validU A).
Canonical liftPCM A := Eval hnf in PCM (lift A) (liftPCMMixin A).

(* simplifying up-up expressions *)

Lemma upupE (A : unlifted) (a1 a2 : A) :
        up a1 \+ up a2 =
        if ojoin a1 a2 is Some a then up a else undef.
Proof. by []. Qed.

(* We can prove that lifting preserves equality types *)

Module LiftEqType.
Section LiftEqType.
Variable (A : eqType) (c : Unlifted.mixin_of A).

Let U := (Unlifted A c).

Definition lift_eq (u v : lift U) :=
  match u, v with
    Lift.Up a, Lift.Up b => a == b
  | Lift.Undef, Lift.Undef => true
  | _, _ => false
  end.

Lemma lift_eqP : Equality.axiom lift_eq.
Proof.
case=>[|x][|y] /=; try by constructor.
by apply: (iffP eqP)=>[->|[]].
Qed.

End LiftEqType.
End LiftEqType.

Definition liftEqMixin A c := EqMixin (@LiftEqType.lift_eqP A c).
Canonical liftEqType A c := Eval hnf in EqType _ (@liftEqMixin A c).

(******************************)
(* Now some PCM constructions *)
(******************************)

(* heaps are pcms, albeit large *)
(* remove this line eventually; this is here for legacy *)
(*
Definition old_heapPCMMixin := PCMMixin unC unA un0h defUnl def0.
Canonical old_heapPCM := Eval hnf in PCM heap old_heapPCMMixin.
*)

(* nats with addition are a pcm *)

Definition natPCMMixin :=
  PCMMixin addnC addnA add0n (fun x y => @id true) (erefl _).
Canonical natPCM := Eval hnf in PCM nat natPCMMixin.

(* also with multiplication, but we don't make that one canonical *)

Definition multPCMMixin :=
  PCMMixin mulnC mulnA mul1n (fun x y => @id true) (erefl _).
Definition multPCM := Eval hnf in PCM nat multPCMMixin.

(* with max too *)

Definition maxPCMMixin :=
  PCMMixin maxnC maxnA max0n (fun x y => @id true) (erefl _).
Definition maxPCM := Eval hnf in PCM nat maxPCMMixin.

(* mutexes are an unlifted pcm and an equality type *)

Structure mutex := own | nown.

Module MutexUnlift.

Definition mutex_eq x y :=
  match x, y with
    own, own => true
  | nown, nown => true
  | _, _ => false
  end.

Lemma mutex_eqP : Equality.axiom mutex_eq.
Proof. by case; case; constructor. Qed.

Definition ojoin x y :=
  match x, y with
    own, nown => Some own
  | nown, own => Some own
  | nown, nown => Some nown
  | _, _ => None
  end.

Let ounit := nown.

Lemma ojoinC x y : ojoin x y = ojoin y x.
Proof. by case: x; case: y. Qed.

Lemma ojoinA x y z :
        obind (ojoin x) (ojoin y z) = obind (ojoin^~ z) (ojoin x y).
Proof. by case: x; case: y; case: z. Qed.

Lemma ounitL x : ojoin ounit x = Some x.
Proof. by case: x. Qed.

End MutexUnlift.

Definition mutexEqMixin := EqMixin MutexUnlift.mutex_eqP.
Canonical mutexEqType := Eval hnf in EqType mutex mutexEqMixin.

Definition mutexUnliftedMixin :=
  UnliftedMixin MutexUnlift.ojoinC MutexUnlift.ojoinA MutexUnlift.ounitL.
Canonical mutexUnlifted := Eval hnf in Unlifted mutex mutexUnliftedMixin.

(* some lemmas for mutexes *)

Lemma mtx00E m1 m2 : m1 \+ m2 = up nown -> m1 = up nown /\ m2 = up nown.
Proof. by case: (liftP m1)=>//; case: (liftP m2)=>//; case; case. Qed.

(* pairs of pcms are a pcm *)

Module ProdPCM.
Section ProdPCM.
Variables (U V : pcm).
Local Notation tp := (U * V)%type.

Definition pvalid := [fun x : tp => valid x.1 && valid x.2].
Definition pjoin := [fun x1 x2 : tp => (x1.1 \+ x2.1, x1.2 \+ x2.2)].
Definition punit : tp := (Unit, Unit).

Lemma joinC x y : pjoin x y = pjoin y x.
Proof.
move: x y => [x1 x2][y1 y2] /=.
by rewrite (joinC x1) (joinC x2).
Qed.

Lemma joinA x y z : pjoin x (pjoin y z) = pjoin (pjoin x y) z.
Proof.
move: x y z => [x1 x2][y1 y2][z1 z2] /=.
by rewrite (joinA x1) (joinA x2).
Qed.

Lemma validL x y : pvalid (pjoin x y) -> pvalid x.
Proof.
move: x y => [x1 x2][y1 y2] /=.
by case/andP=>D1 D2; rewrite (validL D1) (validL D2).
Qed.

Lemma unitL x : pjoin punit x = x.
Proof. by case: x=>x1 x2; rewrite /= !unitL. Qed.

Lemma validU : pvalid punit.
Proof. by rewrite /pvalid /= !valid_unit. Qed.

End ProdPCM.
End ProdPCM.

Definition prodPCMMixin U V :=
  PCMMixin (@ProdPCM.joinC U V) (@ProdPCM.joinA U V)
           (@ProdPCM.unitL U V) (@ProdPCM.validL U V) (@ProdPCM.validU U V).
Canonical prodPCM U V := Eval hnf in PCM (_ * _) (@prodPCMMixin U V).

(* unit is a pcm; just for kicks *)

Module UnitPCM.
Section UnitPCM.

Definition uvalid (x : unit) := true.
Definition ujoin (x y : unit) := tt.
Definition uunit := tt.

Lemma ujoinC x y : ujoin x y = ujoin y x.
Proof. by []. Qed.

Lemma ujoinA x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by []. Qed.

Lemma uvalidL x y : uvalid (ujoin x y) -> uvalid x.
Proof. by []. Qed.

Lemma uunitL x : ujoin uunit x = x.
Proof. by case: x. Qed.

Lemma uvalidU : uvalid uunit.
Proof. by []. Qed.

End UnitPCM.
End UnitPCM.

Definition unitPCMMixin :=
  PCMMixin UnitPCM.ujoinC UnitPCM.ujoinA
           UnitPCM.uunitL UnitPCM.uvalidL UnitPCM.uvalidU.
Canonical unitPCM := Eval hnf in PCM unit unitPCMMixin.

(* bools with conjunction are a pcm *)

Module BoolConjPCM.
Lemma unitL x : true && x = x. Proof. by []. Qed.
End BoolConjPCM.

Definition boolPCMMixin := PCMMixin andbC andbA BoolConjPCM.unitL
                           (fun x y => @id true) (erefl _).
Canonical boolConjPCM := Eval hnf in PCM bool boolPCMMixin.

(* finite maps with disjoint union are a pcm *)

Module FinMapPCM.
Section FinMapPCM.
Variables (K : ordType) (V : Type).

Structure finmap := Undef | Def of {finMap K -> V}.

Definition valid (f : finmap) :=
  if f is Def _ then true else false.

Definition join (f1 f2 : finmap) :=
  if (f1, f2) is (Def m1, Def m2) then
    if disj m1 m2 then Def (fcat m1 m2)
    else Undef
  else Undef.

Definition unit := Def (@nil K V).

Lemma joinC f1 f2 : join f1 f2 = join f2 f1.
Proof.
case: f1 f2=>[|m1][|m2] //; rewrite /join.
by case: ifP=>E; rewrite disjC E // fcatC.
Qed.

Lemma joinCA f1 f2 f3 : join f1 (join f2 f3) = join f2 (join f1 f3).
Proof.
case: f1 f2 f3=>[|m1][|m2][|m3] //.
rewrite /join; case E1: (disj m2 m3); last first.
- by case E2: (disj m1 m3)=>//; rewrite disj_fcat E1 andbF.
rewrite disj_fcat andbC.
case E2: (disj m1 m3)=>//; rewrite disj_fcat (disjC m2) E1 /= andbT.
by case E3: (disj m1 m2)=>//; rewrite fcatAC // E1 E2 E3.
Qed.

Lemma joinA f1 f2 f3 : join f1 (join f2 f3) = join (join f1 f2) f3.
Proof. by rewrite (joinC f2) joinCA joinC. Qed.

Lemma validL f1 f2 : valid (join f1 f2) -> valid f1.
Proof. by case: f1. Qed.

Lemma unitL f : join unit f = f.
Proof. by case: f=>[//|m]; rewrite /join/unit disjC disj_nil fcat0s. Qed.

Lemma validU : valid unit.
Proof. by []. Qed.

End FinMapPCM.

Module Exports.
Notation finmap := finmap.

Section Exports.
Variables (K : ordType) (V : Type).

Definition finmapPCMMixin :=
  PCMMixin (@joinC K V) (@joinA K V) (@unitL K V) (@validL K V) (@validU K V).
Canonical finmapPCM := Eval hnf in PCM (finmap K V) finmapPCMMixin.

End Exports.
End Exports.
End FinMapPCM.

Export FinMapPCM.Exports.



