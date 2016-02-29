From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path div.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*************)
(* Locations *)
(*************)

Inductive ptr := ptr_nat of nat.

Definition null := ptr_nat 0.

Definition nat_ptr (x : ptr) := let: ptr_nat y := x in y.

Definition eq_ptr (x y : ptr) : bool :=
  match x, y with ptr_nat m, ptr_nat n => m == n end.

Lemma eq_ptrP : Equality.axiom eq_ptr.
Proof. by case=>x [y] /=; case: eqP=>[->|*]; constructor=>//; case. Qed.

Definition ptr_eqMixin := EqMixin eq_ptrP.
Canonical ptr_eqType := EqType ptr ptr_eqMixin.

(* some pointer arithmetic: offsetting from a base *)

Definition ptr_offset x i := ptr_nat (nat_ptr x + i).

Notation "x .+ i" := (ptr_offset x i)
  (at level 3, format "x .+ i").

Lemma ptrE x y : (x == y) = (nat_ptr x == nat_ptr y).
Proof. by move: x y=>[x][y]. Qed.

Lemma ptr0 x : x.+0 = x.
Proof. by case: x=>x; rewrite /ptr_offset addn0. Qed.

Lemma ptrA x i j : x.+i.+j = x.+(i+j).
Proof. by case: x=>x; rewrite /ptr_offset addnA. Qed.

Lemma ptrK x i j : (x.+i == x.+j) = (i == j).
Proof. by case: x=>x; rewrite ptrE eqn_add2l. Qed.

Lemma ptr_null x m : (x.+m == null) = (x == null) && (m == 0).
Proof. by case: x=>x; rewrite !ptrE addn_eq0. Qed.

Lemma ptrT x y : {m : nat | (x == y.+m) || (y == x.+m)}.
Proof.
case: x y=>x [y]; exists (if x <= y then (y - x) else (x - y)).
rewrite !ptrE leq_eqVlt /=.
by case: (ltngtP x y)=>/= E; rewrite subnKC ?(ltnW E) ?eq_refl ?orbT // E.
Qed.

Definition ltn_ptr (x y : ptr) :=
  match x, y with ptr_nat m, ptr_nat n => m < n end.

Lemma ltn_ptr_irr : irreflexive ltn_ptr.
Proof. by case=>x /=; rewrite ltnn. Qed.

Lemma ltn_ptr_trans : transitive ltn_ptr.
Proof. by case=>x [y][z]; apply: ltn_trans. Qed.

Lemma ltn_ptr_total : forall x y : ptr, [|| ltn_ptr x y, x == y | ltn_ptr y x].
Proof. by case=>x [y]; rewrite ptrE /=; case: ltngtP. Qed.

Definition ptr_ordMixin := OrdMixin ltn_ptr_irr ltn_ptr_trans ltn_ptr_total.
Canonical ptr_ordType := OrdType ptr ptr_ordMixin.

(*********)
(* Heaps *)
(*********)

Module Heap.

Local Notation idyn v := (@idyn _ id _ v).

Inductive heap :=
  Undef | Def (finmap : {finMap ptr -> idynamic id}) of
               null \notin supp finmap.

Section NullLemmas.
Variables (f g : {finMap ptr -> idynamic id}) (x : ptr) (v : idynamic id).

Lemma upd_nullP :
        x != null -> null \notin supp f -> null \notin supp (ins x v f).
Proof. by move=>H1 H2; rewrite supp_ins negb_or /= inE /= eq_sym H1. Qed.

Lemma free_nullP : null \notin supp f -> null \notin supp (rem x f).
Proof. by move=>H; rewrite supp_rem negb_and /= H orbT. Qed.

Lemma un_nullP :
        null \notin supp f -> null \notin supp g ->
          null \notin supp (fcat f g).
Proof. by move=>H1 H2; rewrite supp_fcat negb_or H1 H2. Qed.

Lemma filt_nullP (q : pred ptr) :
        null \notin supp f -> null \notin supp (kfilter q f).
Proof. by move=>H; rewrite supp_kfilt mem_filter negb_and H orbT. Qed.

Lemma heap_base : null \notin supp f -> all (fun k => k != null) (supp f).
Proof. by move=>H; apply/allP=>k; case: eqP H=>// -> /negbTE ->. Qed.

Lemma base_heap : all (fun k => k != null) (supp f) -> null \notin supp f.
Proof. by move/allP=>H; apply: (introN idP); move/H. Qed.

Lemma heapE (h1 h2 : heap) :
        h1 = h2 <->
        match h1, h2 with
          Def f' pf, Def g' pg => f' = g'
        | Undef, Undef => true
        | _, _ => false
        end.
Proof.
split; first by move=>->; case: h2.
case: h1; case: h2=>// f1 pf1 f2 pf2 E.
move: pf2; rewrite {f2}E in pf1 *; move=>pf2.
by congr Def; apply: bool_irrelevance.
Qed.

End NullLemmas.


(* methods *)

Definition def h := if h is Def _ _ then true else false.

Definition empty := @Def (finmap.nil _ _) is_true_true.

Definition upd k v h :=
  if h is Def hs ns then
    if decP (@idP (k != null)) is left pf then
      Def (@upd_nullP _ _ v pf ns)
    else Undef
  else Undef.

Definition dom h : pred ptr :=
  if h is Def f _ then [fun x => x \in supp f] else pred0.

Definition dom_eq h1 h2 :=
  (def h1 == def h2) &&
  match h1, h2 with
    Def f1 _, Def f2 _ => supp f1 == supp f2
  | Undef, Undef => true
  | _, _ => false
  end.

Definition free x h :=
  if h is Def hs ns then Def (free_nullP x ns) else Undef.

Definition find (x : ptr) h :=
  if h is Def hs _ then fnd x hs else None.

Definition union h1 h2 :=
  if (h1, h2) is (Def hs1 ns1, Def hs2 ns2) then
    if disj hs1 hs2 then
       Def (@un_nullP _ _ ns1 ns2)
    else Undef
  else Undef.

Definition um_filter q f :=
  if f is Def fs pf then Def (@filt_nullP fs q pf) else Undef.

Definition pts (x : ptr) v := upd x v empty.

Definition empb h :=
  if h is Def hs _ then supp hs == [::] else false.

Definition keys_of h : seq ptr :=
  if h is Def f _ then supp f else [::].

Local Notation base :=
  (@UM.base ptr_ordType (idynamic id) (fun k => k != null)).

Definition from (f : heap) : base :=
  if f is Def hs ns then UM.Def (heap_base ns) else UM.Undef _ _.

Definition to (b : base) : heap :=
  if b is UM.Def hs ns then Def (base_heap ns) else Undef.

Lemma ftE b : from (to b) = b.
Proof. by case: b=>// f H; rewrite UM.umapE. Qed.

Lemma tfE f : to (from f) = f.
Proof. by case: f=>// f H; rewrite heapE. Qed.

Lemma undefE : Undef = to (@UM.Undef _ _ _).
Proof. by []. Qed.

Lemma defE f : def f = UM.valid (from f).
Proof. by case: f. Qed.

Lemma emptyE : empty = to (@UM.empty _ _ _).
Proof. by rewrite heapE. Qed.

Lemma updE k v f : upd k v f = to (UM.upd k v (from f)).
Proof. by case: f=>[|f H] //=; case: decP=>// H1; rewrite heapE. Qed.

Lemma domE f : dom f = UM.dom (from f).
Proof. by case: f. Qed.

Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by case: f1 f2=>[|f1 H1][|f2 H2]. Qed.

Lemma freeE k f : free k f = to (UM.free k (from f)).
Proof. by case: f=>[|f H] //; rewrite heapE. Qed.

Lemma findE k f : find k f = UM.find k (from f).
Proof. by case: f. Qed.

Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof.
case: f1 f2=>[|f1 H1][|f2 H2] //; rewrite /union /UM.union /=.
by case: ifP=>D //; rewrite heapE.
Qed.

Lemma umfiltE q f : um_filter q f = to (UM.um_filter q (from f)).
Proof. by case: f=>[|f H] //; rewrite heapE. Qed.

Lemma empbE f : empb f = UM.empb (from f).
Proof. by case: f. Qed.

Lemma ptsE k (v : idynamic id) : pts k v = to (@UM.pts _ _ _ k v).
Proof.
by rewrite /pts /UM.pts /UM.upd /=; case: decP=>// H; rewrite heapE.
Qed.

Lemma keys_ofE f : keys_of f = UM.keys_of (from f).
Proof. by case: f. Qed.

Module Exports.

(* the inheritance from PCMs *)

Definition heapUMCMixin :=
  UMCMixin ftE tfE defE undefE emptyE updE domE dom_eqE freeE
           findE unionE umfiltE empbE ptsE keys_ofE.
Canonical heapUMC := Eval hnf in UMC heap heapUMCMixin.

(* Can I get heap's own PCM? *)

Definition heapPCMMixin := union_map_classPCMMixin heapUMC.
Canonical heapPCM := Eval hnf in PCM heap heapPCMMixin.

End Exports.

End Heap.

Export Heap.Exports.

Notation heap := Heap.heap.

Definition heap_pts A (x : ptr) (v : A) :=
  @UMC.pts _ _ heapUMC x (@idyn _ id _ v).

(*
Notation "x :-> v" := (@heap_pts _ x v) (at level 30).
*)

(*
Notation "x :-> v" := (@UMC.pts heapUMC x (idyn v)) (at level 30).
*)

(* The above notation is not getting printed *)
(* I think something is overriding it; possibly *)
(* that it's head is the same as in other notations *)
(* namely, UMC.pts, and it's only types that differentiate *)
(* which notation should be printed *)

(* if I introduce an explicit definition to override any other *)
(* conflicting notation, it is printed *)
Notation "x :-> v" := (@heap_pts _ x v) (at level 30).

(*****************************)
(* Specific points-to lemmas *)
(*****************************)

Section HeapPointsToLemmas.
Implicit Types (x : ptr) (h : heap).
(* A: upd requires explicit annotation; change that *)
(* why is notation not being displayed? *)
Local Notation idyn v := (@idyn _ id _ v).

Lemma hptsU A x (v : A) : x :-> v = upd x (idyn v) (Unit : heap).
Proof. exact: gen_ptsU. Qed.

Lemma hdomPt A x (v : A) : dom (x :-> v) =i [pred y | x != null & x == y].
Proof. exact: gen_domPt. Qed.

Lemma hvalidPt A x (v : A) : valid (x :-> v) = (x != null).
Proof. exact: gen_validPt. Qed.

Lemma hfindPt A x (v : A) :
        find x (x :-> v) = if x != null then Some (idyn v) else None.
Proof. exact: gen_findPt. Qed.

Lemma hfindPt2 A x1 x2 (v : A) :
        find x1 (x2 :-> v) =
        if (x1 == x2) && (x2 != null) then Some (idyn v) else None.
Proof. exact: gen_findPt2. Qed.

Lemma hfreePt A x (v : A) : x != null -> free x (x :-> v) = Unit.
Proof. by move=>N; apply: gen_freePt. Qed.

Lemma hfreePt2 A x1 x2 (v : A) :
        x2 != null ->
        free x1 (x2 :-> v) = if x1 == x2 then Unit else x2 :-> v.
Proof. by move=>N; apply: gen_freePt2. Qed.

Lemma hdomeqPt A1 A2 x (v1 : A1) (v2 : A2) :
        dom_eq (x :-> v1) (x :-> v2).
Proof. exact: gen_domeqPt. Qed.

Lemma hcancelPt A1 A2 x (v1 : A1) (v2 : A2) :
        valid (x :-> v1) -> x :-> v1 = x :-> v2 -> idyn v1 = idyn v2.
Proof. exact: gen_cancelPt. Qed.

Lemma hcancelPtT A1 A2 x (v1 : A1) (v2 : A2) :
        valid (x :-> v1) -> x :-> v1 = x :-> v2 -> A1 = A2.
Proof. by move=>V; move/(hcancelPt V); move/idyn_injT. Qed.

Lemma hcancelPtV A x (v1 v2 : A) :
        valid (x :-> v1) -> x :-> v1 = x :-> v2 -> v1 = v2.
Proof. by move=>V; move/(hcancelPt V)/idyn_inj. Qed.

Lemma hupdPt A1 A2 x (v1 : A1) (v2 : A2) :
        upd x (idyn v1) (x :-> v2) = x :-> v1.
Proof. exact: gen_updPt. Qed.

Lemma hempbPt A x (v : A) : empb (x :-> v) = false.
Proof. exact: gen_empbPt. Qed.

(* valid *)

Lemma hvalidPtUn A x (v : A) h :
        valid (x :-> v \+ h) = [&& x != null, valid h & x \notin dom h].
Proof. exact: gen_validPtUn. Qed.

Lemma hvalidPt_cond A x (v : A) h : valid (x :-> v \+ h) -> x != null.
Proof. exact: gen_validPt_cond. Qed.

Lemma hvalidPtV A x (v : A) h : valid (x :-> v \+ h) -> valid h.
Proof. exact: gen_validPtV. Qed.

Lemma hvalidPtD A x (v : A) h : valid (x :-> v \+ h) -> x \notin dom h.
Proof. exact: gen_validPtD. Qed.

Prenex Implicits hvalidPtD.

(* dom *)

Lemma hdomPtUn A x (v : A) h :
        dom (x :-> v \+ h) =i
        [pred y | valid (x :-> v \+ h) & (x == y) || (y \in dom h)].
Proof. exact: gen_domPtUn. Qed.

(* find *)

Lemma hfindPtUn A x (v : A) h :
        valid (x :-> v \+ h) -> find x (x :-> v \+ h) = Some (idyn v).
Proof. exact: gen_findPtUn. Qed.

Lemma hfindPtUn2 A x1 x2 (v : A) h :
        valid (x2 :-> v \+ h) ->
        find x1 (x2 :-> v \+ h) = if x1 == x2 then Some (idyn v) else find x1 h.
Proof. exact: gen_findPtUn2. Qed.

(* free *)

Lemma hfreePtUn A x (v : A) h :
        valid (x :-> v \+ h) -> free x (x :-> v \+ h) = h.
Proof. exact: gen_freePtUn. Qed.

Lemma hfreePtUn2 A x1 x2 (v : A) h :
        valid (x2 :-> v \+ h) ->
        free x1 (x2 :-> v \+ h) = if x1 == x2 then h else x2 :-> v \+ free x1 h.
Proof. exact: gen_freePtUn2. Qed.

(* upd *)

Lemma hupdPtUn A1 A2 x (v1 : A1) (v2 : A2) h :
        upd x (idyn v1) (x :-> v2 \+ h) = x :-> v1 \+ h.
Proof. exact: gen_updPtUn. Qed.

Lemma heap_eta x h :
        x \in dom h -> exists A (v : A),
        find x h = Some (idyn v) /\ h = x :-> v \+ free x h.
Proof. by case/gen_eta; case=>A v H; exists A, v. Qed.

(* to get rid of pesky idyn *)
Lemma heap_eta2 A x h (v : A) :
        find x h = Some (idyn v) -> h = x :-> v \+ free x h.
Proof.
move=>E; case: (heap_eta (find_some E))=>B [w][].
rewrite {}E; case=>E; rewrite -E in w *.
by move/(@inj_pair2 _ _ _ _ _)=>->.
Qed.

Lemma hcancel A1 A2 x (v1 : A1) (v2 : A2) h1 h2 :
        valid (x :-> v1 \+ h1) ->
        x :-> v1 \+ h1 = x :-> v2 \+ h2 ->
       [/\ idyn v1 = idyn v2, valid h1 & h1 = h2].
Proof. exact: gen_cancel. Qed.

Lemma hcancelT A1 A2 x (v1 : A1) (v2 : A2) h1 h2 :
        valid (x :-> v1 \+ h1) ->
        x :-> v1 \+ h1 = x :-> v2 \+ h2 -> A1 = A2.
Proof. by move=>V; case/(hcancel V); move/idyn_injT. Qed.

Lemma hcancelV A x (v1 v2 : A) h1 h2 :
        valid (x :-> v1 \+ h1) ->
        x :-> v1 \+ h1 = x :-> v2 \+ h2 -> [/\ v1 = v2, valid h1 & h1 = h2].
Proof. by move=>V; case/(hcancel V); move/idyn_inj. Qed.

Lemma hcancel2 A1 A2 x1 x2 (v1 : A1) (v2 : A2) h1 h2 :
        valid (x1 :-> v1 \+ h1) ->
        x1 :-> v1 \+ h1 = x2 :-> v2 \+ h2 ->
        if x1 == x2 then idyn v1 = idyn v2 /\ h1 = h2
        else [/\ free x1 h2 = free x2 h1,
                 h1 = x2 :-> v2 \+ free x1 h2 &
                 h2 = x1 :-> v1 \+ free x2 h1].
Proof. exact: gen_cancel2. Qed.

Lemma hcancel2V A x1 x2 (v1 v2 : A) h1 h2 :
        valid (x1 :-> v1 \+ h1) ->
        x1 :-> v1 \+ h1 = x2 :-> v2 \+ h2 ->
        if x1 == x2 then v1 = v2 /\ h1 = h2
        else [/\ free x1 h2 = free x2 h1,
                 h1 = x2 :-> v2 \+ free x1 h2 &
                 h2 = x1 :-> v1 \+ free x2 h1].
Proof. by move=>V /(gen_cancel2 V); case: ifP=>// _ [/idyn_inj]. Qed.

Lemma humfiltPt A p x (v : A) :
        um_filter p (x :-> v) =
        if p x then x :-> v else if x != null then Unit else um_undef.
Proof. exact: gen_umfiltPt. Qed.

End HeapPointsToLemmas.

Prenex Implicits hvalidPt_cond heap_eta2.

(******************************************)
(* additional stuff, on top of union maps *)
(* mostly random stuff, kept for legacy   *)
(* should be removed/redone eventually    *)
(******************************************)

Definition fresh (h : heap) :=
  (if h is Heap.Def hs _ then last null (supp hs) else null) .+ 1.

Definition pick (h : heap) :=
  if h is Heap.Def hs _ then head null (supp hs) else null.

(*********)
(* fresh *)
(*********)

Lemma path_last n s x : path ord x s -> ord x (last x s).+(n+1).
Proof.
move: n s x.
suff L: forall s x, path ord x s -> ord x (last x s).+(1).
- elim=>[|n IH] // s x; move/IH=>E; apply: trans E _.
  by case: (last x s)=>m; rewrite /ord /= addSn (addnS m).
elim=>[|y s IH x] /=; first by case=>x; rewrite /ord /= addn1.
by case/andP=>H1; move/IH; apply: trans H1.
Qed.

Lemma path_filter (A : ordType) (s : seq A) (p : pred A) x :
        path ord x s -> path ord x (filter p s).
Proof.
elim: s x=>[|y s IH] x //=.
case/andP=>H1 H2.
case: ifP=>E; first by rewrite /= H1 IH.
apply: IH; elim: s H2=>[|z s IH] //=.
by case/andP=>H2 H3; rewrite (@trans _ y).
Qed.

Lemma dom_fresh h n : (fresh h).+n \notin dom h.
Proof.
suff L2: forall h x, x \in dom h -> ord x (fresh h).
- by apply: (contra (L2 _ _)); rewrite -leqNgt leq_addr.
case=>[|[s H1]] //; rewrite /supp => /= H2 x.
rewrite /dom /fresh /supp -topredE /=.
elim: s H1 null H2 x=>[|[y d] s IH] //= H1 x.
rewrite inE negb_or; case/andP=>H3 H4 z; rewrite inE.
case/orP; first by move/eqP=>->{z}; apply: (path_last 0).
by apply: IH; [apply: path_sorted H1 | apply: notin_path H1].
Qed.

Lemma fresh_null h : fresh h != null.
Proof. by rewrite -lt0n addn1. Qed.

Opaque fresh.

Hint Resolve dom_fresh fresh_null.

(********)
(* pick *)
(********)

Lemma emp_pick (h : heap) : (pick h == null) = (~~ valid h || empb h).
Proof.
rewrite /empb; case: h=>[|h] //=; case: (supp h)=>[|x xs] //=.
by rewrite inE negb_or eq_sym; case/andP; move/negbTE=>->.
Qed.

Lemma pickP h : valid h && ~~ empb h = (pick h \in dom h).
Proof.
rewrite /dom /empb; case: h=>[|h] //=.
by case: (supp h)=>// *; rewrite inE eq_refl.
Qed.


(***********************)
(* Some derived lemmas *)
(***********************)

Lemma domPtUnX A (v : A) x i : valid (x :-> v \+ i) -> x \in dom (x :-> v \+ i).
Proof. by move=>D; rewrite hdomPtUn inE /= D eq_refl. Qed.

Lemma domPtX A (v : A) x : valid (x :-> v) -> x \in dom (x :-> v).
Proof. by move=>D; rewrite -(unitR (x :-> v)) domPtUnX // unitR. Qed.

Lemma dom_notin_notin (h1 h2 : heap) x :
        valid (h1 \+ h2) -> x \notin dom (h1 \+ h2) -> x \notin dom h1.
Proof. by move=>D; rewrite domUn inE /= negb_and negb_or /= D; case/andP. Qed.

Lemma dom_in_notin (h1 h2 : heap) x :
       valid (h1 \+ h2) -> x \in dom h1 -> x \notin dom h2.
Proof. by case: validUn=>// D1 D2 H _; apply: H. Qed.


(*******************************************)
(* Block update for reasoning about arrays *)
(*******************************************)

Section BlockUpdate.
Variable (A : Type).

Fixpoint updi x (vs : seq A) {struct vs} : heap :=
  if vs is v'::vs' then x :-> v' \+ updi (x .+ 1) vs' else Unit.

Lemma updiS x v vs : updi x (v :: vs) = x :-> v \+ updi (x .+ 1) vs.
Proof. by []. Qed.

Lemma updi_last x v vs :
        updi x (rcons vs v) = updi x vs \+ x.+(size vs) :-> v.
Proof.
elim: vs x v=>[|w vs IH] x v /=.
- by rewrite ptr0 unitR unitL.
by rewrite -(addn1 (size vs)) addnC -ptrA IH joinA.
Qed.

Lemma updi_cat x vs1 vs2 :
        updi x (vs1 ++ vs2) = updi x vs1 \+ updi x.+(size vs1) vs2.
Proof.
elim: vs1 x vs2=>[|v vs1 IH] x vs2 /=.
- by rewrite ptr0 unitL.
by rewrite -(addn1 (size vs1)) addnC -ptrA IH joinA.
Qed.

Lemma updi_catI x y vs1 vs2 :
        y = x.+(size vs1) -> updi x vs1 \+ updi y vs2 = updi x (vs1 ++ vs2).
Proof. by move=>->; rewrite updi_cat. Qed.

(* helper lemma *)
Lemma updiVm' x m xs : m > 0 -> x \notin dom (updi x.+m xs).
Proof.
elim: xs x m=>[|v vs IH] x m //= H.
rewrite ptrA hdomPtUn inE /= negb_and negb_or -{4}(ptr0 x) ptrK -lt0n H /=.
by rewrite orbC IH // addn1.
Qed.

Lemma updiD x xs : valid (updi x xs) = (x != null) || (size xs == 0).
Proof.
elim: xs x=>[|v xs IH] x //=; first by rewrite orbC.
by rewrite hvalidPtUn updiVm' // orbF IH ptr_null andbF andbC.
Qed.

Lemma updiVm x m xs :
        x \in dom (updi x.+m xs) = [&& x != null, m == 0 & size xs > 0].
Proof.
case: m=>[|m] /=; last first.
- by rewrite andbF; apply: negbTE; apply: updiVm'.
case: xs=>[|v xs]; rewrite ptr0 ?andbF ?andbT //=.
by rewrite hdomPtUn inE /= eq_refl -updiS updiD orbF andbT /=.
Qed.

Lemma updimV x m xs :
        x.+m \in dom (updi x xs) = (x != null) && (m < size xs).
Proof.
case H: (x == null)=>/=.
- by case: xs=>// a s; rewrite (eqP H).
elim: xs x m H=>[|v vs IH] x m H //; case: m=>[|m].
- by rewrite ptr0 /= hdomPtUn inE /= eq_refl andbT -updiS updiD H.
rewrite -addn1 addnC -ptrA updiS hdomPtUn inE /= IH; last first.
- by rewrite ptrE /= addn1.
by rewrite -updiS updiD H /= -{1}(ptr0 x) ptrA ptrK.
Qed.

Lemma updiP x y xs :
        reflect (y != null /\ exists m, x = y.+m /\ m < size xs)
                (x \in dom (updi y xs)).
Proof.
case H: (y == null)=>/=.
- by rewrite (eqP H); elim: xs=>[|z xs IH] //=; constructor; case.
case E: (x \in _); constructor; last first.
- by move=>[_][m][H1] H2; rewrite H1 updimV H2 H in E.
case: (ptrT x y) E=>m; case/orP; move/eqP=>->.
- by rewrite updimV H /= => H1; split=>//; exists m.
rewrite updiVm; case/and3P=>H1; move/eqP=>-> H2.
by split=>//; exists 0; rewrite ptrA addn0 ptr0.
Qed.

(* Invertibility *)
Lemma updi_inv x xs1 xs2 :
        valid (updi x xs1) -> updi x xs1 = updi x xs2 -> xs1 = xs2.
Proof.
elim: xs1 x xs2 =>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= D;
[move/esym| | ]; try by rewrite empbE empbUn hempbPt.
by case/(hcancelV D)=><- {D} D; move/(IH _ _ D)=><-.
Qed.

Lemma updi_iinv x xs1 xs2 h1 h2 :
        size xs1 = size xs2 -> valid (updi x xs1 \+ h1) ->
        updi x xs1 \+ h1 = updi x xs2 \+ h2 -> xs1 = xs2 /\ h1 = h2.
Proof.
elim: xs1 x xs2 h1 h2=>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= h1 h2.
- by rewrite !unitL.
move=>[E]; rewrite -!joinA=>D; case/(hcancelV D)=><- {D} D.
by case/(IH _ _ _ _ E D)=>->->.
Qed.

End BlockUpdate.

(*************************************)
(* the automation of the PtUn lemmas *)
(*************************************)

(* First, the mechanism for search-and-replace for the overloaded lemas, *)
(* pattern-matching on heap expressions.                                 *)

Structure tagged_heap := Tag {untag :> heap}.

Definition right_tag := Tag.
Definition left_tag := right_tag.
Canonical found_tag i := left_tag i.

Definition partition_axiom k r (h : tagged_heap) := untag h = k \+ r.

Structure partition (k r : heap) :=
  Partition {heap_of :> tagged_heap;
             _ : partition_axiom k r heap_of}.

Lemma partitionE r k (f : partition k r) : untag f = k \+ r.
Proof. by case: f=>[[j]] /=; rewrite /partition_axiom /= => ->. Qed.

Lemma found_pf k : partition_axiom k Unit (found_tag k).
Proof. by rewrite /partition_axiom unitR. Qed.

Canonical found_struct k := Partition (found_pf k).

Lemma left_pf h r (f : forall k, partition k r) k :
        partition_axiom k (r \+ h) (left_tag (untag (f k) \+ h)).
Proof. by rewrite partitionE /partition_axiom /= joinA. Qed.

Canonical left_struct h r (f : forall k, partition k r) k :=
  Partition (left_pf h f k).

Lemma right_pf h r (f : forall k, partition k r) k :
        partition_axiom k (h \+ r) (right_tag (h \+ f k)).
Proof. by rewrite partitionE /partition_axiom /= joinCA. Qed.

Canonical right_struct h r (f : forall k, partition k r) k :=
  Partition (right_pf h f k).

(* now the actual lemmas *)

Lemma defPtUnO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) = [&& x != null, valid h & x \notin dom h].
Proof. by rewrite partitionE hvalidPtUn. Qed.

Implicit Arguments defPtUnO [A h v f].

Lemma defPt_nullO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> x != null.
Proof. by rewrite partitionE; apply: hvalidPt_cond. Qed.

Implicit Arguments defPt_nullO [A h x v f].

Lemma defPt_defO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> valid h.
Proof. by rewrite partitionE; apply: hvalidPtV. Qed.

Implicit Arguments defPt_defO [A h v f].

Lemma defPt_domO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> x \notin dom h.
Proof. by rewrite partitionE; apply: hvalidPtD. Qed.

Implicit Arguments defPt_domO [A h v f].

Lemma domPtUnO A h x (v : A) (f : partition (x :-> v) h) :
        dom (untag f) =i
        [pred y | valid (untag f) & (x == y) || (y \in dom h)].
Proof. by rewrite partitionE; apply: hdomPtUn. Qed.

Implicit Arguments domPtUnO [A h v f].

Lemma lookPtUnO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> find x (untag f) = Some (@idyn _ id _ v).
Proof. by rewrite partitionE; apply: hfindPtUn. Qed.

Implicit Arguments lookPtUnO [A h x v f].

Lemma freePtUnO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> free x (untag f) = h.
Proof. by rewrite partitionE; apply: hfreePtUn. Qed.

Implicit Arguments freePtUnO [A h x v f].

Lemma updPtUnO A1 A2 x i (v1 : A1) (v2 : A2)
               (f : forall k, partition k i) :
        upd x (@idyn _ id _ v2) (untag (f (x :-> v1))) = f (x :-> v2).
Proof. by rewrite !partitionE; apply: hupdPtUn. Qed.

Implicit Arguments updPtUnO [A1 A2 x i v1 v2].

Lemma cancelTO A1 A2 h1 h2 x (v1 : A1) (v2 : A2)
               (f1 : partition (x :-> v1) h1)
               (f2 : partition (x :-> v2) h2) :
        valid (untag f1) -> f1 = f2 :> heap -> A1 = A2.
Proof. by rewrite !partitionE; apply: hcancelT. Qed.

Implicit Arguments cancelTO [A1 A2 h1 h2 v1 v2 f1 f2].

Lemma cancelO A h1 h2 x (v1 v2 : A)
              (f1 : partition (x :-> v1) h1)
              (f2 : partition (x :-> v2) h2) :
        valid (untag f1) -> f1 = f2 :> heap ->
        [/\ v1 = v2, valid h1 & h1 = h2].
Proof. by rewrite !partitionE; apply: hcancelV. Qed.

Implicit Arguments cancelO [A h1 h2 v1 v2 f1 f2].

Lemma domPtUnXO A (v : A) x i (f : partition (x :-> v) i) :
        valid (untag f) -> x \in dom (untag f).
Proof. by rewrite partitionE; apply: domPtUnX. Qed.


