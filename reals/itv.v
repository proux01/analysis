(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice order ssralg ssrnum ssrint.
From mathcomp Require Import interval.
From mathcomp Require Import mathcomp_extra boolp.

(**md**************************************************************************)
(* # Numbers within an interval                                               *)
(*                                                                            *)
(* This file develops tools to make the manipulation of numbers within        *)
(* a known interval easier, thanks to canonical structures. This adds types   *)
(* like {itv R & `[a, b]}, a notation e%:itv that infers an enclosing         *)
(* interval for expression e according to existing canonical instances and    *)
(* %:inum to cast back from type {itv R & i} to R.                            *)
(* For instance, x : {i01 R}, we have (1 - x%:inum)%:itv : {i01 R}            *)
(* automatically inferred.                                                    *)
(*                                                                            *)
(* ## types for values within known interval                                  *)
(* ```                                                                        *)
(*       {i01 R} == interface type for elements in R that live in `[0, 1];    *)
(*                  R must have a numDomainType structure.                    *)
(*                  Allows to solve automatically goals of the form x >= 0    *)
(*                  and x <= 1 if x is canonically a {i01 R}. {i01 R} is      *)
(*                  canonically stable by common operations.                  *)
(*   {itv R & i} == more generic type of values in interval i : interval int  *)
(*                  R must have a numDomainType structure. This type is shown *)
(*                  to be a porderType.                                       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## casts from/to values within known interval                              *)
(* ```                                                                        *)
(*        x%:itv == explicitly casts x to the most precise known {itv R & i}  *)
(*                  according to existing canonical instances.                *)
(*        x%:i01 == explicitly casts x to {i01 R} according to existing       *)
(*                  canonical instances.                                      *)
(*       x%:inum == explicit cast from {itv R & i} to R.                      *)
(* ```                                                                        *)
(*                                                                            *)
(* ## sign proofs                                                             *)
(* ```                                                                        *)
(*    [itv of x] == proof that x is in interval inferred by x%:itv            *)
(*     [lb of x] == proof that lb < x or lb <= x with lb the lower bound      *)
(*                  inferred by x%:itv                                        *)
(*     [ub of x] == proof that x < ub or x <= ub with ub the upper bound      *)
(*                  inferred by x%:itv                                        *)
(*    [lbe of x] == proof that lb <= x                                        *)
(*    [ube of x] == proof that x <= ub                                        *)
(* ```                                                                        *)
(*                                                                            *)
(* ## constructors                                                            *)
(* ```                                                                        *)
(*    ItvNum xin == builds a {itv R & i} from a proof xin : x \in i           *)
(*                  where x : R                                               *)
(* TODO Implement ItvNum *)
(* ```                                                                        *)
(*                                                                            *)
(* A number of canonical instances are provided for common operations, if     *)
(* your favorite operator is missing, look below for examples on how to add   *)
(* the appropriate Canonical.                                                 *)
(* Canonical instances are also provided according to types, as a             *)
(* fallback when no known operator appears in the expression. Look to         *)
(* itv_top_typ below for an example on how to add your favorite type.         *)
(******************************************************************************)

Reserved Notation "{ 'itv' R & i }"
  (at level 0, R at level 200, i at level 200, format "{ 'itv'  R  &  i }").
Reserved Notation "{ 'i01' R }"
  (at level 0, R at level 200, format "{ 'i01'  R }").

Reserved Notation "x %:itv" (at level 2, format "x %:itv").
Reserved Notation "x %:i01" (at level 2, format "x %:i01").
Reserved Notation "x %:inum" (at level 2, format "x %:inum").
Reserved Notation "[ 'itv' 'of' x ]" (format "[ 'itv' 'of'  x ]").
Reserved Notation "[ 'lb' 'of' x ]" (format "[ 'lb' 'of'  x ]").
Reserved Notation "[ 'ub' 'of' x ]" (format "[ 'ub' 'of'  x ]").
Reserved Notation "[ 'lbe' 'of' x ]" (format "[ 'lbe' 'of'  x ]").
Reserved Notation "[ 'ube' 'of' x ]" (format "[ 'ube' 'of'  x ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Order.Syntax.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope order_scope.

Module Itv.

Variant t := Top | Real of interval int.

Definition sub (x y : t) :=
  match x, y with
  | _, Top => true
  | Top, Real _ => false
  | Real xi, Real yi => subitv xi yi
  end.

Definition map_itv_bound S T (f : S -> T) (b : itv_bound S) : itv_bound T :=
  match b with
  | BSide b x => BSide b (f x)
  | BInfty b => BInfty _ b
  end.

Section Itv.
Context T (sem : interval int -> T -> bool).

Definition spec (i : t) (x : T) := if i is Real i then sem i x else true.

Record def (i : t) := Def {
  r : T;
  #[canonical=no]
  P : spec i r
}.

End Itv.

Record typ i := Typ {
  sort : Type;
  #[canonical=no]
  sort_sem : interval int -> sort -> bool;
  #[canonical=no]
  allP : forall x : sort, spec sort_sem i x
}.

Definition mk {T f} i x P : @def T f i := @Def T f i x P.

Definition from {T f i} {x : @def T f i} (phx : phantom T (r x)) := x.

Definition fromP {T f i} {x : @def T f i} (phx : phantom T (r x)) := P x.

Definition num_sem (R : numDomainType) (i : interval int) (x : R) : bool :=
  (x \in Num.real)
  && let: Interval l u := i in
     x \in Interval (map_itv_bound intr l) (map_itv_bound intr u).

Definition nat_sem (i : interval int) (x : nat) : bool := Posz x \in i.

Module Exports.
Arguments r {T sem i}.
Notation "{ 'itv' R & i }" := (def (@num_sem R) (Itv.Real i%Z)) : type_scope.
Notation "{ 'i01' R }" := {itv R & `[0, 1]} : type_scope.
Notation "x %:itv" := (from (Phantom _ x)) : ring_scope.
Notation "[ 'itv' 'of' x ]" := (fromP (Phantom _ x)) : ring_scope.
Notation inum := r.
Notation "x %:inum" := (r x) : ring_scope.
End Exports.
End Itv.
Export Itv.Exports.

Local Notation num_spec := (Itv.spec (@Itv.num_sem _)).
Local Notation num_def R := (Itv.def (@Itv.num_sem R)).
Local Notation num_itv_bound R := (@Itv.map_itv_bound _ R intr).

Local Notation nat_spec := (Itv.spec Itv.nat_sem).
Local Notation nat_def := (Itv.def Itv.nat_sem).

Section POrder.
Context d (T : porderType d) (f : interval int -> T -> bool) (i : Itv.t).
Local Notation itv := (Itv.def f i).
HB.instance Definition _ := [isSub for @Itv.r T f i].
HB.instance Definition _ := [Choice of itv by <:].
HB.instance Definition _ := [SubChoice_isSubPOrder of itv by <: with d].
End POrder.

Lemma top_typ_subproof T f (x : T) : Itv.spec f Itv.Top x.
Proof. by []. Qed.

Canonical top_typ T f := Itv.Typ (@top_typ_subproof T f).

Lemma real_domain_typ_subproof (R : realDomainType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. by rewrite /Itv.num_sem/= num_real. Qed.

Canonical real_domain_typ (R : realDomainType) :=
  Itv.Typ (@real_domain_typ_subproof R).

Lemma real_field_typ_subproof (R : realFieldType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. exact: real_domain_typ_subproof. Qed.

Canonical real_field_typ (R : realFieldType) :=
  Itv.Typ (@real_field_typ_subproof R).

Lemma nat_typ_subproof (x : nat) : nat_spec (Itv.Real `[0, +oo[) x.
Proof. by []. Qed.

Canonical nat_typ := Itv.Typ nat_typ_subproof.

Lemma typ_inum_subproof (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :
  Itv.spec (@Itv.sort_sem _ xt) i x.
Proof. by move: xt x => []. Qed.

(* This adds _ <- Itv.r ( typ_inum )
   to canonical projections (c.f., Print Canonical Projections
   Itv.r) meaning that if no other canonical instance (with a
   registered head symbol) is found, a canonical instance of
   Itv.typ, like the ones above, will be looked for. *)
Canonical typ_inum (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :=
  Itv.mk (typ_inum_subproof x).

Class unify {T} f (x y : T) := Unify : f x y = true.
#[export] Hint Mode unify - - - + : typeclass_instances.
Class unify' {T} f (x y : T) := Unify' : f x y = true.
#[export] Instance unify'P {T} f (x y : T) : unify' f x y -> unify f x y := id.
#[export]
Hint Extern 0 (unify' _ _ _) => vm_compute; reflexivity : typeclass_instances.

Notation unify_itv ix iy := (unify Itv.sub ix iy).

Definition itv_real1_subdef (op1 : interval int -> interval int)
    (x : Itv.t) : Itv.t :=
  match x with Itv.Top => Itv.Top | Itv.Real x => Itv.Real (op1 x) end.

Definition itv_real2_subdef (op2 : interval int -> interval int -> interval int)
    (x y : Itv.t) : Itv.t :=
  match x, y with
  | Itv.Top, _ | _, Itv.Top => Itv.Top
  | Itv.Real x, Itv.Real y => Itv.Real (op2 x y)
  end.

Lemma itv_real1_subproof T f (op1 : T -> T)
    (op1i : interval int -> interval int) (x : T) :
    (forall xi, f xi x = true -> f (op1i xi) (op1 x) = true) ->
  forall xi, Itv.spec f xi x ->
    Itv.spec f (itv_real1_subdef op1i xi) (op1 x).
Proof. by move=> + [//| xi]; apply. Qed.

Lemma itv_real2_subproof T f (op2 : T -> T -> T)
    (op2i : interval int -> interval int -> interval int) (x y : T) :
    (forall xi yi, f xi x = true -> f yi y = true ->
     f (op2i xi yi) (op2 x y) = true) ->
  forall xi yi, Itv.spec f xi x -> Itv.spec f yi y ->
    Itv.spec f (itv_real2_subdef op2i xi yi) (op2 x y).
Proof. by move=> + [//| xi] [//| yi]; apply. Qed.

Section NumDomainTheory.
Context {R : numDomainType} {i : Itv.t}.
Implicit Type x : num_def R i.

Lemma le_map_itv_bound (x y : itv_bound int) :
  x <= y -> num_itv_bound R x <= num_itv_bound R y.
Proof.
case: x y => [xs x [ys y |//] | + [//|]]; last by case.
by rewrite /Order.le/=; case: (_ ==> _) => /=; rewrite ?ler_int ?ltr_int.
Qed.

Lemma subitv_map_itv (x y : Itv.t) : Itv.sub x y ->
  forall z : R, num_spec x z -> num_spec y z.
Proof.
case: x y => [| x] [| y] //= x_sub_y z /andP[rz]; rewrite /Itv.num_sem rz/=.
move: x y x_sub_y => [lx ux] [ly uy] /andP[lel leu] /=.
move=> /andP[lxz zux]; apply/andP; split.
- apply: le_trans lxz.
  by apply: (le_map_itv_bound lel); apply: map_itv_bound_num.
- apply: le_trans zux _.
  by apply: (le_map_itv_bound leu); apply: map_itv_bound_num.
Qed.

Definition empty_itv := Itv.Real `[Posz 1, Posz 0].

Lemma itv_bottom x : unify_itv i empty_itv -> False.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /andP[] /le_trans /[apply]; rewrite ler10.
Qed.

Lemma itv_gt0 x : unify_itv i (Itv.Real `]Posz 0, +oo[) -> 0%R < x%:inum :> R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_].
by rewrite /= in_itv/= andbT.
Qed.

Lemma itv_le0F x : unify_itv i (Itv.Real `]Posz 0, +oo[) ->
  x%:inum <= 0%R :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /lt_geF.
Qed.

Lemma itv_lt0 x : unify_itv i (Itv.Real `]-oo, Posz 0[) -> x%:inum < 0%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma itv_ge0F x : unify_itv i (Itv.Real `]-oo, Posz 0[) ->
  0%R <= x%:inum :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma itv_ge0 x : unify_itv i (Itv.Real `[Posz 0, +oo[) -> 0%R <= x%:inum :> R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT.
Qed.

Lemma itv_lt0F x : unify_itv i (Itv.Real `[Posz 0, +oo[) ->
  x%:inum < 0%R :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /le_gtF.
Qed.

Lemma itv_le0 x : unify_itv i (Itv.Real `]-oo, Posz 0]) -> x%:inum <= 0%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma itv_gt0F x : unify_itv i (Itv.Real `]-oo, Posz 0]) ->
  0%R < x%:inum :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma lt1 x : unify_itv i (Itv.Real `]-oo, Posz 1[) -> x%:inum < 1%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge1F x : unify_itv i (Itv.Real `]-oo, Posz 1[) ->
  1%R <= x%:inum :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma le1 x : unify_itv i (Itv.Real `]-oo, Posz 1]) -> x%:inum <= 1%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma gt1F x : unify_itv i (Itv.Real `]-oo, Posz 1]) ->
  1%R < x%:inum :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma widen_itv_subproof x i' : Itv.sub i i' -> num_spec i' x%:inum.
Proof. by case: x => x /= /[swap] /subitv_map_itv; apply. Qed.

Definition widen_itv x i' (uni : unify_itv i i') :=
  Itv.mk (widen_itv_subproof x uni).

Lemma widen_itvE x (uni : unify_itv i i) : @widen_itv x i uni = x.
Proof. exact/val_inj. Qed.

End NumDomainTheory.

Arguments itv_bottom {R i} _ {_}.
Arguments itv_gt0 {R i} _ {_}.
Arguments itv_le0F {R i} _ {_}.
Arguments itv_lt0 {R i} _ {_}.
Arguments itv_ge0F {R i} _ {_}.
Arguments itv_ge0 {R i} _ {_}.
Arguments itv_lt0F {R i} _ {_}.
Arguments itv_le0 {R i} _ {_}.
Arguments itv_gt0F {R i} _ {_}.
Arguments lt1 {R i} _ {_}.
Arguments ge1F {R i} _ {_}.
Arguments le1 {R i} _ {_}.
Arguments gt1F {R i} _ {_}.
Arguments widen_itv {R i} _ {_ _}.
Arguments widen_itvE {R i} _ {_}.

#[export] Hint Extern 0 (is_true (0%R < _)%O) => solve [apply: itv_gt0] : core.
#[export] Hint Extern 0 (is_true (_ < 0%R)%O) => solve [apply: itv_lt0] : core.
#[export] Hint Extern 0 (is_true (0%R <= _)%O) => solve [apply: itv_ge0] : core.
#[export] Hint Extern 0 (is_true (_ <= 0%R)%O) => solve [apply: itv_le0] : core.
#[export] Hint Extern 0 (is_true (_ < 1%R)%O) => solve [apply: lt1] : core.
#[export] Hint Extern 0 (is_true (_ <= 1%R)%O) => solve [apply: le1] : core.

Notation "x %:i01" := (widen_itv x%:itv : {i01 _}) (only parsing) : ring_scope.
Notation "x %:i01" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[Posz 0, Posz 1]) _)
  (only printing) : ring_scope.

Local Open Scope ring_scope.

Section NumDomainInstances.
Context {R : numDomainType}.

Lemma zero_inum_subproof : num_spec (Itv.Real `[0, 0]) (0 : R).
Proof. by apply/andP; split; [exact: real0 | rewrite /= in_itv/= lexx]. Qed.

Canonical zero_inum := Itv.mk zero_inum_subproof.

Lemma one_inum_subproof : num_spec (Itv.Real `[1, 1]) (1 : R).
Proof. by apply/andP; split; [exact: real1 | rewrite /= in_itv/= lexx]. Qed.

Canonical one_inum := Itv.mk one_inum_subproof.

Definition opp_itv_bound_subdef (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b x => BSide (~~ b) (intZmod.oppz x)
  | BInfty b => BInfty _ (~~ b)
  end.
Arguments opp_itv_bound_subdef /.

Lemma opp_itv_ge0_subproof b :
  (BLeft 0%R <= opp_itv_bound_subdef b)%O = (b <= BRight 0%R)%O.
Proof. by case: b => [[] b | []//]; rewrite /= !bnd_simp oppr_ge0. Qed.

Lemma opp_itv_gt0_subproof b :
  (BLeft 0%R < opp_itv_bound_subdef b)%O = (b < BRight 0%R)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp ?oppr_ge0 // oppr_gt0.
Qed.

Lemma opp_itv_boundr_subproof (x : R) b :
  (BRight (- x)%R <= num_itv_bound R (opp_itv_bound_subdef b))%O
  = (num_itv_bound R b <= BLeft x)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Lemma opp_itv_le0_subproof b :
  (opp_itv_bound_subdef b <= BRight 0%R)%O = (BLeft 0%R <= b)%O.
Proof. by case: b => [[] b | []//]; rewrite /= !bnd_simp oppr_le0. Qed.

Lemma opp_itv_lt0_subproof b :
  (opp_itv_bound_subdef b < BRight 0%R)%O = (BLeft 0%R < b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp ?oppr_le0 // oppr_lt0.
Qed.

Lemma opp_itv_boundl_subproof (x : R) b :
  (num_itv_bound R (opp_itv_bound_subdef b) <= BLeft (- x)%R)%O
  = (BRight x <= num_itv_bound R b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Definition opp_itv_subdef (i : interval int) : interval int :=
  let 'Interval l u := i in
  Interval (opp_itv_bound_subdef u) (opp_itv_bound_subdef l).
Arguments opp_itv_subdef /.

Lemma opp_inum_subproof (i : Itv.t) (x : num_def R i)
    (r := itv_real1_subdef opp_itv_subdef i) :
  num_spec r (- x%:inum).
Proof.
apply: itv_real1_subproof (Itv.P x).
case: x => x /= _ [l u] /and3P[xr lx xu].
rewrite /Itv.num_sem/= realN xr/=; apply/andP.
by rewrite opp_itv_boundl_subproof opp_itv_boundr_subproof.
Qed.

Canonical opp_inum (i : Itv.t) (x : num_def R i) :=
  Itv.mk (opp_inum_subproof x).

Definition add_itv_boundl_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ true
  end.
Arguments add_itv_boundl_subdef /.

Lemma add_itv_boundl_subproof (x1 x2 : R) b1 b2 :
  (num_itv_bound R b1 <= BLeft x1)%O -> (num_itv_bound R b2 <= BLeft x2)%O ->
  (num_itv_bound R (add_itv_boundl_subdef b1 b2) <= BLeft (x1 + x2)%R)%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr_tmp.
- exact: lerD.
- exact: ler_ltD.
- exact: ltr_leD.
- exact: ltrD.
Qed.

Definition add_itv_boundr_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ false
  end.
Arguments add_itv_boundr_subdef /.

Lemma add_itv_boundr_subproof (x1 x2 : R) b1 b2 :
  (BRight x1 <= num_itv_bound R b1)%O -> (BRight x2 <= num_itv_bound R b2)%O ->
  (BRight (x1 + x2)%R <= num_itv_bound R (add_itv_boundr_subdef b1 b2))%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr_tmp.
- exact: ltrD.
- exact: ltr_leD.
- exact: ler_ltD.
- exact: lerD.
Qed.

Definition add_itv_subdef (i1 i2 : interval int) : interval int :=
  let 'Interval l1 u1 := i1 in
  let 'Interval l2 u2 := i2 in
  Interval (add_itv_boundl_subdef l1 l2) (add_itv_boundr_subdef u1 u2).
Arguments add_itv_subdef /.

Lemma add_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef add_itv_subdef xi yi) :
  num_spec r (x%:inum + y%:inum).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
rewrite /Itv.num_sem realD//=; apply/andP.
by rewrite add_itv_boundl_subproof ?add_itv_boundr_subproof.
Qed.

Canonical add_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (add_inum_subproof x y).

Variant sign := EqZero | NonNeg | NonPos.

Definition itv_bound_signl (b : itv_bound int) : sign :=
  let b0 := BLeft 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Definition itv_bound_signr (b : itv_bound int) : sign :=
  let b0 := BRight 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Definition interval_sign (i : interval int) : option (option sign) :=
  let 'Interval l u := i in
  match itv_bound_signl l, itv_bound_signr u with
  | EqZero, NonPos
  | NonNeg, EqZero
  | NonNeg, NonPos => None
  | EqZero, EqZero => Some (Some EqZero)
  | NonPos, EqZero
  | NonPos, NonPos => Some (Some NonPos)
  | EqZero, NonNeg
  | NonNeg, NonNeg => Some (Some NonNeg)
  | NonPos, NonNeg => Some None
  end.

Variant interval_sign_spec (l u : itv_bound int) : option (option sign) -> Set :=
  | ISignNone : (u <= l)%O -> interval_sign_spec l u None
  | ISignEqZero : l = BLeft 0 -> u = BRight 0 ->
                  interval_sign_spec l u (Some (Some EqZero))
  | ISignNeg : (l < BLeft 0%:Z)%O -> (u <= BRight 0%:Z)%O ->
               interval_sign_spec l u (Some (Some NonPos))
  | ISignPos : (BLeft 0%:Z <= l)%O -> (BRight 0%:Z < u)%O ->
               interval_sign_spec l u (Some (Some NonNeg))
  | ISignBoth : (l < BLeft 0%:Z)%O -> (BRight 0%:Z < u)%O ->
                interval_sign_spec l u (Some None).

Lemma interval_signP l u :
  interval_sign_spec l u (interval_sign (Interval l u)).
Proof.
rewrite /interval_sign/itv_bound_signl/itv_bound_signr.
have [lneg|lpos|->] := ltgtP l; have [uneg|upos|->] := ltgtP u.
- apply: ISignNeg => //; exact: ltW.
- exact: ISignBoth.
- exact: ISignNeg.
- by apply/ISignNone/ltW/(lt_le_trans uneg); rewrite leBRight_ltBLeft.
- by apply: ISignPos => //; exact: ltW.
- by apply: ISignNone; rewrite leBRight_ltBLeft.
- by apply: ISignNone; rewrite -ltBRight_leBLeft.
- exact: ISignPos.
- exact: ISignEqZero.
Qed.

Definition mul_itv_boundl_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide true 0%Z, BSide _ _
  | BSide _ _, BSide true 0%Z => BSide true 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intRing.mulz x1 x2)
  | _, BInfty _
  | BInfty _, _ => BInfty _ false
  end.
Arguments mul_itv_boundl_subdef /.

Definition mul_itv_boundr_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide true 0%Z, _
  | _, BSide true 0%Z => BSide true 0%Z
  | BSide false 0%Z, _
  | _, BSide false 0%Z => BSide false 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intRing.mulz x1 x2)
  | _, BInfty _
  | BInfty _, _ => BInfty _ false
  end.
Arguments mul_itv_boundr_subdef /.

Lemma mul_itv_boundl_subproof b1 b2 (x1 x2 : R) :
  (BLeft 0%:Z <= num_itv_bound int b1 -> BLeft 0%:Z <= num_itv_bound int b2 ->
   num_itv_bound R b1 <= BLeft x1 ->
   num_itv_bound R b2 <= BLeft x2 ->
   num_itv_bound R (mul_itv_boundl_subdef b1 b2) <= BLeft (x1 * x2))%O.
Proof.
Admitted.
(* move: b1 b2 => [[] b1 | []//] [[] b2 | []//] /=; rewrite 4!bnd_simp. *)
(* - set bl := match b1 with 0%Z => _ | _ => _ end. *)
(*   have -> : bl = BLeft (b1 * b2). *)
(*     rewrite {}/bl; move: b1 b2 => [[|p1]|p1] [[|p2]|p2]; congr BLeft. *)
(*     by rewrite mulr0. *)
(*   rewrite -2!(ler0z R) bnd_simp intrM; exact: ler_pM. *)
(* - case: b1 => [[|p1]|//]; rewrite -2!(ler0z R) !bnd_simp ?intrM. *)
(*     by move=> _ geb2 ? ?; apply: mulr_ge0 => //; apply/(le_trans geb2)/ltW. *)
(*   move=> p1gt0 b2ge0 lep1x1 ltb2x2. *)
(*   have: (Posz p1.+1)%:~R * x2 <= x1 * x2. *)
(*     by rewrite ler_pM2r //; apply: le_lt_trans ltb2x2. *)
(*   by apply: lt_le_trans; rewrite ltr_pM2l // ltr0z. *)
(* - case: b2 => [[|p2]|//]; rewrite -2!(ler0z R) !bnd_simp ?intrM. *)
(*     by move=> geb1 _ ? ?; apply: mulr_ge0 => //; apply/(le_trans geb1)/ltW. *)
(*   move=> b1ge0 p2gt0 ltb1x1 lep2x2. *)
(*   have: b1%:~R * x2 < x1 * x2; last exact/le_lt_trans/ler_pM. *)
(*   by rewrite ltr_pM2r //; apply: lt_le_trans lep2x2; rewrite ltr0z. *)
(* - rewrite -2!(ler0z R) bnd_simp intrM; exact: ltr_pM. *)
(* Qed. *)

Lemma mul_itv_boundrC_subproof b1 b2 :
  mul_itv_boundr_subdef b1 b2 = mul_itv_boundr_subdef b2 b1.
Proof.
by move: b1 b2 => [[] [[|?]|?] | []] [[] [[|?]|?] | []] //=; rewrite mulnC.
Qed.

Lemma mul_itv_boundr_subproof b1 b2 (x1 x2 : R) :
  (BLeft 0%R <= BLeft x1 -> BLeft 0%R <= BLeft x2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_itv_boundl_subdef b1 b2))%O.
Proof.
Admitted.
(* move: b1 b2 => [b1b b1 | []] [b2b b2 | []] //=; last first. *)
(* - move: b2 b2b => [[|p2]|p2] [] // _ + _ +; rewrite !bnd_simp => le1 le2. *)
(*   + by move: (le_lt_trans le1 le2); rewrite ltxx. *)
(*   + by move: (conj le1 le2) => /andP/le_anti <-; rewrite mulr0. *)
(* - move: b1 b1b => [[|p1]|p1] [] // + _ + _; rewrite !bnd_simp => le1 le2. *)
(*   + by move: (le_lt_trans le1 le2); rewrite ltxx. *)
(*   + by move: (conj le1 le2) => /andP/le_anti <-; rewrite mul0r. *)
(* case: b1 => [[|p1]|p1]. *)
(* - case: b1b. *)
(*     by rewrite !bnd_simp => l _ l' _; move: (le_lt_trans l l'); rewrite ltxx. *)
(*   by move: b2b b2 => [] [[|p2]|p2]; rewrite !bnd_simp; *)
(*     first (by move=> _ l _ l'; move: (le_lt_trans l l'); rewrite ltxx); *)
(*     move=> l _ l' _; move: (conj l l') => /andP/le_anti <-; rewrite mul0r. *)
(* - rewrite if_same. *)
(*   case: b2 => [[|p2]|p2]. *)
(*   + case: b2b => _ + _ +; rewrite !bnd_simp => l l'. *)
(*       by move: (le_lt_trans l l'); rewrite ltxx. *)
(*     by move: (conj l l') => /andP/le_anti <-; rewrite mulr0. *)
(*   + move: b1b b2b => [] []; rewrite !bnd_simp; *)
(*       rewrite -[intRing.mulz ?[a] ?[b]]/((Posz ?[a]) * ?[b])%R intrM. *)
(*     * exact: ltr_pM. *)
(*     * move=> x1ge0 x2ge0 ltx1p1 lex2p2. *)
(*       have: x1 * p2.+1%:~R < p1.+1%:~R * p2.+1%:~R. *)
(*         by rewrite ltr_pM2r // ltr0z. *)
(*       exact/le_lt_trans/ler_pM. *)
(*     * move=> x1ge0 x2ge0 lex1p1 ltx2p2. *)
(*       have: p1.+1%:~R * x2 < p1.+1%:~R * p2.+1%:~R. *)
(*         by rewrite ltr_pM2l // ltr0z. *)
(*       exact/le_lt_trans/ler_pM. *)
(*     * exact: ler_pM. *)
(*   + case: b2b => _ + _; rewrite 2!bnd_simp => l l'. *)
(*       by move: (le_lt_trans l l'); rewrite ltr0z. *)
(*     by move: (le_trans l l'); rewrite ler0z. *)
(* - case: b1b => + _ + _; rewrite 2!bnd_simp => l l'. *)
(*     by move: (le_lt_trans l l'); rewrite ltr0z. *)
(*   by move: (le_trans l l'); rewrite ler0z. *)
(* Qed. *)

Lemma mul_itv_boundr'_subproof b1 b2 (x1 x2 : R) :
  (BLeft 0%:R <= BLeft x1 -> BRight 0%:Z <= num_itv_bound int b2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_itv_boundl_subdef b1 b2))%O.
Proof.
Admitted.
(* move=> x1ge0 b2ge0 lex1b1 lex2b2. *)
(* have [x2ge0 | x2lt0] := leP 0 x2; first exact: mul_itv_boundr_subproof. *)
(* have lem0 : (BRight (x1 * x2) <= BRight 0%R)%O. *)
(*   by rewrite bnd_simp mulr_ge0_le0 // ltW. *)
(* apply: le_trans lem0 _. *)
(* move: b1 b2 lex1b1 lex2b2 b2ge0 => [b1b b1 | []] [b2b b2 | []] //=; last first. *)
(* - by move: b2 b2b => [[|?]|?] []. *)
(* - move: b1 b1b => [[|p1]|p1] [] //. *)
(*   by rewrite leBRight_ltBLeft => /(le_lt_trans x1ge0); rewrite ltxx. *)
(* case: b1 => [[|p1]|p1]. *)
(* - case: b1b; last by move: b2b b2 => [] [[|]|]. *)
(*   by rewrite leBRight_ltBLeft => /(le_lt_trans x1ge0); rewrite ltxx. *)
(* - rewrite if_same. *)
(*   case: b2 => [[|p2]|p2]; first (by case: b2b); last by case: b2b. *)
(*   by rewrite if_same => _ _ _ /=; rewrite leBSide ltrW_lteif // ltr0z. *)
(* - rewrite leBRight_ltBLeft => /(le_lt_trans x1ge0). *)
(*   by case: b1b; rewrite bnd_simp ?ltr0z // ler0z. *)
(* Qed. *)

Definition mul_itv_subdef (i1 i2 : interval int) : interval int :=
  let 'Interval l1 u1 := i1 in
  let 'Interval l2 u2 := i2 in
  let opp := opp_itv_bound_subdef in
  let mull := mul_itv_boundl_subdef in
  let mulr := mul_itv_boundr_subdef in
  match interval_sign i1, interval_sign i2 with
  | None, _ | _, None => `[1, 0]
  | some s1, Some s2 =>
    match s1, s2 with
    | Some EqZero, _ => `[0, 0]
    | _, Some EqZero => `[0, 0]
    | Some NonNeg, Some NonNeg =>
        Interval (mull l1 l2) (mulr u1 u2)
    | Some NonPos, Some NonPos =>
        Interval (mull (opp u1) (opp u2)) (mulr (opp l1) (opp l2))
    | Some NonNeg, Some NonPos =>
        Interval (opp (mulr u1 (opp l2))) (opp (mull l1 (opp u2)))
    | Some NonPos, Some NonNeg =>
        Interval (opp (mulr (opp l1) u2)) (opp (mull (opp u1) l2))
    | Some NonNeg, None =>
        Interval (opp (mulr u1 (opp l2))) (mulr u1 u2)
    | Some NonPos, None =>
        Interval (opp (mulr (opp l1) u2)) (mulr (opp l1) (opp l2))
    | None, Some NonNeg =>
        Interval (opp (mulr (opp l1) u2)) (mulr u1 u2)
    | None, Some NonPos =>
        Interval (opp (mulr u1 (opp l2))) (mulr (opp l1) (opp l2))
    | None, None =>
        Interval
          (Order.min (opp (mulr (opp l1) u2)) (opp (mulr u1 (opp l2))))
          (Order.max (mulr (opp l1) (opp l2)) (mulr u1 u2))
    end
  end.
Arguments mul_itv_subdef /.

(* Lemma map_itv_bound_min (x y : itv_bound int) : *)
(*   Itv.map_itv_bound (fun x => x%:~R : R) (Order.min x y) *)
(*   = Order.min (Itv.map_itv_bound intr x) (Itv.map_itv_bound intr y). *)
(* Proof. *)
(* have [lexy|ltyx] := leP x y; first by rewrite !minEle Itv.le_map_itv_bound. *)
(* by rewrite minElt -if_neg -leNgt Itv.le_map_itv_bound // ltW. *)
(* Qed. *)

(* Lemma map_itv_bound_max (x y : itv_bound int) : *)
(*   Itv.map_itv_bound (fun x => x%:~R : R) (Order.max x y) *)
(*   = Order.max (Itv.map_itv_bound intr x) (Itv.map_itv_bound intr y). *)
(* Proof. *)
(* have [lexy|ltyx] := leP x y; first by rewrite !maxEle Itv.le_map_itv_bound. *)
(* by rewrite maxElt -if_neg -leNgt Itv.le_map_itv_bound // ltW. *)
(* Qed. *)

Lemma mul_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef mul_itv_subdef xi yi) :
  num_spec r (x%:inum * y%:inum).
Proof.
Admitted. (*
rewrite {}/r.
move: xi x yi y => [lx ux] [x /= /andP[+ +]] [ly uy] [y /= /andP[+ +]].
rewrite -/(interval_sign (Interval lx ux)).
rewrite -/(interval_sign (Interval ly uy)).
have empty10 (z : R) l u : (u <= l)%O ->
    (Itv.map_itv_bound [eta intr] l <= BLeft z)%O ->
    (BRight z <= Itv.map_itv_bound [eta intr] u)%O -> False.
  move=> leul; rewrite leBRight_ltBLeft => /le_lt_trans /[apply].
  rewrite lt_def => /andP[/[swap]] => + /ltac:(apply/negP).
  rewrite negbK; move: leul => /(Itv.le_map_itv_bound R) le1 le2.
  by apply/eqP/le_anti; rewrite le1.
pose opp := opp_itv_bound_subdef.
pose mull := mul_itv_boundl_subdef.
pose mulr := mul_itv_boundr_subdef.
have [leuxlx|-> ->|lxneg uxneg|lxpos uxpos|lxneg uxpos] := interval_signP.
- move=> + + /ltac:(exfalso); exact: empty10.
- rewrite 2!bnd_simp => lex1 lex2 ley1 ley2.
  have -> : x = 0 by apply: le_anti; rewrite lex1 lex2.
  rewrite mul0r.
  case: interval_signP; [|by move=> _ _; rewrite /Itv.spec in_itv/= lexx..].
  by move=> leul; exfalso; move: ley1 ley2; apply: empty10.
- move=> lelxx lexux.
  have xneg : x <= 0.
    move: (le_trans lexux (Itv.le_map_itv_bound R uxneg)).
    by rewrite /= bnd_simp.
  have [leuyly|-> ->|lyneg uyneg|lypos uypos|lyneg uypos] := interval_signP.
  + move=> + + /ltac:(exfalso); exact: empty10.
  + rewrite 2!bnd_simp => ley1 ley2.
    have -> : y = 0 by apply: le_anti; rewrite ley1 ley2.
    by rewrite mulr0 /Itv.spec in_itv/= lexx.
  + move=> lelyy leyuy.
    have yneg : y <= 0.
      move: (le_trans leyuy (Itv.le_map_itv_bound R uyneg)).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (mull (opp ux) (opp uy))
                               (mulr (opp lx) (opp ly))).
    rewrite -mulrNN /Itv.spec itv_boundlr.
    rewrite mul_itv_boundl_subproof ?mul_itv_boundr_subproof //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite opp_itv_boundr_subproof.
    * by rewrite opp_itv_boundr_subproof.
    * by rewrite opp_itv_ge0_subproof.
    * by rewrite opp_itv_ge0_subproof.
    * by rewrite opp_itv_boundl_subproof.
    * by rewrite opp_itv_boundl_subproof.
  + move=> lelyy leyuy.
    have ypos : 0 <= y.
      move: (le_trans (Itv.le_map_itv_bound R lypos) lelyy).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr (opp lx) uy))
                               (opp (mull (opp ux) ly))).
    rewrite -[x * y]opprK -mulNr /Itv.spec itv_boundlr.
    rewrite opp_itv_boundl_subproof opp_itv_boundr_subproof.
    rewrite mul_itv_boundl_subproof ?mul_itv_boundr_subproof //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite opp_itv_boundr_subproof.
    * by rewrite opp_itv_ge0_subproof.
    * by rewrite opp_itv_boundl_subproof.
  + move=> lelyy leyuy.
    rewrite -[Interval _ _]/(Interval (opp (mulr (opp lx) uy))
                               (mulr (opp lx) (opp ly))).
    rewrite -[x * y]opprK -mulNr /Itv.spec itv_boundlr.
    rewrite opp_itv_boundl_subproof -mulrN.
    rewrite 2?mul_itv_boundr'_subproof //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite leBRight_ltBLeft opp_itv_gt0_subproof ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr_subproof.
    * by rewrite opp_itv_boundr_subproof.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite ltW.
    * by rewrite opp_itv_boundr_subproof.
- move=> lelxx lexux.
  have xpos : 0 <= x.
    move: (le_trans (Itv.le_map_itv_bound R lxpos) lelxx).
    by rewrite /= bnd_simp.
  have [leuyly|-> ->|lyneg uyneg|lypos uypos|lyneg uypos] := interval_signP.
  + move=> + + /ltac:(exfalso); exact: empty10.
  + rewrite 2!bnd_simp => ley1 ley2.
    have -> : y = 0 by apply: le_anti; rewrite ley1 ley2.
    by rewrite mulr0 /Itv.spec in_itv/= lexx.
  + move=> lelyy leyuy.
    have yneg : y <= 0.
      move: (le_trans leyuy (Itv.le_map_itv_bound R uyneg)).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr ux (opp ly)))
                               (opp (mull lx (opp uy)))).
    rewrite -[x * y]opprK -mulrN /Itv.spec itv_boundlr.
    rewrite opp_itv_boundl_subproof opp_itv_boundr_subproof.
    rewrite mul_itv_boundr_subproof ?mul_itv_boundl_subproof //.
    * by rewrite opp_itv_ge0_subproof.
    * by rewrite opp_itv_boundl_subproof.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite opp_itv_boundr_subproof.
  + move=> lelyy leyuy.
    have ypos : 0 <= y.
      move: (le_trans (Itv.le_map_itv_bound R lypos) lelyy).
      by rewrite /= bnd_simp.
      rewrite -[Interval _ _]/(Interval (mull lx ly) (mulr ux uy)).
    rewrite /Itv.spec itv_boundlr.
    by rewrite mul_itv_boundr_subproof ?mul_itv_boundl_subproof.
  + move=> lelyy leyuy.
    rewrite -[Interval _ _]/(Interval (opp (mulr ux (opp ly))) (mulr ux uy)).
    rewrite -[x * y]opprK -mulrN /Itv.spec itv_boundlr.
    rewrite opp_itv_boundl_subproof -mulrN opprK.
    rewrite 2?mul_itv_boundr'_subproof //.
    * by rewrite ltW.
    * by rewrite leBRight_ltBLeft opp_itv_gt0_subproof ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr_subproof.
- move=> lelxx lexux.
  have [leuyly|-> ->|lyneg uyneg|lypos uypos|lyneg uypos] := interval_signP.
  + move=> + + /ltac:(exfalso); exact: empty10.
  + rewrite 2!bnd_simp => ley1 ley2.
    have -> : y = 0 by apply: le_anti; rewrite ley1 ley2.
    by rewrite mulr0 /Itv.spec in_itv/= lexx.
  + move=> lelyy leyuy.
    have yneg : y <= 0.
      move: (le_trans leyuy (Itv.le_map_itv_bound R uyneg)).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr ux (opp ly)))
                               (mulr (opp lx) (opp ly))).
    rewrite -[x * y]opprK -mulrN /Itv.spec itv_boundlr.
    rewrite /mulr mul_itv_boundrC_subproof mulrC opp_itv_boundl_subproof.
    rewrite [in X in _ && X]mul_itv_boundrC_subproof -mulrN.
    rewrite mul_itv_boundr'_subproof ?mul_itv_boundr'_subproof //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite leBRight_ltBLeft opp_itv_gt0_subproof ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr_subproof.
    * by rewrite opp_itv_boundr_subproof.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite ltW.
    * by rewrite opp_itv_boundr_subproof.
  + move=> lelyy leyuy.
    have ypos : 0 <= y.
      move: (le_trans (Itv.le_map_itv_bound R lypos) lelyy).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr (opp lx) uy)) (mulr ux uy)).
    rewrite -[x * y]opprK -mulNr /Itv.spec itv_boundlr.
    rewrite /mulr mul_itv_boundrC_subproof mulrC opp_itv_boundl_subproof.
    rewrite [in X in _ && X]mul_itv_boundrC_subproof -mulrN opprK.
    rewrite mul_itv_boundr'_subproof ?mul_itv_boundr'_subproof //.
    * by rewrite ltW.
    * by rewrite leBRight_ltBLeft opp_itv_gt0_subproof ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr_subproof.
  + move=> lelyy leyuy.
    rewrite -[Interval _ _]/(Interval
                               (Order.min (opp (mulr (opp lx) uy))
                                  (opp (mulr ux (opp ly))))
                               (Order.max (mulr (opp lx) (opp ly))
                                  (mulr ux uy))).
    rewrite /Itv.spec itv_boundlr.
    rewrite map_itv_bound_min map_itv_bound_max ge_min le_max.
    rewrite -[x * y]opprK !opp_itv_boundl_subproof.
    rewrite -[in X in ((X || _) && _)]mulNr -[in X in ((_ || X) && _)]mulrN.
    rewrite -[in X in (_ && (X || _))]mulrNN !opprK.
    have [xpos|xneg] := leP 0 x.
    * rewrite [in X in ((_ || X) && _)]mul_itv_boundr'_subproof ?orbT //=;
        rewrite ?[in X in (_ || X)]mul_itv_boundr'_subproof ?orbT //.
      - by rewrite ltW.
      - by rewrite leBRight_ltBLeft opp_itv_gt0_subproof ltBRight_leBLeft ltW.
      - by rewrite opp_itv_boundr_subproof.
    * rewrite [in X in ((X || _) && _)]mul_itv_boundr'_subproof //=;
        rewrite ?[in X in (X || _)]mul_itv_boundr'_subproof //.
      - by rewrite bnd_simp oppr_ge0 ltW.
      - by rewrite leBRight_ltBLeft opp_itv_gt0_subproof ltBRight_leBLeft ltW.
      - by rewrite opp_itv_boundr_subproof.
      - by rewrite opp_itv_boundr_subproof.
      - by rewrite bnd_simp oppr_ge0 ltW.
      - by rewrite ltW.
      - by rewrite opp_itv_boundr_subproof.
Qed. *)

Canonical mul_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (mul_inum_subproof x y).

Lemma min_itv_boundl_subproof x1 x2 b1 b2 :
  (num_itv_bound R b1 <= BLeft x1)%O -> (num_itv_bound R b2 <= BLeft x2)%O ->
  (num_itv_bound R (Order.min b1 b2) <= BLeft (Order.min x1 x2))%O.
Proof.
case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- have sb1_le_sb2 := @le_map_itv_bound R _ _ b1_le_b2.
  by rewrite minElt; case: (x1 < x2)%O => [//|_]; apply: le_trans.
- have sb2_le_sb1 := @le_map_itv_bound R _ _ b2_le_b1.
  by rewrite minElt; case: (x1 < x2)%O => [+ _|//]; apply: le_trans.
Qed.

Lemma min_itv_boundr_subproof (x1 x2 : R) b1 b2 : (x1 >=< x2)%O ->
  (BRight x1 <= num_itv_bound R b1)%O -> (BRight x2 <= num_itv_bound R b2)%O ->
  (BRight (Order.min x1 x2) <= num_itv_bound R (Order.min b1 b2))%O.
Proof.
move=> x1_cmp_x2; case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- have sb1_le_sb2 := @le_map_itv_bound R _ _ b1_le_b2.
  by case: (comparable_leP x1_cmp_x2) => [//| /ltW ? + _]; apply: le_trans.
- have sb2_le_sb1 := @le_map_itv_bound R _ _ b2_le_b1.
  by case: (comparable_leP x1_cmp_x2) => [? _ |//]; apply: le_trans.
Qed.

Definition min_itv_subdef (x y : interval int) : interval int :=
  let 'Interval lx ux := x in
  let 'Interval ly uy := y in
  Interval (Order.min lx ly) (Order.min ux uy).
Arguments min_itv_subdef /.

Lemma num_min_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef min_itv_subdef xi yi) :
  num_spec r (Order.min x%:inum y%:inum).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
rewrite /Itv.num_sem min_real//=; apply/andP; split.
- exact: min_itv_boundl_subproof.
- by apply: min_itv_boundr_subproof => //; apply: real_comparable.
Qed.

Lemma max_itv_boundl_subproof (x1 x2 : R) b1 b2 : (x1 >=< x2)%O ->
  (num_itv_bound R b1 <= BLeft x1)%O -> (num_itv_bound R b2 <= BLeft x2)%O ->
  (num_itv_bound R (Order.max b1 b2) <= BLeft (Order.max x1 x2))%O.
Proof.
move=> x1_cmp_x2.
case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- case: (comparable_leP x1_cmp_x2) => [//| /ltW ? _ sb2_x2].
  exact: le_trans sb2_x2 _.
- case: (comparable_leP x1_cmp_x2) => [? sb1_x1 _ |//].
  exact: le_trans sb1_x1 _.
Qed.

Lemma max_itv_boundr_subproof (x1 x2 : R) b1 b2 :
  (BRight x1 <= num_itv_bound R b1)%O -> (BRight x2 <= num_itv_bound R b2)%O ->
  (BRight (Order.max x1 x2) <= num_itv_bound R (Order.max b1 b2))%O.
Proof.
case: (leP b1 b2) => [b1_le_b2 | /ltW b2_le_b1].
- have sb1_le_sb2 := @le_map_itv_bound R _ _ b1_le_b2.
  by rewrite maxElt; case: ifP => [//|_ ? _]; apply: le_trans sb1_le_sb2.
- have sb2_le_sb1 := @le_map_itv_bound R _ _ b2_le_b1.
  by rewrite maxElt; case: ifP => [_ _ ?|//]; apply: le_trans sb2_le_sb1.
Qed.

Definition max_itv_subdef (x y : interval int) : interval int :=
  let 'Interval lx ux := x in
  let 'Interval ly uy := y in
  Interval (Order.max lx ly) (Order.max ux uy).
Arguments max_itv_subdef /.

Lemma num_max_inum_subproof (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef max_itv_subdef xi yi) :
  num_spec r (Order.max x%:inum y%:inum).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
rewrite /Itv.num_sem max_real//=; apply/andP; split.
- by apply: max_itv_boundl_subproof => //; apply: real_comparable.
- exact: max_itv_boundr_subproof.
Qed.

Lemma nat_num_spec (i : Itv.t) (n : nat) : nat_spec i n = num_spec i (n%:R : R).
Proof.
case: i => [//| [l u]]; rewrite /= /Itv.num_sem realn/=; congr (_ && _).
- by case: l => [[] l |//]; rewrite !bnd_simp ?pmulrn ?ler_int ?ltr_int.
- by case: u => [[] u |//]; rewrite !bnd_simp ?pmulrn ?ler_int ?ltr_int.
Qed.

Lemma natmul_inum_subproof (xi ni : Itv.t) (x : num_def R xi) (n : nat_def ni)
    (r := itv_real2_subdef mul_itv_subdef xi ni) :
  num_spec r (x%:inum *+ n%:inum).
Proof.
have Pn : num_spec ni (n%:inum%:R : R) by case: n => /= n; rewrite nat_num_spec.
by rewrite -mulr_natr -[n%:inum%:R]/((Itv.Def Pn)%:inum) mul_inum_subproof.
Qed.

Canonical natmul_inum (xi ni : Itv.t) (x : num_def R xi) (n : nat_def ni) :=
  Itv.mk (natmul_inum_subproof x n).

Lemma int_num_spec (i : Itv.t) (n : int) :
  num_spec i n = num_spec i (n%:~R : R).
Proof.
case: i => [//| [l u]]; rewrite /= /Itv.num_sem num_real realz/=.
congr (andb _ _).
- by case: l => [[] l |//]; rewrite !bnd_simp intz ?ler_int ?ltr_int.
- by case: u => [[] u |//]; rewrite !bnd_simp intz ?ler_int ?ltr_int.
Qed.

Lemma intmul_inum_subproof (xi ii : Itv.t)
    (x : num_def R xi) (i : num_def int ii)
    (r := itv_real2_subdef mul_itv_subdef xi ii) :
  num_spec r (x%:inum *~ i%:inum).
Proof.
have Pi : num_spec ii (i%:inum%:~R : R) by case: i => /= i; rewrite int_num_spec.
by rewrite -mulrzr -[i%:inum%:~R]/((Itv.Def Pi)%:inum) mul_inum_subproof.
Qed.

Canonical intmul_inum (xi ni : Itv.t) (x : num_def R xi) (n : num_def int ni) :=
  Itv.mk (intmul_inum_subproof x n).

Definition keep_pos_itv_bound_subdef (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b (Posz 0) => BSide b 0
  | BSide _ (Posz (S _)) => BRight 0
  | BSide _ (Negz _) => -oo
  | BInfty _ => -oo
  end.
Arguments keep_pos_itv_bound_subdef /.

Lemma keep_pos_itv_bound_subproof (op : R -> R) (x : R) b :
  {homo op : x / 0 <= x} -> {homo op : x / 0 < x} ->
  (num_itv_bound R b <= BLeft x)%O ->
  (num_itv_bound R (keep_pos_itv_bound_subdef b) <= BLeft (op x))%O.
Proof.
case: b => [[] [] [| b] // | []//] hle hlt; rewrite !bnd_simp.
- exact: hle.
- by move=> blex; apply: le_lt_trans (hlt _ _) => //; apply: lt_le_trans blex.
- exact: hlt.
- by move=> bltx; apply: le_lt_trans (hlt _ _) => //; apply: le_lt_trans bltx.
Qed.

Definition keep_neg_itv_bound_subdef (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b (Posz 0) => BSide b 0
  | BSide _ (Negz _) => BLeft 0
  | BSide _ (Posz _) => +oo
  | BInfty _ => +oo
  end.
Arguments keep_neg_itv_bound_subdef /.

Lemma keep_neg_itv_bound_subproof (op : R -> R) (x : R) b :
  {homo op : x / x <= 0} -> {homo op : x / x < 0} ->
  (BRight x <= num_itv_bound R b)%O ->
  (BRight (op x) <= num_itv_bound R (keep_neg_itv_bound_subdef b))%O.
Proof.
case: b => [[] [[|//] | b] | []//] hge hgt; rewrite !bnd_simp.
- exact: hgt.
- by move=> xltb; apply: hgt; apply: lt_le_trans xltb _; rewrite lerz0.
- exact: hge.
- by move=> xleb; apply: hgt; apply: le_lt_trans xleb _; rewrite ltrz0.
Qed.

Definition inv_itv_subdef (i : interval int) : interval int :=
  let 'Interval l u := i in
  Interval (keep_pos_itv_bound_subdef l) (keep_neg_itv_bound_subdef u).
Arguments inv_itv_subdef /.

Lemma inv_inum_subproof (i : Itv.t) (x : num_def R i)
    (r := itv_real1_subdef inv_itv_subdef i) :
  num_spec r (x%:inum^-1).
Proof.
apply: itv_real1_subproof (Itv.P x).
case: x => x /= _ [l u] /and3P[xr /= lx xu].
rewrite /Itv.num_sem/= realV xr/=; apply/andP; split.
- apply: keep_pos_itv_bound_subproof lx.
  + by move=> ?; rewrite invr_ge0.
  + by move=> ?; rewrite invr_gt0.
- apply: keep_neg_itv_bound_subproof xu.
  + by move=> ?; rewrite invr_le0.
  + by move=> ?; rewrite invr_lt0.
Qed.

Canonical inv_inum (i : Itv.t) (x : num_def R i) :=
  Itv.mk (inv_inum_subproof x).

Definition exprn_itv_subdef (i : interval int) : interval int :=
  let 'Interval l u := i in
  Interval (keep_pos_itv_bound_subdef l) +oo.
Arguments exprn_itv_subdef /.

Lemma exprn_inum_subproof (i : Itv.t) (x : num_def R i) n
    (r := itv_real1_subdef exprn_itv_subdef i) :
  num_spec r (x%:inum ^+ n).
Proof.
apply: (@itv_real1_subproof _ _ (fun x => x^+n) _ _ _ _ (Itv.P x)).
case: x => x /= _ [l u] /and3P[xr /= lx xu].
rewrite /Itv.num_sem realX//=; apply/andP; split=> [|//].
apply: (@keep_pos_itv_bound_subproof (fun x => x^+n)) lx.
- exact: exprn_ge0.
- exact: exprn_gt0.
Qed.

Canonical exprn_inum (i : Itv.t) (x : num_def R i) n :=
  Itv.mk (exprn_inum_subproof x n).

Lemma norm_inum_subproof {V : normedZmodType R} (x : V) :
  num_spec (Itv.Real `[0, +oo[) `|x|.
Proof. by apply/and3P; split; rewrite //= ?normr_real ?bnd_simp ?normr_ge0. Qed.

Canonical norm_inum {V : normedZmodType R} (x : V) :=
  Itv.mk (norm_inum_subproof x).

End NumDomainInstances.

Section RcfInstances.
Context {R : rcfType}.

Lemma sqrt_inum_subproof (i : Itv.t) (x : num_def R i)
    (r := itv_real1_subdef exprn_itv_subdef i) :
  num_spec r (Num.sqrt x%:inum).
Proof.
apply: itv_real1_subproof (Itv.P x).
case: x => x /= _ [l u] /and3P[xr /= lx xu].
rewrite /Itv.num_sem num_real/=; apply/andP; split=> [|//].
apply: keep_pos_itv_bound_subproof lx.
- by move=> ?; rewrite sqrtr_ge0.
- by move=> ?; rewrite sqrtr_gt0.
Qed.

Canonical sqrt_inum (i : Itv.t) (x : num_def R i) :=
  Itv.mk (sqrt_inum_subproof x).

End RcfInstances.

Section NatInstances.
Local Open Scope nat_scope.
Implicit Type (n : nat).

Lemma zeron_inum_subproof : nat_spec (Itv.Real `[0, 0]%Z) 0.
Proof. by []. Qed.

Canonical zeron_snum := Itv.mk zeron_inum_subproof.

Lemma succn_inum_subproof n : nat_spec (Itv.Real `[1, +oo[%Z) n.+1.
Proof. by []. Qed.

Canonical succn_inum n := Itv.mk (succn_inum_subproof n).

Lemma addn_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef add_itv_subdef xi yi) :
  nat_spec r (x%:inum + y%:inum).
Proof.
have Px : num_spec xi (x%:inum%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:inum%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrD.
rewrite -[x%:inum%:R]/((Itv.Def Px)%:inum) -[y%:inum%:R]/((Itv.Def Py)%:inum).
exact: add_inum_subproof.
Qed.

Canonical addn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (addn_inum_subproof x y).

Lemma double_inum_subproof (i : Itv.t) (n : nat_def i)
    (r := itv_real2_subdef add_itv_subdef i i) :
  nat_spec r (n%:inum.*2).
Proof. by rewrite -addnn addn_inum_subproof. Qed.

Canonical double_inum (i : Itv.t) (x : nat_def i) :=
  Itv.mk (double_inum_subproof x).

Lemma muln_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef mul_itv_subdef xi yi) :
  nat_spec r (x%:inum * y%:inum).
Proof.
have Px : num_spec xi (x%:inum%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:inum%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrM.
rewrite -[x%:inum%:R]/((Itv.Def Px)%:inum) -[y%:inum%:R]/((Itv.Def Py)%:inum).
exact: mul_inum_subproof.
Qed.

Canonical muln_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (muln_inum_subproof x y).

Lemma expn_inum_subproof (i : Itv.t) (x : nat_def i) n
    (r := itv_real1_subdef exprn_itv_subdef i) :
  nat_spec r (x%:inum ^ n).
Proof.
have Px : num_spec i (x%:inum%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) natrX -[x%:inum%:R]/((Itv.Def Px)%:inum).
exact: exprn_inum_subproof.
Qed.

Canonical expn_inum (i : Itv.t) (x : nat_def i) n :=
  Itv.mk (expn_inum_subproof x n).

(* TODO: move in mathcomp_extra *)
Lemma natr_min (R' : numDomainType) (m n : nat) :
  (Order.min m n)%:R = Order.min m%:R n%:R :> R'.
Proof. by rewrite !minElt ltr_nat /Order.lt/= -fun_if. Qed.

(* TODO: move in mathcomp_extra *)
Lemma natr_max (R' : numDomainType) (m n : nat) :
  (Order.max m n)%:R = Order.max m%:R n%:R :> R'.
Proof. by rewrite !maxElt ltr_nat /Order.lt/= -fun_if. Qed.

Lemma minn_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef min_itv_subdef xi yi) :
  nat_spec r (minn x%:inum y%:inum).
Proof.
have Px : num_spec xi (x%:inum%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:inum%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) -minEnat natr_min.
rewrite -[x%:inum%:R]/((Itv.Def Px)%:inum) -[y%:inum%:R]/((Itv.Def Py)%:inum).
exact: num_min_inum_subproof.
Qed.

Canonical minn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (minn_inum_subproof x y).

Lemma maxn_inum_subproof (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi)
    (r := itv_real2_subdef max_itv_subdef xi yi) :
  nat_spec r (maxn x%:inum y%:inum).
Proof.
have Px : num_spec xi (x%:inum%:R : int).
  by case: x => /= x; rewrite (@nat_num_spec int).
have Py : num_spec yi (y%:inum%:R : int).
  by case: y => /= y; rewrite (@nat_num_spec int).
rewrite (@nat_num_spec int) -maxEnat natr_max.
rewrite -[x%:inum%:R]/((Itv.Def Px)%:inum) -[y%:inum%:R]/((Itv.Def Py)%:inum).
exact: num_max_inum_subproof.
Qed.

Canonical maxn_inum (xi yi : Itv.t) (x : nat_def xi) (y : nat_def yi) :=
  Itv.mk (maxn_inum_subproof x y).

End NatInstances.

Section Morph.
Context {R : numDomainType} {i : Itv.t}.
Local Notation nR := (num_def R i).
Implicit Types x y : nR.
Local Notation inum := (@inum R (@Itv.num_sem R) i).

Lemma inum_eq : {mono inum : x y / x == y}. Proof. by []. Qed.
Lemma inum_le : {mono inum : x y / (x <= y)%O}. Proof. by []. Qed.
Lemma inum_lt : {mono inum : x y / (x < y)%O}. Proof. by []. Qed.
Lemma inum_min : {morph inum : x y / Order.min x y}.
Proof. by move=> x y; rewrite !minEle inum_le -fun_if. Qed.
Lemma inum_max : {morph inum : x y / Order.max x y}.
Proof. by move=> x y; rewrite !maxEle inum_le -fun_if. Qed.

End Morph.

Section Test1.

Variable R : numDomainType.
Variable x : {i01 R}.

Goal 0%:i01 = 1%:i01 :> {i01 R}.
Proof.
Abort.

Goal (- x%:inum)%:itv = (- x%:inum)%:itv :> {itv R & `[-1, 0]}.
Proof.
Abort.

Goal (1 - x%:inum)%:i01 = x.
Proof.
Abort.

End Test1.

Section Test2.

Variable R : realDomainType.
Variable x y : {i01 R}.

Goal (x%:inum * y%:inum)%:i01 = x%:inum%:i01.
Proof.
Abort.

End Test2.

Module Test3.
Section Test3.
Variable R : realDomainType.

Definition s_of_pq (p q : {i01 R}) : {i01 R} :=
  (1 - ((1 - p%:inum)%:i01%:inum * (1 - q%:inum)%:i01%:inum))%:i01.

Lemma s_of_p0 (p : {i01 R}) : s_of_pq p 0%:i01 = p.
Proof.
apply/val_inj => /=.
by rewrite subr0 mulr1 opprB addrCA subrr addr0.
Qed.

Canonical onem_itv01 (p : {i01 R}) : {i01 R} :=
  @Itv.mk _ _ _ (onem p%:inum) [itv of 1 - p%:inum].

Definition s_of_pq' (p q : {i01 R}) : {i01 R} :=
  (`1- (`1-(p%:inum) * `1-(q%:inum)))%:i01.

End Test3.
End Test3.
