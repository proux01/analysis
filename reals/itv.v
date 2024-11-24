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
(* %:num to cast back from type {itv R & i} to R.                             *)
(* For instance, for x : {i01 R}, we have (1 - x%:num)%:itv : {i01 R}         *)
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
(*                  (see interval.v for notations that can be sused for i).   *)
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
(*        x%:num == explicit cast from {itv R & i} to R.                      *)
(* ```                                                                        *)
(*                                                                            *)
(* ## sign proofs                                                             *)
(* ```                                                                        *)
(*    [itv of x] == proof that x is in interval inferred by x%:itv            *)
(* ```                                                                        *)
(*                                                                            *)
(* ## constructors                                                            *)
(* ```                                                                        *)
(* ItvNum xr lx xu == builds a {itv R & i} from proofs xr : x \in Num.real,   *)
(*                    lx : Itv.map_itv_bound (Itv.num_sem R) l <= BLeft x     *)
(*                    xu : BRight x <= Itv.map_itv_bound (Itv.num_sem R) u    *)
(*                    where x : R with R : numDomainType                      *)
(*                    and l u : itv_bound int                                 *)
(*   ItvReal lx xu == builds a {itv R & i} from proofs                        *)
(*                    lx : Itv.map_itv_bound (Itv.num_sem R) l <= BLeft x     *)
(*                    xu : BRight x <= Itv.map_itv_bound (Itv.num_sem R) u    *)
(*                    where x : R with R : realDomainType                     *)
(*                    and l u : itv_bound int                                 *)
(*     Itv01 x0 x1 == builds a {i01 R} from proofs x0 : 0 <= x and x1 : x <= 1*)
(*                    where x : R with R : numDomainType                      *)
(* ```                                                                        *)
(*                                                                            *)
(* A number of canonical instances are provided for common operations, if     *)
(* your favorite operator is missing, look below for examples on how to add   *)
(* the appropriate Canonical.                                                 *)
(* Also note that all provided instances aren't necessarily optimal,          *)
(* improvements welcome!                                                      *)
(* Canonical instances are also provided according to types, as a             *)
(* fallback when no known operator appears in the expression. Look to top_typ *)
(* below for an example on how to add your favorite type.                     *)
(******************************************************************************)

Reserved Notation "{ 'itv' R & i }"
  (at level 0, R at level 200, i at level 200, format "{ 'itv'  R  &  i }").
Reserved Notation "{ 'i01' R }"
  (at level 0, R at level 200, format "{ 'i01'  R }").

Reserved Notation "x %:itv" (at level 2, format "x %:itv").
Reserved Notation "x %:i01" (at level 2, format "x %:i01").
Reserved Notation "x %:inum" (at level 2, format "x %:inum").
Reserved Notation "x %:num" (at level 2, format "x %:num").

Reserved Notation "[ 'itv' 'of' x ]" (format "[ 'itv' 'of'  x ]").

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
Notation num := r.
Notation "x %:inum" := (r x) (only parsing) : ring_scope.
Notation "x %:num" := (r x) : ring_scope.
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
HB.instance Definition _ : Order.POrder d itv := [POrder of itv by <:].
End POrder.

Section Order.
Variables (R : numDomainType) (i : interval int).
Local Notation nR := (num_def R (Itv.Real i)).

Lemma itv_le_total_subproof : total (<=%O : rel nR).
Proof.
move=> x y; apply: real_comparable.
- by case: x => [x /=/andP[]].
- by case: y => [y /=/andP[]].
Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build ring_display nR
  itv_le_total_subproof.

End Order.

Module TypInstances.

Lemma top_typ_spec T f (x : T) : Itv.spec f Itv.Top x.
Proof. by []. Qed.

Canonical top_typ T f := Itv.Typ (@top_typ_spec T f).

Lemma real_domain_typ_spec (R : realDomainType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. by rewrite /Itv.num_sem/= num_real. Qed.

Canonical real_domain_typ (R : realDomainType) :=
  Itv.Typ (@real_domain_typ_spec R).

Lemma real_field_typ_spec (R : realFieldType) (x : R) :
  num_spec (Itv.Real `]-oo, +oo[) x.
Proof. exact: real_domain_typ_spec. Qed.

Canonical real_field_typ (R : realFieldType) :=
  Itv.Typ (@real_field_typ_spec R).

Lemma nat_typ_spec (x : nat) : nat_spec (Itv.Real `[0, +oo[) x.
Proof. by []. Qed.

Canonical nat_typ := Itv.Typ nat_typ_spec.

Lemma typ_inum_spec (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :
  Itv.spec (@Itv.sort_sem _ xt) i x.
Proof. by move: xt x => []. Qed.

(* This adds _ <- Itv.r ( typ_inum )
   to canonical projections (c.f., Print Canonical Projections
   Itv.r) meaning that if no other canonical instance (with a
   registered head symbol) is found, a canonical instance of
   Itv.typ, like the ones above, will be looked for. *)
Canonical typ_inum (i : Itv.t) (xt : Itv.typ i) (x : Itv.sort xt) :=
  Itv.mk (typ_inum_spec x).

End TypInstances.
Export (canonicals) TypInstances.

Class unify {T} f (x y : T) := Unify : f x y = true.
#[export] Hint Mode unify - - - + : typeclass_instances.
Class unify' {T} f (x y : T) := Unify' : f x y = true.
#[export] Instance unify'P {T} f (x y : T) : unify' f x y -> unify f x y := id.
#[export]
Hint Extern 0 (unify' _ _ _) => vm_compute; reflexivity : typeclass_instances.

Notation unify_itv ix iy := (unify Itv.sub ix iy).

#[export] Instance top_wider_anything i : unify_itv i Itv.Top.
Proof. by case: i. Qed.

#[export] Instance real_wider_anyreal i :
  unify_itv (Itv.Real i) (Itv.Real `]-oo, +oo[).
Proof. by case: i => [l u]; apply/andP; rewrite !bnd_simp. Qed.

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

Lemma map_itv_bound_comp S T U (f : T -> S) (g : U -> T) (b : itv_bound U) :
  Itv.map_itv_bound (f \o g) b = Itv.map_itv_bound f (Itv.map_itv_bound g b).
Proof. by case: b. Qed.

Section NumDomainTheory.
Context {R : numDomainType} {i : Itv.t}.
Implicit Type x : num_def R i.

Lemma intr_le_map_itv_bound (x y : itv_bound int) :
  (num_itv_bound R x <= num_itv_bound R y)%O = (x <= y)%O.
Proof.
by case: x y => [[] x | x] [[] y | y]//=; rewrite !bnd_simp ?ler_int ?ltr_int.
Qed.

Lemma intr_BLeft_le_map_itv_bound (x : itv_bound int) (y : int) :
  (num_itv_bound R x <= BLeft (y%:~R : R))%O = (x <= BLeft y)%O.
Proof.
rewrite -[BLeft y%:~R]/(Itv.map_itv_bound intr (BLeft y)).
by rewrite intr_le_map_itv_bound.
Qed.

Lemma BRight_intr_le_map_itv_bound (x : int) (y : itv_bound int) :
  (BRight (x%:~R : R) <= num_itv_bound R y)%O = (BRight x <= y)%O.
Proof.
rewrite -[BRight x%:~R]/(Itv.map_itv_bound intr (BRight x)).
by rewrite intr_le_map_itv_bound.
Qed.

Lemma subitv_map_itv (x y : Itv.t) : Itv.sub x y ->
  forall z : R, num_spec x z -> num_spec y z.
Proof.
case: x y => [| x] [| y] //= x_sub_y z /andP[rz]; rewrite /Itv.num_sem rz/=.
move: x y x_sub_y => [lx ux] [ly uy] /andP[lel leu] /=.
move=> /andP[lxz zux]; apply/andP; split.
- by apply: le_trans lxz; rewrite intr_le_map_itv_bound ?map_itv_bound_num.
- by apply: le_trans zux _; rewrite intr_le_map_itv_bound ?map_itv_bound_num.
Qed.

Definition empty_itv := Itv.Real `[Posz 1, Posz 0].

Lemma bottom x : unify_itv i empty_itv -> False.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /andP[] /le_trans /[apply]; rewrite ler10.
Qed.

Lemma gt0 x : unify_itv i (Itv.Real `]Posz 0, +oo[) -> 0%R < x%:num :> R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_].
by rewrite /= in_itv/= andbT.
Qed.

Lemma le0F x : unify_itv i (Itv.Real `]Posz 0, +oo[) ->
  x%:num <= 0%R :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /lt_geF.
Qed.

Lemma lt0 x : unify_itv i (Itv.Real `]-oo, Posz 0[) -> x%:num < 0%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge0F x : unify_itv i (Itv.Real `]-oo, Posz 0[) ->
  0%R <= x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma ge0 x : unify_itv i (Itv.Real `[Posz 0, +oo[) -> 0%R <= x%:num :> R.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT.
Qed.

Lemma lt0F x : unify_itv i (Itv.Real `[Posz 0, +oo[) ->
  x%:num < 0%R :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= andbT => /le_gtF.
Qed.

Lemma le0 x : unify_itv i (Itv.Real `]-oo, Posz 0]) -> x%:num <= 0%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma gt0F x : unify_itv i (Itv.Real `]-oo, Posz 0]) ->
  0%R < x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma cmp0 x : unify_itv i (Itv.Real `]-oo, +oo[) -> (0 >=< x%:num).
Proof. by case: i x => [//| i' [x /=/andP[]]]. Qed.

Lemma neq0 x :
  unify (fun ix iy => negb (Itv.sub ix iy)) (Itv.Real `[0%Z, 0%Z]) i ->
  x%:num != 0 :> R.
Proof.
case: i x => [//| [l u] [x /= Px]]; apply: contra => /eqP x0 /=.
move: Px; rewrite x0 => /and3P[_ /= l0 u0]; apply/andP; split.
- by case: l l0 => [[] l /= |//]; rewrite !bnd_simp ?lerz0 ?ltrz0.
- by case: u u0 => [[] u /= |//]; rewrite !bnd_simp ?ler0z ?ltr0z.
Qed.

Lemma eq0F x :
  unify (fun ix iy => negb (Itv.sub ix iy)) (Itv.Real `[0%Z, 0%Z]) i ->
  x%:num == 0 :> R = false.
Proof. by move=> u; apply/negbTE/neq0. Qed.

Lemma lt1 x : unify_itv i (Itv.Real `]-oo, Posz 1[) -> x%:num < 1%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma ge1F x : unify_itv i (Itv.Real `]-oo, Posz 1[) ->
  1%R <= x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma le1 x : unify_itv i (Itv.Real `]-oo, Posz 1]) -> x%:num <= 1%R :> R.
Proof.
by case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=; rewrite in_itv.
Qed.

Lemma gt1F x : unify_itv i (Itv.Real `]-oo, Posz 1]) ->
  1%R < x%:num :> R = false.
Proof.
case: x => x /= /[swap] /subitv_map_itv /[apply] /andP[_] /=.
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma widen_itv_subproof x i' : Itv.sub i i' -> num_spec i' x%:num.
Proof. by case: x => x /= /[swap] /subitv_map_itv; apply. Qed.

Definition widen_itv x i' (uni : unify_itv i i') :=
  Itv.mk (widen_itv_subproof x uni).

Lemma widen_itvE x (uni : unify_itv i i) : @widen_itv x i uni = x.
Proof. exact/val_inj. Qed.

End NumDomainTheory.

Arguments bottom {R i} _ {_}.
Arguments gt0 {R i} _ {_}.
Arguments le0F {R i} _ {_}.
Arguments lt0 {R i} _ {_}.
Arguments ge0F {R i} _ {_}.
Arguments ge0 {R i} _ {_}.
Arguments lt0F {R i} _ {_}.
Arguments le0 {R i} _ {_}.
Arguments gt0F {R i} _ {_}.
Arguments cmp0 {R i} _ {_}.
Arguments neq0 {R i} _ {_}.
Arguments eq0F {R i} _ {_}.
Arguments lt1 {R i} _ {_}.
Arguments ge1F {R i} _ {_}.
Arguments le1 {R i} _ {_}.
Arguments gt1F {R i} _ {_}.
Arguments widen_itv {R i} _ {_ _}.
Arguments widen_itvE {R i} _ {_}.

#[export] Hint Extern 0 (is_true (0%R < _)%R) => solve [apply: gt0] : core.
#[export] Hint Extern 0 (is_true (_ < 0%R)%R) => solve [apply: lt0] : core.
#[export] Hint Extern 0 (is_true (0%R <= _)%R) => solve [apply: ge0] : core.
#[export] Hint Extern 0 (is_true (_ <= 0%R)%R) => solve [apply: le0] : core.
#[export] Hint Extern 0 (is_true (_ \is Num.real)) => solve [apply: cmp0]
  : core.
#[export] Hint Extern 0 (is_true (0%R >=< _)%R) => solve [apply: cmp0] : core.
#[export] Hint Extern 0 (is_true (_ != 0%R)) => solve [apply: neq0] : core.
#[export] Hint Extern 0 (is_true (_ < 1%R)%R) => solve [apply: lt1] : core.
#[export] Hint Extern 0 (is_true (_ <= 1%R)%R) => solve [apply: le1] : core.

Notation "x %:i01" := (widen_itv x%:itv : {i01 _}) (only parsing) : ring_scope.
Notation "x %:i01" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) (Itv.Real `[Posz 0, Posz 1]) _)
  (only printing) : ring_scope.

Local Open Scope ring_scope.

Module Instances.

Section NumDomainInstances.
Context {R : numDomainType}.

Lemma zero_spec : num_spec (Itv.Real `[0, 0]) (0 : R).
Proof. by apply/andP; split; [exact: real0 | rewrite /= in_itv/= lexx]. Qed.

Canonical zero_inum := Itv.mk zero_spec.

Lemma one_spec : num_spec (Itv.Real `[1, 1]) (1 : R).
Proof. by apply/andP; split; [exact: real1 | rewrite /= in_itv/= lexx]. Qed.

Canonical one_inum := Itv.mk one_spec.

Definition opp_itv_bound (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b x => BSide (~~ b) (intZmod.oppz x)
  | BInfty b => BInfty _ (~~ b)
  end.

Lemma opp_itv_ge0 b : (BLeft 0%R <= opp_itv_bound b)%O = (b <= BRight 0%R)%O.
Proof. by case: b => [[] b | []//]; rewrite /= !bnd_simp oppr_ge0. Qed.

Lemma opp_itv_gt0 b : (BRight 0%R <= opp_itv_bound b)%O = (b <= BLeft 0%R)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp ?oppr_ge0 ?oppr_gt0.
Qed.

Lemma opp_itv_boundr (x : R) b :
  (BRight (- x)%R <= num_itv_bound R (opp_itv_bound b))%O
  = (num_itv_bound R b <= BLeft x)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Lemma opp_itv_boundl (x : R) b :
  (num_itv_bound R (opp_itv_bound b) <= BLeft (- x)%R)%O
  = (BRight x <= num_itv_bound R b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Definition opp_itv (i : interval int) : interval int :=
  let: Interval l u := i in Interval (opp_itv_bound u) (opp_itv_bound l).
Arguments opp_itv /.

Lemma opp_spec (i : Itv.t) (x : num_def R i)
    (r := itv_real1_subdef opp_itv i) :
  num_spec r (- x%:num).
Proof.
apply: itv_real1_subproof (Itv.P x).
case: x => x /= _ [l u] /and3P[xr lx xu].
rewrite /Itv.num_sem/= realN xr/=; apply/andP.
by rewrite opp_itv_boundl opp_itv_boundr.
Qed.

Canonical opp_inum (i : Itv.t) (x : num_def R i) := Itv.mk (opp_spec x).

Definition add_itv_boundl (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ true
  end.

Lemma add_itv_boundl_spec (x1 x2 : R) b1 b2 :
  (num_itv_bound R b1 <= BLeft x1)%O -> (num_itv_bound R b2 <= BLeft x2)%O ->
  (num_itv_bound R (add_itv_boundl b1 b2) <= BLeft (x1 + x2)%R)%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr_tmp.
- exact: lerD.
- exact: ler_ltD.
- exact: ltr_leD.
- exact: ltrD.
Qed.

Definition add_itv_boundr (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ false
  end.

Lemma add_itv_boundr_spec (x1 x2 : R) b1 b2 :
  (BRight x1 <= num_itv_bound R b1)%O -> (BRight x2 <= num_itv_bound R b2)%O ->
  (BRight (x1 + x2)%R <= num_itv_bound R (add_itv_boundr b1 b2))%O.
Proof.
case: b1 b2 => [bb1 b1 |//] [bb2 b2 |//].
case: bb1; case: bb2; rewrite /= !bnd_simp mulrzDr_tmp.
- exact: ltrD.
- exact: ltr_leD.
- exact: ler_ltD.
- exact: lerD.
Qed.

Definition add_itv (i1 i2 : interval int) : interval int :=
  let: Interval l1 u1 := i1 in
  let: Interval l2 u2 := i2 in
  Interval (add_itv_boundl l1 l2) (add_itv_boundr u1 u2).
Arguments add_itv /.

Lemma add_spec (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef add_itv xi yi) :
  num_spec r (x%:num + y%:num).
Proof.
apply: itv_real2_subproof (Itv.P x) (Itv.P y).
case: x y => [x /= _] [y /= _] => {xi yi r} -[lx ux] [ly uy]/=.
move=> /andP[xr /=/andP[lxx xux]] /andP[yr /=/andP[lyy yuy]].
rewrite /Itv.num_sem realD//=; apply/andP.
by rewrite add_itv_boundl_spec ?add_itv_boundr_spec.
Qed.

Canonical add_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (add_spec x y).

Variant signb := EqZero | NonNeg | NonPos.

Definition itv_bound_signl (b : itv_bound int) : signb :=
  let: b0 := BLeft 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Definition itv_bound_signr (b : itv_bound int) : signb :=
  let: b0 := BRight 0%Z in
  if b == b0 then EqZero else if (b <= b0)%O then NonPos else NonNeg.

Variant signi := Known of signb | Unknown | Empty.

Definition interval_sign (i : interval int) : signi :=
  let: Interval l u := i in
  match itv_bound_signl l, itv_bound_signr u with
  | EqZero, NonPos
  | NonNeg, EqZero
  | NonNeg, NonPos => Empty
  | EqZero, EqZero => Known EqZero
  | NonPos, EqZero
  | NonPos, NonPos => Known NonPos
  | EqZero, NonNeg
  | NonNeg, NonNeg => Known NonNeg
  | NonPos, NonNeg => Unknown
  end.

Variant interval_sign_spec (l u : itv_bound int) (x : R) : signi -> Set :=
  | ISignEqZero : l = BLeft 0 -> u = BRight 0 -> x = 0 ->
                  interval_sign_spec l u x (Known EqZero)
  | ISignNonNeg : (BLeft 0%:Z <= l)%O -> (BRight 0%:Z < u)%O -> 0 <= x ->
                  interval_sign_spec l u x (Known NonNeg)
  | ISignNonPos : (l < BLeft 0%:Z)%O -> (u <= BRight 0%:Z)%O -> x <= 0 ->
                  interval_sign_spec l u x (Known NonPos)
  | ISignBoth : (l < BLeft 0%:Z)%O -> (BRight 0%:Z < u)%O -> x \in Num.real ->
                interval_sign_spec l u x Unknown.

Lemma interval_signP (l u : itv_bound int) (x : R) :
    (num_itv_bound R l <= BLeft x)%O -> (BRight x <= num_itv_bound R u)%O ->
    x \in Num.real ->
  interval_sign_spec l u x (interval_sign (Interval l u)).
Proof.
move=> + + xr; rewrite /interval_sign/itv_bound_signl/itv_bound_signr.
have [lneg|lpos|->] := ltgtP l; have [uneg|upos|->] := ltgtP u => lx xu.
- apply: ISignNonPos => //; first exact: ltW.
  have:= le_trans xu (eqbRL (intr_le_map_itv_bound _ _) (ltW uneg)).
  by rewrite bnd_simp.
- exact: ISignBoth.
- exact: ISignNonPos.
- have:= (@ltxx _ _ (num_itv_bound R l)).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite intr_le_map_itv_bound (le_trans (ltW uneg)).
- apply: ISignNonNeg => //; first exact: ltW.
  have:= (le_trans (eqbRL (intr_le_map_itv_bound _ _) (ltW lpos)) lx).
  by rewrite bnd_simp.
- have:= (@ltxx _ _ (num_itv_bound R l)).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite intr_le_map_itv_bound ?leBRight_ltBLeft.
- have:= (@ltxx _ _ (num_itv_bound R (BLeft 0%Z))).
  rewrite (le_lt_trans lx) -?leBRight_ltBLeft ?(le_trans xu)//.
  by rewrite intr_le_map_itv_bound -?ltBRight_leBLeft.
- exact: ISignNonNeg.
- apply: ISignEqZero => //.
  by apply/le_anti/andP; move: lx xu; rewrite !bnd_simp.
Qed.

Definition mul_itv_boundl (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BInfty _, _
  | _, BInfty _
  | BLeft 0%Z, _
  | _, BLeft 0%Z => BLeft 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intRing.mulz x1 x2)
  end.

Definition mul_itv_boundr (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BLeft 0%Z, _
  | _, BLeft 0%Z => BLeft 0%Z
  | BRight 0%Z, _
  | _, BRight 0%Z => BRight 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intRing.mulz x1 x2)
  | _, BInfty _
  | BInfty _, _ => +oo%O
  end.

Lemma mul_itv_boundl_spec b1 b2 (x1 x2 : R) :
  (BLeft 0%:Z <= b1 -> BLeft 0%:Z <= b2 ->
   num_itv_bound R b1 <= BLeft x1 ->
   num_itv_bound R b2 <= BLeft x2 ->
   num_itv_bound R (mul_itv_boundl b1 b2) <= BLeft (x1 * x2))%O.
Proof.
move: b1 b2 => [[] b1 | []//] [[] b2 | []//] /=; rewrite 4!bnd_simp.
- set bl := match b1 with 0%Z => _ | _ => _ end.
  have -> : bl = BLeft (b1 * b2).
    rewrite {}/bl; move: b1 b2 => [[|p1]|p1] [[|p2]|p2]; congr BLeft.
    by rewrite mulr0.
  by rewrite bnd_simp intrM -2!(ler0z R); apply: ler_pM.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp// => b1p b2p sx1 sx2.
  + by rewrite mulr_ge0 ?(le_trans _ (ltW sx2)) ?ler0z.
  + rewrite intrM (@lt_le_trans _ _ (b1.+1%:~R * x2)) ?ltr_pM2l//.
    by rewrite ler_pM2r// (le_lt_trans _ sx2) ?ler0z.
- case: b2 => [[|b2] | b2]; rewrite !bnd_simp// => b1p b2p sx1 sx2.
  + by rewrite mulr_ge0 ?(le_trans _ (ltW sx1)) ?ler0z.
  + rewrite intrM (@le_lt_trans _ _ (b1%:~R * x2)) ?ler_wpM2l ?ler0z//.
    by rewrite ltr_pM2r ?(lt_le_trans _ sx2).
- by rewrite -2!(ler0z R) bnd_simp intrM; apply: ltr_pM.
Qed.

Lemma mul_itv_boundrC b1 b2 :
  mul_itv_boundr b1 b2 = mul_itv_boundr b2 b1.
Proof.
by move: b1 b2 => [[] [[|?]|?] | []] [[] [[|?]|?] | []] //=; rewrite mulnC.
Qed.

Lemma mul_itv_boundr_spec b1 b2 (x1 x2 : R) :
  (0 <= x1 -> 0 <= x2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_itv_boundr b1 b2))%O.
Proof.
case: b1 b2 => [b1b b1 | []] [b2b b2 | []] //= x1p x2p; last first.
- case: b2b b2 => -[[|//] | //] _ x20.
  + have:= (@ltxx _ (itv_bound R) (BLeft 0%:~R)).
    by rewrite (lt_le_trans _ x20).
  + have -> : x2 = 0 by apply/le_anti/andP.
    by rewrite mulr0.
- case: b1b b1 => -[[|//] |//] x10 _.
  + have:= (@ltxx _ (itv_bound R) (BLeft 0%Z%:~R)).
    by rewrite (lt_le_trans _ x10).
  + by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
case: b1b b2b => -[]; rewrite -[intRing.mulz]/GRing.mul.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have:= (@ltxx _ R 0); rewrite (le_lt_trans x1p x1b).
  + case: b2 x2b => [[| b2] | b2] => x2b; rewrite bnd_simp.
    * by have:= (@ltxx _ R 0); rewrite (le_lt_trans x2p x2b).
    * by rewrite intrM ltr_pM.
    * have:= (@ltxx _ R 0); rewrite (le_lt_trans x2p)//.
      by rewrite (lt_le_trans x2b) ?lerz0.
  + have:= (@ltxx _ R 0); rewrite (le_lt_trans x1p)//.
    by rewrite (lt_le_trans x1b) ?lerz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have:= (@ltxx _ R 0); rewrite (le_lt_trans x1p x1b).
  + case: b2 x2b => [[| b2] | b2] x2b; rewrite bnd_simp.
    * exact: mulr_ge0_le0.
    * by rewrite intrM (le_lt_trans (ler_wpM2l x1p x2b)) ?ltr_pM2r.
    * have:= (@ltxx _ _ x2).
      by rewrite (le_lt_trans x2b) ?(lt_le_trans _ x2p) ?ltrz0.
  + have:= (@ltxx _ _ x1).
    by rewrite (lt_le_trans x1b) ?(le_trans _ x1p) ?lerz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + case: b2 x2b => [[|b2] | b2] x2b; rewrite bnd_simp.
    * by have:= (@ltxx _ _ x2); rewrite (lt_le_trans x2b).
    * by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
    * have:= (@ltxx _ _ x2).
      by rewrite (lt_le_trans x2b) ?(le_trans _ x2p) ?lerz0.
  + case: b2 x2b => [[|b2] | b2] x2b; rewrite bnd_simp.
    * by have:= (@ltxx _ _ x2); rewrite (lt_le_trans x2b).
    * by rewrite intrM (le_lt_trans (ler_wpM2r x2p x1b)) ?ltr_pM2l.
    * have:= (@ltxx _ _ x2).
      by rewrite (lt_le_trans x2b) ?(le_trans _ x2p) ?lerz0.
  + have:= (@ltxx _ _ x1).
    by rewrite (le_lt_trans x1b) ?(lt_le_trans _ x1p) ?ltrz0.
- case: b1 => [[|b1] | b1]; rewrite !bnd_simp => x1b x2b.
  + by have -> : x1 = 0; [apply/le_anti/andP | rewrite mul0r].
  + case: b2 x2b => [[| b2] | b2] x2b; rewrite bnd_simp.
    * by have -> : x2 = 0; [apply/le_anti/andP | rewrite mulr0].
    * by rewrite intrM ler_pM.
    * have:= (@ltxx _ _ x2).
      by rewrite (le_lt_trans x2b) ?(lt_le_trans _ x2p) ?ltrz0.
  + have:= (@ltxx _ _ x1).
    by rewrite (le_lt_trans x1b) ?(lt_le_trans _ x1p) ?ltrz0.
Qed.

Lemma mul_itv_boundr_BRight b1 b2 :
  (BRight 0%Z <= b1 -> BRight 0%Z <= b2 ->
   BRight 0%Z <= mul_itv_boundr b1 b2)%O.
Proof.
case: b1 b2 => [b1b b1 | []] [b2b b2 | []]//=.
- by case: b1b b2b => -[]; case: b1 b2 => [[|b1] | b1] [[|b2] | b2].
- by case: b1b b1 => -[[] |].
- by case: b2b b2 => -[[] |].
Qed.

Lemma mul_itv_boundr'_spec b1 b2 (x1 x2 : R) :
  (0 <= x1 -> x2 \in Num.real -> BRight 0%Z <= b2 ->
   BRight x1 <= num_itv_bound R b1 ->
   BRight x2 <= num_itv_bound R b2 ->
   BRight (x1 * x2) <= num_itv_bound R (mul_itv_boundr b1 b2))%O.
Proof.
move=> x1ge0 x2r b2ge0 lex1b1 lex2b2.
have /orP[x2ge0 | x2le0] := x2r; first exact: mul_itv_boundr_spec.
have lem0 : (BRight (x1 * x2) <= BRight 0%R)%O.
  by rewrite bnd_simp mulr_ge0_le0 // ltW.
apply: le_trans lem0 _.
rewrite -(mulr0z 1) BRight_intr_le_map_itv_bound.
apply: mul_itv_boundr_BRight => //.
by rewrite -(@BRight_intr_le_map_itv_bound R) (le_trans _ lex1b1).
Qed.

Definition mul_itv (i1 i2 : interval int) : interval int :=
  let: Interval l1 u1 := i1 in
  let: Interval l2 u2 := i2 in
  let: opp := opp_itv_bound in
  let: mull := mul_itv_boundl in
  let: mulr := mul_itv_boundr in
  match interval_sign i1, interval_sign i2 with
  | Empty, _ | _, Empty => `[1, 0]
  | Known EqZero, _ | _, Known EqZero => `[0, 0]
  | Known NonNeg, Known NonNeg =>
      Interval (mull l1 l2) (mulr u1 u2)
  | Known NonPos, Known NonPos =>
      Interval (mull (opp u1) (opp u2)) (mulr (opp l1) (opp l2))
  | Known NonNeg, Known NonPos =>
      Interval (opp (mulr u1 (opp l2))) (opp (mull l1 (opp u2)))
  | Known NonPos, Known NonNeg =>
      Interval (opp (mulr (opp l1) u2)) (opp (mull (opp u1) l2))
  | Known NonNeg, Unknown =>
      Interval (opp (mulr u1 (opp l2))) (mulr u1 u2)
  | Known NonPos, Unknown =>
      Interval (opp (mulr (opp l1) u2)) (mulr (opp l1) (opp l2))
  | Unknown, Known NonNeg =>
      Interval (opp (mulr (opp l1) u2)) (mulr u1 u2)
  | Unknown, Known NonPos =>
      Interval (opp (mulr u1 (opp l2))) (mulr (opp l1) (opp l2))
  | Unknown, Unknown =>
      Interval
        (Order.min (opp (mulr (opp l1) u2)) (opp (mulr u1 (opp l2))))
        (Order.max (mulr (opp l1) (opp l2)) (mulr u1 u2))
  end.
Arguments mul_itv /.

Lemma comparable_num_itv_bound (x y : itv_bound int) :
  (num_itv_bound R x >=< num_itv_bound R y)%O.
Proof.
by case: x y => [[] x | []] [[] y | []]//; apply/orP;
  rewrite !bnd_simp ?ler_int ?ltr_int;
  case: leP => xy; apply/orP => //; rewrite ltW ?orbT.
Qed.

Lemma map_itv_bound_min (x y : itv_bound int) :
  num_itv_bound R (Order.min x y)
  = Order.min (num_itv_bound R x) (num_itv_bound R y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !minEle intr_le_map_itv_bound lexy|].
rewrite minElt -if_neg -comparable_leNgt ?intr_le_map_itv_bound ?ltW//.
exact: comparable_num_itv_bound.
Qed.

Lemma map_itv_bound_max (x y : itv_bound int) :
  num_itv_bound R (Order.max x y)
  = Order.max (num_itv_bound R x) (num_itv_bound R y).
Proof.
have [lexy | ltyx] := leP x y; [by rewrite !maxEle intr_le_map_itv_bound lexy|].
rewrite maxElt -if_neg -comparable_leNgt ?intr_le_map_itv_bound ?ltW//.
exact: comparable_num_itv_bound.
Qed.

Lemma mul_spec (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi)
    (r := itv_real2_subdef mul_itv xi yi) :
  num_spec r (x%:num * y%:num).
Proof.
rewrite {}/r; case: xi yi x y => [//| [xl xu]] [//| [yl yu]].
case=> [x /=/and3P[xr /= xlx xxu]] [y /=/and3P[yr /= yly yyu]].
rewrite -/(interval_sign (Interval xl xu)) -/(interval_sign (Interval yl yu)).
have ns000 : @Itv.num_sem R `[0, 0] 0 by apply/and3P.
have xyr : x * y \in Num.real by exact: realM.
case: (interval_signP xlx xxu xr) => xlb xub xs.
- by rewrite xs mul0r; case: (interval_signP yly yyu yr).
- case: (interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=.
    * exact: mul_itv_boundl_spec xlx yly.
    * exact: mul_itv_boundr_spec xxu yyu.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK -mulrN.
    * rewrite opp_itv_boundl.
      by rewrite mul_itv_boundr_spec ?oppr_ge0// opp_itv_boundr.
    * rewrite opp_itv_boundr.
      rewrite mul_itv_boundl_spec ?opp_itv_boundl//.
      by rewrite opp_itv_ge0.
  + apply/and3P; split=> //=.
    * rewrite  -[x * y]opprK -mulrN opp_itv_boundl.
      rewrite mul_itv_boundr'_spec ?realN ?opp_itv_boundr//.
      by rewrite opp_itv_gt0 ltW.
    * by rewrite mul_itv_boundr'_spec// ltW.
- case: (interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK -mulNr.
    * rewrite opp_itv_boundl.
      by rewrite mul_itv_boundr_spec ?oppr_ge0 ?opp_itv_boundr.
    * rewrite opp_itv_boundr.
      rewrite mul_itv_boundl_spec ?opp_itv_boundl//.
      by rewrite opp_itv_ge0.
  + apply/and3P; split=> //=; rewrite -mulrNN.
    * by rewrite mul_itv_boundl_spec
        ?opp_itv_ge0 ?opp_itv_boundl.
    * by rewrite mul_itv_boundr_spec ?oppr_ge0 ?opp_itv_boundr.
  + apply/and3P; split=> //=; rewrite -[x * y]opprK.
    * rewrite -mulNr opp_itv_boundl.
      rewrite mul_itv_boundr'_spec ?oppr_ge0 ?opp_itv_boundr//.
      exact: ltW.
    * rewrite opprK -mulrNN.
      by rewrite mul_itv_boundr'_spec ?opp_itv_boundr
              ?oppr_ge0 ?realN ?opp_itv_gt0// ltW.
- case: (interval_signP yly yyu yr) => ylb yub ys.
  + by rewrite ys mulr0.
  + apply/and3P; split=> //=; rewrite mulrC mul_itv_boundrC.
    * rewrite -[y * x]opprK -mulrN opp_itv_boundl.
      rewrite mul_itv_boundr'_spec ?oppr_ge0 ?realN
              ?opp_itv_boundr//.
      by rewrite opp_itv_gt0 ltW.
    * by rewrite mul_itv_boundr'_spec// ltW.
  + apply/and3P; split=> //=; rewrite mulrC mul_itv_boundrC.
    * rewrite -[y * x]opprK -mulNr opp_itv_boundl.
      rewrite mul_itv_boundr'_spec ?oppr_ge0 ?opp_itv_boundr//.
      exact: ltW.
    * rewrite -mulrNN mul_itv_boundr'_spec ?oppr_ge0 ?realN
              ?opp_itv_boundr//.
      by rewrite opp_itv_gt0 ltW.
apply/and3P; rewrite xyr/= map_itv_bound_min map_itv_bound_max.
rewrite (comparable_ge_min _ (comparable_num_itv_bound _ _)).
rewrite (comparable_le_max _ (comparable_num_itv_bound _ _)).
case: (comparable_leP xr) => [x0 | /ltW x0]; split=> //.
- apply/orP; right; rewrite -[x * y]opprK -mulrN opp_itv_boundl.
  rewrite mul_itv_boundr'_spec ?realN ?opp_itv_boundr//.
  by rewrite opp_itv_gt0 ltW.
- by apply/orP; right; rewrite mul_itv_boundr'_spec// ltW.
- apply/orP; left; rewrite -[x * y]opprK -mulNr opp_itv_boundl.
  by rewrite mul_itv_boundr'_spec ?oppr_ge0 ?opp_itv_boundr// ltW.
- apply/orP; left; rewrite -mulrNN.
  rewrite mul_itv_boundr'_spec ?oppr_ge0 ?realN ?opp_itv_boundr//.
  by rewrite opp_itv_gt0 ltW.
Qed.

Canonical mul_inum (xi yi : Itv.t) (x : num_def R xi) (y : num_def R yi) :=
  Itv.mk (mul_spec x y).

End NumDomainInstances.

End Instances.
Export (canonicals) Instances.

Section Morph.
Context {R : numDomainType} {i : Itv.t}.
Local Notation nR := (num_def R i).
Implicit Types x y : nR.
Local Notation num := (@num R (@Itv.num_sem R) i).

Lemma num_eq : {mono num : x y / x == y}. Proof. by []. Qed.
Lemma num_le : {mono num : x y / (x <= y)%O}. Proof. by []. Qed.
Lemma num_lt : {mono num : x y / (x < y)%O}. Proof. by []. Qed.
Lemma num_min : {morph num : x y / Order.min x y}.
Proof. by move=> x y; rewrite !minEle num_le -fun_if. Qed.
Lemma num_max : {morph num : x y / Order.max x y}.
Proof. by move=> x y; rewrite !maxEle num_le -fun_if. Qed.

End Morph.

Section MorphReal.
Context {R : numDomainType} {i : interval int}.
Local Notation nR := (num_def R (Itv.Real i)).
Implicit Type x y : nR.
Local Notation num := (@num R (@Itv.num_sem R) i).

Lemma num_le_max a x y :
  a <= Num.max x%:num y%:num = (a <= x%:num) || (a <= y%:num).
Proof. by rewrite -comparable_le_max// real_comparable. Qed.

Lemma num_ge_max a x y :
  Num.max x%:num y%:num <= a = (x%:num <= a) && (y%:num <= a).
Proof. by rewrite -comparable_ge_max// real_comparable. Qed.

Lemma num_le_min a x y :
  a <= Num.min x%:num y%:num = (a <= x%:num) && (a <= y%:num).
Proof. by rewrite -comparable_le_min// real_comparable. Qed.

Lemma num_ge_min a x y :
  Num.min x%:num y%:num <= a = (x%:num <= a) || (y%:num <= a).
Proof. by rewrite -comparable_ge_min// real_comparable. Qed.

Lemma num_lt_max a x y :
  a < Num.max x%:num y%:num = (a < x%:num) || (a < y%:num).
Proof. by rewrite -comparable_lt_max// real_comparable. Qed.

Lemma num_gt_max a x y :
  Num.max x%:num  y%:num < a = (x%:num < a) && (y%:num < a).
Proof. by rewrite -comparable_gt_max// real_comparable. Qed.

Lemma num_lt_min a x y :
  a < Num.min x%:num y%:num = (a < x%:num) && (a < y%:num).
Proof. by rewrite -comparable_lt_min// real_comparable. Qed.

Lemma num_gt_min a x y :
  Num.min x%:num y%:num < a = (x%:num < a) || (y%:num < a).
Proof. by rewrite -comparable_gt_min// real_comparable. Qed.

End MorphReal.

Section ItvNum.
Context (R : numDomainType).
Context (x : R) (l u : itv_bound int).
Context (x_real : x \in Num.real).
Context (l_le_x : (num_itv_bound R l <= BLeft x)%O).
Context (x_le_u : (BRight x <= num_itv_bound R u)%O).
Lemma itvnum_subdef : num_spec (Itv.Real (Interval l u)) x.
Proof. by apply/and3P. Qed.
Definition ItvNum : num_def R (Itv.Real (Interval l u)) := Itv.mk itvnum_subdef.
End ItvNum.

Section ItvReal.
Context (R : realDomainType).
Context (x : R) (l u : itv_bound int).
Context (l_le_x : (num_itv_bound R l <= BLeft x)%O).
Context (x_le_u : (BRight x <= num_itv_bound R u)%O).
Lemma itvreal_subdef : num_spec (Itv.Real (Interval l u)) x.
Proof. by apply/and3P; split; first exact: num_real. Qed.
Definition ItvReal : num_def R (Itv.Real (Interval l u)) :=
  Itv.mk itvreal_subdef.
End ItvReal.

Section Itv01.
Context (R : numDomainType).
Context (x : R) (x_ge0 : 0 <= x) (x_le1 : x <= 1).
Lemma itv01_subdef : num_spec (Itv.Real `[0%Z, 1%Z]) x.
Proof. by apply/and3P; split; rewrite ?bnd_simp// ger0_real. Qed.
Definition Itv01 : num_def R (Itv.Real `[0%Z, 1%Z]) := Itv.mk itv01_subdef.
End Itv01.

Section Test1.

Variable R : numDomainType.
Variable x : {i01 R}.

Goal 0%:i01 = 1%:i01 :> {i01 R}.
Proof.
Abort.

Goal (- x%:num)%:itv = (- x%:num)%:itv :> {itv R & `[-1, 0]}.
Proof.
Abort.

Goal (1 - x%:num)%:i01 = x.
Proof.
Abort.

End Test1.

Section Test2.

Variable R : realDomainType.
Variable x y : {i01 R}.

Goal (x%:num * y%:num)%:i01 = x%:num%:i01.
Proof.
Abort.

End Test2.

Module Test3.
Section Test3.
Variable R : realDomainType.

Definition s_of_pq (p q : {i01 R}) : {i01 R} :=
  (1 - ((1 - p%:num)%:i01%:num * (1 - q%:num)%:i01%:num))%:i01.

Lemma s_of_p0 (p : {i01 R}) : s_of_pq p 0%:i01 = p.
Proof. by apply/val_inj; rewrite /= subr0 mulr1 subKr. Qed.

Canonical onem_itv01 (p : {i01 R}) : {i01 R} :=
  @Itv.mk _ _ _ (onem p%:num) [itv of 1 - p%:num].

Definition s_of_pq' (p q : {i01 R}) : {i01 R} :=
  (`1- (`1-(p%:num) * `1-(q%:num)))%:i01.

End Test3.
End Test3.
