(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import cardinality set_interval mathcomp_extra.
Require Import ereal reals signed topology prodnormedzmodule.

(******************************************************************************)
(* This file extends the topological hierarchy with norm-related notions.     *)
(*                                                                            *)
(* Note that balls in topology.v are not necessarily open, here they are.     *)
(*                                                                            *)
(* * Normed Topological Abelian groups:                                       *)
(*  pseudoMetricNormedZmodType R  == interface type for a normed topological  *)
(*                                   Abelian group equipped with a norm       *)
(*  PseudoMetricNormedZmodule.Mixin nb == builds the mixin for a normed       *)
(*                                   topological Abelian group from the       *)
(*                                   compatibility between the norm and       *)
(*                                   balls; the carrier type must have a      *)
(*                                   normed Zmodule over a numDomainType.     *)
(*                                                                            *)
(* * Normed modules :                                                         *)
(*                normedModType K == interface type for a normed module       *)
(*                                   structure over the numDomainType K.      *)
(*           NormedModMixin normZ == builds the mixin for a normed module     *)
(*                                   from the property of the linearity of    *)
(*                                   the norm; the carrier type must have a   *)
(*                                   pseudoMetricNormedZmodType structure     *)
(*            NormedModType K T m == packs the mixin m to build a             *)
(*                                   normedModType K; T must have canonical   *)
(*                                   pseudoMetricNormedZmodType K and         *)
(*                                   pseudoMetricType structures.             *)
(*  [normedModType K of T for cT] == T-clone of the normedModType K structure *)
(*                                   cT.                                      *)
(*         [normedModType K of T] == clone of a canonical normedModType K     *)
(*                                   structure on T.                          *)
(*                           `|x| == the norm of x (notation from ssrnum).    *)
(*                      ball_norm == balls defined by the norm.               *)
(*                      nbhs_norm == neighborhoods defined by the norm.       *)
(*                    closed_ball == closure of a ball.                       *)
(*   f @`[ a , b ], f @`] a , b [ == notations for images of intervals,       *)
(*                                   intended for continuous, monotonous      *)
(*                                   functions, defined in ring_scope and     *)
(*                                   classical_set_scope respectively as:     *)
(*                  f @`[ a , b ] := `[minr (f a) (f b), maxr (f a) (f b)]%O  *)
(*                  f @`] a , b [ := `]minr (f a) (f b), maxr (f a) (f b)[%O  *)
(*                  f @`[ a , b ] := `[minr (f a) (f b),                      *)
(*                                     maxr (f a) (f b)]%classic              *)
(*                  f @`] a , b [ := `]minr (f a) (f b),                      *)
(*                                     maxr (f a) (f b)[%classic              *)
(*                                                                            *)
(* * Domination notations:                                                    *)
(*              dominated_by h k f F == `|f| <= k * `|h|, near F              *)
(*                  bounded_near f F == f is bounded near F                   *)
(*            [bounded f x | x in A] == f is bounded on A, ie F := globally A *)
(*   [locally [bounded f x | x in A] == f is locally bounded on A             *)
(*                       bounded_set == set of bounded sets.                  *)
(*                                   := [set A | [bounded x | x in A]]        *)
(*                       bounded_fun == set of functions bounded on their     *)
(*                                      whole domain.                         *)
(*                                   := [set f | [bounded f x | x in setT]]   *)
(*                  lipschitz_on f F == f is lipschitz near F                 *)
(*          [lipschitz f x | x in A] == f is lipschitz on A                   *)
(* [locally [lipschitz f x | x in A] == f is locally lipschitz on A           *)
(*               k.-lipschitz_on f F == f is k.-lipschitz near F              *)
(*                  k.-lipschitz_A f == f is k.-lipschitz on A                *)
(*        [locally k.-lipschitz_A f] == f is locally k.-lipschitz on A        *)
(*                   contraction q f == f is q.-lipschitz and q < 1           *)
(*                  is_contraction f == exists q, f is q.-lipschitz and q < 1 *)
(*                                                                            *)
(*                     is_interval E == the set E is an interval              *)
(*                bigcup_ointsub U q == union of open real interval included  *)
(*                                      in U and that contain the rational    *)
(*                                      number q                              *)
(*                           Rhull A == the real interval hull of a set A     *)
(*                         shift x y == y + x                                 *)
(*                          center c := shift (- c)                           *)
(*                                                                            *)
(* * Complete normed modules :                                                *)
(*        completeNormedModType K == interface type for a complete normed     *)
(*                                   module structure over a realFieldType    *)
(*                                   K.                                       *)
(* [completeNormedModType K of T] == clone of a canonical complete normed     *)
(*                                   module structure over K on T.            *)
(*                                                                            *)
(* * Filters :                                                                *)
(*          at_left x, at_right x == filters on real numbers for predicates   *)
(*                                   s.t. nbhs holds on the left/right of x   *)
(*                                                                            *)
(* --> We used these definitions to prove the intermediate value theorem and  *)
(*     the Heine-Borel theorem, which states that the compact sets of R^n are *)
(*     the closed and bounded sets.                                           *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "f @`[ a , b ]" (at level 20, b at level 9,
  format "f  @`[ a ,  b ]").
Reserved Notation "f @`] a , b [" (at level 20, b at level 9,
  format "f  @`] a ,  b [").
Reserved Notation "x ^'+" (at level 3, format "x ^'+").
Reserved Notation "x ^'-" (at level 3, format "x ^'-").
Reserved Notation "+oo_ R" (at level 3, format "+oo_ R").
Reserved Notation "-oo_ R" (at level 3, format "-oo_ R").
Reserved Notation "[ 'bounded' E | x 'in' A ]"
  (at level 0, x name, format "[ 'bounded'  E  |  x  'in'  A ]").
Reserved Notation "k .-lipschitz_on f"
  (at level 2, format "k .-lipschitz_on  f").
Reserved Notation "k .-lipschitz_ A f"
  (at level 2, A at level 0, format "k .-lipschitz_ A  f").
Reserved Notation "k .-lipschitz f" (at level 2, format "k .-lipschitz  f").
Reserved Notation "[ 'lipschitz' E | x 'in' A ]"
  (at level 0, x name, format "[ 'lipschitz'  E  |  x  'in'  A ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma nbhsN (R : numFieldType) (x : R) : nbhs (- x) = -%R @ x.
Proof.
rewrite predeqE => A; split=> //= -[] e e_gt0 xeA; exists e => //= y /=.
  by move=> ?; apply: xeA => //=; rewrite -opprD normrN.
by rewrite -opprD normrN => ?; rewrite -[y]opprK; apply: xeA; rewrite /= opprK.
Qed.

Lemma nbhsNimage (R : numFieldType) (x : R) :
  nbhs (- x) = [set -%R @` A | A in nbhs x].
Proof.
rewrite nbhsN /fmap/=; under eq_set => A do rewrite preimageEinv//= inv_oppr.
by rewrite (eq_imageK opprK opprK).
Qed.

Lemma nearN (R : numFieldType) (x : R) (P : R -> Prop) :
  (\forall y \near - x, P y) <-> \near x, P (- x).
Proof. by rewrite -near_simpl nbhsN. Qed.

Lemma openN (R : numFieldType) (A : set R) :
  open A -> open [set - x | x in A].
Proof.
move=> Aop; rewrite openE => _ [x /Aop x_A <-].
by rewrite /interior nbhsNimage; exists A.
Qed.

Lemma closedN (R : numFieldType) (A : set R) :
  closed A -> closed [set - x | x in A].
Proof.
move=> Acl x clNAx.
suff /Acl : closure A (- x) by exists (- x)=> //; rewrite opprK.
move=> B oppx_B; have : [set - x | x in A] `&` [set - x | x in B] !=set0.
  by apply: clNAx; rewrite -[x]opprK nbhsNimage; exists B.
move=> [y [[z Az oppzey] [t Bt opptey]]]; exists (- y).
by split; [rewrite -oppzey opprK|rewrite -opptey opprK].
Qed.

HB.mixin Record NormedZmod_PseudoMetric_eq (R : numDomainType) T
    of Num.NormedZmodule R T & PseudoMetric R T := {
  pseudo_metric_ball_norm : ball = ball_ (fun x : T => `| x |)
}.

#[short(type="pseudoMetricNormedZmodType")]
HB.structure Definition PseudoMetricNormedZmod (R : numDomainType) :=
  {T of Num.NormedZmodule R T & PseudoMetric R T
   & NormedZmod_PseudoMetric_eq R T}.

Section pseudoMetricnormedzmodule_lemmas.
Context {K : numDomainType} {V : pseudoMetricNormedZmodType K}.

Local Notation ball_norm := (ball_ (@normr K V)).

Lemma ball_normE : ball_norm = ball.
Proof. by rewrite pseudo_metric_ball_norm. Qed.

End pseudoMetricnormedzmodule_lemmas.

(** neighborhoods *)

Section Nbhs'.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
rewrite forallNE notK => exNP.
pose D := [set d : R^o | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosNum d_gt0).
by move: exNP => [e eP]; exists e%:num.
Qed.

Lemma nbhsC (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
  nbhs x (~` P).
Proof. by move=> /ex_ball_sig [e] ?; apply/nbhs_ballP; exists e%:num => /=. Qed.

Lemma nbhsC_ball (x : T) (P : set T) :
  nbhs x (~` P) -> {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
move=> /nbhs_ballP xNP; apply: ex_ball_sig.
by have [_ /posnumP[e] eP /(_ _ eP)] := xNP.
Qed.

Lemma nbhs_ex (x : T) (P : T -> Prop) : nbhs x P ->
  {d : {posnum R} | forall y, ball x d%:num y -> P y}.
Proof.
move=> /nbhs_ballP xP.
pose D := [set d : R^o | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosNum d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

End Nbhs'.

Lemma coord_continuous {K : numFieldType} m n i j :
  continuous (fun M : 'M[K]_(m, n) => M i j).
Proof.
move=> /= M s /= /(nbhs_ballP (M i j)) [e e0 es].
apply/nbhs_ballP; exists e => //= N MN; exact/es/MN.
Qed.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2); apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_spaddl.
Qed.

#[global] Hint Extern 0 (ProperFilter _^') =>
  (apply: Proper_dnbhs_numFieldType) : typeclass_instances.

(** * Some Topology on extended real numbers *)

Definition pinfty_nbhs (R : numFieldType) : set_system R :=
  fun P => exists M, M \is Num.real /\ forall x, M < x -> P x.
Arguments pinfty_nbhs R : clear implicits.
Definition ninfty_nbhs (R : numFieldType) : set_system R :=
  fun P => exists M, M \is Num.real /\ forall x, x < M -> P x.
Arguments ninfty_nbhs R : clear implicits.

Notation "+oo_ R" := (pinfty_nbhs R)
  (only parsing) : ring_scope.
Notation "-oo_ R" := (ninfty_nbhs R)
  (only parsing) : ring_scope.

Notation "+oo" := (pinfty_nbhs _) : ring_scope.
Notation "-oo" := (ninfty_nbhs _) : ring_scope.

Section infty_nbhs_instances.
Context {R : numFieldType}.
Implicit Types r : R.

Global Instance proper_pinfty_nbhs : ProperFilter (pinfty_nbhs R).
Proof.
apply Build_ProperFilter.
  by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltr_addl.
split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
- by exists 0.
- exists (maxr MP MQ); split=> [|x]; first exact: max_real.
  by rewrite comparable_lt_maxl ?real_comparable // => /andP[/gtMP ? /gtMQ].
- by exists M; split => // ? /gtM /sPQ.
Qed.

Global Instance proper_ninfty_nbhs : ProperFilter (ninfty_nbhs R).
Proof.
apply Build_ProperFilter.
  move=> P [M [Mr ltMP]]; exists (M - 1).
  by apply: ltMP; rewrite gtr_addl oppr_lt0.
split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
- by exists 0.
- exists (Num.min MP MQ); split=> [|x]; first exact: min_real.
  by rewrite comparable_lt_minr ?real_comparable // => /andP[/ltMP ? /ltMQ].
- by exists M; split => // x /ltM /sPQ.
Qed.

Lemma nbhs_pinfty_gt r : r \is Num.real -> \forall x \near +oo, r < x.
Proof. by exists r. Qed.

Lemma nbhs_pinfty_ge r : r \is Num.real -> \forall x \near +oo, r <= x.
Proof. by exists r; split => //; apply: ltW. Qed.

Lemma nbhs_ninfty_lt r : r \is Num.real -> \forall x \near -oo, r > x.
Proof. by exists r. Qed.

Lemma nbhs_ninfty_le r : r \is Num.real -> \forall x \near -oo, r >= x.
Proof. by exists r; split => // ?; apply: ltW. Qed.

Lemma nbhs_pinfty_real : \forall x \near +oo, x \is @Num.real R.
Proof. by apply: filterS (nbhs_pinfty_gt (@real0 _)); apply: gtr0_real. Qed.

Lemma nbhs_ninfty_real : \forall x \near -oo, x \is @Num.real R.
Proof. by apply: filterS (nbhs_ninfty_lt (@real0 _)); apply: ltr0_real. Qed.

Lemma pinfty_ex_gt (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m < M & A M.
Proof.
move=> m_real Agt; near (pinfty_nbhs R) => M.
by exists M; near: M => //; apply: nbhs_pinfty_gt.
Unshelve. all: by end_near. Qed.

Lemma pinfty_ex_ge (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m <= M & A M.
Proof.
move=> m_real Agt; near (pinfty_nbhs R) => M.
by exists M; near: M => //; apply: nbhs_pinfty_ge.
Unshelve. all: by end_near. Qed.

Lemma pinfty_ex_gt0 (A : set R) :
  (\forall k \near +oo, A k) -> exists2 M, M > 0 & A M.
Proof. exact: pinfty_ex_gt. Qed.

Lemma near_pinfty_div2 (A : set R) :
  (\forall k \near +oo, A k) -> (\forall k \near +oo, A (k / 2)).
Proof.
move=> [M [Mreal AM]]; exists (M * 2); split; first by rewrite realM.
by move=> x; rewrite -ltr_pdivl_mulr //; exact: AM.
Qed.

End infty_nbhs_instances.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_gt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_ge end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_lt end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_le end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_real end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_real end : core.

#[global] Hint Extern 0 (is_true (_ < ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_gt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_ge end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_lt end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_le end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_real end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_real end : core.

Section cvg_infty_numField.
Context {R : numFieldType}.

Let cvgryPnum {F : set_system R} {FF : Filter F} : [<->
(* 0 *) F --> +oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A <= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A < x;
(* 3 *) \forall A \near +oo, \forall x \near F, A < x;
(* 4 *) \forall A \near +oo, \forall x \near F, A <= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: nbhs_pinfty_ge.
- move=> AF A Areal; near +oo_R => B.
  by near do apply: (@lt_le_trans _ _ B) => //=; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near +oo_R => B.
by near do [apply: Px; apply: (@lt_le_trans _ _ B) => //]; apply: AF.
Unshelve. all: by end_near. Qed.

Let cvgrNyPnum {F : set_system R} {FF : Filter F} : [<->
(* 0 *) F --> -oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A >= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A > x;
(* 3 *) \forall A \near -oo, \forall x \near F, A > x;
(* 4 *) \forall A \near -oo, \forall x \near F, A >= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: nbhs_ninfty_le.
- move=> AF A Areal; near -oo_R => B.
  by near do apply: (@le_lt_trans _ _ B) => //; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near -oo_R => B.
by near do [apply: Px; apply: (@le_lt_trans _ _ B) => //]; apply: AF.
Unshelve. all: end_near. Qed.

Context {T} {F : set_system T} {FF : Filter F}.
Implicit Types f : T -> R.

Lemma cvgryPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Proof. exact: (cvgryPnum 0%N 1%N). Qed.

Lemma cvgryPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A < f x.
Proof. exact: (cvgryPnum 0%N 2%N). Qed.

Lemma cvgryPgty f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A < f x.
Proof. exact: (cvgryPnum 0%N 3%N). Qed.

Lemma cvgryPgey f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A <= f x.
Proof. exact: (cvgryPnum 0%N 4%N). Qed.

Lemma cvgrNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Proof. exact: (cvgrNyPnum 0%N 1%N). Qed.

Lemma cvgrNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A > f x.
Proof. exact: (cvgrNyPnum 0%N 2%N). Qed.

Lemma cvgrNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A > f x.
Proof. exact: (cvgrNyPnum 0%N 3%N). Qed.

Lemma cvgrNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A >= f x.
Proof. exact: (cvgrNyPnum 0%N 4%N). Qed.

Lemma cvgry_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Proof. by rewrite cvgryPger. Qed.

Lemma cvgry_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A < f x.
Proof. by rewrite cvgryPgtr. Qed.

Lemma cvgrNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Proof. by rewrite cvgrNyPler. Qed.

Lemma cvgrNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A > f x.
Proof. by rewrite cvgrNyPltr. Qed.

Lemma cvgNry f : (- f @ F --> +oo) <-> (f @ F --> -oo).
Proof.
rewrite cvgrNyPler cvgryPger; split=> Foo A Areal;
by near do rewrite -ler_opp2 ?opprK; apply: Foo; rewrite rpredN.
Unshelve. all: end_near. Qed.

Lemma cvgNrNy f : (- f @ F --> -oo) <-> (f @ F --> +oo).
Proof. by rewrite -cvgNry opprK. Qed.

End cvg_infty_numField.

Section cvg_infty_realField.
Context {R : realFieldType}.
Context {T} {F : set_system T} {FF : Filter F} (f : T -> R).

Lemma cvgryPge : f @ F --> +oo <-> forall A, \forall x \near F, A <= f x.
Proof.
by rewrite cvgryPger; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgryPgt : f @ F --> +oo <-> forall A, \forall x \near F, A < f x.
Proof.
by rewrite cvgryPgtr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgrNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A >= f x.
Proof.
by rewrite cvgrNyPler; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgrNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A > f x.
Proof.
by rewrite cvgrNyPltr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgry_ge : f @ F --> +oo -> forall A, \forall x \near F, A <= f x.
Proof. by rewrite cvgryPge. Qed.

Lemma cvgry_gt : f @ F --> +oo -> forall A, \forall x \near F, A < f x.
Proof. by rewrite cvgryPgt. Qed.

Lemma cvgrNy_le : f @ F --> -oo -> forall A, \forall x \near F, A >= f x.
Proof. by rewrite cvgrNyPle. Qed.

Lemma cvgrNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A > f x.
Proof. by rewrite cvgrNyPlt. Qed.

End cvg_infty_realField.

Lemma cvgrnyP {R : realType} {T} {F : set_system T} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R) @[n --> F] --> +oo) <-> (f @ F --> \oo).
Proof.
split=> [/cvgryPge|/cvgnyPge] Foo.
  by apply/cvgnyPge => A; near do rewrite -(@ler_nat R); apply: Foo.
apply/cvgryPgey; near=> A; near=> n.
rewrite (le_trans (@ceil_ge R A))// (ler_int _ _ (f n)) [ceil _]intEsign.
by rewrite le_gtF ?expr0 ?mul1r ?lez_nat ?ceil_ge0//; near: n; apply: Foo.
Unshelve. all: by end_near. Qed.

Section ecvg_infty_numField.
Local Open Scope ereal_scope.

Context {R : numFieldType}.

Let cvgeyPnum {F : set_system \bar R} {FF : Filter F} : [<->
(* 0 *) F --> +oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A%:E <= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A%:E < x;
(* 3 *) \forall A \near +oo%R, \forall x \near F, A%:E < x;
(* 4 *) \forall A \near +oo%R, \forall x \near F, A%:E <= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: ereal_nbhs_pinfty_ge.
- move=> AF A Areal; near +oo_R => B.
  by near do rewrite (@lt_le_trans _ _ B%:E) ?lte_fin//; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near +oo_R => B.
by near do [apply: Px; rewrite (@lt_le_trans _ _ B%:E) ?lte_fin//]; apply: AF.
Unshelve. all: end_near. Qed.

Let cvgeNyPnum {F : set_system \bar R} {FF : Filter F} : [<->
(* 0 *) F --> -oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A%:E >= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A%:E > x;
(* 3 *) \forall A \near -oo%R, \forall x \near F, A%:E > x;
(* 4 *) \forall A \near -oo%R, \forall x \near F, A%:E >= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: ereal_nbhs_ninfty_le.
- move=> AF A Areal; near -oo_R => B.
  by near do rewrite (@le_lt_trans _ _ B%:E) ?lte_fin//; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near -oo_R => B.
by near do [apply: Px; rewrite (@le_lt_trans _ _ B%:E) ?lte_fin//]; apply: AF.
Unshelve. all: end_near. Qed.

Context {T} {F : set_system T} {FF : Filter F}.
Implicit Types (f : T -> \bar R) (u : T -> R).

Lemma cvgeyPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Proof. exact: (cvgeyPnum 0%N 1%N). Qed.

Lemma cvgeyPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Proof. exact: (cvgeyPnum 0%N 2%N). Qed.

Lemma cvgeyPgty f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E < f x.
Proof. exact: (cvgeyPnum 0%N 3%N). Qed.

Lemma cvgeyPgey f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E <= f x.
Proof. exact: (cvgeyPnum 0%N 4%N). Qed.

Lemma cvgeNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Proof. exact: (cvgeNyPnum 0%N 1%N). Qed.

Lemma cvgeNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Proof. exact: (cvgeNyPnum 0%N 2%N). Qed.

Lemma cvgeNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E > f x.
Proof. exact: (cvgeNyPnum 0%N 3%N). Qed.

Lemma cvgeNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E >= f x.
Proof. exact: (cvgeNyPnum 0%N 4%N). Qed.

Lemma cvgey_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Proof. by rewrite cvgeyPger. Qed.

Lemma cvgey_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Proof. by rewrite cvgeyPgtr. Qed.

Lemma cvgeNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Proof. by rewrite cvgeNyPler. Qed.

Lemma cvgeNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Proof. by rewrite cvgeNyPltr. Qed.

Lemma cvgNey f : (\- f @ F --> +oo) <-> (f @ F --> -oo).
Proof.
rewrite cvgeNyPler cvgeyPger; split=> Foo A Areal;
by near do rewrite -lee_opp2 ?oppeK; apply: Foo; rewrite rpredN.
Unshelve. all: end_near. Qed.

Lemma cvgNeNy f : (\- f @ F --> -oo) <-> (f @ F --> +oo).
Proof.
by rewrite -cvgNey (_ : \- \- f = f)//; apply/funeqP => x /=; rewrite oppeK.
Qed.

Lemma cvgeryP u : ((u x)%:E @[x --> F] --> +oo) <-> (u @ F --> +oo%R).
Proof.
split=> [/cvgeyPger|/cvgryPger] Foo.
  by apply/cvgryPger => A Ar; near do rewrite -lee_fin; apply: Foo.
by apply/cvgeyPger => A Ar; near do rewrite lee_fin; apply: Foo.
Unshelve. all: end_near. Qed.

Lemma cvgerNyP u : ((u x)%:E @[x --> F] --> -oo) <-> (u @ F --> -oo%R).
Proof.
split=> [/cvgeNyPler|/cvgrNyPler] Foo.
  by apply/cvgrNyPler => A Ar; near do rewrite -lee_fin; apply: Foo.
by apply/cvgeNyPler => A Ar; near do rewrite lee_fin; apply: Foo.
Unshelve. all: end_near. Qed.

End ecvg_infty_numField.

Section ecvg_infty_realField.
Local Open Scope ereal_scope.
Context {R : realFieldType}.
Context {T} {F : set_system T} {FF : Filter F} (f : T -> \bar R).

Lemma cvgeyPge : f @ F --> +oo <-> forall A, \forall x \near F, A%:E <= f x.
Proof.
by rewrite cvgeyPger; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeyPgt : f @ F --> +oo <-> forall A, \forall x \near F, A%:E < f x.
Proof.
by rewrite cvgeyPgtr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A%:E >= f x.
Proof.
by rewrite cvgeNyPler; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A%:E > f x.
Proof.
by rewrite cvgeNyPltr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgey_ge : f @ F --> +oo -> forall A, \forall x \near F, A%:E <= f x.
Proof. by rewrite cvgeyPge. Qed.

Lemma cvgey_gt : f @ F --> +oo -> forall A, \forall x \near F, A%:E < f x.
Proof. by rewrite cvgeyPgt. Qed.

Lemma cvgeNy_le : f @ F --> -oo -> forall A, \forall x \near F, A%:E >= f x.
Proof. by rewrite cvgeNyPle. Qed.

Lemma cvgeNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A%:E > f x.
Proof. by rewrite cvgeNyPlt. Qed.

End ecvg_infty_realField.

Lemma cvgenyP {R : realType} {T} {F : set_system T} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R)%:E @[n --> F] --> +oo%E) <-> (f @ F --> \oo).
Proof. by rewrite cvgeryP cvgrnyP. Qed.

(** ** Modules with a norm *)

HB.mixin Record PseudoMetricNormedZmod_Lmodule_isNormedModule K V
    of PseudoMetricNormedZmod K V & GRing.Lmodule K V := {
  normrZ : forall (l : K) (x : V), `| l *: x | = `| l | * `| x |;
}.

#[short(type="normedModType")]
HB.structure Definition NormedModule (K : numDomainType) :=
  {T of PseudoMetricNormedZmod K T & GRing.Lmodule K T
   & PseudoMetricNormedZmod_Lmodule_isNormedModule K T}.

Section regular_topology.

Variable R : numFieldType.

HB.instance Definition _ := Num.NormedZmodule.on R^o.
HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build R R^o erefl.
HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build R R^o (@normrM _).

End regular_topology.

Module numFieldNormedType.

Section realType.
Variable (R : realType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End realType.

Section rcfType.
Variable (R : rcfType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End rcfType.

Section archiFieldType.
Variable (R : archiFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End archiFieldType.

Section realFieldType.
Variable (R : realFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.RealField.on R.
End realFieldType.

Section numClosedFieldType.
Variable (R : numClosedFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.ClosedField.on R.
End numClosedFieldType.

Section numFieldType.
Variable (R : numFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.NumField.on R.
End numFieldType.

Module Exports. Export numFieldTopology.Exports. HB.reexport. End Exports.

End numFieldNormedType.
Import numFieldNormedType.Exports.

Section NormedModule_numDomainType.
Variables (R : numDomainType) (V : normedModType R).

Lemma normrZV (x : V) : `|x| \in GRing.unit -> `| `| x |^-1 *: x | = 1.
Proof. by move=> nxu; rewrite normrZ normrV// normr_id mulVr. Qed.

End NormedModule_numDomainType.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `normrZ`")]
Notation normmZ := normrZ.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Lemma normfZV (x : V) : x != 0 -> `| `|x|^-1 *: x | = 1.
Proof. by rewrite -normr_eq0 -unitfE => /normrZV->. Qed.

End NormedModule_numFieldType.

Section PseudoNormedZmod_numDomainType.
Variables (R : numDomainType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_ball := (@nbhs_ball _ V).

Local Notation nbhs_norm := (nbhs_ball_ ball_norm).

(* if we do not give the V argument to nbhs, the universally quantified set that
appears inside the notation for cvg_to has type
set (let '{| PseudoMetricNormedZmodule.sort := T |} := V in T) instead of set V,
which causes an inference problem in derive.v *)
Lemma nbhs_nbhs_norm : nbhs_norm = nbhs.
Proof. by rewrite ball_normE funeqE => x; rewrite -filter_from_ballE. Qed.

Lemma nbhs_normP x (P : V -> Prop) : (\near x, P x) <-> nbhs_norm x P.
Proof. by rewrite nbhs_nbhs_norm. Qed.

Lemma nbhs_le_nbhs_norm (x : V) : @nbhs V _ x `=>` nbhs_norm x.
Proof. by move=> P [e e0 subP]; apply/nbhs_normP; exists e. Qed.

Lemma nbhs_norm_le_nbhs x : nbhs_norm x `=>` nbhs x.
Proof. by move=> P /nbhs_normP [e e0 Pxe]; exists e. Qed.

Lemma filter_from_norm_nbhs x :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) = nbhs x.
Proof. by rewrite -nbhs_nbhs_norm ball_normE. Qed.

Lemma nbhs_normE (x : V) (P : V -> Prop) :
  nbhs_norm x P = \near x, P x.
Proof. by rewrite nbhs_nbhs_norm near_simpl. Qed.

Lemma filter_from_normE (x : V) (P : V -> Prop) :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) P = \near x, P x.
Proof. by rewrite filter_from_norm_nbhs. Qed.

Lemma near_nbhs_norm (x : V) (P : V -> Prop) :
  (\forall x \near nbhs_norm x, P x) = \near x, P x.
Proof. exact: nbhs_normE. Qed.

Lemma nbhs_norm_ball_norm x (e : {posnum R}) :
  nbhs_norm x (ball_norm x e%:num).
Proof. by rewrite ball_normE; exists e%:num => /=. Qed.

Lemma nbhs_ball_norm (x : V) (eps : {posnum R}) : nbhs x (ball_norm x eps%:num).
Proof. rewrite -nbhs_nbhs_norm; apply: nbhs_norm_ball_norm. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm/= -opprB normrN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /lt_le_trans; apply. Qed.

Let nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).

Lemma fcvgrPdist_lt {F : set_system V} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Proof. by rewrite -filter_fromP /= !nbhs_simpl. Qed.

Lemma cvgrPdist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| < eps.
Proof. exact: fcvgrPdist_lt. Qed.

Lemma cvgrPdistC_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| < eps.
Proof.
by rewrite cvgrPdist_lt; under eq_forall do under eq_near do rewrite distrC.
Qed.

Lemma cvgr_dist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| < eps.
Proof. by move=> /cvgrPdist_lt. Qed.

Lemma __deprecated__cvg_dist {F : set_system V} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> \forall y' \near F, `|y - y'| < eps.
Proof. exact: cvgr_dist_lt. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgr_dist_lt` or a variation instead")]
Notation cvg_dist := __deprecated__cvg_dist.

Lemma cvgr_distC_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| < eps.
Proof. by move=> /cvgrPdistC_lt. Qed.

Lemma cvgr_dist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr_dist_lt.
Unshelve. all: by end_near. Qed.

Lemma cvgr_distC_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr_distC_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_norm0P {P : V -> Prop} :
  (\forall x \near 0, P x) <->
  filter_from [set e | 0 < e] (fun e => [set y | `|y| < e]) P.
Proof.
rewrite nbhs_normP; split=> -[/= e e0 Pe];
by exists e => // y /=; have /= := Pe y; rewrite distrC subr0.
Qed.

Lemma cvgr0Pnorm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| < eps.
Proof.
by rewrite cvgrPdistC_lt; under eq_forall do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0_norm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| < eps.
Proof. by move=> /cvgr0Pnorm_lt. Qed.

Lemma cvgr0_norm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr0_norm_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs0_lt e : 0 < e -> \forall x \near (0 : V), `|x| < e.
Proof. exact: cvgr0_norm_lt. Qed.

Lemma dnbhs0_lt e : 0 < e -> \forall x \near (0 : V)^', `|x| < e.
Proof. by move=> e_gt0; apply: cvg_within; apply: nbhs0_lt. Qed.

Lemma nbhs0_le e : 0 < e -> \forall x \near (0 : V), `|x| <= e.
Proof. exact: cvgr0_norm_le. Qed.

Lemma dnbhs0_le e : 0 < e -> \forall x \near (0 : V)^', `|x| <= e.
Proof. by move=> e_gt0; apply: cvg_within; apply: nbhs0_le. Qed.

Lemma nbhs_norm_ball x (eps : {posnum R}) : nbhs_norm x (ball x eps%:num).
Proof. rewrite nbhs_nbhs_norm; by apply: nbhsx_ballx. Qed.

Lemma nbhsDl (P : set V) (x y : V) :
  (\forall z \near (x + y), P z) <-> (\near x, P (x + y)).
Proof.
split=> /nbhs_normP[_/posnumP[e]/= Px]; apply/nbhs_normP; exists e%:num => //=.
  by move=> z /= xze; apply: Px; rewrite /= opprD addrACA subrr addr0.
by move=> z /= xyz; rewrite -[z](addrNK y); apply: Px; rewrite /= opprB addrA.
Qed.

Lemma nbhsDr (P : set V) x y :
  (\forall z \near (x + y), P z) <-> (\near y, P (x + y)).
Proof. by rewrite addrC nbhsDl -propeqE; apply: eq_near => ?; rewrite addrC. Qed.

Lemma nbhs0P (P : set V) x : (\near x, P x) <-> (\forall e \near 0, P (x + e)).
Proof. by rewrite -nbhsDr addr0. Qed.

End PseudoNormedZmod_numDomainType.
#[global] Hint Resolve normr_ge0 : core.
Arguments cvgr_dist_lt {_ _ _ F FF}.
Arguments cvgr_distC_lt {_ _ _ F FF}.
Arguments cvgr_dist_le {_ _ _ F FF}.
Arguments cvgr_distC_le {_ _ _ F FF}.
Arguments cvgr0_norm_lt {_ _ _ F FF}.
Arguments cvgr0_norm_le {_ _ _ F FF}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_lt end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_le end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_le end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_le end : core.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgrPdist_lt` or a variation instead")]
Notation cvg_distP := fcvgrPdist_lt.

Section open_closed_sets.
(* TODO: duplicate theory within the subspace topology of Num.real
         in a numDomainType *)
Variable R : realFieldType.

(** Some open sets of [R] *)
Lemma open_lt (y : R) : open [set x : R| x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0. exists (y - x) => // z.
by rewrite /= ltr_distlC addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt : core.

Lemma open_gt (y : R) : open [set x : R | x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /= ltr_distlC opprB addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_gt : core.

Lemma open_neq (y : R) : open [set x : R | x != y].
Proof.
rewrite (_ : mkset _ = [set x | x < y] `|` [set x | x > y]); first exact: openU.
rewrite predeqE => x /=; rewrite eq_le !leNgt negb_and !negbK orbC.
by symmetry; apply (rwP orP).
Qed.

Lemma interval_open a b : ~~ bound_side true a -> ~~ bound_side false b ->
  open [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _.
- have -> : [set x | a < x < b] = [set x | a < x] `&` [set x | x < b].
    by rewrite predeqE => r; rewrite /mkset; split => [/andP[? ?] //|[-> ->]].
  by apply openI; [exact: open_gt | exact: open_lt].
- by under eq_set do rewrite itv_ge// inE.
- by under eq_set do rewrite in_itv andbT/=; exact: open_gt.
- exact: open_lt.
- by rewrite (_ : mkset _ = setT); [exact: openT | rewrite predeqE].
Qed.

(** Some closed sets of [R] *)
(* TODO: we can probably extend these results to numFieldType
   by adding a precondition that y \is Num.real *)

Lemma closed_le (y : R) : closed [set x : R | x <= y].
Proof.
rewrite (_ : mkset _ = ~` [set x | x > y]); first exact: open_closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_ge (y : R) : closed [set x : R | y <= x].
Proof.
rewrite (_ : mkset _ = ~` [set x | x < y]); first exact: open_closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_eq (y : R) : closed [set x : R | x = y].
Proof.
rewrite [X in closed X](_ : (eq^~ _) = ~` (xpredC (eq_op^~ y))).
  by apply: open_closedC; exact: open_neq.
by rewrite predeqE /setC => x /=; rewrite (rwP eqP); case: eqP; split.
Qed.

Lemma interval_closed a b : ~~ bound_side false a -> ~~ bound_side true b ->
  closed [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _;
  do ?by under eq_set do rewrite itv_ge// inE falseE; apply: closed0.
- have -> : `[a, b]%classic = [set x | x >= a] `&` [set x | x <= b].
    by rewrite predeqE => ?; rewrite /= in_itv/=; split=> [/andP[]|[->]].
  by apply closedI; [exact: closed_ge | exact: closed_le].
- by under eq_set do rewrite in_itv andbT/=; exact: closed_ge.
- exact: closed_le.
Qed.

End open_closed_sets.

#[global] Hint Extern 0 (open _) => now apply: open_gt : core.
#[global] Hint Extern 0 (open _) => now apply: open_lt : core.
#[global] Hint Extern 0 (open _) => now apply: open_neq : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_ge : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_le : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_eq : core.

Section at_left_right.
Variable R : numFieldType.

Definition at_left (x : R) := within (fun u => u < x) (nbhs x).
Definition at_right (x : R) := within (fun u => x < u) (nbhs x).
Local Notation "x ^'-" := (at_left x) : classical_set_scope.
Local Notation "x ^'+" := (at_right x) : classical_set_scope.

Global Instance at_right_proper_filter (x : R) : ProperFilter x^'+.
Proof.
apply: Build_ProperFilter' => -[_/posnumP[d] /(_ (x + d%:num / 2))].
apply; last (by rewrite ltr_addl); rewrite /=.
rewrite opprD !addrA subrr add0r normrN normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

Global Instance at_left_proper_filter (x : R) : ProperFilter x^'-.
Proof.
apply: Build_ProperFilter' => -[_ /posnumP[d] /(_ (x - d%:num / 2))].
apply; last (by rewrite ltr_subl_addl ltr_addr); rewrite /=.
rewrite opprD !addrA subrr add0r opprK normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

Lemma nbhs_right0P x (P : set R) :
  (\forall y \near x^'+, P y) <-> \forall e \near 0^'+, P (x + e).
Proof.
rewrite !near_withinE !near_simpl nbhs0P -propeqE.
by apply: (@eq_near _ (nbhs (0 : R))) => y; rewrite ltr_addl.
Qed.

Lemma nbhs_left0P x (P : set R) :
  (\forall y \near x^'-, P y) <-> \forall e \near 0^'+, P (x - e).
Proof.
rewrite !near_withinE !near_simpl nbhs0P; split=> Px.
  rewrite -oppr0 nearN; near=> e; rewrite ltr_opp2 opprK => e_lt0.
  by apply: (near Px) => //; rewrite gtr_addl.
by rewrite -oppr0 nearN; near=> e; rewrite gtr_addl oppr_lt0; apply: (near Px).
Unshelve. all: by end_near. Qed.

Lemma nbhs_right_gt x : \forall y \near x^'+, x < y.
Proof. by rewrite near_withinE; apply: nearW. Qed.

Lemma nbhs_left_lt x : \forall y \near x^'-, y < x.
Proof. by rewrite near_withinE; apply: nearW. Qed.

Lemma nbhs_right_neq x : \forall y \near x^'+, y != x.
Proof. by rewrite near_withinE; apply: nearW => ? /gt_eqF->. Qed.

Lemma nbhs_left_neq x : \forall y \near x^'-, y != x.
Proof. by rewrite near_withinE; apply: nearW => ? /lt_eqF->. Qed.

Lemma nbhs_right_ge x : \forall y \near x^'+, x <= y.
Proof. by rewrite near_withinE; apply: nearW; apply/ltW. Qed.

Lemma nbhs_left_le x : \forall y \near x^'-, y <= x.
Proof. by rewrite near_withinE; apply: nearW => ?; apply/ltW. Qed.

Lemma nbhs_right_lt x z : x < z -> \forall y \near x^'+, y < z.
Proof.
move=> xz; exists (z - x) => //=; first by rewrite subr_gt0.
by move=> y /= + xy; rewrite distrC ?ger0_norm ?subr_ge0 1?ltW// ltr_add2r.
Qed.

Lemma nbhs_right_le x z : x < z -> \forall y \near x^'+, y <= z.
Proof. by move=> xz; near do apply/ltW; apply: nbhs_right_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_gt x z : z < x -> \forall y \near x^'-, z < y.
Proof.
move=> xz; rewrite nbhs_left0P; near do rewrite -ltr_opp2 opprB ltr_subl_addl.
by apply: nbhs_right_lt; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_ge x z : z < x -> \forall y \near x^'-, z <= y.
Proof. by move=> xz; near do apply/ltW; apply: nbhs_left_gt.
Unshelve. all: by end_near. Qed.

End at_left_right.
#[global] Typeclasses Opaque at_left at_right.
Notation "x ^'-" := (at_left x) : classical_set_scope.
Notation "x ^'+" := (at_right x) : classical_set_scope.

Section at_left_right_topologicalType.
Variables (R : numFieldType) (V : topologicalType) (f : R -> V) (x : R).

Lemma cvg_at_right_filter : f z @[z --> x] --> f x -> f z @[z --> x^'+] --> f x.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma cvg_at_left_filter : f z @[z --> x] --> f x -> f z @[z --> x^'-] --> f x.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma cvg_at_right_within : f x @[x --> x^'+] --> f x ->
  f x @[x --> within (fun u => x <= u) (nbhs x)] --> f x.
Proof.
move=> fxr U Ux; rewrite ?near_simpl ?near_withinE; near=> z; rewrite le_eqVlt.
by move/predU1P => [<-|]; [exact: nbhs_singleton | near: z; exact: fxr].
Unshelve. all: by end_near. Qed.

Lemma cvg_at_left_within : f x @[x --> x^'-] --> f x ->
  f x @[x --> within (fun u => u <= x) (nbhs x)] --> f x.
Proof.
move=> fxr U Ux; rewrite ?near_simpl ?near_withinE; near=> z; rewrite le_eqVlt.
by move/predU1P => [->|]; [exact: nbhs_singleton | near: z; exact: fxr].
Unshelve. all: by end_near. Qed.

End at_left_right_topologicalType.

Section at_left_right_pmNormedZmod.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Lemma nbhsr0P (P : set V) x :
  (\forall y \near x, P y) <->
  (\forall e \near 0^'+, forall y, `|x - y| <= e -> P y).
Proof.
rewrite nbhs0P/= near_withinE/= !near_simpl.
split=> /nbhs_norm0P[/= _/posnumP[e] /(_ _) Px]; apply/nbhs_norm0P.
  exists e%:num => //= r /= re yr y xyr; rewrite -[y](addrNK x) addrC.
  by apply: Px; rewrite /= distrC (le_lt_trans _ re)// gtr0_norm.
exists (e%:num / 2) => //= r /= re; apply: (Px (e%:num / 2)) => //=.
   by rewrite gtr0_norm// ltr_pdivr_mulr// ltr_pmulr// ?(ltr_nat _ 1 2).
by rewrite opprD addNKr normrN ltW.
Qed.

Let cvgrP {F : set_system V} {FF : Filter F} (y : V) : [<->
  F --> y;
  forall eps, 0 < eps -> \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| < eps].
Proof.
tfae; first by move=> *; apply: cvgr_dist_le.
- by move=> Fy; near do apply: Fy; apply: nbhs_right_gt.
- move=> Fy; near=> e; near (0:R)^'+ => d; near=> x.
  rewrite (@le_lt_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_lt; near: e; apply: nbhs_right_gt.
- move=> Fy; apply/cvgrPdist_lt => e e_gt0; near (0:R)^'+ => d.
  near=> x; rewrite (@lt_le_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma cvgrPdist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| <= eps.
Proof. exact: (cvgrP _ 0 1)%N. Qed.

Lemma cvgrPdist_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| < eps.
Proof. exact: (cvgrP _ 0 3)%N. Qed.

Lemma cvgrPdist_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| <= eps.
Proof. exact: (cvgrP _ 0 2)%N. Qed.

Lemma cvgrPdistC_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| <= eps.
Proof.
rewrite cvgrPdist_le.
by under [X in X <-> _]eq_forall do under eq_near do rewrite distrC.
Qed.

Lemma cvgrPdistC_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| < eps.
Proof.
by rewrite cvgrPdist_ltp; under eq_near do under eq_near do rewrite distrC.
Qed.

Lemma cvgrPdistC_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| <= eps.
Proof.
by rewrite cvgrPdist_lep; under eq_near do under eq_near do rewrite distrC.
Qed.

Lemma cvgr0Pnorm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| <= eps.
Proof.
rewrite cvgrPdistC_le.
by under [X in X <-> _]eq_forall do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0Pnorm_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| < eps.
Proof.
by rewrite cvgrPdistC_ltp; under eq_near do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0Pnorm_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| <= eps.
Proof.
by rewrite cvgrPdistC_lep; under eq_near do under eq_near do rewrite subr0.
Qed.

Lemma cvgr_norm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| < u.
Proof.
move=> Fy z zy; near (0:R)^'+ => k; near=> x; have : `|f x - y| < k.
  by near: x; apply: cvgr_distC_lt => //; near: k; apply: nbhs_right_gt.
move=> /(le_lt_trans (ler_dist_dist _ _)) /real_ltr_normlW.
rewrite realB// ltr_subl_addl => /(_ _)/lt_le_trans; apply => //.
by rewrite -ler_subr_addl; near: k; apply: nbhs_right_le; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| <= u.
Proof.
by move=> fy u yu; near do apply/ltW; apply: cvgr_norm_lt yu.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_gt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| > u.
Proof.
move=> Fy z zy; near (0:R)^'+ => k; near=> x; have: `|f x - y| < k.
  by near: x; apply: cvgr_distC_lt => //; near: k; apply: nbhs_right_gt.
move=> /(le_lt_trans (ler_dist_dist _ _)); rewrite distrC => /real_ltr_normlW.
rewrite realB// ltr_subl_addl  -ltr_subl_addr => /(_ isT); apply: le_lt_trans.
rewrite ler_subr_addl -ler_subr_addr; near: k; apply: nbhs_right_le.
by rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_ge {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| >= u.
Proof.
by move=> fy u yu; near do apply/ltW; apply: cvgr_norm_gt yu.
Unshelve. all: by end_near. Qed.

Lemma cvgr_neq0 {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> y != 0 -> \forall t \near F, f t != 0.
Proof.
move=> Fy z; near do rewrite -normr_gt0.
by apply: (@cvgr_norm_gt _ _ _ _ y); rewrite // normr_gt0.
Unshelve. all: by end_near. Qed.

End at_left_right_pmNormedZmod.
Arguments cvgr_norm_lt {R V T F FF f}.
Arguments cvgr_norm_le {R V T F FF f}.
Arguments cvgr_norm_gt {R V T F FF f}.
Arguments cvgr_norm_ge {R V T F FF f}.
Arguments cvgr_neq0 {R V T F FF f}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_lt end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_le end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_le end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_le end : core.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_lt end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_neq end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_neq end : core.
#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_lt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.


#[global] Hint Extern 0 (ProperFilter _^'-) =>
  (apply: at_left_proper_filter) : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter _^'+) =>
  (apply: at_right_proper_filter) : typeclass_instances.

Section at_left_rightR.
Variable (R : numFieldType).

Lemma real_cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t < z.
Proof.
move=> yr Fy z zy; near=> x => fxr.
rewrite -(ltr_add2r (- y)) real_ltr_normlW// ?rpredB//.
by near: x; apply: cvgr_distC_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma real_cvgr_le {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real ->  f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t <= z.
Proof.
move=> /real_cvgr_lt/[apply] + ? z0 => /(_ _ z0).
by apply: filterS => ? /[apply]/ltW.
Qed.

Lemma real_cvgr_gt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, y > z -> \forall t \near F, f t \is Num.real -> f t > z.
Proof.
move=> yr Fy z zy; near=> x => fxr.
rewrite -ltr_opp2 -(ltr_add2l y) real_ltr_normlW// ?rpredB//.
by near: x; apply: cvgr_dist_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma real_cvgr_ge {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z < y -> \forall t \near F, f t \is Num.real -> f t >= z.
Proof.
move=> /real_cvgr_gt/[apply] + ? z0 => /(_ _ z0).
by apply: filterS => ? /[apply]/ltW.
Qed.

End at_left_rightR.
Arguments real_cvgr_le {R T F FF f}.
Arguments real_cvgr_lt {R T F FF f}.
Arguments real_cvgr_ge {R T F FF f}.
Arguments real_cvgr_gt {R T F FF f}.

Section realFieldType.
Context (R : realFieldType).

Lemma at_right_in_segment (x : R) (P : set R) :
  (\forall e \near 0^'+, {in `[x - e, x + e], forall x, P x}) <-> (\near x, P x).
Proof.
rewrite nbhsr0P -propeqE; apply: eq_near => y /=.
by rewrite -propeqE; apply: eq_forall => z; rewrite ler_distlC.
Qed.

Lemma cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t < z.
Proof.
move=> Fy z zy; near=> x; rewrite -(ltr_add2r (- y)) ltr_normlW//.
by near: x; apply: cvgr_distC_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_le {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t <= z.
Proof.
by move=> /cvgr_lt + ? z0 => /(_ _ z0); apply: filterS => ?; apply/ltW.
Qed.

Lemma cvgr_gt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, y > z -> \forall t \near F, f t > z.
Proof.
move=> Fy z zy; near=> x; rewrite -ltr_opp2 -(ltr_add2l y) ltr_normlW//.
by near: x; apply: cvgr_dist_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_ge {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z < y -> \forall t \near F, f t >= z.
Proof.
by move=> /cvgr_gt + ? z0 => /(_ _ z0); apply: filterS => ?; apply/ltW.
Qed.

End realFieldType.
Arguments cvgr_le {R T F FF f}.
Arguments cvgr_lt {R T F FF f}.
Arguments cvgr_ge {R T F FF f}.
Arguments cvgr_gt {R T F FF f}.

Definition self_sub (K : numDomainType) (V W : normedModType K)
  (f : V -> W) (x : V * V) : W := f x.1 - f x.2.
Arguments self_sub {K V W} f x /.

Definition fun1 {T : Type} {K : numFieldType} : T -> K := fun=> 1.
Arguments fun1 {T K} x /.

Definition dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set_system T) :=
  F [set x | `|f x| <= k * `|h x|].

Definition strictly_dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set_system T) :=
  F [set x | `|f x| < k * `|h x|].

Lemma sub_dominatedl (T : Type) (K : numDomainType) (V W : pseudoMetricNormedZmodType K)
   (h : T -> V) (k : K) (F G : set_system T) : F `=>` G ->
  (@dominated_by T K V W h k)^~ G `<=` (dominated_by h k)^~ F.
Proof. by move=> FG f; exact: FG. Qed.

Lemma sub_dominatedr (T : Type) (K : numDomainType) (V : pseudoMetricNormedZmodType K)
    (h : T -> V) (k : K) (f g : T -> V) (F : set_system T) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->
   dominated_by h k g F -> dominated_by h k f F.
Proof. by move=> le_fg; apply: filterS2 le_fg => x; apply: le_trans. Qed.

Lemma dominated_by1 {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K} :
  @dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| <= k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma strictly_dominated_by1 {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K} :
  @strictly_dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| < k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma ex_dom_bound {T : Type} {K : numFieldType} {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set_system T) {PF : ProperFilter F}:
  (\forall M \near +oo, dominated_by h M f F) <->
  exists M, dominated_by h M f F.
Proof.
rewrite /dominated_by; split => [/pinfty_ex_gt0[M M_gt0]|[M]] FM.
  by exists M.
have [] := pselect (exists x, (h x != 0) && (`|f x| <= M * `|h x|)); last first.
  rewrite -forallNE => Nex; exists 0; split => //.
  move=> k k_gt0; apply: filterS FM => x /= f_le_Mh.
  have /negP := Nex x; rewrite negb_and negbK f_le_Mh orbF => /eqP h_eq0.
  by rewrite h_eq0 normr0 !mulr0 in f_le_Mh *.
case => x0 /andP[hx0_neq0] /(le_trans (normr_ge0 _)) /ger0_real.
rewrite realrM // ?normr_eq0// => M_real.
exists M; split => // k Mk; apply: filterS FM => x /le_trans/= ->//.
by rewrite ler_wpmul2r// ltW.
Qed.

Lemma ex_strict_dom_bound {T : Type} {K : numFieldType}
    {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set_system T) {PF : ProperFilter F} :
  (\forall x \near F, h x != 0) ->
  (\forall M \near +oo, dominated_by h M f F) <->
   exists M, strictly_dominated_by h M f F.
Proof.
move=> hN0; rewrite ex_dom_bound /dominated_by /strictly_dominated_by.
split => -[] M FM; last by exists M; apply: filterS FM => x /ltW.
exists (M + 1); apply: filterS2 hN0 FM => x hN0 /le_lt_trans/= ->//.
by rewrite ltr_pmul2r ?normr_gt0// ltr_addl.
Qed.

Definition bounded_near {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) :=
  \forall M \near +oo, F [set x | `|f x| <= M].

Lemma boundedE {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K} :
  @bounded_near T K V = fun f F => \forall M \near +oo, dominated_by fun1 M f F.
Proof. by rewrite dominated_by1. Qed.

Lemma sub_boundedr (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (F G : set_system T) : F `=>` G ->
  (@bounded_near T K V)^~ G `<=` bounded_near^~ F.
Proof. by move=> FG f; rewrite /bounded_near; apply: filterS=> M; apply: FG. Qed.

Lemma sub_boundedl (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (f g : T -> V) (F : set_system T) (FF : Filter F) :
 (\forall x \near F, `|f x| <= `|g x|) ->  bounded_near g F -> bounded_near f F.
Proof.
move=> le_fg; rewrite /bounded_near; apply: filterS => M.
by apply: filterS2 le_fg => x; apply: le_trans.
Qed.

Lemma ex_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| <= M].
Proof. by rewrite boundedE ex_dom_bound dominated_by1. Qed.

Lemma ex_strict_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| < M].
Proof.
rewrite boundedE ex_strict_dom_bound ?strictly_dominated_by1//.
by near=> x; rewrite oner_eq0.
Unshelve. all: by end_near. Qed.

Lemma ex_strict_bound_gt0 {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : Filter F}:
  bounded_near f F -> exists2 M, M > 0 & F [set x | `|f x| < M].
Proof.
move=> /pinfty_ex_gt0[M M_gt0 FM]; exists (M + 1); rewrite ?addr_gt0//.
by apply: filterS FM => x /le_lt_trans/= ->//; rewrite ltr_addl.
Qed.

Notation "[ 'bounded' E | x 'in' A ]" :=
  (bounded_near (fun x => E) (globally A)).
Notation bounded_set := [set A | [bounded x | x in A]].
Notation bounded_fun := [set f | [bounded f x | x in setT]].

Lemma bounded_fun_has_ubound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_ubound (range a).
Proof.
move=> [M [Mreal]]/(_ (`|M| + 1)).
rewrite (le_lt_trans (ler_norm _)) ?ltr_addl// => /(_ erefl) aM.
by exists (`|M| + 1) => _ [n _ <-]; rewrite (le_trans (ler_norm _))// aM.
Qed.

Lemma bounded_funN (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> bounded_fun (- a).
Proof.
move=> [M [Mreal aM]]; rewrite /bounded_fun /bounded_near; near=> x => y /= _.
by rewrite normrN; apply: aM.
Unshelve. all: by end_near. Qed.

Lemma bounded_fun_has_lbound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_lbound (range a).
Proof.
move=> /bounded_funN/bounded_fun_has_ubound ba; apply/has_lb_ubN.
by apply: subset_has_ubound ba => _ [_ [n _] <- <-]; exists n.
Qed.

Lemma bounded_funD (T : Type) (R : realFieldType) (a b : T -> R) :
  bounded_fun a -> bounded_fun b -> bounded_fun (a \+ b).
Proof.
move=> [M [Mreal Ma]] [N [Nreal Nb]].
rewrite /bounded_fun/bounded_near; near=> x => y /= _.
rewrite (le_trans (ler_norm_add _ _))// [x]splitr.
by rewrite ler_add// (Ma, Nb)// ltr_pdivl_mulr//;
   near: x; apply: nbhs_pinfty_gt; rewrite ?rpredM ?rpred_nat.
Unshelve. all: by end_near. Qed.

Lemma bounded_locally (T : topologicalType)
    (R : numFieldType) (V : normedModType R) (A : set T) (f : T -> V) :
  [bounded f x | x in A] -> [locally [bounded f x | x in A]].
Proof. by move=> /sub_boundedr AB x Ax; apply: AB; apply: within_nbhsW. Qed.

Notation "k .-lipschitz_on f" :=
  (dominated_by (self_sub id) k (self_sub f)) : type_scope.

Definition sub_klipschitz (K : numFieldType) (V W : normedModType K) (k : K)
           (f : V -> W) (F G : set_system (V * V)) :
  F `=>` G -> k.-lipschitz_on f G -> k.-lipschitz_on f F.
Proof. exact. Qed.

Definition lipschitz_on (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F : set_system (V * V)) :=
  \forall M \near +oo, M.-lipschitz_on f F.

Definition sub_lipschitz (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F G : set_system (V * V)) :
  F `=>` G -> lipschitz_on f G -> lipschitz_on f F.
Proof. by move=> FG; rewrite /lipschitz_on; apply: filterS => M; apply: FG. Qed.

Lemma klipschitzW (K : numFieldType) (V W : normedModType K) (k : K)
      (f : V -> W) (F : set_system (V * V)) {PF : ProperFilter F} :
  k.-lipschitz_on f F -> lipschitz_on f F.
Proof. by move=> f_lip; apply/ex_dom_bound; exists k. Qed.

Notation "k .-lipschitz_ A f" :=
  (k.-lipschitz_on f (globally (A `*` A))) : type_scope.
Notation "k .-lipschitz f" := (k.-lipschitz_setT f) : type_scope.
Notation "[ 'lipschitz' E | x 'in' A ]" :=
  (lipschitz_on (fun x => E) (globally (A `*` A))) : type_scope.
Notation lipschitz f := [lipschitz f x | x in setT].

Lemma lipschitz_set0 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) : [lipschitz f x | x in set0].
Proof. by apply: nearW; rewrite setM0 => ?; apply: globally0. Qed.

Lemma lipschitz_set1 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) (a : V) : [lipschitz f x | x in [set a]].
Proof.
apply: (@klipschitzW _ _ _ `|f a|).
  exact: (@globally_properfilter _ _ (a, a)).
by move=> [x y] /= [] -> ->; rewrite !subrr !normr0 mulr0.
Qed.

Lemma klipschitz_locally (R : numFieldType) (V W : normedModType R) (k : R)
    (f : V -> W) (A : set V) :
  k.-lipschitz_A f -> [locally k.-lipschitz_A f].
Proof. by move=> + x Ax; apply: sub_klipschitz; apply: within_nbhsW. Qed.

Lemma lipschitz_locally (R : numFieldType) (V W : normedModType R)
    (A : set V) (f : V -> W) :
  [lipschitz f x | x in A] -> [locally [lipschitz f x | x in A]].
Proof. by move=> + x Ax; apply: sub_lipschitz; apply: within_nbhsW. Qed.

Lemma lipschitz_id (R : numFieldType) (V : normedModType R) :
  1.-lipschitz (@id V).
Proof. by move=> [/= x y] _; rewrite mul1r. Qed.
Arguments lipschitz_id {R V}.

Section contractions.
Context {R : numDomainType} {X Y : normedModType R} {U : set X} {V : set Y}.

Definition contraction (q : {nonneg R}) (f : {fun U >-> V}) :=
  q%:num < 1 /\ q%:num.-lipschitz_U f.

Definition is_contraction (f : {fun U >-> V}) := exists q, contraction q f.

End contractions.

Lemma contraction_fixpoint_unique {R : realDomainType}
    {X : normedModType R} (U : set X) (f : {fun U >-> U}) (x y : X) :
  is_contraction f -> U x -> U y -> x = f x -> y = f y -> x = y.
Proof.
case => q [q1 ctrfq] Ux Uy fixx fixy; apply/subr0_eq/normr0_eq0/eqP.
have [->|xyneq] := eqVneq x y; first by rewrite subrr normr0.
have xypos : 0 < `|x - y| by rewrite normr_gt0 subr_eq0.
suff : `|x - y| <= q%:num * `|x - y| by rewrite ler_pmull // leNgt q1.
by rewrite [in leLHS]fixx [in leLHS]fixy; exact: (ctrfq (_, _)).
Qed.

Section PseudoNormedZMod_numFieldType.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma norm_hausdorff : hausdorff_space V.
Proof.
rewrite ball_hausdorff => a b ab.
have ab2 : 0 < `|a - b| / 2 by apply divr_gt0 => //; rewrite normr_gt0 subr_eq0.
set r := PosNum ab2; exists (r, r) => /=.
apply/negPn/negP => /set0P[c] []; rewrite -ball_normE /ball_ => acr bcr.
have r22 : r%:num * 2 = r%:num + r%:num.
  by rewrite (_ : 2 = 1 + 1) // mulrDr mulr1.
move: (ltr_add acr bcr); rewrite -r22 (distrC b c).
move/(le_lt_trans (ler_dist_add c a b)).
by rewrite -mulrA mulVr ?mulr1 ?ltxx // unitfE.
Qed.
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

(* TODO: check if the following lemma are indeed useless *)
(*       i.e. where the generic lemma is applied, *)
(*            check that norm_hausdorff is not used in a hard way *)

Lemma norm_closeE (x y : V): close x y = (x = y). Proof. exact: closeE. Qed.
Lemma norm_close_eq (x y : V) : close x y -> x = y. Proof. exact: close_eq. Qed.

Lemma norm_cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : V | F --> x].
Proof. exact: cvg_unique. Qed.

Lemma norm_cvg_eq (x y : V) : x --> y -> x = y. Proof. exact: (@cvg_eq V). Qed.
Lemma norm_lim_id (x : V) : lim (nbhs x) = x. Proof. exact: lim_id. Qed.

Lemma norm_cvg_lim {F} {FF : ProperFilter F} (l : V) : F --> l -> lim F = l.
Proof. exact: (@cvg_lim V). Qed.

Lemma norm_lim_near_cst U {F} {FF : ProperFilter F} (l : V) (f : U -> V) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. exact: lim_near_cst. Qed.

Lemma norm_lim_cst U {F} {FF : ProperFilter F} (k : V) :
   lim ((fun _ : U => k) @ F) = k.
Proof. exact: lim_cst. Qed.

Lemma norm_cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set V) :
  {near F, is_fun f} -> is_subset1 [set x : V | f `@ F --> x].
Proof. exact: cvgi_unique. Qed.

Lemma norm_cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> V -> Prop) (l : V) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof. exact: cvgi_lim. Qed.

Lemma distm_lt_split (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_split _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitr (z x y : V) (e : R) :
  `|z - x| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitr _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitl (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitl _ _ z x y e; rewrite -ball_normE. Qed.

Lemma normm_leW (x : V) (e : R) : e > 0 -> `|x| <= e / 2 -> `|x| < e.
Proof.
by move=> /posnumP[{}e] /le_lt_trans ->//; rewrite [ltRHS]splitr ltr_spaddl.
Qed.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Proof.
by move=> xlt ylt; rewrite -[y]opprK (@distm_lt_split 0) ?subr0 ?opprK ?add0r.
Qed.

Lemma __deprecated__cvg_distW {F : set_system V} {FF : Filter F} (y : V) :
  (forall eps, 0 < eps -> \forall y' \near F, `|y - y'| <= eps) ->
  F --> y.
Proof. by move=> /cvgrPdist_le. Qed.

End PseudoNormedZMod_numFieldType.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgrPdist_le` or a variation instead")]
Notation cvg_distW := __deprecated__cvg_distW.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `norm_cvgi_lim`")]
Notation norm_cvgi_map_lim := norm_cvgi_lim.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Section cvgr_norm_infty.
Variables (I : Type) (F : set_system I) (FF : Filter F) (f : I -> V) (y : V).

Lemma cvgr_norm_lty :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| < M.
Proof. by move=> Fy; near do exact: (cvgr_norm_lt y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_ley :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| <= M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_le y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_gtNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| > M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_gt y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_geNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| >= M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_ge y).
Unshelve. all: by end_near. Qed.

End cvgr_norm_infty.

Lemma __deprecated__cvg_bounded_real {F : set_system V} {FF : Filter F} (y : V) :
  F --> y -> \forall M \near +oo, \forall y' \near F, `|y'| < M.
Proof. exact: cvgr_norm_lty. Qed.

Lemma cvg_bounded {I} {F : set_system I} {FF : Filter F} (f : I -> V) (y : V) :
  f @ F --> y -> bounded_near f F.
Proof. exact: cvgr_norm_ley. Qed.

End NormedModule_numFieldType.
Arguments cvgr_norm_lty {R V I F FF}.
Arguments cvgr_norm_ley {R V I F FF}.
Arguments cvgr_norm_gtNy {R V I F FF}.
Arguments cvgr_norm_geNy {R V I F FF}.
Arguments cvg_bounded {R V I F FF}.
#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgr_norm_lty` or a variation instead")]
Notation cvg_bounded_real := __deprecated__cvg_bounded_real.

Module Export NbhsNorm.
Definition nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).
End NbhsNorm.

(* TODO: generalize to R : numFieldType *)
Section hausdorff.

Lemma Rhausdorff (R : realFieldType) :
  hausdorff_space [the topologicalType of R : Type].
Proof.
move=> x y clxy; apply/eqP; rewrite eq_le.
apply/in_segment_addgt0Pr => _ /posnumP[e].
rewrite in_itv /= -ler_distl; set he := (e%:num / 2)%:pos.
have [z [zx_he yz_he]] := clxy _ _ (nbhsx_ballx x he) (nbhsx_ballx y he).
have := ball_triangle yz_he (ball_sym zx_he).
by rewrite -mulr2n -mulr_natr divfK // => /ltW.
Qed.

Lemma pseudoMetricNormedZModType_hausdorff (R : realFieldType)
    (V : pseudoMetricNormedZmodType R) :
  hausdorff_space V.
Proof.
move=> p q clp_q; apply/subr0_eq/normr0_eq0/Rhausdorff => A B pq_A.
rewrite -(@normr0 _ V) -(subrr p) => pp_B.
suff loc_preim r C : nbhs`|p - r| C ->
    nbhs r ((fun r => `|p - r|) @^-1` C).
  have [r []] := clp_q _ _ (loc_preim _ _ pp_B) (loc_preim _ _ pq_A).
  by exists `|p - r|.
move=> [e egt0 pre_C]; apply: nbhs_le_nbhs_norm; exists e => //= s /= rse.
apply: pre_C; apply: le_lt_trans (ler_dist_dist _ _) _.
by rewrite opprB addrC subrKA distrC.
Qed.

End hausdorff.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @nbhs_normE, @filter_from_normE,
  @near_nbhs_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

Lemma __deprecated__continuous_cvg_dist {R : numFieldType}
  (V W : pseudoMetricNormedZmodType R) (f : V -> W) x l :
  continuous f -> x --> l -> forall e : {posnum R}, `|f l - f x| < e%:num.
Proof. by move=> cf /cvg_eq->// e; rewrite subrr normr0. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="simply use the fact that `(x --> l) -> (x = l)`")]
Notation continuous_cvg_dist := __deprecated__continuous_cvg_dist.

(** ** Matrices *)

Section mx_norm.
Variables (K : numDomainType) (m n : nat).
Implicit Types x y : 'M[K]_(m, n).

Definition mx_norm x : K := (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num.

Lemma mx_normE x : mx_norm x = (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num.
Proof. by []. Qed.

Lemma ler_mx_norm_add x y : mx_norm (x + y) <= mx_norm x + mx_norm y.
Proof.
rewrite !mx_normE [_ <= _%:num]num_le; apply/bigmax_leP.
split=> [|ij _]; first exact: addr_ge0.
rewrite mxE; apply: le_trans (ler_norm_add _ _) _.
by rewrite ler_add// -[leLHS]nngE num_le; exact: le_bigmax.
Qed.

Lemma mx_norm_eq0 x : mx_norm x = 0 -> x = 0.
Proof.
move/eqP; rewrite eq_le -[0]nngE mx_normE num_le => /andP[/bigmax_leP[_ x0] _].
apply/matrixP => i j; rewrite mxE; apply/eqP.
by rewrite -num_abs_eq0 eq_le (x0 (i, j))//= -num_le/=.
Qed.

Lemma mx_norm0 : mx_norm 0 = 0.
Proof.
rewrite /mx_norm (eq_bigr (fun=> 0%R%:nng)) /=.
  by elim/big_ind : _ => // a b; rewrite num_max => -> ->; rewrite maxxx.
by move=> i _; apply val_inj => /=; rewrite mxE normr0.
Qed.

Lemma mx_norm_neq0 x : mx_norm x != 0 -> exists i, mx_norm x = `|x i.1 i.2|.
Proof.
rewrite /mx_norm.
elim/big_ind : _ => [|a b Ha Hb H|/= i _ _]; [by rewrite eqxx| |by exists i].
case: (leP a b) => ab.
+ suff /Hb[i xi] : b%:num != 0 by exists i.
  by apply: contra H => b0; rewrite max_r.
+ suff /Ha[i xi] : a%:num != 0 by exists i.
  by apply: contra H => a0; rewrite max_l // ltW.
Qed.

Lemma mx_norm_natmul x k : mx_norm (x *+ k) = (mx_norm x) *+ k.
Proof.
rewrite [in RHS]/mx_norm; elim: k => [|k ih]; first by rewrite !mulr0n mx_norm0.
rewrite !mulrS; apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite -ih; exact/ler_mx_norm_add.
have [/mx_norm_eq0->|x0] := eqVneq (mx_norm x) 0.
  by rewrite -/(mx_norm 0) -/(mx_norm 0) !(mul0rn,addr0,mx_norm0).
rewrite -/(mx_norm x) -num_abs_le; last by rewrite mx_normE.
apply/bigmax_geP; right => /=.
have [i Hi] := mx_norm_neq0 x0.
exists i => //; rewrite Hi -!mulrS -normrMn mulmxnE.
by rewrite le_eqVlt; apply/orP; left; apply/eqP/val_inj => /=; rewrite normr_id.
Qed.

Lemma mx_normN x : mx_norm (- x) = mx_norm x.
Proof.
congr (_%:nngnum).
by apply eq_bigr => /= ? _; apply/eqP; rewrite mxE -num_eq //= normrN.
Qed.

End mx_norm.

Lemma mx_normrE (K : realDomainType) (m n : nat) (x : 'M[K]_(m, n)) :
  mx_norm x = \big[maxr/0]_ij `|x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
by have [ab|ab] := leP a b; [rewrite max_r | rewrite max_l // ltW].
Qed.

HB.instance Definition _ (K : numDomainType) (m n : nat) :=
  Num.Zmodule_isNormed.Build K 'M[K]_(m, n)
    (@ler_mx_norm_add _ _ _) (@mx_norm_eq0 _ _ _)
    (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Section matrix_NormedModule.
Variables (K : numFieldType) (m n : nat).

Local Lemma ball_gt0 (x y : 'M[K]_(m.+1, n.+1)) e : ball x e y -> 0 < e.
Proof. by move/(_ ord0 ord0); apply: le_lt_trans. Qed.

Lemma mx_norm_ball :
  @ball _ [the pseudoMetricType K of 'M[K]_(m.+1, n.+1)] = ball_ (fun x => `| x |).
Proof.
rewrite /normr /ball_ predeq3E => x e y /=; rewrite mx_normE; split => xey.
- have e_gt0 : 0 < e := ball_gt0 xey.
  move: e_gt0 (e_gt0) xey => /ltW/nonnegP[{}e] e_gt0 xey.
  rewrite num_lt; apply/bigmax_ltP => /=.
  by rewrite -num_lt /=; split => // -[? ?] _; rewrite !mxE; exact: xey.
- have e_gt0 : 0 < e by rewrite (le_lt_trans _ xey).
  move: e_gt0 (e_gt0) xey => /ltW/nonnegP[{}e] e_gt0.
  move=> /(bigmax_ltP _ _ _ (fun _ => _%:sgn)) /= [e0 xey] i j.
  by move: (xey (i, j)); rewrite !mxE; exact.
Qed.

HB.instance Definition _ :=
  NormedZmod_PseudoMetric_eq.Build K 'M[K]_(m.+1, n.+1) mx_norm_ball.

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Proof.
rewrite {1 3}/normr /= !mx_normE
 (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -num_eq /= normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
by rewrite !num_max bE dE maxr_pmulr.
Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build K 'M[K]_(m.+1, n.+1)
    mx_normZ.

End matrix_NormedModule.

(** ** Pairs *)

Section prod_PseudoMetricNormedZmodule.
Context {K : numDomainType} {U V : pseudoMetricNormedZmodType K}.

Lemma ball_prod_normE : ball = ball_ (fun x => `| x : U * V |).
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
rewrite /ball /= /prod_ball -!ball_normE /ball_ /=.
by rewrite comparable_lt_maxl// ?real_comparable//; split=> /andP.
Qed.

Lemma prod_norm_ball :
  @ball _ [the pseudoMetricType K of (U * V)%type] = ball_ (fun x => `|x|).
Proof. by rewrite /= - ball_prod_normE. Qed.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build K (U * V)%type
  prod_norm_ball.

End prod_PseudoMetricNormedZmodule.

Section prod_NormedModule.
Context {K : numDomainType} {U V : normedModType K}.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Proof. by rewrite prod_normE /= !normrZ maxr_pmulr. Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build K (U * V)%type
    prod_norm_scale.

End prod_NormedModule.

Section example_of_sharing.
Variables (K : numDomainType).

Example matrix_triangke m n (M N : 'M[K]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Proof. apply ler_norm_add. Qed.

Example pair_triangle (x y : K * K) : `|x + y| <= `|x| + `|y|.
Proof. apply ler_norm_add. Qed.

End example_of_sharing.

Section prod_NormedModule_lemmas.

Context {T : Type} {K : numDomainType} {U V : normedModType K}.

Lemma fcvgr2dist_ltP {F : set_system U} {G : set_system V}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V) :
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `| (y, z) - (y', z') | < eps.
Proof. exact: fcvgrPdist_lt. Qed.

Lemma cvgr2dist_ltP {I J} {F : set_system I} {G : set_system J}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
Proof.
rewrite fcvgr2dist_ltP; split=> + e e0 => /(_ e e0);
  by rewrite !near_simpl// => ?; rewrite !near_simpl.
Qed.

Lemma cvgr2dist_lt {I J} {F : set_system I} {G : set_system J}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
Proof. by rewrite cvgr2dist_ltP. Qed.

Lemma __deprecated__cvg_dist2 {F : set_system U} {G : set_system V}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `|(y, z) - (y', z')| < eps.
Proof. exact: cvgr2dist_lt. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
note="use `cvgr2dist_lt` or a variant instead")]
Notation cvg_dist2 := __deprecated__cvg_dist2.

End prod_NormedModule_lemmas.
Arguments cvgr2dist_ltP {_ _ _ _ _ F G FF FG}.
Arguments cvgr2dist_lt {_ _ _ _ _ F G FF FG}.

#[deprecated(since="mathcomp-analysis 0.6.0",
note="use `fcvgr2dist_ltP` or a variant instead")]
Notation cvg_dist2P := fcvgr2dist_ltP.

(** Normed vector spaces have some continuous functions *)
(** that are in fact continuous on pseudoMetricNormedZmodType *)
Section NVS_continuity_pseudoMetricNormedZmodType.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=> x; apply/cvgrPdist_lt=> e e0; near do rewrite -opprD normrN.
exact: cvgr_dist_lt.
Unshelve. all: by end_near. Qed.

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/= x y]; apply/cvgrPdist_lt=> _/posnumP[e]; near=> a b => /=.
by rewrite opprD addrACA normm_lt_split.
Unshelve. all: by end_near. Qed.

Lemma natmul_continuous n : continuous (fun x : V => x *+ n).
Proof.
case: n => [|n] x; first exact: cvg_cst.
apply/cvgrPdist_lt=> _/posnumP[e]; near=> a.
by rewrite -mulrnBl normrMn -mulr_natr -ltr_pdivl_mulr.
Unshelve. all: by end_near. Qed.

Lemma norm_continuous : continuous (normr : V -> K).
Proof.
move=> x; apply/cvgrPdist_lt => e e0; apply/nbhs_normP; exists e => //= y.
exact/le_lt_trans/ler_dist_dist.
Qed.

End NVS_continuity_pseudoMetricNormedZmodType.

Section NVS_continuity_normedModType.
Context {K : numFieldType} {V : normedModType K}.

Lemma scale_continuous : continuous (fun z : K * V => z.1 *: z.2).
Proof.
move=> [/= k x]; apply/cvgrPdist_lt => _/posnumP[e]; near +oo_K => M.
near=> l z => /=; have M0 : 0 < M by [].
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normrZ.
  rewrite (@le_lt_trans _ _ (M * `|x - z|)) ?ler_wpmul2r -?ltr_pdivl_mull//.
  by near: z; apply: cvgr_dist_lt; rewrite // mulr_gt0 ?invr_gt0.
rewrite (@le_lt_trans _ _ (`|k - l| * M)) ?ler_wpmul2l -?ltr_pdivl_mulr//.
  by near: z; near: M; apply: cvg_bounded (@cvg_refl _ _).
by near: l; apply: cvgr_dist_lt; rewrite // divr_gt0.
Unshelve. all: by end_near. Qed.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (scale_continuous (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : K => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (scale_continuous (_, _))).
Qed.

(** Continuity of norm *)
End NVS_continuity_normedModType.

Section NVS_continuity_mul.

Context {K : numFieldType}.

Lemma mul_continuous : continuous (fun z : K * K => z.1 * z.2).
Proof. exact: scale_continuous. Qed.

Lemma mulrl_continuous (x : K) : continuous ( *%R x).
Proof. exact: scaler_continuous. Qed.

Lemma mulrr_continuous (y : K) : continuous ( *%R^~ y : K -> K).
Proof. exact: scalel_continuous. Qed.

Lemma inv_continuous (x : K) : x != 0 -> {for x, continuous (@GRing.inv K)}.
Proof.
move=> x_neq0; have nx_gt0 : `|x| > 0 by rewrite normr_gt0.
apply/(@cvgrPdist_ltp _ _ _ (nbhs x)); near (0 : K)^'+ => d. near=> e.
near=> y; have y_neq0 : y != 0 by near: y; apply: (cvgr_neq0 x).
rewrite /= -div1r -[y^-1]div1r -mulNr addf_div// mul1r mulN1r normrM normfV.
rewrite ltr_pdivr_mulr ?normr_gt0 ?mulf_neq0// (@lt_le_trans _ _ (e * d))//.
  by near: y;  apply: cvgr_distC_lt => //; rewrite mulr_gt0.
rewrite ler_pmul2l => //=; rewrite normrM -ler_pdivr_mull//.
near: y; apply: (cvgr_norm_ge x) => //; rewrite ltr_pdivr_mull//.
by near: d; apply: nbhs_right_lt; rewrite mulr_gt0.
Unshelve. all: by end_near. Qed.

End NVS_continuity_mul.

Section cvg_composition_pseudometric.

Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgN f a : f @ F --> a -> - f @ F --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: opp_continuous. Qed.

Lemma cvgNP f a : - f @ F --> - a <-> f @ F --> a.
Proof. by split=> /cvgN//; rewrite !opprK. Qed.

Lemma is_cvgN f : cvg (f @ F) -> cvg (- f @ F).
Proof. by move=> /cvgN /cvgP. Qed.

Lemma is_cvgNE f : cvg ((- f) @ F) = cvg (f @ F).
Proof. by rewrite propeqE; split=> /cvgN; rewrite ?opprK => /cvgP. Qed.

Lemma cvgMn f n a : f @ F --> a -> ((@GRing.natmul _)^~n \o f) @ F --> a *+ n.
Proof. by move=> ?;  apply: continuous_cvg => //; exact: natmul_continuous. Qed.

Lemma is_cvgMn f n : cvg (f @ F) -> cvg (((@GRing.natmul _)^~n \o f) @ F).
Proof. by move=> /cvgMn /cvgP. Qed.

Lemma cvgD f g a b : f @ F --> a -> g @ F --> b -> (f + g) @ F --> a + b.
Proof. by move=> ? ?; apply: continuous2_cvg => //; apply add_continuous. Qed.

Lemma is_cvgD f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f + g @ F).
Proof. by have := cvgP _ (cvgD _ _); apply. Qed.

Lemma cvgB f g a b : f @ F --> a -> g @ F --> b -> (f - g) @ F --> a - b.
Proof. by move=> ? ?; apply: cvgD => //; apply: cvgN. Qed.

Lemma is_cvgB f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f - g @ F).
Proof. by have := cvgP _ (cvgB _ _); apply. Qed.

Lemma is_cvgDlE f g : cvg (g @ F) -> cvg ((f + g) @ F) = cvg (f @ F).
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cvgD; apply.
by move=> /is_cvgB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_cvgDrE f g : cvg (f @ F) -> cvg ((f + g) @ F) = cvg (g @ F).
Proof. by rewrite addrC; apply: is_cvgDlE. Qed.

Lemma cvg_sub0 f g a : (f - g) @ F --> (0 : V) -> g @ F --> a -> f @ F --> a.
Proof.
by move=> Cfg Cg; have := cvgD Cfg Cg; rewrite subrK add0r; apply.
Qed.

Lemma cvg_zero f a : (f - cst a) @ F --> (0 : V) -> f @ F --> a.
Proof. by move=> Cfa; apply: cvg_sub0 Cfa (cvg_cst _). Qed.

Lemma cvg_norm f a : f @ F --> a -> `|f x| @[x --> F] --> (`|a| : K).
Proof. by apply: continuous_cvg; apply: norm_continuous. Qed.

Lemma is_cvg_norm f : cvg (f @ F) -> cvg ((Num.norm \o f : T -> K) @ F).
Proof. by have := cvgP _ (cvg_norm _); apply. Qed.

Lemma norm_cvg0P f : `|f x| @[x --> F] --> 0 <-> f @ F --> 0.
Proof.
split; last by move=> /cvg_norm; rewrite normr0.
move=> f0; apply/cvgr0Pnorm_lt => e e_gt0.
by near do rewrite -normr_id; apply: cvgr0_norm_lt.
Unshelve. all: by end_near. Qed.

Lemma norm_cvg0 f : `|f x| @[x --> F] --> 0 -> f @ F --> 0.
Proof. by rewrite norm_cvg0P. Qed.

End cvg_composition_pseudometric.

Lemma __deprecated__cvg_dist0 {U} {K : numFieldType} {V : normedModType K}
  {F : set_system U} {FF : Filter F} (f : U -> V) :
  (fun x => `|f x|) @ F --> (0 : K)
  -> f @ F --> (0 : V).
Proof. exact: norm_cvg0. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
 note="renamed to `norm_cvg0` and generalized to `pseudoMetricNormedZmodType`")]
Notation cvg_dist0 := __deprecated__cvg_dist0.

Section cvg_composition_normed.
Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgZ s f k a : s @ F --> k -> f @ F --> a ->
                     s x *: f x @[x --> F] --> k *: a.
Proof. by move=> ? ?; apply: continuous2_cvg => //; apply scale_continuous. Qed.

Lemma is_cvgZ s f : cvg (s @ F) ->
  cvg (f @ F) -> cvg ((fun x => s x *: f x) @ F).
Proof. by have := cvgP _ (cvgZ _ _); apply. Qed.

Lemma cvgZl s k a : s @ F --> k -> s x *: a @[x --> F] --> k *: a.
Proof. by move=> ?; apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZl s a : cvg (s @ F) -> cvg ((fun x => s x *: a) @ F).
Proof. by have := cvgP _ (cvgZl  _); apply. Qed.

Lemma cvgZr k f a : f @ F --> a -> k \*: f @ F --> k *: a.
Proof. apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZr k f : cvg (f @ F) -> cvg (k *: f  @ F).
Proof. by have := cvgP _ (cvgZr  _); apply. Qed.

Lemma is_cvgZrE k f : k != 0 -> cvg (k *: f @ F) = cvg (f @ F).
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@cvgZr k^-1)|/(@cvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

End cvg_composition_normed.

Section cvg_composition_field.
Context {K : numFieldType}  {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma cvgV f a : a != 0 -> f @ F --> a -> f\^-1 @ F --> a^-1.
Proof.
by move=> k_neq0 f_cvg; apply: continuous_cvg => //; apply: inv_continuous.
Qed.

Lemma cvgVP f a : a != 0 -> f\^-1 @ F --> a^-1 <-> f @ F --> a.
Proof.
move=> aN0; split=> /(cvgV _); last exact.
by rewrite invrK invr_eq0 inv_funK; apply.
Qed.

Lemma is_cvgV f : lim (f @ F) != 0 -> cvg (f @ F) -> cvg (f\^-1 @ F).
Proof. by move=> /cvgV cvf /cvf /cvgP. Qed.

Lemma cvgM f g a b : f @ F --> a -> g @ F --> b -> (f \* g) @ F --> a * b.
Proof. exact: cvgZ. Qed.

Lemma cvgMl f a b : f @ F --> a -> (f x * b) @[x --> F] --> a * b.
Proof. exact: cvgZl. Qed.

Lemma cvgMr g a b : g @ F --> b -> (a * g x) @[x --> F] --> a * b.
Proof. exact: cvgZr. Qed.

Lemma is_cvgM f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZ. Qed.

Lemma is_cvgMr g a (f := fun=> a) : cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZr. Qed.

Lemma is_cvgMrE g a (f := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (g @ F).
Proof. exact: is_cvgZrE. Qed.

Lemma is_cvgMl f a (g := fun=> a) : cvg (f @ F) -> cvg (f \* g @ F).
Proof.
move=> f_cvg; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMr.
Qed.

Lemma is_cvgMlE f a (g := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (f @ F).
Proof.
move=> a_neq0; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMrE.
Qed.

End cvg_composition_field.

Section limit_composition_pseudometric.

Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limN f : cvg (f @ F) -> lim (- f @ F) = - lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgN. Qed.

Lemma limD f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f + g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgD. Qed.

Lemma limB f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f - g @ F) = lim (f @ F) - lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgB. Qed.

Lemma lim_norm f : cvg (f @ F) -> lim ((fun x => `|f x| : K) @ F) = `|lim (f @ F)|.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_norm. Qed.

End limit_composition_pseudometric.

Section limit_composition_normed.

Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limZ s f : cvg (s @ F) -> cvg (f @ F) ->
   lim ((fun x => s x *: f x) @ F) = lim (s @ F) *: lim (f @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgZ. Qed.

Lemma limZl s a : cvg (s @ F) ->
   lim ((fun x => s x *: a) @ F) = lim (s @ F) *: a.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZl. Qed.

Lemma limZr k f : cvg (f @ F) -> lim (k *: f @ F) = k *: lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZr. Qed.

End limit_composition_normed.

Section limit_composition_field.

Context {K : numFieldType} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K).

Lemma limM f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgM. Qed.

End limit_composition_field.

Section cvg_composition_field_proper.

Context {K : numFieldType}  {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma limV f : lim (f @ F) != 0 -> lim (f\^-1 @ F) = (lim (f @ F))^-1.
Proof.
by move=> ?; apply: cvg_lim => //; apply: cvgV => //; apply: cvgNpoint.
Qed.

Lemma is_cvgVE f : lim (f @ F) != 0 -> cvg (f\^-1 @ F) = cvg (f @ F).
Proof.
move=> ?; apply/propeqP; split=> /is_cvgV; last exact.
by rewrite inv_funK; apply; rewrite limV ?invr_eq0//.
Qed.

End cvg_composition_field_proper.

Section ProperFilterRealType.
Context {T : Type} {F : set_system T} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g h : T -> R) (a b : R).

Lemma cvgr_to_ge f a b : f @ F --> a -> (\near F, b <= f F) -> b <= a.
Proof. by move=> /[swap]/(closed_cvg _ (@closed_ge _ b))/[apply]. Qed.

Lemma cvgr_to_le f a b : f @ F --> a -> (\near F, f F <= b) -> a <= b.
Proof. by move=> /[swap]/(closed_cvg _ (@closed_le _ b))/[apply]. Qed.

Lemma limr_ge x f : cvg (f @ F) -> (\near F, x <= f F) -> x <= lim (f @ F).
Proof. exact: cvgr_to_ge. Qed.

Lemma limr_le x f : cvg (f @ F) -> (\near F, x >= f F) -> x >= lim (f @ F).
Proof. exact: cvgr_to_le. Qed.

Lemma __deprecated__cvg_gt_ge (u : T -> R) a b :
  u @ F --> b -> a < b -> \forall n \near F, a <= u n.
Proof. by move=> ?; apply: cvgr_ge. Qed.

Lemma __deprecated__cvg_lt_le (u : T -> R) c b :
  u @ F --> b -> b < c -> \forall n \near F, u n <= c.
Proof. by move=> ?; apply: cvgr_le. Qed.

End ProperFilterRealType.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgr_ge` and generalized to a `Filter`")]
Notation cvg_gt_ge := __deprecated__cvg_gt_ge.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgr_le` and generalized to a `Filter`")]
Notation cvg_lt_le_:= __deprecated__cvg_lt_le.

Section local_continuity.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Implicit Types (f g : T -> V) (s t : T -> K) (x : T) (k : K) (a : V).

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Proof. by move=> ?; apply: cvgN. Qed.

Lemma continuousD f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f + g)}.
Proof. by move=> f_cont g_cont; apply: cvgD. Qed.

Lemma continuousB f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f - g)}.
Proof. by move=> f_cont g_cont; apply: cvgB. Qed.

Lemma continuousZ s f x :
  {for x, continuous s} -> {for x, continuous f} ->
  {for x, continuous (fun x => s x *: f x)}.
Proof. by move=> ? ?; apply: cvgZ. Qed.

Lemma continuousZr f k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; apply: cvgZr. Qed.

Lemma continuousZl s a x :
  {for x, continuous s} -> {for x, continuous (fun z => s z *: a)}.
Proof. by move=> ?; apply: cvgZl. Qed.

Lemma continuousM s t x :
  {for x, continuous s} -> {for x, continuous t} ->
  {for x, continuous (s * t)}.
Proof. by move=> f_cont g_cont; apply: cvgM. Qed.

Lemma continuousV s x : s x != 0 ->
  {for x, continuous s} -> {for x, continuous (fun x => (s x)^-1%R)}.
Proof. by move=> ?; apply: cvgV. Qed.

End local_continuity.

Section nbhs_ereal.
Context {R : numFieldType} (P : \bar R -> Prop).

Lemma nbhs_EFin (x : R) : (\forall y \near x%:E, P y) <-> \near x, P x%:E.
Proof. done. Qed.

Lemma nbhs_ereal_pinfty :
  (\forall x \near +oo%E, P x) <-> [/\ P +oo%E & \forall x \near +oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.

Lemma nbhs_ereal_ninfty :
  (\forall x \near -oo%E, P x) <-> [/\ P -oo%E & \forall x \near -oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.
End nbhs_ereal.

Section cvg_fin.
Context {R : numFieldType}.

Section filter.
Context {F : set_system \bar R} {FF : Filter F}.

Lemma fine_fcvg a : F --> a%:E -> fine @ F --> a.
Proof.
move=> /(_ _)/= Fa; apply/cvgrPdist_lt=> // _/posnumP[e]; rewrite near_simpl.
by apply: Fa; apply/nbhs_EFin => /=; apply: (@cvgr_dist_lt _ _ _ (nbhs a)).
(* BUG: using cvgr_dist_lt without (nbhs _) expands the definition of nbhs, *)
(*    so that it is not recognized as a filter anymore *)
Qed.

Lemma fcvg_is_fine a : F --> a%:E -> \near F, F \is a fin_num.
Proof. by apply; apply/nbhs_EFin; near=> x. Unshelve. all: by end_near. Qed.

End filter.

Section limit.
Context {I : Type} {F : set_system I} {FF : Filter F} (f : I -> \bar R).

Lemma fine_cvg a : f @ F --> a%:E -> fine \o f @ F --> a.
Proof. exact: fine_fcvg. Qed.

Lemma cvg_is_fine a : f @ F --> a%:E -> \near F, f F \is a fin_num.
Proof. exact: fcvg_is_fine. Qed.

Lemma cvg_EFin a : (\near F, f F \is a fin_num) -> fine \o f @ F --> a ->
  f @ F --> a%:E.
Proof.
move=> Ffin Fa P/= /nbhs_EFin /Fa; rewrite !near_simpl.
by apply: filterS2 Ffin => x /fineK->.
Qed.

Lemma fine_cvgP a :
   f @ F --> a%:E <-> (\near F, f F \is a fin_num) /\ fine \o f @ F --> a.
Proof.
by split;[split;[exact: (@cvg_is_fine a)|exact: fine_cvg]|case; apply: cvg_EFin].
Qed.

Lemma neq0_fine_cvgP a : a != 0 -> f @ F --> a%:E <-> fine \o f @ F --> a.
Proof.
move=> a_neq0; split=> [|Fa]; first exact: fine_cvg.
apply: cvg_EFin=> //; near (0 : R)^'+ => e.
have lea : e <= `|a| by near: e; apply: nbhs_right_le; rewrite normr_gt0.
near=> x; have : `|a - fine (f x)| < e by near: x; apply: cvgr_dist_lt.
by case: f=> //=; rewrite subr0; apply: contra_ltT.
Unshelve. all: by end_near. Qed.

End limit.

End cvg_fin.

Section ecvg_realFieldType.
Context {I} {F : set_system I} {FF : Filter F} {R : realFieldType}.
Implicit Types f g u v : I -> \bar R.
Local Open Scope ereal_scope.

Lemma cvgeD f g a b :
  a +? b -> f @ F --> a -> g @ F --> b -> f \+ g @ F --> a + b.
Proof.
have yE u v x : u @ F --> +oo -> v @ F --> x%:E -> u \+ v @ F --> +oo.
  move=> /cvgeyPge/= foo /fine_cvgP[Fg gb]; apply/cvgeyPgey.
  near=> A; near=> n; have /(_ _)/wrap[//|Fgn] := near Fg n.
  rewrite -lee_subl_addr// (@le_trans _ _ (A - (x - 1))%:E)//; last by near: n.
  rewrite ?EFinB lee_sub// lee_subl_addr// -[v n]fineK// -EFinD lee_fin.
  by rewrite ler_distl_addr// ltW//; near: n; apply: cvgr_dist_lt.
have NyE u v x : u @ F --> -oo -> v @ F --> x%:E -> u \+ v @ F --> -oo.
  move=> /cvgeNyPle/= foo /fine_cvgP -[Fg gb]; apply/cvgeNyPleNy.
  near=> A; near=> n; have /(_ _)/wrap[//|Fgn] := near Fg n.
  rewrite -lee_subr_addr// (@le_trans _ _ (A - (x + 1))%:E)//; first by near: n.
  rewrite ?EFinB ?EFinD lee_sub// -[v n]fineK// -EFinD lee_fin.
  by rewrite ler_distlC_addr// ltW//; near: n; apply: cvgr_dist_lt.
have yyE u v : u @ F --> +oo -> v @ F --> +oo -> u \+ v @ F --> +oo.
  move=> /cvgeyPge foo /cvgeyPge goo; apply/cvgeyPge => A; near=> y.
  by rewrite -[leLHS]adde0 lee_add//; near: y; [apply: foo|apply: goo].
have NyNyE u v : u @ F --> -oo -> v @ F --> -oo -> u \+ v @ F --> -oo.
  move=> /cvgeNyPle foo /cvgeNyPle goo; apply/cvgeNyPle => A; near=> y.
  by rewrite -[leRHS]adde0 lee_add//; near: y; [apply: foo|apply: goo].
have addfC u v : u \+ v = v \+ u.
  by apply/funeqP => x; rewrite /= addeC.
move: a b => [a| |] [b| |] //= _; rewrite ?(addey, addye, addeNy, addNye)//=;
  do ?by [apply: yE|apply: NyE|apply: yyE|apply: NyNyE].
- move=> /fine_cvgP[Ff fa] /fine_cvgP[Fg ga]; rewrite -EFinD.
  apply/fine_cvgP; split.
    by near do [rewrite fin_numD; apply/andP; split].
  apply: (@cvg_trans _ ((fine \o f) \+ (fine \o g) @ F))%R; last exact: cvgD.
  by apply: near_eq_cvg; near do rewrite /= fineD//.
- by move=> /[swap]; rewrite addfC; apply: yE.
- by move=> /[swap]; rewrite addfC; apply: NyE.
Unshelve. all: by end_near. Qed.

Lemma cvgeN f x : f @ F --> x -> - f x @[x --> F] --> - x.
Proof. by move=> ?; apply: continuous_cvg => //; exact: oppe_continuous. Qed.

Lemma cvgeNP f a : - f x @[x --> F] --> - a <-> f @ F --> a.
Proof.
by split=> /cvgeN//; rewrite oppeK//; under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvgeB f g a b :
  a +? - b -> f @ F --> a -> g @ F --> b -> f \- g @ F --> a - b.
Proof. by move=> ab fa gb; apply: cvgeD => //; exact: cvgeN. Qed.

Lemma cvge_sub0 f (k : \bar R) :
  k \is a fin_num -> (fun x => f x - k) @ F --> 0 <-> f @ F --> k.
Proof.
move=> kfin; split.
  move=> /cvgeD-/(_ (cst k) _ isT (cvg_cst _)).
  by rewrite add0e; under eq_fun => x do rewrite subeK//.
move: k kfin => [k _ fk| |]//; rewrite -(@subee _ k%:E)//.
by apply: cvgeB => //; exact: cvg_cst.
Qed.

Lemma abse_continuous : continuous (@abse R).
Proof.
case=> [r|A /= [r [rreal rA]]|A /= [r [rreal rA]]]/=.
- exact/(cvg_comp (@norm_continuous _ [the normedModType R of R^o] r)).
- by exists r; split => // y ry; apply: rA; rewrite (lt_le_trans ry)// lee_abs.
- exists (- r)%R; rewrite realN; split => // y; rewrite EFinN -lte_oppr => yr.
  by apply: rA; rewrite (lt_le_trans yr)// -abseN lee_abs.
Qed.

Lemma cvg_abse f (a : \bar R) : f @ F --> a -> `|f x|%E @[x --> F] --> `|a|%E.
Proof. by apply: continuous_cvg => //; apply: abse_continuous. Qed.

Lemma is_cvg_abse (f : I -> \bar R) : cvg (f @ F) -> cvg (`|f x|%E @[x --> F]).
Proof. by move/cvg_abse/cvgP. Qed.

Lemma is_cvgeN f : cvg (f @ F) -> cvg (\- f @ F).
Proof. by move=> /cvg_ex[l fl]; apply: (cvgP (- l)); exact: cvgeN. Qed.

Lemma is_cvgeNE f : cvg (\- f @ F) = cvg (f @ F).
Proof.
rewrite propeqE; split=> /cvgeNP/cvgP//.
by under eq_is_cvg do rewrite oppeK.
Qed.

Lemma mule_continuous (r : R) : continuous (mule r%:E).
Proof.
rewrite /continuous_at; wlog r0 : r / (r > 0)%R => [hwlog|].
  have [r0|r0|->] := ltrgtP r 0; do ?exact: hwlog; last first.
    by move=> x; rewrite mul0e; apply: cvg_near_cst; near=> y; rewrite mul0e.
  have -> : *%E r%:E = \- ( *%E (- r)%:E ).
    by apply/funeqP=> x /=; rewrite EFinN mulNe oppeK.
  move=> x; apply: (continuous_comp (hwlog (- r)%R _ _)); rewrite ?oppr_gt0//.
  exact: oppe_continuous.
move=> [s||]/=.
- rewrite -EFinM; apply: cvg_EFin => /=.
    by apply/nbhs_EFin; near do rewrite fin_numM//.
  move=> P /= Prs; apply/nbhs_EFin=> //=.
  by apply: near_fun => //=; apply: continuousM => //=; apply: cvg_cst.
- rewrite muleC /mule/= eqe gt_eqF// lte_fin r0 => A [u [realu uA]].
  exists (r^-1 * u)%R; split; first by rewrite realM// realV realE ltW.
  by move=> x rux; apply: uA; move: rux; rewrite EFinM lte_pdivr_mull.
- rewrite muleC /mule/= eqe gt_eqF// lte_fin r0 => A [u [realu uA]].
  exists (r^-1 * u)%R; split; first by rewrite realM// realV realE ltW.
  by move=> x xru; apply: uA; move: xru; rewrite EFinM lte_pdivl_mull.
Unshelve. all: by end_near. Qed.

Lemma cvgeMl f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => y * f n) @ F --> y * x.
Proof. by move: y => [r| |]// _ /cvg_comp; apply; exact: mule_continuous. Qed.

Lemma is_cvgeMl f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => y * f n) @ F).
Proof. by move=> fy /(cvgeMl fy)/cvgP. Qed.

Lemma cvgeMr f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => f n * y) @ F --> x * y.
Proof.
by move=> ? ?; rewrite muleC; under eq_fun do rewrite muleC; exact: cvgeMl.
Qed.

Lemma is_cvgeMr f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => f n * y) @ F).
Proof. by move=> fy /(cvgeMr fy)/cvgP. Qed.

Lemma cvg_abse0P f : abse \o f @ F --> 0 <-> f @ F --> 0.
Proof.
split; last by move=> /cvg_abse; rewrite abse0.
move=> /cvg_ballP f0; apply/cvg_ballP => _/posnumP[e].
have := !! f0 _ (gt0 e); rewrite !near_simpl => absf0; rewrite near_simpl.
apply: filterS absf0 => x /=; rewrite /ball/= /ereal_ball !contract0 !sub0r !normrN.
have [fx0|fx0] := leP 0 (f x); first by rewrite gee0_abs.
by rewrite (lte0_abs fx0) contractN normrN.
Qed.

Let cvgeM_gt0_pinfty f g b :
  (0 < b)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Proof.
move=> b_gt0 /cvgeyPge foo /fine_cvgP[gfin gb]; apply/cvgeyPgey.
near (0%R : R)^'+ => e; near=> A; near=> n.
rewrite (@le_trans _ _ (f n * e%:E))// ?lee_pmul// ?lee_fin//.
- by rewrite -lee_pdivr_mulr ?divr_gt0//; near: n; apply: foo.
- by rewrite (@le_trans _ _ 1) ?lee_fin//; near: n; apply: foo.
rewrite -(@fineK _ (g n)) ?lee_fin; last by near: n; exact: gfin.
by near: n; apply: (cvgr_ge b).
Unshelve. all: end_near. Qed.

Let cvgeM_lt0_pinfty  f g b :
  (b < 0)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Proof.
move=> b0 /cvgeyPge foo /fine_cvgP -[gfin gb]; apply/cvgeNyPleNy.
near (0%R : R)^'+ => e; near=> A; near=> n.
rewrite -lee_opp -muleN (@le_trans _ _ (f n * e%:E))//.
  by rewrite -lee_pdivr_mulr ?mulr_gt0 ?oppr_gt0//; near: n; apply: foo.
rewrite lee_pmul ?lee_fin//.
  by rewrite (@le_trans _ _ 1) ?lee_fin//; near: n; apply: foo.
rewrite -(@fineK _ (g n)) ?lee_fin; last by near: n; exact: gfin.
near: n; apply: (cvgr_ge (- b)); rewrite 1?cvgNP//.
by near: e; apply: nbhs_right_lt; rewrite oppr_gt0.
Unshelve. all: end_near. Qed.

Let cvgeM_gt0_ninfty f g b :
  (0 < b)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Proof.
move=> b0 foo gb; under eq_fun do rewrite -muleNN.
apply: (@cvgeM_lt0_pinfty _ _ (- b)%R); first by rewrite oppr_lt0.
- by rewrite -(oppeK +oo); apply: cvgeN.
- by rewrite EFinN; apply: cvgeN.
Qed.

Let cvgeM_lt0_ninfty f g b :
  (b < 0)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Proof.
move=> b0 foo gb; under eq_fun do rewrite -muleNN.
apply: (@cvgeM_gt0_pinfty _ _ (- b)%R); first by rewrite oppr_gt0.
- by rewrite -(oppeK +oo); apply: cvgeN.
- by rewrite EFinN; apply: cvgeN.
Qed.

Lemma cvgeM f g (a b : \bar R) :
 a *? b -> f @ F --> a -> g @ F --> b -> f \* g @ F --> a * b.
Proof.
move=> [:apoo] [:bnoo] [:poopoo] [:poonoo]; move: a b => [a| |] [b| |] //.
- move=> _ /fine_cvgP[finf fa] /fine_cvgP[fing gb].
  apply/fine_cvgP; split.
    by near do apply: fin_numM; [apply: finf | apply: fing].
  apply: (@cvg_trans _ (((fine \o f) \* (fine \o g)) @ F)%R).
    apply: near_eq_cvg; near=> n => //=.
    rewrite -[in RHS](@fineK _ (f n)); last by near: n; exact: finf.
    by rewrite -[in RHS](@fineK _ (g n)) //; near: n; exact: fing.
  exact: cvgM.
- move: f g a; abstract: apoo.
  move=> {}f {}g {}a + fa goo; have [a0 _|a0 _|->] := ltgtP a 0%R.
  + rewrite mulry ltr0_sg// ?mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_pinfty a0).
  + rewrite mulry gtr0_sg// ?mul1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_gt0_pinfty a0).
  + by rewrite /mule_def eqxx.
- move: f g a; abstract: bnoo.
  move=> {}f {}g {}a + fa goo; have [a0 _|a0 _|->] := ltgtP a 0%R.
  + rewrite mulrNy ltr0_sg// ?mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_ninfty a0).
  + rewrite mulrNy gtr0_sg// ?mul1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_gt0_ninfty a0).
  + by rewrite /mule_def eqxx.
- rewrite mule_defC => ? foo gb; rewrite muleC.
  by under eq_fun do rewrite muleC; exact: apoo.
- move=> _; move: f g; abstract: poopoo.
  move=> {}f {}g /cvgeyPge foo /cvgeyPge goo.
  rewrite mulyy; apply/cvgeyPgey; near=> A; near=> n.
  have A_gt0 : (0 <= A)%R by [].
  by rewrite -[leLHS]mule1 lee_pmul//=; near: n; [apply: foo|apply: goo].
- move=> _; move: f g; abstract: poonoo.
  move=> {}f {}g /cvgeyPge foo /cvgeNyPle goo.
  rewrite mulyNy; apply/cvgeNyPle => A; near=> n.
  rewrite (@le_trans _ _ (g n))//; last by near: n; exact: goo.
  apply: lee_nemull; last by near: n; apply: foo.
  by rewrite (@le_trans _ _ (- 1)%:E)//; near: n; apply: goo; rewrite ltrN10.
- rewrite mule_defC => ? foo gb; rewrite muleC.
  by under eq_fun do rewrite muleC; exact: bnoo.
- move=> _ foo goo.
  by under eq_fun do rewrite muleC; exact: poonoo.
- move=> _ foo goo; rewrite mulNyNy -mulyy.
  by under eq_fun do rewrite -muleNN; apply: poopoo;
    rewrite -/(- -oo); apply: cvgeN.
Unshelve. all: end_near. Qed.

End ecvg_realFieldType.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeN, and generalized to filter in Type")]
Notation ereal_cvgN := cvgeN.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to is_cvgeN, and generalized to filter in Type")]
Notation ereal_is_cvgN := is_cvgeN.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeMl, and generalized to filter in Type")]
Notation ereal_cvgrM := cvgeMl.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to is_cvgeMl, and generalized to filter in Type")]
Notation ereal_is_cvgrM := is_cvgeMl.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeMr, and generalized to filter in Type")]
Notation ereal_cvgMr := cvgeMr.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to is_cvgeMr, and generalized to filter in Type")]
Notation ereal_is_cvgMr := is_cvgeMr.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeM, and generalized to a realFieldType")]
Notation ereal_cvgM := cvgeM.

Section open_closed_sets_ereal.
Variable R : realFieldType (* TODO: generalize to numFieldType? *).
Local Open Scope ereal_scope.
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma open_ereal_lt y : open [set r : R | r%:E < y].
Proof.
case: y => [y||] /=; first exact: open_lt.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite ltry trueE.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
Qed.

Lemma open_ereal_gt y : open [set r : R | y < r%:E].
Proof.
case: y => [y||] /=; first exact: open_gt.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite ltNyr trueE.
Qed.

Lemma open_ereal_lt' x y : x < y -> ereal_nbhs x (fun u => u < y).
Proof.
case: x => [x|//|] xy; first exact: open_ereal_lt.
- case: y => [y||//] /= in xy *; last by exists 0%R.
  by exists y; rewrite num_real; split => //= x ?.
- case: y => [y||//] /= in xy *.
  + by exists y; rewrite num_real; split => //= x ?.
  + by exists 0%R; split => // x /lt_le_trans; apply; rewrite leey.
Qed.

Lemma open_ereal_gt' x y : y < x -> ereal_nbhs x (fun u => y < u).
Proof.
case: x => [x||] //=; do ?[exact: open_ereal_gt];
  case: y => [y||] //=; do ?by exists 0.
- by exists y; rewrite num_real.
- by move=> _; exists 0%R; split => // x; apply/le_lt_trans; rewrite leNye.
Qed.

Lemma open_ereal_lt_ereal x : open [set y | y < x].
Proof.
have openr r : open [set x : \bar R | x < r%:E].
  (* BUG: why doesn't case work? *)
  move=> [? | // | ?]; [rewrite /= lte_fin => xy | by exists r].
  by move: (@open_ereal_lt r%:E); rewrite openE; apply; rewrite /= lte_fin.
move: x => [ // | | ]; last by move=> []. (* same BUG *)
suff -> : [set y | y < +oo] = \bigcup_r [set y : \bar R | y < r%:E].
  exact: bigcup_open.
rewrite predeqE => -[r | | ]/=.
- rewrite ltry; split => // _.
  by exists (r + 1)%R => //=; rewrite lte_fin ltr_addl.
- by rewrite ltxx; split => // -[] x /=; rewrite ltNge leey.
- by split => // _; exists 0%R => //=; rewrite ltNye.
Qed.

Lemma open_ereal_gt_ereal x : open [set y | x < y].
Proof.
have openr r : open [set x | r%:E < x].
  move=> [? | ? | //]; [rewrite /= lte_fin => xy | by exists r].
  by move: (@open_ereal_gt r%:E); rewrite openE; apply; rewrite /= lte_fin.
case: x => [ // | | ]; first by move=> [].
suff -> : [set y | -oo < y] = \bigcup_r [set y : \bar R | r%:E < y].
  exact: bigcup_open.
rewrite predeqE => -[r | | ]/=.
- rewrite ltNyr; split => // _.
  by exists (r - 1)%R => //=; rewrite lte_fin ltr_subl_addr ltr_addl.
- by split => // _; exists 0%R => //=; rewrite ltey.
- by rewrite ltxx; split => // -[] x _ /=; rewrite ltNge leNye.
Qed.

Lemma closed_ereal_le_ereal y : closed [set x | y <= x].
Proof.
rewrite (_ : [set x | y <= x] = ~` [set x | y > x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/open_closedC/open_ereal_lt_ereal.
Qed.

Lemma closed_ereal_ge_ereal y : closed [set x | y >= x].
Proof.
rewrite (_ : [set x | y >= x] = ~` [set x | y < x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/open_closedC/open_ereal_gt_ereal.
Qed.

End open_closed_sets_ereal.

Section closure_left_right_open.
Variable R : realFieldType.
Implicit Types z : R.

Lemma closure_gt z : closure ([set x | z < x] : set R) = [set x | z <= x].
Proof.
rewrite eqEsubset; split.
  by rewrite closureE; apply: smallest_sub => // ? /ltW.
move=> v; rewrite /mkset le_eqVlt => /predU1P[<-{v}|]; last first.
  by move=> ?; exact: subset_closure.
move=> B [e /= e0 zB]; near (0 : R)^'+ => d.
exists (z + d); split; rewrite /= ?ltr_addl//; apply: zB => /=.
by rewrite opprD addNKr normrN gtr0_norm//.
Unshelve. all: by end_near. Qed.

Lemma closure_lt z : closure ([set x : R | x < z]) = [set x | x <= z].
Proof.
rewrite eqEsubset; split.
  by rewrite closureE; apply: smallest_sub => // ? /ltW.
move=> v; rewrite /mkset le_eqVlt => /predU1P[<-{z}|]; last first.
  by move=> ?; exact: subset_closure.
move=> B [e /= e0 vB]; near (0 : R)^'+ => d.
exists (v - d); split; rewrite /= ?gtr_addl ?oppr_lt0//; apply: vB => /=.
by rewrite opprB addrC addrNK gtr0_norm//; near: d.
Unshelve. all: by end_near. Qed.

End closure_left_right_open.

(** ** Complete Normed Modules *)

#[short(type="completeNormedModType")]
HB.structure Definition CompleteNormedModule (K : numFieldType) :=
  {T of NormedModule K T & Complete T}.

(** * Extended Types *)

(** * The topology on real numbers *)

Lemma R_complete (R : realType) (F : set_system R) : ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF /cauchy_ballP F_cauchy; apply/cvg_ex.
pose D := \bigcap_(A in F) (down A).
have /cauchy_ballP /cauchyP /(_ 1) [//|x0 x01] := F_cauchy.
have D_has_sup : has_sup D; first split.
- exists (x0 - 1) => A FA.
  near F => x.
  apply/downP; exists x; first by near: x.
  by rewrite ler_distl_subl // ltW //; near: x.
- exists (x0 + 1); apply/ubP => x /(_ _ x01) /downP [y].
  rewrite -[ball _ _ _]/(_ (_ < _)) ltr_distl ltr_subl_addr => /andP[/ltW].
  by move=> /(le_trans _) yx01 _ /yx01.
exists (sup D).
apply/cvgrPdist_le => /= _ /posnumP[eps]; near=> x.
rewrite ler_distl; move/ubP: (sup_upper_bound D_has_sup) => -> //=.
  apply: sup_le_ub => //; first by case: D_has_sup.
  have Fxeps : F (ball_ [eta normr] x eps%:num).
    by near: x; apply: nearP_dep; apply: F_cauchy.
  apply/ubP => y /(_ _ Fxeps) /downP[z].
  rewrite /ball_/= ltr_distl ltr_subl_addr.
  by move=> /andP [/ltW /(le_trans _) le_xeps _ /le_xeps].
rewrite /D /= => A FA; near F => y.
apply/downP; exists y.
by near: y.
rewrite ler_subl_addl -ler_subl_addr ltW //.
suff: `|x - y| < eps%:num by rewrite ltr_norml => /andP[_].
by near: y; near: x; apply: nearP_dep; apply: F_cauchy.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ (R : realType) := Uniform_isComplete.Build R^o
  (@R_complete R). (* todo : delete *)

HB.instance Definition _ (R : realType) := Complete.copy R
  [the completeType of R^o].
(* new *)

Section cvg_seq_bounded.
Context {K : numFieldType}.
Local Notation "'+oo'" := (@pinfty_nbhs K).

Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  cvgn a -> bounded_fun a.
Proof.
move=> /cvg_bounded/ex_bound => -[/= Moo] => -[N _ /(_ _) aM].
have Moo_real : Moo \is Num.real by rewrite ger0_real ?(le_trans _ (aM N _))/=.
rewrite /bounded_near /=; near=> M => n _.
have [nN|nN]/= := leqP N n; first by apply: (le_trans (aM _ _)).
move: n nN; suff /(_ (Ordinal _)) : forall n : 'I_N, `|a n| <= M by [].
by near: M; apply: filter_forall => i; apply: nbhs_pinfty_ge.
Unshelve. all: by end_near. Qed.

End cvg_seq_bounded.

Lemma closure_sup (R : realType) (A : set R) :
  A !=set0 -> has_ubound A -> closure A (sup A).
Proof.
move=> A0 ?; have [|AsupA] := pselect (A (sup A)); first exact: subset_closure.
rewrite closure_limit_point; right => U /nbhs_ballP[_ /posnumP[e]] supAeU.
suff [x [Ax /andP[sAex xsA]]] : exists x, A x /\ sup A - e%:num < x < sup A.
  exists x; split => //; first by rewrite lt_eqF.
  apply supAeU; rewrite /ball /= ltr_distl (addrC x e%:num) -ltr_subl_addl sAex.
  by rewrite andbT (le_lt_trans _ xsA) // ler_subl_addl ler_addr.
apply: contrapT => /forallNP Ax.
suff /(sup_le_ub A0) : ubound A (sup A - e%:num).
  by rewrite leNgt => /negP; apply; rewrite ltr_subl_addl ltr_addr.
move=> y Ay; have /not_andP[//|/negP] := Ax y.
rewrite negb_and leNgt => /orP[//|]; apply: contra => sAey.
rewrite lt_neqAle sup_upper_bound // andbT.
by apply: contra_not_neq AsupA => <-.
Qed.

Lemma near_infty_natSinv_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, n.+1%:R^-1 < e%:num.
Proof.
near=> n; rewrite -(@ltr_pmul2r _ n.+1%:R) // mulVr ?unitfE //.
rewrite -(@ltr_pmul2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // ltr_nat.
by near: n; exists (Num.bound e%:num^-1).
Unshelve. all: by end_near. Qed.

Lemma near_infty_natSinv_expn_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, 1 / 2 ^+ n < e%:num.
Proof.
near=> n.
rewrite -(@ltr_pmul2r _ (2 ^+ n)) // -?natrX ?ltr0n ?expn_gt0//.
rewrite mul1r mulVr ?unitfE ?gt_eqF// ?ltr0n ?expn_gt0//.
rewrite -(@ltr_pmul2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // natrX upper_nthrootP //.
near: n; eexists; last by move=> m; exact.
by [].
Unshelve. all: by end_near. Qed.

Lemma limit_pointP (T : archiFieldType) (A : set T) (x : T) :
  limit_point A x <-> exists a_ : nat -> T,
    [/\ a_ @` setT `<=` A, forall n, a_ n != x & a_ @ \oo --> x].
Proof.
split=> [Ax|[a_ [aTA a_x] ax]]; last first.
  move=> U /ax[m _ a_U]; near \oo => n; exists (a_ n); split => //.
  by apply aTA; exists n.
  by apply a_U; near: n; exists m.
pose U := fun n : nat => [set z : T | `|x - z| < n.+1%:R^-1].
suff /(_ _)/cid-/all_sig[a_ anx] : forall n, exists a, a != x /\ (U n `&` A) a.
  exists a_; split.
  - by move=> a [n _ <-]; have [? []] := anx n.
  - by move=> n; have [] := anx n.
  - apply/cvgrPdist_lt => _/posnumP[e]; near=> n;  have [? [] Uan Aan] := anx n.
    by rewrite (lt_le_trans Uan)// ltW//; near: n; exact: near_infty_natSinv_lt.
move=> n; have : nbhs (x : T) (U n).
  by apply/(nbhs_ballP (x:T) (U n)); rewrite nbhs_ballE; exists n.+1%:R^-1 => //=.
by move/Ax/cid => [/= an [anx Aan Uan]]; exists an.
Unshelve. all: by end_near. Qed.

Section interval.
Variable R : numDomainType.

Definition is_interval (E : set R) :=
  forall x y, E x -> E y -> forall z, x <= z <= y -> E z.

Lemma is_intervalPlt (E : set R) :
  is_interval E <-> forall x y, E x -> E y -> forall z, x < z < y -> E z.
Proof.
split=> iE x y Ex Ey z /andP[].
  by move=> xz zy; apply: (iE x y); rewrite ?ltW.
rewrite !le_eqVlt => /predU1P[<-//|xz] /predU1P[->//|zy].
by apply: (iE x y); rewrite ?xz.
Qed.

Lemma interval_is_interval (i : interval R) : is_interval [set` i].
Proof.
by case: i => -[[]a|[]] [[]b|[]] // x y /=; do ?[by rewrite ?itv_ge//];
  move=> xi yi z; rewrite -[x <= z <= y]/(z \in `[x, y]); apply/subitvP;
  rewrite subitvE /Order.le/= ?(itvP xi, itvP yi).
Qed.

End interval.

Section ereal_is_hausdorff.
Variable R : realFieldType.
Implicit Types r : R.

Lemma nbhs_image_EFin (x : R) (X : set R) :
  nbhs x X -> nbhs x%:E ((fun r => r%:E) @` X).
Proof.
case => _/posnumP[e] xeX; exists e%:num => //= r xer.
by exists r => //; apply xeX.
Qed.

Lemma nbhs_open_ereal_lt r (f : R -> R) : r < f r ->
  nbhs r%:E [set y | y < (f r)%:E]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_gt r (f : R -> R) : f r < r ->
  nbhs r%:E [set y | (f r)%:E < y]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_pinfty r : (nbhs +oo [set y | r%:E < y])%E.
Proof.
rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= ltry].
Qed.

Lemma nbhs_open_ereal_ninfty r : (nbhs -oo [set y | y < r%:E])%E.
Proof.
rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= ltNyr].
Qed.

Lemma ereal_hausdorff : hausdorff_space (\bar R).
Proof.
move=> -[r| |] // [r' | |] //=.
- move=> rr'; congr (_%:E); apply Rhausdorff => /= A B rA r'B.
  have [/= z [[r0 ? r0z] [r1 ?]]] :=
    rr' _ _ (nbhs_image_EFin rA) (nbhs_image_EFin r'B).
  by rewrite -r0z => -[r1r0]; exists r0; split => //; rewrite -r1r0.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r : r < r + 1.
    by rewrite ltr_addl.
  move/(_ _ _ loc_r (nbhs_open_ereal_pinfty (r + 1))) => -[z [zr rz]].
  by move: (lt_trans rz zr); rewrite lte_fin ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) loc_r : r - 1 < r.
    by rewrite ltr_subl_addr ltr_addl.
  move/(_ _ _ loc_r (nbhs_open_ereal_ninfty (r - 1))) => -[z [rz zr]].
  by move: (lt_trans zr rz); rewrite ltxx.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r' : r' < r' + 1.
    by rewrite ltr_addl.
  move/(_ _ _ (nbhs_open_ereal_pinfty (r' + 1)) loc_r') => -[z [r'z zr']].
  by move: (lt_trans zr' r'z); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_pinfty 0) (nbhs_open_ereal_ninfty 0)).
  by move=> -[z [zx xz]]; move: (lt_trans xz zx); rewrite ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) yB : r' - 1 < r'.
    by rewrite ltr_subl_addr ltr_addl.
  move/(_ _ _ (nbhs_open_ereal_ninfty (r' - 1)) yB) => -[z [zr' r'z]].
  by move: (lt_trans r'z zr'); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_ninfty 0) (nbhs_open_ereal_pinfty 0)).
  by move=> -[z [zO Oz]]; move: (lt_trans Oz zO); rewrite ltxx.
Qed.

End ereal_is_hausdorff.

#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: ereal_hausdorff] : core.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `nbhs_image_EFin`")]
Notation nbhs_image_ERFin := nbhs_image_EFin.

Lemma EFin_lim (R : realFieldType) (f : nat -> R) : cvgn f ->
  limn (EFin \o f) = (limn f)%:E.
Proof.
move=> cf; apply: cvg_lim => //; move/cvg_ex : cf => [l fl].
by apply: (cvg_comp fl); rewrite (cvg_lim _ fl).
Qed.

Section ProperFilterERealType.
Context {T : Type} {a : set_system T} {Fa : ProperFilter a} {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma cvge_to_ge f b c : f @ a --> c -> (\near a, b <= f a) -> b <= c.
Proof.
by move=> /[swap]/(closed_cvg _ (@closed_ereal_le_ereal _ b)) /[apply].
Qed.

Lemma cvge_to_le f b c : f @ a --> c -> (\near a, f a <= b) -> c <= b.
Proof.
by move=> /[swap]/(closed_cvg _ (@closed_ereal_ge_ereal _ b))/[apply].
Qed.

Lemma lime_ge x f : cvg (f @ a) -> (\near a, x <= f a) -> x <= lim (f @ a).
Proof. exact: cvge_to_ge. Qed.

Lemma lime_le x f : cvg (f @ a) -> (\near a, x >= f a) -> x >= lim (f @ a).
Proof. exact: cvge_to_le. Qed.

End ProperFilterERealType.

Section ecvg_realFieldType_proper.
Context {I} {F : set_system I} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g : I -> \bar R) (u v : I -> R) (x : \bar R) (r : R).
Local Open Scope ereal_scope.

Lemma is_cvgeD f g :
  lim (f @ F) +? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \+ g @ F).
Proof. by move=> fg fc gc; have /(_ _)/cvgP := cvgeD fg fc gc. Qed.

Lemma limeD f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) +? lim (g @ F) ->
  lim (f \+ g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> cf cg fg; apply/cvg_lim => //; exact: cvgeD. Qed.

Lemma limeMl f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => y * f n) @ F) = y * lim (f @ F).
Proof. by move=> yfn cf; apply/cvg_lim => //; exact: cvgeMl. Qed.

Lemma limeMr f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => f n * y) @ F) = lim (f @ F) * y.
Proof. by move=> yfn cf; apply/cvg_lim => //; apply: cvgeMr. Qed.

Lemma is_cvgeM f g :
  lim (f @ F) *? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Proof. by move=> fg fc gc; have /(_ _)/cvgP := cvgeM fg fc gc. Qed.

Lemma limeM f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) *? lim (g @ F) ->
  lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Proof. by move=> cf cg fg; apply/cvg_lim => //; exact: cvgeM. Qed.

Lemma limeN f : cvg (f @ F) -> lim (\- f @ F) = - lim (f @ F).
Proof. by move=> cf; apply/cvg_lim => //; apply: cvgeN. Qed.

Lemma cvge_ge f a b : (\forall x \near F, b <= f x) -> f @ F --> a -> b <= a.
Proof. by move=> ? fa; rewrite -(cvg_lim _ fa) ?lime_ge//=; apply: cvgP fa. Qed.

Lemma cvge_le f a b : (\forall x \near F, b >= f x) -> f @ F --> a -> b >= a.
Proof. by move=> ? fa; rewrite -(cvg_lim _ fa) ?lime_le//=; apply: cvgP fa. Qed.

Lemma cvg_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> f j @ F --> l j) ->
  \sum_(j <- r | P j) f j i @[i --> F] --> \sum_(j <- r | P j) l j.
Proof.
pose bigsimp := (big_nil, big_cons);
elim: r => [|x r IHr]/= f0 fl; rewrite bigsimp; under eq_fun do rewrite bigsimp.
  exact: cvg_cst.
case: ifPn => [Px|Pnx]; last exact: IHr.
apply: cvgeD; [|exact: fl|exact: IHr].
by rewrite ge0_adde_def ?inE// ?sume_ge0// => [|j Pj];
   rewrite (cvge_ge _ (fl _ _))//; apply: f0.
Qed.

Lemma lim_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> cvg (f j @ F)) ->
  lim (\sum_(j <- r | P j) f j i @[i --> F]) = \sum_(j <- r | P j) (lim (f j @ F)).
Proof. by move=> ? ?; apply/cvg_lim => //; apply: cvg_nnesum. Qed.

End ecvg_realFieldType_proper.

#[deprecated(since="mathcomp-analysis 0.6.0", note="generalized to `limeMl`")]
Notation ereal_limrM := limeMl.
#[deprecated(since="mathcomp-analysis 0.6.0", note="generalized to `limeMr`")]
Notation ereal_limMr := limeMr.
#[deprecated(since="mathcomp-analysis 0.6.0", note="generalized to `limeN`")]
Notation ereal_limN := limeN.

Section cvg_0_pinfty.
Context {R : realFieldType} {I : Type} {a : set_system I} {FF : Filter a}.
Implicit Types f : I -> R.

Lemma gtr0_cvgV0 f : (\near a, 0 < f a) -> f\^-1 @ a --> 0 <-> f @ a --> +oo.
Proof.
move=> f_gt0; split; last first.
  move=> /cvgryPgt cvg_f_oo; apply/cvgr0Pnorm_lt => _/posnumP[e].
  near=> i; rewrite gtr0_norm ?invr_gt0//=; last by near: i.
  by rewrite -ltf_pinv ?qualifE/= ?invr_gt0 ?invrK//=; near: i.
move=> /cvgr0Pnorm_lt uB; apply/cvgryPgty.
near=> M; near=> i; suff: `|(f i)^-1| < M^-1.
  by rewrite gtr0_norm ?ltf_pinv ?qualifE ?invr_gt0//=; near: i.
by near: i; apply: uB; rewrite ?invr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgrVy f : (\near a, 0 < f a) -> f\^-1 @ a --> +oo <-> f @ a --> 0.
Proof.
by move=> f_gt0; rewrite -gtr0_cvgV0 ?inv_funK//; near do rewrite invr_gt0.
Unshelve. all: by end_near. Qed.

Lemma ltr0_cvgV0 f : (\near a, 0 > f a) -> f\^-1 @ a --> 0 <-> f @ a --> -oo.
Proof.
move=> fL0; rewrite -cvgNP oppr0 (_ : - f\^-1 =  (- f)\^-1); last first.
   by apply/funeqP => i; rewrite opprfctE/= invrN.
by rewrite gtr0_cvgV0 ?cvgNry//; near do rewrite oppr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgrVNy f : (\near a, 0 > f a) -> f\^-1 @ a --> -oo <-> f @ a --> 0.
Proof.
by move=> f_lt0; rewrite -ltr0_cvgV0 ?inv_funK//; near do rewrite invr_lt0.
Unshelve. all: by end_near. Qed.

End cvg_0_pinfty.

Section FilterRealType.
Context {T : Type} {a : set_system T} {Fa : Filter a} {R : realFieldType}.
Implicit Types f g h : T -> R.

Lemma squeeze_cvgr f g h : (\near a, f a <= g a <= h a) ->
  forall (l : R), f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof.
move=> fgh l lfa lga; apply/cvgrPdist_lt => e e_gt0.
near=> x; have /(_ _)/andP[//|fg gh] := near fgh x.
rewrite distrC ltr_distl (lt_le_trans _ fg) ?(le_lt_trans gh)//=.
  by near: x; apply: (cvgr_lt l); rewrite // ltr_addl.
by near: x; apply: (cvgr_gt l); rewrite // gtr_addl oppr_lt0.
Unshelve. all: end_near. Qed.

Lemma ger_cvgy f g : (\near a, f a <= g a) ->
  f @ a --> +oo -> g @ a --> +oo.
Proof.
move=> uv /cvgryPge ucvg; apply/cvgryPge => A.
by near=> x do rewrite (le_trans _ (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma ler_cvgNy f g : (\near a, f a >= g a) ->
  f @ a --> -oo -> g @ a --> -oo.
Proof.
move=> uv /cvgrNyPle ucvg; apply/cvgrNyPle => A.
by near=> x do rewrite (le_trans (near uv x _))//.
Unshelve. all: end_near. Qed.

End FilterRealType.

Section TopoProperFilterRealType.
Context {T : topologicalType} {a : set_system T} {Fa : ProperFilter a}.
Context {R : realFieldType}.
Implicit Types f g h : T -> R.

Lemma ler_cvg_to f g (l l' : R) : f @ a --> l -> g @ a --> l' ->
  (\near a, f a <= g a) -> l <= l'.
Proof.
move=> fl gl; under eq_near do rewrite -subr_ge0; rewrite -subr_ge0.
by apply: cvgr_to_ge; apply: cvgB.
Qed.

Lemma ler_lim f g : cvg (f @ a) -> cvg (g @ a) ->
  (\near a, f a <= g a) -> lim (f @ a) <= lim (g @ a).
Proof. exact: ler_cvg_to. Qed.

End TopoProperFilterRealType.

Section FilterERealType.
Context {T : Type} {a : set_system T} {Fa : Filter a} {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma gee_cvgy f g : (\near a, f a <= g a) ->
  f @ a --> +oo -> g @ a --> +oo.
Proof.
move=> uv /cvgeyPge uecvg; apply/cvgeyPge => A.
by near=> x do rewrite (le_trans _ (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma lee_cvgNy f g : (\near a, f a >= g a) ->
  f @ a --> -oo -> g @ a --> -oo.
Proof.
move=> uv /cvgeNyPle uecvg; apply/cvgeNyPle => A.
by near=> x do rewrite (le_trans (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma squeeze_fin f g h : (\near a, f a <= g a <= h a) ->
    (\near a, f a \is a fin_num) -> (\near a, h a \is a fin_num) ->
  (\near a, g a \is a fin_num).
Proof.
apply: filterS3 => x /andP[fg gh].
rewrite !fin_numElt => /andP[oof _] /andP[_ hoo].
by rewrite (lt_le_trans oof) ?(le_lt_trans gh).
Qed.

Lemma squeeze_cvge f g h : (\near a, f a <= g a <= h a) ->
  forall (l : \bar R), f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof.
move=> fgh [l||]; last 2 first.
- by move=> + _; apply: gee_cvgy; apply: filterS fgh => ? /andP[].
- by move=> _; apply: lee_cvgNy; apply: filterS fgh => ? /andP[].
move=> /fine_cvgP[Ff fl] /fine_cvgP[Fh hl]; apply/fine_cvgP.
have Fg := squeeze_fin fgh Ff Fh; split=> //.
apply: squeeze_cvgr fl hl; near=> x => /=.
by have /(_ _)/andP[//|fg gh] := near fgh x; rewrite !fine_le//=; near: x.
Unshelve. all: end_near. Qed.

End FilterERealType.

Section TopoProperFilterERealType.
Context {T : topologicalType} {a : set_system T} {Fa : ProperFilter a}.
Context {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma lee_cvg_to f g l l' : f @ a --> l -> g @ a --> l' ->
  (\near a, f a <= g a) -> l <= l'.
Proof.
move=> + + fg; move: l' l.
move=> /= [l'||] [l||]//=; rewrite ?leNye ?leey//=; first 1 last.
- by move=> /(gee_cvgy fg) /cvg_lim<-// /cvg_lim<-.
- by move=> /cvg_lim <-// /(lee_cvgNy fg) /cvg_lim<-.
- by move=> /(gee_cvgy fg) /cvg_lim<-// /cvg_lim<-.
move=> /fine_cvgP[Ff fl] /fine_cvgP[Fg gl].
rewrite lee_fin -(cvg_lim _ fl)// -(cvg_lim _ gl)//.
by apply: ler_lim; [apply: cvgP fl|apply: cvgP gl|near do apply: fine_le].
Unshelve. all: end_near. Qed.

Lemma lee_lim f g : cvg (f @ a) -> cvg (g @ a) ->
  (\near a, f a <= g a) -> lim (f @ a) <= lim (g @ a).
Proof. exact: lee_cvg_to. Qed.

End TopoProperFilterERealType.

Section open_union_rat.
Variable R : realType.
Implicit Types A U : set R.

Let ointsub A U := [/\ open A, is_interval A & A `<=` U].

Let ointsub_rat U q := [set A | ointsub A U /\ A (ratr q)].

Let ointsub_rat0 q : ointsub_rat set0 q = set0.
Proof. by apply/seteqP; split => // A [[_ _]]; rewrite subset0 => ->. Qed.

Definition bigcup_ointsub U q := \bigcup_(A in ointsub_rat U q) A.

Lemma bigcup_ointsub0 q : bigcup_ointsub set0 q = set0.
Proof. by rewrite /bigcup_ointsub ointsub_rat0 bigcup_set0. Qed.

Lemma open_bigcup_ointsub U q : open (bigcup_ointsub U q).
Proof. by apply: bigcup_open => i [[]]. Qed.

Lemma is_interval_bigcup_ointsub U q : is_interval (bigcup_ointsub U q).
Proof.
move=> /= a b [A [[oA iA AU] Aq] Aa] [B [[oB iB BU] Bq] Bb] c /andP[ac cb].
have [cq|cq|->] := ltgtP c (ratr q); last by exists A.
- by exists A => //; apply: (iA a (ratr q)) => //; rewrite ac (ltW cq).
- by exists B => //; apply: (iB (ratr q) b) => //; rewrite cb (ltW cq).
Qed.

Lemma bigcup_ointsub_sub U q : bigcup_ointsub U q `<=` U.
Proof. by move=> y [A [[oA _ +] _ Ay]]; exact. Qed.

Lemma open_bigcup_rat U : open U ->
  U = \bigcup_(q in [set q | ratr q \in U]) bigcup_ointsub U q.
Proof.
move=> oU; have [->|U0] := eqVneq U set0.
  by rewrite bigcup0// => q _; rewrite bigcup_ointsub0.
apply/seteqP; split=> [x Ux|x [p _ Ipx]]; last exact: bigcup_ointsub_sub Ipx.
suff [q Iqx] : exists q, bigcup_ointsub U q x.
  by exists q => //=; rewrite in_setE; case: Iqx => A [[_ _ +] ? _]; exact.
have : nbhs x U by rewrite nbhsE /=; exists U.
rewrite -nbhs_ballE /nbhs_ball /nbhs_ball_ => -[_/posnumP[r] xrU].
have /rat_in_itvoo[q qxxr] : (x - r%:num < x + r%:num)%R.
  by rewrite ltr_subl_addr -addrA ltr_addl.
exists q, `](x - r%:num)%R, (x + r%:num)%R[%classic; last first.
  by rewrite /= in_itv/= ltr_subl_addl ltr_addr// ltr_addl//; apply/andP.
split=> //; split; [exact: interval_open|exact: interval_is_interval|].
move=> y /=; rewrite in_itv/= => /andP[xy yxr]; apply xrU => /=.
rewrite /ball /= /ball_ /= in xrU *; have [yx|yx] := leP x y.
  by rewrite ler0_norm ?subr_le0// opprB ltr_subl_addl.
by rewrite gtr0_norm ?subr_gt0// ltr_subl_addr -ltr_subl_addl.
Qed.

End open_union_rat.

Lemma right_bounded_interior (R : realType) (X : set R) :
  has_ubound X -> X^° `<=` [set r | r < sup X].
Proof.
move=> uX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP supXr|]; last first.
  by apply/negP; rewrite -leNgt sup_ub //; exact: interior_subset.
suff : ~ X^° (sup X) by rewrite supXr.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (sup X + f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprD addrA subrr.
  by rewrite sub0r normrN gtr0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
have : sup X + f%:num <= sup X by apply sup_ub.
by apply/negP; rewrite -ltNge; rewrite ltr_addl.
Qed.

Lemma left_bounded_interior (R : realType) (X : set R) :
  has_lbound X -> X^° `<=` [set r | inf X < r].
Proof.
move=> lX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP rinfX|]; last first.
  by apply/negP; rewrite -leNgt inf_lb //; exact: interior_subset.
suff : ~ X^° (inf X) by rewrite -rinfX.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (inf X - f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprB addrCA subrr.
  by rewrite addr0 gtr0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
have : inf X <= inf X - f%:num by apply inf_lb.
by apply/negP; rewrite -ltNge; rewrite ltr_subl_addr ltr_addl.
Qed.

Section interval_realType.
Variable R : realType.

Lemma interval_unbounded_setT (X : set R) : is_interval X ->
  ~ has_lbound X -> ~ has_ubound X -> X = setT.
Proof.
move=> iX lX uX; rewrite predeqE => x; split => // _.
move/has_lbPn : lX => /(_ x) [y Xy xy].
move/has_ubPn : uX => /(_ x) [z Xz xz].
by apply: (iX y z); rewrite ?ltW.
Qed.

Lemma interval_left_unbounded_interior (X : set R) : is_interval X ->
  ~ has_lbound X -> has_ubound X -> X^° = [set r | r < sup X].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: right_bounded_interior.
rewrite -(open_subsetE _ (@open_lt _ _)) => r rsupX.
move/has_lbPn : lX => /(_ r)[y Xy yr].
have hsX : has_sup X by split => //; exists y.
have /sup_adherent/(_ hsX)[e Xe] : 0 < sup X - r by rewrite subr_gt0.
by rewrite opprB addrCA subrr addr0 => re; apply: (iX y e); rewrite ?ltW.
Qed.

Lemma interval_right_unbounded_interior (X : set R) : is_interval X ->
  has_lbound X -> ~ has_ubound X -> X^° = [set r | inf X < r].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: left_bounded_interior.
rewrite -(open_subsetE _ (@open_gt _ _)) => r infXr.
move/has_ubPn : uX => /(_ r)[y Xy yr].
have hiX : has_inf X by split => //; exists y.
have /inf_adherent/(_ hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
by rewrite addrCA subrr addr0 => er; apply: (iX e y); rewrite ?ltW.
Qed.

Lemma interval_bounded_interior (X : set R) : is_interval X ->
  has_lbound X -> has_ubound X -> X^° = [set r | inf X < r < sup X].
Proof.
move=> iX bX aX; rewrite eqEsubset; split=> [r Xr|].
  apply/andP; split;
    [exact: left_bounded_interior|exact: right_bounded_interior].
rewrite -open_subsetE; last exact: (@interval_open _ (BRight _) (BLeft _)).
move=> r /andP[iXr rsX].
have [X0|/set0P X0] := eqVneq X set0.
  by move: (lt_trans iXr rsX); rewrite X0 inf_out ?sup_out ?ltxx // => - [[]].
have hiX : has_inf X by split.
have /inf_adherent/(_ hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
rewrite addrCA subrr addr0 => er.
have hsX : has_sup X by split.
have /sup_adherent/(_ hsX)[f Xf] : 0 < sup X - r by rewrite subr_gt0.
by rewrite opprB addrCA subrr addr0 => rf; apply: (iX e f); rewrite ?ltW.
Qed.

Definition Rhull (X : set R) : interval R := Interval
  (if `[< has_lbound X >] then BSide `[< X (inf X) >] (inf X)
                          else BInfty _ true)
  (if `[< has_ubound X >] then BSide (~~ `[< X (sup X) >]) (sup X)
                          else BInfty _ false).

Lemma Rhull0 : Rhull set0 = `]0, 0[ :> interval R.
Proof.
rewrite /Rhull  (asboolT (has_lbound0 R)) (asboolT (has_ubound0 R)) asboolF //.
by rewrite sup0 inf0.
Qed.

Lemma sub_Rhull (X : set R) : X `<=` [set x | x \in Rhull X].
Proof.
move=> x Xx/=; rewrite in_itv/=.
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
+ by case: asboolP => ?; case: asboolP => ? //=;
     rewrite !(lteifF, lteifT, sup_ub, inf_lb, sup_ub_strict, inf_lb_strict).
+ by case: asboolP => XinfX; rewrite !(lteifF, lteifT);
     [rewrite inf_lb | rewrite inf_lb_strict].
+ by case: asboolP => XsupX; rewrite !(lteifF, lteifT);
     [rewrite sup_ub | rewrite sup_ub_strict].
Qed.

Lemma is_intervalP (X : set R) : is_interval X <-> X = [set x | x \in Rhull X].
Proof.
split=> [iX|->]; last exact: interval_is_interval.
rewrite predeqE => x /=; split; [exact: sub_Rhull | rewrite in_itv/=].
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
- case: asboolP => XinfX; case: asboolP => XsupX;
    rewrite !(lteifF, lteifT).
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx].
    rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx supXx].
    apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[infXx]; rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> ?; apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_bounded_interior // /mkset infXx.
- case: asboolP => XinfX; rewrite !(lteifF, lteifT, andbT).
  + rewrite le_eqVlt => /orP[/eqP<-//|infXx].
    apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_right_unbounded_interior.
  + move=> infXx; apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_right_unbounded_interior.
- case: asboolP => XsupX /=.
  + rewrite le_eqVlt => /orP[/eqP->//|xsupX].
    apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_left_unbounded_interior.
  + move=> xsupX; apply: (@interior_subset [the topologicalType of R : Type]).
    by rewrite interval_left_unbounded_interior.
- by move=> _; rewrite (interval_unbounded_setT iX).
Qed.

Lemma connected_intervalP (E : set R) : connected E <-> is_interval E.
Proof.
split => [cE x y Ex Ey z /andP[xz zy]|].
- apply: contrapT => Ez.
  pose Az := E `&` [set x | x < z]; pose Bz := E `&` [set x | z < x].
  apply/connectedPn : cE; exists (fun b => if b then Az else Bz); split.
  + move: xz zy Ez.
    rewrite !le_eqVlt => /predU1P[<-//|xz] /predU1P[->//|zy] Ez.
    by case; [exists x | exists y].
  + rewrite /Az /Bz -setIUr; apply/esym/setIidPl => u Eu.
    by apply/orP; rewrite -neq_lt; apply/negP; apply: contraPnot Eu => /eqP <-.
  + split; [|rewrite setIC].
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_gt => zu.
      by rewrite /Az setCI; right; apply/negP; rewrite -leNgt.
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_lt => zu.
      by rewrite /Bz setCI; right; apply/negP; rewrite -leNgt.
- apply: contraPP => /connectedPn[A [A0 EU sepA]] intE.
  have [/= x A0x] := A0 false; have [/= y A1y] := A0 true.
  wlog xy : A A0 EU sepA x A0x y A1y / x < y.
    move=> /= wlog_hypo; have [xy|yx|{wlog_hypo}yx] := ltgtP x y.
    + exact: (wlog_hypo _ _ _ _ _ A0x _ A1y).
    + apply: (wlog_hypo (A \o negb) _ _ _ y _ x) => //=;
      by [rewrite setUC | rewrite separatedC].
    + move/separated_disjoint : sepA; rewrite predeqE => /(_ x)[] + _; apply.
      by split => //; rewrite yx.
  pose z := sup (A false `&` [set z | x <= z <= y]).
  have A1z : ~ (A true) z.
    have cA0z : closure (A false) z.
      suff : closure (A false `&` [set z | x <= z <= y]) z by case/closureI.
      apply: closure_sup; last by exists y => u [_] /andP[].
      by exists x; split => //; rewrite /mkset lexx /= (ltW xy).
    by move: sepA; rewrite /separated => -[] /disjoints_subset + _; apply.
  have /andP[xz zy] : x <= z < y.
    rewrite sup_ub //=; [|by exists y => u [_] /andP[]|].
    + rewrite lt_neqAle sup_le_ub ?andbT; last by move=> u [_] /andP[].
      * by apply/negP; apply: contraPnot A1y => /eqP <-.
      * by exists x; split => //; rewrite /mkset /= lexx /= (ltW xy).
    + by split=> //; rewrite /mkset lexx (ltW xy).
  have [A0z|A0z] := pselect ((A false) z); last first.
  have {}xzy : x <= z <= y by rewrite xz ltW.
    have : ~ E z by rewrite EU => -[].
    by apply; apply (intE x y) => //; rewrite EU; [left|right].
  suff [z1 [/andP[zz1 z1y] Ez1]] : exists z1 : R, z <= z1 <= y /\ ~ E z1.
    apply Ez1; apply (intE x y) => //; rewrite ?EU; [by left|by right|].
    by rewrite z1y (le_trans _ zz1).
  have [r zcA1] : {r:{posnum R}| ball z r%:num `<=` ~` closure (A true)}.
    have ? : ~ closure (A true) z.
      by move: sepA; rewrite /separated => -[] _ /disjoints_subset; apply.
    have ? : open (~` closure (A true)) by exact/closed_openC/closed_closure.
    exact/nbhsC_ball/open_nbhs_nbhs.
  pose z1 : R := z + r%:num / 2; exists z1.
  have z1y : z1 <= y.
    rewrite leNgt; apply/negP => yz1.
    suff : (~` closure (A true)) y by apply; exact: subset_closure.
    apply zcA1; rewrite /ball /= ltr_distl (lt_le_trans zy) // ?ler_addl //.
    rewrite andbT ltr_subl_addl addrC (lt_trans yz1) // ltr_add2l.
    by rewrite ltr_pdivr_mulr // ltr_pmulr // ltr1n.
  rewrite z1y andbT ler_addl; split => //.
  have ncA1z1 : (~` closure (A true)) z1.
    apply zcA1; rewrite /ball /= /z1 opprD addrA subrr add0r normrN.
    by rewrite ger0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
  have nA0z1 : ~ (A false) z1.
    move=> A0z1; have : z < z1 by rewrite /z1 ltr_addl.
    apply/negP; rewrite -leNgt.
     apply: sup_ub; first by exists y => u [_] /andP[].
    by split => //; rewrite /mkset /z1 (le_trans xz) /= ?ler_addl // (ltW z1y).
  by rewrite EU => -[//|]; apply: contra_not ncA1z1; exact: subset_closure.
Qed.
End interval_realType.

Section segment.
Variable R : realType.

(** properties of segments in [R] *)

Lemma segment_connected (a b : R) : connected `[a, b].
Proof. exact/connected_intervalP/interval_is_interval. Qed.

Lemma segment_compact (a b : R) : compact `[a, b].
Proof.
have [leab|ltba] := lerP a b; last first.
  by move=> F FF /filter_ex [x abx]; move: ltba; rewrite (itvP abx).
rewrite compact_cover => I D f fop sabUf.
set B := [set x | exists2 E : {fset I}, {subset E <= D} &
  `[a, x] `<=` \bigcup_(i in [set` E]) f i /\ (\bigcup_(i in [set` E]) f i) x].
set A := `[a, b] `&` B.
suff Aeab : A = `[a, b]%classic.
  suff [_ [E ? []]] : A b by exists E.
  by rewrite Aeab/= inE/=; apply/andP.
apply: segment_connected.
- have aba : a \in `[a, b] by rewrite in_itv /= lexx.
  exists a; split=> //; have /sabUf [i /= Di fia] := aba.
  exists [fset i]%fset; first by move=> ?; rewrite inE inE => /eqP->.
  split; last by exists i => //=; rewrite inE.
  move=> x /= aex; exists i; [by rewrite /= inE|suff /eqP-> : x == a by []].
  by rewrite eq_le !(itvP aex).
- exists B => //; rewrite openE => x [E sD [saxUf [i Di fx]]].
  have : open (f i) by have /sD := Di; rewrite inE => /fop.
  rewrite openE => /(_ _ fx) [e egt0 xe_fi]; exists e => // y xe_y.
  exists E => //; split; last by exists i => //; apply/xe_fi.
  move=> z /= ayz; have [lezx|ltxz] := lerP z x.
    by apply/saxUf; rewrite /= in_itv/= (itvP ayz) lezx.
  exists i => //; apply/xe_fi; rewrite /ball_/= distrC ger0_norm.
    have lezy : z <= y by rewrite (itvP ayz).
    rewrite ltr_subl_addl; apply: le_lt_trans lezy _; rewrite -ltr_subl_addr.
    by have := xe_y; rewrite /ball_ => /ltr_distlC_subl.
  by rewrite subr_ge0; apply/ltW.
exists A; last by rewrite predeqE => x; split=> [[] | []].
move=> x clAx; have abx : x \in `[a, b].
  by apply: interval_closed; have /closureI [] := clAx.
split=> //; have /sabUf [i Di fx] := abx.
have /fop := Di; rewrite openE => /(_ _ fx) [_ /posnumP[e] xe_fi].
have /clAx [y [[aby [E sD [sayUf _]]] xe_y]] := nbhsx_ballx x e.
exists (i |` E)%fset; first by move=> j /fset1UP[->|/sD] //; rewrite inE.
split=> [z axz|]; last first.
  exists i; first by rewrite /= !inE eq_refl.
  by apply/xe_fi; rewrite /ball_/= subrr normr0.
have [lezy|ltyz] := lerP z y.
  have /sayUf [j Dj fjz] : z \in `[a, y] by rewrite in_itv /= (itvP axz) lezy.
  by exists j => //=; rewrite inE orbC Dj.
exists i; first by rewrite /= !inE eq_refl.
apply/xe_fi; rewrite /ball_/= ger0_norm; last by rewrite subr_ge0 (itvP axz).
rewrite ltr_subl_addl -ltr_subl_addr; apply: lt_trans ltyz.
by apply: ltr_distlC_subl; rewrite distrC.
Qed.

End segment.

Lemma __deprecated__ler0_addgt0P (R : numFieldType) (x : R) :
  reflect (forall e, e > 0 -> x <= e) (x <= 0).
Proof. exact: ler_gtP. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `ler_gtP` instead which generalizes it to any upper bound.")]
Notation ler0_addgt0P := __deprecated__ler0_addgt0P.

Lemma IVT (R : realType) (f : R -> R) (a b v : R) :
  a <= b -> {within `[a, b], continuous f} ->
  minr (f a) (f b) <= v <= maxr (f a) (f b) ->
  exists2 c, c \in `[a, b] & f c = v.
Proof.
move=> leab fcont; gen have ivt : f v fcont / f a <= v <= f b ->
    exists2 c, c \in `[a, b] & f c = v; last first.
  case: (leP (f a) (f b)) => [] _ fabv /=; first exact: ivt.
  have [| |c cab /oppr_inj] := ivt (- f) (- v); last by exists c.
  - by move=> x /=; apply/continuousN/fcont.
  - by rewrite ler_oppr opprK ler_oppr opprK andbC.
move=> favfb; suff: is_interval (f @` `[a,b]).
  apply; last exact: favfb.
  - by exists a => //=; rewrite in_itv/= lexx.
  - by exists b => //=; rewrite in_itv/= leab lexx.
apply/connected_intervalP/connected_continuous_connected => //.
exact: segment_connected.
Qed.

(** Local properties in [R] *)

(* Topology on [R]² *)

(* Lemma locally_2d_align : *)
(*   forall (P Q : R -> R -> Prop) x y, *)
(*   ( forall eps : {posnum R}, (forall uv, ball (x, y) eps uv -> P uv.1 uv.2) -> *)
(*     forall uv, ball (x, y) eps uv -> Q uv.1 uv.2 ) -> *)
(*   {near x & y, forall x y, P x y} ->  *)
(*   {near x & y, forall x y, Q x y}. *)
(* Proof. *)
(* move=> P Q x y /= K => /locallyP [d _ H]. *)
(* apply/locallyP; exists d => // uv Huv. *)
(* by apply (K d) => //. *)
(* Qed. *)

(* Lemma locally_2d_1d_const_x : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally y (fun t => P x t). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* exists d => // z Hz. *)
(* by apply (Hd (x, z)). *)
(* Qed. *)

(* Lemma locally_2d_1d_const_y : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally x (fun t => P t y). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* apply/locallyP; exists d => // z Hz. *)
(* by apply (Hd (z, y)). *)
(* Qed. *)

(* Lemma locally_2d_1d_strong (P : R -> R -> Prop) (x y : R): *)
(*   (\near x & y, P x y) -> *)
(*   \forall u \near x & v \near y, *)
(*       forall (t : R), 0 <= t <= 1 -> *)
(*       \forall z \near t, \forall a \near (x + z * (u - x)) *)
(*                                & b \near (y + z * (v - y)), P a b. *)
(* Proof. *)
(* move=> P x y. *)
(* apply locally_2d_align => eps HP uv Huv t Ht. *)
(* set u := uv.1. set v := uv.2. *)
(* have Zm : 0 <= Num.max `|u - x| `|v - y| by rewrite ler_maxr 2!normr_ge0. *)
(* rewrite ler_eqVlt in Zm. *)
(* case/orP : Zm => Zm. *)
(* - apply filterE => z. *)
(*   apply/locallyP. *)
(*   exists eps => // pq. *)
(*   rewrite !(RminusE,RmultE,RplusE). *)
(*   move: (Zm). *)
(*   have : Num.max `|u - x| `|v - y| <= 0 by rewrite -(eqP Zm). *)
(*   rewrite ler_maxl => /andP[H1 H2] _. *)
(*   rewrite (_ : u - x = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite (_ : v - y = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite !(mulr0,addr0); by apply HP. *)
(* - have : Num.max (`|u - x|) (`|v - y|) < eps. *)
(*     rewrite ltr_maxl; apply/andP; split. *)
(*     - case: Huv => /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*     - case: Huv => _ /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*   rewrite -subr_gt0 => /RltP H1. *)
(*   set d1 := mk{posnum R} _ H1. *)
(*   have /RltP H2 : 0 < pos d1 / 2 / Num.max `|u - x| `|v - y| *)
(*     by rewrite mulr_gt0 // invr_gt0. *)
(*   set d2 := mk{posnum R} _ H2. *)
(*   exists d2 => // z Hz. *)
(*   apply/locallyP. *)
(*   exists [{posnum R} of d1 / 2] => //= pq Hpq. *)
(*   set p := pq.1. set q := pq.2. *)
(*   apply HP; split. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : p - x = p - (x + z * (u - x)) + (z - t + t) * (u - x)); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hp) // (ler_trans (absrM _ _)) //. *)
(*     apply (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)). *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : (q - y) = (q - (y + z * (v - y)) + (z - t + t) * (v - y))); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hq) // (ler_trans (absrM _ _)) //. *)
(*     rewrite (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)) //. *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr orbT. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(* Qed. *)
(* Admitted. *)

(* TODO redo *)
(* Lemma locally_2d_1d (P : R -> R -> Prop) x y : *)
(*   locally_2d x y P -> *)
(*   locally_2d x y (fun u v => forall t, 0 <= t <= 1 -> locally_2d (x + t * (u - x)) (y + t * (v - y)) P). *)
(* Proof. *)
(* move/locally_2d_1d_strong. *)
(* apply: locally_2d_impl. *)
(* apply locally_2d_forall => u v H t Ht. *)
(* specialize (H t Ht). *)
(* have : locally t (fun z => locally_2d (x + z * (u - x)) (y + z * (v - y)) P) by []. *)
(* by apply: locally_singleton. *)
(* Qed. *)

(* TODO redo *)
(* Lemma locally_2d_ex_dec : *)
(*   forall P x y, *)
(*   (forall x y, P x y \/ ~P x y) -> *)
(*   locally_2d x y P -> *)
(*   {d : {posnum R} | forall u v, `|u - x| < d -> `|v - y| < d -> P u v}. *)
(* Proof. *)
(* move=> P x y P_dec H. *)
(* destruct (@locally_ex _ (x, y) (fun z => P (fst z) (snd z))) as [d Hd]. *)
(* - move: H => /locallyP [e _ H]. *)
(*   by apply/locallyP; exists e. *)
(* exists d=>  u v Hu Hv. *)
(* by apply (Hd (u, v)) => /=; split; apply sub_abs_ball; rewrite absrB. *)
(* Qed. *)

Lemma compact_bounded (K : realType) (V : normedModType K) (A : set V) :
  compact A -> bounded_set A.
Proof.
rewrite compact_cover => Aco.
have covA : A `<=` \bigcup_(n : int) [set p | `|p| < n%:~R].
  by move=> p _; exists (floor `|p| + 1) => //; rewrite rmorphD/= lt_succ_floor.
have /Aco [] := covA.
  move=> n _; rewrite openE => p; rewrite /= -subr_gt0 => ltpn.
  apply/nbhs_ballP; exists (n%:~R - `|p|) => // q.
  rewrite -ball_normE /= ltr_subr_addr distrC; apply: le_lt_trans.
  by rewrite -{1}(subrK p q) ler_norm_add.
move=> D _ DcovA.
exists (\big[maxr/0]_(i : D) (fsval i)%:~R).
rewrite bigmax_real//; last by move=> ? _; rewrite realz.
split => // x ltmaxx p /DcovA [n Dn /lt_trans /(_ _)/ltW].
apply; apply: le_lt_trans ltmaxx.
have : n \in enum_fset D by [].
by rewrite enum_fsetE => /mapP[/= i iD ->]; exact/le_bigmax.
Qed.

Lemma rV_compact (T : topologicalType) n (A : 'I_n.+1 -> set T) :
  (forall i, compact (A i)) ->
  compact [ set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)].
Proof.
move=> Aico.
have : @compact (prod_topology _) [set f | forall i, A i (f i)].
  by apply: tychonoff.
move=> Aco F FF FA.
set G := [set [set f : 'I_n.+1 -> T | B (\row_j f j)] | B in F].
have row_simpl (v : 'rV[T]_n.+1) : \row_j (v ord0 j) = v.
  by apply/rowP => ?; rewrite mxE.
have row_simpl' (f : 'I_n.+1 -> T) : (\row_j f j) ord0 = f.
  by rewrite funeqE=> ?; rewrite mxE.
have [f [Af clGf]] : [set f | forall i, A i (f i)] `&`
  @cluster (prod_topology _) G !=set0.
  suff GF : ProperFilter G.
    apply: Aco; exists [set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)] => //.
    by rewrite predeqE => f; split => Af i; [have := Af i|]; rewrite row_simpl'.
  apply Build_ProperFilter.
    move=> _ [C FC <-]; have /filter_ex [v Cv] := FC.
    by exists (v ord0); rewrite /= row_simpl.
  split.
  - by exists setT => //; apply: filterT.
  - by move=> _ _ [C FC <-] [D FD <-]; exists (C `&` D) => //; apply: filterI.
  move=> C D sCD [E FE EeqC]; exists [set v : 'rV[T]_n.+1 | D (v ord0)].
    by apply: filterS FE => v Ev; apply/sCD; rewrite -EeqC/= row_simpl.
  by rewrite predeqE => ? /=; rewrite row_simpl'.
exists (\row_j f j); split; first by move=> i; rewrite mxE; apply: Af.
move=> C D FC f_D; have {}f_D :
  nbhs (f : prod_topology _) [set g | D (\row_j g j)].
  have [E f_E sED] := f_D; rewrite nbhsE.
  set Pj := fun j Bj => open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
  have exPj : forall j, exists Bj, open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
    move=> j; have := f_E ord0 j; rewrite nbhsE => - [Bj].
    by rewrite row_simpl'; exists Bj.
  exists [set g | forall j, (get (Pj j)) (g j)]; last first.
    move=> g Pg; apply: sED => i j; rewrite ord1 row_simpl'.
    by have /getPex [_ /(_ _ (Pg j))] := exPj j.
  split; last by move=> j; have /getPex [[]] := exPj j.
  exists [set [set g | forall j, get (Pj j) (g j)] | k in [set x | 'I_n.+1 x]];
    last first.
    rewrite predeqE => g; split; first by move=> [_ [_ _ <-]].
    move=> Pg; exists [set g | forall j, get (Pj j) (g j)] => //.
    by exists ord0.
  move=> _ [_ _ <-]; set s := [seq (@^~ j) @^-1` (get (Pj j)) | j : 'I_n.+1].
  exists [fset x in s]%fset.
    move=> B'; rewrite in_fset => /mapP [j _ ->]; rewrite inE.
    exists j => //; exists (get (Pj j)) => //.
    by have /getPex [[]] := exPj j.
  rewrite predeqE => g; split=> [Ig j|Ig B'].
    apply: (Ig ((@^~ j) @^-1` (get (Pj j)))).
    by rewrite /= in_fset; apply/mapP; exists j => //; rewrite mem_enum.
  by rewrite /= in_fset => /mapP [j _ ->]; apply: Ig.
have GC : G [set g | C (\row_j g j)] by exists C.
by have [g []] := clGf _ _ GC f_D; exists (\row_j (g j : T)).
Qed.

Lemma bounded_closed_compact (R : realType) n (A : set 'rV[R]_n.+1) :
  bounded_set A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact
  [set v : 'rV[R]_n.+1 | forall i, v ord0 i \in `[(- (M + 1)), (M + 1)]].
  apply: (@rV_compact _  _ (fun _ => `[(- (M + 1)), (M + 1)]%classic)).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvleM i.
suff : `|v ord0 i : R| <= M + 1 by rewrite ler_norml.
apply: le_trans (normvleM _ _); last by rewrite ltr_addl.
have /mapP[j Hj ->] : `|v ord0 i| \in [seq `|v x.1 x.2| | x : 'I_1 * 'I_n.+1].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
by rewrite [leRHS]/normr /= mx_normrE; apply/bigmax_geP; right => /=; exists j.
Qed.

(** * Some limits on real functions *)

Section Shift.

Context {R : zmodType} {T : Type}.

Definition shift (x y : R) := y + x.
Notation center c := (shift (- c)).
Arguments shift x / y.

Lemma comp_shiftK (x : R) (f : R -> T) : (f \o shift x) \o center x = f.
Proof. by rewrite funeqE => y /=; rewrite addrNK. Qed.

Lemma comp_centerK (x : R) (f : R -> T) : (f \o center x) \o shift x = f.
Proof. by rewrite funeqE => y /=; rewrite addrK. Qed.

Lemma shift0 : shift 0 = id.
Proof. by rewrite funeqE => x /=; rewrite addr0. Qed.

Lemma center0 : center 0 = id.
Proof. by rewrite oppr0 shift0. Qed.

End Shift.
Arguments shift {R} x / y.
Notation center c := (shift (- c)).

Lemma near_shift {K : numDomainType} {R : normedModType K}
   (y x : R) (P : set R) :
   (\near x, P x) = (\forall z \near y, (P \o shift (x - y)) z).
Proof.
(* rewrite propeqE nbhs0P [X in _ <-> X]nbhs0P/= -propeqE. *)
(* by apply: eq_near => e; rewrite ![_ + e]addrC addrACA subrr addr0. *)
rewrite propeqE; split=> /= /nbhs_normP [_/posnumP[e] ye];
apply/nbhs_normP; exists e%:num => //= t et.
  apply: ye; rewrite /= !opprD addrA addrACA subrr add0r.
  by rewrite opprK addrC.
have /= := ye (t - (x - y)); rewrite addrNK; apply.
by rewrite /= opprB addrCA addrA subrK.
Qed.

Lemma cvg_comp_shift {T : Type} {K : numDomainType} {R : normedModType K}
  (x y : R) (f : R -> T) :
  (f \o shift x) @ y = f @ (y + x).
Proof.
rewrite funeqE => A; rewrite /= !near_simpl (near_shift (y + x)).
by rewrite (_ : _ \o _ = A \o f) // funeqE=> z; rewrite /= opprD addNKr addrNK.
Qed.

Section continuous.
Variables (K : numFieldType) (U V : normedModType K).

Lemma continuous_shift (f : U -> V) u :
  {for u, continuous f} = {for 0, continuous (f \o shift u)}.
Proof.
by rewrite [in RHS]forE /continuous_at/= add0r cvg_comp_shift add0r.
Qed.

Lemma continuous_withinNshiftx (f : U -> V) u :
  f \o shift u @ 0^' --> f u <-> {for u, continuous f}.
Proof.
rewrite continuous_shift; split=> [cfu|].
  by apply/(continuous_withinNx _ _).2/(cvg_trans cfu); rewrite /= add0r.
by move/(continuous_withinNx _ _).1/cvg_trans; apply; rewrite /= add0r.
Qed.

End continuous.

Section Closed_Ball.

Lemma ball_open (R : numDomainType) (V : normedModType R) (x : V) (r : R) :
  0 < r -> open (ball x r).
Proof.
rewrite openE -ball_normE /interior => r0 y /= Bxy; near=> z.
rewrite /= (le_lt_trans (ler_dist_add y _ _)) // addrC -ltr_subr_addr.
by near: z; apply: cvgr_dist_lt; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.

Definition closed_ball_ (R : numDomainType) (V : zmodType) (norm : V -> R)
  (x : V) (e : R) := [set y | norm (x - y) <= e].

Lemma closed_closed_ball_ (R : realFieldType) (V : normedModType R)
  (x : V) (e : R) : closed (closed_ball_ normr x e).
Proof.
rewrite /closed_ball_ -/((normr \o (fun y => x - y)) @^-1` [set x | x <= e]).
apply: (closed_comp _ (@closed_le _ _)) => y _.
apply: (continuous_comp _ (@norm_continuous _ _ _)).
exact: (continuousB (@cst_continuous _ _ _ _)).
Qed.

Definition closed_ball (R : numDomainType) (V : pseudoMetricType R)
  (x : V) (e : R) := closure (ball x e).

Lemma closed_ballxx (R: numDomainType) (V : pseudoMetricType R) (x : V)
  (e : R) : 0 < e -> closed_ball x e x.
Proof. by move=> ?; exact/subset_closure/ballxx. Qed.

Lemma closed_ballE (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> closed_ball x r = closed_ball_ normr x r.
Proof.
move=> /posnumP[e]; rewrite eqEsubset; split => y.
  rewrite /closed_ball closureE; apply; split; first exact: closed_closed_ball_.
  by move=> z; rewrite -ball_normE; exact: ltW.
have [-> _|xy] := eqVneq x y; first exact: closed_ballxx.
rewrite /closed_ball closureE -ball_normE.
rewrite /closed_ball_ /= le_eqVlt.
move => /orP[/eqP xye B [Bc Be]|xye _ [_ /(_ _ xye)]//].
apply: Bc => B0 /nbhs_ballP[s s0] B0y.
have [es|se] := leP s e%:num; last first.
  exists x; split; first by apply: Be; rewrite ball_normE; apply: ballxx.
  by apply: B0y; rewrite -ball_normE /ball_ /= distrC xye.
exists (y + (s / 2) *: (`|x - y|^-1 *: (x - y))); split; [apply: Be|apply: B0y].
  rewrite /= opprD addrA -[X in `|X - _|](scale1r (x - y)) scalerA -scalerBl.
  rewrite -[X in X - _](@divrr _ `|x - y|) ?unitfE ?normr_eq0 ?subr_eq0//.
  rewrite -mulrBl -scalerA normrZ normfZV ?subr_eq0// mulr1.
  rewrite gtr0_norm; first by rewrite ltr_subl_addl xye ltr_addr mulr_gt0.
  by rewrite subr_gt0 xye ltr_pdivr_mulr // mulr_natr mulr2n ltr_spaddl.
rewrite -ball_normE /ball_ /= opprD addrA addrN add0r normrN normrZ.
rewrite normfZV ?subr_eq0// mulr1 normrM (gtr0_norm s0) gtr0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // ltr1n.
Qed.

Lemma closed_ball_closed (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> closed (closed_ball x r).
Proof. by move => r0; rewrite closed_ballE //; exact: closed_closed_ball_. Qed.

Lemma closed_ballR_compact (R : realType) (x e : R) : 0 < e ->
  compact (closed_ball x e).
Proof.
move=> e_gt0; have : compact `[x - e, x + e] by apply: segment_compact.
by rewrite closed_ballE//; under eq_set do rewrite in_itv -ler_distlC.
Qed.

Lemma closed_ball_subset (R : realFieldType) (M : normedModType R) (x : M)
  (r0 r1 : R) : 0 < r0 -> r0 < r1 -> closed_ball x r0 `<=` ball x r1.
Proof.
move=> r00 r01; rewrite (_ : r0 = (PosNum r00)%:num) // closed_ballE //.
by move=> m xm; rewrite -ball_normE /ball_ /= (le_lt_trans _ r01).
Qed.

Lemma nbhs_closedballP (R : realFieldType) (M : normedModType R) (B : set M)
  (x : M) : nbhs x B <-> exists (r : {posnum R}), closed_ball x r%:num `<=` B.
Proof.
split=> [/nbhs_ballP[_/posnumP[r] xrB]|[e xeB]]; last first.
  apply/nbhs_ballP; exists e%:num => //=.
  exact: (subset_trans (@subset_closure _ _) xeB).
exists (r%:num / 2)%:sgn.
apply: (subset_trans (closed_ball_subset _ _) xrB) => //=.
by rewrite lter_pdivr_mulr // ltr_pmulr // ltr1n.
Qed.

Lemma subset_closed_ball (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> ball x r `<=` closed_ball x r.
Proof. move=> r0; rewrite /closed_ball; apply: subset_closure. Qed.

Lemma locally_compactR (R : realType) : locally_compact [set: R].
Proof.
move=> x _; rewrite withinET; exists (closed_ball x 1).
  by apply/nbhs_closedballP; exists 1%:pos.
by split; [apply: closed_ballR_compact | apply: closed_ball_closed].
Qed.

(*TBA topology.v once ball_normE is there*)

Lemma interior_closed_ballE (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> (closed_ball x r)^° = ball x r.
Proof.
move=> r0; rewrite eqEsubset; split; last first.
  by rewrite -open_subsetE; [exact: subset_closure | exact: ball_open].
move=> /= t; rewrite closed_ballE // /interior /= -nbhs_ballE => [[]] s s0.
have [-> _|nxt] := eqVneq t x; first exact: ballxx.
near ((0 : R^o)^') => e; rewrite -ball_normE /closed_ball_ => tsxr.
pose z := t + `|e| *: (t - x); have /tsxr /= : `|t - z| < s.
  rewrite distrC addrAC subrr add0r normrZ normr_id.
  rewrite -ltr_pdivl_mulr ?(normr_gt0,subr_eq0) //.
  by near: e; apply/dnbhs0_lt; rewrite divr_gt0 // normr_gt0 subr_eq0.
rewrite /z opprD addrA -scalerN -{1}(scale1r (x - t)) opprB -scalerDl normrZ.
apply lt_le_trans; rewrite ltr_pmull; last by rewrite normr_gt0 subr_eq0 eq_sym.
by rewrite ger0_norm // ltr_addl normr_gt0; near: e; exists 1 => /=.
Unshelve. all: by end_near. Qed.

Lemma open_nbhs_closed_ball (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> open_nbhs x (closed_ball x r)^°.
Proof.
move=> r0; split; first exact: open_interior.
by rewrite interior_closed_ballE //; exact: ballxx.
Qed.

End Closed_Ball.

(* multi-rule bound_in_itv already exists in interval.v, but we
  advocate that it should actually have the following statement.
  This does not expose the order between interval bounds. *)
Lemma bound_itvE (R : numDomainType) (a b : R) :
  ((a \in `[a, b]) = (a <= b)) *
  ((b \in `[a, b]) = (a <= b)) *
  ((a \in `[a, b[) = (a < b)) *
  ((b \in `]a, b]) = (a < b)) *
  (a \in `[a, +oo[) *
  (a \in `]-oo, a]).
Proof. by rewrite !(boundr_in_itv, boundl_in_itv). Qed.

Lemma near_in_itv {R : realFieldType} (a b : R) :
  {in `]a, b[, forall y, \forall z \near y, z \in `]a, b[}.
Proof. exact: interval_open. Qed.

Notation "f @`[ a , b ]" :=
  (`[minr (f a) (f b), maxr (f a) (f b)]) : ring_scope.
Notation "f @`[ a , b ]" :=
  (`[minr (f a) (f b), maxr (f a) (f b)]%classic) : classical_set_scope.
Notation "f @`] a , b [" :=
  (`](minr (f a) (f b)), (maxr (f a) (f b))[) : ring_scope.
Notation "f @`] a , b [" :=
  (`](minr (f a) (f b)), (maxr (f a) (f b))[%classic) : classical_set_scope.

Section image_interval.
Variable R : realDomainType.
Implicit Types (a b : R) (f : R -> R).

Lemma mono_mem_image_segment a b f : monotonous `[a, b] f ->
  {homo f : x / x \in `[a, b] >-> x \in f @`[a, b]}.
Proof.
move=> [fle|fge] x xab; have leab : a <= b by rewrite (itvP xab).
  have: f a <= f b by rewrite fle ?bound_itvE.
  by case: leP => // fafb _; rewrite in_itv/= !fle ?(itvP xab).
have: f a >= f b by rewrite fge ?bound_itvE.
by case: leP => // fafb _; rewrite in_itv/= !fge ?(itvP xab).
Qed.

Lemma mono_mem_image_itvoo a b f : monotonous `[a, b] f ->
  {homo f : x / x \in `]a, b[ >-> x \in f @`]a, b[}.
Proof.
move=> []/[dup] => [/leW_mono_in|/leW_nmono_in] flt fle x xab;
    have ltab : a < b by rewrite (itvP xab).
  have: f a <= f b by rewrite ?fle ?bound_itvE ?ltW.
  by case: leP => // fafb _; rewrite in_itv/= ?flt ?in_itv/= ?(itvP xab, lexx).
have: f a >= f b by rewrite fle ?bound_itvE ?ltW.
by case: leP => // fafb _; rewrite in_itv/= ?flt ?in_itv/= ?(itvP xab, lexx).
Qed.

Lemma mono_surj_image_segment a b f : a <= b ->
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  f @` `[a, b] = f @`[a, b]%classic.
Proof.
move=> leab fmono; apply: surj_image_eq => _ /= [x xab <-];
exact: mono_mem_image_segment.
Qed.

Lemma inc_segment_image a b f : f a <= f b -> f @`[a, b] = `[f a, f b].
Proof. by case: ltrP. Qed.

Lemma dec_segment_image a b f : f b <= f a -> f @`[a, b] = `[f b, f a].
Proof. by case: ltrP. Qed.

Lemma inc_surj_image_segment a b f : a <= b ->
    {in `[a, b] &, {mono f : x y / x <= y}} ->
    set_surj `[a, b] `[f a, f b] f ->
  f @` `[a, b] = `[f a, f b]%classic.
Proof.
move=> leab fle f_surj; have fafb : f a <= f b by rewrite fle ?bound_itvE.
by rewrite mono_surj_image_segment ?inc_segment_image//; left.
Qed.

Lemma dec_surj_image_segment a b f : a <= b ->
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  f @` `[a, b] = `[f b, f a]%classic.
Proof.
move=> leab fge f_surj; have fafb : f b <= f a by rewrite fge ?bound_itvE.
by rewrite mono_surj_image_segment ?dec_segment_image//; right.
Qed.

Lemma inc_surj_image_segmentP a b f : a <= b ->
    {in `[a, b] &, {mono f : x y / x <= y}} ->
    set_surj `[a, b] `[f a, f b] f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in `[f a, f b]).
Proof.
move=> /inc_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

Lemma dec_surj_image_segmentP a b f : a <= b ->
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in `[f b, f a]).
Proof.
move=> /dec_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

Lemma mono_surj_image_segmentP a b f : a <= b ->
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in f @`[a, b]).
Proof.
move=> /mono_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

End image_interval.

Section LinearContinuousBounded.

Variables (R : numFieldType) (V W : normedModType R).

Lemma linear_boundedP (f : {linear V -> W}) : bounded_near f (nbhs 0) <->
  \forall r \near +oo, forall x, `|f x| <= r * `|x|.
Proof.
split=> [|/pinfty_ex_gt0 [r r0 Bf]]; last first.
  apply/ex_bound; exists r; apply/nbhs_norm0P; exists 1 => //= x /=.
  by rewrite -(gtr_pmulr _ r0) => /ltW; exact/le_trans/Bf.
rewrite /bounded_near => /pinfty_ex_gt0 [M M0 /nbhs_norm0P [_/posnumP[e] efM]].
near (0 : R)^'+ => d; near=> r => x.
have[->|x0] := eqVneq x 0; first by rewrite raddf0 !normr0 mulr0.
have nd0 : d / `|x| > 0 by rewrite divr_gt0 ?normr_gt0.
have: `|f (d / `|x| *: x)| <= M.
  by apply: efM => /=; rewrite normrZ gtr0_norm// divfK ?normr_eq0//.
rewrite linearZ/= normrZ gtr0_norm// -ler_pdivl_mull//; move/le_trans; apply.
rewrite invfM invrK mulrAC ler_wpmul2r//; near: r; apply: nbhs_pinfty_ge.
by rewrite rpredM// ?rpredV ?gtr0_real.
Unshelve. all: by end_near. Qed.

Lemma continuous_linear_bounded (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs x).
Proof.
rewrite /prop_for/continuous_at linear0 /bounded_near => f0.
near=> M; apply/nbhs0P.
near do rewrite /= linearD (le_trans (ler_norm_add _ _))// -ler_subr_addl.
by apply: cvgr0_norm_le; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma __deprecated__linear_continuous0 (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs (0 : V)).
Proof. exact: continuous_linear_bounded. Qed.

Lemma bounded_linear_continuous (f : {linear V -> W}) :
  bounded_near f (nbhs (0 : V)) -> continuous f.
Proof.
move=> /linear_boundedP [y [yreal fr]] x; near +oo_R => r.
apply/(@cvgrPdist_lt _ _ _ (nbhs x)) => e e_gt0; near=> z; rewrite -linearB.
rewrite (le_lt_trans (fr r _ _))// -?ltr_pdivl_mull//.
by near: z; apply: cvgr_dist_lt => //; rewrite mulrC divr_gt0.
Unshelve. all: by end_near. Qed.

Lemma __deprecated__linear_bounded0 (f : {linear V -> W}) :
  bounded_near f (nbhs (0 : V)) -> {for 0, continuous f}.
Proof. by move=> ? ?; exact: bounded_linear_continuous. Qed.

Lemma continuousfor0_continuous (f : {linear V -> W}) :
  {for 0, continuous f} -> continuous f.
Proof. by move=> /continuous_linear_bounded/bounded_linear_continuous. Qed.

Lemma linear_bounded_continuous (f : {linear V -> W}) :
  bounded_near f (nbhs 0) <-> continuous f.
Proof.
split; first exact: bounded_linear_continuous.
by move=> /(_ 0); apply: continuous_linear_bounded.
Qed.

Lemma bounded_funP (f : {linear V -> W}) :
  (forall r, exists M, forall x, `|x| <= r -> `|f x| <= M) <->
  bounded_near f (nbhs (0 : V)).
Proof.
split => [/(_ 1) [M Bf]|/linear_boundedP fr y].
  apply/ex_bound; exists M; apply/nbhs_normP => /=; exists 1 => //= x /=.
  by rewrite sub0r normrN => x1; exact/Bf/ltW.
near +oo_R => r; exists (r * y) => x xe.
rewrite (@le_trans _ _ (r * `|x|)) //; first by move: {xe} x; near: r.
by rewrite ler_pmul //.
Unshelve. all: by end_near. Qed.

End LinearContinuousBounded.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="generalized to `continuous_linear_bounded`")]
Notation linear_continuous0 := __deprecated__linear_continuous0.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="generalized to `bounded_linear_continuous`")]
Notation linear_bounded0 := __deprecated__linear_bounded0.
