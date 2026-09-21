/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.LoopExample
import LeanPool.RegtsSevenster.RS.TheoremConverse
import LeanPool.RegtsSevenster.RS.TheoremForward
import LeanPool.RegtsSevenster.RS.TheoremQuant
import LeanPool.RegtsSevenster.RS.Summit

/-!
# The statement surface, pinned

Reading a formalization means reading what its theorems *say*, and
that reduces to the handful of definitions their statements are
phrased in.  This module lists exactly those definitions and pins
each one's type, and then pins the type of every theorem of record.

For the development's own definitions this is a *signature* audit.
Each `#guard_msgs` turns a change to a pinned type into a compile
error, so nothing enters or leaves a summit statement unnoticed; but
a type is not a meaning, and a definition can be rewritten while
keeping it — `EdgeRankBounded` would still read
`(ClosedFragment → ℂ) → ℕ → Prop` whatever it bounded.  Reading the
summits therefore means reading the linked definitions, which is
what the file lists them for.  For the one definition where a
convention could silently be wrong — `mixedPartition`, which carries
the circuit sign, the Eulerian condition and the odd-colour
bookkeeping — the last section pins a value instead of a type.

Deligne's theorem is pinned by content, as is every predicate its
hypothesis list is phrased in. The corollary definitions are likewise
pinned by content so the meaning of rank, minimum and prescribed
dimensions is visible. `Blueprint.lean` and its parts then pin what
the summits depend on.

The main definitions live in `RS/Definitions.lean`, the
self-contained statement surface that the comparator certification
trusts. `RS/DimensionDefinitions.lean` adds the growth, minimum and
prescribed-dimension surface and imports only that main surface.
-/

namespace RS

/-! ## The model

A fragment is a flag (half-edge) graph over a label type; a closed
fragment is one with no boundary labels, and `Fragment.Equiv` is
isomorphism of fragments. -/

/- Upstream audit output: Fragment : Type → Type 1 -/

/- Upstream audit output: ClosedFragment : Type 1 -/

/- Upstream audit output: emptyClosedFragment : ClosedFragment -/

/- Upstream audit output: @Fragment.Equiv : {α : Type} → Fragment α → Fragment α → Type -/

/-! ## Mixed partition functions

`MixedFunctional k ℓ` is a vertex functional with `k` even and `2ℓ`
odd colours, `mixedPartition` is Definition 5 of Regts–Sevenster on
the flag model, and the two predicates say that a parameter is such
a partition function, with and without a bound on the dimensions. -/

/- Upstream audit output: MixedFunctional : ℕ → ℕ → Type -/

/- Upstream audit output: @mixedPartition : {α : Type} → {k ℓ : ℕ} → MixedFunctional k ℓ → Fragment α → ℂ -/

/- Upstream audit output: IsMixedPartitionFunction : (ClosedFragment → ℂ) → Prop -/

/- Upstream audit output: IsMixedPartitionFunctionBounded : (ClosedFragment → ℂ) → ℕ → Prop -/

/- Upstream audit output: TotalBoundedMixedModel : (ClosedFragment → ℂ) → ℕ → Type -/

/- Upstream audit output: IsMixedPartitionFunctionTotalBounded : (ClosedFragment → ℂ) → ℕ → Prop -/

/-! The total bound is pinned by content: its witness bounds the
sum of both dimensions and evaluates to the original parameter. -/

/--
info: structure RS.TotalBoundedMixedModel (f : ClosedFragment → ℂ) (B : ℕ) : Type
number of parameters: 2
fields:
  RS.TotalBoundedMixedModel.k : ℕ
  RS.TotalBoundedMixedModel.ℓ : ℕ
  RS.TotalBoundedMixedModel.functional : MixedFunctional self.k self.ℓ
  RS.TotalBoundedMixedModel.dimension_le : self.k + 2 * self.ℓ ≤ B
  RS.TotalBoundedMixedModel.partition_eq : ∀ (W : ClosedFragment), f W = mixedPartition self.functional W
constructor:
  RS.TotalBoundedMixedModel.mk {f : ClosedFragment → ℂ} {B : ℕ} (k ℓ : ℕ) (functional : MixedFunctional k ℓ)
    (dimension_le : k + 2 * ℓ ≤ B) (partition_eq : ∀ (W : ClosedFragment), f W = mixedPartition functional W) :
    TotalBoundedMixedModel f B
-/

/--
info: def RS.IsMixedPartitionFunctionTotalBounded : (ClosedFragment → ℂ) → ℕ → Prop :=
fun (f : ClosedFragment → ℂ) (B : ℕ) => Nonempty (TotalBoundedMixedModel f B)
-/

/-! ## Edge-connection rank

`EdgeRankBounded f R` says the connection pairings of `f` have rank
at most `R ^ t` at every arity `t`; `EdgeRankParameter R` packages a
normalized, isomorphism-invariant parameter with that bound. -/

/- Upstream audit output: EdgeRankBounded : (ClosedFragment → ℂ) → ℕ → Prop -/

/- Upstream audit output: EdgeRankParameter : ℕ → Type 1 -/

/-! ## The statements and Deligne's theorem -/

/- Upstream audit output: RegtsSevensterStatement : Prop -/

/- Upstream audit output: RegtsSevensterStatementQuant : Prop -/

/- Upstream audit output: RegtsSevensterStatementTotal : Prop -/

/--
info: def RS.RegtsSevensterStatementTotal : Prop :=
∀ (R : ℕ) (f : EdgeRankParameter R), IsMixedPartitionFunctionTotalBounded f.val R
-/

/- Upstream audit output: RegtsSevensterConverseStatement : Prop -/

/- Upstream audit output: DeligneTheoremStatement : Prop -/

/-! ### Deligne's theorem, unfolded

A type is not a meaning, so `DeligneTheoremStatement` is pinned by
content as well as by name: its hypothesis list, and the definition
of every predicate that list is phrased in.  An auditor compares
what follows with Deligne's Théorème 0.6 and §0.1; a change to any
of it is a compile error.  The statement is proved in
`RS/Classical/Deligne/`, so the pin fixes the meaning of a theorem
of this tree rather than of an assumption.
-/

/--
info: def RS.HasScalarUnit.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] →
    [inst_1 : CategoryTheory.Preadditive A] →
      [CategoryTheory.Linear ℂ A] → [CategoryTheory.MonoidalCategory A] → Prop :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.Preadditive A] [CategoryTheory.Linear ℂ A]
    [CategoryTheory.MonoidalCategory A] =>
  Function.Bijective fun (c : ℂ) =>
    c • CategoryTheory.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorUnit A)
-/

/--
info: tensorPow_zero : ∀ (A : Type u_2) [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] (X : A),
  tensorPow A X 0 = CategoryTheory.MonoidalCategoryStruct.tensorUnit A
-/

/--
info: tensorPow_succ : ∀ (A : Type u_2) [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] (X : A) (n : ℕ),
  tensorPow A X (n + 1) = CategoryTheory.MonoidalCategoryStruct.tensorObj (tensorPow A X n) X
-/

/--
info: def RS.mixedPow.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] →
    [inst_1 : CategoryTheory.MonoidalCategory A] → [CategoryTheory.RigidCategory A] → A → ℕ → ℕ → A :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.MonoidalCategory A] [CategoryTheory.RigidCategory A]
    (X : A) (a b : ℕ) =>
  CategoryTheory.MonoidalCategoryStruct.tensorObj (tensorPow A X a) (tensorPow A Xᘁ b)
-/

/--
info: def RS.IsSubquotientOf.{v, u} : {C : Type u} → [CategoryTheory.Category.{v, u} C] → C → C → Prop :=
fun {C : Type u} [CategoryTheory.Category.{v, u} C] (Y Z : C) =>
  ∃ (S : C) (i : S ⟶ Z) (p : S ⟶ Y), CategoryTheory.Mono i ∧ CategoryTheory.Epi p
-/

/--
info: def RS.TensorGeneratedBy.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] →
    [inst_1 : CategoryTheory.MonoidalCategory A] →
      [inst_2 : CategoryTheory.Preadditive A] →
        [CategoryTheory.Limits.HasFiniteBiproducts A] → [CategoryTheory.RigidCategory A] → A → Prop :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.MonoidalCategory A] [CategoryTheory.Preadditive A]
    [CategoryTheory.Limits.HasFiniteBiproducts A] [CategoryTheory.RigidCategory A] (X : A) =>
  ∀ (Y : A), ∃ (k : ℕ) (ab : Fin k → ℕ × ℕ), IsSubquotientOf Y (⨁ fun (t : Fin k) => mixedPow A X (ab t).1 (ab t).2)
-/

/--
info: def RS.LengthLE.{v, u} : {C : Type u} → [CategoryTheory.Category.{v, u} C] → C → ℕ → Prop :=
fun {C : Type u} [CategoryTheory.Category.{v, u} C] (Y : C) (k : ℕ) =>
  ∀ (f : Fin (k + 2) → CategoryTheory.Subobject Y), ¬StrictMono f
-/

/--
info: def RS.ModerateLengthGrowth.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] → [CategoryTheory.MonoidalCategory A] → Prop :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.MonoidalCategory A] =>
  ∀ (Y : A), ∃ (C : ℕ) (c : ℕ), ∀ (N : ℕ), LengthLE (tensorPow A Y N) (C * c ^ N)
-/

/--
info: structure RS.DeligneFibreFunctor.{u_1, u_2} (A : Type u_1) [CategoryTheory.Category.{u_2, u_1} A]
  [CategoryTheory.MonoidalCategory A] [CategoryTheory.SymmetricCategory A] [CategoryTheory.Preadditive A]
  [CategoryTheory.Linear ℂ A] : Type (max (max 1 u_1) u_2)
number of parameters: 6
fields:
  RS.DeligneFibreFunctor.ω : CategoryTheory.Functor A SuperVect
  RS.DeligneFibreFunctor.braided : self.ω.Braided
  RS.DeligneFibreFunctor.additive : self.ω.Additive
  RS.DeligneFibreFunctor.linear : CategoryTheory.Functor.Linear ℂ self.ω
  RS.DeligneFibreFunctor.faithful : self.ω.Faithful
  RS.DeligneFibreFunctor.preservesFiniteLimits : CategoryTheory.Limits.PreservesFiniteLimits self.ω
  RS.DeligneFibreFunctor.preservesFiniteColimits : CategoryTheory.Limits.PreservesFiniteColimits self.ω
constructor:
  RS.DeligneFibreFunctor.mk.{u_1, u_2} {A : Type u_1} [CategoryTheory.Category.{u_2, u_1} A]
    [CategoryTheory.MonoidalCategory A] [CategoryTheory.SymmetricCategory A] [CategoryTheory.Preadditive A]
    [CategoryTheory.Linear ℂ A] (ω : CategoryTheory.Functor A SuperVect) (braided : ω.Braided) (additive : ω.Additive)
    (linear : CategoryTheory.Functor.Linear ℂ ω) (faithful : ω.Faithful)
    (preservesFiniteLimits : CategoryTheory.Limits.PreservesFiniteLimits ω)
    (preservesFiniteColimits : CategoryTheory.Limits.PreservesFiniteColimits ω) : DeligneFibreFunctor A
-/

/--
info: def RS.DeligneTheoremStatement.{u, v} : Prop :=
∀ (A : Type u) [inst : CategoryTheory.Category.{v, u} A] [inst_1 : CategoryTheory.Abelian A]
  [inst_2 : CategoryTheory.Linear ℂ A] [inst_3 : CategoryTheory.MonoidalCategory A]
  [inst_4 : CategoryTheory.SymmetricCategory A] [inst_5 : CategoryTheory.MonoidalPreadditive A]
  [CategoryTheory.MonoidalLinear ℂ A] [inst_7 : CategoryTheory.Limits.HasFiniteBiproducts A]
  [inst_8 : CategoryTheory.RigidCategory A] [CategoryTheory.EssentiallySmall.{v, v, u} A],
  HasScalarUnit A → (∃ (X : A), TensorGeneratedBy A X) → ModerateLengthGrowth A → Nonempty (DeligneFibreFunctor A)
-/

/-! ## The theorems of record

The converse carries no hypothesis; the forward direction and the
characterization carry Deligne's theorem and nothing else. -/

/- Upstream audit output: regts_sevenster_converse : RegtsSevensterConverseStatement -/

/- Upstream audit output: regts_sevenster_deligne_only : DeligneTheoremStatement → RegtsSevensterStatement -/

/--
info: regts_sevenster_quant_deligne_only : DeligneTheoremStatement → RegtsSevensterStatementQuant
-/

/- Upstream audit output: regts_sevenster_total_deligne_only : DeligneTheoremStatement → RegtsSevensterStatementTotal -/

/- Upstream audit output: regts_sevenster_total : RegtsSevensterStatementTotal -/

/--
info: @edgeRankBounded_of_mixedBounded : ∀ {f : ClosedFragment → ℂ} {B : ℕ},
  IsMixedPartitionFunctionBounded f B → EdgeRankBounded f (max 1 (2 * B))
-/

/--
info: regts_sevenster_iff : DeligneTheoremStatement →
  ∀ (f : ClosedFragment → ℂ),
    f emptyClosedFragment = 1 →
      (∀ (W₁ W₂ : ClosedFragment) (a : Fragment.Equiv W₁ W₂), f W₁ = f W₂) →
        ((∃ R, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f)
-/

/--
info: regts_sevenster_quant_roundtrip : DeligneTheoremStatement →
  ∀ (f : ClosedFragment → ℂ),
    f emptyClosedFragment = 1 →
      (∀ (W₁ W₂ : ClosedFragment) (a : Fragment.Equiv W₁ W₂), f W₁ = f W₂) →
        (∀ (R : ℕ), EdgeRankBounded f R → IsMixedPartitionFunctionBounded f ⌊2 * Real.exp 1 * ↑R⌋₊) ∧
          ∀ (B : ℕ), IsMixedPartitionFunctionBounded f B → EdgeRankBounded f (max 1 (2 * B))
-/

/-! ## The definition, evaluated

A pinned type says nothing about a convention, and `mixedPartition`
is where the conventions are: the circuit sign, the Eulerian
condition, a loop's two incidences at its vertex, the difference
between a loop and a free circle, and the `η`-convention through
which distinct odd colourings reach a common basis vector.

The accompanying paper's worked example fixes all five at once.
Against the functional `charPolyFunctional θ`, whose mixed partition
function is the characteristic polynomial `det(θ I − A_G)` on graphs
without free circles, the one-vertex one-loop graph has `A_L = (2)`
and so must evaluate to `θ − 2`.  It does
(`RS/Novel/Skein/LoopExample.lean`); a sign error in any one of the
five would change the number.  Adjoining a free circle sends the
same functional to `0`, since `k − 2ℓ = 0` here — the same graph,
worth `θ − 2` with a loop and `0` with a circle. -/

/- Upstream audit output: loopGraph : ClosedFragment -/

/- Upstream audit output: charPolyFunctional : ℂ → MixedFunctional 2 1 -/

/- Upstream audit output: mixedPartition_loopGraph : ∀ (θ : ℂ), mixedPartition (charPolyFunctional θ) loopGraph = θ - 2 -/

/- Upstream audit output: mixedPartition_loopGraphCircle : ∀ (θ : ℂ), mixedPartition (charPolyFunctional θ) loopGraphCircle = 0 -/

/-! ## Minimum dimensions, rank growth and padding -/

/--
info: circlesClosed : ℕ → ClosedFragment
-/

/--
info: connectionRank : (ClosedFragment → ℂ) → ℕ → ℕ
-/

/--
info: @MixedFunctional.Represents : {k ℓ : ℕ} → MixedFunctional k ℓ → (ClosedFragment → ℂ) → Prop
-/

/--
info: minimumColourDimension : (ClosedFragment → ℂ) → ℕ
-/

/--
info: PrescribedColourBounds : (ClosedFragment → ℂ) → ℕ → ℕ → Prop
-/

/--
info: @regts_sevenster_minimum : ∀ {R : ℕ} (f : EdgeRankParameter R),
  IsMixedPartitionFunctionTotalBounded f.val (minimumColourDimension f.val)
-/

/--
info: @regts_sevenster_rank_growth : ∀ {R : ℕ} (f : EdgeRankParameter R),
  Filter.Tendsto (fun n => ↑(connectionRank f.val (2 * n)) ^ (↑(2 * n))⁻¹) Filter.atTop
    (nhds ↑(minimumColourDimension f.val))
-/

/--
info: regts_sevenster_prescribed : ∀ (f : ClosedFragment → ℂ),
  f emptyClosedFragment = 1 →
    (∀ (W₁ W₂ : ClosedFragment) (a : Fragment.Equiv W₁ W₂), f W₁ = f W₂) →
      ∀ (k ℓ : ℕ), (∃ h, h.Represents f) ↔ PrescribedColourBounds f k ℓ
-/

/--
info: regts_sevenster_minimum_deligne_only : DeligneTheoremStatement →
  ∀ {R : ℕ} (f : EdgeRankParameter R), IsMixedPartitionFunctionTotalBounded f.val (minimumColourDimension f.val)
-/

/--
info: regts_sevenster_rank_growth_deligne_only : DeligneTheoremStatement →
  ∀ {R : ℕ} (f : EdgeRankParameter R),
    Filter.Tendsto (fun n => ↑(connectionRank f.val (2 * n)) ^ (↑(2 * n))⁻¹) Filter.atTop
      (nhds ↑(minimumColourDimension f.val))
-/

/--
info: regts_sevenster_prescribed_deligne_only : DeligneTheoremStatement →
  ∀ (f : ClosedFragment → ℂ),
    f emptyClosedFragment = 1 →
      (∀ (W₁ W₂ : ClosedFragment) (a : Fragment.Equiv W₁ W₂), f W₁ = f W₂) →
        ∀ (K L : ℕ), (∃ h, h.Represents f) ↔ PrescribedColourBounds f K L
-/

/--
info: @minimumColourDimension_le_of_represents : ∀ {f : ClosedFragment → ℂ} {k ℓ : ℕ} (h : MixedFunctional k ℓ),
  h.Represents f → minimumColourDimension f ≤ k + 2 * ℓ
-/

/--
info: @TotalBoundedMixedModel.dimension_eq_minimum : ∀ {f : ClosedFragment → ℂ}
  (M : TotalBoundedMixedModel f (minimumColourDimension f)), M.k + 2 * M.ℓ = minimumColourDimension f
-/

/--
info: @TotalBoundedMixedModel.even_dimension_eq : ∀ {f : ClosedFragment → ℂ}
  (M : TotalBoundedMixedModel f (minimumColourDimension f)),
  ↑M.k = (↑(minimumColourDimension f) + f (circlesClosed 1)) / 2
-/

/--
info: @TotalBoundedMixedModel.half_odd_dimension_eq : ∀ {f : ClosedFragment → ℂ}
  (M : TotalBoundedMixedModel f (minimumColourDimension f)),
  ↑M.ℓ = (↑(minimumColourDimension f) - f (circlesClosed 1)) / 4
-/

/--
info: @MixedFunctional.padColours : {k ℓ K L : ℕ} → MixedFunctional k ℓ → k ≤ K → ℓ ≤ L → MixedFunctional K L
-/

/--
info: @MixedFunctional.padColours_represents : ∀ {k ℓ K L : ℕ} (h : MixedFunctional k ℓ) (hk : k ≤ K) (hℓ : ℓ ≤ L),
  ↑K - 2 * ↑L = ↑k - 2 * ↑ℓ → ∀ {f : ClosedFragment → ℂ}, h.Represents f → (h.padColours hk hℓ).Represents f
-/

/--
info: @connectionRank_cast_eq_rank : ∀ {R : ℕ} (f : EdgeRankParameter R) (t : ℕ),
  ↑(connectionRank f.val t) = Module.rank ℂ ↥(connectionMap f.val t).range
-/

/--
info: def RS.circlesClosed : ℕ → ClosedFragment :=
fun c => (Fragment.circlesOnly c).relabel (Equiv.equivOfIsEmpty Empty (Fin 0))
-/

/--
info: def RS.connectionRank : (ClosedFragment → ℂ) → ℕ → ℕ :=
fun f t => Module.finrank ℂ ↥(connectionMap f t).range
-/

/--
info: def RS.MixedFunctional.Represents : {k ℓ : ℕ} → MixedFunctional k ℓ → (ClosedFragment → ℂ) → Prop :=
fun {k ℓ} h f => ∀ (W : ClosedFragment), f W = mixedPartition h W
-/

/--
info: def RS.minimumColourDimension : (ClosedFragment → ℂ) → ℕ :=
fun f => sInf {d | IsMixedPartitionFunctionTotalBounded f d}
-/

/--
info: structure RS.PrescribedColourBounds (f : ClosedFragment → ℂ) (k ℓ : ℕ) : Prop
number of parameters: 3
fields:
  RS.PrescribedColourBounds.circle_eq : f (circlesClosed 1) = ↑k - 2 * ↑ℓ
  RS.PrescribedColourBounds.rank_bounded : EdgeRankBounded f (k + 2 * ℓ)
constructor:
  RS.PrescribedColourBounds.mk {f : ClosedFragment → ℂ} {k ℓ : ℕ} (circle_eq : f (circlesClosed 1) = ↑k - 2 * ↑ℓ)
    (rank_bounded : EdgeRankBounded f (k + 2 * ℓ)) : PrescribedColourBounds f k ℓ
-/

end RS
