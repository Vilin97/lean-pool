/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanMergelyanAssembly

/-!
# From local smooth outer approximation to a nested exhaustion

An exact realization of every metric thickening by a smooth Jordan domain is
far stronger than the planar approximation theorem needed by the
Crouzeix--Palencia assembly.  This file isolates the correct local statement:
for every positive radius there is a smooth Jordan domain between `K` and
that radius's open thickening of `K`.

Compactness then turns these independent approximations into a strict nested
exhaustion.  At each successor stage, a closed thickening of `K` is chosen
inside the preceding open carrier, and the next approximation radius is also
bounded by `1/(n+1)`.  The first bound gives strict nesting; the second makes
the intersection exactly `K`.
-/

@[expose] public section

open Complex Metric Set
open scoped InnerProductSpace

/-- A planar set admits smooth Jordan outer approximations at every positive
metric scale. -/
def HasSmoothJordanOuterApproximation (K : Set ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Omega : SmoothJordanDomain,
    K ⊆ Omega.carrier ∧
      closure Omega.carrier ⊆ Metric.thickening ε K

/-- Choose a smooth Jordan domain approximating a set at a prescribed positive scale. -/
noncomputable def chooseSmoothJordanOuter
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K)
    (ε : ℝ) (hε : 0 < ε) : SmoothJordanDomain :=
  Classical.choose (houter ε hε)

/-- The chosen outer domain contains the target set. -/
theorem target_subset_chooseSmoothJordanOuter
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K)
    (ε : ℝ) (hε : 0 < ε) :
    K ⊆ (chooseSmoothJordanOuter houter ε hε).carrier :=
  (Classical.choose_spec (houter ε hε)).1

/-- The chosen outer domain has closure inside the prescribed thickening. -/
theorem closure_chooseSmoothJordanOuter_subset_thickening
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K)
    (ε : ℝ) (hε : 0 < ε) :
    closure (chooseSmoothJordanOuter houter ε hε).carrier ⊆
      Metric.thickening ε K :=
  (Classical.choose_spec (houter ε hε)).2

/-- A smooth Jordan domain whose interior contains the target set. -/
abbrev ContainingSmoothJordanDomain (K : Set ℂ) :=
  { Omega : SmoothJordanDomain // K ⊆ Omega.carrier }

/-- A positive thickening radius for a compact set inside the current Jordan domain. -/
noncomputable def smoothJordanNestingRadius
    {K : Set ℂ} (hK : IsCompact K)
    (Omega : ContainingSmoothJordanDomain K) : ℝ :=
  Classical.choose
    (hK.exists_cthickening_subset_open
      Omega.val.isOpen_carrier Omega.property)

/-- The nesting radius is strictly positive. -/
theorem smoothJordanNestingRadius_pos
    {K : Set ℂ} (hK : IsCompact K)
    (Omega : ContainingSmoothJordanDomain K) :
    0 < smoothJordanNestingRadius hK Omega :=
  (Classical.choose_spec
    (hK.exists_cthickening_subset_open
      Omega.val.isOpen_carrier Omega.property)).1

/-- The closed thickening at the nesting radius lies inside the current domain. -/
theorem cthickening_smoothJordanNestingRadius_subset
    {K : Set ℂ} (hK : IsCompact K)
    (Omega : ContainingSmoothJordanDomain K) :
    Metric.cthickening (smoothJordanNestingRadius hK Omega) K ⊆
      Omega.val.carrier :=
  (Classical.choose_spec
    (hK.exists_cthickening_subset_open
      Omega.val.isOpen_carrier Omega.property)).2

private theorem smoothApproxRadius_pos_outer (n : ℕ) :
    0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity

/-- The smaller of the nesting radius and the next approximation scale. -/
noncomputable def smoothJordanOuterStepRadius
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) : ℝ :=
  min (smoothJordanNestingRadius hK Omega) (smoothApproxRadius (n + 1))

/-- The next approximation scale is strictly positive. -/
theorem smoothJordanOuterStepRadius_pos
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    0 < smoothJordanOuterStepRadius hK n Omega := by
  exact lt_min (smoothJordanNestingRadius_pos hK Omega)
    (smoothApproxRadius_pos_outer (n + 1))

/-- The next approximation scale does not exceed the nesting radius. -/
theorem smoothJordanOuterStepRadius_le_nesting
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    smoothJordanOuterStepRadius hK n Omega ≤
      smoothJordanNestingRadius hK Omega :=
  min_le_left _ _

/-- The next approximation scale does not exceed the scheduled radius. -/
theorem smoothJordanOuterStepRadius_le_schedule
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    smoothJordanOuterStepRadius hK n Omega ≤
      smoothApproxRadius (n + 1) :=
  min_le_right _ _

/-- The next containing Jordan domain, chosen inside the current domain and scale. -/
noncomputable def nextSmoothJordanOuter
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    ContainingSmoothJordanDomain K :=
  ⟨chooseSmoothJordanOuter houter
      (smoothJordanOuterStepRadius hK n Omega)
      (by exact smoothJordanOuterStepRadius_pos hK n Omega),
    by
      exact target_subset_chooseSmoothJordanOuter houter
        (smoothJordanOuterStepRadius hK n Omega)
        (smoothJordanOuterStepRadius_pos hK n Omega)⟩

/-- The closure of the next outer domain lies inside the current domain. -/
theorem closure_nextSmoothJordanOuter_subset_carrier
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    closure (nextSmoothJordanOuter hK houter n Omega).val.carrier ⊆
      Omega.val.carrier := by
  apply (closure_chooseSmoothJordanOuter_subset_thickening houter
    (smoothJordanOuterStepRadius hK n Omega)
    (by exact smoothJordanOuterStepRadius_pos hK n Omega)).trans
  apply (Metric.thickening_subset_cthickening_of_le
    (smoothJordanOuterStepRadius_le_nesting hK n Omega) K).trans
  exact cthickening_smoothJordanNestingRadius_subset hK Omega

/-- The closure of the next outer domain lies inside the next scheduled thickening. -/
theorem closure_nextSmoothJordanOuter_subset_schedule
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    closure (nextSmoothJordanOuter hK houter n Omega).val.carrier ⊆
      convexThickeningApprox K (n + 1) := by
  apply (closure_chooseSmoothJordanOuter_subset_thickening houter
    (smoothJordanOuterStepRadius hK n Omega)
    (by exact smoothJordanOuterStepRadius_pos hK n Omega)).trans
  unfold convexThickeningApprox
  exact Metric.thickening_mono
    (smoothJordanOuterStepRadius_le_schedule hK n Omega) K

/-- The initial Jordan domain at the first approximation scale. -/
noncomputable def firstSmoothJordanOuter
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K) :
    ContainingSmoothJordanDomain K :=
  ⟨chooseSmoothJordanOuter houter (smoothApproxRadius 0)
      (by exact smoothApproxRadius_pos_outer 0),
    by
      exact target_subset_chooseSmoothJordanOuter houter (smoothApproxRadius 0)
        (smoothApproxRadius_pos_outer 0)⟩

/-- The initial outer domain has closure inside the initial scheduled thickening. -/
theorem closure_firstSmoothJordanOuter_subset_schedule
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K) :
    closure (firstSmoothJordanOuter houter).val.carrier ⊆
      convexThickeningApprox K 0 := by
  exact closure_chooseSmoothJordanOuter_subset_thickening houter
    (smoothApproxRadius 0) (by exact smoothApproxRadius_pos_outer 0)

/-- The recursively chosen sequence of nested smooth Jordan outer approximations. -/
noncomputable def nestedSmoothJordanOuterStage
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) :
    ℕ → ContainingSmoothJordanDomain K :=
  fun n => Nat.rec (firstSmoothJordanOuter houter)
    (fun n Omega => nextSmoothJordanOuter hK houter n Omega) n

/-- The closure of each successive outer approximation lies inside the previous domain. -/
theorem closure_nestedSmoothJordanOuterStage_succ_subset
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ) :
    closure (nestedSmoothJordanOuterStage hK houter (n + 1)).val.carrier ⊆
      (nestedSmoothJordanOuterStage hK houter n).val.carrier := by
  exact closure_nextSmoothJordanOuter_subset_carrier hK houter n
    (nestedSmoothJordanOuterStage hK houter n)

/-- Each outer approximation has closure inside its scheduled thickening. -/
theorem closure_nestedSmoothJordanOuterStage_subset_schedule
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ) :
    closure (nestedSmoothJordanOuterStage hK houter n).val.carrier ⊆
      convexThickeningApprox K n := by
  cases n with
  | zero => exact closure_firstSmoothJordanOuter_subset_schedule houter
  | succ n =>
      exact closure_nextSmoothJordanOuter_subset_schedule hK houter n
        (nestedSmoothJordanOuterStage hK houter n)

/-- Arbitrarily tight smooth Jordan outer approximations can be chosen
recursively to form a strict nested smooth Jordan exhaustion. -/
noncomputable def StrictNestedSmoothJordanExhaustion.ofOuterApproximation
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (houter : HasSmoothJordanOuterApproximation K) :
    StrictNestedSmoothJordanExhaustion K where
  domain n := (nestedSmoothJordanOuterStage hK houter n).val
  target_subset n := (nestedSmoothJordanOuterStage hK houter n).property
  isCompact_closure n := by
    apply (hK.cthickening (r := smoothApproxRadius n)).of_isClosed_subset
      isClosed_closure
    exact (closure_nestedSmoothJordanOuterStage_subset_schedule
      hK houter n).trans
        (Metric.thickening_subset_cthickening (smoothApproxRadius n) K)
  closure_succ_subset n := by
    exact closure_nestedSmoothJordanOuterStage_succ_subset hK houter n
  iInter_closure := by
    apply Set.Subset.antisymm
    · intro z hz
      have hthick : z ∈ ⋂ n, convexThickeningApprox K n := by
        rw [Set.mem_iInter]
        intro n
        exact closure_nestedSmoothJordanOuterStage_subset_schedule
          hK houter n (Set.mem_iInter.mp hz n)
      rw [(convexThickeningApprox_spec K hK hconvex).2] at hthick
      exact hthick
    · intro z hz
      rw [Set.mem_iInter]
      intro n
      exact subset_closure
        ((nestedSmoothJordanOuterStage hK houter n).property hz)

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Local smooth outer approximation of the closed numerical range is the
remaining geometric input for the exact Crouzeix--Palencia bound. -/
theorem crouzeix_palencia_of_smoothJordanOuterApproximation
    (A : E →L[ℂ] E)
    (houter : HasSmoothJordanOuterApproximation
      (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hcompact : IsCompact (closure (numericalRange A)) := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    exact hbounded.isCompact_closure
  exact crouzeix_palencia_of_strictNestedSmoothJordanExhaustion A
    (StrictNestedSmoothJordanExhaustion.ofOuterApproximation
      (closure (numericalRange A)) hcompact
        (convex_numericalRange A).closure houter)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
