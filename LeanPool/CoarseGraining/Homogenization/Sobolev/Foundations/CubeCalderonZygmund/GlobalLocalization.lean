/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeightedTailRestrict

/-! # Global Localization -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-!
# Localization for the global good-`λ` extension

The global good-`λ` argument extends the reflected parent-cube gradient and
datum by zero.  This file records exactly the identities which let that
global extension be used on a ball lying in the original parent cube.  In
particular, no assertion identifies the extension with the original function
away from its support.
-/

/-- On every set contained in `U`, the zero extension `U.indicator f` agrees
pointwise (and hence almost everywhere) with `f`. -/
theorem indicator_aeEq_of_subset {α E : Type*} [MeasurableSpace α]
    [Zero E] {μ : Measure α} {U B : Set α} {f : α → E}
    (hB : MeasurableSet B) (hBU : B ⊆ U) :
    U.indicator f =ᵐ[μ.restrict B] f := by
  filter_upwards [ae_restrict_mem hB] with x hx
  exact Set.indicator_of_mem (hBU hx) f

/-- Measurability of a zero extension is precisely measurability of the
underlying function on its support. -/
theorem aestronglyMeasurable_indicator_iff_restrict {α E : Type*}
    [MeasurableSpace α] [TopologicalSpace E] [Zero E]
    {μ : Measure α} {U : Set α} {f : α → E}
    (hU : MeasurableSet U) :
    AEStronglyMeasurable (U.indicator f) μ ↔
      AEStronglyMeasurable f (μ.restrict U) :=
  aestronglyMeasurable_indicator_iff hU

/-- The global `Lᵖ` membership of a zero extension is exactly its local
membership on the support. -/
theorem memLp_indicator_iff_restrict {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {U : Set α} {f : α → E}
    {p : ℝ≥0∞} (hU : MeasurableSet U) :
    MemLp (U.indicator f) p μ ↔ MemLp f p (μ.restrict U) :=
  MeasureTheory.memLp_indicator_iff_restrict hU

/-- Integrating a zero extension over the ambient space is integration of the
original function over its measurable support. -/
theorem integral_indicator_eq_integral_restrict {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {U : Set α} {f : α → E} (hU : MeasurableSet U) :
    ∫ x, U.indicator f x ∂μ = ∫ x in U, f x ∂μ :=
  MeasureTheory.integral_indicator hU

/-- The analogous identity for nonnegative extended-valued integrands. -/
theorem lintegral_indicator_eq_lintegral_restrict {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {U : Set α} {f : α → ℝ≥0∞} (hU : MeasurableSet U) :
    ∫⁻ x, U.indicator f x ∂μ = ∫⁻ x in U, f x ∂μ :=
  MeasureTheory.lintegral_indicator hU f

/-- Squared weighted measure commutes exactly with extension by zero: its
base measure is simply restricted to the support. -/
theorem sqWeightedMeasure_indicator_eq_restrict {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {U : Set α} {f : α → E}
    (hU : MeasurableSet U) :
    sqWeightedMeasure (U.indicator f) μ = sqWeightedMeasure f (μ.restrict U) := by
  change μ.withDensity (fun x => ENNReal.ofReal (‖U.indicator f x‖ ^ (2 : ℕ))) =
    (μ.restrict U).withDensity (fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)))
  rw [show (fun x => ENNReal.ofReal (‖U.indicator f x‖ ^ (2 : ℕ))) =
      U.indicator (fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) by
        funext x
        by_cases hx : x ∈ U
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]]
  exact MeasureTheory.withDensity_indicator hU _

/-- On a measurable set inside `U`, squared weighted mass is unchanged by
extension by zero.  The test set need not itself be measurable. -/
theorem sqWeightedMeasure_indicator_restrict_eq_of_subset {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {U B : Set α} {f : α → E} (hU : MeasurableSet U) (hB : MeasurableSet B)
    (hBU : B ⊆ U) :
    (sqWeightedMeasure (U.indicator f) μ).restrict B =
      (sqWeightedMeasure f μ).restrict B := by
  rw [sqWeightedMeasure_indicator_eq_restrict hU]
  change ((μ.restrict U).withDensity fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))).restrict B =
    (μ.withDensity fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))).restrict B
  rw [← MeasureTheory.restrict_withDensity hU]
  ext s hs
  rw [Measure.restrict_apply' hB, Measure.restrict_apply' hB,
    Measure.restrict_apply' hU]
  rw [Set.inter_eq_left.mpr (Set.inter_subset_right.trans hBU)]

/-- A positive-level tail of a zero extension is the corresponding tail
inside its support. -/
theorem indicator_tail_set_eq_inter {α E : Type*} [NormedAddCommGroup E]
    {U : Set α} {f : α → E} {a : ℝ} (ha : 0 < a) :
    {x | a < ‖U.indicator f x‖} = U ∩ {x | a < ‖f x‖} := by
  ext x
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, not_lt_of_ge ha.le]

/-- Inside a set contained in `U`, level tails and their squared weighted
mass are exactly those of the unextended function. -/
theorem sqWeightedMeasure_indicator_tail_inter_eq_of_subset {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {U B : Set α} {f : α → E} {a : ℝ} (hU : MeasurableSet U)
    (hB : MeasurableSet B) (hBU : B ⊆ U) :
    sqWeightedMeasure (U.indicator f) μ ({x | a < ‖U.indicator f x‖} ∩ B) =
      sqWeightedMeasure f μ ({x | a < ‖f x‖} ∩ B) := by
  have htail : {x | a < ‖U.indicator f x‖} ∩ B =
      {x | a < ‖f x‖} ∩ B := by
    ext x
    by_cases hx : x ∈ B
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hx, and_true]
      rw [Set.indicator_of_mem (hBU hx)]
    · simp only [Set.mem_inter_iff, hx, and_false]
  rw [htail]
  have hrestrict := sqWeightedMeasure_indicator_restrict_eq_of_subset
    (μ := μ) (f := f) hU hB hBU
  have happly := congrArg (fun ν : Measure α => ν ({x | a < ‖f x‖} ∩ B)) hrestrict
  change (sqWeightedMeasure (U.indicator f) μ).restrict B ({x | a < ‖f x‖} ∩ B) =
    (sqWeightedMeasure f μ).restrict B ({x | a < ‖f x‖} ∩ B) at happly
  rw [Measure.restrict_apply' hB, Measure.restrict_apply' hB] at happly
  simpa only [Set.inter_assoc, Set.inter_self] using happly

end CubeCalderonZygmund

end

end Homogenization
