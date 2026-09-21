/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0OperatorMeasure

/-!
# Total mass of pointwise Riesz measures

A positive contraction on real continuous functions vanishing at infinity induces pointwise
Riesz measures of total mass at most one.  The proof first bounds compact sets using compactly
supported Urysohn cutoff functions, then passes to the whole space by inner regularity.

This file proves only a pointwise total-mass bound and finiteness.  It does not construct a kernel
or prove any regularity in the evaluation point.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0OperatorMeasure

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)

/-- The Riesz measure of a positive contraction assigns mass at most one to every compact set. -/
theorem measure_compact_le_one (hT_norm : ‖T‖ ≤ 1) (x : α) {K : Set α} (hK : IsCompact K) :
    measure T hT x K ≤ 1 := by
  obtain ⟨f, hfK, hfcompact, _hf_support, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (Set.subset_univ K)
  let g : C_c(α, ℝ) := ⟨f, hasCompactSupport_def.mpr hfcompact⟩
  have hg_nonneg (y : α) : 0 ≤ g y := (hf y).1
  have hg_le_one (y : α) : g y ≤ 1 := (hf y).2
  have hg_norm : ‖compactlySupportedToC0LinearMap g‖ ≤ 1 := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le zero_le_one).2 fun y ↦ ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(neg_nonpos.mpr zero_le_one).trans (hg_nonneg y), hg_le_one y⟩
  have hfunctional_le_one : functional T hT x g ≤ 1 := by
    calc
      functional T hT x g = T (compactlySupportedToC0LinearMap g) x := rfl
      _ ≤ |T (compactlySupportedToC0LinearMap g) x| := le_abs_self _
      _ ≤ ‖T (compactlySupportedToC0LinearMap g)‖ := by
        exact (T (compactlySupportedToC0LinearMap g)).toBCF.norm_coe_le_norm x
      _ ≤ 1 := by
        simpa only [one_mul] using
          T.le_of_opNorm_le_of_le hT_norm hg_norm
  calc
    measure T hT x K ≤ ENNReal.ofReal (functional T hT x g) := by
      apply RealRMK.rieszMeasure_le_of_eq_one (functional T hT x) hg_nonneg hK
      intro y hy
      exact hfK hy
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr hfunctional_le_one

/-- The Riesz measure of a positive contraction has total mass at most one. -/
theorem measure_univ_le_one (hT_norm : ‖T‖ ≤ 1) (x : α) :
    measure T hT x Set.univ ≤ 1 := by
  let := regular_measure T hT x
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  refine iSup_le fun K ↦ iSup_le fun _hK_univ ↦ iSup_le fun hK ↦ ?_
  exact measure_compact_le_one T hT hT_norm x hK

/-- The pointwise Riesz measure of a positive contraction is finite. -/
theorem isFiniteMeasure_measure (hT_norm : ‖T‖ ≤ 1) (x : α) :
    IsFiniteMeasure (measure T hT x) :=
  ⟨(measure_univ_le_one T hT hT_norm x).trans_lt ENNReal.one_lt_top⟩

end MarkovProcess.PositiveC0OperatorMeasure
