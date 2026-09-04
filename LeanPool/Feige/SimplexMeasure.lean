/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Constants
import LeanPool.Feige.SimplexGeometry
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Uniform measure and halfspace statistic on the simplex

This file equips the full-dimensional simplex with normalized Lebesgue
measure.  It also isolates the `α = 0` centroid-halfspace statement used in
the `δ = 1` specialization of §2.2.  Everything after that geometric input,
including the strict-boundary/complement step, is proved here.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Feige

variable {ι : Type*} [Fintype ι]

/-- Lebesgue measure restricted to the full-dimensional simplex. -/
noncomputable def simplexRestrictedVolume (ι : Type*) [Fintype ι] :
    Measure (ι → ℝ) :=
  volume.restrict (fullSimplex ι)

/-- Uniform probability measure on the full-dimensional standard simplex. -/
noncomputable def simplexUniformMeasure (ι : Type*) [Fintype ι] :
    Measure (ι → ℝ) :=
  (volume (fullSimplex ι))⁻¹ • simplexRestrictedVolume ι

noncomputable instance simplexUniformMeasure.isProbabilityMeasure :
    IsProbabilityMeasure (simplexUniformMeasure ι) := by
  refine ⟨?_⟩
  simp only [simplexUniformMeasure, Measure.coe_smul, Pi.smul_apply,
    smul_eq_mul, simplexRestrictedVolume, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (volume_fullSimplex_pos (ι := ι)))
    (ne_of_lt (volume_fullSimplex_lt_top (ι := ι)))

theorem simplexUniformMeasure_apply {s : Set (ι → ℝ)} (hs : MeasurableSet s) :
    simplexUniformMeasure ι s =
      (volume (fullSimplex ι))⁻¹ * volume (s ∩ fullSimplex ι) := by
  simp only [simplexUniformMeasure, Measure.coe_smul, Pi.smul_apply,
    smul_eq_mul, simplexRestrictedVolume, Measure.restrict_apply hs]

/-- The simplex form of the Dirichlet statistic `Kₙ` in (2.1). -/
noncomputable def simplexK (y : ι → ℝ) : ℝ :=
  (simplexUniformMeasure ι).real {x | simplexLinearForm y x ≤ 1}

theorem measurableSet_simplexK_event (y : ι → ℝ) :
    MeasurableSet {x : ι → ℝ | simplexLinearForm y x ≤ 1} := by
  apply measurableSet_le
  · exact Finset.measurable_fun_sum Finset.univ fun i _ ↦
      measurable_const.mul (measurable_pi_apply i)
  · exact measurable_const

theorem simplexK_nonneg (y : ι → ℝ) : 0 ≤ simplexK y :=
  measureReal_nonneg

theorem simplexK_le_one (y : ι → ℝ) : simplexK y ≤ 1 := by
  calc
    simplexK y ≤ (simplexUniformMeasure ι).real univ :=
      measureReal_mono (subset_univ _)
    _ = 1 := probReal_univ

/-- The precise `α = 0` simplex centroid-halfspace conclusion used by the
`δ = 1` geometric estimate in §2.2. -/
def SimplexCentroidHalfspaceProperty : Prop :=
  ∀ y : ι → ℝ,
    (∀ i, 0 ≤ y i) →
    (Fintype.card ι : ℝ) + 1 ≤ ∑ i, y i →
    sharpConstant (Fintype.card ι) ≤
      (simplexUniformMeasure ι).real {x | 1 < simplexLinearForm y x}

/-- The strict upper halfspace and the closed sublevel event are complements. -/
theorem simplex_upper_compl (y : ι → ℝ) :
    {x : ι → ℝ | 1 < simplexLinearForm y x}ᶜ =
      {x | simplexLinearForm y x ≤ 1} := by
  ext x
  simp

/-- Specialized Grünbaum immediately gives the deterministic large-sum
bridge for the simplex statistic. -/
theorem simplex_largeSumBridge
    (hcentroid : SimplexCentroidHalfspaceProperty (ι := ι)) :
    ∀ y : ι → ℝ,
      (∀ i, 0 ≤ y i) →
      (Fintype.card ι : ℝ) + 1 ≤ ∑ i, y i →
      simplexK y ≤ 1 - sharpConstant (Fintype.card ι) := by
  intro y hy hsum
  have hu_meas : MeasurableSet {x : ι → ℝ | 1 < simplexLinearForm y x} := by
    apply measurableSet_lt
    · exact measurable_const
    · exact Finset.measurable_fun_sum Finset.univ fun i _ ↦
        measurable_const.mul (measurable_pi_apply i)
  have hgeom := hcentroid y hy hsum
  have hcomp :
      (simplexUniformMeasure ι).real
          {x | simplexLinearForm y x ≤ 1} =
        1 - (simplexUniformMeasure ι).real
          {x | 1 < simplexLinearForm y x} := by
    rw [← simplex_upper_compl]
    exact probReal_compl_eq_one_sub hu_meas
  rw [simplexK, hcomp]
  linarith

end Feige
