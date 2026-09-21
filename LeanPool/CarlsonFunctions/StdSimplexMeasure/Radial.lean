/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Integral
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Radial integration over the positive orthant

The radial coordinate is the sum of the coordinates. Its angular measure is the
coordinate-normalized standard-simplex measure, so the radial factor is `t^(card ι - 1)`.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Classical

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- Scaling free coordinates in a slice of fixed coordinate sum scales its simplex chart. -/
theorem radial_slice_smul (i : ι) (t : ℝ) (v : {j : ι // j ≠ i} → ℝ) :
    (Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, t * v j, t • v) =
      t • stdSimplexCoordMap i v := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [stdSimplexCoordMap, ← Finset.mul_sum, mul_sub]
  · simp [stdSimplexCoordMap, hj]

/-- Lebesgue integration with the sum of the coordinates as the first coordinate. -/
theorem lintegral_eq_lintegral_sum_slice (i : ι) (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ t : ℝ, ∫⁻ v : {j : ι // j ≠ i} → ℝ,
      f ((Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, v j, v)) := by
  let e := Homeomorph.funSplitAt ℝ i
  have hf' : Measurable (fun p => f (e.symm p)) := hf.comp e.symm.measurable
  have H : (∫⁻ x, f x) = ∫⁻ p, f (e.symm p) ∂(volume.prod volume) := by
    simpa only [e, Homeomorph.symm_apply_apply] using
      (volume_preserving_funSplitAt i).lintegral_comp hf'
  rw [H]
  rw [lintegral_prod_symm _ hf'.aemeasurable]
  have ht (v : {j : ι // j ≠ i} → ℝ) :=
    lintegral_sub_right_eq_self (μ := volume) (fun t : ℝ => f (e.symm (t, v))) (∑ j, v j)
  simp_rw [← ht]
  exact lintegral_lintegral_swap (by fun_prop)

/-- The affine slice with total `t` has coordinate sum `t`. -/
theorem sum_radial_slice (i : ι) (t : ℝ) (v : {j : ι // j ≠ i} → ℝ) :
    ∑ j, (Homeomorph.funSplitAt ℝ i).symm (t - ∑ k, v k, v) j = t := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
  have hsum : (∑ j : {j : ι // j ≠ i},
      (Homeomorph.funSplitAt ℝ i).symm (t - ∑ k, v k, v) j) = ∑ j, v j :=
    Finset.sum_congr rfl (fun j _ => by simp [j.property])
  rw [hsum]
  simp

/-- Nonnegative points on the slice of total `t` are parametrized by the positive simplex
of radius `t` in the free coordinates. -/
theorem nonneg_radial_slice_iff (i : ι) (t : ℝ) (v : {j : ι // j ≠ i} → ℝ) :
    (∀ j, 0 ≤ (Homeomorph.funSplitAt ℝ i).symm (t - ∑ k, v k, v) j) ↔
      v ∈ posSimplex {j : ι // j ≠ i} t := by
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · simpa [j.property] using h j
    · have H := h i
      simpa using H
  · rintro ⟨hv, hs⟩ j
    by_cases hj : j = i
    · subst j
      simpa using sub_nonneg.mpr hs
    · simpa [hj] using hv ⟨j, hj⟩

/-- Radial integration for a measurable nonnegative function supported on the positive
orthant. The simplex measure is the coordinate-normalized one, with no Euclidean area factor. -/
theorem lintegral_eq_radial_stdSimplex [Nonempty ι]
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hsupp : ∀ x, ¬ (∀ i, 0 ≤ x i) → f x = 0) :
    ∫⁻ x, f x = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (Fintype.card ι - 1)) *
      ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, f (t • u) ∂stdSimplexMeasure := by
  let i : ι := Classical.choice inferInstance
  rw [lintegral_eq_lintegral_sum_slice i f hf, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht0
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have hs : (∫⁻ v : {j : ι // j ≠ i} → ℝ,
        f ((Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, v j, v))) =
        ∫⁻ v in posSimplex {j : ι // j ≠ i} t,
          f ((Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, v j, v)) := by
      rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
      apply lintegral_congr
      intro v
      by_cases hv : v ∈ posSimplex {j : ι // j ≠ i} t
      · rw [Set.indicator_of_mem hv]
      · rw [Set.indicator_of_notMem hv]
        exact hsupp _ (fun h => hv ((nonneg_radial_slice_iff i t v).mp h))
    rw [hs, lintegral_posSimplex_scale i t ht,
      lintegral_stdSimplex_eq_lintegral_freeCoords i]
    congr 1
    apply lintegral_congr
    intro v
    simp only [Pi.smul_apply, smul_eq_mul, radial_slice_smul]
  · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro v
    apply hsupp
    intro hv
    have H := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hv j)
    rw [sum_radial_slice] at H
    exact ht0 (le_antisymm (le_of_not_gt ht) H)

end MeasureTheory

end
