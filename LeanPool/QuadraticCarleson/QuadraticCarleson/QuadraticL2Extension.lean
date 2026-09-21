/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticAveragingTTStar

/-!
# Extending finite-range integral estimates beyond test inputs

Spatial truncations eventually leave each kernel row unchanged. Fatou's lemma
therefore extends uniform second-moment bounds from integrable test functions
to locally integrable functions, in particular to all measurable `L²` inputs.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace QuadraticCarleson.FiniteRangeKernel

/-- A spatial truncation outside the finite range does not change the integral
action at the chosen point. No integrability assumption is necessary here. -/
theorem applyIntegral_indicator_Icc_eq (K : FiniteRangeKernel) (f : ℝ → ℂ)
    (x n : ℝ) (hn : |x| + K.radius ≤ n) :
    K.applyIntegral ((Icc (-n) n).indicator f) x = K.applyIntegral f x := by
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc (-n) n
  · simp [Set.indicator, ht]
  · have hdist : K.radius < |x - t| := by
      by_contra h
      have hxt := abs_le.mp (le_of_not_gt h)
      apply ht
      constructor <;> linarith [neg_abs_le x, le_abs_self x]
    rw [K.eq_zero x t hdist]
    simp

/-- A uniform second-moment bound on integrable measurable tests extends to
every measurable locally integrable input. -/
theorem sq_lintegral_bound_of_integrable (K : FiniteRangeKernel) (A : ℝ≥0∞)
    (hbound : ∀ g : ℝ → ℂ, Measurable g → Integrable g →
      (∫⁻ t, ‖K.applyIntegral g t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖g t‖ₑ ^ 2)
    {f : ℝ → ℂ} (hfm : Measurable f) (hfloc : LocallyIntegrable f) :
    (∫⁻ t, ‖K.applyIntegral f t‖ₑ ^ 2) ≤ A * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  let fN : ℕ → ℝ → ℂ := fun n ↦ (Icc (-(n : ℝ)) (n : ℝ)).indicator f
  have hm (n : ℕ) : Measurable (fN n) := hfm.indicator measurableSet_Icc
  have hi (n : ℕ) : Integrable (fN n) :=
    (hfloc.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc
  have henergy (n : ℕ) : (∫⁻ t, ‖K.applyIntegral (fN n) t‖ₑ ^ 2) ≤
      A * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
    apply (hbound (fN n) (hm n) (hi n)).trans
    apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro t
    by_cases ht : t ∈ Icc (-(n : ℝ)) (n : ℝ)
    · simp [fN, ht]
    · simp [fN, ht]
  have hevent (t : ℝ) :
      (fun n : ℕ ↦ ‖K.applyIntegral (fN n) t‖ₑ ^ 2) =ᶠ[atTop]
        (fun _ ↦ ‖K.applyIntegral f t‖ₑ ^ 2) := by
    obtain ⟨n, hn⟩ := exists_nat_ge (|t| + K.radius)
    filter_upwards [eventually_ge_atTop n] with m hm
    have htm : |t| + K.radius ≤ (m : ℝ) := hn.trans (by exact_mod_cast hm)
    rw [show K.applyIntegral (fN m) t = K.applyIntegral f t from
      K.applyIntegral_indicator_Icc_eq f t m htm]
  have hlim (t : ℝ) :
      liminf (fun n : ℕ ↦ ‖K.applyIntegral (fN n) t‖ₑ ^ 2) atTop =
        ‖K.applyIntegral f t‖ₑ ^ 2 := by
    rw [liminf_congr (hevent t), liminf_const]
  have hfatou := lintegral_liminf_le
    (μ := (volume : Measure ℝ)) (u := (atTop : Filter ℕ))
    (fun n ↦ (K.measurable_applyIntegral (hm n)).enorm.pow_const 2)
  simp only [hlim] at hfatou
  exact hfatou.trans (liminf_le_of_frequently_le'
    (Filter.Eventually.of_forall henergy).frequently)

/-- The symmetric averaging majorant gives the adjoint estimate on all
measurable `L²` functions, with no `L¹` restriction. -/
theorem adjoint_sq_lintegral_le_of_selectedAverageKernel_memLp {N : ℕ}
    (K : FiniteRangeKernel) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    {σ : ℝ → Fin N} (hσ : Measurable σ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ x y, ‖K.correlation x y‖ₑ ≤ C *
      (QuadraticCarleson.selectedAverageKernel r σ x y +
        QuadraticCarleson.selectedAverageKernel r σ y x))
    {g : ℝ → ℂ} (hgm : Measurable g) (hg : MemLp g 2) :
    (∫⁻ t, ‖K.adjoint.applyIntegral g t‖ₑ ^ 2) ≤
      (66 * C) * ∫⁻ t, ‖g t‖ₑ ^ 2 := by
  apply K.adjoint.sq_lintegral_bound_of_integrable (66 * C) ?_ hgm
    (hg.locallyIntegrable (by norm_num))
  intro f hfm hfi
  exact K.adjoint_sq_lintegral_le_of_selectedAverageKernel r hr hσ C hC hbound hfm hfi

end QuadraticCarleson.FiniteRangeKernel
