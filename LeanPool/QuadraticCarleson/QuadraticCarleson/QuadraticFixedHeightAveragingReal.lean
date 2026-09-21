/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingRational

/-!
# Real-parameter fixed-height quadratic maximal L² decay

The supremum is over every nonzero real modulation. Its reduction to the
explicit rational sequence respects the half-open scale bands. The resulting
estimate has no analytic assumptions beyond membership of the input in L².
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- The full fixed-height maximal operator, with no discretization or
restriction on the nonzero real modulation parameter. -/
noncomputable def realFixedHeightQuadraticMaximal
    (height : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : {lam : ℝ // lam ≠ 0},
    ‖∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) * f t‖ₑ

/-- Exact pointwise reduction of the unrestricted real supremum to the
explicit enumeration of nonzero rational modulations. -/
theorem realFixedHeightQuadraticMaximal_eq_rational (height : ℕ)
    {f : ℝ → ℂ} (hf : LocallyIntegrable f) :
    realFixedHeightQuadraticMaximal height f = rationalFixedHeightQuadraticMaximal height f := by
  funext x
  apply le_antisymm
  · apply iSup_le
    intro lam
    exact fixedHeightQuadratic_integral_enorm_le_rational height lam.val lam.property hf x
  · apply iSup_le
    intro n
    exact le_iSup (fun lam : {lam : ℝ // lam ≠ 0} ↦
      ‖∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) * f t‖ₑ)
      ⟨rationalModulationSequence n, rationalModulationSequence_ne_zero n⟩

theorem measurable_realFixedHeightQuadraticMaximal (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    Measurable (realFixedHeightQuadraticMaximal height f) := by
  rw [realFixedHeightQuadraticMaximal_eq_rational height
    (hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  exact measurable_countableConvolutionMaximal_of_memLp _
    (fun n ↦ (continuous_fixedHeightQuadraticKernel _ _ _).measurable) hf

/-- The actual fixed-height quadratic maximal `L²` decay estimate over all
nonzero real modulations, including both signs and every natural height. All
kernel, oscillation, measurability and maximal-operator inputs are proved. -/
theorem realFixedHeightQuadraticMaximal_sq_lintegral_decay
    (height : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, realFixedHeightQuadraticMaximal height f x ^ 2) ≤
      ENNReal.ofReal (70996725888 * positiveDyadicAmplitudeBound ^ 2 /
        (2 : ℝ) ^ ((height - 1) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [realFixedHeightQuadraticMaximal_eq_rational height
    (hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  exact countable_fixedHeightQuadraticKernel_maximal_sq_decay_all_heights
    height rationalModulationSequence rationalModulationSequence_ne_zero hf

/-- Change of variables to the exact convolution convention used in the
paper: the dyadic kernel is evaluated at `t` and the input at `x - t`. -/
theorem fixedHeightQuadraticKernel_integral_eq_paper
    (height : ℕ) (lam : ℝ) (hlam : lam ≠ 0) (f : ℝ → ℂ) (x : ℝ) :
    (∫ t, fixedHeightQuadraticKernel lam height hlam (x - t) * f t) =
      ∫ t, f (x - t) * (dyadicPsi (oscillatoryScaleIndex lam height hlam) t : ℂ) *
        phase (lam * t ^ 2) := by
  calc
    _ = ∫ t, fixedHeightQuadraticKernel lam height hlam t * f (x - t) := by
      simpa only [sub_sub_cancel] using integral_sub_left_eq_self
        (fun t ↦ fixedHeightQuadraticKernel lam height hlam t * f (x - t)) volume x
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      unfold fixedHeightQuadraticKernel
      ring

/-- The paper's exact fixed-height quadratic maximal integral, with the
supremum over all nonzero real modulation parameters. -/
noncomputable def paperFixedHeightQuadraticMaximal
    (height : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : {lam : ℝ // lam ≠ 0},
    ‖∫ t, f (x - t) * (dyadicPsi (oscillatoryScaleIndex lam.val height lam.property) t : ℂ) *
      phase (lam.val * t ^ 2)‖ₑ

theorem paperFixedHeightQuadraticMaximal_eq_real (height : ℕ) (f : ℝ → ℂ) :
    paperFixedHeightQuadraticMaximal height f = realFixedHeightQuadraticMaximal height f := by
  funext x
  apply iSup_congr
  intro lam
  rw [fixedHeightQuadraticKernel_integral_eq_paper]

theorem measurable_paperFixedHeightQuadraticMaximal (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    Measurable (paperFixedHeightQuadraticMaximal height f) := by
  rw [paperFixedHeightQuadraticMaximal_eq_real]
  exact measurable_realFixedHeightQuadraticMaximal height hf

/-- Fixed-height quadratic maximal `L²` decay in the paper's exact integral
notation. The modulation supremum is unrestricted and both signs are included. -/
theorem paperFixedHeightQuadraticMaximal_sq_lintegral_decay
    (height : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, paperFixedHeightQuadraticMaximal height f x ^ 2) ≤
      ENNReal.ofReal (70996725888 * positiveDyadicAmplitudeBound ^ 2 /
        (2 : ℝ) ^ ((height - 1) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [paperFixedHeightQuadraticMaximal_eq_real]
  exact realFixedHeightQuadraticMaximal_sq_lintegral_decay height hf

end QuadraticCarleson
