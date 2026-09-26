/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

/-!
# Temporal Hölder estimates for the pressure source

The products in the slice estimate `eq:pressure-gradient-morrey` are integrated
at exponent `6/5`. Velocity cubes and gradient squares enter with powers
`2/5` and `3/5`; quadratic velocity and tensor-energy terms use the remaining
`1/5` power of the time-window measure.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- Temporal Hölder for the velocity-gradient product in the source. -/
theorem origin_time_velocity_gradient_product_bound
    {μ : Measure ℝ} {U D : ℝ → ℝ≥0∞}
    (hU : AEMeasurable U μ) (hD : AEMeasurable D μ) :
    (∫⁻ s, (U s * D s) ^ (6 / 5 : ℝ) ∂μ) ≤
      (∫⁻ s, U s ^ (3 : ℝ) ∂μ) ^ (2 / 5 : ℝ) *
        (∫⁻ s, D s ^ (2 : ℝ) ∂μ) ^ (3 / 5 : ℝ) := by
  have hconj : (5 / 2 : ℝ).HolderConjugate (5 / 3 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (hU.pow_const (6 / 5 : ℝ)) (hD.pow_const (6 / 5 : ℝ))
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at h
  norm_num at h
  simpa only [ENNReal.rpow_ofNat, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5)]
    using h

/-- Temporal Hölder for the four-fifths power of the tensor energy. -/
theorem origin_time_energy_four_fifths_bound
    {μ : Measure ℝ} {E : ℝ → ℝ≥0∞} (hE : AEMeasurable E μ) :
    (∫⁻ s, E s ^ (4 / 5 : ℝ) ∂μ) ≤
      (∫⁻ s, E s ∂μ) ^ (4 / 5 : ℝ) * μ univ ^ (1 / 5 : ℝ) := by
  have hconj : (5 / 4 : ℝ).HolderConjugate 5 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (hE.pow_const (4 / 5 : ℝ)) (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) μ)
  simpa only [Pi.mul_apply, mul_one, ← ENNReal.rpow_mul,
    show (4 / 5 : ℝ) * (5 / 4) = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.one_rpow, lintegral_const, one_mul,
    show (1 : ℝ) / (5 / 4) = 4 / 5 by norm_num] using h

/-- The cutoff's quadratic velocity term is controlled by the velocity
cube integral and the one-fifth power of the time-window measure. -/
theorem origin_time_velocity_square_bound
    {μ : Measure ℝ} {U : ℝ → ℝ≥0∞} (hU : AEMeasurable U μ) :
    (∫⁻ s, (U s * U s) ^ (6 / 5 : ℝ) ∂μ) ≤
      (∫⁻ s, U s ^ (3 : ℝ) ∂μ) ^ (4 / 5 : ℝ) * μ univ ^ (1 / 5 : ℝ) := by
  have h := origin_time_energy_four_fifths_bound (hU.pow_const (3 : ℝ))
  have heq : ∀ s, (U s * U s) ^ (6 / 5 : ℝ) = (U s ^ (3 : ℝ)) ^ (4 / 5 : ℝ) := by
    intro s
    rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 1
    norm_num
  simpa only [heq] using h

/-- A two-term centered-source majorant integrates using only the velocity
cube, gradient square, and the measure of the time window. -/
theorem origin_time_two_product_majorant_bound
    {μ : Measure ℝ} {U D N : ℝ → ℝ≥0∞} (c d : ℝ≥0∞)
    (hU : AEMeasurable U μ) (hD : AEMeasurable D μ)
    (hN : ∀ᵐ s ∂μ, N s ≤ c * (D s * U s + d * (U s * U s))) :
    (∫⁻ s, N s ^ (6 / 5 : ℝ) ∂μ) ≤
      c ^ (6 / 5 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 5 : ℝ) *
        ((∫⁻ s, U s ^ (3 : ℝ) ∂μ) ^ (2 / 5 : ℝ) *
            (∫⁻ s, D s ^ (2 : ℝ) ∂μ) ^ (3 / 5 : ℝ) +
          d ^ (6 / 5 : ℝ) *
            ((∫⁻ s, U s ^ (3 : ℝ) ∂μ) ^ (4 / 5 : ℝ) * μ univ ^ (1 / 5 : ℝ))) := by
  have hpoint : ∀ᵐ s ∂μ, N s ^ (6 / 5 : ℝ) ≤
      (c ^ (6 / 5 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 5 : ℝ)) *
        ((D s * U s) ^ (6 / 5 : ℝ) + d ^ (6 / 5 : ℝ) * (U s * U s) ^ (6 / 5 : ℝ)) := by
    filter_upwards [hN] with s hs
    have h := ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 6 / 5)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5)] at h
    have ha := ENNReal.rpow_add_le_mul_rpow_add_rpow (D s * U s) (d * (U s * U s))
      (by norm_num : (1 : ℝ) ≤ 6 / 5)
    have hh := h.trans (mul_le_mul' le_rfl ha)
    simpa only [show (6 / 5 : ℝ) - 1 = 1 / 5 by norm_num,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5), mul_assoc] using hh
  have h1 := (hD.mul hU).pow_const (6 / 5 : ℝ)
  have h2 := (hU.mul hU).pow_const (6 / 5 : ℝ)
  change AEMeasurable (fun s => (D s * U s) ^ (6 / 5 : ℝ)) μ at h1
  change AEMeasurable (fun s => (U s * U s) ^ (6 / 5 : ℝ)) μ at h2
  have hsum : AEMeasurable (fun s => (D s * U s) ^ (6 / 5 : ℝ) +
      d ^ (6 / 5 : ℝ) * (U s * U s) ^ (6 / 5 : ℝ)) μ :=
    h1.add (aemeasurable_const.mul h2)
  refine (lintegral_mono_ae hpoint).trans ?_
  rw [lintegral_const_mul'' _ hsum,
    lintegral_add_left' h1, lintegral_const_mul'' _ h2]
  apply mul_le_mul' le_rfl
  apply add_le_add
  · simpa only [mul_comm] using origin_time_velocity_gradient_product_bound hU hD
  · exact mul_le_mul' le_rfl (origin_time_velocity_square_bound hU)

end CKN.Core.Step4
