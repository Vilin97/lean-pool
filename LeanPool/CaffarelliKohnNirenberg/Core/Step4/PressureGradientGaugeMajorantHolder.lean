/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# A power-mean estimate for time majorants

An extended-real estimate used when a slice majorant is integrated in time over
the backward window of a parabolic cell: a power-mean bound that trades a
sub-unit power for the total mass.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section
namespace CKN.Core.Step4

/-- Jensen/Hoelder on a finite measure space: a sub-unit power of an integral
dominates the integral of the power, at the cost of the total mass. -/
theorem lintegral_rpow_le_rpow_lintegral_mul_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {J : α → ℝ≥0∞} (hJ : AEMeasurable J μ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫⁻ s, J s ^ θ ∂μ) ≤ (∫⁻ s, J s ∂μ) ^ θ * (μ Set.univ) ^ (1 - θ) := by
  have hθne : θ ≠ 0 := hθ0.ne'
  have h1θne : (1 - θ) ≠ 0 := (sub_pos.mpr hθ1).ne'
  have hab : (1 / θ).HolderConjugate (1 / (1 - θ)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact one_lt_one_div hθ0 hθ1
    · field_simp [hθne, h1θne]
      ring
  have hpow : ∀ s, (J s ^ θ) ^ (1 / θ) = J s := by
    intro s
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hθne, ENNReal.rpow_one]
  have hleft : (∫⁻ s, (J s ^ θ) ^ (1 / θ) ∂μ) = ∫⁻ s, J s ∂μ := by
    apply lintegral_congr
    exact hpow
  have huniv : (∫⁻ _s : α, (1 : ℝ≥0∞) ^ (1 / (1 - θ)) ∂μ) = μ Set.univ := by
    simp
  have haexp : 1 / (1 / θ) = θ := by
    rw [one_div_div, div_one]
  have hbexp : 1 / (1 / (1 - θ)) = 1 - θ := by
    rw [one_div_div, div_one]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hab (hJ.pow_const θ)
    (aemeasurable_const : AEMeasurable (fun _ : α => (1 : ℝ≥0∞)) μ)
  rw [hleft, huniv, haexp, hbexp] at h
  simpa only [Pi.mul_apply, mul_one] using h

end CKN.Core.Step4
