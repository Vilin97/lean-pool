/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Abstract real inequalities for the stream-difference estimate

A Cauchy–Schwarz inequality for integrals from a pointwise nonnegative quadratic form, and the
final real-number step turning the energy balance into the `η/κ` bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.Infra.Section5.RelativeError

/-- Cauchy–Schwarz from a pointwise nonnegative quadratic form. -/
theorem sq_integral_le_of_quadratic_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q r : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ) (hr : Integrable r μ)
    (h : ∀ᵐ x ∂μ, ∀ l : ℝ, 0 ≤ l ^ 2 * p x + 2 * l * q x + r x) :
    (∫ x, q x ∂μ) ^ 2 ≤ (∫ x, p x ∂μ) * ∫ x, r x ∂μ := by
  have hl : ∀ l : ℝ, 0 ≤ (∫ x, p x ∂μ) * l * l + 2 * (∫ x, q x ∂μ) * l + ∫ x, r x ∂μ := by
    intro l
    have h0 : 0 ≤ ∫ x, (l ^ 2 * p x + 2 * l * q x + r x) ∂μ :=
      integral_nonneg_of_ae (by filter_upwards [h] with x hx using hx l)
    have hsplit : ∫ x, (l ^ 2 * p x + 2 * l * q x + r x) ∂μ =
        l ^ 2 * ∫ x, p x ∂μ + 2 * l * ∫ x, q x ∂μ + ∫ x, r x ∂μ := by
      have h1 : Integrable (fun x => l ^ 2 * p x) μ := hp.const_mul _
      have h2 : Integrable (fun x => 2 * l * q x) μ := hq.const_mul _
      have h12 : Integrable (fun x => l ^ 2 * p x + 2 * l * q x) μ := h1.add h2
      rw [integral_add h12 hr, integral_add h1 h2, integral_const_mul,
        integral_const_mul]
    rw [hsplit] at h0
    nlinarith [h0]
  have hl' : ∀ l : ℝ, 0 ≤ (∫ x, p x ∂μ) * (l * l) + (2 * ∫ x, q x ∂μ) * l + ∫ x, r x ∂μ := by
    intro l
    have := hl l
    rw [← mul_assoc]
    exact this
  have := discrim_le_zero hl'
  unfold discrim at this
  nlinarith [this]

/-- The final real step: from the energy balance `l + 2κA = -2C`, the Cauchy–Schwarz bound
`C² ≤ E A` and `E ≤ η² B`, conclude `√κ √A ≤ (η/κ) (√κ √B)`. -/
theorem stream_final_real {κ η A B C E l : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hl : 0 ≤ l) (hid : l + 2 * κ * A = -2 * C) (hCE : C ^ 2 ≤ E * A)
    (hE : E ≤ η ^ 2 * B) :
    Real.sqrt κ * Real.sqrt A ≤ (η / κ) * (Real.sqrt κ * Real.sqrt B) := by
  have hrhs : 0 ≤ (η / κ) * (Real.sqrt κ * Real.sqrt B) := by positivity
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, mul_zero]
    exact hrhs
  · have h1 : κ * A ≤ -C := by linarith
    have h2 : (κ * A) ^ 2 ≤ C ^ 2 := by
      have : 0 ≤ κ * A := by positivity
      nlinarith
    have h3 : (κ * A) ^ 2 ≤ η ^ 2 * B * A := by
      calc (κ * A) ^ 2 ≤ C ^ 2 := h2
        _ ≤ E * A := hCE
        _ ≤ η ^ 2 * B * A := mul_le_mul_of_nonneg_right hE hA
    have h4 : κ ^ 2 * A ≤ η ^ 2 * B := by
      have : A * (κ ^ 2 * A) ≤ A * (η ^ 2 * B) := by nlinarith [h3]
      exact le_of_mul_le_mul_left this hpos
    have h5 : A ≤ (η / κ) ^ 2 * B := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [h4]
    have h6 : Real.sqrt A ≤ (η / κ) * Real.sqrt B := by
      calc Real.sqrt A ≤ Real.sqrt ((η / κ) ^ 2 * B) := Real.sqrt_le_sqrt h5
        _ = (η / κ) * Real.sqrt B := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc Real.sqrt κ * Real.sqrt A ≤ Real.sqrt κ * ((η / κ) * Real.sqrt B) :=
          mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg _)
      _ = (η / κ) * (Real.sqrt κ * Real.sqrt B) := by ring

end AVenhance.Infra.Section5.RelativeError

end
