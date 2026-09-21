/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.OffSupportOscillatory

/-!
# Uniform constants for arbitrary-order off-support integration by parts

The recursion separates the original packet derivative seminorms from the
modulation, interval length, and distance. It is used without changing any
hypothesis of the paper's off-support lemma.
-/

open MeasureTheory

namespace QuadraticCarleson


noncomputable def offSupportDerivativeMass (r : ℕ) : ℝ :=
  ∫ u : ℝ, |iteratedDeriv r baseBump u|

theorem offSupportDerivativeMass_nonneg (r : ℕ) : 0 ≤ offSupportDerivativeMass r :=
  integral_nonneg fun _ ↦ abs_nonneg _

noncomputable def offSupportDecayConstant : ℕ → ℕ → ℕ → ℝ
  | 0, r, q => 3 ^ q * offSupportDerivativeMass r
  | k + 1, r, q =>
      (offSupportDecayConstant k (r + 1) (q + 1) +
        2 * (q + 1 : ℝ) * offSupportDecayConstant k r (q + 2)) / (4 * Real.pi)

theorem offSupportDecayConstant_nonneg (k r q : ℕ) : 0 ≤ offSupportDecayConstant k r q := by
  induction k generalizing r q with
  | zero => exact mul_nonneg (by positivity) (offSupportDerivativeMass_nonneg r)
  | succ k ih =>
      exact div_nonneg
        (add_nonneg (ih (r + 1) (q + 1)) (mul_nonneg (by positivity) (ih r (q + 2))))
        (by positivity)

/-- The only scale trade in the induction is the geometric inequality `t ≤ 2a`. -/
theorem offSupport_step_fraction_le
    {A B z l mu t a : ℝ} (hB : 0 ≤ B) (hz : 0 ≤ z)
    (hl : 0 < l) (hmu : 0 < mu) (ht : 0 < t) (ha : 0 < a) (hta : t ≤ 2 * a) :
    (A / (l * t * a) + z * (B / (l * a ^ 2))) / (4 * Real.pi * mu) ≤
      ((A + 2 * z * B) / (4 * Real.pi)) / (mu * l * t * a) := by
  have hterm : z * (B / (l * a ^ 2)) ≤ (2 * z * B) / (l * t * a) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < l * a ^ 2)
      (by positivity : 0 < l * t * a)).2
    have h := mul_le_mul_of_nonneg_left hta
      (show 0 ≤ z * B * l * a by positivity)
    nlinarith
  calc
    _ ≤ (A / (l * t * a) + (2 * z * B) / (l * t * a)) /
        (4 * Real.pi * mu) :=
      div_le_div_of_nonneg_right (add_le_add le_rfl hterm) (by positivity)
    _ = _ := by field_simp

/-- The scalar step with the exact derivative and denominator-power indices
needed by the weighted integration-by-parts induction. -/
theorem offSupport_step_power_fraction_le (k r q : ℕ)
    {A B mu t a : ℝ} (hB : 0 ≤ B) (hmu : 0 < mu) (ht : 0 < t)
    (ha : 0 < a) (hta : t ≤ 2 * a) :
    (A / (mu ^ k * t ^ (k + (r + 1)) * a ^ (k + (q + 1))) +
      (q + 1 : ℝ) * (B / (mu ^ k * t ^ (k + r) * a ^ (k + (q + 2))))) /
        (4 * Real.pi * mu) ≤
      ((A + 2 * (q + 1 : ℝ) * B) / (4 * Real.pi)) /
        (mu ^ (k + 1) * t ^ (k + 1 + r) * a ^ (k + 1 + q)) := by
  have h1 : mu ^ k * t ^ (k + (r + 1)) * a ^ (k + (q + 1)) =
      (mu ^ k * t ^ (k + r) * a ^ (k + q)) * t * a := by
    simp only [pow_add, pow_one]
    ring
  have h2 : mu ^ k * t ^ (k + r) * a ^ (k + (q + 2)) =
      (mu ^ k * t ^ (k + r) * a ^ (k + q)) * a ^ 2 := by
    simp only [pow_add]
    ring
  have h3 : mu ^ (k + 1) * t ^ (k + 1 + r) * a ^ (k + 1 + q) =
      mu * (mu ^ k * t ^ (k + r) * a ^ (k + q)) * t * a := by
    simp only [pow_add, pow_one]
    ring
  rw [h1, h2, h3]
  exact offSupport_step_fraction_le hB (by positivity) (by positivity) hmu ht ha hta

/-- Iterating the weighted recurrence yields the exact all-order decay.
The analytic zero-step and one-step estimates are supplied separately. -/
theorem offSupportDecay_bound_of_step (U : ℕ → ℕ → ℝ)
    {mu t a : ℝ} (hmu : 0 < mu) (ht : 0 < t) (ha : 0 < a) (hta : t ≤ 2 * a)
    (hzero : ∀ r q : ℕ,
      U r q ≤ 3 ^ q * offSupportDerivativeMass r / (t ^ r * a ^ q))
    (hstep : ∀ r q : ℕ,
      U r q ≤ (U (r + 1) (q + 1) + (q + 1 : ℝ) * U r (q + 2)) /
        (4 * Real.pi * mu)) :
    ∀ k r q : ℕ, U r q ≤ offSupportDecayConstant k r q /
      (mu ^ k * t ^ (k + r) * a ^ (k + q)) := by
  intro k
  induction k with
  | zero =>
      intro r q
      simpa only [offSupportDecayConstant, pow_zero, zero_add, one_mul] using hzero r q
  | succ k ih =>
      intro r q
      apply (hstep r q).trans
      calc
        _ ≤ (offSupportDecayConstant k (r + 1) (q + 1) /
            (mu ^ k * t ^ (k + (r + 1)) * a ^ (k + (q + 1))) +
            (q + 1 : ℝ) * (offSupportDecayConstant k r (q + 2) /
              (mu ^ k * t ^ (k + r) * a ^ (k + (q + 2))))) /
              (4 * Real.pi * mu) :=
          div_le_div_of_nonneg_right
            (add_le_add (ih (r + 1) (q + 1))
              (mul_le_mul_of_nonneg_left (ih r (q + 2)) (by positivity))) (by positivity)
        _ ≤ _ := offSupport_step_power_fraction_le k r q
          (offSupportDecayConstant_nonneg k r (q + 2)) hmu ht ha hta


end QuadraticCarleson
