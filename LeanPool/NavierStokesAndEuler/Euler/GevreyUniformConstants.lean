/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionForcing
public import LeanPool.NavierStokesAndEuler.Euler.H6PressureConstants

@[expose] public section

/-! Explicit cutoff-independent coefficient and inverse constants in the nonlinear correction
  estimate. -/

noncomputable section

namespace EulerGevreyUniformConstants

open EulerLiftedGradientSpace EulerCylinderSobolev EulerSpatialSobolevInverse EulerJetProductBounds
  EulerH6Pressure EulerSobolevGevreyOperators EulerBasePressureCommutator EulerPacketWeights
  EulerPressureCommutatorWeights

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- The fixed H⁶ coefficient block is bounded by 448 times the base coefficient bound. -/
theorem coefficientBlock_zero_le {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A) (L : ℝ)
    (hL : ∀ r ≤ 6, boundLevel period K r ≤ L) : coefficientBlock period K 6 0 ≤ 448*L := by
  have h := Finset.sum_le_sum (s := Finset.range 7) (fun r hr => hL r (by have :=
    Finset.mem_range.mp hr; omega))
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 64)
  calc
    _ = 64 * ∑ r ∈ Finset.range 7, boundLevel period K r := by norm_num [coefficientBlock]
    _ ≤ 64 * ∑ _r ∈ Finset.range 7, L := hh
    _ = _ := by simp; ring

omit [Fact (0 < period)] in
/-- The finite weighted coefficient sum is bounded by its base block and a geometric tail. -/
theorem weightedCoefficient_le {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hsmall : ρ*Rc ≤ 1/2)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2) :
    weightedCoefficient period K 6 N ρ ≤ coefficientBlock period K 6 0+2*(ρ*Rc) := by
  have h := positiveCoefficientSum_bound ρ Rc hρ hRc hsmall N (coefficientBlock period K 6) hcoeff
  have he : weightedCoefficient period K 6 N ρ = coefficientBlock period K 6 0+
      ∑ l ∈ Finset.range (N+1), weight ρ l*positivePart (coefficientBlock period K 6) l := by
    rw [weightedCoefficient, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [positivePart, Nat.add_one_ne_zero, ite_false, ite_true, mul_zero, add_zero]
    simp only [weight, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, div_one, one_mul]
    ring
  rw [he]
  exact add_le_add le_rfl h

omit [Fact (0 < period)] in
/-- Under the fixed geometric smallness condition the coefficient multiplier bound is independent of N. -/
theorem weightedCoefficient_uniform {s : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (N : ℕ) (ρ Rc L : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hsmall : ρ*Rc ≤ 1/2)
    (hL : ∀ r ≤ 6, boundLevel period K r ≤ L)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2) :
    weightedCoefficient period K 6 N ρ ≤ 448*L+1 := by
  have h := weightedCoefficient_le period K N ρ Rc hρ hRc hsmall hcoeff
  have hz := coefficientBlock_zero_le period K L hL
  linarith

omit [Fact (0 < period)] in
/-- Summed positive base coefficient derivatives contribute at most 6L. -/
theorem baseCoefficientSum_le {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A) (L : ℝ)
    (hL : ∀ r ≤ 6, boundLevel period K r ≤ L) : baseCoefficientSum period K ≤ 6*L := by
  have h := Finset.sum_le_sum (s := Finset.range 6) (fun r hr => hL (r+1) (by have :=
    Finset.mem_range.mp hr; omega))
  simpa [baseCoefficientSum] using h

omit [Fact (0 < period)] in
/-- One explicit polynomial bounds every coercive inverse at base order at most six. -/
theorem pressureConstant_le_six {q : ℕ} (hq : q ≤ 6) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection q A)
    (c L : ℝ) (hc : 0 < c) (hL : 1 ≤ L) (hcL : c⁻¹ ≤ L)
    (hcoeff : ∀ r ≤ q, boundLevel period K r ≤ L) : K.pressureConstant c ≤ (9*L)^729 := by
  have h := pressureConstant_polynomial K c L hc hL hcL hcoeff
  have he : 3^q ≤ 729 := by
    exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hq).trans (by norm_num)
  exact h.trans (pow_le_pow_right₀ (by linarith : 1 ≤ 9*L) he)

omit [Fact (0 < period)] in
/-- Both fixed inverse orders needed by the actual pressure forcing have the same cutoff-independent polynomial bound. -/
theorem fixed_pressure_constants {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (c L : ℝ) (hc : 0 < c) (hL : 1 ≤ L) (hcL : c⁻¹ ≤ L)
    (hcoeff : ∀ r ≤ 6, boundLevel period K r ≤ L) :
    (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ (9*L)^729 ∧
    (EulerH6Pressure.CoefficientJet.restrict K 6 hs).pressureConstant c ≤ (9*L)^729 := by
  constructor
  · apply pressureConstant_le_six period (by norm_num : 5 ≤ 6) _ c L hc hL hcL
    intro r hr
    rw [coefficient_restrict_level period K (by omega : 5 ≤ s) hr]
    exact hcoeff r (by omega)
  · apply pressureConstant_le_six period (by norm_num : 6 ≤ 6) _ c L hc hL hcL
    intro r hr
    rw [coefficient_restrict_level period K hs hr]
    exact hcoeff r hr

end EulerGevreyUniformConstants
