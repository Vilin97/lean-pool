/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Local uniqueness from smooth test pairings

These measure-generic facts turn a vanishing distributional pairing into
almost-everywhere vanishing on an open set. They require no regularity of the
L² representative itself.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ]

/-- An L² class annihilating all smooth tests supported in an open set vanishes there. -/
theorem lp_ae_eq_zero_on_of_smooth_tests (u : Lp ℝ 2 μ) {U : Set E}
    (hU : IsOpen U)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, φ x * u x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → u x = 0 := by
  apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp u).integrable (by norm_num)).integrableOn.locallyIntegrableOn
  simpa only [smul_eq_mul] using h

/-- Pairing with a function supported in the vanishing open set is zero. -/
theorem integral_mul_eq_zero_of_lp_smooth_tests (u : Lp ℝ 2 μ) {U : Set E}
    (hU : IsOpen U)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, φ x * u x ∂μ = 0)
    (q : E → ℝ) (hq : Function.support q ⊆ U) :
    ∫ x, u x * q x ∂μ = 0 := by
  have hu := lp_ae_eq_zero_on_of_smooth_tests u hU h
  apply integral_eq_zero_of_ae
  filter_upwards [hu] with x hx
  by_cases hqx : q x = 0
  · simp [hqx]
  · simp [hx (hq hqx)]

end AlmostSchur
