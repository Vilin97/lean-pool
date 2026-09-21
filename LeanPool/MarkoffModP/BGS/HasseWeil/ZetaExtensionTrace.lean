/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.SpectralFromAsymptotic

/-!
# Extension point counts and the zeta spectral formula

This file packages the elementary interface between rationality of a curve's
zeta function and the even-extension estimate produced by the
Bombieri--Stepanov/Galois-averaging argument.  The geometric construction of
the zeta function remains a separate preceding stage.
-/

namespace BGS.HasseWeil

open Filter Asymptotics
open scoped BigOperators

noncomputable section

/-- A compatible spectral formula for every positive extension degree. -/
def HasExtensionPointCountSpectralFormula
    (q g : ℕ) (pointCount : ℕ → ℕ) (alpha : Fin (2 * g) → ℂ) : Prop :=
  ∀ m, 0 < m →
    (pointCount m : ℂ) = (q : ℂ) ^ m + 1 - ∑ i, alpha i ^ m

/-- The extension formula at degree one is the single spectral formula used
in the final Hasse inequality. -/
theorem HasExtensionPointCountSpectralFormula.at_one
    {q g : ℕ} {pointCount : ℕ → ℕ} {alpha : Fin (2 * g) → ℂ}
    (h : HasExtensionPointCountSpectralFormula q g pointCount alpha) :
    HasPointCountSpectralFormula q g (pointCount 1) alpha := by
  simpa [HasPointCountSpectralFormula] using h 1 (by omega)

/-- An even-extension point-count error of order `q ^ n` is exactly the
power-sum estimate needed to bound the Frobenius parameters. -/
theorem evenPowerSum_isBigO_of_extensionPointCountError_isBigO
    {q g : ℕ} {pointCount : ℕ → ℕ} {alpha : Fin (2 * g) → ℂ}
    (hformula : HasExtensionPointCountSpectralFormula q g pointCount alpha)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =O[atTop]
          fun n : ℕ ↦ (q : ℝ) ^ n) :
    (fun n : ℕ ↦ ∑ i, alpha i ^ (2 * n)) =O[atTop]
      fun n : ℕ ↦ (q : ℝ) ^ n := by
  apply herror.neg_left.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpositive : 0 < 2 * n := by omega
    have h := hformula (2 * n) hpositive
    change -((pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =
      ∑ i, alpha i ^ (2 * n)
    rw [h]
    ring
  · exact Filter.EventuallyEq.rfl

/-- The complete analytic last step: a zeta spectral formula together with
the two-sided even-extension asymptotic gives Hasse--Weil at the base field. -/
theorem abs_pointCount_sub_card_sub_one_le_of_extensionFormula_and_evenError_isBigO
    (q g : ℕ) (pointCount : ℕ → ℕ) (alpha : Fin (2 * g) → ℂ)
    (hformula : HasExtensionPointCountSpectralFormula q g pointCount alpha)
    (herror :
      (fun n : ℕ ↦
        (pointCount (2 * n) : ℂ) - (q : ℂ) ^ (2 * n) - 1) =O[atTop]
          fun n : ℕ ↦ (q : ℝ) ^ n) :
    |(pointCount 1 : ℝ) - q - 1| ≤ (2 * g : ℝ) * Real.sqrt q := by
  apply abs_pointCount_sub_card_sub_one_le_of_evenPowerSum_isBigO
    q g (pointCount 1) alpha hformula.at_one
  exact evenPowerSum_isBigO_of_extensionPointCountError_isBigO hformula herror

end

end BGS.HasseWeil
