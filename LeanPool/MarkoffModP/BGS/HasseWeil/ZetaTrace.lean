/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic

/-!
# From zeta-function spectral data to the Hasse--Weil estimate

This file isolates the final, elementary inequality in the Hasse--Weil
argument. Once the point-count formula writes the error as a sum of `2g`
Frobenius parameters of norm at most `sqrt q`, the projective point-count
bound follows from the triangle inequality.

The zeta-function construction and the proof of the spectral bound are kept
separate: they are the substantive preceding stages of the
Corvaja--Zannier/Bombieri argument.
-/

@[expose] public section

namespace BGS.HasseWeil

open scoped BigOperators

noncomputable section

/-- A single point-count formula with `2g` Frobenius parameters. -/
def HasPointCountSpectralFormula
    (q g N : ℕ) (alpha : Fin (2 * g) → ℂ) : Prop :=
  (N : ℂ) = (q : ℂ) + 1 - ∑ i, alpha i

/-- The Hasse--Weil inequality is the triangle inequality once every
Frobenius parameter has norm at most `sqrt q`. -/
theorem abs_pointCount_sub_card_sub_one_le_of_spectralFormula
    (q g N : ℕ) (alpha : Fin (2 * g) → ℂ)
    (hformula : HasPointCountSpectralFormula q g N alpha)
    (hspectral : ∀ i, ‖alpha i‖ ≤ Real.sqrt q) :
    |(N : ℝ) - q - 1| ≤ (2 * g : ℝ) * Real.sqrt q := by
  have hformula' :
      (N : ℂ) = (q : ℂ) + 1 - ∑ i, alpha i := hformula
  have herror :
      (((N : ℝ) - q - 1 : ℝ) : ℂ) = -(∑ i, alpha i) := by
    push_cast
    linear_combination hformula'
  calc
    |(N : ℝ) - q - 1| = ‖(((N : ℝ) - q - 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ i, alpha i‖ := by rw [herror, norm_neg]
    _ ≤ ∑ i, ‖alpha i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (2 * g), Real.sqrt q := by
      exact Finset.sum_le_sum fun i _ => hspectral i
    _ = (2 * g : ℝ) * Real.sqrt q := by simp

end

end BGS.HasseWeil
