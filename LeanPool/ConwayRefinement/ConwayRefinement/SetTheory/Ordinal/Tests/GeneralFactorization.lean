/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.GeneralFactorization

/-!
# Certificate: the residual factor deletes the least Cantor term, not `1`

The nearest plausible wrong reading of `residualFactor_omega0_opow` is the shape proved in
`ConwayRefinement.SetTheory.Ordinal.SuccessorFactorization`, where the residual factor
is `ω ^ (α.removeNat 1)`. That deletes a finite amount from the exponent, so at `α = ω` it must
leave `ω` and predict residual factor `ω ^ ω`.

The theorem gives `1`, and `1 ≠ ω ^ ω` is checked below. The limit case is therefore not an
instance of the successor shape but a genuine strengthening, and it is what makes truncation a
descent at a grade with no finite part.

The degenerate case `α = 1` is included because there the two readings agree, so it certifies
that the generalization did not break the case it generalizes.
-/

open Ordinal

public noncomputable section

namespace Tests

theorem one_lt_omega0_opow {a : Ordinal} (ha : a ≠ 0) : 1 < Ordinal.omega0 ^ a :=
  calc (1 : Ordinal) < Ordinal.omega0 := one_lt_omega0
    _ = Ordinal.omega0 ^ (1 : Ordinal) := (opow_one _).symm
    _ ≤ Ordinal.omega0 ^ a :=
        opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.mpr ha)

theorem residualFactor_omega0_opow_omega0 :
    AdditivePrincipalAboveOne.residualFactor
        ⟨Ordinal.omega0 ^ Ordinal.omega0, isAdditivelyPrincipal_omega0_opow _,
          one_lt_omega0_opow omega0_ne_zero⟩ = 1 := by
  rw [residualFactor_omega0_opow Ordinal.omega0 (isAdditivelyPrincipal_omega0_opow _)
    (one_lt_omega0_opow omega0_ne_zero)]
  have hw : (Ordinal.omega0 : Ordinal) = Ordinal.omega0 ^ (1 : Ordinal) := (opow_one _).symm
  rw [hw, additivePrincipalTerms_of_isAdditivelyPrincipal (isAdditivelyPrincipal_omega0_opow 1)]
  simp

theorem one_ne_omega0_opow_omega0 : (1 : Ordinal) ≠ Ordinal.omega0 ^ Ordinal.omega0 :=
  (one_lt_omega0_opow omega0_ne_zero).ne

theorem residualFactor_omega0_opow_one :
    AdditivePrincipalAboveOne.residualFactor
        ⟨Ordinal.omega0 ^ (1 : Ordinal), isAdditivelyPrincipal_omega0_opow _,
          one_lt_omega0_opow one_ne_zero⟩ = 1 := by
  rw [residualFactor_omega0_opow (1 : Ordinal) (isAdditivelyPrincipal_omega0_opow _)
    (one_lt_omega0_opow one_ne_zero)]
  have h1 : (1 : Ordinal) = Ordinal.omega0 ^ (0 : Ordinal) := by simp
  rw [h1, additivePrincipalTerms_of_isAdditivelyPrincipal (isAdditivelyPrincipal_omega0_opow 0)]
  simp

end Tests

end
