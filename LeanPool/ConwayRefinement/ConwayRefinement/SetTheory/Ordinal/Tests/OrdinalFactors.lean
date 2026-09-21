/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.MultiplicativelyPrincipal

import Mathlib.Tactic.NormNum

/-!
# API checks for multiplicatively principal ordinal factors

The first certificate exposes the exceptional ordinal `2`: it satisfies Berarducci's printed
multiplicative-principality predicate but is not one of the infinite factors described in the
paper's classification. This prevents the exact source predicate from being silently replaced by
the incomplete classification.

The value `ω ^ 3` has three equal factors, while `ω ^ (ω + 1)` has the asymmetric factor list
`[ω ^ ω, ω]`. The latter example distinguishes the final principal factor from the initial
factor and verifies the residual factor simultaneously. A singleton example checks Berarducci's
convention that the residual factor is one when the value is already infinite multiplicatively
principal. The final certificate exercises the equality between ordinary and Hessenberg products.
-/

open scoped NatOrdinal

public noncomputable section

namespace Tests

open Ordinal

/-- The finite ordinal two separates Berarducci's exact predicate from the infinite factor
shape asserted by the paper's incomplete classification. -/
theorem two_multiplicativePrincipal_boundary :
    IsMultiplicativelyPrincipal (2 : Ordinal) ∧
      ¬IsInfiniteMultiplicativelyPrincipal 2 := by
  constructor
  · exact isMultiplicativelyPrincipal_two
  · rw [isInfiniteMultiplicativelyPrincipal_iff_two_lt_and_isMultiplicativelyPrincipal]
    simp

private theorem omegaCubed_product :
    [omega0, omega0, omega0].prod = omega0 ^ (3 : Ordinal) := by
  simp only [List.prod_cons, List.prod_nil, mul_one]
  rw [← opow_one omega0, ← opow_add, ← opow_add]
  norm_num

/-- The canonical multiplicative factor list of `ω ^ 3` consists of three copies of `ω`. -/
theorem omegaCubed_multiplicativePrincipalFactors :
    [omega0, omega0, omega0] =
      (omega0 ^ (3 : Ordinal)).multiplicativePrincipalFactors := by
  apply multiplicativePrincipalFactors_unique
  · exact isAdditivelyPrincipal_omega0_opow 3
  · exact omegaCubed_product
  · intro f hf
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    all_goals simpa [opow_zero, opow_one] using
      isMultiplicativelyPrincipal_omega0_opow_opow 0
  · intro f hf
    rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    all_goals exact one_lt_omega0
  · simp [List.sortedGE_iff_pairwise]

/-- The additive-principal value `ω ^ 3`, packaged in the exact domain of the principal and
residual factor operations. -/
def omegaCubedValue : AdditivePrincipalAboveOne.{0} :=
  ⟨omega0 ^ (3 : Ordinal), isAdditivelyPrincipal_omega0_opow 3,
    by rw [one_lt_opow]; exact ⟨one_lt_omega0, by norm_num⟩⟩

/-- Berarducci's example `ω ^ 3` has principal factor `ω` and residual factor `ω ^ 2`. -/
theorem omegaCubed_principal_residual :
    omegaCubedValue.principalFactor = omega0 ∧
      omegaCubedValue.residualFactor = omega0 ^ (2 : Ordinal) := by
  constructor
  · rw [omegaCubedValue.principalFactor_eq_getLast]
    change (omega0 ^ (3 : Ordinal)).multiplicativePrincipalFactors.getLast _ = omega0
    calc
      (omega0 ^ (3 : Ordinal)).multiplicativePrincipalFactors.getLast _ =
          [omega0, omega0, omega0].getLast (by simp) :=
        List.getLast_congr _ _ omegaCubed_multiplicativePrincipalFactors.symm
      _ = omega0 := rfl
  · rw [omegaCubedValue.residualFactor_eq_dropLast_prod]
    change (omega0 ^ (3 : Ordinal)).multiplicativePrincipalFactors.dropLast.prod =
      omega0 ^ (2 : Ordinal)
    rw [omegaCubed_multiplicativePrincipalFactors.symm]
    simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.prod_cons,
      List.prod_nil, mul_one]
    rw [← opow_one omega0, ← opow_add]
    norm_num

private theorem omegaOmegaMulOmega_product :
    [omega0 ^ omega0, omega0].prod =
      omega0 ^ (omega0 + 1) := by
  simp only [List.prod_cons, List.prod_nil, mul_one]
  simp

/-- The canonical factor list of `ω ^ (ω + 1)` is the asymmetric list `[ω ^ ω, ω]`. -/
theorem omegaOmegaAddOne_multiplicativePrincipalFactors :
    [omega0 ^ omega0, omega0] =
      (omega0 ^ (omega0 + 1)).multiplicativePrincipalFactors := by
  apply multiplicativePrincipalFactors_unique
  · exact isAdditivelyPrincipal_omega0_opow (omega0 + 1)
  · exact omegaOmegaMulOmega_product
  · intro f hf
    rw [List.mem_cons, List.mem_singleton] at hf
    rcases hf with rfl | rfl
    · simpa [opow_one] using isMultiplicativelyPrincipal_omega0_opow_opow 1
    · simpa [opow_zero, opow_one] using
        isMultiplicativelyPrincipal_omega0_opow_opow 0
  · intro f hf
    rw [List.mem_cons, List.mem_singleton] at hf
    rcases hf with rfl | rfl
    · rw [one_lt_opow]
      exact ⟨one_lt_omega0, omega0_ne_zero⟩
    · exact one_lt_omega0
  · rw [List.sortedGE_iff_pairwise, List.pairwise_cons]
    constructor
    · intro f hf
      rw [List.mem_singleton] at hf
      subst f
      simpa [opow_one] using
        opow_le_opow_right omega0_pos (show (1 : Ordinal) ≤ omega0 by
          exact one_lt_omega0.le)
    · exact List.pairwise_singleton _ _

/-- The additive-principal value `ω ^ (ω + 1)`, packaged in the exact factor domain. -/
def omegaOmegaAddOneValue : AdditivePrincipalAboveOne.{0} :=
  ⟨omega0 ^ (omega0 + 1),
    isAdditivelyPrincipal_omega0_opow (omega0 + 1),
    by rw [one_lt_opow]; exact ⟨one_lt_omega0, by simp⟩⟩

/-- The asymmetric example has final principal factor `ω` and residual factor `ω ^ ω`. -/
theorem omegaOmegaAddOne_principal_residual :
    omegaOmegaAddOneValue.principalFactor = omega0 ∧
      omegaOmegaAddOneValue.residualFactor = omega0 ^ omega0 := by
  constructor
  · rw [omegaOmegaAddOneValue.principalFactor_eq_getLast]
    change (omega0 ^ (omega0 + 1)).multiplicativePrincipalFactors.getLast _ =
      omega0
    calc
      (omega0 ^ (omega0 + 1)).multiplicativePrincipalFactors.getLast _ =
          [omega0 ^ omega0, omega0].getLast (by simp) :=
        List.getLast_congr _ _
          omegaOmegaAddOne_multiplicativePrincipalFactors.symm
      _ = omega0 := rfl
  · rw [omegaOmegaAddOneValue.residualFactor_eq_dropLast_prod]
    change (omega0 ^ (omega0 + 1)).multiplicativePrincipalFactors.dropLast.prod =
      omega0 ^ omega0
    rw [omegaOmegaAddOne_multiplicativePrincipalFactors.symm]
    simp

/-- The infinite multiplicatively principal value `ω ^ ω`, packaged in the exact factor
domain. -/
def omegaOmegaValue : AdditivePrincipalAboveOne.{0} :=
  ⟨omega0 ^ omega0, isAdditivelyPrincipal_omega0_opow omega0,
    by rw [one_lt_opow]; exact ⟨one_lt_omega0, omega0_ne_zero⟩⟩

/-- A singleton factor list gives principal factor equal to the value and residual factor one. -/
theorem omegaOmega_principal_residual :
    omegaOmegaValue.principalFactor = omega0 ^ omega0 ∧
      omegaOmegaValue.residualFactor = 1 := by
  have hprincipal : IsInfiniteMultiplicativelyPrincipal (omega0 ^ omega0) := by
    simpa [opow_one] using isInfiniteMultiplicativelyPrincipal_omega0_opow_opow 1
  have hprincipal' : IsInfiniteMultiplicativelyPrincipal omegaOmegaValue.1 := by
    simpa [omegaOmegaValue] using hprincipal
  exact ⟨omegaOmegaValue.principalFactor_eq_self_of_isInfiniteMultiplicativelyPrincipal
      hprincipal',
    omegaOmegaValue.residualFactor_eq_one_of_isInfiniteMultiplicativelyPrincipal
      hprincipal'⟩

/-- In the asymmetric example, the Hessenberg product of the residual and principal factors
equals the same ordinal as their ordinary product. -/
theorem omegaOmegaAddOne_natural_factorization :
    NatOrdinal.of ((omega0 : Ordinal.{0}) ^ omega0) * NatOrdinal.of omega0 =
      NatOrdinal.of ((omega0 : Ordinal.{0}) ^ (omega0 + 1)) := by
  have h := omegaOmegaAddOneValue.naturalResidual_mul_naturalPrincipal
  rw [omegaOmegaAddOne_principal_residual.1,
    omegaOmegaAddOne_principal_residual.2] at h
  simpa [omegaOmegaAddOneValue] using h

end Tests
