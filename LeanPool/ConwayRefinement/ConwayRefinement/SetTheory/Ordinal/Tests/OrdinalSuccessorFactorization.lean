/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SuccessorFactorization

import Mathlib.Tactic.NormNum

/-!
# API checks for successor-exponent factorisation

The successor fixture has exponent `omega + 1`. Its principal factor is `omega`, while its
residual factor is `omega ^ omega`. This separates the intended last-factor convention from
using the entire power as the principal factor or assigning residual value one at every
successor exponent.

The neighboring limit fixture has exponent `omega`; its full power is already infinitely
multiplicatively principal and is therefore its own principal factor. This checks that the
positive-constant-coefficient hypothesis is essential.
-/

open scoped NatOrdinal
open Ordinal

public noncomputable section

namespace Tests

/-- The limit exponent `omega`. -/
abbrev successorFactorLimitExponent : NatOrdinal := ω^ (1 : NatOrdinal)

/-- The successor exponent `omega + 1`. -/
abbrev successorFactorLimitSuccessorExponent : NatOrdinal :=
  successorFactorLimitExponent + (1 : ℕ)

theorem successorFactorLimitSuccessorExponent_constantCoeff :
    successorFactorLimitSuccessorExponent.constantCoeff = 1 := by
  rw [successorFactorLimitSuccessorExponent, NatOrdinal.constantCoeff_add_natCast]
  rw [successorFactorLimitExponent, NatOrdinal.constantCoeff_wpow]
  simp

theorem successorFactorLimitSuccessorExponent_removeOne :
    successorFactorLimitSuccessorExponent.removeNat 1 = successorFactorLimitExponent := by
  symm
  apply (NatOrdinal.eq_removeNat_iff_add_natCast_eq
    (a := successorFactorLimitSuccessorExponent)
    (eta := successorFactorLimitExponent) (n := 1) (by
      rw [successorFactorLimitSuccessorExponent_constantCoeff])).mpr
  rfl

private theorem successorFactorLimitSuccessorExponent_ne_zero :
    successorFactorLimitSuccessorExponent ≠ 0 := by
  intro hzero
  have h := congrArg NatOrdinal.constantCoeff hzero
  rw [successorFactorLimitSuccessorExponent_constantCoeff,
    NatOrdinal.constantCoeff_zero] at h
  norm_num at h

/-- The power at exponent `omega + 1` lies in the domain of the factor projections. -/
theorem one_lt_wpow_successorFactorLimitSuccessor :
    1 < Ordinal.omega0 ^ successorFactorLimitSuccessorExponent.val := by
  rw [Ordinal.one_lt_opow]
  exact ⟨Ordinal.one_lt_omega0,
    NatOrdinal.val_ne_zero.mpr successorFactorLimitSuccessorExponent_ne_zero⟩

/-- At exponent `omega + 1`, the final multiplicatively principal factor is `omega`. -/
theorem principalFactor_wpow_successorFactorLimitSuccessor :
    Ordinal.AdditivePrincipalAboveOne.principalFactor
        (⟨Ordinal.omega0 ^ successorFactorLimitSuccessorExponent.val,
          Ordinal.isAdditivelyPrincipal_omega0_opow
            successorFactorLimitSuccessorExponent.val,
          one_lt_wpow_successorFactorLimitSuccessor⟩ :
          Ordinal.AdditivePrincipalAboveOne) = Ordinal.omega0 :=
  Ordinal.AdditivePrincipalAboveOne.principalFactor_wpow_of_constantCoeff_pos
    successorFactorLimitSuccessorExponent
      (by rw [successorFactorLimitSuccessorExponent_constantCoeff]; norm_num)
      (Ordinal.isAdditivelyPrincipal_omega0_opow
        successorFactorLimitSuccessorExponent.val)
      one_lt_wpow_successorFactorLimitSuccessor

/-- At exponent `omega + 1`, deleting the final factor leaves `omega ^ omega`. -/
theorem residualFactor_wpow_successorFactorLimitSuccessor :
    Ordinal.AdditivePrincipalAboveOne.residualFactor
        (⟨Ordinal.omega0 ^ successorFactorLimitSuccessorExponent.val,
          Ordinal.isAdditivelyPrincipal_omega0_opow
            successorFactorLimitSuccessorExponent.val,
          one_lt_wpow_successorFactorLimitSuccessor⟩ :
          Ordinal.AdditivePrincipalAboveOne) =
      Ordinal.omega0 ^ successorFactorLimitExponent.val := by
  rw [Ordinal.AdditivePrincipalAboveOne.residualFactor_wpow_of_constantCoeff_pos
    successorFactorLimitSuccessorExponent
    (by rw [successorFactorLimitSuccessorExponent_constantCoeff]; norm_num)
    (Ordinal.isAdditivelyPrincipal_omega0_opow
      successorFactorLimitSuccessorExponent.val)
    one_lt_wpow_successorFactorLimitSuccessor]
  rw [successorFactorLimitSuccessorExponent_removeOne]

private theorem successorFactorLimitExponent_ne_zero : successorFactorLimitExponent ≠ 0 :=
  NatOrdinal.wpow_ne_zero 1

/-- The power at exponent `omega` lies in the domain of the factor projections. -/
theorem one_lt_wpow_successorFactorLimit :
    1 < Ordinal.omega0 ^ successorFactorLimitExponent.val := by
  rw [Ordinal.one_lt_opow]
  exact ⟨Ordinal.one_lt_omega0,
    NatOrdinal.val_ne_zero.mpr successorFactorLimitExponent_ne_zero⟩

private theorem wpow_successorFactorLimit_isInfiniteMultiplicativelyPrincipal :
    Ordinal.IsInfiniteMultiplicativelyPrincipal
      (Ordinal.omega0 ^ successorFactorLimitExponent.val) := by
  simpa only [NatOrdinal.val_wpow, NatOrdinal.val_one] using
    Ordinal.isInfiniteMultiplicativelyPrincipal_omega0_opow_opow 1

/-- At the neighboring limit exponent `omega`, the principal factor is not `omega`; it is the
entire power `omega ^ omega`. -/
theorem principalFactor_wpow_successorFactorLimit_ne_omega0 :
    Ordinal.AdditivePrincipalAboveOne.principalFactor
        (⟨Ordinal.omega0 ^ successorFactorLimitExponent.val,
          Ordinal.isAdditivelyPrincipal_omega0_opow successorFactorLimitExponent.val,
          one_lt_wpow_successorFactorLimit⟩ : Ordinal.AdditivePrincipalAboveOne) ≠
      Ordinal.omega0 := by
  rw [AdditivePrincipalAboveOne.principalFactor_eq_self_of_isInfiniteMultiplicativelyPrincipal
    _ wpow_successorFactorLimit_isInfiniteMultiplicativelyPrincipal]
  apply ne_of_gt
  change Ordinal.omega0 < Ordinal.omega0 ^ (Ordinal.omega0 ^ (1 : Ordinal))
  simpa only [Ordinal.opow_one] using
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      Ordinal.one_lt_omega0

end Tests
