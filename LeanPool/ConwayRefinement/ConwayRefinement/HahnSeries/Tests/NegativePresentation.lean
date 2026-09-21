/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Negative
public import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.NormNum

/-!
# API checks for the strictly negative presentation

This file checks the public presentation of a truncation integer part as the pointwise sum of
integral constants and strictly negative Hahn series. The examples distinguish strict-negative
support from nonpositive support, exercise multiplication in the nonunital negative ring, and
verify existence and uniqueness for a nonconstant element of `TIP(ℤ, ℚ, ℚ)`.
-/

public noncomputable section

namespace Tests

open scoped Pointwise

open HahnSeries

/-- The monomial `3t⁻¹`, regarded as a strictly negative rational Hahn series. -/
def negativeMonomial : Negative ℚ ℚ :=
  Negative.single (-1) 3 (by norm_num)

theorem negativeMonomial_coeff_neg_one :
    (negativeMonomial : HahnSeries ℚ ℚ).coeff (-1) = 3 := by
  simp [negativeMonomial]

theorem negativeMonomial_constantCoeff :
    Nonpositive.constantCoeff (Γ := ℚ) (R := ℚ) negativeMonomial = 0 :=
  Negative.constantCoeff_eq_zero negativeMonomial

theorem one_not_mem_negativeIdeal :
    (1 : Nonpositive ℚ ℚ) ∉ negativeIdeal ℚ ℚ := by
  intro h
  have hzero := Negative.constantCoeff_eq_zero
    (⟨1, h⟩ : Negative ℚ ℚ)
  simp at hzero

theorem negativeMonomial_mul_self_coeff_neg_two :
    (((negativeMonomial * negativeMonomial : Negative ℚ ℚ) : Nonpositive ℚ ℚ) :
      HahnSeries ℚ ℚ).coeff (-2) = 9 := by
  norm_num [negativeMonomial]

/-- The series `2 + 3t⁻¹` in the nonpositive rational Hahn ring. -/
def presentedIntegerPartSeries : Nonpositive ℚ ℚ :=
  Nonpositive.C (Γ := ℚ) (R := ℚ) 2 + (negativeMonomial : Nonpositive ℚ ℚ)

theorem presentedIntegerPartSeries_mem :
    presentedIntegerPartSeries ∈ truncationIntegerPart ℚ (⊥ : Subring ℚ) := by
  apply (mem_truncationIntegerPart_iff_exists_add_negative
    (Γ := ℚ) (R := ℚ)).mpr
  exact ⟨2, negativeMonomial, rfl⟩

theorem presentedIntegerPartSeries_negativePart :
    Nonpositive.negativePart ℚ ℚ presentedIntegerPartSeries = negativeMonomial := by
  simp [presentedIntegerPartSeries]

theorem presentedIntegerPartSeries_decomposition_unique
    (z : (⊥ : Subring ℚ)) (n : Negative ℚ ℚ)
    (h : presentedIntegerPartSeries =
      Nonpositive.C (Γ := ℚ) (R := ℚ) z + (n : Nonpositive ℚ ℚ)) :
    z = 2 ∧ n = negativeMonomial := by
  apply (constant_add_negative_eq_iff (Γ := ℚ) (R := ℚ)).mp
  have htwo : ((2 : (⊥ : Subring ℚ)) : ℚ) = 2 :=
    Subring.coe_natCast (⊥ : Subring ℚ) 2
  simpa only [presentedIntegerPartSeries, htwo] using h.symm

theorem rational_truncationIntegerPart_carrier :
    (truncationIntegerPart ℚ (⊥ : Subring ℚ) : Set (Nonpositive ℚ ℚ)) =
      (constantSubring ℚ ℚ (⊥ : Subring ℚ) : Set (Nonpositive ℚ ℚ)) +
        (negativeIdeal ℚ ℚ : Set (Nonpositive ℚ ℚ)) :=
  coe_truncationIntegerPart_eq_constantSubring_add_negativeIdeal ℚ ℚ
    (⊥ : Subring ℚ)

end Tests
