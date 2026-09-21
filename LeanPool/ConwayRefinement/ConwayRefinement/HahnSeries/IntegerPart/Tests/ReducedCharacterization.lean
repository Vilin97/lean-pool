/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedCharacterization

/-!
# API checks for the leading-class characterization of reducedness

The boundary monomial `5t⁻¹` exercises the `tau = 0` branch. The series `1 + 5t⁻¹`
exercises the `tau = 1` branch. Both are nonconstant and reduced, so together they certify the
two alternatives in LM24, Proposition 8.2.5 `(4) ↔ (5)` through the public API.
-/

public noncomputable section

namespace Tests

open HahnSeries

def reducedZeroTauSeries : Nonpositive ℚ ℚ :=
  Nonpositive.single (-1) 5 (by norm_num)

def reducedOneTauSeries : Nonpositive ℚ ℚ :=
  1 + reducedZeroTauSeries

private theorem reducedZeroTauSeries_ne_zero : reducedZeroTauSeries ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun x : Nonpositive ℚ ℚ ↦ (x : ℚ⟦ℚ⟧).coeff (-1)) h
  simp [reducedZeroTauSeries] at hcoeff

private theorem reducedZeroTauSeries_order :
    (reducedZeroTauSeries : ℚ⟦ℚ⟧).order = -1 := by
  rw [reducedZeroTauSeries, Nonpositive.coe_single, HahnSeries.order_single (by norm_num)]

private theorem reducedOneTauSeries_ne_zero : reducedOneTauSeries ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun x : Nonpositive ℚ ℚ ↦ (x : ℚ⟦ℚ⟧).coeff (-1)) h
  simp [reducedOneTauSeries, reducedZeroTauSeries] at hcoeff

private theorem reducedOneTauSeries_order :
    (reducedOneTauSeries : ℚ⟦ℚ⟧).order = -1 := by
  have htop : (reducedOneTauSeries : ℚ⟦ℚ⟧).orderTop = (-1 : ℚ) := by
    apply HahnSeries.orderTop_eq_of_le
    · rw [HahnSeries.mem_support]
      simp [reducedOneTauSeries, reducedZeroTauSeries]
    · intro g hg
      have hgNonpos := Nonpositive.support_subset reducedOneTauSeries hg
      by_contra hnot
      have hgLt : g < (-1 : ℚ) := lt_of_not_ge hnot
      have hgZero : g ≠ 0 := by linarith
      have hgNegOne : g ≠ -1 := by linarith
      rw [HahnSeries.mem_support] at hg
      simp [reducedOneTauSeries, reducedZeroTauSeries, hgZero, hgNegOne] at hg
  exact WithTop.coe_injective
    ((HahnSeries.order_eq_orderTop_of_ne_zero (fun h ↦
      reducedOneTauSeries_ne_zero (Subtype.ext h))).trans htop)

theorem reducedZeroTauSeries_characterization :
    Nonpositive.IsReduced reducedZeroTauSeries ↔
      Nonpositive.tau (K := ℚ)
          (Nonpositive.leadingClass reducedZeroTauSeries (by
            rw [reducedZeroTauSeries_order]
            norm_num))
          reducedZeroTauSeries = 0 ∨
        Nonpositive.tau (K := ℚ)
          (Nonpositive.leadingClass reducedZeroTauSeries (by
            rw [reducedZeroTauSeries_order]
            norm_num))
          reducedZeroTauSeries = 1 :=
  Nonpositive.isReduced_iff_tau_leadingClass_eq_zero_or_one
    reducedZeroTauSeries reducedZeroTauSeries_ne_zero (by
      rw [reducedZeroTauSeries_order]
      norm_num)

theorem reducedOneTauSeries_characterization :
    Nonpositive.IsReduced reducedOneTauSeries ↔
      Nonpositive.tau (K := ℚ)
          (Nonpositive.leadingClass reducedOneTauSeries (by
            rw [reducedOneTauSeries_order]
            norm_num))
          reducedOneTauSeries = 0 ∨
        Nonpositive.tau (K := ℚ)
          (Nonpositive.leadingClass reducedOneTauSeries (by
            rw [reducedOneTauSeries_order]
            norm_num))
          reducedOneTauSeries = 1 :=
  Nonpositive.isReduced_iff_tau_leadingClass_eq_zero_or_one
    reducedOneTauSeries reducedOneTauSeries_ne_zero (by
      rw [reducedOneTauSeries_order]
      norm_num)

end Tests
