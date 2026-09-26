/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Order.Ring.Rat

/-!
# Tests for nonpositive Hahn series and their integer parts

The examples distinguish nonpositive support and integral constant coefficient from the nearby
unrestricted conditions.
-/

public noncomputable section

namespace Tests

open HahnSeries

/-- A monomial with positive exponent does not belong to the nonpositive Hahn subring. -/
theorem positiveMonomial_not_mem_nonpositiveSubring :
    HahnSeries.single (1 : ℚ) (1 : ℚ) ∉ nonpositiveSubring ℚ ℚ := by
  rw [mem_nonpositiveSubring]
  intro h
  have hsupport : (1 : ℚ) ∈ (HahnSeries.single (1 : ℚ) (1 : ℚ)).support := by
    simp
  exact (by norm_num : ¬(1 : ℚ) ≤ 0) (h hsupport)

/-- A nonconstant rational Hahn series with integral constant coefficient. -/
def nonconstantIntegerPartSeries : Nonpositive ℚ ℚ :=
  Nonpositive.C (Γ := ℚ) (R := ℚ) 2 +
    Nonpositive.single (Γ := ℚ) (R := ℚ) (-1) 3 (by norm_num)

theorem nonconstantIntegerPartSeries_coeff_neg_one :
    (nonconstantIntegerPartSeries : HahnSeries ℚ ℚ).coeff (-1) = 3 := by
  simp [nonconstantIntegerPartSeries]

theorem nonconstantIntegerPartSeries_constantCoeff :
    Nonpositive.constantCoeff (Γ := ℚ) (R := ℚ) nonconstantIntegerPartSeries = 2 := by
  simp [nonconstantIntegerPartSeries]

theorem nonconstantIntegerPartSeries_mem_truncationIntegerPart :
    nonconstantIntegerPartSeries ∈ truncationIntegerPart ℚ (⊥ : Subring ℚ) := by
  simp [nonconstantIntegerPartSeries]

theorem nonconstantIntegerPartSeries_add_self_mem_truncationIntegerPart :
    nonconstantIntegerPartSeries + nonconstantIntegerPartSeries ∈
      truncationIntegerPart ℚ (⊥ : Subring ℚ) :=
  (truncationIntegerPart ℚ (⊥ : Subring ℚ)).add_mem
    nonconstantIntegerPartSeries_mem_truncationIntegerPart
    nonconstantIntegerPartSeries_mem_truncationIntegerPart

theorem nonconstantIntegerPartSeries_mul_self_mem_truncationIntegerPart :
    nonconstantIntegerPartSeries * nonconstantIntegerPartSeries ∈
      truncationIntegerPart ℚ (⊥ : Subring ℚ) :=
  (truncationIntegerPart ℚ (⊥ : Subring ℚ)).mul_mem
    nonconstantIntegerPartSeries_mem_truncationIntegerPart
    nonconstantIntegerPartSeries_mem_truncationIntegerPart

theorem nonconstantIntegerPartSeries_add_self_constantCoeff :
    Nonpositive.constantCoeff (Γ := ℚ) (R := ℚ)
      (nonconstantIntegerPartSeries + nonconstantIntegerPartSeries) = 4 := by
  rw [map_add, nonconstantIntegerPartSeries_constantCoeff]
  norm_num

theorem nonconstantIntegerPartSeries_mul_self_constantCoeff :
    Nonpositive.constantCoeff (Γ := ℚ) (R := ℚ)
      (nonconstantIntegerPartSeries * nonconstantIntegerPartSeries) = 4 := by
  rw [map_mul, nonconstantIntegerPartSeries_constantCoeff]
  norm_num

/-- A nonpositive rational Hahn series whose constant coefficient is not integral. -/
def nonintegralConstantSeries : Nonpositive ℚ ℚ :=
  Nonpositive.C (Γ := ℚ) (R := ℚ) (1 / 2) +
    Nonpositive.single (Γ := ℚ) (R := ℚ) (-1) 3 (by norm_num)

theorem nonintegralConstantSeries_not_mem_truncationIntegerPart :
    nonintegralConstantSeries ∉ truncationIntegerPart ℚ (⊥ : Subring ℚ) := by
  norm_num [nonintegralConstantSeries, Subring.mem_bot]
  intro z hz
  have hz2 := congrArg (fun q : ℚ => q * 2) hz
  norm_num at hz2
  norm_cast at hz2
  omega

end Tests
