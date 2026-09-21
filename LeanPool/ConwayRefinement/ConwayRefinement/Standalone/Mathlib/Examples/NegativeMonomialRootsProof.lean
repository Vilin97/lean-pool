/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Examples.NegativeMonomialRoots

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Negative Monomial Roots Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.Hahn.NegativeMonomialExample

private theorem eq_zero_of_mem_addAntidiagonal_zero {x y : Ring} {ij : ℝ × ℝ}
    (hij : ij ∈ Finset.addAntidiagonal x.1.isPWO_support y.1.isPWO_support 0) :
    ij = (0, 0) := by
  rcases Finset.mem_addAntidiagonal.mp hij with ⟨hi, hj, hij⟩
  have hi_zero := eq_zero_of_add_nonneg_left (x.2 hi) (y.2 hj) hij.ge
  have hj_zero := eq_zero_of_add_nonneg_right (x.2 hi) (y.2 hj) hij.ge
  exact Prod.ext hi_zero hj_zero

private def constantCoeff : Ring →+* ℚ where
  toFun x := x.1.coeff 0
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    change (x.1 * y.1).coeff 0 = x.1.coeff 0 * y.1.coeff 0
    rw [HahnSeries.coeff_mul]
    by_cases hx : x.1.coeff 0 = 0
    · rw [hx, zero_mul]
      apply Finset.sum_eq_zero
      intro ij hij
      rw [eq_zero_of_mem_addAntidiagonal_zero hij]
      simp [hx]
    · by_cases hy : y.1.coeff 0 = 0
      · rw [hy, mul_zero]
        apply Finset.sum_eq_zero
        intro ij hij
        rw [eq_zero_of_mem_addAntidiagonal_zero hij]
        simp [hy]
      · apply Finset.sum_eq_single (0, 0)
        · intro ij hij hne
          exact (hne (eq_zero_of_mem_addAntidiagonal_zero hij)).elim
        · simp [Finset.mem_addAntidiagonal, HahnSeries.mem_support, hx, hy]

private theorem nthRoot_not_unit (n : ℕ) (hn : 0 < n) : ¬ IsUnit (nthRoot n) := by
  intro h
  have hu := h.map constantCoeff
  have hz : constantCoeff (nthRoot n) = 0 := by
    change ((HahnSeries.single (-(n : ℝ)⁻¹)) 1).coeff 0 = 0
    rw [HahnSeries.coeff_single_of_ne]
    exact fun hzero ↦ by
      have : (n : ℝ)⁻¹ = 0 := by linarith
      exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) this
  rw [hz] at hu
  exact not_isUnit_zero hu

private theorem nthRoot_pow (n : ℕ) (hn : 0 < n) :
    nthRoot n ^ n = negativeOne := by
  apply Subtype.ext
  simp [nthRoot, negativeOne, monomial, HahnSeries.single_pow]
  field_simp

namespace NegativeMonomialHasAllRoots

/-- The exponent identity `n(-1/n) = -1` gives the factorisation; the zero coefficient shows
that each factor is a nonunit. -/
theorem proof : NegativeMonomialExample.NegativeMonomialHasAllRoots := by
  intro n hn
  exact ⟨nthRoot_not_unit n hn, nthRoot_pow n hn⟩

end NegativeMonomialHasAllRoots

end ConwayRefinement.Standalone.Hahn.NegativeMonomialExample
