/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Counting.Definitions

/-!
# From slope form to the original coefficient form

The bookkeeping step from the normalized slope count to the coefficient
statement of the original conjecture: dividing the coefficient equation
`v₁ x + v₂ y + (v₁+v₂) z = 0` through by `v₁` turns it into the normalized
equation at slope `ρ = v₂/v₁`.

`coefficientTripleCount` itself is the audited definition from
`KasamiCyclicAdditive.Statement.Definitions`.

`Assembly/CoefficientReduction.lean` and `Assembly/Normalization.lean` import
this module; `coefficient_form_nat_of_slope_form` is what carries the assembled
slope theorem back to the coefficient form of the original conjecture.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Dividing the coefficient equation by `v₁` gives the normalized slope
`ρ=v₂/v₁`.  No characteristic-two hypothesis is needed for this bookkeeping
identity. -/
theorem coefficientTripleCount_eq_slopeTripleCount {k : ℕ} {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) :
    coefficientTripleCount k v₁ v₂ = slopeTripleCount k (v₂ / v₁) := by
  unfold coefficientTripleCount slopeTripleCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p hp
  let x : K := p.1
  let y : K := p.2.1
  let z : K := p.2.2
  have hscale :
      v₁ * (x + (v₂ / v₁) * y + (1 + v₂ / v₁) * z)
        = v₁ * x + v₂ * y + (v₁ + v₂) * z := by
    field_simp [hv₁]
  constructor
  · intro h
    have hz : v₁ * (x + (v₂ / v₁) * y + (1 + v₂ / v₁) * z) = 0 := by
      rw [hscale]
      exact h
    exact (mul_eq_zero.mp hz).resolve_left hv₁
  · intro h
    rw [← hscale, h, mul_zero]

omit [Fintype K] [DecidableEq K] in
/-- Distinct nonzero coefficients give an admissible normalized slope. -/
theorem coefficientSlope_admissible {v₁ v₂ : K}
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    AdmissibleSlope (v₂ / v₁) := by
  constructor
  · exact div_ne_zero hv₂ hv₁
  · intro h
    have hv₂1 : v₂ = v₁ := (div_eq_one_iff_eq hv₁).mp h
    exact hne hv₂1.symm

/-- Any theorem proved uniformly for all admissible slopes immediately yields
the original coefficient-form theorem. -/
theorem coefficient_form_of_slope_form {k : ℕ} {c : ℝ}
    (hslope : ∀ ρ ∈ slopes K, (slopeTripleCount k ρ : ℝ) = c)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (coefficientTripleCount k v₁ v₂ : ℝ) = c := by
  rw [coefficientTripleCount_eq_slopeTripleCount hv₁]
  apply hslope (v₂ / v₁)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, coefficientSlope_admissible hv₁ hv₂ hne⟩

omit [Field K] [DecidableEq K] in
/-- The real-valued main term `|K|^2/8` is the natural number `2^(2n-3)`
when `|K| = 2^n` and `n ≥ 2`. -/
theorem card_sq_div_eight_eq_pow {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card K = 2 ^ n) :
    (Fintype.card K : ℝ) ^ 2 / 8 = ((2 ^ (2 * n - 3) : ℕ) : ℝ) := by
  rw [hcard]
  push_cast
  rw [← pow_mul, Nat.mul_comm n 2]
  have h3 : 3 ≤ 2 * n := by omega
  have hsplit : 2 * n = (2 * n - 3) + 3 := (Nat.sub_add_cancel h3).symm
  rw [hsplit, pow_add]
  norm_num

/-- Natural-number version of the original coefficient statement, obtained
from a slope theorem with the standard real main term. -/
theorem coefficient_form_nat_of_slope_form {n k : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card K = 2 ^ n)
    (hslope : ∀ ρ ∈ slopes K,
      (slopeTripleCount k ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  have h := coefficient_form_of_slope_form hslope hv₁ hv₂ hne
  rw [card_sq_div_eight_eq_pow hn hcard] at h
  exact_mod_cast h

end KasamiCyclicAdditive
