/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Assembly.ElementaryInputs
import LeanPool.KasamiCyclicAdditive.Statement.CoefficientForm

/-!
# Reduction glue

This module knows nothing about the proof of normalization.  It states the
exact interface normalization must provide and shows that, once the normalized
slope theorem is available, the original coefficient-form conjecture follows.

It also bridges the normalization coprimality `gcd(m, 2^n-1) = 1` to the exact
modulus `|Kˣ|` used by the phase argument, and constructs the inverse exponent
`D`.
-/

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- In a finite field of cardinality `2^n`, the unit group has cardinality
`2^n-1`. -/
theorem card_units_eq_two_pow_sub_one {n : ℕ}
    (hcard : Fintype.card K = 2 ^ n) :
    Fintype.card Kˣ = 2 ^ n - 1 := by
  rw [Fintype.card_units, hcard]

/-- Inverse exponent `D` with `m * D ≡ 1` modulo the exact order `|Kˣ|`. -/
theorem exists_inverse_exponent_units {n m : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card K = 2 ^ n)
    (hcop : Nat.Coprime m (2 ^ n - 1)) :
    ∃ D : ℕ, D ≠ 0 ∧ m * D ≡ 1 [MOD Fintype.card Kˣ] := by
  have hN : 1 < 2 ^ n - 1 := by
    have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  obtain ⟨D, hD, hmod⟩ := exists_inverse_exponent hcop hN
  refine ⟨D, hD, ?_⟩
  rw [card_units_eq_two_pow_sub_one hcard]
  exact hmod


/-- Coefficient form at `(k, v₁, v₂)` from the normalized slope formula at
`k0`, given a witness identifying the two triple counts. -/
theorem coefficient_form_of_normalized_witness {n k k0 : ℕ}
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    (hslope : ∀ ρ ∈ slopes K,
      (slopeTripleCount k0 ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8)
    {v₁ v₂ w1 w2 : K}
    (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (hwne : w1 ≠ w2)
    (hcount : coefficientTripleCount k v₁ v₂ = coefficientTripleCount k0 w1 w2) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  rw [hcount]
  exact coefficient_form_nat_of_slope_form hn hcard hslope hw1 hw2 hwne

end KasamiCyclicAdditive
