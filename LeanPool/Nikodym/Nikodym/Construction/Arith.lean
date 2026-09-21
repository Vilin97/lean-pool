/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# Exponent arithmetic

Blueprint node M01: real-power bookkeeping used to assemble the final upper bound, and the
supply of `2m` pairwise distinct odd primes indexed as pairs `(ℓⱼ, ℓ'ⱼ)`.
-/

namespace Nikodym

open Real

/-- Blueprint M01: `(1 : ℝ) ≤ 2 ^ m`. -/
theorem two_pow_ge_one (m : ℕ) : (1 : ℝ) ≤ 2 ^ m :=
  one_le_pow₀ one_le_two

/-- Blueprint M01(a): there is `m` with `3h / 2^m ≤ ε/2`. -/
theorem exists_pow_two_ge (h : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, (3 * h : ℝ) / 2 ^ m ≤ ε / 2 := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((3 * h : ℝ) / (ε / 2)) one_lt_two
  refine ⟨m, ?_⟩
  have hε2 : 0 < ε / 2 := half_pos hε
  have h2m : (0 : ℝ) < 2 ^ m := pow_pos two_pos _
  rw [div_le_iff₀ h2m, mul_comm (ε / 2)]
  exact (div_lt_iff₀ hε2 |>.1 hm).le

/-- Blueprint M01(b): `q^{-ε/2} ≤ c` for all real `q` at least some natural `q₁`. -/
theorem exists_rpow_neg_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ q₁ : ℕ, ∀ q : ℝ, (q₁ : ℝ) ≤ q → q ^ (-(ε / 2)) ≤ c := by
  obtain ⟨q₁, hq₁⟩ := exists_nat_ge (max 1 (c⁻¹ ^ (2 / ε)))
  refine ⟨q₁, fun q hq ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := (le_max_left _ _).trans (hq₁.trans hq)
  have hqpos : 0 < q := zero_lt_one.trans_le hq1
  have hε2 : 0 < ε / 2 := half_pos hε
  have hbase : c⁻¹ ^ (2 / ε) ≤ q := (le_max_right 1 _).trans (hq₁.trans hq)
  rw [rpow_neg hqpos.le, inv_le_comm₀ (rpow_pos_of_pos hqpos _) hc]
  calc
    c⁻¹ = (c⁻¹ ^ (2 / ε)) ^ (ε / 2) := by
      rw [← rpow_mul (inv_nonneg.2 hc.le), show (2 / ε) * (ε / 2) = 1 by field_simp, rpow_one]
    _ ≤ q ^ (ε / 2) := rpow_le_rpow (by positivity) hbase hε2.le

/-- Blueprint M01(c): if `1 ≤ q`, `s ≤ ε/2` and `q^{-ε/2} ≤ c`, then
`q^{a-ε} ≤ c · q^{a-s}`. -/
theorem rpow_gap {q c ε a s : ℝ} (hq : 1 ≤ q) (hs : s ≤ ε / 2) (hc : q ^ (-(ε / 2)) ≤ c) :
    q ^ (a - ε) ≤ c * q ^ (a - s) := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  rw [show a - ε = a - s + (s - ε) by ring, rpow_add hqpos, mul_comm (q ^ (a - s))]
  refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hqpos.le _)
  calc
    q ^ (s - ε) ≤ q ^ (-(ε / 2)) := rpow_le_rpow_of_exponent_le hq (by linarith)
    _ ≤ c := hc

/-- Blueprint M01(c), specialised to the construction exponents: if `3h/n ≤ ε/2` and
`q^{-ε/2} ≤ c` with `1 ≤ q`, then `c · q^{h - 2^{1-h} - 3h/n} ≥ q^{h - 2^{1-h} - ε}`. -/
theorem rpow_gap_construction {q c ε : ℝ} {h n : ℕ} (hq : 1 ≤ q)
    (hs : (3 * h : ℝ) / n ≤ ε / 2) (hc : q ^ (-(ε / 2)) ≤ c) :
    c * q ^ ((h : ℝ) - 2 ^ (1 - (h : ℝ)) - (3 * h : ℝ) / n) ≥
      q ^ ((h : ℝ) - 2 ^ (1 - (h : ℝ)) - ε) :=
  (rpow_gap hq hs hc).ge

/-- Blueprint M01: the `n`th prime is odd for `n ≥ 1` (index `0` is `2`). -/
theorem odd_nth_prime {n : ℕ} (hn : 0 < n) : Odd (Nat.nth Nat.Prime n) := by
  refine (Nat.prime_nth_prime n).odd_of_ne_two ?_
  intro h
  have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime n :=
    (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).2 hn
  rw [Nat.nth_prime_zero_eq_two, h] at hlt
  exact (lt_irrefl _ hlt).elim

/-- Blueprint M01(d): `2m` pairwise distinct odd primes, indexed as pairs `(ℓⱼ, ℓ'ⱼ)`. -/
theorem exists_distinct_odd_primes (m : ℕ) :
    ∃ ℓ ℓ' : Fin m → ℕ,
      (∀ j, (ℓ j).Prime ∧ Odd (ℓ j)) ∧ (∀ j, (ℓ' j).Prime ∧ Odd (ℓ' j)) ∧
        (∀ j, ℓ j ≠ ℓ' j) ∧
          (∀ j k, j ≠ k → ℓ j ≠ ℓ k ∧ ℓ j ≠ ℓ' k ∧ ℓ' j ≠ ℓ' k) := by
  let ℓ : Fin m → ℕ := fun j ↦ Nat.nth Nat.Prime (2 * (j : ℕ) + 1)
  let ℓ' : Fin m → ℕ := fun j ↦ Nat.nth Nat.Prime (2 * (j : ℕ) + 2)
  refine ⟨ℓ, ℓ', ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨Nat.prime_nth_prime _, odd_nth_prime (Nat.succ_pos _)⟩
  · intro j
    exact ⟨Nat.prime_nth_prime _, odd_nth_prime (by omega)⟩
  · intro j
    exact (Nat.nth_injective Nat.infinite_setOfPred_prime).ne (by omega)
  · intro j k hjk
    have hjk' : (j : ℕ) ≠ k := fun h ↦ hjk (Fin.ext h)
    exact ⟨(Nat.nth_injective Nat.infinite_setOfPred_prime).ne (by omega),
      (Nat.nth_injective Nat.infinite_setOfPred_prime).ne (by omega),
      (Nat.nth_injective Nat.infinite_setOfPred_prime).ne (by omega)⟩

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
