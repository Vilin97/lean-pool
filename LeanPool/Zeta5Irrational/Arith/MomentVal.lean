/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.Val
public import LeanPool.Zeta5Irrational.Construction
import LeanPool.Zeta5Irrational.Arith.DirectPoly
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Valuations of the polynomial moments

`μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5)/24` has `v_p ≥ -1` (`p ≥ 5`), and is `p`-integral
for `e < 2p - 3` (von Staudt–Clausen).
-/

public section

open Finset

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

lemma VG_bernoulli_even (k : ℕ) : VG p (_root_.bernoulli (2 * k)) (-1) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have e :
    _root_.bernoulli (2 * k) =
      (z : ℚ) - ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q :=
    by rw [hz]; ring
  rw [e]
  refine ((VG.intCast (p := p) z).mono (by norm_num)).sub (VG.sum _ fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.2.1.ne_zero
  rw [one_div]
  refine VG.inv hq0 ?_
  rw [padicValRat.of_nat]
  have : padicValNat p q ≤ 1 := by
    by_cases hpq : p = q
    · subst hpq; rw [padicValNat_self]
    · have := Fact.mk hq.2.1
      rw [padicValNat_primes hpq]; omega
  exact_mod_cast this

lemma VG_bernoulli_even_int (k : ℕ) (hk : ¬(p - 1) ∣ 2 * k) : VG p (_root_.bernoulli (2 * k)) 0 :=
  by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have e :
    _root_.bernoulli (2 * k) =
      (z : ℚ) - ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q :=
    by rw [hz]; ring
  rw [e]
  refine (VG.intCast (p := p) z).sub (VG.sum _ fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.2.1.ne_zero
  have hpq : p ≠ q := fun h => hk (h ▸ hq.2.2)
  rw [one_div]
  refine (VG.inv (r := 0) hq0 ?_).mono (by norm_num)
  have := Fact.mk hq.2.1
  rw [padicValRat.of_nat, padicValNat_primes hpq]; simp

lemma VG_inv24 (hp5 : 5 ≤ p) : VG p ((24 : ℚ)⁻¹) 0 := by
  refine (VG.inv (r := 0) (by norm_num) ?_).mono (by norm_num)
  rw [show (24 : ℚ) = ((24 : ℕ) : ℚ) by norm_num, padicValRat.of_nat, padicValNat_24 hp5]; simp

/-- `v_p(μ(t^e)) ≥ -1`. -/
theorem VG_μmono (hp5 : 5 ≤ p) (e : ℕ) : VG p (μmono e) (-1) := by
  unfold μmono
  rw [show 2 * e + 2 = 2 * (e + 1) by ring, div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ e) 0 := by
    rcases neg_one_pow_eq_or ℚ e with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  have h3 : VG p (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ) 0 := VG.natCast _
  have := ((h1.mul (VG_bernoulli_even (e + 1))).mul h3).mul (VG_inv24 hp5)
  push_cast at this
  simpa using this

/-- `μ(t^e)` is `p`-integral for `e < 2p - 3`. -/
theorem VG_μmono_int (hp5 : 5 ≤ p) {e : ℕ} (he : e + 3 < 2 * p) : VG p (μmono e) 0 := by
  unfold μmono
  rw [show 2 * e + 2 = 2 * (e + 1) by ring, div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ e) 0 := by
    rcases neg_one_pow_eq_or ℚ e with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  by_cases hd : (p - 1) ∣ 2 * (e + 1)
  · -- `2e + 2 = j (p - 1)` with `j ∈ {1, 2, 3}`
    obtain ⟨j, hj⟩ := hd
    have hp1 : 1 ≤ p - 1 := by omega
    have hj3 : j ≤ 3 := by
      by_contra h; rw [not_le] at h
      have : (p - 1) * 4 ≤ (p - 1) * j := Nat.mul_le_mul_left _ h
      omega
    have hj0 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, mul_zero] at hj; omega
      · exact h
    have hprod : VG p (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ) 1 := by
      apply VG.of_eq
      intro hne
      rw [padicValRat.of_nat]
      have hdvd : p ∣ (2 * e + 3) * (2 * e + 4) * (2 * e + 5) := by
        interval_cases j
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ⟨1, by omega⟩ _) _
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨2, by omega⟩ _) _
        · exact Dvd.dvd.mul_left ⟨3, by omega⟩ _
      have hne' : (2 * e + 3) * (2 * e + 4) * (2 * e + 5) ≠ 0 := by positivity
      have := one_le_padicValNat_of_dvd hne' hdvd
      exact_mod_cast this
    have := ((h1.mul (VG_bernoulli_even (e + 1))).mul hprod).mul (VG_inv24 hp5)
    push_cast at this
    simpa using this
  · have h3 : VG p (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ) 0 := VG.natCast _
    have := ((h1.mul (VG_bernoulli_even_int (e + 1) hd)).mul h3).mul (VG_inv24 hp5)
    push_cast at this
    simpa using this

end Zeta5Irrational
