/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.Kummer
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Binary reduction of the GKP conjecture

Kummer's theorem at `p = 2` identifies the two-adic valuation of a central
binomial coefficient with binary popcount.  Hence every positive non-power of
two already satisfies the divisibility-by-four branch of GKP.
-/

namespace GKPCarry

open Nat

/-- The two-adic valuation of `Nat.centralBinom n` is the binary popcount of
`n`. -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by decide)
  have hkummer :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits
      (p := 2) (k := n) (n := 2 * n) hn
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hkummer
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at hkummer
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp
  · rw [hkummer, Nat.digits_base_mul (by decide : 1 < 2) hnpos]
    simp

/-- Binary popcount at least two forces divisibility by four. -/
theorem four_dvd_centralBinom_of_binary_popcount_ge_two
    {n : ℕ} (hpop : 2 ≤ (Nat.digits 2 n).sum) :
    4 ∣ Nat.centralBinom n := by
  have hval : 2 ≤ padicValNat 2 (Nat.centralBinom n) := by
    simpa [padicValNat_two_centralBinom] using hpop
  have hpow : (2 : ℕ) ^ 2 ∣ Nat.centralBinom n :=
    dvd_trans (pow_dvd_pow 2 hval) pow_padicValNat_dvd
  simpa using hpow

/-- A natural number with binary popcount at most one is zero or a power of
two. -/
theorem popcount_le_one_zero_or_pow_two
    (n : ℕ) (hpop : (Nat.digits 2 n).sum ≤ 1) :
    n = 0 ∨ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact Or.inl rfl
      · have hdigits : Nat.digits 2 n = (n % 2) :: Nat.digits 2 (n / 2) :=
          Nat.digits_def' (by decide) hn
        have hsum : n % 2 + (Nat.digits 2 (n / 2)).sum ≤ 1 := by
          simpa [hdigits] using hpop
        have hmod : n % 2 < 2 := Nat.mod_lt _ (by decide)
        have hdecomp : 2 * (n / 2) + n % 2 = n := by
          have := Nat.div_add_mod n 2
          omega
        interval_cases n % 2
        · rcases Nat.eq_zero_or_pos (n / 2) with hq | hq
          · omega
          · have hlt : n / 2 < n := Nat.div_lt_self hn (by decide)
            have htail : (Nat.digits 2 (n / 2)).sum ≤ 1 := by omega
            rcases ih (n / 2) hlt htail with hzero | ⟨k, hk⟩
            · exact absurd hzero hq.ne'
            · refine Or.inr ⟨k + 1, ?_⟩
              have hn' : n = 2 * (n / 2) := by omega
              rw [hn', hk, pow_succ]
              ring
        · have htail : (Nat.digits 2 (n / 2)).sum = 0 := by omega
          have hquotient : n / 2 = 0 := by
            by_contra hne
            have hdigits_ne : Nat.digits 2 (n / 2) ≠ [] :=
              Nat.digits_ne_nil_iff_ne_zero.mpr hne
            have hlast : 0 < (Nat.digits 2 (n / 2)).getLast hdigits_ne :=
              Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hne)
            have hsum_pos : 0 < (Nat.digits 2 (n / 2)).sum :=
              List.sum_pos_iff_exists_pos_nat.mpr
                ⟨_, List.getLast_mem hdigits_ne, hlast⟩
            omega
          have hn_one : n = 1 := by omega
          exact Or.inr ⟨0, by simp [hn_one]⟩

/-- Every power of two has binary popcount one. -/
theorem popcount_pow_two (k : ℕ) :
    (Nat.digits 2 (2 ^ k)).sum = 1 := by
  have hfactor : (2 : ℕ) ^ k = 2 ^ k * 1 := by ring
  rw [hfactor, Nat.digits_base_pow_mul (by decide : 1 < 2) (by decide : 0 < 1)]
  simp

/-- Every positive non-power of two satisfies the divisibility-by-four branch
of GKP. -/
theorem four_dvd_centralBinom_of_not_power_of_two
    {n : ℕ} (hn : 0 < n) (hnp : ¬ ∃ k : ℕ, n = 2 ^ k) :
    4 ∣ Nat.centralBinom n := by
  apply four_dvd_centralBinom_of_binary_popcount_ge_two
  by_contra hpop
  push Not at hpop
  have hle : (Nat.digits 2 n).sum ≤ 1 := Nat.lt_succ_iff.mp hpop
  rcases popcount_le_one_zero_or_pow_two n hle with hzero | hpower
  · exact hn.ne' hzero
  · exact hnp hpower

/-- The full GKP conjecture follows from its power-of-two restriction. -/
theorem gkpConjecture_of_powerOfTwo (h : gkpPowerOfTwoConjecture) :
    gkpConjecture := by
  intro n hn4 hn64 hn256
  by_cases hp2 : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hp2
    have hk2 : 2 < k := by
      by_contra h
      push Not at h
      have : (2 : ℕ) ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) h
      norm_num at this
      omega
    have hk6 : k ≠ 6 := by
      intro h
      subst k
      norm_num at hn64
    have hk8 : k ≠ 8 := by
      intro h
      subst k
      norm_num at hn256
    exact Or.inr (h k hk2 hk6 hk8)
  · exact Or.inl (four_dvd_centralBinom_of_not_power_of_two (by omega) hp2)

/-- The power-of-two restriction follows from the full GKP conjecture. -/
theorem gkpPowerOfTwoConjecture_of_gkp (h : gkpConjecture) :
    gkpPowerOfTwoConjecture := by
  intro k hk2 hk6 hk8
  have hgt : 4 < (2 : ℕ) ^ k := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ < 2 ^ k := Nat.pow_lt_pow_right (by decide) hk2
  have h64 : (2 : ℕ) ^ k ≠ 64 := by
    intro heq
    apply hk6
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    simpa using heq
  have h256 : (2 : ℕ) ^ k ≠ 256 := by
    intro heq
    apply hk8
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    simpa using heq
  rcases h (2 ^ k) hgt h64 h256 with h4 | h9
  · have hval : padicValNat 2 (Nat.centralBinom (2 ^ k)) = 1 := by
      rw [padicValNat_two_centralBinom, popcount_pow_two]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hge : 2 ≤ padicValNat 2 (Nat.centralBinom (2 ^ k)) := by
      apply (pow_dvd_iff_le_padicValNat
        (by decide : (2 : ℕ) ≠ 1) (Nat.centralBinom_ne_zero _)).mp
      simpa using h4
    omega
  · exact h9

/-- GKP is equivalent to its restriction to powers of two. -/
theorem gkpConjecture_iff_powerOfTwo :
    gkpConjecture ↔ gkpPowerOfTwoConjecture :=
  ⟨gkpPowerOfTwoConjecture_of_gkp, gkpConjecture_of_powerOfTwo⟩

end GKPCarry
