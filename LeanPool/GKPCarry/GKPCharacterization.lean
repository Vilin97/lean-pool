/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.BadCarryLanguage

/-!
# A regular-language characterization of the GKP conjecture

For every `n`, the deficient-carry automaton on the canonical ternary digits of
`n` accepts exactly when `9` does not divide `Nat.centralBinom n`.  Combining
this exact local characterization with the binary reduction yields an
equivalence between the Graham--Knuth--Patashnik conjecture and avoidance of an
explicit regular language by nonexceptional powers of two.

This equivalence is a reduction of the open conjecture, not a proof of it.
-/

namespace GKPCarry

open Nat

/-- Divisibility by nine is exactly the condition that ternary doubling creates
at least two carries. -/
theorem nine_dvd_centralBinom_iff_two_le_ternaryDoubleCarryCount (n : ℕ) :
    9 ∣ Nat.centralBinom n ↔
      2 ≤ ternaryDoubleCarryCount (Nat.digits 3 n) := by
  constructor
  · intro hdiv
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hval : 2 ≤ padicValNat 3 (Nat.centralBinom n) := by
      apply (pow_dvd_iff_le_padicValNat
        (by decide : (3 : ℕ) ≠ 1) (Nat.centralBinom_ne_zero n)).mp
      simpa using hdiv
    have hidentity :
        2 * padicValNat 3 (Nat.centralBinom n) =
          2 * ternaryDoubleCarryCount (Nat.digits 3 n) := by
      calc
        2 * padicValNat 3 (Nat.centralBinom n) = ternaryDigitExcess n := by
          simpa [ternaryDigitExcess] using
            two_mul_padicValNat_three_centralBinom n
        _ = 2 * ternaryDoubleCarryCount (Nat.digits 3 n) :=
          ternaryDigitExcess_eq_two_mul_ternaryDoubleCarryCount n
    omega
  · exact nine_dvd_centralBinom_of_two_le_ternaryDoubleCarryCount

/-- The automaton accepts the canonical ternary expansion of `n` exactly when
`9` does not divide its central binomial coefficient. -/
theorem badCarryLanguage_digits_true_iff_not_nine_dvd (n : ℕ) :
    badCarryLanguage (Nat.digits 3 n) = true ↔
      ¬ 9 ∣ Nat.centralBinom n := by
  rw [badCarryLanguage_true_iff_carryCount_lt_two
    (fun digit hdigit => Nat.digits_lt_base (by decide) hdigit)]
  rw [nine_dvd_centralBinom_iff_two_le_ternaryDoubleCarryCount]
  omega

/-- The remaining language-avoidance statement for nonexceptional powers of
two.  This proposition is open. -/
def gkpBadCarryLanguageExclusion : Prop :=
  ∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 →
    badCarryLanguage (Nat.digits 3 (2 ^ k)) = false

/-- The language-avoidance statement is equivalent to excluding each of the
three concrete deficient-carry shapes. -/
theorem gkpBadCarryLanguageExclusion_iff_shape_exclusions :
    gkpBadCarryLanguageExclusion ↔
      (∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 →
        ¬ badCarryAllZeroOrOne (Nat.digits 3 (2 ^ k))) ∧
      (∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 →
        ¬ badCarryExactlyOneTopTwo (Nat.digits 3 (2 ^ k))) ∧
      (∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 →
        ¬ badCarryExactlyOneTwoFollowedByZero
          (Nat.digits 3 (2 ^ k))) := by
  constructor
  · intro hexclude
    refine ⟨?_, ?_, ?_⟩
    · intro k hk2 hk6 hk8 hshape
      have hbad := (badCarryLanguage_true_iff_shape _).mpr (Or.inl hshape)
      rw [hexclude k hk2 hk6 hk8] at hbad
      contradiction
    · intro k hk2 hk6 hk8 hshape
      have hbad :=
        (badCarryLanguage_true_iff_shape _).mpr (Or.inr (Or.inl hshape))
      rw [hexclude k hk2 hk6 hk8] at hbad
      contradiction
    · intro k hk2 hk6 hk8 hshape
      have hbad :=
        (badCarryLanguage_true_iff_shape _).mpr (Or.inr (Or.inr hshape))
      rw [hexclude k hk2 hk6 hk8] at hbad
      contradiction
  · rintro ⟨hzero, htop, hfollow⟩ k hk2 hk6 hk8
    cases hbad : badCarryLanguage (Nat.digits 3 (2 ^ k)) with
    | false => rfl
    | true =>
        rcases (badCarryLanguage_true_iff_shape _).mp hbad with
          hshape | hshape | hshape
        · exact False.elim ((hzero k hk2 hk6 hk8) hshape)
        · exact False.elim ((htop k hk2 hk6 hk8) hshape)
        · exact False.elim ((hfollow k hk2 hk6 hk8) hshape)

/-- GKP implies avoidance of the deficient-carry language. -/
theorem gkpBadCarryLanguageExclusion_of_gkp
    (h : gkpConjecture) :
    gkpBadCarryLanguageExclusion := by
  intro k hk2 hk6 hk8
  have hdiv : 9 ∣ Nat.centralBinom (2 ^ k) :=
    gkpPowerOfTwoConjecture_of_gkp h k hk2 hk6 hk8
  cases hbad : badCarryLanguage (Nat.digits 3 (2 ^ k)) with
  | false => rfl
  | true =>
      exact False.elim
        ((badCarryLanguage_digits_true_iff_not_nine_dvd (2 ^ k)).mp hbad hdiv)

/-- Avoidance of the deficient-carry language implies GKP. -/
theorem gkpConjecture_of_badCarryLanguageExclusion
    (h : gkpBadCarryLanguageExclusion) :
    gkpConjecture := by
  apply gkpConjecture_of_ternaryCarryCount
  intro k hk2 hk6 hk8
  have hfalse := h k hk2 hk6 hk8
  have hvalid : ∀ digit ∈ Nat.digits 3 (2 ^ k), digit < 3 :=
    fun digit hdigit => Nat.digits_lt_base (by decide) hdigit
  by_contra hcarry
  have hlt : ternaryDoubleCarryCount (Nat.digits 3 (2 ^ k)) < 2 := by
    omega
  have htrue :=
    (badCarryLanguage_true_iff_carryCount_lt_two hvalid).mpr hlt
  rw [hfalse] at htrue
  contradiction

/-- Headline theorem: the GKP conjecture is equivalent to avoidance of the
explicit deficient-carry regular language by nonexceptional powers of two. -/
theorem gkpConjecture_iff_badCarryLanguageExclusion :
    gkpConjecture ↔ gkpBadCarryLanguageExclusion :=
  ⟨gkpBadCarryLanguageExclusion_of_gkp,
    gkpConjecture_of_badCarryLanguageExclusion⟩

/-- The GKP exclusion would imply the tail of Erdős Problem 406: powers of two
above `2 ^ 8` cannot have ternary expansions using only `0` and `1`. -/
theorem erdos406_tail_of_gkpBadCarryLanguageExclusion
    (h : gkpBadCarryLanguageExclusion) :
    ∀ k : ℕ, 8 < k →
      ¬ badCarryAllZeroOrOne (Nat.digits 3 (2 ^ k)) := by
  intro k hk
  exact (gkpBadCarryLanguageExclusion_iff_shape_exclusions.mp h).1
    k (by omega) (by omega) (by omega)

end GKPCarry
