/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.GKPCharacterization
import LeanPool.GKPCarry.ModularPrefix
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
# Infinite periodic slices of the GKP carry condition

The first three ternary digits of `2 ^ k` are periodic in `k` modulo `18`.
Exactly nine of those eighteen exponent classes already create at least two
doubling carries in that three-digit prefix. Consequently, every exponent in
those classes satisfies the divisibility-by-nine branch of the GKP conjecture.

This is an infinite scoped result. The other nine residue classes are not
settled here, and the universal GKP conjecture remains open.
-/

namespace GKPCarry

open Nat

/-! ## Modular carry certificates -/

lemma ternaryDoubleCarryCountAux_append_le
    (prefixDigits suffix : List ℕ) (carry : ℕ) :
    ternaryDoubleCarryCountAux prefixDigits carry ≤
      ternaryDoubleCarryCountAux (prefixDigits ++ suffix) carry := by
  induction prefixDigits generalizing carry with
  | nil => simp [ternaryDoubleCarryCountAux]
  | cons digit digits ih =>
      simp only [List.cons_append, ternaryDoubleCarryCountAux]
      exact Nat.add_le_add_left
        (ih (ternaryDoubleCarryStep carry digit)) _

/-- The carry count of a canonical ternary residue modulo `3 ^ depth` is a
lower bound for the carry count of the whole number. -/
theorem ternaryDoubleCarryCount_mod_pow_le (depth n : ℕ) :
    ternaryDoubleCarryCount (Nat.digits 3 (n % 3 ^ depth)) ≤
      ternaryDoubleCarryCount (Nat.digits 3 n) := by
  classical
  set residue := n % 3 ^ depth with hresidue
  set quotient := n / 3 ^ depth with hquotient
  have hpow : 0 < (3 : ℕ) ^ depth := by positivity
  have hresidue_lt : residue < 3 ^ depth := Nat.mod_lt _ hpow
  have hlength : (Nat.digits 3 residue).length ≤ depth :=
    (Nat.digits_length_le_iff (b := 3) (by decide) residue).mpr hresidue_lt
  have hsplit : n = residue + 3 ^ depth * quotient := by
    rw [hresidue, hquotient]
    exact (Nat.mod_add_div n (3 ^ depth)).symm
  by_cases hquotient_zero : quotient = 0
  · have hn : n = residue := by
      rw [hsplit, hquotient_zero]
      ring_nf
    rw [hn]
  · have hquotient_pos : 0 < quotient := Nat.pos_of_ne_zero hquotient_zero
    have hdecomp :
        Nat.digits 3 n =
          Nat.digits 3 residue ++
            List.replicate (depth - (Nat.digits 3 residue).length) 0 ++
              Nat.digits 3 quotient := by
      have hfill :
          (Nat.digits 3 residue).length +
              (depth - (Nat.digits 3 residue).length) = depth := by
        omega
      have hdigits := Nat.digits_append_zeroes_append_digits
        (b := 3) (k := depth - (Nat.digits 3 residue).length)
        (m := quotient) (n := residue) (by decide) hquotient_pos
      rw [hfill] at hdigits
      rw [hdigits, hsplit]
    unfold ternaryDoubleCarryCount
    rw [hdecomp]
    simpa [List.append_assoc] using
      (ternaryDoubleCarryCountAux_append_le
        (Nat.digits 3 residue)
        (List.replicate (depth - (Nat.digits 3 residue).length) 0 ++
          Nat.digits 3 quotient) 0)

/-- Any finite modular prefix with two carries certifies divisibility by nine
for the full central binomial coefficient. -/
theorem nine_dvd_centralBinom_of_modular_carry_certificate
    {depth n : ℕ}
    (hcarry :
      2 ≤ ternaryDoubleCarryCount (Nat.digits 3 (n % 3 ^ depth))) :
    9 ∣ Nat.centralBinom n := by
  apply nine_dvd_centralBinom_of_two_le_ternaryDoubleCarryCount
  exact le_trans hcarry (ternaryDoubleCarryCount_mod_pow_le depth n)

/-! ## The period modulo `27` -/

/-- The exponent period used for the three-digit ternary prefix. -/
lemma two_pow_eighteen_mod_twentySeven : (2 : ℕ) ^ 18 % 27 = 1 := by
  decide

/-- The residue of `2 ^ k` modulo `27` depends only on `k % 18`. -/
theorem two_pow_mod_twentySeven_eq_reduced_exponent (k : ℕ) :
    (2 : ℕ) ^ k % 27 = 2 ^ (k % 18) % 27 := by
  have hk : k = 18 * (k / 18) + k % 18 := by omega
  calc
    (2 : ℕ) ^ k % 27 = 2 ^ (18 * (k / 18) + k % 18) % 27 := by
      exact congrArg (fun exponent : ℕ => 2 ^ exponent % 27) hk
    _ = ((2 ^ 18) ^ (k / 18) * 2 ^ (k % 18)) % 27 := by
      rw [pow_add, pow_mul]
    _ = 2 ^ (k % 18) % 27 := by
      conv_lhs =>
        rw [Nat.mul_mod, Nat.pow_mod, two_pow_eighteen_mod_twentySeven]
      simp

/-! ## Exact three-digit sieve -/

/-- Exponent classes whose first three ternary digits already create at least
two doubling carries. -/
def gkpSafeExponentResiduesMod18 : Finset ℕ :=
  {3, 4, 5, 7, 9, 10, 11, 15, 17}

/-- Exactly half of the exponent classes modulo `18` pass the three-digit
carry sieve. -/
theorem card_gkpSafeExponentResiduesMod18 :
    gkpSafeExponentResiduesMod18.card = 9 := by
  decide

/-- Exact classification of the exponent classes whose residue modulo `27`
already displays two ternary doubling carries. -/
theorem lowThreeCarryCertificate_iff (k : ℕ) :
    2 ≤ ternaryDoubleCarryCount (Nat.digits 3 (2 ^ k % 27)) ↔
      k % 18 ∈ gkpSafeExponentResiduesMod18 := by
  rw [two_pow_mod_twentySeven_eq_reduced_exponent]
  have hremainder : k % 18 < 18 := Nat.mod_lt _ (by norm_num)
  interval_cases hcase : k % 18 <;>
    norm_num [hcase, gkpSafeExponentResiduesMod18,
      ternaryDoubleCarryCount, ternaryDoubleCarryCountAux,
      ternaryDoubleCarryStep]

/-- **Infinite periodic GKP slice.** If `k` lies in one of nine explicit
classes modulo `18`, then the central binomial coefficient indexed by `2 ^ k`
is divisible by `9`. -/
theorem nine_dvd_centralBinom_two_pow_of_safe_mod_eighteen
    {k : ℕ} (hk : k % 18 ∈ gkpSafeExponentResiduesMod18) :
    9 ∣ Nat.centralBinom (2 ^ k) := by
  apply nine_dvd_centralBinom_of_modular_carry_certificate (depth := 3)
  norm_num only [pow_succ, pow_zero]
  exact (lowThreeCarryCertificate_iff k).mpr hk

/-- On the same nine infinite classes, powers of two avoid the deficient-carry
language used in the exact GKP characterization. -/
theorem badCarryLanguage_two_pow_eq_false_of_safe_mod_eighteen
    {k : ℕ} (hk : k % 18 ∈ gkpSafeExponentResiduesMod18) :
    badCarryLanguage (Nat.digits 3 (2 ^ k)) = false := by
  have hdiv := nine_dvd_centralBinom_two_pow_of_safe_mod_eighteen hk
  cases hbad : badCarryLanguage (Nat.digits 3 (2 ^ k)) with
  | false => rfl
  | true =>
      exact False.elim
        ((badCarryLanguage_digits_true_iff_not_nine_dvd (2 ^ k)).mp hbad hdiv)

end GKPCarry
