/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
/-!
# Gauss reciprocity and its supplementary laws

This file proves Gauss reciprocity and its supplementary laws. Mathlib's Jacobi symbol has a
  natural-number
denominator, so an integer denominator `b` is written canonically as
`jacobiSym a b.natAbs`, as is forced by the principal ideal `(b)`.
-/

@[expose] public section

open scoped NumberTheorySymbols

namespace AlgebraicNumberTheory
namespace PowerResidueSymbols

/-- Positive form of Gauss reciprocity for arbitrary coprime odd natural
numbers (not only primes). -/
theorem gaussReciprocity_nat
    {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab : a.Coprime b) :
    J((a : ℤ) | b) * J((b : ℤ) | a) =
      (-1 : ℤ) ^ (a / 2 * (b / 2)) := by
  rw [jacobiSym.quadratic_reciprocity ha hb, mul_assoc]
  have hsq : J((b : ℤ) | a) ^ 2 = 1 := by
    apply jacobiSym.sq_one
    simpa [Int.gcd_eq_natAbs] using hab.symm.gcd_eq_one
  rw [← pow_two, hsq, mul_one]

/-- **Gauss reciprocity.**  This signed formulation
applies to all odd, relatively prime integers. -/
theorem gaussReciprocity
    {a b : ℤ} (ha : Odd a) (hb : Odd b)
    (hab : a.natAbs.Coprime b.natAbs) :
    J(a | b.natAbs) * J(b | a.natAbs) =
      (-1 : ℤ) ^
        (a.natAbs / 2 * (b.natAbs / 2) +
          (if a < 0 then b.natAbs / 2 else 0) +
          (if b < 0 then a.natAbs / 2 else 0)) := by
  have ha' : Odd a.natAbs := ha.natAbs
  have hb' : Odd b.natAbs := hb.natAbs
  have hpos :=
    gaussReciprocity_nat ha' hb' hab
  have hchiA :
      ZMod.χ₄ a.natAbs = (-1 : ℤ) ^ (a.natAbs / 2) :=
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp ha')
  have hchiB :
      ZMod.χ₄ b.natAbs = (-1 : ℤ) ^ (b.natAbs / 2) :=
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hb')
  by_cases hna : a < 0
  · have ha_cast : a = -(a.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_neg hna, neg_neg]
    by_cases hnb : b < 0
    · have hb_cast : b = -(b.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_neg hnb, neg_neg]
      rw [ite_eq_left hna, ite_eq_left hnb]
      rw [ha_cast, hb_cast]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      rw [jacobiSym.neg _ hb', jacobiSym.neg _ ha', hchiA, hchiB]
      calc
        ((-1 : ℤ) ^ (b.natAbs / 2) *
              J((a.natAbs : ℤ) | b.natAbs)) *
            ((-1 : ℤ) ^ (a.natAbs / 2) *
              J((b.natAbs : ℤ) | a.natAbs)) =
            ((-1 : ℤ) ^ (a.natAbs / 2 * (b.natAbs / 2))) *
              ((-1 : ℤ) ^ (b.natAbs / 2)) *
              ((-1 : ℤ) ^ (a.natAbs / 2)) := by
                rw [← hpos]
                ring
        _ = (-1 : ℤ) ^
              (a.natAbs / 2 * (b.natAbs / 2) +
                b.natAbs / 2 + a.natAbs / 2) := by
              rw [pow_add, pow_add]
    · have hb_nonneg : 0 ≤ b := le_of_not_gt hnb
      have hb_cast : (b.natAbs : ℤ) = b :=
        Int.natAbs_of_nonneg hb_nonneg
      rw [ite_eq_left hna, ite_eq_right hnb]
      rw [ha_cast, ← hb_cast]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      rw [jacobiSym.neg _ hb', hchiB]
      calc
        ((-1 : ℤ) ^ (b.natAbs / 2) *
              J((a.natAbs : ℤ) | b.natAbs)) *
            J((b.natAbs : ℤ) | a.natAbs) =
            ((-1 : ℤ) ^ (b.natAbs / 2)) *
              ((-1 : ℤ) ^
                (a.natAbs / 2 * (b.natAbs / 2))) := by
              rw [mul_assoc, hpos]
        _ = (-1 : ℤ) ^
              (a.natAbs / 2 * (b.natAbs / 2) +
                b.natAbs / 2 + 0) := by
              rw [add_zero, pow_add, mul_comm]
  · have ha_nonneg : 0 ≤ a := le_of_not_gt hna
    have ha_cast : (a.natAbs : ℤ) = a :=
      Int.natAbs_of_nonneg ha_nonneg
    by_cases hnb : b < 0
    · have hb_cast : b = -(b.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_neg hnb, neg_neg]
      rw [ite_eq_right hna, ite_eq_left hnb]
      rw [← ha_cast, hb_cast]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      rw [jacobiSym.neg _ ha', hchiA]
      calc
        J((a.natAbs : ℤ) | b.natAbs) *
            ((-1 : ℤ) ^ (a.natAbs / 2) *
              J((b.natAbs : ℤ) | a.natAbs)) =
            ((-1 : ℤ) ^
                (a.natAbs / 2 * (b.natAbs / 2))) *
              ((-1 : ℤ) ^ (a.natAbs / 2)) := by
              rw [← hpos]
              ring
        _ = (-1 : ℤ) ^
              (a.natAbs / 2 * (b.natAbs / 2) + 0 +
                a.natAbs / 2) := by
              rw [add_zero, pow_add]
    · have hb_nonneg : 0 ≤ b := le_of_not_gt hnb
      have hb_cast : (b.natAbs : ℤ) = b :=
        Int.natAbs_of_nonneg hb_nonneg
      rw [ite_eq_right hna, ite_eq_right hnb]
      rw [← ha_cast, ← hb_cast]
      simp only [Int.natAbs_natCast, add_zero]
      exact hpos

/-- The first supplementary law, expressed by its parity exponent. -/
theorem gaussSupplement_neg_one
    {b : ℕ} (hb : Odd b) :
    J((-1 : ℤ) | b) = (-1 : ℤ) ^ ((b - 1) / 2) := by
  rw [jacobiSym.at_neg_one hb,
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hb)]
  congr 1
  obtain ⟨k, rfl⟩ := hb
  omega

/-- The second supplementary law in residue-class form. -/
theorem gaussSupplement_two
    {b : ℕ} (hb : Odd b) :
    J((2 : ℤ) | b) =
      if b % 8 = 1 ∨ b % 8 = 7 then 1 else -1 := by
  have hbne : b % 2 ≠ 0 := by
    rw [Nat.odd_iff.mp hb]
    decide
  rw [jacobiSym.at_two hb, ZMod.χ₈_nat_eq_if_mod_eight,
    ite_eq_right hbne]

/-- For odd `b`, the mod-eight sign is the classical exponent
`(-1)^((b²-1)/8)`. -/
theorem twoSupplementSign_eq_neg_one_pow
    {b : ℕ} (hb : Odd b) :
    (if b % 8 = 1 ∨ b % 8 = 7 then (1 : ℤ) else -1) =
      (-1 : ℤ) ^ ((b ^ 2 - 1) / 8) := by
  have hbmod : b % 2 = 1 := Nat.odd_iff.mp hb
  have hresidue :
      b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
    have hlt : b % 8 < 8 := Nat.mod_lt b (by decide)
    have hparity : (b % 8) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd b (by decide : 2 ∣ 8)]
      exact hbmod
    omega
  rcases hresidue with h1 | h3 | h5 | h7
  · let q := b / 8
    have hbq : b = 8 * q + 1 := by
      dsimp [q]
      have hdiv := Nat.mod_add_div b 8
      omega
    have hsquare :
        (8 * q + 1) ^ 2 =
          8 * (8 * q ^ 2 + 2 * q) + 1 := by
      ring
    have hexponent :
        (b ^ 2 - 1) / 8 = 8 * q ^ 2 + 2 * q := by
      rw [hbq, hsquare, Nat.add_sub_cancel, Nat.mul_div_right]
      decide
    have heven : Even (8 * q ^ 2 + 2 * q) := by
      refine ⟨4 * q ^ 2 + q, ?_⟩
      ring
    rw [ite_eq_left (Or.inl h1), hexponent, heven.neg_one_pow]
  · let q := b / 8
    have hbq : b = 8 * q + 3 := by
      dsimp [q]
      have hdiv := Nat.mod_add_div b 8
      omega
    have hsquare :
        (8 * q + 3) ^ 2 =
          8 * (8 * q ^ 2 + 6 * q + 1) + 1 := by
      ring
    have hexponent :
        (b ^ 2 - 1) / 8 = 8 * q ^ 2 + 6 * q + 1 := by
      rw [hbq, hsquare, Nat.add_sub_cancel, Nat.mul_div_right]
      decide
    have hodd : Odd (8 * q ^ 2 + 6 * q + 1) := by
      refine ⟨4 * q ^ 2 + 3 * q, ?_⟩
      ring
    rw [ite_eq_right, hexponent, hodd.neg_one_pow]
    omega
  · let q := b / 8
    have hbq : b = 8 * q + 5 := by
      dsimp [q]
      have hdiv := Nat.mod_add_div b 8
      omega
    have hsquare :
        (8 * q + 5) ^ 2 =
          8 * (8 * q ^ 2 + 10 * q + 3) + 1 := by
      ring
    have hexponent :
        (b ^ 2 - 1) / 8 = 8 * q ^ 2 + 10 * q + 3 := by
      rw [hbq, hsquare, Nat.add_sub_cancel, Nat.mul_div_right]
      decide
    have hodd : Odd (8 * q ^ 2 + 10 * q + 3) := by
      refine ⟨4 * q ^ 2 + 5 * q + 1, ?_⟩
      ring
    rw [ite_eq_right, hexponent, hodd.neg_one_pow]
    omega
  · let q := b / 8
    have hbq : b = 8 * q + 7 := by
      dsimp [q]
      have hdiv := Nat.mod_add_div b 8
      omega
    have hsquare :
        (8 * q + 7) ^ 2 =
          8 * (8 * q ^ 2 + 14 * q + 6) + 1 := by
      ring
    have hexponent :
        (b ^ 2 - 1) / 8 = 8 * q ^ 2 + 14 * q + 6 := by
      rw [hbq, hsquare, Nat.add_sub_cancel, Nat.mul_div_right]
      decide
    have heven : Even (8 * q ^ 2 + 14 * q + 6) := by
      refine ⟨4 * q ^ 2 + 7 * q + 3, ?_⟩
      ring
    rw [ite_eq_left (Or.inr h7), hexponent, heven.neg_one_pow]

/-- The second supplementary law, expressed by its parity exponent. -/
theorem gaussSupplement_two_pow
    {b : ℕ} (hb : Odd b) :
    J((2 : ℤ) | b) = (-1 : ℤ) ^ ((b ^ 2 - 1) / 8) := by
  rw [gaussSupplement_two hb, twoSupplementSign_eq_neg_one_pow hb]

end PowerResidueSymbols
end AlgebraicNumberTheory
