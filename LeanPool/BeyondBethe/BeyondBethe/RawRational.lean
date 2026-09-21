/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.BinaryLongDivision
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! # Raw Rational -/

namespace BeyondBethe

/-!
# Unreduced rational arithmetic

The machine implementation carries signed numerators and positive
denominators without reducing after every field operation.  This avoids hiding
a gcd call inside each use of Lean's canonical `Rat` arithmetic.  Reduction is
performed explicitly by `binaryNormalizeRawRat` using the verified division
and Euclid recurrences.
-/

/-- A signed fraction with a strictly positive, not necessarily reduced,
denominator. -/
structure RawRat where
  num : ℤ
  den : ℕ
  den_pos : 0 < den
deriving DecidableEq

namespace RawRat

def zero : RawRat := ⟨0, 1, by omega⟩

def one : RawRat := ⟨1, 1, by omega⟩

/-- Mathematical value of an unreduced fraction. -/
def value (q : RawRat) : ℚ := (q.num : ℚ) / (q.den : ℚ)

def neg (q : RawRat) : RawRat := ⟨-q.num, q.den, q.den_pos⟩

def add (q r : RawRat) : RawRat :=
  ⟨q.num * r.den + r.num * q.den, q.den * r.den,
    Nat.mul_pos q.den_pos r.den_pos⟩

def sub (q r : RawRat) : RawRat := add q (neg r)

def mul (q r : RawRat) : RawRat :=
  ⟨q.num * r.num, q.den * r.den, Nat.mul_pos q.den_pos r.den_pos⟩

@[simp] theorem value_zero : zero.value = 0 := by
  norm_num [zero, value]

@[simp] theorem value_one : one.value = 1 := by
  norm_num [one, value]

@[simp] theorem value_neg (q : RawRat) : q.neg.value = -q.value := by
  rw [neg, value, value]
  push_cast
  ring

@[simp] theorem value_add (q r : RawRat) : (q.add r).value = q.value + r.value := by
  rw [add, value, value, value]
  push_cast
  field_simp [Nat.ne_of_gt q.den_pos, Nat.ne_of_gt r.den_pos]
  <;> ring

@[simp] theorem value_sub (q r : RawRat) : (q.sub r).value = q.value - r.value := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem value_mul (q r : RawRat) : (q.mul r).value = q.value * r.value := by
  rw [mul, value, value, value]
  push_cast
  field_simp [Nat.ne_of_gt q.den_pos, Nat.ne_of_gt r.den_pos]
  <;> ring

end RawRat

/-- Signed division by a positive natural, implemented by dividing the
absolute value and restoring the sign. -/
def binaryIntDivNat (z : ℤ) (d : ℕ) : ℤ :=
  z.sign * ((binaryLongDiv z.natAbs d).1 : ℤ)

theorem binaryIntDivNat_eq_ediv {z : ℤ} {d : ℕ}
    (hd : 0 < d) (hdvd : d ∣ z.natAbs) :
    binaryIntDivNat z d = z / (d : ℤ) := by
  have hquot : (binaryLongDiv z.natAbs d).1 = z.natAbs / d := by
    simp [binaryLongDiv_eq_div_mod]
  have habs : z.natAbs = (z.natAbs / d) * d :=
    (Nat.div_mul_cancel hdvd).symm
  apply (Int.ediv_eq_of_eq_mul_left (by exact_mod_cast hd.ne') ?_).symm
  rw [binaryIntDivNat, hquot]
  calc
    z = z.sign * (z.natAbs : ℤ) := (Int.sign_mul_natAbs z).symm
    _ = z.sign * (((z.natAbs / d) * d : ℕ) : ℤ) := by rw [← habs]
    _ = (z.sign * (z.natAbs / d : ℕ)) * (d : ℤ) := by
      push_cast
      ring

/-- Explicit canonicalization of one unreduced fraction. -/
def binaryNormalizeRawRat (q : RawRat) : ℚ :=
  let g := binaryEuclidBounded q.num.natAbs q.den
  have hgcd : g = Nat.gcd q.num.natAbs q.den :=
    binaryEuclidBounded_eq_gcd _ _
  have hgpos : 0 < g := by
    rw [hgcd]
    exact Nat.gcd_pos_of_pos_right _ q.den_pos
  have hgdvdNum : g ∣ q.num.natAbs := by
    rw [hgcd]
    exact Nat.gcd_dvd_left _ _
  have hnum : binaryIntDivNat q.num g = q.num / (g : ℤ) :=
    binaryIntDivNat_eq_ediv hgpos hgdvdNum
  have hden : (binaryLongDiv q.den g).1 = q.den / g := by
    simp [binaryLongDiv_eq_div_mod]
  have hgdvdDen : g ∣ q.den := by
    rw [hgcd]
    exact Nat.gcd_dvd_right _ _
  have hdenPos : 0 < (binaryLongDiv q.den g).1 := by
    rw [hden]
    exact Nat.div_pos (Nat.le_of_dvd q.den_pos hgdvdDen) hgpos
  have hreduced :
      (binaryIntDivNat q.num g).natAbs.Coprime
        (binaryLongDiv q.den g).1 := by
    rw [hnum, hden, hgcd]
    exact Rat.normalize.reduced (Nat.ne_of_gt q.den_pos) rfl
  Rat.mk' (binaryIntDivNat q.num g) (binaryLongDiv q.den g).1
    (Nat.ne_of_gt hdenPos) hreduced

theorem binaryNormalizeRawRat_eq_normalize (q : RawRat) :
    binaryNormalizeRawRat q =
      Rat.normalize q.num q.den (Nat.ne_of_gt q.den_pos) := by
  let g := binaryEuclidBounded q.num.natAbs q.den
  have hgcd : g = Nat.gcd q.num.natAbs q.den :=
    binaryEuclidBounded_eq_gcd _ _
  have hgpos : 0 < g := by
    rw [hgcd]
    exact Nat.gcd_pos_of_pos_right _ q.den_pos
  have hgdvdNum : g ∣ q.num.natAbs := by
    rw [hgcd]
    exact Nat.gcd_dvd_left _ _
  have hnum : binaryIntDivNat q.num g = q.num / (g : ℤ) :=
    binaryIntDivNat_eq_ediv hgpos hgdvdNum
  have hden : (binaryLongDiv q.den g).1 = q.den / g := by
    simp [binaryLongDiv_eq_div_mod]
  rw [binaryNormalizeRawRat, Rat.normalize_eq]
  apply Rat.ext
  · simpa only [g, hgcd] using hnum
  · simpa only [g, hgcd] using hden

theorem binaryNormalizeRawRat_eq_value (q : RawRat) :
    binaryNormalizeRawRat q = q.value := by
  rw [binaryNormalizeRawRat_eq_normalize,
    Rat.normalize_eq_mkRat (Nat.ne_of_gt q.den_pos)]
  change mkRat q.num q.den = (q.num : ℚ) / ((q.den : ℤ) : ℚ)
  rw [Rat.intCast_div_eq_divInt]
  simp [Rat.divInt, mkRat, Nat.ne_of_gt q.den_pos]

end BeyondBethe
