/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.DyadicRounding
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic

/-! # Dyadic Magnitude Precision -/

@[expose] public section

namespace BeyondBethe

/-!
# A magnitude-sensitive dyadic precision

Using the full encoding length of a rational as a dyadic precision is much
too conservative: the determinant of a dyadic `d`-by-`d` matrix can have a
denominator with `d p` bits even when its numerical magnitude is bounded
away from zero.  Iterating that rule would multiply the stored precision by
the dimension.  The definition below instead uses the *difference* between
the denominator and numerator bit lengths.  It therefore measures
`log₂ (1 / q)`, up to an additive constant, rather than the cost of writing
the exact reduced fraction.
-/

/-- A total precision selector.  On a positive rational it is, up to two
guard bits, the binary exponent needed to resolve its magnitude. -/
def positiveDyadicPrecision (q : ℚ) : ℕ :=
  q.den.size + 2 - q.num.natAbs.size

theorem positiveDyadicPrecision_add_num_size_ge (q : ℚ) :
    q.den.size + 2 ≤
      positiveDyadicPrecision q + q.num.natAbs.size := by
  rw [positiveDyadicPrecision]
  omega

/-- The selected dyadic mesh is strictly below every positive input. -/
theorem dyadicMesh_positiveDyadicPrecision_lt {q : ℚ} (hq : 0 < q) :
    dyadicMesh (positiveDyadicPrecision q) < q := by
  let a := q.num.natAbs
  let D := q.den.size
  let N := a.size
  let p := positiveDyadicPrecision q
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have ha0 : 0 < a := by
    dsimp only [a]
    exact Int.natAbs_pos.mpr hnum.ne'
  have hN0 : 0 < N := by
    dsimp only [N]
    exact Nat.size_pos.mpr ha0
  have haLower : 2 ^ (N - 1) ≤ a := by
    rw [← Nat.lt_size]
    dsimp only [N]
    omega
  have hdenUpper : q.den < 2 ^ D := by
    dsimp only [D]
    exact Nat.lt_size_self q.den
  have hsum : D + 2 ≤ p + N := by
    simpa only [D, N, p] using positiveDyadicPrecision_add_num_size_ge q
  have hexp : 2 ^ (D + 1) ≤ 2 ^ (p + (N - 1)) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hmulLower : 2 ^ (p + (N - 1)) ≤ 2 ^ p * a := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ haLower
  have hdenMul : q.den < 2 ^ p * a := by
    calc
      q.den < 2 ^ D := hdenUpper
      _ < 2 ^ (D + 1) := by
        rw [pow_succ]
        have : 0 < 2 ^ D := by positivity
        omega
      _ ≤ 2 ^ (p + (N - 1)) := hexp
      _ ≤ 2 ^ p * a := hmulLower
  have hqrep : q = (a : ℚ) / (q.den : ℚ) := by
    calc
      q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      _ = (a : ℚ) / (q.den : ℚ) := by
        congr 1
        have haz : (a : ℤ) = q.num := by
          dsimp only [a]
          exact Int.natAbs_of_nonneg hnum.le
        have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) haz.symm
        simpa using hcast
  have hdenMulQ : (q.den : ℚ) < (2 : ℚ) ^ p * (a : ℚ) := by
    exact_mod_cast hdenMul
  change 1 / (2 : ℚ) ^ p < q
  rw [hqrep]
  have hpow : (0 : ℚ) < (2 : ℚ) ^ p := by positivity
  have hden : (0 : ℚ) < q.den := by positivity
  rw [div_lt_div_iff₀ hpow hden]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hdenMulQ

/-- Conversely, any proved dyadic lower bound on a positive rational gives
a direct upper bound on the selected precision.  This is the key estimate
that prevents precision from tracking irrelevant exact denominators. -/
theorem positiveDyadicPrecision_le_of_dyadicMesh_le
    {q : ℚ} (hq : 0 < q) {P : ℕ}
    (hlower : dyadicMesh P ≤ q) :
    positiveDyadicPrecision q ≤ P + 2 := by
  let a := q.num.natAbs
  let D := q.den.size
  let N := a.size
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have ha0 : 0 < a := by
    dsimp only [a]
    exact Int.natAbs_pos.mpr hnum.ne'
  have hqrep : q = (a : ℚ) / (q.den : ℚ) := by
    calc
      q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      _ = (a : ℚ) / (q.den : ℚ) := by
        congr 1
        have haz : (a : ℤ) = q.num := by
          dsimp only [a]
          exact Int.natAbs_of_nonneg hnum.le
        have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) haz.symm
        simpa using hcast
  have hcrossQ : (q.den : ℚ) ≤ (2 : ℚ) ^ P * (a : ℚ) := by
    rw [dyadicMesh, hqrep] at hlower
    have hpow : (0 : ℚ) < (2 : ℚ) ^ P := by positivity
    have hden : (0 : ℚ) < q.den := by positivity
    rw [div_le_div_iff₀ hpow hden] at hlower
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlower
  have hcross : q.den ≤ 2 ^ P * a := by
    exact_mod_cast hcrossQ
  have haUpper : a < 2 ^ N := by
    dsimp only [N]
    exact Nat.lt_size_self a
  have hdenUpper : q.den < 2 ^ (P + N) := by
    calc
      q.den ≤ 2 ^ P * a := hcross
      _ < 2 ^ P * 2 ^ N :=
        Nat.mul_lt_mul_of_pos_left haUpper (by positivity)
      _ = 2 ^ (P + N) := by rw [pow_add]
  have hD : D ≤ P + N := by
    dsimp only [D]
    exact Nat.size_le.mpr hdenUpper
  dsimp only [D, N, a] at hD
  rw [positiveDyadicPrecision]
  omega

end BeyondBethe
