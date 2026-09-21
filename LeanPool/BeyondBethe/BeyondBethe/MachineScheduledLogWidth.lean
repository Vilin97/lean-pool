/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineNearbyCoordinate

/-!
# Explicit raw-width bounds for scheduled logarithms

These lemmas bound the unreduced fractions produced by the directed logarithm
and by one nearby-Bethe coordinate.  They are intentionally stated in terms of
the exact arithmetic definitions, so the matrix-fold clamp can later be proved
inactive without an abstract bit-complexity assumption.
-/

namespace BeyondBethe

def rawLogSeriesWidthBudget (w N : ℕ) : ℕ :=
  1 + N * ((2 * N + 1) * w + 2 * N + 4)

def rawLogUnitLowerWidthBudget (w N : ℕ) : ℕ :=
  3 + rawLogSeriesWidthBudget (2 * w + 4) N

def rawLogSeriesErrorWidthBudget (w N : ℕ) : ℕ :=
  6 + (2 * N + 3) * (2 * w + 4)

def rawLogUnitUpperWidthBudget (w N : ℕ) : ℕ :=
  rawLogUnitLowerWidthBudget w N +
    rawLogSeriesErrorWidthBudget w N + 1

def rawDirectedLogWidthBudget (w N : ℕ) : ℕ :=
  (2 * w + 2 + rawLogUnitUpperWidthBudget 2 N) +
    rawLogUnitUpperWidthBudget (2 * w + 1) N + 1

/-- A deliberately coarse closed form for the exact syntactic budget above.
It is useful when composing the logarithm machine with matrix traversals: the
right-hand side exposes only the input width and the actual number of series
terms. -/
theorem rawDirectedLogWidthBudget_le (w N : ℕ) :
    rawDirectedLogWidthBudget w N ≤ 64 * (N + 2) ^ 2 * (w + 2) := by
  simp only [rawDirectedLogWidthBudget, rawLogUnitUpperWidthBudget,
    rawLogUnitLowerWidthBudget, rawLogSeriesErrorWidthBudget,
    rawLogSeriesWidthBudget]
  nlinarith

theorem rawRatWidth_ofInt_le (z : ℤ) :
    rawRatWidth (RawRat.ofInt z) ≤ z.natAbs.size + 1 := by
  simp [RawRat.ofInt, rawRatWidth]

theorem rawRatWidth_logScale_le (q : ℚ) :
    rawRatWidth (RawRat.logScale q) ≤
      rawRatWidth (rawRatOfRat q) + 1 := by
  have hnum := rawRat_num_size_le_width (rawRatOfRat q)
  have hden := rawRat_den_size_le_width (rawRatOfRat q)
  simp only [rawRatOfRat] at hnum hden
  rw [RawRat.logScale, rawRatWidth]
  change max (2 ^ binaryNatLog2 q.num.natAbs).size
      (2 ^ binaryNatLog2 q.den).size ≤
        rawRatWidth (⟨q.num, q.den, q.den_pos⟩ : RawRat) + 1
  rw [Nat.size_pow, Nat.size_pow, binaryNatLog2, binaryNatLog2]
  apply max_le <;> omega

theorem rawRatWidth_logResidual_le (q : ℚ) :
    rawRatWidth (RawRat.logResidual q) ≤
      2 * rawRatWidth (rawRatOfRat q) + 1 := by
  rw [RawRat.logResidual]
  have hdiv := rawRatWidth_div_le (rawRatOfRat q) (RawRat.logScale q)
  have hscale := rawRatWidth_logScale_le q
  omega

theorem rawRatWidth_logUnit_le (q : ℚ) :
    rawRatWidth (RawRat.logUnit q) ≤
      2 * rawRatWidth (rawRatOfRat q) + 1 := by
  rw [RawRat.logUnit]
  split_ifs
  · exact rawRatWidth_logResidual_le q
  · exact (rawRatWidth_inv_le _).trans (rawRatWidth_logResidual_le q)

theorem rawRatWidth_logUnitParameter_le (y : RawRat) :
    rawRatWidth (RawRat.logUnitParameter y) ≤ 2 * rawRatWidth y + 4 := by
  rw [RawRat.logUnitParameter]
  have hneg : rawRatWidth RawRat.one.neg = 1 := by
    rw [rawRatWidth_neg, rawRatWidth_one]
  have hnum := rawRatWidth_add_le y RawRat.one.neg
  have hden := rawRatWidth_add_le y RawRat.one
  have hdiv := rawRatWidth_div_le (y.add RawRat.one.neg) (y.add RawRat.one)
  rw [hneg] at hnum
  rw [rawRatWidth_one] at hden
  omega

theorem rawLogSeriesWidthBudget_mono {w w' N : ℕ} (h : w ≤ w') :
    rawLogSeriesWidthBudget w N ≤ rawLogSeriesWidthBudget w' N := by
  have hmul : (2 * N + 1) * w ≤ (2 * N + 1) * w' :=
    Nat.mul_le_mul_left _ h
  have hinner : (2 * N + 1) * w + 2 * N + 4 ≤
      (2 * N + 1) * w' + 2 * N + 4 := by omega
  simp only [rawLogSeriesWidthBudget]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left N hinner) 1

theorem rawLogUnitLowerWidthBudget_mono {w w' N : ℕ} (h : w ≤ w') :
    rawLogUnitLowerWidthBudget w N ≤ rawLogUnitLowerWidthBudget w' N := by
  simp only [rawLogUnitLowerWidthBudget]
  exact Nat.add_le_add_left
    (rawLogSeriesWidthBudget_mono (by omega : 2 * w + 4 ≤ 2 * w' + 4)) 3

theorem rawLogSeriesErrorWidthBudget_mono {w w' N : ℕ} (h : w ≤ w') :
    rawLogSeriesErrorWidthBudget w N ≤ rawLogSeriesErrorWidthBudget w' N := by
  have hinner : 2 * w + 4 ≤ 2 * w' + 4 := by omega
  simp only [rawLogSeriesErrorWidthBudget]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (2 * N + 3) hinner) 6

theorem rawLogUnitUpperWidthBudget_mono {w w' N : ℕ} (h : w ≤ w') :
    rawLogUnitUpperWidthBudget w N ≤ rawLogUnitUpperWidthBudget w' N := by
  simp only [rawLogUnitUpperWidthBudget]
  exact Nat.add_le_add_right
    (Nat.add_le_add (rawLogUnitLowerWidthBudget_mono h)
      (rawLogSeriesErrorWidthBudget_mono h)) 1

theorem rawRatWidth_logSeriesSum_budget (x : RawRat) (N : ℕ) :
    rawRatWidth (RawRat.logSeriesSum x N) ≤
      rawLogSeriesWidthBudget (rawRatWidth x) N := by
  exact RawRat.width_logSeriesSum_le x N

theorem rawRatWidth_logUnitLower_le (y : RawRat) (N : ℕ) :
    rawRatWidth (RawRat.logUnitLower y N) ≤
      rawLogUnitLowerWidthBudget (rawRatWidth y) N := by
  rw [RawRat.logUnitLower]
  have htwo := RawRat.width_ofNat_le 2
  have hx := rawRatWidth_logUnitParameter_le y
  have hseries := RawRat.width_logSeriesSum_le
    (RawRat.logUnitParameter y) N
  have hmul := rawRatWidth_mul_le (RawRat.ofNat 2)
    (RawRat.logSeriesSum (RawRat.logUnitParameter y) N)
  simp only [rawLogUnitLowerWidthBudget, rawLogSeriesWidthBudget]
  have hprod :
      (2 * N + 1) * rawRatWidth (RawRat.logUnitParameter y) ≤
        (2 * N + 1) * (2 * rawRatWidth y + 4) :=
    Nat.mul_le_mul_left _ hx
  have hinner :
      (2 * N + 1) * rawRatWidth (RawRat.logUnitParameter y) + 2 * N + 4 ≤
        (2 * N + 1) * (2 * rawRatWidth y + 4) + 2 * N + 4 := by omega
  have hseriesMono := Nat.mul_le_mul_left N hinner
  omega

theorem rawRatWidth_logSeriesError_le (y : RawRat) (N : ℕ) :
    rawRatWidth (RawRat.logSeriesError y N) ≤
      rawLogSeriesErrorWidthBudget (rawRatWidth y) N := by
  let x := RawRat.logUnitParameter y
  change rawRatWidth
      ((RawRat.ofNat 2).mul
        ((x.pow (2 * N + 1)).div
          (RawRat.one.add (x.mul x).neg))) ≤ _
  have hx : rawRatWidth x ≤ 2 * rawRatWidth y + 4 :=
    rawRatWidth_logUnitParameter_le y
  have hpow := RawRat.width_pow_le x (2 * N + 1)
  have hsquare := rawRatWidth_mul_le x x
  have hden := rawRatWidth_add_le RawRat.one (x.mul x).neg
  rw [rawRatWidth_one, rawRatWidth_neg] at hden
  have hdiv := rawRatWidth_div_le (x.pow (2 * N + 1))
    (RawRat.one.add (x.mul x).neg)
  have htwo := RawRat.width_ofNat_le 2
  have hmul := rawRatWidth_mul_le (RawRat.ofNat 2)
    ((x.pow (2 * N + 1)).div (RawRat.one.add (x.mul x).neg))
  simp only [rawLogSeriesErrorWidthBudget]
  have hprod :
      (2 * N + 3) * rawRatWidth x ≤
        (2 * N + 3) * (2 * rawRatWidth y + 4) :=
    Nat.mul_le_mul_left _ hx
  have hdivBound :
      rawRatWidth
          ((x.pow (2 * N + 1)).div
            (RawRat.one.add (x.mul x).neg)) ≤
        3 + (2 * N + 3) * rawRatWidth x := by
    have hdenBound :
        rawRatWidth (RawRat.one.add (x.mul x).neg) ≤
          2 * rawRatWidth x + 2 := by omega
    calc
      _ ≤ rawRatWidth (x.pow (2 * N + 1)) +
          rawRatWidth (RawRat.one.add (x.mul x).neg) := hdiv
      _ ≤ (1 + (2 * N + 1) * rawRatWidth x) +
          (2 * rawRatWidth x + 2) := Nat.add_le_add hpow hdenBound
      _ = 3 + (2 * N + 3) * rawRatWidth x := by ring
  have hmulBound :
      rawRatWidth
          ((RawRat.ofNat 2).mul
            ((x.pow (2 * N + 1)).div
              (RawRat.one.add (x.mul x).neg))) ≤
        6 + (2 * N + 3) * rawRatWidth x := by
    calc
      _ ≤ rawRatWidth (RawRat.ofNat 2) +
          rawRatWidth
            ((x.pow (2 * N + 1)).div
              (RawRat.one.add (x.mul x).neg)) := hmul
      _ ≤ 3 + (3 + (2 * N + 3) * rawRatWidth x) :=
        Nat.add_le_add htwo hdivBound
      _ = 6 + (2 * N + 3) * rawRatWidth x := by omega
  exact hmulBound.trans (Nat.add_le_add_left hprod 6)

theorem rawRatWidth_logUnitUpper_le (y : RawRat) (N : ℕ) :
    rawRatWidth (RawRat.logUnitUpper y N) ≤
      rawLogUnitUpperWidthBudget (rawRatWidth y) N := by
  rw [RawRat.logUnitUpper]
  have hlo := rawRatWidth_logUnitLower_le y N
  have herr := rawRatWidth_logSeriesError_le y N
  have hadd := rawRatWidth_add_le (RawRat.logUnitLower y N)
    (RawRat.logSeriesError y N)
  simp only [rawLogUnitUpperWidthBudget]
  omega

theorem rawLogUnitLowerWidthBudget_le_upper (w N : ℕ) :
    rawLogUnitLowerWidthBudget w N ≤ rawLogUnitUpperWidthBudget w N := by
  simp only [rawLogUnitUpperWidthBudget]
  omega

theorem rationalBinaryExponent_natAbs_size_le (q : ℚ) :
    (rationalBinaryExponent q).natAbs.size ≤
      2 * rawRatWidth (rawRatOfRat q) + 1 := by
  have hexp := rationalBinaryExponent_natAbs_le_two_rawWidth q
  have hsize : (rationalBinaryExponent q).natAbs.size ≤
      (rationalBinaryExponent q).natAbs + 1 := by
    rw [Nat.size_le]
    exact (Nat.lt_two_pow_self
      (n := (rationalBinaryExponent q).natAbs)).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  omega

theorem rawRatWidth_logIntegerLower_le (q : ℚ) (N : ℕ) :
    rawRatWidth (RawRat.logIntegerLower q N) ≤
      2 * rawRatWidth (rawRatOfRat q) + 2 +
        rawLogUnitUpperWidthBudget 2 N := by
  rw [RawRat.logIntegerLower, binaryRationalBinaryExponent_eq]
  have hk := rationalBinaryExponent_natAbs_size_le q
  have hint := rawRatWidth_ofInt_le (rationalBinaryExponent q)
  have htwo : rawRatWidth (RawRat.ofNat 2) = 2 := by
    decide
  have hlo := rawRatWidth_logUnitLower_le (RawRat.ofNat 2) N
  have hhi := rawRatWidth_logUnitUpper_le (RawRat.ofNat 2) N
  rw [htwo] at hlo hhi
  have hint' :
      rawRatWidth (RawRat.ofInt (rationalBinaryExponent q)) ≤
        2 * rawRatWidth (rawRatOfRat q) + 2 := by omega
  split_ifs with hsign
  · have hmul := rawRatWidth_mul_le
      (RawRat.ofInt (rationalBinaryExponent q))
      (RawRat.logUnitLower (RawRat.ofNat 2) N)
    have hfactor :
        rawRatWidth (RawRat.logUnitLower (RawRat.ofNat 2) N) ≤
          rawLogUnitUpperWidthBudget 2 N :=
      hlo.trans (rawLogUnitLowerWidthBudget_le_upper 2 N)
    exact hmul.trans (Nat.add_le_add hint' hfactor)
  · have hmul := rawRatWidth_mul_le
      (RawRat.ofInt (rationalBinaryExponent q))
      (RawRat.logUnitUpper (RawRat.ofNat 2) N)
    exact hmul.trans (Nat.add_le_add hint' hhi)

theorem rawRatWidth_logIntegerUpper_le (q : ℚ) (N : ℕ) :
    rawRatWidth (RawRat.logIntegerUpper q N) ≤
      2 * rawRatWidth (rawRatOfRat q) + 2 +
        rawLogUnitUpperWidthBudget 2 N := by
  rw [RawRat.logIntegerUpper, binaryRationalBinaryExponent_eq]
  have hk := rationalBinaryExponent_natAbs_size_le q
  have hint := rawRatWidth_ofInt_le (rationalBinaryExponent q)
  have htwo : rawRatWidth (RawRat.ofNat 2) = 2 := by
    decide
  have hlo := rawRatWidth_logUnitLower_le (RawRat.ofNat 2) N
  have hhi := rawRatWidth_logUnitUpper_le (RawRat.ofNat 2) N
  rw [htwo] at hlo hhi
  have hint' :
      rawRatWidth (RawRat.ofInt (rationalBinaryExponent q)) ≤
        2 * rawRatWidth (rawRatOfRat q) + 2 := by omega
  split_ifs with hsign
  · have hmul := rawRatWidth_mul_le
      (RawRat.ofInt (rationalBinaryExponent q))
      (RawRat.logUnitUpper (RawRat.ofNat 2) N)
    exact hmul.trans (Nat.add_le_add hint' hhi)
  · have hmul := rawRatWidth_mul_le
      (RawRat.ofInt (rationalBinaryExponent q))
      (RawRat.logUnitLower (RawRat.ofNat 2) N)
    have hfactor :
        rawRatWidth (RawRat.logUnitLower (RawRat.ofNat 2) N) ≤
          rawLogUnitUpperWidthBudget 2 N :=
      hlo.trans (rawLogUnitLowerWidthBudget_le_upper 2 N)
    exact hmul.trans (Nat.add_le_add hint' hfactor)

theorem rawRatWidth_logResidualLower_le (q : ℚ) (N : ℕ) :
    rawRatWidth (RawRat.logResidualLower q N) ≤
      rawLogUnitUpperWidthBudget
        (2 * rawRatWidth (rawRatOfRat q) + 1) N := by
  rw [RawRat.logResidualLower]
  have hy := rawRatWidth_logUnit_le q
  have hlo := rawRatWidth_logUnitLower_le (RawRat.logUnit q) N
  have hhi := rawRatWidth_logUnitUpper_le (RawRat.logUnit q) N
  have hmono :
      rawLogUnitUpperWidthBudget (rawRatWidth (RawRat.logUnit q)) N ≤
        rawLogUnitUpperWidthBudget
          (2 * rawRatWidth (rawRatOfRat q) + 1) N := by
    exact rawLogUnitUpperWidthBudget_mono hy
  split_ifs
  · exact hlo.trans
      ((rawLogUnitLowerWidthBudget_le_upper _ _).trans hmono)
  · rw [rawRatWidth_neg]
    exact hhi.trans hmono

theorem rawRatWidth_logResidualUpper_le (q : ℚ) (N : ℕ) :
    rawRatWidth (RawRat.logResidualUpper q N) ≤
      rawLogUnitUpperWidthBudget
        (2 * rawRatWidth (rawRatOfRat q) + 1) N := by
  rw [RawRat.logResidualUpper]
  have hy := rawRatWidth_logUnit_le q
  have hlo := rawRatWidth_logUnitLower_le (RawRat.logUnit q) N
  have hhi := rawRatWidth_logUnitUpper_le (RawRat.logUnit q) N
  have hmono :
      rawLogUnitUpperWidthBudget (rawRatWidth (RawRat.logUnit q)) N ≤
        rawLogUnitUpperWidthBudget
          (2 * rawRatWidth (rawRatOfRat q) + 1) N := by
    exact rawLogUnitUpperWidthBudget_mono hy
  split_ifs
  · exact hhi.trans hmono
  · rw [rawRatWidth_neg]
    exact hlo.trans
      ((rawLogUnitLowerWidthBudget_le_upper _ _).trans hmono)

theorem rawRatWidth_logLower_le (q : ℚ) (N : ℕ) :
    rawRatWidth (RawRat.logLower q N) ≤
      rawDirectedLogWidthBudget (rawRatWidth (rawRatOfRat q)) N := by
  rw [RawRat.logLower]
  have hint := rawRatWidth_logIntegerLower_le q N
  have hres := rawRatWidth_logResidualLower_le q N
  have hadd := rawRatWidth_add_le (RawRat.logIntegerLower q N)
    (RawRat.logResidualLower q N)
  exact hadd.trans (by
    simp only [rawDirectedLogWidthBudget]
    omega)

theorem rawRatWidth_logUpper_le (q : ℚ) (N : ℕ) :
    rawRatWidth (RawRat.logUpper q N) ≤
      rawDirectedLogWidthBudget (rawRatWidth (rawRatOfRat q)) N := by
  rw [RawRat.logUpper]
  have hint := rawRatWidth_logIntegerUpper_le q N
  have hres := rawRatWidth_logResidualUpper_le q N
  have hadd := rawRatWidth_add_le (RawRat.logIntegerUpper q N)
    (RawRat.logResidualUpper q N)
  exact hadd.trans (by
    simp only [rawDirectedLogWidthBudget]
    omega)

theorem rawRatWidth_scheduledLogLower_le (q : ℚ) (p : ℕ) :
    rawRatWidth (rawScheduledLogLower q p) ≤
      rawDirectedLogWidthBudget (rawRatWidth (rawRatOfRat q))
        (directedLogTerms q p) := by
  exact rawRatWidth_logLower_le q (directedLogTerms q p)

theorem rawRatWidth_scheduledLogUpper_le (q : ℚ) (p : ℕ) :
    rawRatWidth (rawScheduledLogUpper q p) ≤
      rawDirectedLogWidthBudget (rawRatWidth (rawRatOfRat q))
        (directedLogTerms q p) := by
  exact rawRatWidth_logUpper_le q (directedLogTerms q p)

theorem directedLogTerms_le_rawWidth (q : ℚ) (p : ℕ) :
    directedLogTerms q p ≤
      p + 2 * rawRatWidth (rawRatOfRat q) + 2 := by
  have h := rationalBinaryExponent_natAbs_le_two_rawWidth q
  rw [directedLogTerms]
  omega

/-- Closed polynomial width bound for one scheduled lower logarithm. -/
theorem rawRatWidth_scheduledLogLower_polynomial_le (q : ℚ) (p : ℕ) :
    rawRatWidth (rawScheduledLogLower q p) ≤
      64 * (p + 2 * rawRatWidth (rawRatOfRat q) + 4) ^ 2 *
        (rawRatWidth (rawRatOfRat q) + 2) := by
  have hterms0 := directedLogTerms_le_rawWidth q p
  have hterms : directedLogTerms q p + 2 ≤
      p + 2 * rawRatWidth (rawRatOfRat q) + 4 := by omega
  have hsquare : (directedLogTerms q p + 2) ^ 2 ≤
      (p + 2 * rawRatWidth (rawRatOfRat q) + 4) ^ 2 :=
    Nat.pow_le_pow_left hterms 2
  have hmul := Nat.mul_le_mul_right
      (rawRatWidth (rawRatOfRat q) + 2)
    (Nat.mul_le_mul_left 64 hsquare)
  exact (rawRatWidth_scheduledLogLower_le q p).trans
    ((rawDirectedLogWidthBudget_le
      (rawRatWidth (rawRatOfRat q)) (directedLogTerms q p)).trans hmul)

/-- Closed polynomial width bound for one scheduled upper logarithm. -/
theorem rawRatWidth_scheduledLogUpper_polynomial_le (q : ℚ) (p : ℕ) :
    rawRatWidth (rawScheduledLogUpper q p) ≤
      64 * (p + 2 * rawRatWidth (rawRatOfRat q) + 4) ^ 2 *
        (rawRatWidth (rawRatOfRat q) + 2) := by
  have hterms0 := directedLogTerms_le_rawWidth q p
  have hterms : directedLogTerms q p + 2 ≤
      p + 2 * rawRatWidth (rawRatOfRat q) + 4 := by omega
  have hsquare : (directedLogTerms q p + 2) ^ 2 ≤
      (p + 2 * rawRatWidth (rawRatOfRat q) + 4) ^ 2 :=
    Nat.pow_le_pow_left hterms 2
  have hmul := Nat.mul_le_mul_right
      (rawRatWidth (rawRatOfRat q) + 2)
    (Nat.mul_le_mul_left 64 hsquare)
  exact (rawRatWidth_scheduledLogUpper_le q p).trans
    ((rawDirectedLogWidthBudget_le
      (rawRatWidth (rawRatOfRat q)) (directedLogTerms q p)).trans hmul)

theorem rawRatWidth_scheduledLogLower_of_bounds_le
    (q : ℚ) {p P W : ℕ} (hp : p ≤ P)
    (hw : rawRatWidth (rawRatOfRat q) ≤ W) :
    rawRatWidth (rawScheduledLogLower q p) ≤
      64 * (P + 2 * W + 4) ^ 2 * (W + 2) := by
  have hbase : p + 2 * rawRatWidth (rawRatOfRat q) + 4 ≤
      P + 2 * W + 4 := by omega
  have hpow := Nat.pow_le_pow_left hbase 2
  have hleft := Nat.mul_le_mul_left 64 hpow
  have hright : rawRatWidth (rawRatOfRat q) + 2 ≤ W + 2 := by omega
  exact (rawRatWidth_scheduledLogLower_polynomial_le q p).trans
    (Nat.mul_le_mul hleft hright)

theorem rawRatWidth_scheduledLogUpper_of_bounds_le
    (q : ℚ) {p P W : ℕ} (hp : p ≤ P)
    (hw : rawRatWidth (rawRatOfRat q) ≤ W) :
    rawRatWidth (rawScheduledLogUpper q p) ≤
      64 * (P + 2 * W + 4) ^ 2 * (W + 2) := by
  have hbase : p + 2 * rawRatWidth (rawRatOfRat q) + 4 ≤
      P + 2 * W + 4 := by omega
  have hpow := Nat.pow_le_pow_left hbase 2
  have hleft := Nat.mul_le_mul_left 64 hpow
  have hright : rawRatWidth (rawRatOfRat q) + 2 ≤ W + 2 := by omega
  exact (rawRatWidth_scheduledLogUpper_polynomial_le q p).trans
    (Nat.mul_le_mul hleft hright)

theorem rawRatWidth_complement_le (x : ℚ) :
    rawRatWidth (rawRatOfRat (1 - x)) ≤
      44 + 12 * rawRatWidth (rawRatOfRat x) := by
  let r := RawRat.one.add (rawRatOfRat x).neg
  have hr : rawRatWidth r ≤ rawRatWidth (rawRatOfRat x) + 2 := by
    have hadd := rawRatWidth_add_le RawRat.one (rawRatOfRat x).neg
    rw [rawRatWidth_one, rawRatWidth_neg] at hadd
    exact hadd.trans (by omega)
  have hvalue : binaryNormalizeRawRat r = 1 - x := by
    rw [binaryNormalizeRawRat_eq_value]
    simp [r, RawRat.value_add, RawRat.value_one, RawRat.value_neg,
      rawRatOfRat_value]
    ring
  have hcanonical := rawRatOfRat_width_le_encodedBitLength (1 - x)
  rw [← hvalue] at hcanonical
  have hnormalize := binaryNormalizeRawRat_encodedBitLength_le r
  rw [← hvalue]
  omega

def rawNearbyCoordinateWidthBudget (tau : RawRat) (x : ℚ) (p : ℕ) : ℕ :=
  rawDirectedLogWidthBudget (rawRatWidth (rawRatOfRat (1 - x)))
      (directedLogTerms (1 - x) p) +
    rawRatWidth tau + rawRatWidth (rawRatOfRat x) +
    rawDirectedLogWidthBudget (rawRatWidth (rawRatOfRat x))
      (directedLogTerms x p) + 1

theorem rawRatWidth_nearbyCoordinateLower_le
    (tau : RawRat) (x : ℚ) (p : ℕ) :
    rawRatWidth (rawNearbyCoordinateLower tau x p) ≤
      rawNearbyCoordinateWidthBudget tau x p := by
  rw [rawNearbyCoordinateLower]
  have hcomp := rawRatWidth_scheduledLogLower_le (1 - x) p
  have htx := rawRatWidth_mul_le tau (rawRatOfRat x)
  have hlogx := rawRatWidth_scheduledLogLower_le x p
  have hweighted := rawRatWidth_mul_le (tau.mul (rawRatOfRat x))
    (rawScheduledLogLower x p)
  have hadd := rawRatWidth_add_le (rawScheduledLogLower (1 - x) p)
    ((tau.mul (rawRatOfRat x)).mul (rawScheduledLogLower x p))
  exact hadd.trans (by
    simp only [rawNearbyCoordinateWidthBudget]
    omega)

end BeyondBethe
