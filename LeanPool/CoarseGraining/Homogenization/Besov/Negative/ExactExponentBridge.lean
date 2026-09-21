/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactCirc
import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactDual

/-!
# Exponent and coefficient bridges for exact Besov duality

This module contains only arithmetic and parameter-carrier bridges.  In
particular, it does not compare an extended exact seminorm with a legacy
real-valued wrapper.
-/

namespace Homogenization

open scoped ENNReal

/-- The legacy extended conjugate of a finite real exponent agrees with the
real Hölder conjugate used by the exact dual kernel. -/
theorem cubeBesovConjExponent_ofReal_eq_exactDualConjExponent (p : ℝ) (hp : 1 < p) :
    cubeBesovConjExponent (ENNReal.ofReal p) =
      ENNReal.ofReal (exactDualConjExponent p) := by
  let : ENNReal.HolderConjugate (ENNReal.ofReal p)
      (ENNReal.ofReal (exactDualConjExponent p)) :=
    (exactDualConjExponent_holder p hp).ennrealOfReal
  simpa only [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := ENNReal.ofReal p) (q := ENNReal.ofReal (exactDualConjExponent p)))

/-- Conjugating the finite exact-dual exponent recovers its source exponent. -/
theorem cubeBesovConjExponent_exactDualConjExponent_eq_ofReal (p : ℝ) (hp : 1 < p) :
    cubeBesovConjExponent (ENNReal.ofReal (exactDualConjExponent p)) =
      ENNReal.ofReal p := by
  let : ENNReal.HolderConjugate (ENNReal.ofReal (exactDualConjExponent p))
      (ENNReal.ofReal p) :=
    (exactDualConjExponent_holder p hp).symm.ennrealOfReal
  simpa only [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := ENNReal.ofReal (exactDualConjExponent p)) (q := ENNReal.ofReal p))

/-- The finite-real conjugate used by the exact dual kernel is never `∞`. -/
theorem cubeBesovConjExponent_ofReal_ne_top (p : ℝ) (hp : 1 < p) :
    cubeBesovConjExponent (ENNReal.ofReal p) ≠ ∞ := by
  rw [cubeBesovConjExponent_ofReal_eq_exactDualConjExponent p hp]
  exact ENNReal.ofReal_ne_top

/-- The finite-real conjugate used by the exact dual kernel is at least one. -/
theorem cubeBesovConjExponent_ofReal_one_le (p : ℝ) (hp : 1 < p) :
    1 ≤ cubeBesovConjExponent (ENNReal.ofReal p) := by
  rw [cubeBesovConjExponent_ofReal_eq_exactDualConjExponent p hp,
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (exactDualConjExponent_one_le p hp)

/-- The endpoint `q = 1` has conjugate exponent `∞`. -/
theorem cubeBesovConjExponent_one : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
  simp [cubeBesovConjExponent, ENNReal.conjExponent]

/-- The endpoint `q = ∞` has conjugate exponent one. -/
theorem cubeBesovConjExponent_top : cubeBesovConjExponent (∞ : ℝ≥0∞) = 1 := by
  simp [cubeBesovConjExponent, ENNReal.conjExponent]

/-- A finite source `q > 1` has the finite real Hölder conjugate expected by
the exact positive test lane. -/
theorem cubeBesovConjExponent_ofReal_finite (q : ℝ) (hq : 1 < q) :
    cubeBesovConjExponent (ENNReal.ofReal q) =
      ENNReal.ofReal (exactDualConjExponent q) :=
  cubeBesovConjExponent_ofReal_eq_exactDualConjExponent q hq

/-- The legacy conjugate exponent is nonzero on the finite exact-dual range. -/
theorem cubeBesovConjExponent_ofReal_ne_zero (p : ℝ) (hp : 1 < p) :
    cubeBesovConjExponent (ENNReal.ofReal p) ≠ 0 := by
  intro hzero
  have hone := cubeBesovConjExponent_ofReal_one_le p hp
  rw [hzero] at hone
  norm_num at hone

/-- The overlap/projection loss coefficient is bounded by the Chapter 1
coefficient.  All exponents are real and finite in this bridge. -/
theorem exactCircLossCoefficient_le_source (d : ℕ) (s p' : ℝ)
    (hs : 0 ≤ s) (hp' : 1 ≤ p') :
    max 1 ((3 : ℝ) ^ s) * (3 : ℝ) ^ ((d : ℝ) / p') ≤
      (3 : ℝ) ^ ((d : ℝ) + s) := by
  have hp'_pos : 0 < p' := lt_of_lt_of_le zero_lt_one hp'
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd_div_le : (d : ℝ) / p' ≤ (d : ℝ) := by
    rw [div_le_iff₀ hp'_pos]
    exact le_mul_of_one_le_right hd_nonneg hp'
  have hmax : max 1 ((3 : ℝ) ^ s) = (3 : ℝ) ^ s :=
    max_eq_right (Real.one_le_rpow (by norm_num) hs)
  rw [hmax]
  calc
    (3 : ℝ) ^ s * (3 : ℝ) ^ ((d : ℝ) / p') ≤
        (3 : ℝ) ^ s * (3 : ℝ) ^ (d : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hd_div_le)
        (Real.rpow_nonneg (by positivity) _)
    _ = (3 : ℝ) ^ ((d : ℝ) + s) := by
      rw [← Real.rpow_add (by norm_num : 0 < (3 : ℝ))]
      ring_nf

/-- `ENNReal` form of `exactCircLossCoefficient_le_source`, ready to multiply
by an extended circ value. -/
theorem exactCircLossCoefficientENNReal_le_source (d : ℕ) (s p' : ℝ)
    (hs : 0 ≤ s) (hp' : 1 ≤ p') :
    ENNReal.ofReal (max 1 ((3 : ℝ) ^ s) * (3 : ℝ) ^ ((d : ℝ) / p')) ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) + s)) :=
  ENNReal.ofReal_le_ofReal (exactCircLossCoefficient_le_source d s p' hs hp')

/-- Rpow-form `ENNReal` version of the loss bound, directly composable with
an extended circ seminorm. -/
theorem exactCircLossCoefficientENNReal_rpow_le_source (d : ℕ) (s p' : ℝ)
    (hs : 0 ≤ s) (hp' : 1 ≤ p') :
    max 1 ((3 : ℝ≥0∞) ^ s) * (3 : ℝ≥0∞) ^ ((d : ℝ) / p') ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + s) := by
  have hp'_pos : 0 < p' := lt_of_lt_of_le zero_lt_one hp'
  have hd_div_nonneg : 0 ≤ (d : ℝ) / p' :=
    div_nonneg (Nat.cast_nonneg d) hp'_pos.le
  have hd_add_nonneg : 0 ≤ (d : ℝ) + s :=
    add_nonneg (Nat.cast_nonneg d) hs
  have hleft_nonneg : 0 ≤ max 1 ((3 : ℝ) ^ s) :=
    zero_le_one.trans (le_max_left _ _)
  have hleft :
      ENNReal.ofReal (max 1 ((3 : ℝ) ^ s) * (3 : ℝ) ^ ((d : ℝ) / p')) =
        max 1 ((3 : ℝ≥0∞) ^ s) * (3 : ℝ≥0∞) ^ ((d : ℝ) / p') := by
    rw [ENNReal.ofReal_mul hleft_nonneg, ENNReal.ofReal_max,
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ)) hs,
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ)) hd_div_nonneg]
    norm_num
  have hright : ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) + s)) =
      (3 : ℝ≥0∞) ^ ((d : ℝ) + s) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ)) hd_add_nonneg]
    norm_num
  calc
    max 1 ((3 : ℝ≥0∞) ^ s) * (3 : ℝ≥0∞) ^ ((d : ℝ) / p') =
        ENNReal.ofReal (max 1 ((3 : ℝ) ^ s) * (3 : ℝ) ^ ((d : ℝ) / p')) := hleft.symm
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) + s)) :=
      exactCircLossCoefficientENNReal_le_source d s p' hs hp'
    _ = (3 : ℝ≥0∞) ^ ((d : ℝ) + s) := hright

/-- The `q = 1` dual branch supplies an admissible finite-`q` circ parameter
with circ exponent one. -/
noncomputable def ExactDualQOneParameters.circParameters
    (P : ExactDualQOneParameters) : ExactCircFiniteParameters where
  s := P.s
  p := P.p
  q := 1
  admissible := ⟨P.s_pos, P.s_le_one, P.p_one_lt.le, le_rfl, fun _ => rfl⟩

/-- An interior finite dual branch supplies the matching finite circ branch. -/
noncomputable def ExactDualFiniteParameters.circParameters
    (P : ExactDualFiniteParameters) : ExactCircFiniteParameters where
  s := P.s
  p := P.p
  q := P.q
  admissible := ⟨P.s_pos, P.s_lt_one.le, P.p_one_lt.le, P.q_one_lt.le, by
    intro hs
    exact False.elim ((ne_of_lt P.s_lt_one) hs)⟩

/-- The `q = ∞` dual branch supplies the matching top circ branch. -/
noncomputable def ExactDualTopParameters.circParameters
    (P : ExactDualTopParameters) : ExactCircTopParameters where
  s := P.s
  p := P.p
  admissible := ⟨P.s_pos, P.s_lt_one, P.p_one_lt.le⟩

end Homogenization
