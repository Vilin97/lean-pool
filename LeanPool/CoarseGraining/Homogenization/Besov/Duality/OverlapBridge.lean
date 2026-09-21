/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.OverlapDefinitions
import LeanPool.CoarseGraining.Homogenization.Besov.PositiveOverlapBridge

/-! # Overlap Bridge -/

namespace Homogenization

open scoped ENNReal

/-!
# Overlap dual-test norm bridges

This file is the first downstream use of the overlap dual-test definitions. It
keeps the result at the norm/seminorm level: the local `MemLp` admissibility
predicates for disjoint and overlap tests are intentionally not converted here.
-/

theorem cubeBesovConjExponent_toReal_pos_of_ne_top
    (p : ℝ≥0∞) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    0 < (cubeBesovConjExponent p).toReal :=
  ENNReal.toReal_pos (cubeBesovConjExponent_ne_zero p) hpTop

theorem one_le_cubeBesovConjExponent_toReal_of_one_le
    (q : ℝ≥0∞) (hq : 1 ≤ q) (hqConjTop : cubeBesovConjExponent q ≠ ∞) :
    1 ≤ (cubeBesovConjExponent q).toReal := by
  let : ENNReal.HolderConjugate q (cubeBesovConjExponent q) := by
    simpa [cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hq
  let : ENNReal.HolderConjugate (cubeBesovConjExponent q) q :=
    ENNReal.HolderConjugate.symm (p := q) (q := cubeBesovConjExponent q)
  have hqConj : 1 ≤ cubeBesovConjExponent q :=
    ENNReal.HolderConjugate.one_le (p := cubeBesovConjExponent q) (q := q)
  simpa [ENNReal.toReal_one] using
    ((ENNReal.toReal_le_toReal ENNReal.one_ne_top hqConjTop).2 hqConj)

theorem cubeBesovDualTestNorm_le_three_rpow_mul_overlapDualTestNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (g : Vec d → ℝ) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    cubeBesovDualTestNorm Q s p q N g
      ≤ (3 : ℝ) ^ ((d : ℝ) / (cubeBesovConjExponent p).toReal) *
        cubeBesovOverlapDualTestNorm Q s p q N g := by
  have hpConjPos : 0 < (cubeBesovConjExponent p).toReal :=
    cubeBesovConjExponent_toReal_pos_of_ne_top p hpConjTop
  by_cases hqConjTop : cubeBesovConjExponent q = ∞
  · rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s p q N g hqConjTop,
      cubeBesovOverlapDualTestNorm_of_conjExponent_eq_top Q s p q N g hqConjTop]
    exact cubeBesovPartialNormTop_le_three_rpow_mul_overlapPartialNormTop
      Q s hpConjPos N g
  · have hqConjReal : 1 ≤ (cubeBesovConjExponent q).toReal :=
      one_le_cubeBesovConjExponent_toReal_of_one_le q hq hqConjTop
    rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N g hqConjTop,
      cubeBesovOverlapDualTestNorm_of_conjExponent_ne_top Q s p q N g hqConjTop]
    exact cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm
      Q s hpConjPos hqConjReal N g

theorem cubeBesovDualTestSeminorm_le_three_rpow_mul_overlapDualTestSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (g : Vec d → ℝ) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    cubeBesovDualTestSeminorm Q s p q N g
      ≤ (3 : ℝ) ^ ((d : ℝ) / (cubeBesovConjExponent p).toReal) *
        cubeBesovOverlapDualTestSeminorm Q s p q N g := by
  have hpConjPos : 0 < (cubeBesovConjExponent p).toReal :=
    cubeBesovConjExponent_toReal_pos_of_ne_top p hpConjTop
  by_cases hqConjTop : cubeBesovConjExponent q = ∞
  · rw [cubeBesovDualTestSeminorm_of_conjExponent_eq_top Q s p q N g hqConjTop,
      cubeBesovOverlapDualTestSeminorm_of_conjExponent_eq_top Q s p q N g hqConjTop]
    exact cubeBesovPartialSeminormTop_le_three_rpow_mul_overlapPartialSeminormTop
      Q s hpConjPos N g
  · have hqConjReal : 1 ≤ (cubeBesovConjExponent q).toReal :=
      one_le_cubeBesovConjExponent_toReal_of_one_le q hq hqConjTop
    rw [cubeBesovDualTestSeminorm_of_conjExponent_ne_top Q s p q N g hqConjTop,
      cubeBesovOverlapDualTestSeminorm_of_conjExponent_ne_top Q s p q N g hqConjTop]
    exact cubeBesovPartialSeminorm_le_three_rpow_mul_overlapPartialSeminorm
      Q s hpConjPos hqConjReal N g

end Homogenization
