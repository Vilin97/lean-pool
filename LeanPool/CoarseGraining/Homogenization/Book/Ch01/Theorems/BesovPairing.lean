/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.CircDomination
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliBridge

/-!
# Legacy Chapter 1 Besov pairing helpers

This module contains only restricted `p = 2` totalized-real, disjoint-cube
compatibility helpers. They are not exact source pairing theorems and are
available only in `Book.Ch01.Legacy`.
-/

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal

noncomputable section

namespace Legacy

/-- Restricted `p = 2`, `q = 1` totalized-real, disjoint-cube compatibility
pairing helper; it is not an exact source pairing theorem. -/
theorem cubeBesovPairing_two_one_le_circNorm_mul_testBound {d : ℕ}
    (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) * B :=
  Homogenization.abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
    Q s u g hs hu hB hnorm hmem

/-- Restricted `p = 2`, `q = 1` totalized-real, disjoint-cube full-dual
compatibility helper; it is not an exact source pairing theorem. -/
theorem cubeBesovPairing_two_one_le_fullDualNoteRhs_mul_testBound {d : ℕ}
    (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖normalizedAverage Q u‖) * B :=
  Homogenization.abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one_of_nonneg
    Q s u g hs hu hB hnorm hmem

/-- Restricted `p = 2`, `q = 2` totalized-real, disjoint-cube full-dual
compatibility helper; it is not an exact source pairing theorem. -/
theorem cubeBesovPairing_two_two_le_fullDualNoteRhs_mul_testBound {d : ℕ}
    (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          circNegativeBesovNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖normalizedAverage Q u‖) * B :=
  Homogenization.abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two_of_nonneg
    Q s u g hs hu hB hnorm hmem

end Legacy

end

end Ch01
end Book
end Homogenization
