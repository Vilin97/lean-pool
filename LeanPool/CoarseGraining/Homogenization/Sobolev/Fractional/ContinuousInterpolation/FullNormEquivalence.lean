/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.SeminormComparison

/-!
# Additive full-norm equivalence for continuous interpolation

This module packages the approved source-facing convention: the normalized Euclidean `L²`
norm plus either the continuum interpolation seminorm or the exact Euclidean fractional
Sobolev seminorm.  The two resulting extended-valued full norms are equivalent with one
finite constant depending only on the fractional order and the dimension.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The source-facing continuum interpolation full norm: normalized Euclidean `L²` plus the
continuous `K`-seminorm. -/
noncomputable def continuousKFullENorm {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
    continuousKSeminorm s F

/-- The source-facing exact Euclidean fractional full norm: normalized Euclidean `L²` plus the
Euclidean `H^s` seminorm. -/
noncomputable def euclideanHsFullENorm {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
    euclideanHsESeminorm s F

/-- Evaluation formula for the continuous interpolation full norm. -/
theorem continuousKFullENorm_eq {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    continuousKFullENorm s F =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
        continuousKSeminorm s F :=
  rfl

/-- Evaluation formula for the exact Euclidean fractional full norm. -/
theorem euclideanHsFullENorm_eq {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    euclideanHsFullENorm s F =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
        euclideanHsESeminorm s F :=
  rfl

/-- A single constant that controls both directions of the additive full-norm comparison. -/
noncomputable def continuousKEuclideanHsFullENormConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  1 + max (continuousKToEuclideanHsSeminormConstant s d)
    (euclideanHsToContinuousKSeminormConstant s d)

/-- The common full-norm comparison constant is finite. -/
theorem continuousKEuclideanHsFullENormConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    continuousKEuclideanHsFullENormConstant s d < ∞ := by
  unfold continuousKEuclideanHsFullENormConstant
  rw [ENNReal.add_lt_top, max_lt_iff]
  exact ⟨ENNReal.one_lt_top, continuousKToEuclideanHsSeminormConstant_lt_top s d,
    euclideanHsToContinuousKSeminormConstant_lt_top s d⟩

private theorem add_mul_le_one_add_mul_of_le {A B C : ℝ≥0∞} (hAB : A ≤ B) :
    A + C * B ≤ (1 + C) * B := by
  calc
    A + C * B ≤ B + C * B := add_le_add_left hAB _
    _ = (1 + C) * B := by
      rw [add_mul]
      simp only [one_mul]

/-- The continuum interpolation full norm controls the exact Euclidean fractional full norm
with the common finite constant. -/
theorem euclideanHsFullENorm_le_mul_continuousKFullENorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsFullENorm s F ≤
      continuousKEuclideanHsFullENormConstant s d * continuousKFullENorm s F := by
  let L : ℝ≥0∞ := (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F
  let K : ℝ≥0∞ := continuousKSeminorm s F
  let H : ℝ≥0∞ := euclideanHsESeminorm s F
  let C : ℝ≥0∞ := max (continuousKToEuclideanHsSeminormConstant s d)
    (euclideanHsToContinuousKSeminormConstant s d)
  calc
    euclideanHsFullENorm s F = L + H := rfl
    _ ≤ L + euclideanHsToContinuousKSeminormConstant s d * (L + K) := by
      exact add_le_add_right
        (euclideanHsESeminorm_le_mul_normalizedEuclideanLpENorm_add_continuousKSeminorm
          s F) _
    _ ≤ L + C * (L + K) := by
      apply add_le_add_right
      exact mul_le_mul_left
        (le_max_right (continuousKToEuclideanHsSeminormConstant s d)
          (euclideanHsToContinuousKSeminormConstant s d)) _
    _ ≤ (1 + C) * (L + K) :=
      add_mul_le_one_add_mul_of_le (le_add_of_nonneg_right zero_le)
    _ = continuousKEuclideanHsFullENormConstant s d * continuousKFullENorm s F := by
      rfl

/-- The exact Euclidean fractional full norm controls the continuum interpolation full norm
with the same common finite constant. -/
theorem continuousKFullENorm_le_mul_euclideanHsFullENorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKFullENorm s F ≤
      continuousKEuclideanHsFullENormConstant s d * euclideanHsFullENorm s F := by
  let L : ℝ≥0∞ := (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F
  let K : ℝ≥0∞ := continuousKSeminorm s F
  let H : ℝ≥0∞ := euclideanHsESeminorm s F
  let C : ℝ≥0∞ := max (continuousKToEuclideanHsSeminormConstant s d)
    (euclideanHsToContinuousKSeminormConstant s d)
  calc
    continuousKFullENorm s F = L + K := rfl
    _ ≤ L + continuousKToEuclideanHsSeminormConstant s d * H := by
      exact add_le_add_right (continuousKSeminorm_le_mul_euclideanHsESeminorm s F) _
    _ ≤ L + C * H := by
      apply add_le_add_right
      exact mul_le_mul_left
        (le_max_left (continuousKToEuclideanHsSeminormConstant s d)
          (euclideanHsToContinuousKSeminormConstant s d)) _
    _ ≤ L + C * (L + H) := by
      apply add_le_add_right
      exact mul_le_mul_right (le_add_of_nonneg_left zero_le) _
    _ ≤ (1 + C) * (L + H) :=
      add_mul_le_one_add_mul_of_le (le_add_of_nonneg_right zero_le)
    _ = continuousKEuclideanHsFullENormConstant s d * euclideanHsFullENorm s F := by
      rfl

/-- Source-facing all-dimensional equivalence between the approved additive continuous
interpolation and exact Euclidean fractional full norms. -/
theorem exists_continuousKFullENorm_euclideanHsFullENorm_equivalence
    (d : ℕ) (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ F : UnitCubeEuclideanL2Field d,
      (MemEuclideanHs s F ↔ continuousKSeminorm s F < ∞) ∧
        euclideanHsFullENorm s F ≤ C * continuousKFullENorm s F ∧
          continuousKFullENorm s F ≤ C * euclideanHsFullENorm s F := by
  refine ⟨continuousKEuclideanHsFullENormConstant s d,
    continuousKEuclideanHsFullENormConstant_lt_top s d, ?_⟩
  intro F
  exact ⟨memEuclideanHs_iff_continuousKSeminorm_lt_top s F,
    euclideanHsFullENorm_le_mul_continuousKFullENorm s F,
    continuousKFullENorm_le_mul_euclideanHsFullENorm s F⟩

end

end Homogenization
