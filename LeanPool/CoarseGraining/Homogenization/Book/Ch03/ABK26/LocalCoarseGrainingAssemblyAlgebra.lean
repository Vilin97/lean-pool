/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingAggregation

/-!
# Finite-`p` algebra for local coarse-graining assembly

This module records the outer finite descendant-average triangle estimate in
the literal `ENNReal` carrier used by the local coarse-graining definitions.
It is independent of the PDE and response inputs.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped ENNReal

noncomputable section

/-- The finite outer descendant average obeys the powered two-term triangle
inequality.  This is the algebraic form used before taking the single outer
finite-`p` root in the local coarse-graining assembly. -/
theorem descendantsAtScaleENNAverage_rpow_add_le {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) {r : ℝ} (hr : 1 ≤ r)
    (F G : TriadicCube d → ℝ≥0∞) :
    descendantsAtScaleENNAverage Q k (fun R => (F R + G R) ^ r) ≤
      (2 : ℝ≥0∞) ^ (r - 1) *
        (descendantsAtScaleENNAverage Q k (fun R => (F R) ^ r) +
          descendantsAtScaleENNAverage Q k (fun R => (G R) ^ r)) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtScale Q k
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (r - 1)
  have hpoint : ∀ R ∈ D, (F R + G R) ^ r ≤ C * ((F R) ^ r + (G R) ^ r) := by
    intro R hR
    exact ENNReal.rpow_add_le_mul_rpow_add_rpow (F R) (G R) hr
  have hsum :
      ∑ R ∈ D, (F R + G R) ^ r ≤
        ∑ R ∈ D, C * ((F R) ^ r + (G R) ^ r) := by
    exact Finset.sum_le_sum fun R hR => hpoint R (by simpa [D] using hR)
  unfold descendantsAtScaleENNAverage
  change
    (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (F R + G R) ^ r ≤
      C * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (F R) ^ r +
        (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (G R) ^ r)
  calc
    (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (F R + G R) ^ r ≤
        (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, C * ((F R) ^ r + (G R) ^ r) :=
      mul_le_mul_right hsum _
    _ = C * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (F R) ^ r +
        (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (G R) ^ r) := by
      calc
        (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, C * ((F R) ^ r + (G R) ^ r) =
            ∑ R ∈ D, ((D.card : ℝ≥0∞)⁻¹ * C) * ((F R) ^ r + (G R) ^ r) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro R hR
              ring
        _ = ((D.card : ℝ≥0∞)⁻¹ * C) *
            (∑ R ∈ D, (F R) ^ r + ∑ R ∈ D, (G R) ^ r) := by
              calc
                ∑ R ∈ D, ((D.card : ℝ≥0∞)⁻¹ * C) * ((F R) ^ r + (G R) ^ r) =
                    ∑ R ∈ D, (((D.card : ℝ≥0∞)⁻¹ * C) * (F R) ^ r +
                      ((D.card : ℝ≥0∞)⁻¹ * C) * (G R) ^ r) := by
                      apply Finset.sum_congr rfl
                      intro R hR
                      ring
                _ = ∑ R ∈ D, ((D.card : ℝ≥0∞)⁻¹ * C) * (F R) ^ r +
                    ∑ R ∈ D, ((D.card : ℝ≥0∞)⁻¹ * C) * (G R) ^ r := by
                      rw [Finset.sum_add_distrib]
                _ = ((D.card : ℝ≥0∞)⁻¹ * C) *
                    (∑ R ∈ D, (F R) ^ r + ∑ R ∈ D, (G R) ^ r) := by
                      rw [← Finset.mul_sum, ← Finset.mul_sum]
                      ring
        _ = C * ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (F R) ^ r +
            (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, (G R) ^ r) := by ring

/-- After the outer finite-`p` root, the preceding two-term descendant-average
triangle loss is the uniform constant `2`. -/
theorem descendantsAtScaleENNAverage_rpow_add_root_le_two_mul {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) {r : ℝ} (hr : 1 ≤ r)
    (F G : TriadicCube d → ℝ≥0∞) :
    (descendantsAtScaleENNAverage Q k (fun R => (F R + G R) ^ r)) ^ r⁻¹ ≤
      2 * (descendantsAtScaleENNAverage Q k (fun R => (F R) ^ r) +
        descendantsAtScaleENNAverage Q k (fun R => (G R) ^ r)) ^ r⁻¹ := by
  let A : ℝ≥0∞ := descendantsAtScaleENNAverage Q k (fun R => (F R + G R) ^ r)
  let B : ℝ≥0∞ := descendantsAtScaleENNAverage Q k (fun R => (F R) ^ r) +
    descendantsAtScaleENNAverage Q k (fun R => (G R) ^ r)
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr_pos.le
  have hpower : A ≤ (2 : ℝ≥0∞) ^ (r - 1) * B := by
    dsimp [A, B]
    exact descendantsAtScaleENNAverage_rpow_add_le Q k hr F G
  have hexp : (r - 1) * r⁻¹ ≤ 1 := by
    calc
      (r - 1) * r⁻¹ = 1 - r⁻¹ := by field_simp [hr_pos.ne']
      _ ≤ 1 := sub_le_self _ hinv
  have htwo : (2 : ℝ≥0∞) ^ ((r - 1) * r⁻¹) ≤ 2 :=
    (ENNReal.rpow_le_rpow_of_exponent_le (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hexp).trans_eq
      (ENNReal.rpow_one _)
  calc
    A ^ r⁻¹ ≤ ((2 : ℝ≥0∞) ^ (r - 1) * B) ^ r⁻¹ :=
      ENNReal.rpow_le_rpow hpower hinv
    _ = (2 : ℝ≥0∞) ^ ((r - 1) * r⁻¹) * B ^ r⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hinv, ← ENNReal.rpow_mul]
    _ ≤ 2 * B ^ r⁻¹ := mul_le_mul_left htwo _

end

end ABK26
end Ch03
end Book
end Homogenization
