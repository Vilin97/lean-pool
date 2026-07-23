/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.Basic

/-!
# Voronoi quadratic-form bounds

This module proves that one of the four corners of a lattice-coordinate unit
square lies within the required quadratic-form radius.
-/

namespace HadwigerNelsonBounds

private lemma cornerZeroZero_le_third {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hFirst : 2 * α + β ≤ 1) (hSecond : α + 2 * β ≤ 1) :
    α ^ 2 + α * β + β ^ 2 ≤ 1 / 3 :=
  Q_le_third_origin hα hβ hFirst hSecond

private lemma cornerZeroOne_lower_le_third {α β : ℝ}
    (hα : 0 ≤ α) (hDiagonal : α + β ≤ 1)
    (hFront : 1 ≤ α + 2 * β)
    (hOrder : α ≤ β) :
    α ^ 2 + α * (β - 1) + (β - 1) ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      α ^ 2 + α * (β - 1) + (β - 1) ^ 2 =
        (1 - α - β) ^ 2 + (1 - α - β) * α + α ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerOneZero_lower_le_third {α β : ℝ}
    (hβ : 0 ≤ β) (hDiagonal : α + β ≤ 1)
    (hFront : 1 ≤ 2 * α + β)
    (hOrder : β ≤ α) :
    (α - 1) ^ 2 + (α - 1) * β + β ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      (α - 1) ^ 2 + (α - 1) * β + β ^ 2 =
        β ^ 2 + β * (1 - α - β) + (1 - α - β) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerOneOne_le_third {α β : ℝ}
    (hα : α < 1) (hβ : β < 1)
    (hFirst : 2 ≤ 2 * α + β) (hSecond : 2 ≤ α + 2 * β) :
    (α - 1) ^ 2 + (α - 1) * (β - 1) + (β - 1) ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      (α - 1) ^ 2 + (α - 1) * (β - 1) + (β - 1) ^ 2 =
        (1 - α) ^ 2 + (1 - α) * (1 - β) + (1 - β) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerOneZero_upper_le_third {α β : ℝ}
    (hDiagonal : 1 ≤ α + β) (hα : α < 1)
    (hBack : α + 2 * β ≤ 2) (hOrder : β ≤ α) :
    (α - 1) ^ 2 + (α - 1) * β + β ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      (α - 1) ^ 2 + (α - 1) * β + β ^ 2 =
        (α + β - 1) ^ 2 + (α + β - 1) * (1 - α) + (1 - α) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

private lemma cornerZeroOne_upper_le_third {α β : ℝ}
    (hDiagonal : 1 ≤ α + β) (hβ : β < 1)
    (hOrder : α ≤ β) (hBack : 2 * α + β ≤ 2) :
    α ^ 2 + α * (β - 1) + (β - 1) ^ 2 ≤ 1 / 3 := by
  have hIdentity :
      α ^ 2 + α * (β - 1) + (β - 1) ^ 2 =
        (1 - β) ^ 2 + (1 - β) * (α + β - 1) + (α + β - 1) ^ 2 := by
    ring
  rw [hIdentity]
  apply Q_le_third_origin
  · linarith
  · linarith
  · linarith
  · linarith

/-- Every point of the half-open lattice-coordinate unit square lies within
quadratic-form radius 1 / 3 of one of its four corners. -/
lemma unitSquare_has_near_lattice_corner {α β : ℝ}
    (hαLower : 0 ≤ α) (hαUpper : α < 1)
    (hβLower : 0 ≤ β) (hβUpper : β < 1) :
    ∃ Δi Δj : ℤ,
      (α - (Δi : ℝ)) ^ 2 +
        (α - (Δi : ℝ)) * (β - (Δj : ℝ)) +
        (β - (Δj : ℝ)) ^ 2 ≤ 1 / 3 := by
  by_cases hFirst : 2 * α + β ≤ 1
  · by_cases hSecond : α + 2 * β ≤ 1
    · refine ⟨0, 0, ?_⟩
      simpa using
        cornerZeroZero_le_third hαLower hβLower hFirst hSecond
    · have hSecond' : 1 ≤ α + 2 * β := le_of_lt (not_le.mp hSecond)
      have hDiagonal : α + β ≤ 1 := by linarith
      have hOrder : α ≤ β := by linarith
      refine ⟨0, 1, ?_⟩
      simpa using
        cornerZeroOne_lower_le_third
          hαLower hDiagonal hSecond' hOrder
  · have hFirst' : 1 ≤ 2 * α + β := le_of_lt (not_le.mp hFirst)
    by_cases hTop : 2 ≤ 2 * α + β
    · by_cases hTopSecond : 2 ≤ α + 2 * β
      · refine ⟨1, 1, ?_⟩
        simpa using
          cornerOneOne_le_third hαUpper hβUpper hTop hTopSecond
      · have hTopSecond' : α + 2 * β ≤ 2 :=
          le_of_lt (not_le.mp hTopSecond)
        have hDiagonal : 1 ≤ α + β := by linarith
        have hOrder : β ≤ α := by linarith
        refine ⟨1, 0, ?_⟩
        simpa using
          cornerOneZero_upper_le_third
            hDiagonal hαUpper hTopSecond' hOrder
    · have hTop' : 2 * α + β ≤ 2 := le_of_lt (not_le.mp hTop)
      by_cases hDiagonal : α + β ≤ 1
      · by_cases hSecond : α + 2 * β ≤ 1
        · have hOrder : β ≤ α := by linarith
          refine ⟨1, 0, ?_⟩
          simpa using
            cornerOneZero_lower_le_third
              hβLower hDiagonal hFirst' hOrder
        · have hSecond' : 1 ≤ α + 2 * β :=
            le_of_lt (not_le.mp hSecond)
          by_cases hOrder : β ≤ α
          · refine ⟨1, 0, ?_⟩
            simpa using
              cornerOneZero_lower_le_third
                hβLower hDiagonal hFirst' hOrder
          · have hOrder' : α ≤ β := le_of_lt (not_le.mp hOrder)
            refine ⟨0, 1, ?_⟩
            simpa using
              cornerZeroOne_lower_le_third
                hαLower hDiagonal hSecond' hOrder'
      · have hDiagonal' : 1 ≤ α + β :=
          le_of_lt (not_le.mp hDiagonal)
        by_cases hOrder : β ≤ α
        · have hBack : α + 2 * β ≤ 2 := by linarith
          refine ⟨1, 0, ?_⟩
          simpa using
            cornerOneZero_upper_le_third
              hDiagonal' hαUpper hBack hOrder
        · have hOrder' : α ≤ β := le_of_lt (not_le.mp hOrder)
          refine ⟨0, 1, ?_⟩
          simpa using
            cornerZeroOne_upper_le_third
              hDiagonal' hβUpper hOrder' hTop'

end HadwigerNelsonBounds
