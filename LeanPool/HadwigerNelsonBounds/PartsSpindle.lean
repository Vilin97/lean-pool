/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetEmbedding
import LeanPool.HadwigerNelsonBounds.IsbellColoring

/-!
# The Parts spindle and the known bounds

Two copies of the forced distance-four pair share one endpoint.  Rotating the
second copy through cosine `31/32` makes the remaining endpoints unit-adjacent,
contradicting a proper four-coloring.
-/

namespace HadwigerNelsonBounds

/-- The distance-four vector between the translated gadget endpoints. -/
noncomputable def partsSpindleVector : R2 := partsAxialPoint 4 0

/-- Translate the first doubled patch so its left endpoint is the origin. -/
noncomputable def partsFirstSpindleMotion (p : R2) : R2 :=
  p - partsAxialPoint (-2) 0

/-- Translate the second doubled patch and rotate it around the shared origin. -/
noncomputable def partsSecondSpindleMotion (p : R2) : R2 :=
  partsSpindleRotation (p - partsAxialPoint (-2) 0)

lemma partsFirstSpindleMotion_dist_eq (p q : R2) :
    dist (partsFirstSpindleMotion p) (partsFirstSpindleMotion q) = dist p q := by
  simp [partsFirstSpindleMotion]

lemma partsSecondSpindleMotion_dist_eq (p q : R2) :
    dist (partsSecondSpindleMotion p) (partsSecondSpindleMotion q) = dist p q := by
  rw [partsSecondSpindleMotion, partsSecondSpindleMotion,
    partsSpindleRotation_dist_eq, dist_sub_right]

@[simp] lemma partsFirstSpindleMotion_left :
    partsFirstSpindleMotion (partsAxialPoint (-2) 0) = 0 := by
  simp [partsFirstSpindleMotion]

@[simp] lemma partsFirstSpindleMotion_right :
    partsFirstSpindleMotion (partsAxialPoint 2 0) = partsSpindleVector := by
  rw [partsFirstSpindleMotion, partsSpindleVector,
    ← partsAxialPoint_sub]
  norm_num

@[simp] lemma partsSecondSpindleMotion_left :
    partsSecondSpindleMotion (partsAxialPoint (-2) 0) = 0 := by
  simp [partsSecondSpindleMotion]

@[simp] lemma partsSecondSpindleMotion_right :
    partsSecondSpindleMotion (partsAxialPoint 2 0) =
      partsSpindleRotation partsSpindleVector := by
  rw [partsSecondSpindleMotion, partsSpindleVector,
    ← partsAxialPoint_sub]
  norm_num

lemma partsSpindleVector_norm_sq : dist partsSpindleVector 0 ^ 2 = 16 := by
  rw [partsSpindleVector, ← partsAxialPoint_zero,
    partsAxialPoint_dist_sq]
  norm_num

/-- The two free spindle endpoints are exactly one unit apart. -/
lemma partsSpindleVector_rotated_dist :
    dist partsSpindleVector (partsSpindleRotation partsSpindleVector) = 1 := by
  have hsq :
      dist partsSpindleVector (partsSpindleRotation partsSpindleVector) ^ 2 =
        1 := by
    rw [partsSpindleRotation_displacement_sq, partsSpindleVector_norm_sq]
    norm_num
  have hnonneg : 0 ≤
      dist partsSpindleVector (partsSpindleRotation partsSpindleVector) :=
    dist_nonneg
  nlinarith

/-- **Parts lower bound.** The unit-distance graph of the Euclidean plane has
no proper coloring with four colors. -/
theorem unitDistanceGraph_not_colorable_four :
    ¬ unitDistanceGraph.Colorable 4 := by
  rintro ⟨planeColoring⟩
  have hfirst := parts_axial_pair_forces_under_motion planeColoring
    partsFirstSpindleMotion partsFirstSpindleMotion_dist_eq
  have hsecond := parts_axial_pair_forces_under_motion planeColoring
    partsSecondSpindleMotion partsSecondSpindleMotion_dist_eq
  simp only [partsFirstSpindleMotion_left, partsFirstSpindleMotion_right] at hfirst
  simp only [partsSecondSpindleMotion_left,
    partsSecondSpindleMotion_right] at hsecond
  have hsame : planeColoring partsSpindleVector =
      planeColoring (partsSpindleRotation partsSpindleVector) :=
    hfirst.symm.trans hsecond
  have hadj : unitDistanceGraph.Adj partsSpindleVector
      (partsSpindleRotation partsSpindleVector) := by
    rw [unitDistanceGraph_adj]
    constructor
    · intro hpoints
      have hzero : dist partsSpindleVector
          (partsSpindleRotation partsSpindleVector) = 0 := by
        exact dist_eq_zero.mpr hpoints
      linarith [partsSpindleVector_rotated_dist]
    · exact Or.inl partsSpindleVector_rotated_dist
  exact planeColoring.valid hadj hsame

/-- **Lower bound — `5 ≤ χ(ℝ²)`.** -/
theorem five_le_chromaticNumber :
    (5 : ℕ∞) ≤ unitDistanceGraph.chromaticNumber := by
  apply SimpleGraph.le_chromaticNumber_iff_colorable.2
  intro colors hcolorable
  norm_cast
  by_contra hnot
  have hle : colors ≤ 4 := by omega
  exact unitDistanceGraph_not_colorable_four (hcolorable.mono hle)

/-- **Known bounds for the Hadwiger--Nelson problem:**
`5 ≤ χ(ℝ²) ≤ 7`. -/
theorem hadwiger_nelson_known_bounds :
    (5 : ℕ∞) ≤ unitDistanceGraph.chromaticNumber ∧
      unitDistanceGraph.chromaticNumber ≤ (7 : ℕ∞) := by
  exact ⟨five_le_chromaticNumber,
    SimpleGraph.chromaticNumber_le_iff_colorable.2 chromaticNumber_le_seven⟩

end HadwigerNelsonBounds
