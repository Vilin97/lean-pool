/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsPlaneGeometry
import LeanPool.HadwigerNelsonBounds.PartsGadgetData

/-!
# Euclidean realization of the finite Parts gadget

The 73 descriptors encode two radius-three triangular-lattice patches with a
common center.  The second patch is rotated through cosine `7/8`.
-/

namespace HadwigerNelsonBounds

/-- The integral quadratic norm of an axial lattice vector. -/
def partsAxialNormSq (q r : ℤ) : ℤ := q ^ 2 + q * r + r ^ 2

/-- Whether a descriptor is the common center of both patches. -/
def PartsGadgetVertex.IsCenter (vertex : PartsGadgetVertex) : Prop :=
  vertex.q = 0 ∧ vertex.r = 0

instance (vertex : PartsGadgetVertex) : Decidable vertex.IsCenter := by
  unfold PartsGadgetVertex.IsCenter
  infer_instance

/-- Arithmetic classification of every unit edge in the gadget. -/
def PartsGadgetEdgeCase (left right : Fin 73) : Prop :=
  let leftData := partsGadgetVertex left
  let rightData := partsGadgetVertex right
  ((leftData.rotated = rightData.rotated ∨
        leftData.IsCenter ∨ rightData.IsCenter) ∧
      partsAxialNormSq (leftData.q - rightData.q)
        (leftData.r - rightData.r) = 1) ∨
    (leftData.rotated ≠ rightData.rotated ∧
      leftData.q = rightData.q ∧ leftData.r = rightData.r ∧
      partsAxialNormSq leftData.q leftData.r = 4)

instance (left right : Fin 73) : Decidable (PartsGadgetEdgeCase left right) := by
  unfold PartsGadgetEdgeCase
  infer_instance

/-- Explicit point of the doubled triangular-lattice patch. -/
noncomputable def partsGadgetPoint (vertex : Fin 73) : R2 :=
  let descriptor := partsGadgetVertex vertex
  partsApplyPatch descriptor.rotated
    (partsAxialPoint descriptor.q descriptor.r)

lemma partsGadgetPoint_eq_of_axialAt {rotated : Bool} {q r : ℤ}
    {vertex : Fin 73} (hposition : partsGadgetAxialAt rotated q r vertex) :
    partsGadgetPoint vertex = partsApplyPatch rotated (partsAxialPoint q r) := by
  simp only [partsGadgetAxialAt] at hposition
  rcases hposition with ⟨hq, hr, hpatch | hcenter⟩
  · simp [partsGadgetPoint, hq, hr, hpatch]
  · rcases hcenter with ⟨rfl, rfl⟩
    simp [partsGadgetPoint, hq, hr]

private lemma partsGadgetPoint_dist_eq_one_of_samePatch
    {left right : Fin 73}
    (hpatch :
      (partsGadgetVertex left).rotated =
          (partsGadgetVertex right).rotated ∨
        (partsGadgetVertex left).IsCenter ∨
        (partsGadgetVertex right).IsCenter)
    (hnorm :
      partsAxialNormSq
          ((partsGadgetVertex left).q - (partsGadgetVertex right).q)
          ((partsGadgetVertex left).r - (partsGadgetVertex right).r) = 1) :
    dist (partsGadgetPoint left) (partsGadgetPoint right) = 1 := by
  rcases hpatch with hsame | hleft | hright
  · have hleftAt : partsGadgetAxialAt
        (partsGadgetVertex left).rotated
        (partsGadgetVertex left).q (partsGadgetVertex left).r left := by
      simp [partsGadgetAxialAt]
    have hrightAt : partsGadgetAxialAt
        (partsGadgetVertex left).rotated
        (partsGadgetVertex right).q (partsGadgetVertex right).r right := by
      simp [partsGadgetAxialAt, hsame]
    rw [partsGadgetPoint_eq_of_axialAt hleftAt,
      partsGadgetPoint_eq_of_axialAt hrightAt,
      partsApplyPatch_dist_eq]
    apply partsAxialPoint_dist_eq_one
    simpa [partsAxialNormSq] using hnorm
  · have hleftAt : partsGadgetAxialAt
        (partsGadgetVertex right).rotated
        (partsGadgetVertex left).q (partsGadgetVertex left).r left := by
      simp only [partsGadgetAxialAt]
      exact ⟨True.intro, True.intro, Or.inr hleft⟩
    have hrightAt : partsGadgetAxialAt
        (partsGadgetVertex right).rotated
        (partsGadgetVertex right).q (partsGadgetVertex right).r right := by
      simp [partsGadgetAxialAt]
    rw [partsGadgetPoint_eq_of_axialAt hleftAt,
      partsGadgetPoint_eq_of_axialAt hrightAt,
      partsApplyPatch_dist_eq]
    apply partsAxialPoint_dist_eq_one
    simpa [partsAxialNormSq] using hnorm
  · have hleftAt : partsGadgetAxialAt
        (partsGadgetVertex left).rotated
        (partsGadgetVertex left).q (partsGadgetVertex left).r left := by
      simp [partsGadgetAxialAt]
    have hrightAt : partsGadgetAxialAt
        (partsGadgetVertex left).rotated
        (partsGadgetVertex right).q (partsGadgetVertex right).r right := by
      simp only [partsGadgetAxialAt]
      exact ⟨True.intro, True.intro, Or.inr hright⟩
    rw [partsGadgetPoint_eq_of_axialAt hleftAt,
      partsGadgetPoint_eq_of_axialAt hrightAt,
      partsApplyPatch_dist_eq]
    apply partsAxialPoint_dist_eq_one
    simpa [partsAxialNormSq] using hnorm

private lemma partsPatchRotation_dist_eq_one_of_norm_four {q r : ℤ}
    (hnorm : partsAxialNormSq q r = 4) :
    dist (partsAxialPoint q r)
      (partsPatchRotation (partsAxialPoint q r)) = 1 := by
  have hzero : dist (partsAxialPoint q r) 0 ^ 2 = 4 := by
    rw [← partsAxialPoint_zero, partsAxialPoint_dist_sq]
    norm_num
    exact_mod_cast hnorm
  have hsq : dist (partsAxialPoint q r)
      (partsPatchRotation (partsAxialPoint q r)) ^ 2 = 1 := by
    rw [partsPatchRotation_displacement_sq, hzero]
    norm_num
  have hnonneg : 0 ≤ dist (partsAxialPoint q r)
      (partsPatchRotation (partsAxialPoint q r)) := dist_nonneg
  nlinarith

private lemma partsGadgetPoint_dist_eq_one_of_crossPatch
    {left right : Fin 73}
    (hrotated : (partsGadgetVertex left).rotated ≠
      (partsGadgetVertex right).rotated)
    (hq : (partsGadgetVertex left).q = (partsGadgetVertex right).q)
    (hr : (partsGadgetVertex left).r = (partsGadgetVertex right).r)
    (hnorm : partsAxialNormSq (partsGadgetVertex left).q
      (partsGadgetVertex left).r = 4) :
    dist (partsGadgetPoint left) (partsGadgetPoint right) = 1 := by
  have hleftAt : partsGadgetAxialAt
      (partsGadgetVertex left).rotated
      (partsGadgetVertex left).q (partsGadgetVertex left).r left := by
    simp [partsGadgetAxialAt]
  have hrightAt : partsGadgetAxialAt
      (partsGadgetVertex right).rotated
      (partsGadgetVertex right).q (partsGadgetVertex right).r right := by
    simp [partsGadgetAxialAt]
  rw [partsGadgetPoint_eq_of_axialAt hleftAt,
    partsGadgetPoint_eq_of_axialAt hrightAt]
  have hdisplacement := partsPatchRotation_dist_eq_one_of_norm_four hnorm
  cases hleft : (partsGadgetVertex left).rotated <;>
    cases hright : (partsGadgetVertex right).rotated
  · exact (hrotated (by simp [hleft, hright])).elim
  · simpa [partsApplyPatch, hleft, hright, hq, hr] using hdisplacement
  · simpa [partsApplyPatch, hleft, hright, hq, hr, dist_comm] using
      hdisplacement
  · exact (hrotated (by simp [hleft, hright])).elim

/-- Every arithmetically classified gadget edge has Euclidean length one. -/
theorem partsGadgetPoint_dist_eq_one_of_edgeCase {left right : Fin 73}
    (hedge : PartsGadgetEdgeCase left right) :
    dist (partsGadgetPoint left) (partsGadgetPoint right) = 1 := by
  simp only [PartsGadgetEdgeCase] at hedge
  rcases hedge with ⟨hpatch, hnorm⟩ | ⟨hrotated, hq, hr, hnorm⟩
  · exact partsGadgetPoint_dist_eq_one_of_samePatch hpatch hnorm
  · exact partsGadgetPoint_dist_eq_one_of_crossPatch hrotated hq hr hnorm

lemma PartsGadgetTriangleWitnessData.point_a_eq
    {witness : PartsGadgetTriangleWitnessData} {root : Fin 73}
    (hvalid : witness.Valid root) :
    partsGadgetPoint witness.a =
      partsTriangleMotion witness.rotated witness.centerQ witness.centerR
        witness.negated partsTriangleA := by
  rw [partsGadgetPoint_eq_of_axialAt hvalid.2.1]
  exact (partsTriangleMotion_A _ _ _ _).symm

lemma PartsGadgetTriangleWitnessData.point_b_eq
    {witness : PartsGadgetTriangleWitnessData} {root : Fin 73}
    (hvalid : witness.Valid root) :
    partsGadgetPoint witness.b =
      partsTriangleMotion witness.rotated witness.centerQ witness.centerR
        witness.negated partsTriangleB := by
  rw [partsGadgetPoint_eq_of_axialAt hvalid.2.2.1]
  exact (partsTriangleMotion_B _ _ _ _).symm

lemma PartsGadgetTriangleWitnessData.point_c_eq
    {witness : PartsGadgetTriangleWitnessData} {root : Fin 73}
    (hvalid : witness.Valid root) :
    partsGadgetPoint witness.c =
      partsTriangleMotion witness.rotated witness.centerQ witness.centerR
        witness.negated partsTriangleC := by
  rw [partsGadgetPoint_eq_of_axialAt hvalid.2.2.2]
  exact (partsTriangleMotion_C _ _ _ _).symm

lemma partsGadgetWitness_roles_not_monochromatic
    (planeColoring : unitDistanceGraph.Coloring (Fin 4))
    {witness : PartsGadgetTriangleWitnessData} {root : Fin 73}
    (hvalid : witness.Valid root) :
    ¬(planeColoring (partsGadgetPoint witness.a) =
        planeColoring (partsGadgetPoint witness.b) ∧
      planeColoring (partsGadgetPoint witness.b) =
        planeColoring (partsGadgetPoint witness.c)) := by
  rw [PartsGadgetTriangleWitnessData.point_a_eq hvalid,
    PartsGadgetTriangleWitnessData.point_b_eq hvalid,
    PartsGadgetTriangleWitnessData.point_c_eq hvalid]
  exact parts_triangle_motion_not_monochromatic planeColoring _ _ _ _

lemma partsGadget_monochromatic_of_sameTriple
    (coloring : Fin 73 → Fin 4) {a b c x y z : Fin 73}
    (hsame : partsGadgetSameTriple a b c x y z)
    (hmono : coloring x = coloring y ∧ coloring y = coloring z) :
    coloring a = coloring b ∧ coloring b = coloring c := by
  simp only [partsGadgetSameTriple] at hsame
  rcases hsame with h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl⟩ <;> simp_all

end HadwigerNelsonBounds
