/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableObstructionCount

/-!
# Endpoint homotopies for the child-coordinate family

At the lower endpoint every child coordinate is negative, and at the upper endpoint every child
coordinate is positive.  Hence the straight-line segments to the corresponding shifted S5
reference lifts remain in the negative and positive orthants, respectively.
-/

namespace NRR

open Geometry

namespace FoxNeuwirthOrderComplex
namespace EquivariantCoordinateHomotopy

variable {p : Nat}

/-- The full child coordinate map is pointwise negative at the lower endpoint. -/
theorem childMap_left_neg
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    ∀ x : Realization p, ∀ i : Fin p,
      childMap hp hA phi (C, SignedInterval.left) x i < 0 := by
  intro x i
  exact phi.eval_left_neg _

/-- The full child coordinate map is pointwise positive at the upper endpoint. -/
theorem childMap_right_pos
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    ∀ x : Realization p, ∀ i : Fin p,
      0 < childMap hp hA phi (C, SignedInterval.right) x i := by
  intro x i
  exact phi.eval_right_pos _

/-- A convex combination of two coordinatewise-negative vectors is nonzero. -/
theorem segment_ne_zero_of_coordinatewise_neg
    (hp : Nat.Prime p) {v w : Fin p → Real}
    (hv : ∀ i, v i < 0) (hw : ∀ i, w i < 0)
    (t : Set.Icc (0 : Real) 1) :
    (1 - t.1) • v + t.1 • w ≠ 0 := by
  intro hzero
  let i : Fin p := ⟨0, hp.pos⟩
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have hcoord : ((1 - t.1) • v + t.1 • w) i < 0 := by
    change (1 - t.1) * v i + t.1 * w i < 0
    by_cases ht : t.1 = 0
    · rw [ht]
      simpa using hv i
    · by_cases ht' : t.1 = 1
      · rw [ht']
        simpa using hw i
      · have h0 : 0 < t.1 := lt_of_le_of_ne ht0 (Ne.symm ht)
        have h1 : 0 < 1 - t.1 := sub_pos.mpr (lt_of_le_of_ne ht1 ht')
        exact add_neg (mul_neg_of_pos_of_neg h1 (hv i))
          (mul_neg_of_pos_of_neg h0 (hw i))
  have hi := congrFun hzero i
  simp only [Pi.zero_apply] at hi
  linarith

/-- A convex combination of two coordinatewise-positive vectors is nonzero. -/
theorem segment_ne_zero_of_coordinatewise_pos
    (hp : Nat.Prime p) {v w : Fin p → Real}
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (t : Set.Icc (0 : Real) 1) :
    (1 - t.1) • v + t.1 • w ≠ 0 := by
  intro hzero
  let i : Fin p := ⟨0, hp.pos⟩
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have hcoord : 0 < ((1 - t.1) • v + t.1 • w) i := by
    change 0 < (1 - t.1) * v i + t.1 * w i
    by_cases ht : t.1 = 0
    · rw [ht]
      simpa using hv i
    · by_cases ht' : t.1 = 1
      · rw [ht']
        simpa using hw i
      · have h0 : 0 < t.1 := lt_of_le_of_ne ht0 (Ne.symm ht)
        have h1 : 0 < 1 - t.1 := sub_pos.mpr (lt_of_le_of_ne ht1 ht')
        exact add_pos (mul_pos h1 (hv i)) (mul_pos h0 (hw i))
  have hi := congrFun hzero i
  simp only [Pi.zero_apply] at hi
  linarith

/-- Lower child map to negative shifted reference. -/
noncomputable def childLeftToNegativeReference
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    ZeroFreeHomotopy hp
      (childZeroFreeMap hp hA phi (C, SignedInterval.left)
        ((orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_left hA phi C))
      (EquivariantPLPositiveRay.negativeReferenceZeroFreeMap hp) :=
  ZeroFreeHomotopy.segment _ _ (by
    intro x t
    exact segment_ne_zero_of_coordinatewise_neg
      hp (childMap_left_neg hp hA phi C x)
      (AAK.negativeEquivariantReferenceCoordinateMap_global_neg hp x) t)

/-- Upper child map to positive shifted reference. -/
noncomputable def childRightToPositiveReference
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    ZeroFreeHomotopy hp
      (childZeroFreeMap hp hA phi (C, SignedInterval.right)
        ((orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_right hA phi C))
      (EquivariantPLPositiveRay.positiveReferenceZeroFreeMap hp) :=
  ZeroFreeHomotopy.segment _ _ (by
    intro x t
    exact segment_ne_zero_of_coordinatewise_pos
      hp (childMap_right_pos hp hA phi C x)
      (AAK.positiveEquivariantReferenceCoordinateMap_global_pos hp x) t)

end EquivariantCoordinateHomotopy
end FoxNeuwirthOrderComplex
end NRR
