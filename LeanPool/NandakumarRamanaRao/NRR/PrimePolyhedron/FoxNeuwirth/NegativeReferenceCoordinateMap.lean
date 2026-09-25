/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.PositiveReferenceCoordinateMap
/-!
# A globally negative coordinate lift of the S5 reference map

Subtracting a common scalar from every coordinate does not change the deviation map.  The
negative lift is used as the lower-end comparison map in S6.  Its positive-ray count is zero,
while its deviation map remains the regular S5 reference map.
-/

@[expose] public section

namespace NRR
namespace AAK

open FoxNeuwirthOrderComplex

variable {p : Nat}

/-- Globally negative coordinate lift of the S5 reference deviation map. -/
noncomputable def negativeReferenceCoordinateMap
    (hp : Nat.Prime p) : CoordinateAffineVertexMap p where
  vertexValue c i :=
    (referenceCoordinateMap hp).vertexValue c i - referenceCoordinateAbsBound hp

theorem negativeReferenceCoordinateMap_vertex_neg
    (hp : Nat.Prime p) :
    ∀ c i, (negativeReferenceCoordinateMap hp).vertexValue c i < 0 := by
  intro c i
  have h := referenceCoordinate_vertex_lt_bound hp c i
  exact sub_neg.mpr (lt_of_le_of_lt (le_abs_self _) h)

theorem negativeReferenceCoordinateMap_global_neg
    (hp : Nat.Prime p) :
    ∀ x : Realization p, ∀ i : Fin p,
      (negativeReferenceCoordinateMap hp).globalValue x i < 0 := by
  intro x i
  unfold CoordinateAffineVertexMap.globalValue
  have hnonpos : ∀ c : BarredPermutation p,
      x c * (negativeReferenceCoordinateMap hp).vertexValue c i ≤ 0 := by
    intro c
    exact mul_nonpos_of_nonneg_of_nonpos (x.nonneg c)
      (le_of_lt (negativeReferenceCoordinateMap_vertex_neg hp c i))
  obtain ⟨c, hc⟩ : ∃ c, 0 < x c := by
    by_contra h
    push Not at h
    have hz : ∀ c, x c = 0 := fun c => le_antisymm (h c) (x.nonneg c)
    have hx := x.sum_eq_one
    simp [hz] at hx
  have hstrict : x c * (negativeReferenceCoordinateMap hp).vertexValue c i < 0 :=
    mul_neg_of_pos_of_neg hc (negativeReferenceCoordinateMap_vertex_neg hp c i)
  exact Finset.sum_neg' (fun c _ => hnonpos c) ⟨c, by simpa using hstrict⟩

/-- Subtracting a common offset leaves the deviation map unchanged. -/
theorem negativeReferenceCoordinateMap_deviation
    (hp : Nat.Prime p) :
    (negativeReferenceCoordinateMap hp).deviation hp =
      ReferenceAffineOrbitCount.referenceMap hp := by
  rw [← referenceCoordinateMap_deviation hp]
  apply congrArg (fun vertexValue : BarredPermutation p → Fin (p - 1) → ℝ =>
    ({ vertexValue := vertexValue } : AffineVertexMap p (p - 1)))
  funext c r
  simp [negativeReferenceCoordinateMap]

/-- The negative reference has zero positive local-index cochain. -/
theorem negativeReferencePositiveIndex_eq_zero
    (hp : Nat.Prime p) :
    AffinePrismObstruction.positiveIndex hp (negativeReferenceCoordinateMap hp) = 0 := by
  funext q
  exact CoordinateAffineVertexMap.positiveLocalZeroIndex_eq_zero_of_vertex_neg
    hp _ (negativeReferenceCoordinateMap_vertex_neg hp) _

end AAK
end NRR
