/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceCoordinateLift
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedAffineMap
/-!
# A globally positive coordinate lift of the S5 reference map

Adding the same scalar to every coordinate does not change the deviation map.  We choose a finite
vertex-wise offset large enough that the full coordinate lift is strictly positive on the entire
order-complex realization.  This gives a manifestly zero-free straight-line homotopy from the
upper child map to the reference obstruction map.
-/

@[expose] public section

namespace NRR
namespace AAK

open scoped BigOperators
open FoxNeuwirthOrderComplex

variable {p : Nat}

/-- A finite bound for all coordinates of the original reference coordinate lift at vertices. -/
noncomputable def referenceCoordinateAbsBound (hp : Nat.Prime p) : Real :=
  1 + ∑ c : BarredPermutation p, ∑ i : Fin p, |(referenceCoordinateMap hp).vertexValue c i|

theorem referenceCoordinateAbsBound_pos (hp : Nat.Prime p) :
    0 < referenceCoordinateAbsBound hp := by
  unfold referenceCoordinateAbsBound
  positivity

theorem referenceCoordinate_vertex_lt_bound
    (hp : Nat.Prime p) (c : BarredPermutation p) (i : Fin p) :
    |(referenceCoordinateMap hp).vertexValue c i| < referenceCoordinateAbsBound hp := by
  unfold referenceCoordinateAbsBound
  have hinner : |(referenceCoordinateMap hp).vertexValue c i| ≤
      ∑ i' : Fin p, |(referenceCoordinateMap hp).vertexValue c i'| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun i' : Fin p => |(referenceCoordinateMap hp).vertexValue c i'|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have houter : (∑ i' : Fin p, |(referenceCoordinateMap hp).vertexValue c i'|) ≤
      ∑ c' : BarredPermutation p, ∑ i' : Fin p,
        |(referenceCoordinateMap hp).vertexValue c' i'| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun c' : BarredPermutation p =>
        ∑ i' : Fin p, |(referenceCoordinateMap hp).vertexValue c' i'|)
      (fun c' _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ c)
  have hle := hinner.trans houter
  linarith

/-- Globally positive coordinate lift of the S5 reference deviation map. -/
noncomputable def positiveReferenceCoordinateMap
    (hp : Nat.Prime p) : CoordinateAffineVertexMap p where
  vertexValue c i :=
    (referenceCoordinateMap hp).vertexValue c i + referenceCoordinateAbsBound hp

theorem positiveReferenceCoordinateMap_vertex_pos
    (hp : Nat.Prime p) :
    ∀ c i, 0 < (positiveReferenceCoordinateMap hp).vertexValue c i := by
  intro c i
  have h := referenceCoordinate_vertex_lt_bound hp c i
  have hneg : -(referenceCoordinateAbsBound hp) <
      (referenceCoordinateMap hp).vertexValue c i := by
    exact (abs_lt.mp h).1
  simp only [positiveReferenceCoordinateMap]
  linarith

theorem positiveReferenceCoordinateMap_global_pos
    (hp : Nat.Prime p) :
    ∀ x : Realization p, ∀ i : Fin p,
      0 < (positiveReferenceCoordinateMap hp).globalValue x i := by
  intro x i
  unfold CoordinateAffineVertexMap.globalValue
  have hnonneg : ∀ c : BarredPermutation p,
      0 ≤ x c * (positiveReferenceCoordinateMap hp).vertexValue c i := by
    intro c
    exact mul_nonneg (x.nonneg c)
      (le_of_lt (positiveReferenceCoordinateMap_vertex_pos hp c i))
  have hsum : 0 < ∑ c : BarredPermutation p,
      x c * (positiveReferenceCoordinateMap hp).vertexValue c i := by
    obtain ⟨c, hc⟩ : ∃ c, 0 < x c := by
      by_contra h
      push Not at h
      have hz : ∀ c, x c = 0 := fun c => le_antisymm (h c) (x.nonneg c)
      have := x.sum_eq_one
      simp [hz] at this
    exact Finset.sum_pos' (fun c hc' => hnonneg c)
      ⟨c, Finset.mem_univ c,
        mul_pos hc (positiveReferenceCoordinateMap_vertex_pos hp c i)⟩
  exact hsum

/-- Adding a common offset leaves the deviation map unchanged. -/
theorem positiveReferenceCoordinateMap_deviation
    (hp : Nat.Prime p) :
    (positiveReferenceCoordinateMap hp).deviation hp =
      ReferenceAffineOrbitCount.referenceMap hp := by
  rw [← referenceCoordinateMap_deviation hp]
  apply congrArg (fun vertexValue : BarredPermutation p → Fin (p - 1) → ℝ =>
    ({ vertexValue := vertexValue } : AffineVertexMap p (p - 1)))
  funext c r
  simp [positiveReferenceCoordinateMap]

/-- Positive local indices of the shifted reference map equal the S5 reference indices. -/
theorem positiveReferenceIndex_eq_referenceIndex
    (hp : Nat.Prime p) :
    AffinePrismObstruction.positiveIndex hp (positiveReferenceCoordinateMap hp) =
      ReferenceAffineOrbitCount.referenceIndex hp := by
  funext q
  unfold AffinePrismObstruction.positiveIndex
  rw [CoordinateAffineVertexMap.positiveLocalZeroIndex_eq_localZeroIndex_of_vertex_pos
    hp _ (positiveReferenceCoordinateMap_vertex_pos hp)]
  rw [positiveReferenceCoordinateMap_deviation hp]
  rfl

end AAK
end NRR
