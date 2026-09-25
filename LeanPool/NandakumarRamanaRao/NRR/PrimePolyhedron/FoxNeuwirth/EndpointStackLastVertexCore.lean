/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionOneStepCells
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionZeroFreeApproximation
/-!
# Local last-vertex retraction for endpoint subdivision cylinders

This file proves the simplex-local geometric core needed by the endpoint-stack construction.
For a point of a standard simplex, `lastSupportIndex` is the largest vertex index carrying a
nonzero barycentric coordinate.  Applied to every vertex of the recursive one-step cylinder, it
selects a coarse endpoint vertex.  Pushing barycentric weights through this finite selector gives
an explicit coarse-simplex barycentric point.  Consequently every affine combination of selected
endpoint values is exactly a value of the supplied endpoint PL approximation and is therefore
zero-free.

The global descent condition requires these local choices to agree for occurrences of the same
geometric stack vertex in different refined top cells. This overlap compatibility yields an
`Assignment` on the quotient of global collar vertices.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace EndpointStackLastVertexCore

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap


variable {p d : Nat}

/-- Nonzero barycentric-coordinate support of a point of the standard simplex. -/
noncomputable def deltaSupport (x : Delta d) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i => x i ≠ 0

@[simp] theorem mem_deltaSupport_iff (x : Delta d) (i : Fin (d + 1)) :
    i ∈ deltaSupport x ↔ x i ≠ 0 := by
  simp [deltaSupport]

/-- A standard-simplex point has nonempty coordinate support. -/
theorem deltaSupport_nonempty (x : Delta d) : (deltaSupport x).Nonempty := by
  by_contra h
  have hempty : deltaSupport x = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hzero : ∀ i : Fin (d + 1), x i = 0 := by
    intro i
    by_contra hi
    have : i ∈ deltaSupport x := (mem_deltaSupport_iff x i).2 hi
    simpa [hempty] using this
  have hsum := SphereOddDegree.FiniteSimplex.sum_eq_one x
  simpa [hzero] using hsum

/-- Largest index in the nonzero barycentric support. -/
noncomputable def lastSupportIndex (x : Delta d) : Fin (d + 1) :=
  (deltaSupport x).max' (deltaSupport_nonempty x)

/-- The selected last support index is genuinely in the support. -/
theorem lastSupportIndex_mem (x : Delta d) :
    lastSupportIndex x ∈ deltaSupport x := by
  exact Finset.max'_mem _ _

/-- The selected coordinate is nonzero. -/
theorem lastSupportIndex_ne_zero (x : Delta d) :
    x (lastSupportIndex x) ≠ 0 :=
  (mem_deltaSupport_iff x (lastSupportIndex x)).1 (lastSupportIndex_mem x)

/-- The selector depends only on the barycentric point, so it is automatically compatible with
any two local descriptions having the same standard-simplex coordinate. -/
theorem lastSupportIndex_eq_of_eq {x y : Delta d} (hxy : x = y) :
    lastSupportIndex x = lastSupportIndex y :=
  congrArg lastSupportIndex hxy

@[simp] theorem deltaSupport_vertex (i : Fin (d + 1)) :
    deltaSupport (SphereOddDegree.FiniteSimplex.vertex (S := Real) i) = {i} := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [deltaSupport, SphereOddDegree.FiniteSimplex.vertex]
  · simp [deltaSupport, SphereOddDegree.FiniteSimplex.vertex, hji]

/-- The last-support selector fixes every original simplex vertex. -/
@[simp] theorem lastSupportIndex_vertex (i : Fin (d + 1)) :
    lastSupportIndex (SphereOddDegree.FiniteSimplex.vertex (S := Real) i) = i := by
  have h := lastSupportIndex_mem (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)
  simpa [deltaSupport_vertex] using h

/-- If one coordinate vanishes, the last-support selector cannot choose that coordinate. -/
theorem lastSupportIndex_ne_of_coordinate_eq_zero
    (x : Delta d) (k : Fin (d + 1)) (hk : x k = 0) :
    lastSupportIndex x ≠ k := by
  intro h
  have hnz := lastSupportIndex_ne_zero x
  apply hnz
  rw [h]
  exact hk

/-- Coarse endpoint vertex selected at a local vertex of the recursive one-step cylinder. -/
noncomputable def localLastIndex
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d) (i : Fin (d + 2)) : Fin (d +
      1) :=
  lastSupportIndex (RelativeSubdivisionCylinderCombinatorics.vertex d q i).1

/-- The selector fixes the coarse lower-boundary vertices. -/
@[simp] theorem localLastIndex_lower
    (d : Nat) (i : Fin (d + 1)) :
    localLastIndex d (RelativeSubdivisionCylinderCombinatorics.lowerCell d) i.succ = i := by
  simp [localLastIndex, RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex]

/-- Local occurrences with the same spatial barycentric point have the same selected index. -/
theorem localLastIndex_eq_of_spatial_eq
    {q r : RelativeSubdivisionCylinderCombinatorics.Cell d} {i j : Fin (d + 2)}
    (h : (RelativeSubdivisionCylinderCombinatorics.vertex d q i).1 =
      (RelativeSubdivisionCylinderCombinatorics.vertex d r j).1) :
    localLastIndex d q i = localLastIndex d r j := by
  exact lastSupportIndex_eq_of_eq h

/-- Every non-apex vertex of a recursively embedded side selects a vertex of that side. -/
theorem localLastIndex_side_ne_deleted
    (d : Nat) (k : Fin (d + 2)) (q : RelativeSubdivisionCylinderCombinatorics.Cell d) (i : Fin
      (d + 2)) :
    localLastIndex (d + 1) (RelativeSubdivisionCylinderCombinatorics.sideCell d k q) i.succ ≠ k
      := by
  apply lastSupportIndex_ne_of_coordinate_eq_zero
  simp [ RelativeSubdivisionCylinderCombinatorics.vertex_succ_side,
    RelativeSubdivisionCylinderCombinatorics.sidePoint_spatial_deleted]


/-- Reinterpret the selected local index in the ambient `p`-vertex endpoint simplex. -/
noncomputable def endpointIndex
    (hp : Nat.Prime p) (q : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1))
    (i : Fin (p + 1)) : Fin (p - 1 + 1) :=
  localLastIndex (p - 1) q (Fin.cast (by
    have hp2 : 2 ≤ p := hp.two_le
    omega) i)

/-- Push the barycentric weights of a cylinder cell through its finite last-vertex selector. -/
noncomputable def retractedWeight
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d) (w : Delta (d + 1)) : Delta d :=
  ⟨fun j => ∑ i : Fin (d + 2), if localLastIndex d q i = j then w i else 0, by
    constructor
    · intro j
      exact Finset.sum_nonneg fun i _ => by
        split_ifs
        · exact SphereOddDegree.FiniteSimplex.zero_le w i
        · exact le_rfl
    · rw [Finset.sum_comm]
      calc
        ∑ i : Fin (d + 2),
            ∑ j : Fin (d + 1),
              (if localLastIndex d q i = j then w i else 0) =
            ∑ i : Fin (d + 2), w i := by
              apply Finset.sum_congr rfl
              intro i hi
              simp
        _ = 1 := SphereOddDegree.FiniteSimplex.sum_eq_one w⟩

/-- Transport ambient endpoint weights to the recursive cylinder's vertex indexing. -/
noncomputable def endpointCylinderWeight
    (hp : Nat.Prime p) (w : Delta p) : Delta (p - 1 + 1) :=
  let hcard : p + 1 = (p - 1 + 1) + 1 := by
    rw [Nat.sub_add_cancel hp.pos]
  ⟨fun i => w (Fin.cast hcard.symm i), by
    constructor
    · intro i
      exact SphereOddDegree.FiniteSimplex.zero_le w _
    · exact (Equiv.sum_comp (finCongr hcard.symm) w).trans
        (SphereOddDegree.FiniteSimplex.sum_eq_one w)⟩

/-- Retraction specialized to the ambient prime-cardinality simplex. -/
noncomputable def endpointRetractedWeight
    (hp : Nat.Prime p)
    (q : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1))
    (w : Delta p) : Delta (p - 1) :=
  retractedWeight (p - 1) q (endpointCylinderWeight hp w)


/-- On the lower boundary facet, pushing weights through the selector is exactly the original
coarse barycentric coordinate vector. -/
theorem retractedWeight_lower_apply_of_zero
    (d : Nat) (w : Delta (d + 1)) (hzero : w 0 = 0) (j : Fin (d + 1)) :
    retractedWeight d (RelativeSubdivisionCylinderCombinatorics.lowerCell d) w j = w j.succ := by
  change (∑ i : Fin (d + 2),
    if localLastIndex d (RelativeSubdivisionCylinderCombinatorics.lowerCell d) i = j
    then w i else 0) = w j.succ
  simp [Fin.sum_univ_succ, hzero, localLastIndex_lower]

/-- Last-vertex map on the vertices of one barycentric top simplex. -/
noncomputable def upperLastIndex
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) (i : Fin (d + 1)) : Fin (d + 1) :=
  lastSupportIndex (prefixBarycenter d pi i)

@[simp] theorem localLastIndex_upper
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1))) (i : Fin (d + 1)) :
    localLastIndex d (RelativeSubdivisionCylinderCombinatorics.upperCell d pi) i.succ =
      upperLastIndex d pi i := by
  simp [localLastIndex, upperLastIndex,
    RelativeSubdivisionCylinderCombinatorics.vertex_succ_upper,
    RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex]

/-- On an upper boundary facet, the retracted weights are the pushforward by the ordinary
last-vertex map of that barycentric simplex. -/
theorem retractedWeight_upper_apply_of_zero
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1)))
    (w : Delta (d + 1)) (hzero : w 0 = 0) (j : Fin (d + 1)) :
    retractedWeight d (RelativeSubdivisionCylinderCombinatorics.upperCell d pi) w j =
      ∑ i : Fin (d + 1), if upperLastIndex d pi i = j then w i.succ else 0 := by
  change (∑ k : Fin (d + 2),
    if localLastIndex d (RelativeSubdivisionCylinderCombinatorics.upperCell d pi) k = j
    then w k else 0) = _
  simp [Fin.sum_univ_succ, hzero, localLastIndex_upper]

/-- Regrouping identity for affine values after the last-vertex retraction. -/
theorem affine_sum_selected_eq_retracted
    {n : Nat}
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d) (w : Delta (d + 1))
    (V : Fin (d + 1) → Fin n → Real) :
    (fun c => ∑ i : Fin (d + 2), w i * V (localLastIndex d q i) c) =
      fun c => ∑ j : Fin (d + 1), retractedWeight d q w j * V j c := by
  funext c
  change (∑ i : Fin (d + 2), w i * V (localLastIndex d q i) c) =
    ∑ j : Fin (d + 1),
      (∑ i : Fin (d + 2), if localLastIndex d q i = j then w i else 0) * V j c
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- The local affine interpolation of selected endpoint values is exactly an endpoint PL value at
an explicit retracted barycentric point. -/
theorem affine_selectedEndpointValue_eq_value
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (N : Nat) (hN : N = A.level)
    (q : TopCell hp N) (r : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1))
    (w : Delta p) :
    (fun c => ∑ i : Fin (p + 1), w i *
        A.map (RefinedAffineMap.vertex hp N q
          (endpointIndex (p := p) hp r i)) c) =
      RefinedAffineMap.value hp N A.map q
        (StandardSimplex.ofDelta (endpointRetractedWeight (p := p) hp r w)) := by
  subst N
  have hdim : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  have hcard : p + 1 = (p - 1 + 1) + 1 := by
    rw [hdim]
  let w' : Delta ((p - 1) + 1) := endpointCylinderWeight hp w
  have h := affine_sum_selected_eq_retracted (d := p - 1) r w'
    (fun j => A.map (RefinedAffineMap.vertex hp A.level q j))
  have hleft :
      (fun c => ∑ i : Fin (p + 1), w i *
        A.map (RefinedAffineMap.vertex hp A.level q (endpointIndex (p := p) hp r i)) c) =
      fun c => ∑ i : Fin ((p - 1 + 1) + 1), w' i *
        A.map (RefinedAffineMap.vertex hp A.level q (localLastIndex (p - 1) r i)) c := by
    funext c
    apply Fintype.sum_equiv (finCongr hcard); intro i
    have hwi : w i = w' (Fin.cast hcard i) := by
      change w i = w (Fin.cast hcard.symm (Fin.cast hcard i))
      congr 1
    rw [hwi]
    simp [endpointIndex]
  rw [hleft, h]
  funext c
  change (∑ j, (retractedWeight (p - 1) r w') j *
    A.map (RefinedAffineMap.vertex hp A.level q j) c) = _
  simp only [RefinedAffineMap.value, RefinedAffineMap.vertexValue]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2

/-- Every simplex-local one-step endpoint-stack cell obtained from the last-vertex selector avoids
the origin.  This is the quantitative geometric core of the endpoint-stack construction. -/
theorem affine_selectedEndpointValue_ne_zero
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (q : TopCell hp A.level) (r : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1))
    (w : Delta p) :
    (fun c => ∑ i : Fin (p + 1), w i *
        A.map (RefinedAffineMap.vertex hp A.level q
          (endpointIndex (p := p) hp r i)) c) ≠ 0 := by
  rw [affine_selectedEndpointValue_eq_value hp A A.level rfl q r w]
  have h := A.zeroFreeStraightLine q
    (StandardSimplex.ofDelta (endpointRetractedWeight (p := p) hp r w))
    (⟨1, by constructor <;> norm_num⟩ : Set.Icc (0 : Real) 1)
  simpa using h

end EndpointStackLastVertexCore
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
