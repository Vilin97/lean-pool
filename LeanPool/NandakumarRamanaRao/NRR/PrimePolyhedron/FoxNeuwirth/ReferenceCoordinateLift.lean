/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffinePrismObstruction
/-!
# Coordinate lift of the S5 reference deviation map

The S5 model is expressed in fixed difference coordinates.  This module adds one full coordinate
whose value is fixed, producing a coordinate-valued affine map with exactly the same deviation
map and the same positive local-index cochain.
-/

@[expose] public section

namespace NRR
namespace AAK

open Geometry
open FoxNeuwirthOrderComplex
open FoxNeuwirthOrderComplex.AffinePrismObstruction

variable {p : Nat}

/-- S5 reference data expressed as a coordinate-valued affine map. -/
noncomputable def referenceCoordinateMap
    (hp : Nat.Prime p) : CoordinateAffineVertexMap p where
  vertexValue c i :=
    if h : i = ReferenceAffineOrbitCount.lastLabel hp then 1
    else
      let r : Fin (p - 1) :=
        ⟨i.1, by
          have ib := i.2
          have hilast : i.1 ≠ p - 1 := by
            intro hi
            apply h
            apply Fin.ext
            simpa [ReferenceAffineOrbitCount.lastLabel] using hi
          omega⟩
      (ReferenceAffineOrbitCount.referenceMap hp).vertexValue c r + 1

/-- The deviation of the coordinate reference map is exactly the S5 reference map. -/
theorem referenceCoordinateMap_deviation
    (hp : Nat.Prime p) :
    (referenceCoordinateMap hp).deviation hp =
      ReferenceAffineOrbitCount.referenceMap hp := by
  apply congrArg (fun vertexValue : BarredPermutation p → Fin (p - 1) → ℝ =>
    ({ vertexValue := vertexValue } : AffineVertexMap p (p - 1)))
  funext c r
  have hr : (r : Nat) ≠ p - 1 := Nat.ne_of_lt r.isLt
  simp [referenceCoordinateMap,
    ReferenceAffineOrbitCount.referenceMap, ReferenceAffineOrbitCount.mapAt,
    ReferenceAffineOrbitCount.coordinateLabel,
    ReferenceAffineOrbitCount.lastLabel, hr]

/-- At a deviation zero of the lifted reference map, every full coordinate equals one. -/
theorem referenceCoordinateMap_value_eq_one_of_deviation_zero
    (hp : Nat.Prime p)
    (s : Simplex p (p - 1)) (w : StandardSimplex (p - 1))
    (hzero : ∀ r, ((referenceCoordinateMap hp).deviation hp).value s w r = 0) :
    ∀ i : Fin p, (referenceCoordinateMap hp).value s w i = 1 := by
  intro i
  by_cases hi : i = ReferenceAffineOrbitCount.lastLabel hp
  · subst i
    simp [CoordinateAffineVertexMap.value, referenceCoordinateMap]
  · obtain ⟨r, hr⟩ : ∃ r : Fin (p - 1),
        ReferenceAffineOrbitCount.coordinateLabel hp r = i := by
      have hiSet : i ∈ {x : Fin p | x ≠ ReferenceAffineOrbitCount.lastLabel hp} := hi
      rw [← ReferenceAffineOrbitCount.coordinateLabel_range hp] at hiSet
      exact hiSet
    subst i
    have hz := hzero r
    rw [CoordinateAffineVertexMap.deviation_value_apply] at hz
    have hlast : (referenceCoordinateMap hp).value s w
        (ReferenceAffineOrbitCount.lastLabel hp) = 1 := by
      simp [CoordinateAffineVertexMap.value, referenceCoordinateMap]
    linarith

/-- Positive zeros of the lifted reference map are exactly the ordinary S5 reference zeros. -/
theorem referenceCoordinateMap_hasPositive_iff
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    (referenceCoordinateMap hp).HasPositiveInteriorZero hp s ↔
      (ReferenceAffineOrbitCount.referenceMap hp).HasInteriorZero s := by
  rw [← referenceCoordinateMap_deviation hp]
  constructor
  · rintro ⟨w, hw, hzero, hmean⟩
    exact ⟨w, hw, hzero⟩
  · rintro ⟨w, hw, hzero⟩
    refine ⟨w, hw, hzero, ?_⟩
    have hval := referenceCoordinateMap_value_eq_one_of_deviation_zero hp s w hzero
    unfold CoordinateAffineVertexMap.mean coordinateMean
    simp [hval, hp.ne_zero]

/-- The positive-index cochain of the coordinate lift is the S5 reference-index cochain. -/
theorem referencePositiveIndex_eq_referenceIndex
    (hp : Nat.Prime p) :
    AffinePrismObstruction.positiveIndex hp (referenceCoordinateMap hp) =
      ReferenceAffineOrbitCount.referenceIndex hp := by
  funext q
  unfold AffinePrismObstruction.positiveIndex
  unfold CoordinateAffineVertexMap.positiveLocalZeroIndex
  unfold ReferenceAffineOrbitCount.referenceIndex
  let s := ReferenceAffineOrbitCount.topRepr hp q
  have hiff := referenceCoordinateMap_hasPositive_iff hp s
  by_cases hzero : (ReferenceAffineOrbitCount.referenceMap hp).HasInteriorZero s
  · have hpositive : (referenceCoordinateMap hp).HasPositiveInteriorZero hp s :=
      hiff.mpr hzero
    simp [s, hpositive, hzero, referenceCoordinateMap_deviation,
      AffineVertexMap.localZeroIndex]
  · have hpositive : ¬(referenceCoordinateMap hp).HasPositiveInteriorZero hp s :=
      fun h => hzero (hiff.mp h)
    simp [s, hpositive, hzero, AffineVertexMap.localZeroIndex]

end AAK
end NRR
