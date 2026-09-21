/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionZeroFreeApproximation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantReferenceCoordinateMap

/-!
# Explicit refined approximations at the two reference endpoints

The refined approximation interface permits level zero.  At level zero the refined chart is the
original maximal-simplex chart, so sampling a globally affine vertex map and extending it affinely
recovers the same map.  This gives explicit regular approximations of both shifted S5 reference
lifts.  The positive lift has exactly the S5 orbit count; the negative lift has no positive-ray
intersections.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace RefinedAffineMap

variable {p : Nat}

/-- The unique level-zero refinement word. -/
noncomputable def zeroRefinementWord (p : Nat) : RefinementWord p 0 :=
  fun i => Fin.elim0 i

/-- Every level-zero refinement word is the canonical empty word. -/
theorem refinementWord_zero_eq (rho : RefinementWord p 0) :
    rho = zeroRefinementWord p := by
  funext i
  exact Fin.elim0 i

/-- A level-zero refined chart is the original maximal-simplex chart. -/
theorem chart_zero
    (hp : Nat.Prime p) (q : TopCell hp 0) :
    chart hp 0 q = (ReferenceAffineOrbitCount.topRepr hp q.1).realizationContinuousMap := by
  apply ContinuousMap.ext
  intro w
  simp [chart, Simplex.refinedContinuousMap, refinementWord_zero_eq q.2,
    zeroRefinementWord, affineCompMap_zero]

/-- At level zero, sampling and affine interpolation recover an original affine vertex map. -/
theorem value_zero_ofCoordinateAffineVertexMap
    (hp : Nat.Prime p) (F : CoordinateAffineVertexMap p)
    (q : TopCell hp 0) (w : StandardSimplex (p - 1)) :
    value hp 0 (ofCoordinateAffineVertexMap F) q w =
      F.globalValue (chart hp 0 q (StandardSimplex.toDelta w)) := by
  classical
  unfold value vertexValue vertex
  rw [chart_zero hp q]
  change (fun j => ∑ i, w i * (ofCoordinateAffineVertexMap F)
      ((ReferenceAffineOrbitCount.topRepr hp q.1).realizationPoint
        (StandardSimplex.ofDelta (stdSimplex.vertex i))) j) =
    F.globalValue ((ReferenceAffineOrbitCount.topRepr hp q.1).realizationPoint w)
  rw [CoordinateAffineVertexMap.globalValue_realizationPoint]
  have hi (i : Fin (p - 1 + 1)) :
      (ofCoordinateAffineVertexMap F)
          ((ReferenceAffineOrbitCount.topRepr hp q.1).realizationPoint
            (StandardSimplex.ofDelta (stdSimplex.vertex i))) =
        F.vertexValue ((ReferenceAffineOrbitCount.topRepr hp q.1) i) := by
    change F.globalValue _ = _
    rw [CoordinateAffineVertexMap.globalValue_realizationPoint]
    funext r
    simp [CoordinateAffineVertexMap.value, StandardSimplex.ofDelta,
      Pi.single_apply]
  simp_rw [hi]
  rfl

/-- The level-zero determinant of an original affine vertex map is its ordinary simplex
determinant. -/
theorem determinant_zero_ofCoordinateAffineVertexMap
    (hp : Nat.Prime p) (F : CoordinateAffineVertexMap p)
    (q : TopCell hp 0) :
    determinant hp 0 (ofCoordinateAffineVertexMap F) q =
      (F.deviation hp).determinant (ReferenceAffineOrbitCount.topRepr hp q.1) := by
  rw [determinant_ofCoordinateAffineVertexMap]
  simp [AffineSubdivisionDeterminant.iterVertexMatrix_zero,
    refinementWord_zero_eq q.2]

/-- Positive-reference local indices at level zero are exactly the S5 reference indices. -/
theorem positiveReference_localIndex_zero
    (hp : Nat.Prime p) (q : TopCell hp 0) :
    localIndex hp 0
        (ofCoordinateAffineVertexMap (AAK.positiveEquivariantReferenceCoordinateMap hp)) q =
      ReferenceAffineOrbitCount.referenceIndex hp q.1 := by
  classical
  let F := AAK.positiveEquivariantReferenceCoordinateMap hp
  have hdet : determinant hp 0 (ofCoordinateAffineVertexMap F) q =
      (ReferenceAffineOrbitCount.referenceMap hp).determinant
        (ReferenceAffineOrbitCount.topRepr hp q.1) := by
    rw [determinant_zero_ofCoordinateAffineVertexMap]
    rw [AAK.positiveEquivariantReferenceCoordinateMap_deviation hp]
  have hzero : HasPositiveInteriorZero hp 0 (ofCoordinateAffineVertexMap F) q ↔
      (ReferenceAffineOrbitCount.referenceMap hp).HasInteriorZero
        (ReferenceAffineOrbitCount.topRepr hp q.1) := by
    rw [show HasPositiveInteriorZero hp 0 (ofCoordinateAffineVertexMap F) q ↔
        (F.deviation hp).HasInteriorZero (ReferenceAffineOrbitCount.topRepr hp q.1) by
      constructor
      · rintro ⟨w, hw, hdev, hmean⟩
        refine ⟨w, hw, ?_⟩
        intro r
        rw [CoordinateAffineVertexMap.deviation_value_apply]
        apply sub_eq_zero.mpr
        have hr := hdev r
        rw [value_zero_ofCoordinateAffineVertexMap hp F q w, chart_zero] at hr
        simp [Simplex.realizationContinuousMap] at hr
        rw [CoordinateAffineVertexMap.globalValue_realizationPoint] at hr
        exact hr
      · rintro ⟨w, hw, hdev⟩
        refine ⟨w, hw, ?_, ?_⟩
        · intro r
          have hr := hdev r
          rw [CoordinateAffineVertexMap.deviation_value_apply] at hr
          apply sub_eq_zero.mp at hr
          rw [value_zero_ofCoordinateAffineVertexMap hp F q w, chart_zero]
          simp [Simplex.realizationContinuousMap]
          rw [CoordinateAffineVertexMap.globalValue_realizationPoint]
          exact hr
        · have hpos := AAK.positiveEquivariantReferenceCoordinateMap_global_pos hp
            (chart hp 0 q (StandardSimplex.toDelta w))
          unfold coordinateMean
          haveI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
          exact div_pos
            (Finset.sum_pos (fun i _ => by
              simpa [value_zero_ofCoordinateAffineVertexMap hp F q w] using hpos i)
              Finset.univ_nonempty)
            (by exact_mod_cast hp.pos)]
    rw [AAK.positiveEquivariantReferenceCoordinateMap_deviation hp]
  unfold localIndex ReferenceAffineOrbitCount.referenceIndex
  unfold AffineVertexMap.localZeroIndex
  by_cases hz : (ReferenceAffineOrbitCount.referenceMap hp).HasInteriorZero
      (ReferenceAffineOrbitCount.topRepr hp q.1)
  · have hz' := hzero.mpr hz
    rw [if_pos hz', if_pos hz, hdet]
  · have hz' : ¬ HasPositiveInteriorZero hp 0 (ofCoordinateAffineVertexMap F) q :=
      fun h => hz (hzero.mp h)
    rw [if_neg hz', if_neg hz]

/-- The positive level-zero refined count is the S5 reference orbit count. -/
theorem positiveReference_zeroCount_zero
    (hp : Nat.Prime p) :
    zeroCount hp 0
        (ofCoordinateAffineVertexMap (AAK.positiveEquivariantReferenceCoordinateMap hp)) =
      (PrimeOrbitCycle.orbitCycle hp).zeroCount
        (ReferenceAffineOrbitCount.referenceIndex hp) := by
  classical
  unfold zeroCount coefficient
  have hsign (q : TopCell hp 0) : subdivisionSign 0 q.2 = 1 := by
    simp [subdivisionSign]
  simp only [hsign, mul_one]
  rw [show (∑ q : TopCell hp 0,
      (PrimeOrbitCycle.orbitCycle hp).coefficient q.1 *
        localIndex hp 0
          (ofCoordinateAffineVertexMap (AAK.positiveEquivariantReferenceCoordinateMap hp)) q) =
      ∑ q : PrimeOrbitCycle.TopOrbit hp,
        (PrimeOrbitCycle.orbitCycle hp).coefficient q *
          ReferenceAffineOrbitCount.referenceIndex hp q by
    let e : TopCell hp 0 ≃ PrimeOrbitCycle.TopOrbit hp :=
      { toFun := Prod.fst
        invFun := fun q => (q, zeroRefinementWord p)
        left_inv := by intro q; cases q; simp [refinementWord_zero_eq]
        right_inv := by intro q; rfl }
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro q hq
    simp [e, positiveReference_localIndex_zero hp]]
  rfl

/-- The negative shifted reference has no positive local intersection on any level-zero top
simplex. -/
theorem negativeReference_localIndex_zero
    (hp : Nat.Prime p) (q : TopCell hp 0) :
    localIndex hp 0
        (ofCoordinateAffineVertexMap (AAK.negativeEquivariantReferenceCoordinateMap hp)) q = 0 := by
  classical
  unfold localIndex
  rw [if_neg]
  rintro ⟨w, hw, hdev, hmean⟩
  let x := chart hp 0 q (StandardSimplex.toDelta w)
  have hneg := AAK.negativeEquivariantReferenceCoordinateMap_global_neg hp x
  have hmeanneg : coordinateMean hp.pos
      (value hp 0
        (ofCoordinateAffineVertexMap (AAK.negativeEquivariantReferenceCoordinateMap hp)) q w) < 0 := by
    rw [value_zero_ofCoordinateAffineVertexMap]
    unfold coordinateMean
    haveI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
    exact div_neg_of_neg_of_pos
      (Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty)
      (by exact_mod_cast hp.pos)
  linarith

/-- The negative level-zero refined count is zero. -/
theorem negativeReference_zeroCount_zero
    (hp : Nat.Prime p) :
    zeroCount hp 0
        (ofCoordinateAffineVertexMap (AAK.negativeEquivariantReferenceCoordinateMap hp)) = 0 := by
  classical
  unfold zeroCount
  apply Finset.sum_eq_zero
  intro q hq
  rw [negativeReference_localIndex_zero hp q]
  simp

/-- Explicit regular approximation of the positive reference lift. -/
noncomputable def positiveReferenceApproximation
    (hp : Nat.Prime p) :
    RegularApproximation hp
      (ofCoordinateAffineVertexMap (AAK.positiveEquivariantReferenceCoordinateMap hp)) where
  level := 0
  map := ofCoordinateAffineVertexMap (AAK.positiveEquivariantReferenceCoordinateMap hp)
  equivariant := AAK.positiveEquivariantReferenceCoordinateMap_global_smul hp
  regular := by
    intro q
    rw [determinant_zero_ofCoordinateAffineVertexMap]
    rw [AAK.positiveEquivariantReferenceCoordinateMap_deviation hp]
    exact ReferenceAffineOrbitCount.referenceMap_regular hp _
  zeroFreeStraightLine := by
    intro q w u
    rw [value_zero_ofCoordinateAffineVertexMap]
    intro hzero
    have hzero' : (AAK.positiveEquivariantReferenceCoordinateMap hp).globalValue
        (chart hp 0 q (StandardSimplex.toDelta w)) = 0 := by
      change (1 - u.1) • (AAK.positiveEquivariantReferenceCoordinateMap hp).globalValue _ +
        u.1 • (AAK.positiveEquivariantReferenceCoordinateMap hp).globalValue _ = 0 at hzero
      simpa only [← add_smul, sub_add_cancel, one_smul] using hzero
    have hpos := AAK.positiveEquivariantReferenceCoordinateMap_global_pos hp
      (chart hp 0 q (StandardSimplex.toDelta w))
    have hi := congrFun hzero' ⟨0, hp.pos⟩
    exact (ne_of_gt (hpos ⟨0, hp.pos⟩)) hi

/-- Explicit regular approximation of the negative reference lift. -/
noncomputable def negativeReferenceApproximation
    (hp : Nat.Prime p) :
    RegularApproximation hp
      (ofCoordinateAffineVertexMap (AAK.negativeEquivariantReferenceCoordinateMap hp)) where
  level := 0
  map := ofCoordinateAffineVertexMap (AAK.negativeEquivariantReferenceCoordinateMap hp)
  equivariant := AAK.negativeEquivariantReferenceCoordinateMap_global_smul hp
  regular := by
    intro q
    rw [determinant_zero_ofCoordinateAffineVertexMap]
    rw [AAK.negativeEquivariantReferenceCoordinateMap_deviation hp]
    exact ReferenceAffineOrbitCount.referenceMap_regular hp _
  zeroFreeStraightLine := by
    intro q w u
    rw [value_zero_ofCoordinateAffineVertexMap]
    intro hzero
    have hzero' : (AAK.negativeEquivariantReferenceCoordinateMap hp).globalValue
        (chart hp 0 q (StandardSimplex.toDelta w)) = 0 := by
      change (1 - u.1) • (AAK.negativeEquivariantReferenceCoordinateMap hp).globalValue _ +
        u.1 • (AAK.negativeEquivariantReferenceCoordinateMap hp).globalValue _ = 0 at hzero
      simpa only [← add_smul, sub_add_cancel, one_smul] using hzero
    have hneg := AAK.negativeEquivariantReferenceCoordinateMap_global_neg hp
      (chart hp 0 q (StandardSimplex.toDelta w))
    have hi := congrFun hzero' ⟨0, hp.pos⟩
    exact (ne_of_lt (hneg ⟨0, hp.pos⟩)) hi

@[simp] theorem positiveReferenceApproximation_zeroCount
    (hp : Nat.Prime p) :
    (positiveReferenceApproximation hp).zeroCount =
      (PrimeOrbitCycle.orbitCycle hp).zeroCount
        (ReferenceAffineOrbitCount.referenceIndex hp) :=
  positiveReference_zeroCount_zero hp

@[simp] theorem negativeReferenceApproximation_zeroCount
    (hp : Nat.Prime p) :
    (negativeReferenceApproximation hp).zeroCount = 0 :=
  negativeReference_zeroCount_zero hp

end RefinedAffineMap
end FoxNeuwirthOrderComplex
end NRR
