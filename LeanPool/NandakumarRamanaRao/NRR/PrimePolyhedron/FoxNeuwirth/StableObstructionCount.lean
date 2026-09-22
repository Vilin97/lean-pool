/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceZeroFreeMaps
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismStableRelativeBoundary
/-!
# Stable homotopy-invariant positive-ray obstruction

The raw refined count is not invariant under arbitrary subdivision: a positive-ray intersection
can move onto a triangulation face and disappear from the relative-interior count.  This module is
the stable obstruction API.  It uses `StableRegularApproximation`, whose positive-ray
intersections avoid the endpoint skeleton.

Existence of a stable approximation follows from the generic boundary-relative prism construction
applied to the reflexive homotopy.  The negative reference has an explicit stable level-zero
approximation.  The reference-specific input is packaged as
`PositiveReferenceStableTheorem`: a stable approximation of the positive reference with the known
nonzero orbit count.  This obligation is strictly smaller than, and does not imply, the invalid raw
homotopy-invariance proposition.
-/

namespace NRR

open Geometry
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPLPositiveRay

variable {p : Nat}

open EquivariantCoordinateHomotopy
open EquivariantPrismStableRelativeBoundary
open RefinedAffineMap

/-- Every zero-free equivariant coordinate map has at least one stable regular approximation. -/
theorem exists_stableRegularApproximation
    (hp : Nat.Prime p) (F : ZeroFreeMap hp) :
    Nonempty (StableRegularApproximation hp F.map) := by
  obtain ⟨N, L, m, hm, hR⟩ :=
    exists_stable_relative_result hp (ZeroFreeHomotopy.refl hp F)
  exact ⟨(Classical.choice hR).lower⟩

/-- A chosen stable approximation of a zero-free equivariant map. -/
noncomputable def chosenStableApproximation
    (hp : Nat.Prime p) (F : ZeroFreeMap hp) :
    StableRegularApproximation hp F.map :=
  Classical.choice (exists_stableRegularApproximation hp F)

/-- Stable positive-ray obstruction count of a zero-free equivariant coordinate map. -/
noncomputable def stableObstructionValue
    (hp : Nat.Prime p) (F : ZeroFreeMap hp) : ZMod p :=
  (chosenStableApproximation hp F).zeroCount

/-- The chosen stable count agrees with every stable approximation. -/
theorem stableObstructionValue_eq
    (HPL : StableHomotopyInvarianceTheorem)
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) :
    stableObstructionValue hp F = A.zeroCount := by
  unfold stableObstructionValue
  exact HPL hp F F (ZeroFreeHomotopy.refl hp F)
    (chosenStableApproximation hp F) A

/-- Stable obstruction values are invariant under zero-free equivariant homotopy. -/
theorem stableObstructionValue_homotopy
    (HPL : StableHomotopyInvarianceTheorem)
    (hp : Nat.Prime p) {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁) :
    stableObstructionValue hp F₀ = stableObstructionValue hp F₁ := by
  unfold stableObstructionValue
  exact HPL hp F₀ F₁ H
    (chosenStableApproximation hp F₀) (chosenStableApproximation hp F₁)

/-- The explicit negative level-zero approximation is stable because every sampled coordinate is
strictly negative; consequently a positive coordinate mean is impossible. -/
noncomputable def negativeReferenceStableApproximation
    (hp : Nat.Prime p) :
    StableRegularApproximation hp (negativeReferenceZeroFreeMap hp).map where
  toRegularApproximation := by
    simpa [negativeReferenceZeroFreeMap, affineZeroFreeMap] using
      (negativeReferenceApproximation hp)
  positiveRaySkeletonFree := by
    intro q w hdev hmean
    exfalso
    have hneg := AAK.negativeEquivariantReferenceCoordinateMap_global_neg hp
      (chart hp 0 q (StandardSimplex.toDelta w))
    have hmeanneg : coordinateMean p
        (value hp 0
          (ofCoordinateAffineVertexMap
            (AAK.negativeEquivariantReferenceCoordinateMap hp)) q w) < 0 := by
      have heq := value_zero_ofCoordinateAffineVertexMap hp
        (AAK.negativeEquivariantReferenceCoordinateMap hp) q w
      rw [heq]
      unfold coordinateMean
      haveI : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
      exact div_neg_of_neg_of_pos
        (Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty)
        (by exact_mod_cast hp.pos)
    exact (not_lt_of_ge (le_of_lt hmean)) hmeanneg

@[simp] theorem negativeReferenceStableApproximation_zeroCount
    (hp : Nat.Prime p) :
    (negativeReferenceStableApproximation hp).zeroCount = 0 := by
  exact negativeReferenceApproximation_zeroCount hp

/-- The stable positive reference endpoint together with its nonzero count. -/
structure PositiveReferenceStableData (hp : Nat.Prime p) where
  /-- The stable regular approximation of the positive reference map with nonzero count. -/
  approximation :
    StableRegularApproximation hp (positiveReferenceZeroFreeMap hp).map
  zeroCount_ne_zero : approximation.zeroCount ≠ 0

/-- Uniform positive-reference stability theorem required by the stable obstruction route. -/
def PositiveReferenceStableTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p),
    Nonempty (PositiveReferenceStableData hp)

/-- At level zero, every positive-ray intersection of the explicit positive reference lies in
the relative interior of its maximal simplex.  The coordinate-equality equations are exactly the
zero equations for `ReferenceAffineOrbitCount.referenceMap`; the latter were shown above to force
all barycentric coordinates to be positive. -/
theorem positiveReferenceSkeletonFree
    (hp : Nat.Prime p) :
    PositiveRaySkeletonFree hp 0 (positiveReferenceZeroFreeMap hp).map := by
  intro q w hdev hmean
  let F := AAK.positiveEquivariantReferenceCoordinateMap hp
  have hzero : ∀ r, (F.deviation hp).value
      (ReferenceAffineOrbitCount.topRepr hp q.1) w r = 0 := by
    intro r
    rw [CoordinateAffineVertexMap.deviation_value_apply]
    apply sub_eq_zero.mpr
    have hr := hdev r
    change value hp 0 (ofCoordinateAffineVertexMap F) q w
        (ReferenceAffineOrbitCount.coordinateLabel hp r) =
      value hp 0 (ofCoordinateAffineVertexMap F) q w
        (ReferenceAffineOrbitCount.lastLabel hp) at hr
    rw [value_zero_ofCoordinateAffineVertexMap hp F q w, chart_zero] at hr
    simp [Simplex.realizationContinuousMap] at hr
    rw [CoordinateAffineVertexMap.globalValue_realizationPoint] at hr
    exact hr
  rw [AAK.positiveEquivariantReferenceCoordinateMap_deviation hp] at hzero
  exact ReferenceAffineOrbitCount.zero_isInterior hp
    (ReferenceAffineOrbitCount.topRepr hp q.1) w hzero

/-- The explicit positive level-zero approximation is stable. -/
noncomputable def positiveReferenceStableApproximation
    (hp : Nat.Prime p) :
    StableRegularApproximation hp (positiveReferenceZeroFreeMap hp).map where
  toRegularApproximation := by
    simpa [positiveReferenceZeroFreeMap, affineZeroFreeMap] using
      (positiveReferenceApproximation hp)
  positiveRaySkeletonFree := positiveReferenceSkeletonFree hp

@[simp] theorem positiveReferenceStableApproximation_zeroCount
    (hp : Nat.Prime p) :
    (positiveReferenceStableApproximation hp).zeroCount =
      (PrimeOrbitCycle.orbitCycle hp).zeroCount
        (ReferenceAffineOrbitCount.referenceIndex hp) := by
  exact positiveReferenceApproximation_zeroCount hp

/-- Concrete stable positive-reference endpoint data. -/
noncomputable def positiveReferenceStableData
    (hp : Nat.Prime p) : PositiveReferenceStableData hp where
  approximation := positiveReferenceStableApproximation hp
  zeroCount_ne_zero := by
    rw [positiveReferenceStableApproximation_zeroCount]
    exact ReferenceAffineOrbitCount.referenceZeroCount_ne_zero hp

/-- The positive-reference stability theorem is discharged by the explicit level-zero map. -/
theorem positiveReferenceStableTheorem : PositiveReferenceStableTheorem := by
  intro p hp
  exact ⟨positiveReferenceStableData hp⟩

/-- The stable negative-reference obstruction value vanishes. -/
theorem negativeReference_stableObstructionValue_eq_zero
    (HPL : StableHomotopyInvarianceTheorem) (hp : Nat.Prime p) :
    stableObstructionValue hp (negativeReferenceZeroFreeMap hp) = 0 := by
  rw [stableObstructionValue_eq HPL hp (negativeReferenceZeroFreeMap hp)
    (negativeReferenceStableApproximation hp)]
  exact negativeReferenceStableApproximation_zeroCount hp

/-- The stable positive-reference obstruction value is nonzero. -/
theorem positiveReference_stableObstructionValue_ne_zero
    (HPL : StableHomotopyInvarianceTheorem)
    (hp : Nat.Prime p) :
    stableObstructionValue hp (positiveReferenceZeroFreeMap hp) ≠ 0 := by
  rw [stableObstructionValue_eq HPL hp (positiveReferenceZeroFreeMap hp)
    (positiveReferenceStableApproximation hp)]
  rw [positiveReferenceStableApproximation_zeroCount]
  exact ReferenceAffineOrbitCount.referenceZeroCount_ne_zero hp

end EquivariantPLPositiveRay
end FoxNeuwirthOrderComplex
end NRR
