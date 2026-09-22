/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionOneStepEndpoints
/-!
# Base-facet chain of the one-step subdivision cylinder

Every recursive cylinder cell is a cone.  Its facet opposite the cone apex belongs to the
triangulated boundary of `Delta (p - 1) x I`.  This module separates the lower and upper endpoint
parts of that base-facet chain from the recursive spatial-side part and proves that the endpoint
part is exactly

```
sd^(N+1)(orbitCycle) - sd^N(orbitCycle).
```

The radial-facet cancellation and the recursive-side vanishing over the Fox--Neuwirth orbit cycle
are proved in the boundary-cancellation module.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeSubdivisionOneStepBoundaryBase

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open ExplicitAffineRelativeCollar
open RefinedAffineMap


variable {p : Nat}

/-- The base facet occurrence of a coned top cell. -/
noncomputable def baseOccurrence
    (hp : Nat.Prime p) (N : Nat) (q : RelativeSubdivisionOneStepCells.Cell hp N) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence :=
  (q, 0)

/-- Pairing of all cone-base facets against an arbitrary quotient-facet weight. -/
noncomputable def basePairing
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) : ZMod p :=
  ∑ q : RelativeSubdivisionOneStepCells.Cell hp N,
    RelativeSubdivisionOneStepCells.coefficient hp N q *
      W ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (baseOccurrence hp N q))

/-- A local base cell belongs to one of the two external horizontal boundaries. -/
def IsEndpointCell
    (hp : Nat.Prime p) (q : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1)) : Prop :=
  q = RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1) ∨
    ∃ pi : Equiv.Perm (Fin p),
      q = RelativeSubdivisionCylinderCombinatorics.upperCell (p - 1) (by
        simpa [Nat.sub_add_cancel hp.pos] using pi)

noncomputable instance isEndpointCellDecidable
    (hp : Nat.Prime p) (q : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1)) :
    Decidable (IsEndpointCell hp q) := Classical.propDecidable _

/-- Endpoint part of the cone-base pairing. -/
noncomputable def endpointBasePairing
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) : ZMod p :=
  ∑ q : RelativeSubdivisionOneStepCells.Cell hp N,
    if IsEndpointCell hp q.2 then
      RelativeSubdivisionOneStepCells.coefficient hp N q *
        W ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (baseOccurrence hp N q))
    else 0

/-- Recursive spatial-side part of the cone-base pairing. -/
noncomputable def sideBasePairing
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) : ZMod p :=
  ∑ q : RelativeSubdivisionOneStepCells.Cell hp N,
    if IsEndpointCell hp q.2 then 0 else
      RelativeSubdivisionOneStepCells.coefficient hp N q *
        W ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (baseOccurrence hp N q))

/-- The base pairing is the sum of its endpoint and recursive-side parts. -/
theorem basePairing_eq_endpoint_add_side
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) :
    basePairing hp N W = endpointBasePairing hp N W + sideBasePairing hp N W := by
  classical
  unfold basePairing endpointBasePairing sideBasePairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : IsEndpointCell hp q.2 <;> simp [h]

/-- The lower endpoint contribution of the cone-base chain. -/
noncomputable def lowerEndpointPairing
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) : ZMod p :=
  ∑ q : TopCell hp N,
    RefinedAffineMap.coefficient hp N q * W (RelativeSubdivisionOneStepEndpoints.lowerFacet hp N q)

/-- The upper endpoint contribution of the cone-base chain. -/
noncomputable def upperEndpointPairing
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) : ZMod p :=
  ∑ q : TopCell hp (N + 1),
    RefinedAffineMap.coefficient hp (N + 1) q * W (RelativeSubdivisionOneStepEndpoints.upperFacet hp N q)

/-- Endpoint cells in the local recursive cylinder are precisely the one lower cell and all upper
barycentric cells. -/
theorem endpoint_local_sum
    (hp : Nat.Prime p)
    (f : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1) → ZMod p) :
    (∑ q : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1), if IsEndpointCell hp q then f q else 0) =
      f (RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1)) +
        ∑ pi : Equiv.Perm (Fin p),
          f (RelativeSubdivisionCylinderCombinatorics.upperCell (p - 1) (by
            simpa [Nat.sub_add_cancel hp.pos] using pi)) := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 2 := by
    exact ⟨p - 2, (Nat.sub_add_cancel hp.two_le).symm⟩
  simp [IsEndpointCell, RelativeSubdivisionCylinderCombinatorics.Cell, RelativeSubdivisionCylinderCombinatorics.lowerCell, RelativeSubdivisionCylinderCombinatorics.upperCell]

/-- The endpoint part of the base chain is the refined upper chain minus the coarse lower chain. -/
theorem endpointBasePairing_eq_upper_sub_lower
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) :
    endpointBasePairing hp N W =
      upperEndpointPairing hp N W - lowerEndpointPairing hp N W := by
  classical
  unfold endpointBasePairing
  simp only [Fintype.sum_prod_type]
  have hlower :
      (∑ orbit : PrimeOrbitCycle.TopOrbit hp,
        ∑ rho : RefinementWord p N,
          RelativeSubdivisionOneStepCells.coefficient hp N
              ((orbit, rho), RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1)) *
            W ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass
              (baseOccurrence hp N
                ((orbit, rho), RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1))))) =
        -lowerEndpointPairing hp N W := by
    rw [lowerEndpointPairing]
    simp only [Fintype.sum_prod_type]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro orbit horbit
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro rho hrho
    let q : TopCell hp N := (orbit, rho)
    simp [ baseOccurrence,
      RelativeSubdivisionOneStepCells.coefficient,
      RelativeSubdivisionOneStepEndpoints.lowerFacet,
      RelativeSubdivisionOneStepEndpoints.lowerOccurrence]
  have hupper :
      (∑ orbit : PrimeOrbitCycle.TopOrbit hp,
        ∑ rho : RefinementWord p N,
          ∑ pi : Equiv.Perm (Fin p),
            (RefinedAffineMap.coefficient hp N (orbit, rho) *
              (((Equiv.Perm.sign
                (by
                  simpa [Nat.sub_add_cancel hp.pos] using pi :
                    Equiv.Perm (Fin (p - 1 + 1))) : Int) : ZMod p)) *
              W ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass
                (baseOccurrence hp N
                  ((orbit, rho), RelativeSubdivisionCylinderCombinatorics.upperCell (p - 1)
                    (by simpa [Nat.sub_add_cancel hp.pos] using pi)))))) =
        upperEndpointPairing hp N W := by
    rw [upperEndpointPairing,
      ← Equiv.sum_comp (RelativeSubdivisionOneStepEndpoints.splitTopCellEquiv hp N).symm]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro orbit horbit
    apply Finset.sum_congr rfl
    intro rho hrho
    apply Finset.sum_congr rfl
    intro pi hpi
    rw [show
      ((RelativeSubdivisionOneStepEndpoints.splitTopCellEquiv hp N).symm
        ((orbit, rho), pi)) = (orbit, Fin.snoc rho pi) by rfl]
    rw [RelativeSubdivisionOneStepEndpoints.coefficient_snoc hp N (orbit, rho) pi]
    let transported : Equiv.Perm (Fin (p - 1 + 1)) := by
      simpa [Nat.sub_add_cancel hp.pos] using pi
    have hsign :
        (((Equiv.Perm.sign transported : Int) : ZMod p)) =
          (((Equiv.Perm.sign pi : Int) : ZMod p)) := by
      obtain ⟨d, rfl⟩ : ∃ d, p = d + 2 := by
        exact ⟨p - 2, (Nat.sub_add_cancel hp.two_le).symm⟩
      rfl
    change _ * (((Equiv.Perm.sign transported : Int) : ZMod p)) * _ = _
    rw [hsign]
    simp [
      RelativeSubdivisionOneStepEndpoints.upperFacet,
      RelativeSubdivisionOneStepEndpoints.upperOccurrence,
      RelativeSubdivisionOneStepEndpoints.splitTopCellEquiv,
      RelativeSubdivisionOneStepEndpoints.upperOccurrenceBase,
      baseOccurrence
    ]
  have hcoeff (pi : Equiv.Perm (Fin p)) :
      RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient (ZMod p) (p - 1)
          (RelativeSubdivisionCylinderCombinatorics.upperCell (p - 1)
            (by simpa [Nat.sub_add_cancel hp.pos] using pi)) =
        (((Equiv.Perm.sign
          (by simpa [Nat.sub_add_cancel hp.pos] using pi :
            Equiv.Perm (Fin (p - 1 + 1))) : Int) : ZMod p)) := by
    obtain ⟨d, rfl⟩ : ∃ d, p = d + 2 := by
      exact ⟨p - 2, (Nat.sub_add_cancel hp.two_le).symm⟩
    simp [RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient,
      RelativeSubdivisionCylinderCombinatorics.upperCell, permSignCoeff]
  have hlowerCoeff :
      RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient (ZMod p) (p - 1)
          (RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1)) = -1 := by
    obtain ⟨d, rfl⟩ : ∃ d, p = d + 2 := by
      exact ⟨p - 2, (Nat.sub_add_cancel hp.two_le).symm⟩
    simp [RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient,
      RelativeSubdivisionCylinderCombinatorics.lowerCell]
  simp_rw [endpoint_local_sum hp]
  simp_rw [Finset.sum_add_distrib]
  simp only [RelativeSubdivisionOneStepCells.coefficient]
  simp_rw [hcoeff]
  rw [hupper, hlowerCoeff]
  simp only [mul_neg, mul_one]
  simp_rw [neg_mul]
  have hlowerExpanded := hlower
  simp only [RelativeSubdivisionOneStepCells.coefficient, hlowerCoeff,
    mul_neg, mul_one] at hlowerExpanded
  simp_rw [neg_mul] at hlowerExpanded
  rw [hlowerExpanded]
  ring

/-- Exact decomposition of all cone-base facets into the two external endpoint chains and the
recursive spatial-side chain. -/
theorem basePairing_eq_upper_sub_lower_add_side
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) :
    basePairing hp N W =
      upperEndpointPairing hp N W - lowerEndpointPairing hp N W +
        sideBasePairing hp N W := by
  rw [basePairing_eq_endpoint_add_side,
    endpointBasePairing_eq_upper_sub_lower]

end RelativeSubdivisionOneStepBoundaryBase
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
