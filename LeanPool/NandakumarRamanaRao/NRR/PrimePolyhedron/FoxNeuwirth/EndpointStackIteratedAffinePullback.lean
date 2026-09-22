/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ChartMapCollarRepresentation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionEndpointCollar
/-!
# Iterated affine-pullback endpoint stacks

This module iterates the one-step assignment while keeping one fixed endpoint PL map as the
semantic invariant.  At layer `k`, the local formula uses `K.refine k`, but every decorated value
still represents the original chart map `K`.  Hence adjacent layers agree on their seam by chart
compatibility, and the generic assignment-composition theorem glues them.

The lower horizontal values of the stack are the native samples of the supplied regular
approximation.  Reversing an upper stack therefore supplies the exact upper horizontal boundary of
the final collar.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace EndpointStackIteratedAffinePullback

open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollarCompose
open ExplicitAffineRelativeCollarAssignmentCompose
open ExplicitAffineRelativeCollarAssignmentReverse
open CompatibleRefinedChartHomotopy
open CompatibleChartMapOneStep
open ChartMapCollarRepresentation
open RelativeSubdivisionEndpointCollar
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open ExplicitAffineRelativeCollar.Polynomials


variable {p : Nat}

theorem chartMap_refine_zero
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N) : K.refine 0 = K := by
  cases K
  rfl

/-- A nonempty forward stack with `k+1` one-step layers. -/
noncomputable def positiveWitness
    (hp : Nat.Prime p) (N : Nat) :
    (k : Nat) → Witness hp N (N + (k + 1))
  | 0 => by simpa using oneStepWitness hp N
  | k + 1 => by
      simpa [Nat.add_assoc] using
        composeWitness (positiveWitness hp N k)
          (oneStepWitness hp (N + (k + 1)))

/-- One layer using a refined representation of `K` still represents the original chart map. -/
theorem oneStepAssignment_represents_base
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N) (k : Nat) :
    Represents (RelativeSubdivisionOneStepCells.cellSystem hp (N + k)) K
      (vectorValue hp (RelativeSubdivisionOneStepCells.cellSystem hp (N + k))
        (CompatibleChartMapOneStep.assignment hp (K.refine k))) := by
  intro s
  let q0 : TopCell hp N := ancestorTopCell hp N k s.2.1.1
  let w0 : StandardSimplex (p - 1) :=
    ancestorWeight N k s.2.1.1
      (CompatibleChartMapOneStep.localSpatialWeight hp (N + k) s.2)
  refine ⟨q0, w0, ?_, ?_⟩
  · have h := chart_eq_ancestor hp N k s.2.1.1
      (StandardSimplex.ofDelta
        (RelativeSubdivisionOneStepCells.localPoint hp s.2.1.2
          (stdSimplex.vertex (S := Real) s.2.2)).1)
    simpa [q0, w0, coverPoint, RelativeAffineCellSystem.slotPoint,
      RelativeSubdivisionOneStepCells.cellSystem,
      CompatibleChartMapOneStep.localSpatialWeight,
      RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
      RelativeSubdivisionOneStepCells.liftPoint,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using h
  · rfl

/-- Exact native lower endpoint values for the first one-step layer. -/
theorem oneStep_originalPL_lowerFixed
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) :
    ∀ s : (RelativeSubdivisionOneStepCells.cellSystem hp A.level).VertexSlot,
      ((RelativeSubdivisionOneStepCells.cellSystem hp A.level).slotPoint s).time.1 = 0 →
        vectorValue hp (RelativeSubdivisionOneStepCells.cellSystem hp A.level)
            (CompatibleChartMapOneStep.assignment hp
              (baseOriginalPLMap hp A))
            (sampleVertex hp (RelativeSubdivisionOneStepCells.cellSystem hp A.level) s) =
          A.map ((RelativeSubdivisionOneStepCells.cellSystem hp A.level).slotPoint s).spatial := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  rintro ⟨⟨q, r⟩, i⟩ hi
  have htime : (RelativeSubdivisionCylinderCombinatorics.vertex m r i).2.1 = 0 := by
    simpa [RelativeAffineCellSystem.slotPoint, RelativeSubdivisionOneStepCells.cellSystem,
      RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
      RelativeSubdivisionOneStepCells.liftPoint, RelativeSubdivisionOneStepCells.localPoint,
      CompatibleChartMapOneStep.localWeight_succ,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hi
  obtain ⟨j, hj⟩ :=
    RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero m r i htime
  rw [CompatibleChartMapOneStep.vectorValue_assignment_sample]
  simp [CompatibleChartMapOneStep.localVector,
    CompatibleChartMapOneStep.localSpatialWeight,
    baseOriginalPLMap,
    RelativeSubdivisionOneStepCells.localPoint, RelativeSubdivisionOneStepCells.localWeight, hj,
    RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex,
    RelativeAffineCellSystem.slotPoint, RelativeSubdivisionOneStepCells.cellSystem,
    RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
    RelativeSubdivisionOneStepCells.liftPoint, EquivariantPrismVertexParameters.CylinderPoint.ofProd]
  funext c
  simp [RefinedAffineMap.value, RefinedAffineMap.vertexValue, RefinedAffineMap.vertex,
    StandardSimplex.ofDelta, stdSimplex.vertex, Pi.single_apply, ite_mul, Finset.sum_ite_eq']

/-- Complete data carried by a positive endpoint stack. -/
structure Data
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (k : Nat) where
  /-- The vertex assignment on the iterated collar witnessing the affine pullback. -/
  assignment : Assignment hp (positiveWitness hp A.level k).collar.cells
  represents : Represents (positiveWitness hp A.level k).collar.cells
    (baseOriginalPLMap hp A)
    (vectorValue hp (positiveWitness hp A.level k).collar.cells assignment)
  avoidsOrigin : ∀ q : (positiveWitness hp A.level k).collar.cells.Cell,
    AvoidsOrigin
      (localVertexMap hp (positiveWitness hp A.level k).collar.cells assignment q)
  lowerFixed : ∀ s : (positiveWitness hp A.level k).collar.cells.VertexSlot,
    ((positiveWitness hp A.level k).collar.cells.slotPoint s).time.1 = 0 →
      vectorValue hp (positiveWitness hp A.level k).collar.cells assignment
          (sampleVertex hp (positiveWitness hp A.level k).collar.cells s) =
        A.map ((positiveWitness hp A.level k).collar.cells.slotPoint s).spatial

/-- Construct the full positive stack by induction on the number of additional layers. -/
noncomputable def build
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) :
    (k : Nat) → Data hp A k
  | 0 => by
      let K := baseOriginalPLMap hp A
      exact {
        assignment := by
          simpa [positiveWitness, K, oneStepWitness,
            RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
            RelativeSubdivisionOneStepCollar.relativeCollar] using
            CompatibleChartMapOneStep.assignment hp K
        represents := by
          rw [← chartMap_refine_zero hp K]
          simpa [positiveWitness, K, oneStepWitness,
            RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
            RelativeSubdivisionOneStepCollar.relativeCollar] using
            oneStepAssignment_represents_base hp K 0
        avoidsOrigin := by
          intro q
          simpa [positiveWitness, K, oneStepWitness,
            RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
            RelativeSubdivisionOneStepCollar.relativeCollar] using
            CompatibleChartMapOneStep.assignment_avoidsOrigin hp K
              (baseOriginalPLMap_isAffine hp A) q
        lowerFixed := by
          simpa [positiveWitness, K, oneStepWitness,
            RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
            RelativeSubdivisionOneStepCollar.relativeCollar] using
            oneStep_originalPL_lowerFixed hp A
      }
  | k + 1 => by
      let D := build hp A k
      let K := baseOriginalPLMap hp A
      let C := (positiveWitness hp A.level k).collar
      let E := (oneStepWitness hp (A.level + (k + 1))).collar
      let b : Assignment hp E.cells := by
        simpa [E, oneStepWitness,
          RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
          RelativeSubdivisionOneStepCollar.relativeCollar] using
          CompatibleChartMapOneStep.assignment hp (K.refine (k + 1))
      have hbRep : Represents E.cells K (vectorValue hp E.cells b) := by
        simpa [E, b, oneStepWitness,
          RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
          RelativeSubdivisionOneStepCollar.relativeCollar] using
          oneStepAssignment_represents_base hp K (k + 1)
      let hseam := seamCompatible C.cells E.cells K
        (vectorValue hp C.cells D.assignment) (vectorValue hp E.cells b)
        D.represents hbRep
      let a := combinedAssignment C.cells E.cells D.assignment b hseam
      exact {
        assignment := by
          simpa [positiveWitness, composeWitness, C, E,
            ExplicitAffineRelativeCollarCompose.endpointIdentifiedCollar,
            ExplicitAffineRelativeCollarCompose.relativeCollar] using a
        represents := by
          simpa [positiveWitness, composeWitness, C, E, a, hseam,
            ExplicitAffineRelativeCollarCompose.endpointIdentifiedCollar,
            ExplicitAffineRelativeCollarCompose.relativeCollar] using
            combinedAssignment_represents C.cells E.cells K
              D.assignment b D.represents hbRep
        avoidsOrigin := by
          intro q
          have hbAvoid : ∀ r : E.cells.Cell,
              AvoidsOrigin (localVertexMap hp E.cells b r) := by
            intro r
            simpa [E, b, oneStepWitness,
              RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
              RelativeSubdivisionOneStepCollar.relativeCollar] using
              CompatibleChartMapOneStep.assignment_avoidsOrigin hp
                (K.refine (k + 1))
                ((baseOriginalPLMap_isAffine hp A).refine (k + 1)) r
          simpa [positiveWitness, composeWitness, C, E, a, hseam,
            ExplicitAffineRelativeCollarCompose.endpointIdentifiedCollar,
            ExplicitAffineRelativeCollarCompose.relativeCollar] using
            combinedAssignment_avoidsOrigin C.cells E.cells
              D.assignment b hseam D.avoidsOrigin hbAvoid q
        lowerFixed := by
          rintro ⟨q, i⟩ htime
          cases q with
          | inl q =>
              have hleft : (C.cells.vertex q i).time.1 = 0 := by
                change (C.cells.vertex q i).time.1 / 2 = 0 at htime
                linarith
              change vectorValue hp C.cells D.assignment
                  (sampleVertex hp C.cells (q, i)) =
                A.map (C.cells.slotPoint (q, i)).spatial
              exact D.lowerFixed (q, i) hleft
          | inr q =>
              have hnonneg := (E.cells.vertex q i).time.2.1
              change (1 + (E.cells.vertex q i).time.1) / 2 = 0 at htime
              exfalso
              linarith
      }

/-- A built stack starts at the exact stable endpoint samples. -/
theorem build_lowerFixed
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) (k : Nat) :
    ∀ s : (positiveWitness hp A.level k).collar.cells.VertexSlot,
      ((positiveWitness hp A.level k).collar.cells.slotPoint s).time.1 = 0 →
        vectorValue hp (positiveWitness hp A.level k).collar.cells
            (build hp A k).assignment
            (sampleVertex hp (positiveWitness hp A.level k).collar.cells s) =
          A.map ((positiveWitness hp A.level k).collar.cells.slotPoint s).spatial :=
  (build hp A k).lowerFixed

/-- Reversing a built stack gives exact values at its upper horizontal boundary. -/
theorem reverse_build_upperFixed
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) (k : Nat) :
    ∀ s : (ExplicitAffineRelativeCollarReverse.reverseCells
      (positiveWitness hp A.level k).collar.cells).VertexSlot,
      ((ExplicitAffineRelativeCollarReverse.reverseCells
        (positiveWitness hp A.level k).collar.cells).slotPoint s).time.1 = 1 →
        vectorValue hp
            (ExplicitAffineRelativeCollarReverse.reverseCells
              (positiveWitness hp A.level k).collar.cells)
            (reverseAssignment (positiveWitness hp A.level k).collar.cells
              (build hp A k).assignment)
            (sampleVertex hp
              (ExplicitAffineRelativeCollarReverse.reverseCells
                (positiveWitness hp A.level k).collar.cells) s) =
          A.map
            ((ExplicitAffineRelativeCollarReverse.reverseCells
              (positiveWitness hp A.level k).collar.cells).slotPoint s).spatial := by
  intro s hs
  have h0 : ((positiveWitness hp A.level k).collar.cells.slotPoint s).time.1 = 0 := by
    simpa [ExplicitAffineRelativeCollarReverse.reverseCells,
      RelativeAffineCellSystem.slotPoint,
      ExplicitAffineRelativeCollarReverse.reflectPoint] using hs
  change vectorValue hp (positiveWitness hp A.level k).collar.cells
      (build hp A k).assignment
      (sampleVertex hp (positiveWitness hp A.level k).collar.cells s) =
    A.map ((positiveWitness hp A.level k).collar.cells.slotPoint s).spatial
  exact (build hp A k).lowerFixed s h0

end EndpointStackIteratedAffinePullback
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
