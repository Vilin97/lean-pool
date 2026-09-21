/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.OneEdgeSplitRefinement
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.MovingPosition
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionExistence
import Mathlib.Tactic

/-!
# Relabeling subdivided core graphs

This is the occurrence-sensitive symmetry interface for subdivision graphs.
It transports a graph along a permutation of core vertices and edge slots,
allowing each slot independently to be read in either direction.  In
particular, parallel core edges are never identified: unit steps are carried
by an equivalence of their *occurrences*.

The data is intentionally stated for two possibly differently indexed core
presentations.  Thus it applies both to automorphisms of one presentation and
to comparisons with another presentation having a different slot order.
-/

namespace Utilities.Certificate.SubdivisionGraph

open ExplicitPotential

namespace Spec

variable {n p n' p' : ℕ}
  (source : SubdivisionGraph.Spec n p) (target : SubdivisionGraph.Spec n' p')

/-- Slotwise relabeling data.  `reversed edge = true` means that the target
slot is read from the image of the source head to the image of the source
tail. -/
structure Relabeling where
  coreEquiv : Fin n ≃ Fin n'
  slotEquiv : Fin p ≃ Fin p'
  reversed : Fin p → Bool
  length_eq : ∀ edge : Fin p,
    source.length edge = target.length (slotEquiv edge)
  tail_eq : ∀ edge : Fin p,
    target.core.tail (slotEquiv edge) =
      if reversed edge then coreEquiv (source.core.head edge)
      else coreEquiv (source.core.tail edge)
  head_eq : ∀ edge : Fin p,
    target.core.head (slotEquiv edge) =
      if reversed edge then coreEquiv (source.core.tail edge)
      else coreEquiv (source.core.head edge)

variable (relabeling : source.Relabeling target)

/-- Equivalence of numerical positions on a matched edge slot. -/
def positionEquiv (edge : Fin p) :
    source.PathPosition edge ≃
      target.PathPosition (relabeling.slotEquiv edge) :=
  (if relabeling.reversed edge then Fin.revPerm else Equiv.refl _).trans
    (finCongr (congrArg (fun length : ℕ => length + 1)
      (relabeling.length_eq edge)))

/-- The numerical image of an offset.  In a reversed slot this is `L - k`. -/
theorem positionEquiv_val (edge : Fin p) (position : source.PathPosition edge) :
    (positionEquiv source target relabeling edge position).val =
      if relabeling.reversed edge then source.length edge - position.val
      else position.val := by
  unfold positionEquiv
  split_ifs <;> simp [Fin.rev]

/-- Equivalence of interior coordinates on matched slots.  A reversed slot
sends interior coordinate `j` to `L - 2 - j`. -/
def interiorEquiv (edge : Fin p) :
    Fin (source.length edge - 1) ≃
      Fin (target.length (relabeling.slotEquiv edge) - 1) :=
  (if relabeling.reversed edge then Fin.revPerm else Equiv.refl _).trans
    (finCongr (congrArg (fun length : ℕ => length - 1)
      (relabeling.length_eq edge)))

/-- Equivalence of unit-step offsets.  A reversed slot sends step `j` to
`L - 1 - j`. -/
def stepOffsetEquiv (edge : Fin p) :
    Fin (source.length edge) ≃
      Fin (target.length (relabeling.slotEquiv edge)) :=
  (if relabeling.reversed edge then Fin.revPerm else Equiv.refl _).trans
    (finCongr (relabeling.length_eq edge))

/-- Vertex equivalence induced by a relabeling. -/
def vertexEquiv : source.Vertex ≃ target.Vertex :=
  Equiv.sumCongr relabeling.coreEquiv
    (Equiv.sigmaCongr relabeling.slotEquiv
      (fun edge => interiorEquiv source target relabeling edge))

/-- Unit-step occurrence equivalence induced by a relabeling. -/
def stepEquiv : source.Step ≃ target.Step :=
  Equiv.sigmaCongr relabeling.slotEquiv
    (fun edge => stepOffsetEquiv source target relabeling edge)

@[simp] theorem vertexEquiv_coreVertex (vertex : Fin n) :
    vertexEquiv source target relabeling (source.coreVertex vertex) =
      target.coreVertex (relabeling.coreEquiv vertex) := rfl

@[simp] theorem vertexEquiv_interiorVertex (edge : Fin p)
    (offset : Fin (source.length edge - 1)) :
    vertexEquiv source target relabeling (source.interiorVertex edge offset) =
      target.interiorVertex (relabeling.slotEquiv edge)
        (interiorEquiv source target relabeling edge offset) := rfl

@[simp] theorem stepEquiv_apply (edge : Fin p)
    (offset : Fin (source.length edge)) :
    stepEquiv source target relabeling ⟨edge, offset⟩ =
      ⟨relabeling.slotEquiv edge,
        stepOffsetEquiv source target relabeling edge offset⟩ := rfl

/-- Relabeling carries every named path position to the corresponding vertex
of the matched target slot.  This is the basic transport statement used for
both core automorphisms and presentation changes. -/
theorem pathVertex_positionEquiv (edge : Fin p)
    (position : source.PathPosition edge) :
    target.pathVertex (relabeling.slotEquiv edge)
        (positionEquiv source target relabeling edge position) =
      vertexEquiv source target relabeling (source.pathVertex edge position) := by
  have hLength := relabeling.length_eq edge
  by_cases hZero : position.val = 0
  · have hPosition : position = ⟨0, by omega⟩ := Fin.ext hZero
    rw [hPosition]
    rw [source.pathVertex_zero, vertexEquiv_coreVertex]
    by_cases hReversed : relabeling.reversed edge
    · have hMapped :
          positionEquiv source target relabeling edge ⟨0, by omega⟩ =
            ⟨target.length (relabeling.slotEquiv edge), by omega⟩ := by
          apply Fin.ext
          rw [positionEquiv_val]
          simp [hReversed, ← hLength]
      rw [hMapped, target.pathVertex_length]
      exact congrArg target.coreVertex (by simpa [hReversed] using relabeling.head_eq edge)
    · have hMapped :
          positionEquiv source target relabeling edge ⟨0, by omega⟩ =
            ⟨0, by omega⟩ := by
          apply Fin.ext
          rw [positionEquiv_val]
          simp [hReversed]
      rw [hMapped, target.pathVertex_zero]
      exact congrArg target.coreVertex (by simpa [hReversed] using relabeling.tail_eq edge)
  by_cases hLast : position.val = source.length edge
  · have hPosition : position = ⟨source.length edge, by omega⟩ := Fin.ext hLast
    rw [hPosition]
    rw [source.pathVertex_length, vertexEquiv_coreVertex]
    by_cases hReversed : relabeling.reversed edge
    · have hMapped :
          positionEquiv source target relabeling edge
              ⟨source.length edge, by omega⟩ = ⟨0, by omega⟩ := by
          apply Fin.ext
          rw [positionEquiv_val]
          simp [hReversed]
      rw [hMapped, target.pathVertex_zero]
      exact congrArg target.coreVertex (by simpa [hReversed] using relabeling.tail_eq edge)
    · have hMapped :
          positionEquiv source target relabeling edge
              ⟨source.length edge, by omega⟩ =
            ⟨target.length (relabeling.slotEquiv edge), by omega⟩ := by
          apply Fin.ext
          rw [positionEquiv_val]
          simp [hReversed, hLength]
      rw [hMapped, target.pathVertex_length]
      exact congrArg target.coreVertex (by simpa [hReversed] using relabeling.head_eq edge)
  · have hInterior : source.IsInteriorPosition edge position := by
      change 0 < position.val ∧ position.val < source.length edge
      have := position.isLt
      omega
    have hTargetInterior : target.IsInteriorPosition (relabeling.slotEquiv edge)
        (positionEquiv source target relabeling edge position) := by
      change 0 < (positionEquiv source target relabeling edge position).val ∧
        (positionEquiv source target relabeling edge position).val <
          target.length (relabeling.slotEquiv edge)
      rw [positionEquiv_val]
      rw [← hLength]
      split_ifs <;> omega
    rw [target.pathVertex_eq_interiorVertex _ _ hTargetInterior,
      source.pathVertex_eq_interiorVertex _ _ hInterior,
      vertexEquiv_interiorVertex]
    congr 2
    apply Fin.ext
    unfold interiorEquiv positionEquiv
    simp only [interiorOffsetOfPosition]
    split_ifs
    all_goals simp [Fin.rev]
    all_goals omega

/-- In an orientation-preserving slot, left unit-step endpoints retain their
left position. -/
theorem positionEquiv_stepLeft_of_not_reversed (edge : Fin p)
    (offset : Fin (source.length edge))
    (hReversed : relabeling.reversed edge = false) :
    positionEquiv source target relabeling edge
        (source.stepLeftPosition edge offset) =
      target.stepLeftPosition (relabeling.slotEquiv edge)
        (stepOffsetEquiv source target relabeling edge offset) := by
  apply Fin.ext
  rw [positionEquiv_val]
  unfold stepLeftPosition stepOffsetEquiv
  simp [hReversed]

/-- In an orientation-preserving slot, right unit-step endpoints retain their
right position. -/
theorem positionEquiv_stepRight_of_not_reversed (edge : Fin p)
    (offset : Fin (source.length edge))
    (hReversed : relabeling.reversed edge = false) :
    positionEquiv source target relabeling edge
        (source.stepRightPosition edge offset) =
      target.stepRightPosition (relabeling.slotEquiv edge)
        (stepOffsetEquiv source target relabeling edge offset) := by
  apply Fin.ext
  rw [positionEquiv_val]
  unfold stepRightPosition stepOffsetEquiv
  simp [hReversed]

/-- In a reversed slot, a source left unit-step endpoint becomes the target
right endpoint. -/
theorem positionEquiv_stepLeft_of_reversed (edge : Fin p)
    (offset : Fin (source.length edge))
    (hReversed : relabeling.reversed edge = true) :
    positionEquiv source target relabeling edge
        (source.stepLeftPosition edge offset) =
      target.stepRightPosition (relabeling.slotEquiv edge)
        (stepOffsetEquiv source target relabeling edge offset) := by
  apply Fin.ext
  rw [positionEquiv_val]
  unfold stepLeftPosition stepRightPosition stepOffsetEquiv
  simp only [hReversed, ↓reduceIte, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev, finCongr_apply,
    Fin.cast_mk]
  omega

/-- In a reversed slot, a source right unit-step endpoint becomes the target
left endpoint. -/
theorem positionEquiv_stepRight_of_reversed (edge : Fin p)
    (offset : Fin (source.length edge))
    (hReversed : relabeling.reversed edge = true) :
    positionEquiv source target relabeling edge
        (source.stepRightPosition edge offset) =
      target.stepLeftPosition (relabeling.slotEquiv edge)
        (stepOffsetEquiv source target relabeling edge offset) := by
  apply Fin.ext
  rw [positionEquiv_val]
  unfold stepRightPosition stepLeftPosition stepOffsetEquiv
  simp [hReversed, Fin.rev]

/-- Every unit-step occurrence has the same unordered endpoints after a
relabeling.  This retains parallel-edge multiplicities slot by slot. -/
theorem unitEdge_stepEquiv (step : source.Step) :
    target.unitEdge (stepEquiv source target relabeling step) =
        (vertexEquiv source target relabeling (source.unitEdge step).1,
         vertexEquiv source target relabeling (source.unitEdge step).2) ∨
      target.unitEdge (stepEquiv source target relabeling step) =
        (vertexEquiv source target relabeling (source.unitEdge step).2,
         vertexEquiv source target relabeling (source.unitEdge step).1) := by
  rcases step with ⟨edge, offset⟩
  by_cases hReversed : relabeling.reversed edge
  · right
    change
      (target.stepLeft (relabeling.slotEquiv edge)
          (stepOffsetEquiv source target relabeling edge offset),
        target.stepRight (relabeling.slotEquiv edge)
          (stepOffsetEquiv source target relabeling edge offset)) = _
    rw [← target.pathVertex_stepLeftPosition,
      ← target.pathVertex_stepRightPosition,
      ← positionEquiv_stepRight_of_reversed source target relabeling edge offset hReversed,
      ← positionEquiv_stepLeft_of_reversed source target relabeling edge offset hReversed,
      pathVertex_positionEquiv, pathVertex_positionEquiv,
      source.pathVertex_stepRightPosition,
      source.pathVertex_stepLeftPosition]
    rfl
  · left
    have hNotReversed : relabeling.reversed edge = false := Bool.eq_false_of_not_eq_true hReversed
    change
      (target.stepLeft (relabeling.slotEquiv edge)
          (stepOffsetEquiv source target relabeling edge offset),
        target.stepRight (relabeling.slotEquiv edge)
          (stepOffsetEquiv source target relabeling edge offset)) = _
    rw [← target.pathVertex_stepLeftPosition,
      ← target.pathVertex_stepRightPosition,
      ← positionEquiv_stepLeft_of_not_reversed source target relabeling edge offset hNotReversed,
      ← positionEquiv_stepRight_of_not_reversed source target relabeling edge offset hNotReversed,
      pathVertex_positionEquiv, pathVertex_positionEquiv,
      source.pathVertex_stepLeftPosition,
      source.pathVertex_stepRightPosition]
    rfl

/-- The resulting vertex equivalence is a graph isomorphism in the precise
Laplacian sense used by the certificate checker. -/
def laplacianEquiv : LaplacianEquiv source.graph target.graph :=
  OneEdgeSplitRefinement.laplacianEquivOfUnorientedUnitSteps source target
    (vertexEquiv source target relabeling) (stepEquiv source target relabeling)
    (unitEdge_stepEquiv source target relabeling)

/-- The same relabeling packaged for the older, transmission-facing graph
isomorphism API.  It has exactly the same finite multiplicity content as
`laplacianEquiv`. -/
def graphIso : CFGraphIso source.graph target.graph where
  vertexEquiv := vertexEquiv source target relabeling
  map_num_edges := (laplacianEquiv source target relabeling).num_edges_eq

/-- Full finite-length transmission existence is invariant under a checked
slotwise relabeling of a subdivision presentation.  In particular, a
transmission certificate can be reused after independently permuting and
reversing parallel edge occurrences. -/
theorem transmissionExistence_iff (u v : source.Vertex) :
    TransmissionExistence target.graph
        (vertexEquiv source target relabeling u)
        (vertexEquiv source target relabeling v) ↔
      TransmissionExistence source.graph u v :=
  (graphIso source target relabeling).transmissionExistence_map_iff u v

end Spec

/-! ## Reindexing a specification along index equivalences -/

/-- Rename the vertices and edge slots of an ordered core. -/
def coreReindex {n p n' p' : ℕ} (core : Core n p)
    (vertexEquiv : Fin n ≃ Fin n') (slotEquiv : Fin p ≃ Fin p') :
    Core n' p' where
  tail := fun edge => vertexEquiv (core.tail (slotEquiv.symm edge))
  head := fun edge => vertexEquiv (core.head (slotEquiv.symm edge))

/-- Rename the vertices and edge slots of a subdivision specification. -/
def specReindex {n p n' p' : ℕ} (spec : Spec n p)
    (vertexEquiv : Fin n ≃ Fin n') (slotEquiv : Fin p ≃ Fin p')
    (hn : 0 < n') : Spec n' p' where
  core := coreReindex spec.core vertexEquiv slotEquiv
  length := fun edge => spec.length (slotEquiv.symm edge)
  core_nonempty := hn
  core_loopless := by
    intro edge
    simp only [coreReindex, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact spec.core_loopless _
  length_pos := fun edge => spec.length_pos _

/-- Reindexing is a relabeling, hence preserves the subdivided graph. -/
def specReindexRelabeling {n p n' p' : ℕ} (spec : Spec n p)
    (vertexEquiv : Fin n ≃ Fin n') (slotEquiv : Fin p ≃ Fin p')
    (hn : 0 < n') :
    spec.Relabeling (specReindex spec vertexEquiv slotEquiv hn) where
  coreEquiv := vertexEquiv
  slotEquiv := slotEquiv
  reversed := fun _ => false
  length_eq := by intro edge; simp [specReindex]
  tail_eq := by intro edge; simp [specReindex, coreReindex]
  head_eq := by intro edge; simp [specReindex, coreReindex]

theorem laplacianEquiv_specReindex {n p n' p' : ℕ} (spec : Spec n p)
    (vertexEquiv : Fin n ≃ Fin n') (slotEquiv : Fin p ≃ Fin p')
    (hn : 0 < n') :
    Nonempty (LaplacianEquiv spec.graph
      (specReindex spec vertexEquiv slotEquiv hn).graph) :=
  ⟨Spec.laplacianEquiv _ _ (specReindexRelabeling spec vertexEquiv slotEquiv hn)⟩


end Utilities.Certificate.SubdivisionGraph
