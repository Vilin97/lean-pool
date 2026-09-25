/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutTwoRegular
import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocorePresentation
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CorePairMultiplicity

/-!
# Marker-loop cuts of compatible pseudocore splits

Each marker introduced by loop splitting is joined only to its designated base
vertex, by two parallel slot occurrences.  The two vertices therefore form a
canonical genus-one side of a core vertex cut.
-/

namespace Utilities.Certificate.PseudocoreMarkerCut

open Finset
open ExplicitPotential
open GenusFourPseudocore
open GenusFourPseudocore.Pseudocore

variable {n : ℕ} {core : Pseudocore n} (split : core.SplitMetadata)

/-- Nonloop incidence degree at a pseudocore vertex. -/
def nonloopValence (core : Pseudocore n) (vertex : Fin n) : ℕ :=
  ∑ neighbor : Fin n, core.multiplicity vertex neighbor

/-- The incidence degree of an original vertex in a compatible loopless
split core is its loop-aware pseudocore valence. -/
theorem splitCore_incidenceDegree_baseVertex (vertex : Fin n)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    split.splitCore.incidenceDegree (core.baseVertex vertex) =
      core.valence vertex := by
  classical
  have hMarkerSum :
      (∑ marker : Fin core.loopCount,
          if split.markerBase marker = vertex then 2 else 0) =
        2 * (Finset.univ.filter fun marker : Fin core.loopCount =>
          split.markerBase marker = vertex).card := by
    calc
      _ = (∑ marker ∈ (Finset.univ.filter fun marker : Fin core.loopCount =>
          split.markerBase marker = vertex), 2) := by
            rw [Finset.sum_filter]
      _ = _ := by simp [Nat.mul_comm]
  rw [← CubicMatrixReplay.sum_pairMultiplicity_eq_incidenceDegree
    split.splitCore hCompatible.loopless (core.baseVertex vertex)]
  rw [Fin.sum_univ_add]
  change (∑ i : Fin n, explicitCoreMultiplicity split.splitCore
      (core.baseVertex vertex) (Fin.castAdd core.loopCount i)) +
    (∑ i : Fin core.loopCount, explicitCoreMultiplicity split.splitCore
      (core.baseVertex vertex) (Fin.natAdd n i)) = core.valence vertex
  simp_rw [hCompatible.multiplicity]
  simp only [SplitMetadata.expectedMultiplicity, baseVertex, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]
  rw [hMarkerSum]
  simp [Pseudocore.valence, Pseudocore.SplitMetadata.markerMultiplicity,
    ← hCompatible.markers, Nat.add_comm]

/-- A displayed marker certifies a positive semantic-loop multiplicity at its
base vertex. -/
theorem loops_markerBase_pos (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    0 < core.loops (split.markerBase marker) := by
  have hMarker : marker ∈ (Finset.univ.filter fun other : Fin core.loopCount =>
      split.markerBase other = split.markerBase marker) := by simp
  have hPositive : 0 < split.markerMultiplicity (split.markerBase marker) := by
    exact Finset.card_pos.mpr ⟨marker, hMarker⟩
  rwa [hCompatible.markers] at hPositive

/-- If the pseudocore has only one semantic loop in total, every displayed
marker is based at a vertex carrying exactly that one loop. -/
theorem loops_markerBase_eq_one_of_loopCount_eq_one
    (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hLoopCount : core.loopCount = 1) :
    core.loops (split.markerBase marker) = 1 := by
  have hPositive := loops_markerBase_pos split marker hCompatible
  have hLe : core.loops (split.markerBase marker) ≤ core.loopCount := by
    unfold Pseudocore.loopCount
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (split.markerBase marker))
  omega

/-- Stability forces the base of a unique semantic loop to have at least one
nonloop exit. -/
theorem nonloopValence_markerBase_pos_of_loopCount_eq_one
    (marker : Fin core.loopCount)
    (hValid : core.ValidAt g)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hLoopCount : core.loopCount = 1) :
    0 < nonloopValence core (split.markerBase marker) := by
  have hStable := hValid.2.2.1 (split.markerBase marker)
  have hLoop := loops_markerBase_eq_one_of_loopCount_eq_one split marker
    hCompatible hLoopCount
  change 0 < ∑ neighbor : Fin n,
    core.multiplicity (split.markerBase marker) neighbor
  simp only [Pseudocore.valence, hLoop] at hStable
  omega

/-- The exact single-loop structural dichotomy: its base has one nonloop
incidence (the separating-bridge case), or at least two (the wedge case). -/
theorem nonloopValence_markerBase_eq_one_or_ge_two
    (marker : Fin core.loopCount)
    (hValid : core.ValidAt g)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hLoopCount : core.loopCount = 1) :
    nonloopValence core (split.markerBase marker) = 1 ∨
      2 ≤ nonloopValence core (split.markerBase marker) := by
  have hPositive := nonloopValence_markerBase_pos_of_loopCount_eq_one
    split marker hValid hCompatible hLoopCount
  omega

/-- The canonical two-vertex cut side for one split-loop marker. -/
def cut (marker : Fin core.loopCount) : CoreVertexCut.Data split.splitCore where
  glue := core.baseVertex (split.markerBase marker)
  left := {core.baseVertex (split.markerBase marker), core.markerVertex marker}

/-- Base and marker vertices lie in the two disjoint summands of the split
core's vertex type. -/
theorem baseVertex_ne_markerVertex_any (base : Fin n)
    (marker : Fin core.loopCount) :
    core.baseVertex base ≠ core.markerVertex marker := by
  intro h
  have hVal := congrArg Fin.val h
  simp only [baseVertex, Fin.val_castAdd, markerVertex, Fin.val_natAdd] at hVal
  omega

theorem baseVertex_injective : Function.Injective core.baseVertex := by
  intro first second h
  apply Fin.ext
  have hVal := congrArg Fin.val h
  simpa [Pseudocore.baseVertex] using hVal

theorem markerVertex_injective : Function.Injective core.markerVertex := by
  intro first second h
  apply Fin.ext
  have hVal := congrArg Fin.val h
  simpa [Pseudocore.markerVertex] using hVal

theorem baseVertex_ne_markerVertex (marker : Fin core.loopCount) :
    core.baseVertex (split.markerBase marker) ≠ core.markerVertex marker := by
  exact baseVertex_ne_markerVertex_any (core := core)
    (split.markerBase marker) marker

theorem cut_left_card (marker : Fin core.loopCount) :
    (cut split marker).left.card = 2 := by
  simp [cut, baseVertex_ne_markerVertex split marker]

theorem marker_pairMultiplicity (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    split.splitCore.pairMultiplicity
      (core.baseVertex (split.markerBase marker)) (core.markerVertex marker) = 2 := by
  change explicitCoreMultiplicity split.splitCore
    (core.baseVertex (split.markerBase marker)) (core.markerVertex marker) = 2
  rw [hCompatible.multiplicity]
  simp [Pseudocore.SplitMetadata.expectedMultiplicity,
    Pseudocore.baseVertex, Pseudocore.markerVertex]

theorem leftSlots_eq_markerPair (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (cut split marker).leftSlots = Finset.univ.filter fun edge : Fin core.splitEdgeCount =>
      (split.splitCore.tail edge = core.baseVertex (split.markerBase marker) ∧
        split.splitCore.head edge = core.markerVertex marker) ∨
      (split.splitCore.tail edge = core.markerVertex marker ∧
        split.splitCore.head edge = core.baseVertex (split.markerBase marker)) := by
  ext edge
  simp only [CoreVertexCut.Data.mem_leftSlots, Finset.mem_filter, Finset.mem_univ,
    true_and, CoreVertexCut.Data.LeftSlot]
  let base := core.baseVertex (split.markerBase marker)
  let markerVertex := core.markerVertex marker
  have hNe : base ≠ markerVertex := baseVertex_ne_markerVertex split marker
  constructor
  · rintro ⟨hTail, hHead⟩
    rcases (by simpa [cut, base, markerVertex] using hTail) with hTail | hTail <;>
      rcases (by simpa [cut, base, markerVertex] using hHead) with hHead | hHead
    · exact False.elim (hCompatible.loopless edge (hTail.trans hHead.symm))
    · exact Or.inl ⟨hTail, hHead⟩
    · exact Or.inr ⟨hTail, hHead⟩
    · exact False.elim (hCompatible.loopless edge (hTail.trans hHead.symm))
  · rintro (h | h)
    · exact ⟨by simp [cut, h.1], by simp [cut, h.2]⟩
    · exact ⟨by simp [cut, h.1], by simp [cut, h.2]⟩

theorem cut_leftSlotCount (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (cut split marker).leftSlotCount = 2 := by
  rw [CoreVertexCut.Data.leftSlotCount, leftSlots_eq_markerPair split marker hCompatible,
    ← ExplicitPotential.Core.pairMultiplicity]
  exact marker_pairMultiplicity split marker hCompatible

theorem cut_leftGenus (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (cut split marker).leftGenus = 1 := by
  rw [CoreVertexCut.Data.leftGenus, cut_leftSlotCount split marker hCompatible,
    cut_left_card split marker]
  norm_num

theorem cut_leftTwoRegular (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (cut split marker).LeftTwoRegular := by
  intro vertex hVertex
  rcases (by simpa [cut] using hVertex) with hBase | hMarker
  · subst vertex
    rw [CoreVertexCut.Data.leftIncidentDegree,
      leftSlots_eq_markerPair split marker hCompatible]
    simp_rw [Finset.sum_filter]
    have hTerm (edge : Fin core.splitEdgeCount) :
        (if split.splitCore.tail edge = core.baseVertex (split.markerBase marker) ∧
              split.splitCore.head edge = core.markerVertex marker ∨
            split.splitCore.tail edge = core.markerVertex marker ∧
              split.splitCore.head edge = core.baseVertex (split.markerBase marker) then
          ((if split.splitCore.tail edge = core.baseVertex (split.markerBase marker) then 1 else 0) +
            if split.splitCore.head edge = core.baseVertex (split.markerBase marker) then 1 else 0)
        else 0) =
        if split.splitCore.tail edge = core.baseVertex (split.markerBase marker) ∧
              split.splitCore.head edge = core.markerVertex marker ∨
            split.splitCore.tail edge = core.markerVertex marker ∧
              split.splitCore.head edge = core.baseVertex (split.markerBase marker) then 1 else 0 := by
      by_cases h : split.splitCore.tail edge = core.baseVertex (split.markerBase marker) ∧
            split.splitCore.head edge = core.markerVertex marker ∨
          split.splitCore.tail edge = core.markerVertex marker ∧
            split.splitCore.head edge = core.baseVertex (split.markerBase marker)
      · have hNe := baseVertex_ne_markerVertex split marker
        rcases h with h | h <;> simp [h.1, h.2, hNe, hNe.symm]
      · simp [h]
    simp_rw [hTerm]
    have hCount := marker_pairMultiplicity split marker hCompatible
    rw [ExplicitPotential.Core.pairMultiplicity] at hCount
    rw [Finset.sum_boole]
    exact hCount

  · subst vertex
    rw [CoreVertexCut.Data.leftIncidentDegree,
      leftSlots_eq_markerPair split marker hCompatible]
    simp_rw [Finset.sum_filter]
    have hTerm (edge : Fin core.splitEdgeCount) :
        (if split.splitCore.tail edge = core.baseVertex (split.markerBase marker) ∧
              split.splitCore.head edge = core.markerVertex marker ∨
            split.splitCore.tail edge = core.markerVertex marker ∧
              split.splitCore.head edge = core.baseVertex (split.markerBase marker) then
          ((if split.splitCore.tail edge = core.markerVertex marker then 1 else 0) +
            if split.splitCore.head edge = core.markerVertex marker then 1 else 0)
        else 0) =
        if split.splitCore.tail edge = core.baseVertex (split.markerBase marker) ∧
              split.splitCore.head edge = core.markerVertex marker ∨
            split.splitCore.tail edge = core.markerVertex marker ∧
              split.splitCore.head edge = core.baseVertex (split.markerBase marker) then 1 else 0 := by
      by_cases h : split.splitCore.tail edge = core.baseVertex (split.markerBase marker) ∧
            split.splitCore.head edge = core.markerVertex marker ∨
          split.splitCore.tail edge = core.markerVertex marker ∧
            split.splitCore.head edge = core.baseVertex (split.markerBase marker)
      · have hNe := baseVertex_ne_markerVertex split marker
        rcases h with h | h <;> simp [h.1, h.2, hNe, hNe.symm]
      · simp [h]
    simp_rw [hTerm]
    have hCount := marker_pairMultiplicity split marker hCompatible
    rw [ExplicitPotential.Core.pairMultiplicity] at hCount
    rw [Finset.sum_boole]
    exact hCount

theorem cut_valid (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split) :
    (cut split marker).Valid := by
  constructor
  · simp [cut]
  · intro edge hCrosses
    rcases hCrosses with hCrosses | hCrosses
    · have hTail : split.splitCore.tail edge = core.markerVertex marker := by
        rcases (by simpa [cut] using hCrosses.1) with hGlue | hMarker
        · exact False.elim (hCrosses.2.1 hGlue)
        · exact hMarker
      have hHeadNe : split.splitCore.head edge ≠ core.baseVertex (split.markerBase marker) := by
        intro h
        apply hCrosses.2.2
        simp [cut, h]
      have hPos := CubicMatrixReplay.pairMultiplicity_endpoints_pos split.splitCore edge
      rw [hTail] at hPos
      change 0 < explicitCoreMultiplicity split.splitCore
        (core.markerVertex marker) (split.splitCore.head edge) at hPos
      rw [hCompatible.multiplicity] at hPos
      cases hHead : (@finSumFinEquiv n core.loopCount).symm
          (split.splitCore.head edge) with
      | inl base =>
          have hHeadEq : split.splitCore.head edge = core.baseVertex base := by
            have := congrArg (@finSumFinEquiv n core.loopCount) hHead
            simpa [Pseudocore.baseVertex] using this
          have hNe : split.markerBase marker ≠ base := by
            intro hBase
            apply hHeadNe
            simp [hHeadEq, hBase, Pseudocore.baseVertex]
          simp [Pseudocore.SplitMetadata.expectedMultiplicity,
            Pseudocore.markerVertex, hHead, hNe] at hPos
      | inr other =>
          simp [Pseudocore.SplitMetadata.expectedMultiplicity,
            Pseudocore.markerVertex, hHead] at hPos
    · have hHead : split.splitCore.head edge = core.markerVertex marker := by
        rcases (by simpa [cut] using hCrosses.1) with hGlue | hMarker
        · exact False.elim (hCrosses.2.1 hGlue)
        · exact hMarker
      have hTailNe : split.splitCore.tail edge ≠ core.baseVertex (split.markerBase marker) := by
        intro h
        apply hCrosses.2.2
        simp [cut, h]
      have hPos := CubicMatrixReplay.pairMultiplicity_endpoints_pos split.splitCore edge
      rw [hHead] at hPos
      change 0 < explicitCoreMultiplicity split.splitCore
        (split.splitCore.tail edge) (core.markerVertex marker) at hPos
      rw [hCompatible.multiplicity] at hPos
      cases hTail : (@finSumFinEquiv n core.loopCount).symm
          (split.splitCore.tail edge) with
      | inl base =>
          have hTailEq : split.splitCore.tail edge = core.baseVertex base := by
            have := congrArg (@finSumFinEquiv n core.loopCount) hTail
            simpa [Pseudocore.baseVertex] using this
          have hNe : split.markerBase marker ≠ base := by
            intro hBase
            apply hTailNe
            simp [hTailEq, hBase, Pseudocore.baseVertex]
          simp [Pseudocore.SplitMetadata.expectedMultiplicity,
            Pseudocore.markerVertex, hTail, hNe] at hPos
      | inr other =>
          simp [Pseudocore.SplitMetadata.expectedMultiplicity,
            Pseudocore.markerVertex, hTail] at hPos

/-- The marker side is a rigid genus-one left factor whenever the split core
is connected. -/
theorem cut_leftRigidConditions (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (hConnected : split.splitCore.Connected) :
    (cut split marker).LeftRigidConditions :=
  ⟨cut_valid split marker hCompatible, hConnected,
    cut_leftTwoRegular split marker hCompatible,
    cut_leftGenus split marker hCompatible⟩

/-- A connected subdivision presentation supplies the split-core
connectedness needed by the canonical marker rigidity theorem.  This is the
form produced directly by `pseudocorePresentation_genusFive`. -/
theorem cut_leftRigidConditions_of_presentation
    (marker : Fin core.loopCount)
    (hCompatible : PseudocoreSplitGlue.Compatible split)
    (spec : SubdivisionGraph.Spec (n + core.loopCount) core.splitEdgeCount)
    (hCore : spec.core = split.splitCore)
    (hConnected : graphConnected spec.graph) :
    (cut split marker).LeftRigidConditions := by
  have hCoreConnected : spec.core.Connected :=
    PseudocorePresentation.core_connected_of_graph_connected spec hConnected
  rw [hCore] at hCoreConnected
  exact cut_leftRigidConditions split marker hCompatible hCoreConnected

/-- Distinct loop-marker sides are nested in the expected way: after cutting
off one marker cycle, the entire two-vertex side of any other marker remains
in the complementary factor.  The two marker cycles may share their base
vertex; that common vertex is precisely the first cut's glue. -/
theorem cut_left_subset_right_of_ne (first second : Fin core.loopCount)
    (hNe : second ≠ first) :
    (cut split second).left ⊆ (cut split first).right := by
  classical
  intro vertex hVertex
  rw [CoreVertexCut.Data.mem_right_iff]
  rcases (by simpa [cut] using hVertex) with hBase | hMarker
  · subst vertex
    by_cases hSameBase : split.markerBase second = split.markerBase first
    · exact Or.inl (congrArg core.baseVertex hSameBase)
    · apply Or.inr
      simp only [cut, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hSameBase (baseVertex_injective (core := core) h),
        baseVertex_ne_markerVertex_any (core := core)
          (split.markerBase second) first⟩
  · subst vertex
    apply Or.inr
    simp only [cut, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(baseVertex_ne_markerVertex_any (core := core)
        (split.markerBase first) second).symm,
      fun h => hNe (markerVertex_injective (core := core) h)⟩

end Utilities.Certificate.PseudocoreMarkerCut
