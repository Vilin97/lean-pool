/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.GenusFourPseudocore
import Mathlib.Tactic

/-!
# Split-metadata compatibility (light half)

The `Compatible` predicate records the parts of split-metadata validity needed
for gluing: marker multiplicities, looplessness, and preservation of edge
multiplicities.  It is genus-generic and follows directly from `ValidAt`.
The marker-fibre counting lemma below supports comparison of two compatible
presentations.
-/

namespace Utilities.Certificate.PseudocoreSplitGlue

open Utilities.Certificate.GenusFourPseudocore
open Utilities.Certificate.GenusFourPseudocore.Pseudocore

/-- The three pieces of split-metadata validity that the glue actually uses.
Cut connectedness of the split core is deliberately not included. -/
structure Compatible {n : ℕ} {core : Pseudocore n}
    (data : core.SplitMetadata) : Prop where
  markers : ∀ vertex : Fin n,
    data.markerMultiplicity vertex = core.loops vertex
  loopless : ∀ edge : Fin core.splitEdgeCount,
    data.splitCore.tail edge ≠ data.splitCore.head edge
  multiplicity : ∀ first second : Fin (n + core.loopCount),
    explicitCoreMultiplicity data.splitCore first second =
      data.expectedMultiplicity first second

theorem compatible_of_validAt {n : ℕ} {core : Pseudocore n}
    {data : core.SplitMetadata} {g : ℕ} (hValid : data.ValidAt g) :
    Compatible data :=
  ⟨hValid.2.1, hValid.2.2.2.1, hValid.2.2.2.2⟩

/-! ## Recovering the omitted connectedness field -/

/-- Positive multiplicity between two displayed vertices is witnessed by an
actual ordered edge slot. -/
private theorem exists_slot_of_explicitCoreMultiplicity_pos
    {n p : ℕ} (displayed : ExplicitPotential.Core n p) (first second : Fin n)
    (hPositive : 0 < explicitCoreMultiplicity displayed first second) :
    ∃ edge : Fin p,
      (displayed.tail edge = first ∧ displayed.head edge = second) ∨
      (displayed.tail edge = second ∧ displayed.head edge = first) := by
  unfold explicitCoreMultiplicity at hPositive
  rw [Finset.card_pos] at hPositive
  obtain ⟨edge, hEdge⟩ := hPositive
  exact ⟨edge, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hEdge⟩

/-- Although `Compatible` deliberately omits a connectedness field, a
compatible split of a connected pseudocore is automatically connected.

For a cut separating two base vertices, use pseudocore connectedness and the
checked base--base multiplicity.  If a displayed marker lies on the opposite
side from its base, its checked double edge crosses the cut.  These two cases
exhaust arbitrary cuts of the displayed split. -/
theorem splitCore_connected_of_compatible {n : ℕ} {core : Pseudocore n}
    (data : core.SplitMetadata) (hCoreConnected : core.Connected)
    (hCompatible : Compatible data) :
    data.splitCore.Connected := by
  intro S hSplit
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  have hCases (vertex : Fin (n + core.loopCount)) :
      (∃ base : Fin n, vertex = core.baseVertex base) ∨
      (∃ marker : Fin core.loopCount, vertex = core.markerVertex marker) := by
    obtain ⟨index, rfl⟩ := (@finSumFinEquiv n core.loopCount).surjective vertex
    rcases index with base | marker
    · exact Or.inl ⟨base, rfl⟩
    · exact Or.inr ⟨marker, rfl⟩
  have hSlotCross (first second : Fin (n + core.loopCount))
      (hFirst : first ∈ S) (hSecond : second ∉ S)
      (hPositive : 0 < explicitCoreMultiplicity data.splitCore first second) :
      ∃ edge : Fin core.splitEdgeCount,
        (data.splitCore.tail edge ∈ S ∧ data.splitCore.head edge ∉ S) ∨
        (data.splitCore.head edge ∈ S ∧ data.splitCore.tail edge ∉ S) := by
    obtain ⟨edge, hEdge | hEdge⟩ :=
      exists_slot_of_explicitCoreMultiplicity_pos data.splitCore first second hPositive
    · exact ⟨edge, Or.inl ⟨hEdge.1.symm ▸ hFirst, hEdge.2.symm ▸ hSecond⟩⟩
    · exact ⟨edge, Or.inr ⟨hEdge.2.symm ▸ hFirst, hEdge.1.symm ▸ hSecond⟩⟩
  have hBaseCross (first second : Fin n)
      (hFirst : core.baseVertex first ∈ S)
      (hSecond : core.baseVertex second ∉ S) :
      ∃ edge : Fin core.splitEdgeCount,
        (data.splitCore.tail edge ∈ S ∧ data.splitCore.head edge ∉ S) ∨
        (data.splitCore.head edge ∈ S ∧ data.splitCore.tail edge ∉ S) := by
    let baseSide : Finset (Fin n) :=
      Finset.univ.filter fun vertex => core.baseVertex vertex ∈ S
    obtain ⟨left, hLeft, right, hRight, hMultiplicity⟩ := hCoreConnected baseSide
      ⟨first, second, by simpa [baseSide] using hFirst,
        by simpa [baseSide] using hSecond⟩
    have hLeft' : core.baseVertex left ∈ S := by simpa [baseSide] using hLeft
    have hRight' : core.baseVertex right ∉ S := by simpa [baseSide] using hRight
    apply hSlotCross (core.baseVertex left) (core.baseVertex right) hLeft' hRight'
    rw [hCompatible.multiplicity]
    simpa [Pseudocore.SplitMetadata.expectedMultiplicity,
      Pseudocore.baseVertex] using hMultiplicity
  have hMarkerCross (marker : Fin core.loopCount)
      (hMarker : core.markerVertex marker ∈ S)
      (hBase : core.baseVertex (data.markerBase marker) ∉ S) :
      ∃ edge : Fin core.splitEdgeCount,
        (data.splitCore.tail edge ∈ S ∧ data.splitCore.head edge ∉ S) ∨
        (data.splitCore.head edge ∈ S ∧ data.splitCore.tail edge ∉ S) := by
    apply hSlotCross (core.markerVertex marker)
      (core.baseVertex (data.markerBase marker)) hMarker hBase
    rw [hCompatible.multiplicity]
    simp [Pseudocore.SplitMetadata.expectedMultiplicity,
      Pseudocore.baseVertex, Pseudocore.markerVertex]
  have hBaseMarkerCross (marker : Fin core.loopCount)
      (hBase : core.baseVertex (data.markerBase marker) ∈ S)
      (hMarker : core.markerVertex marker ∉ S) :
      ∃ edge : Fin core.splitEdgeCount,
        (data.splitCore.tail edge ∈ S ∧ data.splitCore.head edge ∉ S) ∨
        (data.splitCore.head edge ∈ S ∧ data.splitCore.tail edge ∉ S) := by
    apply hSlotCross (core.baseVertex (data.markerBase marker))
      (core.markerVertex marker) hBase hMarker
    rw [hCompatible.multiplicity]
    simp [Pseudocore.SplitMetadata.expectedMultiplicity,
      Pseudocore.baseVertex, Pseudocore.markerVertex]
  rcases hCases inside with ⟨baseInside, rfl⟩ | ⟨markerInside, rfl⟩ <;>
    rcases hCases outside with ⟨baseOutside, rfl⟩ | ⟨markerOutside, rfl⟩
  · exact hBaseCross baseInside baseOutside hInside hOutside
  · by_cases hMarkerBase : core.baseVertex (data.markerBase markerOutside) ∈ S
    · exact hBaseMarkerCross markerOutside hMarkerBase hOutside
    · exact hBaseCross baseInside (data.markerBase markerOutside)
        hInside hMarkerBase
  · by_cases hMarkerBase : core.baseVertex (data.markerBase markerInside) ∈ S
    · exact hBaseCross (data.markerBase markerInside) baseOutside
        hMarkerBase hOutside
    · exact hMarkerCross markerInside hInside hMarkerBase
  · by_cases hInsideBase : core.baseVertex (data.markerBase markerInside) ∈ S
    · by_cases hOutsideBase : core.baseVertex (data.markerBase markerOutside) ∈ S
      · exact hBaseMarkerCross markerOutside hOutsideBase hOutside
      · exact hBaseCross (data.markerBase markerInside)
          (data.markerBase markerOutside) hInsideBase hOutsideBase
    · exact hMarkerCross markerInside hInside hInsideBase

/-- Core validity plus the lightweight glue predicate reconstructs the full
checked split validity. -/
theorem validAt_of_coreValid_compatible {n g : ℕ} {core : Pseudocore n}
    (data : core.SplitMetadata) (hValid : core.ValidAt g)
    (hCompatible : Compatible data) : data.ValidAt g :=
  ⟨hValid, hCompatible.markers,
    splitCore_connected_of_compatible data hValid.2.1 hCompatible,
    hCompatible.loopless, hCompatible.multiplicity⟩

section Markers

variable {n m : ℕ} {source : Pseudocore n} {target : Pseudocore m}
  (sourceSplit : source.SplitMetadata) (targetSplit : target.SplitMetadata)
  (vertexEquiv : Fin n ≃ Fin m)

/-- Fibres of `markerBase` over corresponding base vertices have the same
size, because both count semantic loops at that vertex. -/
theorem card_markerFiber
    (hSource : ∀ vertex, sourceSplit.markerMultiplicity vertex = source.loops vertex)
    (hTarget : ∀ vertex, targetSplit.markerMultiplicity vertex = target.loops vertex)
    (hLoops : ∀ i : Fin n, source.loops i = target.loops (vertexEquiv i))
    (w : Fin m) :
    Fintype.card {x : Fin source.loopCount //
        vertexEquiv (sourceSplit.markerBase x) = w}
      = Fintype.card {y : Fin target.loopCount //
        targetSplit.markerBase y = w} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hRewrite :
      (Finset.univ.filter fun x : Fin source.loopCount =>
          vertexEquiv (sourceSplit.markerBase x) = w)
        = Finset.univ.filter fun x : Fin source.loopCount =>
            sourceSplit.markerBase x = vertexEquiv.symm w := by
    ext x
    simp [Equiv.eq_symm_apply]
  rw [hRewrite]
  have hLeft := hSource (vertexEquiv.symm w)
  have hRight := hTarget w
  have hTransport : source.loops (vertexEquiv.symm w) = target.loops w := by
    have := hLoops (vertexEquiv.symm w)
    simpa using this
  simp only [Pseudocore.SplitMetadata.markerMultiplicity] at hLeft hRight
  rw [hLeft, hTransport, ← hRight]

end Markers

end Utilities.Certificate.PseudocoreSplitGlue
