/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CorePairMultiplicity
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso

/-!
# Occurrence-sensitive relabeling of ordered subdivision cores

A cubic-core census most naturally compares only unordered vertex-pair
multiplicities.  Subdivision transport, however, must also match each parallel
slot occurrence and record whether that occurrence is reversed.  This module
provides that neutral bridge, independently of any genus, atlas, or marked
graph application.
-/
namespace Utilities.Certificate.ExplicitPotential.Core

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.SubdivisionGraph

variable {n p m q : ℕ}

/-! ## Relabeling one core by a vertex permutation -/

/-- Relabel the vertices of a core while leaving slot occurrences fixed. -/
def relabel (core : Core n p) (vertexPerm : Equiv.Perm (Fin n)) : Core n p where
  tail := fun edge => vertexPerm (core.tail edge)
  head := fun edge => vertexPerm (core.head edge)

@[simp] theorem relabel_tail (core : Core n p)
    (vertexPerm : Equiv.Perm (Fin n)) (edge : Fin p) :
    (core.relabel vertexPerm).tail edge = vertexPerm (core.tail edge) := rfl

@[simp] theorem relabel_head (core : Core n p)
    (vertexPerm : Equiv.Perm (Fin n)) (edge : Fin p) :
    (core.relabel vertexPerm).head edge = vertexPerm (core.head edge) := rfl

theorem relabel_loopless (core : Core n p) (vertexPerm : Equiv.Perm (Fin n))
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) :
    ∀ edge : Fin p,
      (core.relabel vertexPerm).tail edge ≠ (core.relabel vertexPerm).head edge := by
  intro edge hEq
  exact hLoopless edge (vertexPerm.injective hEq)

theorem pairMultiplicity_relabel (core : Core n p)
    (vertexPerm : Equiv.Perm (Fin n)) (i j : Fin n) :
    (core.relabel vertexPerm).pairMultiplicity (vertexPerm i) (vertexPerm j)
      = core.pairMultiplicity i j := by
  unfold pairMultiplicity
  congr 1
  ext edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, relabel_tail,
    relabel_head, EmbeddingLike.apply_eq_iff_eq]

theorem incidenceDegree_relabel (core : Core n p)
    (vertexPerm : Equiv.Perm (Fin n)) (vertex : Fin n) :
    (core.relabel vertexPerm).incidenceDegree (vertexPerm vertex)
      = core.incidenceDegree vertex := by
  unfold incidenceDegree
  refine Finset.sum_congr rfl fun edge _ => ?_
  simp only [relabel_tail, relabel_head, EmbeddingLike.apply_eq_iff_eq]

theorem incidenceDegree_relabel_apply (core : Core n p)
    (vertexPerm : Equiv.Perm (Fin n)) {degree : ℕ}
    (hDegree : ∀ vertex : Fin n, core.incidenceDegree vertex = degree) :
    ∀ vertex : Fin n,
      (core.relabel vertexPerm).incidenceDegree vertex = degree := by
  intro vertex
  have h := incidenceDegree_relabel core vertexPerm (vertexPerm.symm vertex)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact hDegree _

theorem relabel_connected (core : Core n p) (vertexPerm : Equiv.Perm (Fin n))
    (hConnected : core.Connected) : (core.relabel vertexPerm).Connected := by
  intro side hSplit
  obtain ⟨v, w, hv, hw⟩ := hSplit
  let preimage : Finset (Fin n) :=
    side.preimage vertexPerm vertexPerm.injective.injOn
  have hMem : ∀ u : Fin n, u ∈ preimage ↔ vertexPerm u ∈ side := by
    intro u
    simp [preimage, Finset.mem_preimage]
  obtain ⟨edge, hEdge⟩ :=
    hConnected preimage ⟨vertexPerm.symm v, vertexPerm.symm w, by
      simpa [hMem] using hv, by simpa [hMem] using hw⟩
  refine ⟨edge, ?_⟩
  rcases hEdge with ⟨hIn, hOut⟩ | ⟨hIn, hOut⟩
  · exact Or.inl ⟨(hMem _).mp hIn,
      fun hAbsurd => hOut ((hMem _).mpr hAbsurd)⟩
  · exact Or.inr ⟨(hMem _).mp hIn,
      fun hAbsurd => hOut ((hMem _).mpr hAbsurd)⟩

/-- An occurrence-sensitive relabeling between two ordered cores. -/
structure Relabeling (source : Core n p) (target : Core m q) where
  coreEquiv : Fin n ≃ Fin m
  slotEquiv : Fin p ≃ Fin q
  reversed : Fin p → Bool
  tail_eq : ∀ edge : Fin p,
    target.tail (slotEquiv edge) =
      if reversed edge then coreEquiv (source.head edge)
      else coreEquiv (source.tail edge)
  head_eq : ∀ edge : Fin p,
    target.head (slotEquiv edge) =
      if reversed edge then coreEquiv (source.tail edge)
      else coreEquiv (source.head edge)

namespace Relabeling

/-- Transport a source length vector through the slot equivalence. -/
def reindexedLength {source : Core n p} {target : Core m q}
    (relabeling : source.Relabeling target)
    (length : Fin p → ℕ) (edge : Fin q) : ℕ :=
  length (relabeling.slotEquiv.symm edge)

theorem reindexedLength_pos {source : Core n p} {target : Core m q}
    (relabeling : source.Relabeling target)
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge) :
    ∀ edge, 0 < relabeling.reindexedLength length edge := by
  intro edge
  exact hLength (relabeling.slotEquiv.symm edge)

@[simp] theorem reindexedLength_slotEquiv
    {source : Core n p} {target : Core m q}
    (relabeling : source.Relabeling target)
    (length : Fin p → ℕ) (edge : Fin p) :
    relabeling.reindexedLength length (relabeling.slotEquiv edge) = length edge := by
  simp [reindexedLength]

/-- The corresponding relabeling of positive subdivision specifications. -/
def subdivisionRelabeling {source : Core n p} {target : Core m q}
    (relabeling : source.Relabeling target)
    (source_nonempty : 0 < n)
    (source_loopless : ∀ edge : Fin p, source.tail edge ≠ source.head edge)
    (target_nonempty : 0 < m)
    (target_loopless : ∀ edge : Fin q, target.tail edge ≠ target.head edge)
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge) :
    (Spec.ofCore source source_nonempty source_loopless length hLength).Relabeling
      (Spec.ofCore target target_nonempty target_loopless
        (relabeling.reindexedLength length)
        (relabeling.reindexedLength_pos length hLength)) where
  coreEquiv := relabeling.coreEquiv
  slotEquiv := relabeling.slotEquiv
  reversed := relabeling.reversed
  length_eq := by
    intro edge
    exact (relabeling.reindexedLength_slotEquiv length edge).symm
  tail_eq := relabeling.tail_eq
  head_eq := relabeling.head_eq

/-- Positive subdivisions of occurrence-relabelled cores are Laplacian
equivalent. -/
def laplacianEquiv {source : Core n p} {target : Core m q}
    (relabeling : source.Relabeling target)
    (source_nonempty : 0 < n)
    (source_loopless : ∀ edge : Fin p, source.tail edge ≠ source.head edge)
    (target_nonempty : 0 < m)
    (target_loopless : ∀ edge : Fin q, target.tail edge ≠ target.head edge)
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge) :
    LaplacianEquiv
      (Spec.ofCore source source_nonempty source_loopless length hLength).graph
      (Spec.ofCore target target_nonempty target_loopless
        (relabeling.reindexedLength length)
        (relabeling.reindexedLength_pos length hLength)).graph :=
  Spec.laplacianEquiv _ _
    (relabeling.subdivisionRelabeling source_nonempty source_loopless
      target_nonempty target_loopless length hLength)

end Relabeling

/-! ## Multiplicity fibres -/

/-- The unordered endpoint pair of one ordered slot. -/
def edgeKey (core : Core n p) (edge : Fin p) : Sym2 (Fin n) :=
  s(core.tail edge, core.head edge)

/-- The endpoint pair after a vertex relabeling. -/
def mappedEdgeKey (core : Core n p) (vertexEquiv : Fin n ≃ Fin m)
    (edge : Fin p) : Sym2 (Fin m) :=
  s(vertexEquiv (core.tail edge), vertexEquiv (core.head edge))

theorem card_edgeKey_fiber (core : Core n p) (i j : Fin n) :
    Fintype.card {edge : Fin p // core.edgeKey edge = s(i, j)}
      = core.pairMultiplicity i j := by
  have hFilter :
      (Finset.univ.filter fun edge : Fin p => core.edgeKey edge = s(i, j))
        = Finset.univ.filter fun edge : Fin p =>
            (core.tail edge = i ∧ core.head edge = j) ∨
              (core.tail edge = j ∧ core.head edge = i) := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgeKey,
      Sym2.eq_iff]
  rw [Fintype.card_subtype, hFilter]
  rfl

theorem card_mappedEdgeKey_fiber (core : Core n p)
    (vertexEquiv : Fin n ≃ Fin m) (i j : Fin n) :
    Fintype.card {edge : Fin p //
        core.mappedEdgeKey vertexEquiv edge = s(vertexEquiv i, vertexEquiv j)}
      = core.pairMultiplicity i j := by
  have hFilter :
      (Finset.univ.filter fun edge : Fin p =>
          core.mappedEdgeKey vertexEquiv edge = s(vertexEquiv i, vertexEquiv j))
        = Finset.univ.filter fun edge : Fin p =>
            (core.tail edge = i ∧ core.head edge = j) ∨
              (core.tail edge = j ∧ core.head edge = i) := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mappedEdgeKey,
      Sym2.eq_iff, Equiv.apply_eq_iff_eq]
  rw [Fintype.card_subtype, hFilter]
  rfl

/-- A vertex equivalence preserving all unordered pair multiplicities lifts
to a full occurrence-sensitive core relabeling. -/
theorem nonempty_relabeling_of_pairMultiplicity_eq
    (source : Core n p) (target : Core m q)
    (source_loopless : ∀ edge : Fin p, source.tail edge ≠ source.head edge)
    (vertexEquiv : Fin n ≃ Fin m)
    (hMultiplicity : ∀ i j : Fin n,
      source.pairMultiplicity i j =
        target.pairMultiplicity (vertexEquiv i) (vertexEquiv j)) :
    Nonempty (source.Relabeling target) := by
  have hFiber : ∀ key : Sym2 (Fin m),
      Fintype.card {edge : Fin p //
          source.mappedEdgeKey vertexEquiv edge = key}
        = Fintype.card {edge : Fin q // target.edgeKey edge = key} := by
    intro key
    induction key using Sym2.ind with
    | _ a b =>
      obtain ⟨i, rfl⟩ := vertexEquiv.surjective a
      obtain ⟨j, rfl⟩ := vertexEquiv.surjective b
      rw [card_mappedEdgeKey_fiber, card_edgeKey_fiber]
      exact hMultiplicity i j
  have fiberEquiv : ∀ key : Sym2 (Fin m),
      {edge : Fin p // source.mappedEdgeKey vertexEquiv edge = key}
        ≃ {edge : Fin q // target.edgeKey edge = key} :=
    fun key => Fintype.equivOfCardEq (hFiber key)
  obtain ⟨slotEquiv, hSlotKey⟩ :
      ∃ slotEquiv : Fin p ≃ Fin q, ∀ edge : Fin p,
        target.edgeKey (slotEquiv edge) =
          source.mappedEdgeKey vertexEquiv edge := by
    refine ⟨(Equiv.sigmaFiberEquiv
      (source.mappedEdgeKey vertexEquiv)).symm.trans
        ((Equiv.sigmaCongrRight fiberEquiv).trans
          (Equiv.sigmaFiberEquiv target.edgeKey)), fun edge => ?_⟩
    exact (fiberEquiv (source.mappedEdgeKey vertexEquiv edge)
      ⟨edge, rfl⟩).2
  have hEndpoints : ∀ edge : Fin p,
      (target.tail (slotEquiv edge) = vertexEquiv (source.tail edge) ∧
          target.head (slotEquiv edge) = vertexEquiv (source.head edge)) ∨
        (target.tail (slotEquiv edge) = vertexEquiv (source.head edge) ∧
            target.head (slotEquiv edge) = vertexEquiv (source.tail edge) ∧
            target.tail (slotEquiv edge) ≠ vertexEquiv (source.tail edge)) := by
    intro edge
    have hKey := hSlotKey edge
    rw [edgeKey, mappedEdgeKey, Sym2.eq_iff] at hKey
    rcases hKey with ⟨hTail, hHead⟩ | ⟨hTail, hHead⟩
    · exact Or.inl ⟨hTail, hHead⟩
    · refine Or.inr ⟨hTail, hHead, fun hAbsurd => ?_⟩
      have hCollapse : source.head edge = source.tail edge :=
        vertexEquiv.injective (hTail.symm.trans hAbsurd)
      exact source_loopless edge hCollapse.symm
  refine ⟨⟨vertexEquiv, slotEquiv, fun edge =>
    decide (target.tail (slotEquiv edge) ≠ vertexEquiv (source.tail edge)), ?_, ?_⟩⟩
  · intro edge
    rcases hEndpoints edge with ⟨hTail, _⟩ | ⟨hTail, _, hFlip⟩
    · have hReversed :
          decide (target.tail (slotEquiv edge) ≠ vertexEquiv (source.tail edge)) = false :=
        decide_eq_false fun hNe => hNe hTail
      simpa [hReversed] using hTail
    · have hReversed :
          decide (target.tail (slotEquiv edge) ≠ vertexEquiv (source.tail edge)) = true :=
        decide_eq_true hFlip
      simpa [hReversed] using hTail
  · intro edge
    rcases hEndpoints edge with ⟨hTail, hHead⟩ | ⟨hTail, hHead, hFlip⟩
    · have hReversed :
          decide (target.tail (slotEquiv edge) ≠ vertexEquiv (source.tail edge)) = false :=
        decide_eq_false fun hNe => hNe hTail
      simpa [hReversed] using hHead
    · have hReversed :
          decide (target.tail (slotEquiv edge) ≠ vertexEquiv (source.tail edge)) = true :=
        decide_eq_true hFlip
      simpa [hReversed] using hHead

end Utilities.Certificate.ExplicitPotential.Core
