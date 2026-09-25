/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.GraphIsoLaplacianEquiv
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionGraph
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionExistence
public import Mathlib.Tactic

/-!
# One-edge subdivision refinement

An edge refinement replaces one ordered edge occurrence by two positive-length
occurrences through a new bivalent core vertex.  This file provides
proof-carrying transport across that operation.

The fully proved part is deliberately occurrence-based:

* a bijection of subdivision vertices and a bijection of emitted unit steps,
  preserving each unordered endpoint pair, produce a `LaplacianEquiv`;
* the canonical split core and its positive-length `SubdivisionGraph.Spec` are
  constructed without collapsing parallel slots;
* the canonical split's vertex and unit-step equivalences, and the resulting
  `canonicalSplitLaplacianEquiv`, are constructed and checked internally;
* `OneSplitData` packages the corresponding finite bijections for an
  arbitrary endpoint-sorted presentation.

Matching such a presentation to its source remains an explicit data
obligation rather than treating edge ordering as definitional equality.
-/

@[expose] public section

namespace Utilities.Certificate.OneEdgeSplitRefinement

open Finset

open ExplicitPotential SubdivisionGraph

/-! ## Occurrence-preserving graph transport -/

/-- A vertex equivalence and a bijection of emitted unit-step occurrences
induce a `LaplacianEquiv` when each step preserves its unordered endpoints.
The step equivalence, rather than an endpoint-pair map, retains parallel-edge
multiplicity. -/
def laplacianEquivOfUnorientedUnitSteps
    {n p n' p' : ℕ} (source : SubdivisionGraph.Spec n p)
    (target : SubdivisionGraph.Spec n' p')
    (vertexEquiv : source.Vertex ≃ target.Vertex)
    (stepEquiv : source.Step ≃ target.Step)
    (unitEdge_eq : ∀ step : source.Step,
      target.unitEdge (stepEquiv step) =
          (vertexEquiv (source.unitEdge step).1,
           vertexEquiv (source.unitEdge step).2) ∨
        target.unitEdge (stepEquiv step) =
          (vertexEquiv (source.unitEdge step).2,
           vertexEquiv (source.unitEdge step).1)) :
    LaplacianEquiv source.graph target.graph where
  toEquiv := vertexEquiv
  num_edges_eq := by
    intro x y
    rw [target.num_edges_eq_card_filter_steps,
      source.num_edges_eq_card_filter_steps]
    let sourcePredicate : source.Step → Prop := fun step =>
      source.unitEdge step = (x, y) ∨ source.unitEdge step = (y, x)
    let targetPredicate : target.Step → Prop := fun step =>
      target.unitEdge step = (vertexEquiv x, vertexEquiv y) ∨
        target.unitEdge step = (vertexEquiv y, vertexEquiv x)
    have hPredicate (step : source.Step) :
        targetPredicate (stepEquiv step) ↔ sourcePredicate step := by
      rcases unitEdge_eq step with hEdge | hEdge
      · rw [show targetPredicate (stepEquiv step) =
            (target.unitEdge (stepEquiv step) =
                (vertexEquiv x, vertexEquiv y) ∨
              target.unitEdge (stepEquiv step) =
                (vertexEquiv y, vertexEquiv x)) by rfl,
          hEdge]
        simp only [sourcePredicate, Prod.ext_iff,
          vertexEquiv.injective.eq_iff]
      · rw [show targetPredicate (stepEquiv step) =
            (target.unitEdge (stepEquiv step) =
                (vertexEquiv x, vertexEquiv y) ∨
              target.unitEdge (stepEquiv step) =
                (vertexEquiv y, vertexEquiv x)) by rfl,
          hEdge]
        simp only [sourcePredicate, Prod.ext_iff,
          vertexEquiv.injective.eq_iff]
        tauto
    have hFilter :
        (Finset.univ.filter sourcePredicate).map stepEquiv.toEmbedding =
          Finset.univ.filter targetPredicate := by
      ext step
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨sourceStep, hSource, rfl⟩
        exact (hPredicate sourceStep).2 hSource
      · intro hTarget
        refine ⟨stepEquiv.symm step, ?_, by simp⟩
        exact (hPredicate _).1 (by simpa using hTarget)
    change (Finset.univ.filter targetPredicate).card =
      (Finset.univ.filter sourcePredicate).card
    rw [← hFilter, Finset.card_map]

/-- Ordered endpoint preservation is the special case with no reversed
slots. -/
def laplacianEquivOfUnitSteps
    {n p n' p' : ℕ} (source : SubdivisionGraph.Spec n p)
    (target : SubdivisionGraph.Spec n' p')
    (vertexEquiv : source.Vertex ≃ target.Vertex)
    (stepEquiv : source.Step ≃ target.Step)
    (unitEdge_eq : ∀ step : source.Step,
      target.unitEdge (stepEquiv step) =
        (vertexEquiv (source.unitEdge step).1,
         vertexEquiv (source.unitEdge step).2)) :
    LaplacianEquiv source.graph target.graph :=
  laplacianEquivOfUnorientedUnitSteps source target vertexEquiv stepEquiv
    (fun step => Or.inl (unitEdge_eq step))

/-- Composition of two Laplacian-preserving relabelings. -/
def laplacianEquivTrans {G H K : CFGraph}
    (first : LaplacianEquiv G H) (second : LaplacianEquiv H K) :
    LaplacianEquiv G K where
  toEquiv := first.toEquiv.trans second.toEquiv
  num_edges_eq := by
    intro x y
    change numEdges K (second.toEquiv (first.toEquiv x))
      (second.toEquiv (first.toEquiv y)) = numEdges G x y
    rw [second.num_edges_eq, first.num_edges_eq]

/-! ## The canonical split core -/

variable {n p : ℕ}

/-- Original vertices embed below the fresh last core vertex. -/
def oldVertex (_source : SubdivisionGraph.Spec n p) (vertex : Fin n) :
    Fin (n + 1) :=
  vertex.castSucc

/-- The fresh bivalent vertex. -/
def splitVertex (_source : SubdivisionGraph.Spec n p) : Fin (n + 1) :=
  Fin.last n

/-- Original slots embed below the fresh last edge slot. -/
abbrev oldSlot (_source : SubdivisionGraph.Spec n p) (edge : Fin p) :
    Fin (p + 1) :=
  edge.castSucc

/-- Slot occupied by the second half of the split edge. -/
abbrev secondSlot (_source : SubdivisionGraph.Spec n p) : Fin (p + 1) :=
  Fin.last p

variable (source : SubdivisionGraph.Spec n p) (split : Fin p)
  (first second : ℕ)

/-- Replace the named occurrence by a path through the fresh vertex.  All
other occurrences retain their old slots, including parallel copies. -/
def splitCore : ExplicitPotential.Core (n + 1) (p + 1) where
  tail := Fin.lastCases (splitVertex source)
    (fun edge => oldVertex source (source.core.tail edge))
  head := Fin.lastCases (oldVertex source (source.core.head split))
    (fun edge => if edge = split then splitVertex source
      else oldVertex source (source.core.head edge))

/-- The first half remains in the old slot and the second half occupies the
new last slot. -/
def splitLength : Fin (p + 1) → ℕ :=
  Fin.lastCases second
    (fun edge => if edge = split then first else source.length edge)

@[simp] theorem splitCore_tail_old (edge : Fin p) :
    (splitCore source split).tail (oldSlot source edge) =
      oldVertex source (source.core.tail edge) := by
  simp [splitCore, oldSlot]

@[simp] theorem splitCore_tail_second :
    (splitCore source split).tail (secondSlot source) =
      splitVertex source := by
  simp [splitCore, secondSlot]

@[simp] theorem splitCore_head_old (edge : Fin p) :
    (splitCore source split).head (oldSlot source edge) =
      if edge = split then splitVertex source
      else oldVertex source (source.core.head edge) := by
  simp [splitCore, oldSlot]

@[simp] theorem splitCore_head_second :
    (splitCore source split).head (secondSlot source) =
      oldVertex source (source.core.head split) := by
  simp [splitCore, secondSlot]

@[simp] theorem splitLength_old (edge : Fin p) :
    splitLength source split first second (oldSlot source edge) =
      if edge = split then first else source.length edge := by
  simp [splitLength, oldSlot]

@[simp] theorem splitLength_second :
    splitLength source split first second (secondSlot source) = second := by
  simp [splitLength, secondSlot]

/-- Positive-length subdivision specification on the canonical split core. -/
def splitSpec (hFirst : 0 < first) (hSecond : 0 < second) :
    SubdivisionGraph.Spec (n + 1) (p + 1) where
  core := splitCore source split
  length := splitLength source split first second
  core_nonempty := by omega
  core_loopless := by
    intro slot
    refine Fin.lastCases ?_ (fun edge => ?_) slot
    · simpa [splitCore, splitVertex, oldVertex] using
        (Fin.castSucc_ne_last (source.core.head split)).symm
    · by_cases hEdge : edge = split
      · subst edge
        simp [splitCore, splitVertex, oldVertex]
      · simpa [splitCore, splitVertex, oldVertex, hEdge] using
          source.core_loopless edge
  length_pos := by
    intro slot
    refine Fin.lastCases ?_ (fun edge => ?_) slot
    · simpa [splitLength] using hSecond
    · by_cases hEdge : edge = split
      · simpa [splitLength, hEdge] using hFirst
      · simpa [splitLength, hEdge] using source.length_pos edge

/-! ## Proof-carrying normalization of refinements -/

/-- Data required to connect one fixed edge refinement to its
source subdivision.  `stepEquiv` is an equivalence of occurrences, so sorted
parallel slots remain distinct; `unitEdge_eq` permits endpoint orientation to
reverse. -/
structure OneSplitData
    (source : SubdivisionGraph.Spec n p)
    (expanded : SubdivisionGraph.Spec (n + 1) (p + 1)) where
  /-- The source edge divided into two positive segments in the expanded presentation. -/
  splitEdge : Fin p
  /-- The positive first-segment length in the one-edge split. -/
  firstLength : ℕ
  /-- The positive second-segment length, whose sum with the first equals the original edge
  length. -/
  secondLength : ℕ
  firstLength_pos : 0 < firstLength
  secondLength_pos : 0 < secondLength
  length_sum : source.length splitEdge = firstLength + secondLength
  /-- The bijection between source and expanded subdivision vertices. -/
  vertexEquiv : source.Vertex ≃ expanded.Vertex
  /-- The bijection of unit-edge occurrences, required to match endpoints under `vertexEquiv` up
  to reversal. -/
  stepEquiv : source.Step ≃ expanded.Step
  unitEdge_eq : ∀ step : source.Step,
    expanded.unitEdge (stepEquiv step) =
        (vertexEquiv (source.unitEdge step).1,
         vertexEquiv (source.unitEdge step).2) ∨
      expanded.unitEdge (stepEquiv step) =
        (vertexEquiv (source.unitEdge step).2,
         vertexEquiv (source.unitEdge step).1)

namespace OneSplitData

variable {source : SubdivisionGraph.Spec n p}
  {expanded : SubdivisionGraph.Spec (n + 1) (p + 1)}
  (data : OneSplitData source expanded)

/-- A checked one-split normalization preserves the chip-firing Laplacian. -/
def laplacianEquiv : LaplacianEquiv source.graph expanded.graph :=
  laplacianEquivOfUnorientedUnitSteps source expanded
    (OneSplitData.vertexEquiv data) (OneSplitData.stepEquiv data)
    (OneSplitData.unitEdge_eq data)

@[simp] theorem num_edges_eq (x y : source.Vertex) :
    numEdges expanded.graph (data.vertexEquiv x) (data.vertexEquiv y) =
      numEdges source.graph x y :=
  (laplacianEquiv data).num_edges_eq x y

/-- Exact edge count, obtained from the occurrence bijection itself. -/
theorem card_edges_eq (data : OneSplitData source expanded) :
    expanded.graph.edges.card = source.graph.edges.card := by
  rw [expanded.card_edges, source.card_edges]
  simpa [SubdivisionGraph.Spec.Step, Fintype.card_sigma] using
    Fintype.card_congr (OneSplitData.stepEquiv data).symm

theorem bnExists_iff (data : OneSplitData source expanded) (r d : ℤ) :
    BNExists source.graph r d ↔ BNExists expanded.graph r d :=
  (laplacianEquiv data).bnExists_iff r d

/-- A checked one-edge refinement preserves the full finite-length
transmission-existence problem after carrying both marks through the checked
vertex equivalence.  This is stronger than `bnExists_iff`: it transports all
ASP witnesses at once, not only their Grassmannian consequences. -/
theorem transmissionExistence_iff (data : OneSplitData source expanded)
    (u v : source.Vertex) :
    TransmissionExistence expanded.graph (data.vertexEquiv u)
        (data.vertexEquiv v) ↔
      TransmissionExistence source.graph u v := by
  exact (laplacianEquiv data).transmissionExistence_map_iff u v

end OneSplitData

/-! ## Canonical split of a subdivision occurrence -/

/-- The vertex map for the canonical split.  On the selected subdivided path,
the new core vertex occupies path position `first`; all other positions keep
their evident old-slot names. -/
def canonicalSplitVertexMap
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    source.Vertex → (splitSpec source split first second hFirst hSecond).Vertex :=
  fun vertex => match vertex with
  | Sum.inl core =>
      (splitSpec source split first second hFirst hSecond).coreVertex
        (oldVertex source core)
  | Sum.inr ⟨edge, offset⟩ =>
      if hEdge : edge = split then
        by
          subst edge
          by_cases hBefore : offset.val + 1 < first
          · exact
              (splitSpec source split first second hFirst hSecond).interiorVertex
                (oldSlot source split)
                ⟨offset.val, by
                  simp only [splitSpec, splitLength_old]
                  simp only [ite_true]
                  omega⟩
          · by_cases hAt : offset.val + 1 = first
            · exact
                (splitSpec source split first second hFirst hSecond).coreVertex
                  (splitVertex source)
            · exact
                (splitSpec source split first second hFirst hSecond).interiorVertex
                  (secondSlot source)
                  ⟨offset.val - first, by
                    simp only [splitSpec, splitLength_second]
                    have hOffset := offset.isLt
                    omega⟩
      else
        (splitSpec source split first second hFirst hSecond).interiorVertex
          (oldSlot source edge)
          ⟨offset.val, by
            simp only [splitSpec, splitLength_old]
            simp only [hEdge, ite_false]
            exact offset.isLt⟩

/-- The inverse of `canonicalSplitVertexMap`, written by cases on the fresh
core vertex and fresh edge slot. -/
def canonicalSplitVertexMapInv
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    (splitSpec source split first second hFirst hSecond).Vertex → source.Vertex :=
  fun vertex => match vertex with
  | Sum.inl core =>
      Fin.lastCases
        (source.interiorVertex split
          ⟨first - 1, by rw [hLength]; omega⟩)
        (fun old => source.coreVertex old) core
  | Sum.inr ⟨slot, offset⟩ =>
      Fin.lastCases
        (fun secondOffset => source.interiorVertex split
          ⟨first + secondOffset.val, by
            rw [hLength]
            have hOffset := secondOffset.isLt
            simp only [splitSpec, splitLength, Fin.lastCases_last] at hOffset
            omega⟩)
        (fun old offset =>
          if hEdge : old = split then
            by
              subst old
              exact source.interiorVertex split
                ⟨offset.val, by
                  have hOffset : offset.val < first - 1 := by
                    simpa [splitSpec, splitLength] using offset.isLt
                  omega⟩
          else
            source.interiorVertex old
              ⟨offset.val, by
                simpa [splitSpec, splitLength, hEdge] using offset.isLt⟩)
        slot offset

/-- The canonical split preserves the underlying subdivision vertex set up to
the explicit reclassification of the chosen path's position `first` as a
fresh core vertex. -/
def canonicalSplitVertexEquiv
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    source.Vertex ≃ (splitSpec source split first second hFirst hSecond).Vertex where
  toFun := canonicalSplitVertexMap source split first second hFirst hSecond hLength
  invFun := canonicalSplitVertexMapInv source split first second hFirst hSecond hLength
  left_inv := by
    rintro (core | ⟨edge, offset⟩)
    · simp [canonicalSplitVertexMap, canonicalSplitVertexMapInv, oldVertex,
        SubdivisionGraph.Spec.coreVertex, SubdivisionGraph.Spec.interiorVertex]
    · by_cases hEdge : edge = split
      · subst edge
        by_cases hBefore : offset.val + 1 < first
        · simp [canonicalSplitVertexMap, canonicalSplitVertexMapInv, hBefore,
            oldSlot, SubdivisionGraph.Spec.interiorVertex]
        · by_cases hAt : offset.val + 1 = first
          · simp only [canonicalSplitVertexMapInv, canonicalSplitVertexMap, ↓reduceDIte, hAt,
              lt_self_iff_false, Spec.coreVertex, Spec.interiorVertex]
            simp only [splitVertex, Fin.lastCases_last]
            congr 2
            apply Fin.ext
            change first - 1 = offset.val
            omega
          · simp only [canonicalSplitVertexMapInv, canonicalSplitVertexMap, ↓reduceDIte, hBefore,
              hAt, Spec.interiorVertex, secondSlot, Fin.lastCases_last, Sum.inr.injEq,
              Sigma.mk.injEq, heq_eq_eq, true_and]
            have hGe : first ≤ offset.val := by omega
            apply Fin.ext
            exact Nat.add_sub_of_le hGe
      · simp [canonicalSplitVertexMap, canonicalSplitVertexMapInv, hEdge,
          oldSlot, SubdivisionGraph.Spec.interiorVertex]
  right_inv := by
    rintro (core | ⟨slot, offset⟩)
    · refine Fin.lastCases ?_ (fun old => ?_) core
      · simp only [canonicalSplitVertexMap, canonicalSplitVertexMapInv, Spec.interiorVertex,
          Spec.coreVertex, Fin.lastCases_last, ↓reduceDIte, oldSlot, splitVertex, secondSlot,
          tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, Nat.sub_eq_zero_of_le]
        rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      · simp [canonicalSplitVertexMap, canonicalSplitVertexMapInv,
          oldVertex, SubdivisionGraph.Spec.coreVertex,
          SubdivisionGraph.Spec.interiorVertex]
    · refine Fin.lastCases
        (motive := fun slot =>
          ∀ offset : Fin ((splitSpec source split first second hFirst hSecond).length slot - 1),
            canonicalSplitVertexMap source split first second hFirst hSecond hLength
              (canonicalSplitVertexMapInv source split first second hFirst hSecond hLength
                (Sum.inr ⟨slot, offset⟩)) = Sum.inr ⟨slot, offset⟩)
        ?_ (fun old => ?_) slot offset
      · intro offset
        have hNo : ¬ first + offset.val + 1 < first := by omega
        have hNe : ¬ first + offset.val + 1 = first := by omega
        simp [canonicalSplitVertexMap, canonicalSplitVertexMapInv, secondSlot,
          SubdivisionGraph.Spec.interiorVertex, hNo, hNe]
      · intro offset
        by_cases hEdge : old = split
        · subst old
          have hBefore : offset.val + 1 < first := by
            have hOffset := offset.isLt
            simp only [splitSpec, splitLength, Fin.lastCases_castSucc, ↓reduceIte] at hOffset
            omega
          simp [canonicalSplitVertexMap, canonicalSplitVertexMapInv,
            oldSlot, SubdivisionGraph.Spec.interiorVertex, hBefore]
        · simp [canonicalSplitVertexMap, canonicalSplitVertexMapInv, hEdge,
            oldSlot, SubdivisionGraph.Spec.interiorVertex]

/-! ## Canonical occurrence refinement -/

/-- The occurrence map for the canonical split.  A unit step before the new
core vertex remains in the old slot; every later step is moved to the new
second slot.  Thus this is a reclassification of the same unit-edge path,
not an edge contraction or a change of the discrete graph. -/
def canonicalSplitStepMap
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    source.Step → (splitSpec source split first second hFirst hSecond).Step :=
  fun step => match step with
  | ⟨edge, offset⟩ =>
      if hEdge : edge = split then
        by
          subst edge
          by_cases hBefore : offset.val < first
          · exact ⟨oldSlot source split, ⟨offset.val, by
              simp only [splitSpec, splitLength_old, ite_true]
              exact hBefore⟩⟩
          · exact ⟨secondSlot source, ⟨offset.val - first, by
              simp only [splitSpec, splitLength_second]
              have hOffset := offset.isLt
              omega⟩⟩
      else
        ⟨oldSlot source edge, ⟨offset.val, by
          simp only [splitSpec, splitLength_old, ite_eq_right hEdge]
          exact offset.isLt⟩⟩

/-- Inverse occurrence map for `canonicalSplitStepMap`. -/
def canonicalSplitStepMapInv
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    (splitSpec source split first second hFirst hSecond).Step → source.Step :=
  fun step => match step with
  | ⟨slot, offset⟩ =>
      Fin.lastCases
        (fun secondOffset =>
          ⟨split, ⟨first + secondOffset.val, by
            rw [hLength]
            have hOffset := secondOffset.isLt
            simp only [splitSpec, splitLength, Fin.lastCases_last] at hOffset
            omega⟩⟩)
        (fun old oldOffset =>
          if hEdge : old = split then
            by
              subst old
              exact ⟨split, ⟨oldOffset.val, by
                rw [hLength]
                have hOffset : oldOffset.val < first := by
                  simpa [splitSpec, splitLength] using oldOffset.isLt
                omega⟩⟩
          else
            ⟨old, ⟨oldOffset.val, by
              simpa [splitSpec, splitLength, hEdge] using oldOffset.isLt⟩⟩)
        slot offset

private theorem canonicalSplitStepMap_split
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (offset : Fin (source.length split)) :
    canonicalSplitStepMap source split first second hFirst hSecond hLength
      ⟨split, offset⟩ =
        if hBefore : offset.val < first then
          ⟨oldSlot source split, ⟨offset.val, by
            simp only [splitSpec, splitLength_old, ite_true]
            exact hBefore⟩⟩
        else
          ⟨secondSlot source, ⟨offset.val - first, by
            simp only [splitSpec, splitLength_second]
            have _ := offset.isLt
            omega⟩⟩ := by
  simp [canonicalSplitStepMap]

private theorem canonicalSplitStepMap_old
    (source : SubdivisionGraph.Spec n p) (split edge : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (hEdge : edge ≠ split) (offset : Fin (source.length edge)) :
    canonicalSplitStepMap source split first second hFirst hSecond hLength
      ⟨edge, offset⟩ =
        ⟨oldSlot source edge, ⟨offset.val, by
          simp only [splitSpec, splitLength_old, ite_eq_right hEdge]
          exact offset.isLt⟩⟩ := by
  simp [canonicalSplitStepMap, hEdge]

private theorem canonicalSplitStepMapInv_second
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (offset : Fin ((splitSpec source split first second hFirst hSecond).length
      (secondSlot source))) :
    canonicalSplitStepMapInv source split first second hFirst hSecond hLength
      ⟨secondSlot source, offset⟩ =
        ⟨split, ⟨first + offset.val, by
          rw [hLength]
          have hOffset : offset.val < second := by
            simpa [splitSpec, splitLength, secondSlot] using offset.isLt
          omega⟩⟩ := by
  simp [canonicalSplitStepMapInv, secondSlot]

private theorem canonicalSplitStepMapInv_old_split
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (offset : Fin ((splitSpec source split first second hFirst hSecond).length
      (oldSlot source split))) :
    canonicalSplitStepMapInv source split first second hFirst hSecond hLength
      ⟨oldSlot source split, offset⟩ =
        ⟨split, ⟨offset.val, by
          rw [hLength]
          have hOffset : offset.val < first := by
            simpa [splitSpec, splitLength, oldSlot] using offset.isLt
          omega⟩⟩ := by
  simp [canonicalSplitStepMapInv, oldSlot]

private theorem canonicalSplitStepMapInv_old
    (source : SubdivisionGraph.Spec n p) (split edge : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (hEdge : edge ≠ split)
    (offset : Fin ((splitSpec source split first second hFirst hSecond).length
      (oldSlot source edge))) :
    canonicalSplitStepMapInv source split first second hFirst hSecond hLength
      ⟨oldSlot source edge, offset⟩ =
        ⟨edge, ⟨offset.val, by
          simpa [splitSpec, splitLength, oldSlot, hEdge] using offset.isLt⟩⟩ := by
  simp [canonicalSplitStepMapInv, oldSlot, hEdge]
/-- The unit-step occurrences of a subdivision are unchanged when one path
is canonically split at a positive interior position. -/
def canonicalSplitStepEquiv
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    source.Step ≃ (splitSpec source split first second hFirst hSecond).Step where
  toFun := canonicalSplitStepMap source split first second hFirst hSecond hLength
  invFun := canonicalSplitStepMapInv source split first second hFirst hSecond hLength
  left_inv := by
    rintro ⟨edge, offset⟩
    by_cases hEdge : edge = split
    · subst edge
      by_cases hBefore : offset.val < first
      · rw [canonicalSplitStepMap_split source split first second hFirst hSecond hLength,
          dite_eq_left hBefore,
          canonicalSplitStepMapInv_old_split source split first second hFirst hSecond hLength]
      · rw [canonicalSplitStepMap_split source split first second hFirst hSecond hLength,
          dite_eq_right hBefore,
          canonicalSplitStepMapInv_second source split first second hFirst hSecond hLength]
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          exact Nat.add_sub_of_le (Nat.le_of_not_gt hBefore)
    · rw [canonicalSplitStepMap_old source split edge first second hFirst hSecond hLength hEdge,
        canonicalSplitStepMapInv_old source split edge first second hFirst hSecond hLength hEdge]
  right_inv := by
    rintro ⟨slot, offset⟩
    refine Fin.lastCases
      (motive := fun slot =>
        ∀ offset : Fin ((splitSpec source split first second hFirst hSecond).length slot),
          canonicalSplitStepMap source split first second hFirst hSecond hLength
            (canonicalSplitStepMapInv source split first second hFirst hSecond hLength
              ⟨slot, offset⟩) = ⟨slot, offset⟩)
      ?_ (fun old => ?_) slot offset
    · intro secondOffset
      change canonicalSplitStepMap source split first second hFirst hSecond hLength
        (canonicalSplitStepMapInv source split first second hFirst hSecond hLength
          ⟨secondSlot source, secondOffset⟩) = ⟨secondSlot source, secondOffset⟩
      rw [canonicalSplitStepMapInv_second source split first second hFirst hSecond hLength,
        canonicalSplitStepMap_split source split first second hFirst hSecond hLength]
      have hNotBefore : ¬ (first + secondOffset.val < first) := by omega
      rw [dite_eq_right hNotBefore]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        change first + secondOffset.val - first = secondOffset.val
        omega
    · intro oldOffset
      by_cases hEdge : old = split
      · subst old
        have hBefore : oldOffset.val < first := by
          simpa [splitSpec, splitLength] using oldOffset.isLt
        change canonicalSplitStepMap source split first second hFirst hSecond hLength
          (canonicalSplitStepMapInv source split first second hFirst hSecond hLength
            ⟨oldSlot source split, oldOffset⟩) = ⟨oldSlot source split, oldOffset⟩
        rw [canonicalSplitStepMapInv_old_split source split first second hFirst hSecond hLength,
          canonicalSplitStepMap_split source split first second hFirst hSecond hLength,
          dite_eq_left hBefore]

      · change canonicalSplitStepMap source split first second hFirst hSecond hLength
          (canonicalSplitStepMapInv source split first second hFirst hSecond hLength
            ⟨oldSlot source old, oldOffset⟩) = ⟨oldSlot source old, oldOffset⟩
        rw [canonicalSplitStepMapInv_old source split old first second hFirst hSecond hLength hEdge,
          canonicalSplitStepMap_old source split old first second hFirst hSecond hLength hEdge]


/-! ### Compatibility of the canonical vertex and step maps -/

/-- On old core vertices the canonical vertex equivalence is the evident
inclusion into the enlarged core. -/
@[simp] theorem canonicalSplitVertexEquiv_core
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) (vertex : Fin n) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.coreVertex vertex) =
        (splitSpec source split first second hFirst hSecond).coreVertex
          (oldVertex source vertex) := by
  rfl

/-- An interior point in an unsplit slot keeps both its slot and coordinate. -/
@[simp] theorem canonicalSplitVertexEquiv_oldInterior
    (source : SubdivisionGraph.Spec n p) (split edge : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) (hEdge : edge ≠ split)
    (offset : Fin (source.length edge - 1)) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.interiorVertex edge offset) =
        (splitSpec source split first second hFirst hSecond).interiorVertex
          (oldSlot source edge)
          ⟨offset.val, by
            simp only [splitSpec, splitLength_old, ite_eq_right hEdge]
            exact offset.isLt⟩ := by
  change canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (Sum.inr ⟨edge, offset⟩) = _
  simp [canonicalSplitVertexEquiv, canonicalSplitVertexMap, hEdge]

/-- A selected-slot interior point strictly before the split remains in the
first (old) slot. -/
@[simp] theorem canonicalSplitVertexEquiv_splitInterior_before
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (offset : Fin (source.length split - 1))
    (hBefore : offset.val + 1 < first) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.interiorVertex split offset) =
        (splitSpec source split first second hFirst hSecond).interiorVertex
          (oldSlot source split)
          ⟨offset.val, by
            simp only [splitSpec, splitLength_old, ite_true]
            omega⟩ := by
  change canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (Sum.inr ⟨split, offset⟩) = _
  simp [canonicalSplitVertexEquiv, canonicalSplitVertexMap, hBefore]

/-- The old interior position at the split becomes the fresh core vertex. -/
@[simp] theorem canonicalSplitVertexEquiv_splitInterior_at
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (offset : Fin (source.length split - 1))
    (hAt : offset.val + 1 = first) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.interiorVertex split offset) =
        (splitSpec source split first second hFirst hSecond).coreVertex
          (splitVertex source) := by
  change canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (Sum.inr ⟨split, offset⟩) = _
  simp [canonicalSplitVertexEquiv, canonicalSplitVertexMap, hAt]

/-- A selected-slot interior point strictly after the split moves to the
second slot, with its coordinate shifted by `first`. -/
@[simp] theorem canonicalSplitVertexEquiv_splitInterior_after
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (offset : Fin (source.length split - 1))
    (hAfter : first < offset.val + 1) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.interiorVertex split offset) =
        (splitSpec source split first second hFirst hSecond).interiorVertex
          (secondSlot source)
          ⟨offset.val - first, by
            simp only [splitSpec, splitLength_second]
            have _ := offset.isLt
            omega⟩ := by
  have hNotBefore : ¬ offset.val + 1 < first := by omega
  have hNotAt : ¬ offset.val + 1 = first := by omega
  change canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (Sum.inr ⟨split, offset⟩) = _
  simp [canonicalSplitVertexEquiv, canonicalSplitVertexMap, hNotBefore, hNotAt]

/-- Along an unsplit core slot, the canonical vertex equivalence agrees with
the literal numerical path position. -/
theorem canonicalSplitVertexEquiv_pathVertex_old
    (source : SubdivisionGraph.Spec n p) (split edge : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) (hEdge : edge ≠ split)
    (position : source.PathPosition edge) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.pathVertex edge position) =
      (splitSpec source split first second hFirst hSecond).pathVertex
        (oldSlot source edge)
        ⟨position.val, by
          have hLengthOld :
              (splitSpec source split first second hFirst hSecond).length
                (oldSlot source edge) = source.length edge := by
            simp [splitSpec, splitLength_old, hEdge]
          rw [hLengthOld]
          exact position.isLt⟩ := by
  have hLengthOld :
      (splitSpec source split first second hFirst hSecond).length
        (oldSlot source edge) = source.length edge := by
    simp [splitSpec, splitLength_old, hEdge]
  rcases position with ⟨position, hposition⟩
  by_cases hZero : position = 0
  · subst position
    rw [source.pathVertex_zero, canonicalSplitVertexEquiv_core]
    rw [(splitSpec source split first second hFirst hSecond).pathVertex_zero]
    exact congrArg _ (splitCore_tail_old source split edge).symm
  by_cases hLast : position = source.length edge
  · subst position
    rw [source.pathVertex_length, canonicalSplitVertexEquiv_core]
    have hTargetPosition :
        (⟨source.length edge, by omega⟩ :
          (splitSpec source split first second hFirst hSecond).PathPosition
            (oldSlot source edge)) =
          ⟨(splitSpec source split first second hFirst hSecond).length
              (oldSlot source edge), by omega⟩ := by
      apply Fin.ext
      exact hLengthOld.symm
    rw [hTargetPosition,
      (splitSpec source split first second hFirst hSecond).pathVertex_length]
    apply congrArg _
    simp [splitSpec, hEdge]
  · have hInterior : source.IsInteriorPosition edge ⟨position, hposition⟩ := by
      have hPos : 0 < position := Nat.pos_of_ne_zero hZero
      have hLe : position ≤ source.length edge := Nat.le_of_lt_succ hposition
      have hLt : position < source.length edge := Nat.lt_of_le_of_ne hLe hLast
      exact ⟨hPos, hLt⟩
    rw [source.pathVertex_eq_interiorVertex edge _ hInterior,
      canonicalSplitVertexEquiv_oldInterior source split edge first second
        hFirst hSecond hLength hEdge]
    have hTargetInterior :
        (splitSpec source split first second hFirst hSecond).IsInteriorPosition
          (oldSlot source edge)
          ⟨position, by
            rw [hLengthOld]
            exact hposition⟩ := by
      change 0 < position ∧
        position < (splitSpec source split first second hFirst hSecond).length
          (oldSlot source edge)
      rw [hLengthOld]
      exact hInterior
    rw [(splitSpec source split first second hFirst hSecond).pathVertex_eq_interiorVertex
      (oldSlot source edge) _ hTargetInterior]
    congr 3

/-- On the first segment of the selected slot, numerical path positions are
unchanged.  The common endpoint at `first` is the fresh core vertex. -/
theorem canonicalSplitVertexEquiv_pathVertex_split_first
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (position : source.PathPosition split) (hLe : position.val ≤ first) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.pathVertex split position) =
      (splitSpec source split first second hFirst hSecond).pathVertex
        (oldSlot source split)
        ⟨position.val, by
          have hTargetLength :
              (splitSpec source split first second hFirst hSecond).length
                (oldSlot source split) = first := by
            change splitLength source split first second (oldSlot source split) = first
            rw [splitLength_old]
            simp
          omega⟩ := by
  have hTargetLength :
      (splitSpec source split first second hFirst hSecond).length
        (oldSlot source split) = first := by
    change splitLength source split first second (oldSlot source split) = first
    rw [splitLength_old]
    simp
  rcases position with ⟨position, hposition⟩
  by_cases hAt : position = first
  · subst position
    let offset : Fin (source.length split - 1) :=
      ⟨first - 1, by rw [hLength]; omega⟩
    have hSourceInterior : source.IsInteriorPosition split ⟨first, hposition⟩ := by
      constructor
      · exact hFirst
      · omega
    have hSourcePath : source.pathVertex split ⟨first, hposition⟩ =
        source.interiorVertex split offset := by
      rw [source.pathVertex_eq_interiorVertex split _ hSourceInterior]
      congr 3
    rw [hSourcePath,
      canonicalSplitVertexEquiv_splitInterior_at source split first second
        hFirst hSecond hLength offset (by
          dsimp [offset]
          omega)]
    have hTargetPosition :
        (⟨first, by omega⟩ :
          (splitSpec source split first second hFirst hSecond).PathPosition
            (oldSlot source split)) =
          ⟨(splitSpec source split first second hFirst hSecond).length
              (oldSlot source split), by omega⟩ := by
      apply Fin.ext
      exact hTargetLength.symm
    rw [hTargetPosition,
      (splitSpec source split first second hFirst hSecond).pathVertex_length]
    have hHead :
        (splitSpec source split first second hFirst hSecond).core.head
          (oldSlot source split) = splitVertex source := by
      simp [splitSpec]
    exact congrArg _ hHead.symm
  · by_cases hZero : position = 0
    · subst position
      rw [source.pathVertex_zero, canonicalSplitVertexEquiv_core]
      rw [(splitSpec source split first second hFirst hSecond).pathVertex_zero]
      exact congrArg _ (splitCore_tail_old source split split).symm
    · have hLt : position < first := Nat.lt_of_le_of_ne hLe hAt
      let offset : Fin (source.length split - 1) :=
        ⟨position - 1, by
          have hPos : 0 < position := Nat.pos_of_ne_zero hZero
          omega⟩
      have hSourceInterior : source.IsInteriorPosition split ⟨position, hposition⟩ := by
        have hPos : 0 < position := Nat.pos_of_ne_zero hZero
        have hTotal : first < source.length split := by omega
        exact ⟨hPos, Nat.lt_trans hLt hTotal⟩
      have hSourcePath : source.pathVertex split ⟨position, hposition⟩ =
          source.interiorVertex split offset := by
        rw [source.pathVertex_eq_interiorVertex split _ hSourceInterior]
        congr 3
      rw [hSourcePath,
        canonicalSplitVertexEquiv_splitInterior_before source split first second
          hFirst hSecond hLength offset (by
            dsimp [offset]
            omega)]
      have hTargetInterior :
          (splitSpec source split first second hFirst hSecond).IsInteriorPosition
            (oldSlot source split) ⟨position, by omega⟩ := by
        change 0 < position ∧ position <
          (splitSpec source split first second hFirst hSecond).length
            (oldSlot source split)
        rw [hTargetLength]
        exact ⟨Nat.pos_of_ne_zero hZero, hLt⟩
      rw [(splitSpec source split first second hFirst hSecond).pathVertex_eq_interiorVertex
        (oldSlot source split) _ hTargetInterior]
      congr 3

/-- The point at which a slot is split is carried to the fresh bivalent core
vertex.  This proof-term-stable endpoint form is the one used by generated
multi-split certificates. -/
theorem canonicalSplitVertexEquiv_pathVertex_at_split
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.pathVertex split ⟨first, by rw [hLength]; omega⟩) =
      (splitSpec source split first second hFirst hSecond).coreVertex
        (splitVertex source) := by
  have hFirstSegment := canonicalSplitVertexEquiv_pathVertex_split_first
    source split first second hFirst hSecond hLength
    (⟨first, by rw [hLength]; omega⟩ : source.PathPosition split) (by rfl)
  rw [hFirstSegment]
  have hTargetPosition :
      (⟨first, by simp [splitSpec, splitLength_old]⟩ :
        (splitSpec source split first second hFirst hSecond).PathPosition
          (oldSlot source split)) =
        ⟨(splitSpec source split first second hFirst hSecond).length
            (oldSlot source split), by omega⟩ := by
    apply Fin.ext
    simp [splitSpec, splitLength_old]
  rw [hTargetPosition,
    (splitSpec source split first second hFirst hSecond).pathVertex_length]
  congr 1
  simp [splitSpec]

/-- On the second segment of the selected slot, subtracting `first` gives
the literal numerical path position in the new last slot.  The position zero
of that slot is the fresh core vertex. -/
private theorem canonicalSplitVertexEquiv_pathVertex_split_second
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (position : Fin (second + 1)) :
    canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
      (source.pathVertex split
        ⟨first + position.val, by have := position.isLt; omega⟩) =
      (splitSpec source split first second hFirst hSecond).pathVertex
        (secondSlot source)
        ⟨position.val, by
          simpa [splitSpec, splitLength, secondSlot] using position.isLt⟩ := by
  rcases position with ⟨position, hposition⟩
  by_cases hZero : position = 0
  · subst position
    have hFirstLt : first < source.length split := by
      rw [hLength]
      omega
    let offset : Fin (source.length split - 1) :=
      ⟨first - 1, by omega⟩
    have hSourceInterior : source.IsInteriorPosition split
        ⟨first, Nat.lt_succ_of_lt hFirstLt⟩ :=
      ⟨hFirst, hFirstLt⟩
    have hSourcePath : source.pathVertex split
        ⟨first, Nat.lt_succ_of_lt hFirstLt⟩ =
        source.interiorVertex split offset := by
      rw [source.pathVertex_eq_interiorVertex split _ hSourceInterior]
      congr 3
    have hCanonical :
        canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
          (source.pathVertex split ⟨first, Nat.lt_succ_of_lt hFirstLt⟩) =
        (splitSpec source split first second hFirst hSecond).pathVertex
          (secondSlot source)
          ⟨0, by simp [splitSpec, splitLength, secondSlot]⟩ := by
      rw [hSourcePath,
        canonicalSplitVertexEquiv_splitInterior_at source split first second
          hFirst hSecond hLength offset (by
            dsimp [offset]
            omega),
        (splitSpec source split first second hFirst hSecond).pathVertex_zero]
      congr 1
      simp [splitSpec]
    exact hCanonical
  · by_cases hLast : position = second
    · subst position
      have hSourceLast :
          (⟨first + second, by omega⟩ : source.PathPosition split) =
            ⟨source.length split, by omega⟩ := by
        apply Fin.ext
        exact hLength.symm
      have hTargetLast :
          (⟨second, by simp [splitSpec, splitLength, secondSlot]⟩ :
            (splitSpec source split first second hFirst hSecond).PathPosition
              (secondSlot source)) =
            ⟨(splitSpec source split first second hFirst hSecond).length
                (secondSlot source), by simp [splitSpec, splitLength, secondSlot]⟩ := by
        apply Fin.ext
        simp [splitSpec, splitLength, secondSlot]
      rw [hSourceLast, source.pathVertex_length,
        canonicalSplitVertexEquiv_core, hTargetLast,
        (splitSpec source split first second hFirst hSecond).pathVertex_length]
      congr 1
      simp [splitSpec]
    · have hPos : 0 < position := Nat.pos_of_ne_zero hZero
      have hLt : position < second := by
        have hLe : position ≤ second := Nat.le_of_lt_succ hposition
        exact Nat.lt_of_le_of_ne hLe hLast
      have hSourcePositionLt : first + position < source.length split := by
        rw [hLength]
        omega
      let offset : Fin (source.length split - 1) :=
        ⟨first + position - 1, by
          rw [hLength]
          omega⟩
      have hSourceInterior : source.IsInteriorPosition split
          ⟨first + position, by exact Nat.lt_succ_of_lt hSourcePositionLt⟩ := by
        change 0 < first + position ∧ first + position < source.length split
        exact ⟨by omega, hSourcePositionLt⟩
      have hSourcePath : source.pathVertex split
          ⟨first + position, by exact Nat.lt_succ_of_lt hSourcePositionLt⟩ =
          source.interiorVertex split offset := by
        rw [source.pathVertex_eq_interiorVertex split _ hSourceInterior]
        congr 3
      rw [hSourcePath,
        canonicalSplitVertexEquiv_splitInterior_after source split first second
          hFirst hSecond hLength offset (by
            dsimp [offset]
            omega)]
      have hTargetInterior :
          (splitSpec source split first second hFirst hSecond).IsInteriorPosition
            (secondSlot source) ⟨position, by
              simpa [splitSpec, splitLength, secondSlot] using hposition⟩ := by
        change 0 < position ∧ position <
          (splitSpec source split first second hFirst hSecond).length
            (secondSlot source)
        have hTargetLength :
            (splitSpec source split first second hFirst hSecond).length
                (secondSlot source) = second := by
          simp [splitSpec, splitLength, secondSlot]
        rw [hTargetLength]
        exact ⟨hPos, hLt⟩
      rw [(splitSpec source split first second hFirst hSecond).pathVertex_eq_interiorVertex
        (secondSlot source) _ hTargetInterior]
      congr 2
      dsimp [offset]
      omega

/-- Unit steps on the divided slot preserve their ordered endpoints in both new segments. -/
private theorem canonicalSplit_unitEdge_eq_split
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (offset : Fin (source.length split)) :
    (splitSpec source split first second hFirst hSecond).unitEdge
      (canonicalSplitStepEquiv source split first second hFirst hSecond hLength ⟨split, offset⟩) =
      (canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
        (source.unitEdge ⟨split, offset⟩).1,
       canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
        (source.unitEdge ⟨split, offset⟩).2) := by
  change (splitSpec source split first second hFirst hSecond).unitEdge
    (canonicalSplitStepMap source split first second hFirst hSecond hLength
      ⟨split, offset⟩) = _
  by_cases hBefore : offset.val < first
  · let targetOffset : Fin
        ((splitSpec source split first second hFirst hSecond).length
          (oldSlot source split)) :=
      ⟨offset.val, by
        simp [splitSpec, splitLength, oldSlot, hBefore]⟩
    have hMapped : canonicalSplitStepMap source split first second hFirst hSecond hLength
        ⟨split, offset⟩ = ⟨oldSlot source split, targetOffset⟩ := by
      rw [canonicalSplitStepMap_split source split first second hFirst hSecond hLength,
        dite_eq_left hBefore]
    rw [hMapped]
    change
      ((splitSpec source split first second hFirst hSecond).stepLeft
          (oldSlot source split) targetOffset,
        (splitSpec source split first second hFirst hSecond).stepRight
          (oldSlot source split) targetOffset) = _
    have hTargetLeft :
        (splitSpec source split first second hFirst hSecond).stepLeftPosition
            (oldSlot source split) targetOffset =
          ⟨(source.stepLeftPosition split offset).val, by
            simp only [SubdivisionGraph.Spec.stepLeftPosition, Fin.val_mk]
            simp only [splitSpec, oldSlot, splitLength, Fin.lastCases_castSucc, ↓reduceIte,
              Order.lt_add_one_iff]
            omega⟩ := by
      apply Fin.ext
      rfl
    have hTargetRight :
        (splitSpec source split first second hFirst hSecond).stepRightPosition
            (oldSlot source split) targetOffset =
          ⟨(source.stepRightPosition split offset).val, by
            simp only [SubdivisionGraph.Spec.stepRightPosition, Fin.val_mk]
            simp only [splitSpec, oldSlot, splitLength, Fin.lastCases_castSucc, ↓reduceIte,
              Order.lt_add_one_iff, Order.add_one_le_iff]
            omega⟩ := by
      apply Fin.ext
      rfl
    rw [← (splitSpec source split first second hFirst hSecond).pathVertex_stepLeftPosition
        (oldSlot source split) targetOffset,
      ← (splitSpec source split first second hFirst hSecond).pathVertex_stepRightPosition
        (oldSlot source split) targetOffset,
      hTargetLeft, hTargetRight,
      ← canonicalSplitVertexEquiv_pathVertex_split_first source split first second
        hFirst hSecond hLength (source.stepLeftPosition split offset) (by
          change offset.val ≤ first
          exact Nat.le_of_lt hBefore),
      ← canonicalSplitVertexEquiv_pathVertex_split_first source split first second
        hFirst hSecond hLength (source.stepRightPosition split offset) (by
          change offset.val + 1 ≤ first
          omega),
      source.pathVertex_stepLeftPosition,
      source.pathVertex_stepRightPosition]
    rfl
  · rw [canonicalSplitStepMap_split source split first second hFirst hSecond hLength,
      dite_eq_right hBefore]
    have hFirstLe : first ≤ offset.val := Nat.le_of_not_gt hBefore
    have hOffsetLt : offset.val < first + second := by
      rw [← hLength]
      exact offset.isLt
    let targetOffset : Fin
        ((splitSpec source split first second hFirst hSecond).length
          (secondSlot source)) :=
      ⟨offset.val - first, by
        simp only [splitSpec, secondSlot, splitLength, Fin.lastCases_last]
        omega⟩
    have hOffsetDecomp : first + targetOffset.val = offset.val := by
      dsimp [targetOffset]
      omega
    have hLeftBound : first + targetOffset.val < source.length split := by
      rw [hOffsetDecomp]
      exact offset.isLt
    have hRightBound : first + targetOffset.val + 1 < source.length split + 1 := by
      rw [hOffsetDecomp]
      omega
    have hLeftPosition : source.stepLeftPosition split offset =
        ⟨first + targetOffset.val, by
          exact Nat.lt_succ_of_lt hLeftBound⟩ := by
      apply Fin.ext
      change offset.val = first + targetOffset.val
      exact hOffsetDecomp.symm
    have hRightPosition : source.stepRightPosition split offset =
        ⟨first + targetOffset.val + 1, by
          exact hRightBound⟩ := by
      apply Fin.ext
      change offset.val + 1 = first + targetOffset.val + 1
      omega
    change (splitSpec source split first second hFirst hSecond).unitEdge
      ⟨secondSlot source, targetOffset⟩ = _
    change
      ((splitSpec source split first second hFirst hSecond).stepLeft
          (secondSlot source) targetOffset,
        (splitSpec source split first second hFirst hSecond).stepRight
          (secondSlot source) targetOffset) = _
    let targetLeftPosition : Fin (second + 1) :=
      ⟨targetOffset.val, by
        have := targetOffset.isLt
        simp only [splitSpec, secondSlot, splitLength, Fin.lastCases_last] at this
        omega⟩
    let targetRightPosition : Fin (second + 1) :=
      ⟨targetOffset.val + 1, by
        have := targetOffset.isLt
        simp only [splitSpec, secondSlot, splitLength, Fin.lastCases_last] at this
        omega⟩
    have hTargetLeft :
        (splitSpec source split first second hFirst hSecond).stepLeftPosition
            (secondSlot source) targetOffset =
          ⟨targetLeftPosition.val, by
            simp only [splitSpec, secondSlot, splitLength, Fin.lastCases_last,
              Order.lt_add_one_iff]
            have := targetLeftPosition.isLt
            omega⟩ := by
      apply Fin.ext
      rfl
    have hTargetRight :
        (splitSpec source split first second hFirst hSecond).stepRightPosition
            (secondSlot source) targetOffset =
          ⟨targetRightPosition.val, by
            simp only [splitSpec, secondSlot, splitLength, Fin.lastCases_last,
              Order.lt_add_one_iff]
            have := targetRightPosition.isLt
            omega⟩ := by
      apply Fin.ext
      rfl
    have hRightPosition' :
        (⟨first + targetRightPosition.val, by
          dsimp [targetRightPosition]
          omega⟩ : source.PathPosition split) =
        source.stepRightPosition split offset := by
      apply Fin.ext
      change first + targetRightPosition.val = offset.val + 1
      dsimp [targetRightPosition]
      omega
    rw [← (splitSpec source split first second hFirst hSecond).pathVertex_stepLeftPosition
        (secondSlot source) targetOffset,
      ← (splitSpec source split first second hFirst hSecond).pathVertex_stepRightPosition
        (secondSlot source) targetOffset,
      hTargetLeft, hTargetRight,
      ← canonicalSplitVertexEquiv_pathVertex_split_second source split first second
        hFirst hSecond hLength targetLeftPosition,
      ← canonicalSplitVertexEquiv_pathVertex_split_second source split first second
        hFirst hSecond hLength targetRightPosition,
      ← hLeftPosition, hRightPosition',
      source.pathVertex_stepLeftPosition,
      source.pathVertex_stepRightPosition]
    rfl

/-- Each emitted unit step has exactly the same ordered endpoints after the
canonical split.  Unlike a slotwise relabeling, no orientation reversal is
needed: only the slot containing a position changes. -/
theorem canonicalSplit_unitEdge_eq
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second)
    (step : source.Step) :
    (splitSpec source split first second hFirst hSecond).unitEdge
      (canonicalSplitStepEquiv source split first second hFirst hSecond hLength step) =
      (canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
        (source.unitEdge step).1,
       canonicalSplitVertexEquiv source split first second hFirst hSecond hLength
        (source.unitEdge step).2) := by
  rcases step with ⟨edge, offset⟩
  by_cases hEdge : edge = split
  · subst edge
    exact canonicalSplit_unitEdge_eq_split source split first second hFirst hSecond hLength offset
  · change (splitSpec source split first second hFirst hSecond).unitEdge
      (canonicalSplitStepMap source split first second hFirst hSecond hLength
        ⟨edge, offset⟩) = _
    rw [canonicalSplitStepMap_old source split edge first second hFirst hSecond
      hLength hEdge]
    let targetOffset : Fin
        ((splitSpec source split first second hFirst hSecond).length
          (oldSlot source edge)) :=
      ⟨offset.val, by
        simp [splitSpec, splitLength, oldSlot, hEdge]⟩
    change (splitSpec source split first second hFirst hSecond).unitEdge
      ⟨oldSlot source edge, targetOffset⟩ = _
    change
      ((splitSpec source split first second hFirst hSecond).stepLeft
          (oldSlot source edge) targetOffset,
        (splitSpec source split first second hFirst hSecond).stepRight
          (oldSlot source edge) targetOffset) = _
    have hTargetLeft :
        (splitSpec source split first second hFirst hSecond).stepLeftPosition
            (oldSlot source edge) targetOffset =
          ⟨(source.stepLeftPosition edge offset).val, by
            simp only [SubdivisionGraph.Spec.stepLeftPosition, Fin.val_mk]
            simp [splitSpec, splitLength, oldSlot, hEdge]⟩ := by
      apply Fin.ext
      rfl
    have hTargetRight :
        (splitSpec source split first second hFirst hSecond).stepRightPosition
            (oldSlot source edge) targetOffset =
          ⟨(source.stepRightPosition edge offset).val, by
            simp only [SubdivisionGraph.Spec.stepRightPosition, Fin.val_mk]
            simp [splitSpec, splitLength, oldSlot, hEdge]⟩ := by
      apply Fin.ext
      rfl
    rw [← (splitSpec source split first second hFirst hSecond).pathVertex_stepLeftPosition
        (oldSlot source edge) targetOffset,
      ← (splitSpec source split first second hFirst hSecond).pathVertex_stepRightPosition
        (oldSlot source edge) targetOffset,
      hTargetLeft, hTargetRight,
      ← canonicalSplitVertexEquiv_pathVertex_old source split edge first second
        hFirst hSecond hLength hEdge (source.stepLeftPosition edge offset),
      ← canonicalSplitVertexEquiv_pathVertex_old source split edge first second
        hFirst hSecond hLength hEdge (source.stepRightPosition edge offset),
      source.pathVertex_stepLeftPosition,
      source.pathVertex_stepRightPosition]
    rfl

/-- Splitting one positive-length slot through a new bivalent core vertex
preserves the subdivision graph in the Laplacian sense used by certificate
checking. -/
def canonicalSplitLaplacianEquiv
    (source : SubdivisionGraph.Spec n p) (split : Fin p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second)
    (hLength : source.length split = first + second) :
    LaplacianEquiv source.graph
      (splitSpec source split first second hFirst hSecond).graph :=
  laplacianEquivOfUnitSteps source
    (splitSpec source split first second hFirst hSecond)
    (canonicalSplitVertexEquiv source split first second hFirst hSecond hLength)
    (canonicalSplitStepEquiv source split first second hFirst hSecond hLength)
    (canonicalSplit_unitEdge_eq source split first second hFirst hSecond hLength)

/-! ## Identity refinement -/

/-- The identity refinement uses the reflexive vertex and occurrence
bijections. -/
def identityLaplacianEquiv (source : SubdivisionGraph.Spec n p) :
    LaplacianEquiv source.graph source.graph :=
  laplacianEquivOfUnitSteps source source (Equiv.refl source.Vertex)
    (Equiv.refl source.Step) (fun _step => rfl)

@[simp] theorem identity_num_edges (source : SubdivisionGraph.Spec n p)
    (x y : source.Vertex) :
    numEdges source.graph (identityLaplacianEquiv source x)
        (identityLaplacianEquiv source y) = numEdges source.graph x y :=
  (identityLaplacianEquiv source).num_edges_eq x y

end Utilities.Certificate.OneEdgeSplitRefinement
