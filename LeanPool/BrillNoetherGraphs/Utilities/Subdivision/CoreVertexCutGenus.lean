/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCut

/-!
# Genus of factors cut from a subdivided core

The finite core-cut checker already lifts articulation data uniformly over
all positive integral edge lengths.  This file computes the genera of the
two induced factors from the same finite data.  Counts are made on ordered
core **slots**, not endpoint pairs, so parallel occurrences remain distinct.

Every slot wholly contained in one core side contributes its entire
subdivided path to that factor.  Its `L` unit edges and `L - 1` new vertices
cancel in Euler characteristic, leaving one edge-slot contribution.  Hence
the answer is independent of every subdivision length.
-/

namespace Utilities.Certificate

open Finset
open ExplicitPotential

namespace CoreVertexCut.Data

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

/-- A core edge occurrence lies wholly in the named side. -/
def LeftSlot (c : CoreVertexCut.Data core) (edge : Fin p) : Prop :=
  core.tail edge ∈ c.left ∧ core.head edge ∈ c.left

instance leftSlotDecidable (c : CoreVertexCut.Data core) (edge : Fin p) :
    Decidable (c.LeftSlot edge) := by
  unfold LeftSlot
  infer_instance

/-- A core edge occurrence lies wholly in the derived complementary side. -/
def RightSlot (c : CoreVertexCut.Data core) (edge : Fin p) : Prop :=
  core.tail edge ∈ c.right ∧ core.head edge ∈ c.right

instance rightSlotDecidable (c : CoreVertexCut.Data core) (edge : Fin p) :
    Decidable (c.RightSlot edge) := by
  unfold RightSlot
  infer_instance

/-- Ordered core slots wholly contained in the named side. -/
def leftSlots (c : CoreVertexCut.Data core) : Finset (Fin p) :=
  Finset.univ.filter c.LeftSlot

/-- Ordered core slots wholly contained in the complementary side. -/
def rightSlots (c : CoreVertexCut.Data core) : Finset (Fin p) :=
  Finset.univ.filter c.RightSlot

/-- Executable number of ordered core slots in the named side. -/
def leftSlotCount (c : CoreVertexCut.Data core) : ℕ :=
  c.leftSlots.card

/-- Executable number of ordered core slots in the complementary side. -/
def rightSlotCount (c : CoreVertexCut.Data core) : ℕ :=
  c.rightSlots.card

/-- Cyclomatic genus predicted from the named core side. -/
def leftGenus (c : CoreVertexCut.Data core) : ℤ :=
  (c.leftSlotCount : ℤ) - (c.left.card : ℤ) + 1

/-- Cyclomatic genus predicted from the complementary core side. -/
def rightGenus (c : CoreVertexCut.Data core) : ℤ :=
  (c.rightSlotCount : ℤ) - (c.right.card : ℤ) + 1

@[simp] theorem leftSlotCount_eq_card (c : CoreVertexCut.Data core) :
    c.leftSlotCount = c.leftSlots.card := rfl

@[simp] theorem rightSlotCount_eq_card (c : CoreVertexCut.Data core) :
    c.rightSlotCount = c.rightSlots.card := rfl

@[simp] theorem mem_leftSlots (c : CoreVertexCut.Data core) (edge : Fin p) :
    edge ∈ c.leftSlots ↔ c.LeftSlot edge := by
  simp [leftSlots]

@[simp] theorem mem_rightSlots (c : CoreVertexCut.Data core) (edge : Fin p) :
    edge ∈ c.rightSlots ↔ c.RightSlot edge := by
  simp [rightSlots]

@[simp] theorem mem_right_iff (c : CoreVertexCut.Data core) (vertex : Fin n) :
    vertex ∈ c.right ↔ vertex = c.glue ∨ vertex ∉ c.left := by
  simp [CoreVertexCut.Data.right]

/-- The two core vertex sides overlap only in the retained articulation, so
their cardinalities add to one more than the ambient core cardinality. -/
theorem right_card_add_left_card (c : CoreVertexCut.Data core) (h : c.Valid) :
    c.right.card + c.left.card = n + 1 := by
  have hGlueNotMem : c.glue ∉ (Finset.univ \ c.left) := by
    simp [h.1]
  rw [CoreVertexCut.Data.right, Finset.card_insert_of_notMem hGlueNotMem]
  have hDiff := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ c.left)
  have hUniv : (Finset.univ : Finset (Fin n)).card = n := by simp
  omega

/-- Valid cut data assigns every core slot wholly to at least one side. -/
theorem leftSlot_or_rightSlot (c : CoreVertexCut.Data core) (h : c.Valid)
    (edge : Fin p) : c.LeftSlot edge ∨ c.RightSlot edge := by
  by_cases hTail : core.tail edge ∈ c.left
  · by_cases hHead : core.head edge ∈ c.left
    · exact Or.inl ⟨hTail, hHead⟩
    · right
      have hTailGlue : core.tail edge = c.glue := by
        by_contra hNe
        exact (h.2 edge) (Or.inl ⟨hTail, hNe, hHead⟩)
      exact ⟨(c.mem_right_iff _).mpr (Or.inl hTailGlue),
        (c.mem_right_iff _).mpr (Or.inr hHead)⟩
  · right
    have hTailRight : core.tail edge ∈ c.right :=
      (c.mem_right_iff _).mpr (Or.inr hTail)
    by_cases hHead : core.head edge ∈ c.left
    · have hHeadGlue : core.head edge = c.glue := by
        by_contra hNe
        exact (h.2 edge) (Or.inr ⟨hHead, hNe, hTail⟩)
      exact ⟨hTailRight, (c.mem_right_iff _).mpr (Or.inl hHeadGlue)⟩
    · exact ⟨hTailRight, (c.mem_right_iff _).mpr (Or.inr hHead)⟩

/-- On a loopless core, no slot lies in both core sides: that would force
both endpoints to equal the unique common articulation. -/
theorem not_leftSlot_and_rightSlot (c : CoreVertexCut.Data core)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (edge : Fin p) : ¬(c.LeftSlot edge ∧ c.RightSlot edge) := by
  rintro ⟨⟨hTailLeft, hHeadLeft⟩, hTailRight, hHeadRight⟩
  have hTailGlue : core.tail edge = c.glue := by
    rcases (c.mem_right_iff _).mp hTailRight with hGlue | hNotLeft
    · exact hGlue
    · exact False.elim (hNotLeft hTailLeft)
  have hHeadGlue : core.head edge = c.glue := by
    rcases (c.mem_right_iff _).mp hHeadRight with hGlue | hNotLeft
    · exact hGlue
    · exact False.elim (hNotLeft hHeadLeft)
  exact hLoopless edge (hTailGlue.trans hHeadGlue.symm)

/-- The named and complementary slot sets are disjoint. -/
theorem leftSlots_disjoint_rightSlots (c : CoreVertexCut.Data core)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) :
    Disjoint c.leftSlots c.rightSlots := by
  rw [Finset.disjoint_left]
  intro edge hLeft hRight
  exact c.not_leftSlot_and_rightSlot hLoopless edge
    ⟨(c.mem_leftSlots edge).mp hLeft, (c.mem_rightSlots edge).mp hRight⟩

/-- The two side slot counts add to the number of ambient core occurrences. -/
theorem leftSlots_card_add_rightSlots_card (c : CoreVertexCut.Data core)
    (h : c.Valid)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) :
    c.leftSlots.card + c.rightSlots.card = p := by
  have hUnion : c.leftSlots ∪ c.rightSlots = (Finset.univ : Finset (Fin p)) := by
    ext edge
    simp only [Finset.mem_union, mem_leftSlots, mem_rightSlots,
      Finset.mem_univ, iff_true]
    exact c.leftSlot_or_rightSlot h edge
  rw [← Finset.card_union_of_disjoint
    (c.leftSlots_disjoint_rightSlots hLoopless), hUnion]
  simp

/-- Core-computed factor genera add to the cyclomatic genus of the ambient
loopless core. -/
theorem leftGenus_add_rightGenus (c : CoreVertexCut.Data core) (h : c.Valid)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) :
    c.leftGenus + c.rightGenus = (p : ℤ) - (n : ℤ) + 1 := by
  have hVertices := c.right_card_add_left_card h
  have hSlots := c.leftSlots_card_add_rightSlots_card h hLoopless
  have hVerticesInt :
      (c.right.card : ℤ) + (c.left.card : ℤ) = (n : ℤ) + 1 := by
    exact_mod_cast hVertices
  have hSlotsInt :
      (c.leftSlots.card : ℤ) + (c.rightSlots.card : ℤ) = (p : ℤ) := by
    exact_mod_cast hSlots
  unfold leftGenus rightGenus leftSlotCount rightSlotCount
  omega

variable (spec : SubdivisionGraph.Spec n p)
variable (c : CoreVertexCut.Data spec.core)

/-- Both endpoints of a subdivision unit step lie in the named factor exactly
when the parent core slot lies wholly in the named core side. -/
theorem step_mem_leftVertices_iff (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    spec.stepLeft edge offset ∈ CoreVertexCut.Data.leftVertices spec c ∧
        spec.stepRight edge offset ∈ CoreVertexCut.Data.leftVertices spec c ↔
      c.LeftSlot edge := by
  unfold SubdivisionGraph.Spec.stepLeft SubdivisionGraph.Spec.stepRight
  split_ifs with hzero hlast
  · simp [LeftSlot]
  · simp [LeftSlot]
  · simp [LeftSlot]
  · simp [LeftSlot]

/-- Exact edge-occurrence count of the named induced factor. -/
theorem leftGraph_edge_card (h : c.Valid) :
    (c.toOneVertexCut spec h).leftGraph.edges.card =
      ∑ edge ∈ c.leftSlots, spec.length edge := by
  rw [OneVertexCut.leftGraph, inducedSubgraph_edge_card_eq_filter]
  change
    ((((Finset.univ : Finset spec.Step).val.map spec.unitEdge).filter
      (fun pair => pair.1 ∈ CoreVertexCut.Data.leftVertices spec c ∧
        pair.2 ∈ CoreVertexCut.Data.leftVertices spec c)).card : ℕ) = _
  rw [Multiset.filter_map, Multiset.card_map]
  change
    ((Finset.univ.filter (fun step : spec.Step =>
      (spec.unitEdge step).1 ∈ CoreVertexCut.Data.leftVertices spec c ∧
      (spec.unitEdge step).2 ∈ CoreVertexCut.Data.leftVertices spec c)).card = _)
  simp_rw [SubdivisionGraph.Spec.unitEdge]
  simp_rw [c.step_mem_leftVertices_iff spec]
  rw [Finset.card_filter, Fintype.sum_sigma]
  unfold leftSlots
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro edge _hEdge
  by_cases hSlot : c.LeftSlot edge <;> simp [hSlot]

/-- Exact vertex count of the named subdivision side: its named core
vertices, plus the interiors of precisely its wholly contained slots. -/
theorem leftVertices_card :
    (CoreVertexCut.Data.leftVertices spec c).card =
      c.left.card + ∑ edge ∈ c.leftSlots, (spec.length edge - 1) := by
  classical
  unfold CoreVertexCut.Data.leftVertices
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp only [Fintype.sum_sigma]
  simp only [leftSlots, LeftSlot, sum_filter]
  congr 1
  · let indicator : Fin n → ℕ := fun vertex =>
      @ite ℕ
        (match (Sum.inl vertex : spec.Vertex) with
          | Sum.inl coreVertex => coreVertex ∈ c.left
          | Sum.inr interior =>
              spec.core.tail interior.1 ∈ c.left ∧
                spec.core.head interior.1 ∈ c.left)
        (Classical.propDecidable _) 1 0
    change (∑ vertex : Fin n, indicator vertex) = c.left.card
    have hIndicator : indicator = fun vertex =>
        if vertex ∈ c.left then 1 else 0 := by
      funext vertex
      by_cases hVertex : vertex ∈ c.left <;> simp [indicator, hVertex]
    rw [hIndicator]
    change
      (∑ vertex ∈ (Finset.univ : Finset (Fin n)),
        if vertex ∈ c.left then 1 else 0) = c.left.card
    rw [← Finset.natCast_card_filter]
    simp
  apply Finset.sum_congr rfl
  intro edge _hEdge
  by_cases hSlot :
      spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left <;>
    simp [hSlot]

/-- Exact vertex count of the named induced factor. -/
theorem leftGraph_vertex_card (h : c.Valid) :
    Fintype.card (c.toOneVertexCut spec h).leftGraph.V =
      c.left.card + ∑ edge ∈ c.leftSlots, (spec.length edge - 1) := by
  rw [OneVertexCut.leftGraph, inducedSubgraph_vertex_card]
  exact c.leftVertices_card spec

/-- The named induced factor has the core-computed genus, independently of
all positive subdivision lengths. -/
@[simp] theorem leftGraph_genus (h : c.Valid) :
    genus (c.toOneVertexCut spec h).leftGraph = c.leftGenus := by
  have hTerm (edge : Fin p) :
      spec.length edge - 1 + 1 = spec.length edge := by
    have := spec.length_pos edge
    omega
  have hSum :
      (∑ edge ∈ c.leftSlots, (spec.length edge - 1)) +
          c.leftSlots.card =
        ∑ edge ∈ c.leftSlots, spec.length edge := by
    calc
      (∑ edge ∈ c.leftSlots, (spec.length edge - 1)) +
            c.leftSlots.card =
          ∑ edge ∈ c.leftSlots, ((spec.length edge - 1) + 1) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = ∑ edge ∈ c.leftSlots, spec.length edge := by
        apply Finset.sum_congr rfl
        intro edge _hEdge
        exact hTerm edge
  unfold genus leftGenus leftSlotCount
  rw [c.leftGraph_edge_card spec h, c.leftGraph_vertex_card spec h]
  push_cast
  have hSumInt :
      ((∑ edge ∈ c.leftSlots, (spec.length edge - 1) : ℕ) : ℤ) +
          (c.leftSlots.card : ℤ) =
        ((∑ edge ∈ c.leftSlots, spec.length edge : ℕ) : ℤ) := by
    exact_mod_cast hSum
  push_cast at hSumInt
  omega

/-- The complementary induced factor has its core-computed genus,
independently of all positive subdivision lengths. -/
@[simp] theorem rightGraph_genus (h : c.Valid) :
    genus (c.toOneVertexCut spec h).rightGraph = c.rightGenus := by
  have hCut := (c.toOneVertexCut spec h).genus_eq
  rw [spec.genus_graph, c.leftGraph_genus spec h] at hCut
  have hCore := c.leftGenus_add_rightGenus h spec.core_loopless
  omega

/-- Both computed factor genera sum to the genus of every positive
subdivision of the core. -/
theorem leftGenus_add_rightGenus_eq_graph_genus (h : c.Valid) :
    c.leftGenus + c.rightGenus = genus spec.graph := by
  rw [spec.genus_graph]
  exact c.leftGenus_add_rightGenus h spec.core_loopless

/-- Checker-facing form of the named factor genus calculation. -/
@[simp] theorem leftGraph_genus_of_check (hCheck : c.check = true) :
    genus (c.cutOfCheck spec hCheck).leftGraph = c.leftGenus := by
  unfold CoreVertexCut.Data.cutOfCheck
  exact c.leftGraph_genus spec (c.check_eq_true_iff.mp hCheck)

/-- Checker-facing form of the complementary factor genus calculation. -/
@[simp] theorem rightGraph_genus_of_check (hCheck : c.check = true) :
    genus (c.cutOfCheck spec hCheck).rightGraph = c.rightGenus := by
  unfold CoreVertexCut.Data.cutOfCheck
  exact c.rightGraph_genus spec (c.check_eq_true_iff.mp hCheck)

/-! ## Closed non-unit, parallel-slot regression

The core below is two pairs of parallel slots meeting at the articulation.
All four subdivision lengths exceed one and are unequal.  Each induced factor
is therefore a subdivided cycle, and its checked core genus is one.
-/

private def twoCycleCore : ExplicitPotential.Core 3 4 where
  tail
    | 0 => 0
    | 1 => 0
    | 2 => 1
    | 3 => 1
  head
    | 0 => 1
    | 1 => 1
    | 2 => 2
    | 3 => 2

private def twoCycleCut : CoreVertexCut.Data twoCycleCore where
  glue := 1
  left := {0, 1}

private theorem twoCycleCut_check : twoCycleCut.check = true := by
  decide

private def twoCycleSpec : SubdivisionGraph.Spec 3 4 where
  core := twoCycleCore
  length
    | 0 => 2
    | 1 => 3
    | 2 => 4
    | 3 => 5
  core_nonempty := by decide
  core_loopless := by decide
  length_pos := by decide

private theorem twoCycleCut_leftGenus : twoCycleCut.leftGenus = 1 := by
  decide

private theorem twoCycleCut_rightGenus : twoCycleCut.rightGenus = 1 := by
  decide

private theorem twoCycleCut_leftGraph_genus :
    genus (twoCycleCut.cutOfCheck twoCycleSpec twoCycleCut_check).leftGraph = 1 := by
  calc
    genus (twoCycleCut.cutOfCheck twoCycleSpec twoCycleCut_check).leftGraph =
        twoCycleCut.leftGenus := by
      simp [twoCycleSpec]
    _ = 1 := twoCycleCut_leftGenus

private theorem twoCycleCut_rightGraph_genus :
    genus (twoCycleCut.cutOfCheck twoCycleSpec twoCycleCut_check).rightGraph = 1 := by
  calc
    genus (twoCycleCut.cutOfCheck twoCycleSpec twoCycleCut_check).rightGraph =
        twoCycleCut.rightGenus := by
      simp [twoCycleSpec]
    _ = 1 := twoCycleCut_rightGenus

end CoreVertexCut.Data

end Utilities.Certificate
