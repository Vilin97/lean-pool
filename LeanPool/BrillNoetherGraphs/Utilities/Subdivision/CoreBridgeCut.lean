/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionGraph
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutGenus
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeCut

/-!
# Checked core bridge cuts and subdivision lifts

A separating edge of a finite core remains a separating *unit edge* after
arbitrary positive subdivision.  This file makes that elementary fact
occurrence-safe: the selected ordered core slot is cut at its first unit step,
and all of its interior vertices are put on the head side.  Thus no choice of
an interior point, and no assumption that a bridge has length one, is hidden
in a generated core row.
-/

@[expose] public section

namespace MarkedGraphs.Certificate
open Utilities.Certificate

open Utilities

open Finset
open ExplicitPotential

namespace CoreBridgeCut

universe u

/-- Proof-free data for an oriented separating core slot.  `left` is the
tail side; the head side is its complement. -/
structure Data {n p : ℕ} (core : ExplicitPotential.Core n p) where
  /-- The chosen tail-side core vertices; validity requires the distinguished bridge to leave
  this set. -/
  left : Finset (Fin n)
  /-- The candidate separating slot, oriented from the chosen left side to its complement. -/
  bridge : Fin p

namespace Data

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

/-- Forgetting that the distinguished core edge is a bridge gives an
articulation cut at its tail.  This is useful because the existing
`CoreVertexCut` genus calculator can then be reused verbatim. -/
def toCoreVertexCut (c : Data core) : CoreVertexCut.Data core where
  glue := core.tail c.bridge
  left := c.left

/-- Exact validity of an oriented core bridge cut.  The selected slot goes
from `left` to its complement; every other slot stays entirely on one side. -/
def Valid (c : Data core) : Prop :=
  core.tail c.bridge ∈ c.left ∧
  core.head c.bridge ∉ c.left ∧
  ∀ edge : Fin p, edge ≠ c.bridge →
    (core.tail edge ∈ c.left ↔ core.head edge ∈ c.left)

/-- Transparent executable replay of bridge-cut data. -/
def check (c : Data core) : Bool :=
  decide (core.tail c.bridge ∈ c.left) &&
  decide (core.head c.bridge ∉ c.left) &&
  ExplicitPotential.allFin (fun edge : Fin p =>
    decide (edge = c.bridge ∨
      (core.tail edge ∈ c.left ↔ core.head edge ∈ c.left)))

@[simp] theorem check_eq_true_iff (c : Data core) :
    c.check = true ↔ c.Valid := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq,
    ExplicitPotential.allFin_eq_true_iff]
  constructor
  · rintro ⟨⟨hTail, hHead⟩, hOther⟩
    exact ⟨hTail, hHead, fun edge hNe => by
      rcases hOther edge with hEq | hSame
      · exact False.elim (hNe hEq)
      · exact hSame⟩
  · rintro ⟨hTail, hHead, hOther⟩
    exact ⟨⟨hTail, hHead⟩, fun edge => by
      by_cases hEq : edge = c.bridge
      · exact Or.inl hEq
      · exact Or.inr (hOther edge hEq)⟩

/-- Valid bridge data gives a valid articulation cut at the bridge tail. -/
theorem toCoreVertexCut_valid (c : Data core) (h : c.Valid) :
    c.toCoreVertexCut.Valid := by
  constructor
  · exact h.1
  · intro edge hCross
    unfold CoreVertexCut.Data.Crosses at hCross
    rcases hCross with hForward | hBackward
    · rcases hForward with ⟨hTail, hTailNe, hHead⟩
      by_cases hEq : edge = c.bridge
      · subst edge
        exact hTailNe rfl
      · exact hHead ((h.2.2 edge hEq).mp hTail)
    · rcases hBackward with ⟨hHead, _hHeadNe, hTail⟩
      by_cases hEq : edge = c.bridge
      · subst edge
        exact h.2.1 hHead
      · exact hTail ((h.2.2 edge hEq).mpr hHead)

variable (spec : SubdivisionGraph.Spec n p)

/-- The tail-side vertices after subdivision.  An interior vertex is on the
tail side exactly when both endpoints of its original core slot are there. -/
noncomputable def leftVertices (c : Data spec.core) : Finset spec.Vertex := by
  classical
  exact Finset.univ.filter fun vertex =>
    match vertex with
    | Sum.inl coreVertex => coreVertex ∈ c.left
    | Sum.inr interior =>
        spec.core.tail interior.1 ∈ c.left ∧
          spec.core.head interior.1 ∈ c.left

/-- The head-side vertices are the literal complement. -/
noncomputable def rightVertices (c : Data spec.core) : Finset spec.Vertex :=
  Finset.univ \ leftVertices spec c

variable (c : Data spec.core)

@[simp] theorem mem_leftVertices_core (vertex : Fin n) :
    spec.coreVertex vertex ∈ leftVertices spec c ↔ vertex ∈ c.left := by
  simp [leftVertices, SubdivisionGraph.Spec.coreVertex]

@[simp] theorem mem_leftVertices_interior
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.interiorVertex edge offset ∈ leftVertices spec c ↔
      spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left := by
  simp [leftVertices, SubdivisionGraph.Spec.interiorVertex]

@[simp] theorem mem_rightVertices_iff (vertex : spec.Vertex) :
    vertex ∈ rightVertices spec c ↔ vertex ∉ leftVertices spec c := by
  simp [rightVertices]

/-- Both the bridge lift and the articulation lift put exactly the same
vertices on the tail side. -/
theorem leftVertices_eq_coreVertexCut_leftVertices :
    leftVertices spec c =
      CoreVertexCut.Data.leftVertices spec c.toCoreVertexCut := by
  rfl

/-- A valid cut has a nonempty left factor. -/
theorem leftVertices_nonempty (h : c.Valid) : (leftVertices spec c).Nonempty :=
  ⟨spec.coreVertex (spec.core.tail c.bridge),
    (c.mem_leftVertices_core spec _).mpr h.1⟩

/-- The selected first-step neighbour belongs to the complementary factor. -/
theorem tailNeighbor_mem_rightVertices (h : c.Valid) :
    spec.tailNeighbor c.bridge ∈ rightVertices spec c := by
  rw [mem_rightVertices_iff]
  unfold SubdivisionGraph.Spec.tailNeighbor SubdivisionGraph.Spec.stepRight
  by_cases hLast : 0 + 1 = spec.length c.bridge
  · rw [dif_pos hLast]
    exact fun hMem => h.2.1 ((c.mem_leftVertices_core spec _).mp hMem)
  · rw [dif_neg hLast]
    exact fun hMem => h.2.1
      ((c.mem_leftVertices_interior spec _ _).mp hMem).2

/-- The tail endpoint of the selected bridge is on the left. -/
theorem tail_mem_leftVertices (h : c.Valid) :
    spec.coreVertex (spec.core.tail c.bridge) ∈ leftVertices spec c :=
  (c.mem_leftVertices_core spec _).mpr h.1

/-- A subdivision unit step directed from the left side to the right side is
necessarily the selected slot's first unit step. -/
theorem step_eq_bridge_zero_of_left_right (h : c.Valid)
    (edge : Fin p) (offset : Fin (spec.length edge))
    (hLeft : spec.stepLeft edge offset ∈ leftVertices spec c)
    (hRight : spec.stepRight edge offset ∈ rightVertices spec c) :
    edge = c.bridge ∧ offset.val = 0 := by
  rw [mem_rightVertices_iff] at hRight
  by_cases hZero : offset.val = 0
  · refine ⟨?_, hZero⟩
    by_contra hNe
    have hTail : spec.core.tail edge ∈ c.left := by
      rw [SubdivisionGraph.Spec.stepLeft, dif_pos hZero] at hLeft
      exact (c.mem_leftVertices_core spec _).mp hLeft
    have hHead : spec.core.head edge ∈ c.left :=
      (h.2.2 edge hNe).mp hTail
    apply hRight
    unfold SubdivisionGraph.Spec.stepRight
    by_cases hLast : offset.val + 1 = spec.length edge
    · rw [dif_pos hLast]
      exact (c.mem_leftVertices_core spec _).mpr hHead
    · rw [dif_neg hLast]
      exact (c.mem_leftVertices_interior spec _ _).mpr ⟨hTail, hHead⟩
  · have hInterior :
        spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left := by
      rw [SubdivisionGraph.Spec.stepLeft, dif_neg hZero] at hLeft
      exact (c.mem_leftVertices_interior spec _ _).mp hLeft
    exfalso
    apply hRight
    unfold SubdivisionGraph.Spec.stepRight
    by_cases hLast : offset.val + 1 = spec.length edge
    · rw [dif_pos hLast]
      exact (c.mem_leftVertices_core spec _).mpr hInterior.2
    · rw [dif_neg hLast]
      exact (c.mem_leftVertices_interior spec _ _).mpr hInterior

/-- No unit step can be directed from the complementary side back into the
left side. -/
theorem not_step_right_left (h : c.Valid)
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    ¬ (spec.stepLeft edge offset ∈ rightVertices spec c ∧
      spec.stepRight edge offset ∈ leftVertices spec c) := by
  rintro ⟨hLeft, hRight⟩
  rw [mem_rightVertices_iff] at hLeft
  by_cases hLast : offset.val + 1 = spec.length edge
  · have hHead : spec.core.head edge ∈ c.left := by
      rw [SubdivisionGraph.Spec.stepRight, dif_pos hLast] at hRight
      exact (c.mem_leftVertices_core spec _).mp hRight
    by_cases hZero : offset.val = 0
    · have hTail : spec.core.tail edge ∈ c.left := by
        by_cases hEq : edge = c.bridge
        · subst edge
          exact False.elim (h.2.1 hHead)
        · exact (h.2.2 edge hEq).mpr hHead
      apply hLeft
      rw [SubdivisionGraph.Spec.stepLeft, dif_pos hZero]
      exact (c.mem_leftVertices_core spec _).mpr hTail
    · have hBoth : spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left := by
        constructor
        by_cases hEq : edge = c.bridge
        · subst edge
          exact False.elim (h.2.1 hHead)
        · exact (h.2.2 edge hEq).mpr hHead
        exact hHead
      apply hLeft
      rw [SubdivisionGraph.Spec.stepLeft, dif_neg hZero]
      exact (c.mem_leftVertices_interior spec _ _).mpr hBoth
  · have hBoth : spec.core.tail edge ∈ c.left ∧ spec.core.head edge ∈ c.left := by
      rw [SubdivisionGraph.Spec.stepRight, dif_neg hLast] at hRight
      exact (c.mem_leftVertices_interior spec _ _).mp hRight
    apply hLeft
    by_cases hZero : offset.val = 0
    · rw [SubdivisionGraph.Spec.stepLeft, dif_pos hZero]
      exact (c.mem_leftVertices_core spec _).mpr hBoth.1
    · rw [SubdivisionGraph.Spec.stepLeft, dif_neg hZero]
      exact (c.mem_leftVertices_interior spec _ _).mpr hBoth

/-- Lift valid core bridge data to an occurrence-safe separating bridge cut
of every positive subdivision. -/
noncomputable def toOneBridgeCut (h : c.Valid) : OneBridgeCut spec.graph where
  left := leftVertices spec c
  right := rightVertices spec c
  leftAttach := spec.coreVertex (spec.core.tail c.bridge)
  rightAttach := spec.tailNeighbor c.bridge
  left_nonempty := c.leftVertices_nonempty spec h
  right_nonempty := ⟨spec.tailNeighbor c.bridge,
    c.tailNeighbor_mem_rightVertices spec h⟩
  leftAttach_mem := c.tail_mem_leftVertices spec h
  rightAttach_mem := c.tailNeighbor_mem_rightVertices spec h
  disjoint := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    exact ((c.mem_rightVertices_iff spec x).mp hxRight) hxLeft
  vertex_cover := by
    intro x
    by_cases hx : x ∈ leftVertices spec c
    · exact Or.inl hx
    · exact Or.inr ((c.mem_rightVertices_iff spec x).mpr hx)
  cross_num_edges := by
    intro a b ha hb
    rw [spec.num_edges_eq_card_filter_steps]
    by_cases hAttach : a = spec.coreVertex (spec.core.tail c.bridge) ∧
        b = spec.tailNeighbor c.bridge
    · rcases hAttach with ⟨rfl, rfl⟩
      rw [if_pos ⟨rfl, rfl⟩]
      rw [Finset.card_eq_one]
      refine ⟨⟨c.bridge, ⟨0, spec.length_pos c.bridge⟩⟩, ?_⟩
      ext step
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro (hForward | hBackward)
        · have hLeft := c.tail_mem_leftVertices spec h
          have hRight := c.tailNeighbor_mem_rightVertices spec h
          have hForward' :
              spec.stepLeft step.1 step.2 =
                spec.coreVertex (spec.core.tail c.bridge) ∧
              spec.stepRight step.1 step.2 = spec.tailNeighbor c.bridge := by
            simpa only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq] using hForward
          have hStep := c.step_eq_bridge_zero_of_left_right spec h step.1 step.2
            (by rw [hForward'.1]; exact hLeft)
            (by rw [hForward'.2]; exact hRight)
          rcases hStep with ⟨hEdge, hZero⟩
          rcases step with ⟨edge, offset⟩
          change edge = c.bridge at hEdge
          change offset.val = 0 at hZero
          subst edge
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            apply Fin.ext
            exact hZero
        · exact False.elim (c.not_step_right_left spec h step.1 step.2
            ⟨by
                have hBackward' : spec.stepLeft step.1 step.2 =
                    spec.tailNeighbor c.bridge := by
                  simpa only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq] using
                    congrArg Prod.fst hBackward
                rw [hBackward']
                exact c.tailNeighbor_mem_rightVertices spec h,
              by
                have hBackward' : spec.stepRight step.1 step.2 =
                    spec.coreVertex (spec.core.tail c.bridge) := by
                  simpa only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq] using
                    congrArg Prod.snd hBackward
                rw [hBackward']
                exact c.tail_mem_leftVertices spec h⟩)
      · intro hStep
        subst step
        left
        simp [SubdivisionGraph.Spec.unitEdge, SubdivisionGraph.Spec.tailNeighbor,
          SubdivisionGraph.Spec.stepLeft, SubdivisionGraph.Spec.stepRight]
    · have hEmpty : ((Finset.univ : Finset spec.Step).filter fun step =>
          spec.unitEdge step = (a, b) ∨ spec.unitEdge step = (b, a)) = ∅ := by
        ext step
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp
        constructor
        · intro hForward
          apply hAttach
          have hForward' : spec.stepLeft step.1 step.2 = a ∧
              spec.stepRight step.1 step.2 = b := by
            simpa only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq] using hForward
          have hStep' := c.step_eq_bridge_zero_of_left_right spec h step.1 step.2
            (by rw [hForward'.1]; exact ha)
            (by rw [hForward'.2]; exact hb)
          rcases hStep' with ⟨hEdge, hZero⟩
          rcases step with ⟨edge, offset⟩
          change edge = c.bridge at hEdge
          change offset.val = 0 at hZero
          subst edge
          have hOffset : offset = ⟨0, spec.length_pos c.bridge⟩ := by
            apply Fin.ext
            simpa using hZero
          subst offset
          exact ⟨by
              simpa [SubdivisionGraph.Spec.unitEdge, SubdivisionGraph.Spec.tailNeighbor,
                SubdivisionGraph.Spec.stepLeft, SubdivisionGraph.Spec.stepRight] using
                (congrArg Prod.fst hForward).symm,
            by
              simpa [SubdivisionGraph.Spec.unitEdge, SubdivisionGraph.Spec.tailNeighbor,
                SubdivisionGraph.Spec.stepLeft, SubdivisionGraph.Spec.stepRight] using
                (congrArg Prod.snd hForward).symm⟩
        · intro hBackward
          have hBackward' : spec.stepLeft step.1 step.2 = b ∧
              spec.stepRight step.1 step.2 = a := by
            simpa only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq] using hBackward
          exact c.not_step_right_left spec h step.1 step.2
            ⟨by rw [hBackward'.1]; exact hb,
              by rw [hBackward'.2]; exact ha⟩
      rw [hEmpty]
      simp [hAttach]

/-- Changing only the finite-set presentation (or its nonemptiness witness)
does not change the genus of an induced subgraph. -/
private theorem inducedSubgraph_genus_congr {G : CFGraph} (S T : Finset G.V)
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S = T) :
    genus (inducedSubgraph G S hS) = genus (inducedSubgraph G T hT) := by
  subst T
  rfl

/-- The left bridge factor has the genus computed from the finite tail-side
core data.  In particular this number is independent of all edge lengths. -/
theorem leftGraph_genus (h : c.Valid) :
    genus (c.toOneBridgeCut spec h).leftGraph = c.toCoreVertexCut.leftGenus := by
  have hCore := c.toCoreVertexCut.leftGraph_genus spec (c.toCoreVertexCut_valid h)
  let bridgeCut := c.toOneBridgeCut spec h
  let vertexCut := c.toCoreVertexCut.toOneVertexCut spec (c.toCoreVertexCut_valid h)
  have hSets : bridgeCut.left = vertexCut.left := by
    simp [bridgeCut, vertexCut, toOneBridgeCut,
      CoreVertexCut.Data.toOneVertexCut, leftVertices_eq_coreVertexCut_leftVertices]
  calc
    genus bridgeCut.leftGraph = genus vertexCut.leftGraph := by
      apply inducedSubgraph_genus_congr bridgeCut.left vertexCut.left
        bridgeCut.left_nonempty vertexCut.left_nonempty hSets
    _ = c.toCoreVertexCut.leftGenus := hCore

/-- The complementary bridge factor genus is forced by additive genus across
the separating unit edge. -/
theorem rightGraph_genus_eq (h : c.Valid) :
    genus (c.toOneBridgeCut spec h).rightGraph =
      genus spec.graph - c.toCoreVertexCut.leftGenus := by
  have hAdd := (c.toOneBridgeCut spec h).genus_eq
  rw [c.leftGraph_genus spec h] at hAdd
  omega

@[simp] theorem toOneBridgeCut_left (h : c.Valid) :
    (c.toOneBridgeCut spec h).left = leftVertices spec c := rfl

@[simp] theorem toOneBridgeCut_right (h : c.Valid) :
    (c.toOneBridgeCut spec h).right = rightVertices spec c := rfl

@[simp] theorem toOneBridgeCut_leftAttach (h : c.Valid) :
    (c.toOneBridgeCut spec h).leftAttach =
      spec.coreVertex (spec.core.tail c.bridge) := rfl

@[simp] theorem toOneBridgeCut_rightAttach (h : c.Valid) :
    (c.toOneBridgeCut spec h).rightAttach = spec.tailNeighbor c.bridge := rfl

end Data

end CoreBridgeCut

end MarkedGraphs.Certificate
