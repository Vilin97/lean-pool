/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.BridgeGraph
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.GraphIsoLaplacianEquiv
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.InducedSubgraph
public import Mathlib.Tactic

/-!
# Presentations by one separating bridge

`OneBridgeCut` is occurrence-safe finite data exhibiting an ambient graph as
two induced vertex-disjoint factors joined by one specified bridge occurrence.
The cross-edge equation is phrased with `numEdges`, so parallel edges inside
either factor remain fully visible while the separating edge has multiplicity
exactly one.
-/

@[expose] public section

namespace MarkedGraphs

open Utilities

open Finset

universe u

/-- A finite presentation of `K` as two induced pieces joined by a single
unit bridge. -/
structure OneBridgeCut (K : CFGraph.{u}) where
  /-- The nonempty left side of the vertex partition separated from the right side by exactly
  one bridge occurrence. -/
  left : Finset K.V
  /-- The nonempty right side of the disjoint vertex partition separated by the bridge. -/
  right : Finset K.V
  /-- The bridge endpoint belonging to the left side. -/
  leftAttach : K.V
  /-- The bridge endpoint belonging to the right side. -/
  rightAttach : K.V
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  leftAttach_mem : leftAttach ∈ left
  rightAttach_mem : rightAttach ∈ right
  disjoint : Disjoint left right
  vertex_cover : ∀ z : K.V, z ∈ left ∨ z ∈ right
  cross_num_edges : ∀ a b : K.V, a ∈ left → b ∈ right →
    numEdges K a b = if a = leftAttach ∧ b = rightAttach then 1 else 0

namespace OneBridgeCut

variable {K : CFGraph.{u}} (cut : OneBridgeCut K)

/-- The induced left factor. -/
noncomputable abbrev leftGraph : CFGraph :=
  inducedSubgraph K cut.left cut.left_nonempty

/-- The induced right factor. -/
noncomputable abbrev rightGraph : CFGraph :=
  inducedSubgraph K cut.right cut.right_nonempty

/-- The left endpoint, as a vertex of the left induced factor. -/
noncomputable def leftGlue : cut.leftGraph.V :=
  ⟨cut.leftAttach, cut.leftAttach_mem⟩

/-- The right endpoint, as a vertex of the right induced factor. -/
noncomputable def rightGlue : cut.rightGraph.V :=
  ⟨cut.rightAttach, cut.rightAttach_mem⟩

@[simp] theorem leftGlue_val : cut.leftGlue.val = cut.leftAttach := rfl

@[simp] theorem rightGlue_val : cut.rightGlue.val = cut.rightAttach := rfl

private theorem not_left_of_right {z : K.V} (hz : z ∈ cut.right) : z ∉ cut.left :=
  fun hzLeft => (Finset.disjoint_left.mp cut.disjoint) hzLeft hz

private theorem not_right_of_left {z : K.V} (hz : z ∈ cut.left) : z ∉ cut.right :=
  fun hzRight => (Finset.disjoint_left.mp cut.disjoint) hz hzRight

/-- The concrete bridge graph determined by the cut. -/
noncomputable abbrev bridgeGraph : CFGraph :=
  Utilities.bridgeGraph cut.leftGraph cut.rightGraph cut.leftGlue cut.rightGlue
/-- The vertex equivalence from the concrete bridge model to the ambient
graph. -/
noncomputable def vertexEquiv : cut.bridgeGraph.V ≃ K.V where
  toFun
    | Sum.inl a => a.val
    | Sum.inr b => b.val
  invFun z :=
    if hzLeft : z ∈ cut.left then
      Sum.inl ⟨z, hzLeft⟩
    else
      Sum.inr ⟨z, by
        rcases cut.vertex_cover z with hz | hz
        · exact (hzLeft hz).elim
        · exact hz⟩
  left_inv := by
    rintro (a | b)
    · simp [a.property]
    · simp [cut.not_left_of_right b.property]
  right_inv := by
    intro z
    by_cases hzLeft : z ∈ cut.left
    · simp [hzLeft]
    · have hzRight : z ∈ cut.right := by
        rcases cut.vertex_cover z with hz | hz
        · exact (hzLeft hz).elim
        · exact hz
      simp [hzLeft]

@[simp] theorem vertexEquiv_apply_left (a : cut.leftGraph.V) :
    cut.vertexEquiv (Sum.inl a) = a.val := rfl

@[simp] theorem vertexEquiv_apply_right (b : cut.rightGraph.V) :
    cut.vertexEquiv (Sum.inr b) = b.val := rfl
private theorem num_edges_cross (a : cut.leftGraph.V) (b : cut.rightGraph.V) :
    numEdges K a.val b.val =
      if a = cut.leftGlue ∧ b = cut.rightGlue then 1 else 0 := by
  have hRaw := cut.cross_num_edges a.val b.val a.property b.property
  by_cases ha : a = cut.leftGlue
  · by_cases hb : b = cut.rightGlue
    · subst a
      subst b
      simpa [leftGlue, rightGlue] using hRaw
    · have hbVal : b.val ≠ cut.rightAttach := by
        intro hValue
        apply hb
        apply Subtype.ext
        simpa [rightGlue] using hValue
      simp [ha, hb, leftGlue, hbVal] at hRaw ⊢
      exact hRaw
  · have hRawFalse : ¬ (a.val = cut.leftAttach ∧ b.val = cut.rightAttach) := by
      rintro ⟨haVal, _⟩
      apply ha
      apply Subtype.ext
      simpa [leftGlue] using haVal
    simp [ha, hRawFalse] at hRaw ⊢
    exact hRaw
/-- The occurrence-safe isomorphism from the bridge model to the ambient
graph. -/
noncomputable def graphIso : CFGraphIso cut.bridgeGraph K where
  vertexEquiv := cut.vertexEquiv
  map_num_edges := by
    rintro (a | b) (a' | b')
    all_goals dsimp [vertexEquiv]
    · unfold bridgeGraph
      rw [num_edges_bridgeGraph_inl]
      simp [leftGraph]
    · unfold bridgeGraph
      exact (cut.num_edges_cross a b').trans
        (num_edges_bridgeGraph_inl_inr cut.leftGraph cut.rightGraph
          cut.leftGlue cut.rightGlue a b').symm
    · unfold bridgeGraph
      calc
        numEdges K b.val a'.val = numEdges K a'.val b.val :=
          num_edges_symmetric K _ _
        _ = if a' = cut.leftGlue ∧ b = cut.rightGlue then 1 else 0 :=
          cut.num_edges_cross a' b
        _ = numEdges (Utilities.bridgeGraph cut.leftGraph cut.rightGraph
            cut.leftGlue cut.rightGlue) (Sum.inr b) (Sum.inl a') := by
          rw [num_edges_symmetric]
          exact (num_edges_bridgeGraph_inl_inr cut.leftGraph cut.rightGraph
            cut.leftGlue cut.rightGlue a' b).symm
    · unfold bridgeGraph
      rw [num_edges_bridgeGraph_inr]
      simp [rightGraph]

/-- The Laplacian equivalence supplied by a bridge cut. -/
noncomputable def laplacianEquiv : Certificate.LaplacianEquiv cut.bridgeGraph K :=
  cut.graphIso.toLaplacianEquiv

/-- Genus is additive across a separating bridge. -/
theorem genus_eq : genus K = genus cut.leftGraph + genus cut.rightGraph := by
  rw [cut.graphIso.genus_eq]
  exact genus_bridgeGraph _ _ _ _

/-- A connected ambient graph has connected induced left factor across a
single separating bridge. -/
theorem graph_connected_left_of_connected (hK : graphConnected K) :
    graphConnected cut.leftGraph := by
  classical
  intro A hSplit
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  by_cases hAttach : cut.leftGlue ∈ A
  · let S : Finset K.V := A.image Subtype.val ∪ cut.right
    have hSplitS : ∃ x y : K.V, x ∈ S ∧ y ∉ S := by
      refine ⟨inside.val, outside.val, ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨inside, hInside, rfl⟩)
      · intro hOutsideS
        rw [Finset.mem_union] at hOutsideS
        rcases hOutsideS with hOutsideA | hOutsideRight
        · obtain ⟨vertex, hVertex, hValue⟩ := Finset.mem_image.mp hOutsideA
          exact hOutside (Subtype.ext hValue.symm ▸ hVertex)
        · exact (cut.not_left_of_right hOutsideRight outside.property).elim
    obtain ⟨x, hx, y, hy, hxy⟩ := hK S hSplitS
    have hyNotRight : y ∉ cut.right := by
      intro hyRight
      exact hy (Finset.mem_union_right _ hyRight)
    have hyLeft : y ∈ cut.left := by
      rcases cut.vertex_cover y with hyLeft | hyRight
      · exact hyLeft
      · exact (hyNotRight hyRight).elim
    have hyNeAttach : y ≠ cut.leftAttach := by
      intro hEqual
      apply hy
      apply Finset.mem_union_left _
      exact Finset.mem_image.mpr ⟨cut.leftGlue, hAttach, by simp [hEqual]⟩
    have hxLeft : x ∈ cut.left := by
      rcases cut.vertex_cover x with hxLeft | hxRight
      · exact hxLeft
      · by_contra hxNotLeft
        have hZero := cut.cross_num_edges y x hyLeft hxRight
        simp [hyNeAttach] at hZero
        rw [num_edges_symmetric] at hZero
        omega
    let xLeft : cut.leftGraph.V := ⟨x, hxLeft⟩
    have hxA : xLeft ∈ A := by
      rw [Finset.mem_union] at hx
      rcases hx with hxA | hxRight
      · obtain ⟨vertex, hVertex, hValue⟩ := Finset.mem_image.mp hxA
        have hEqual : xLeft = vertex :=
          Subtype.ext hValue.symm
        rw [hEqual]
        exact hVertex
      · exact False.elim (cut.not_right_of_left hxLeft hxRight)
    let yLeft : cut.leftGraph.V := ⟨y, hyLeft⟩
    have hyA : yLeft ∉ A := by
      intro hyA
      apply hy
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨yLeft, hyA, rfl⟩)
    refine ⟨xLeft, ?_, yLeft, hyA, ?_⟩
    · exact hxA
    · simpa [leftGraph, xLeft, yLeft] using hxy
  · let S : Finset K.V := A.image Subtype.val
    have hSplitS : ∃ x y : K.V, x ∈ S ∧ y ∉ S := by
      refine ⟨inside.val, outside.val, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨inside, hInside, rfl⟩
      · intro hOutsideS
        obtain ⟨vertex, hVertex, hValue⟩ := Finset.mem_image.mp hOutsideS
        exact hOutside (Subtype.ext hValue.symm ▸ hVertex)
    obtain ⟨x, hx, y, hy, hxy⟩ := hK S hSplitS
    obtain ⟨xLeft, hxA, hxValue⟩ := Finset.mem_image.mp hx
    have hxNeAttach : x ≠ cut.leftAttach := by
      intro hEqual
      apply hAttach
      have hEqual' : xLeft = cut.leftGlue := Subtype.ext (hxValue.trans hEqual)
      rw [← hEqual']
      exact hxA
    have hxLeftMem : x ∈ cut.left := by
      rw [← hxValue]
      exact xLeft.property
    have hyLeft : y ∈ cut.left := by
      rcases cut.vertex_cover y with hyLeft | hyRight
      · exact hyLeft
      · have hZero := cut.cross_num_edges x y hxLeftMem hyRight
        simp [hxNeAttach] at hZero
        exact False.elim (by rw [hZero] at hxy; omega)
    let yLeft : cut.leftGraph.V := ⟨y, hyLeft⟩
    have hyA : yLeft ∉ A := by
      intro hyA
      apply hy
      exact Finset.mem_image.mpr ⟨yLeft, hyA, rfl⟩
    refine ⟨xLeft, hxA, yLeft, hyA, ?_⟩
    simpa [leftGraph, hxValue, yLeft] using hxy

/-- Exchange the two sides of a bridge cut. -/
def swap : OneBridgeCut K where
  left := cut.right
  right := cut.left
  leftAttach := cut.rightAttach
  rightAttach := cut.leftAttach
  left_nonempty := cut.right_nonempty
  right_nonempty := cut.left_nonempty
  leftAttach_mem := cut.rightAttach_mem
  rightAttach_mem := cut.leftAttach_mem
  disjoint := cut.disjoint.symm
  vertex_cover := by
    intro z
    rcases cut.vertex_cover z with hz | hz
    · exact Or.inr hz
    · exact Or.inl hz
  cross_num_edges := by
    intro a b ha hb
    rw [num_edges_symmetric]
    have h := cut.cross_num_edges b a hb ha
    by_cases hPair : a = cut.rightAttach ∧ b = cut.leftAttach
    · rcases hPair with ⟨rfl, rfl⟩
      simpa using h
    · simp only [hPair, if_false]
      have hReverse : ¬ (b = cut.leftAttach ∧ a = cut.rightAttach) := by
        rintro ⟨hLeft, hRight⟩
        exact hPair ⟨hRight, hLeft⟩
      simp [hReverse] at h
      exact h

@[simp] theorem swap_leftGraph : cut.swap.leftGraph = cut.rightGraph := rfl

@[simp] theorem swap_rightGraph : cut.swap.rightGraph = cut.leftGraph := rfl

@[simp] theorem swap_leftGlue : cut.swap.leftGlue = cut.rightGlue := rfl

@[simp] theorem swap_rightGlue : cut.swap.rightGlue = cut.leftGlue := rfl

/-- A connected ambient graph has connected induced right factor across a
single separating bridge. -/
theorem graph_connected_right_of_connected (hK : graphConnected K) :
    graphConnected cut.rightGraph := by
  simpa using cut.swap.graph_connected_left_of_connected hK

theorem graph_connected_factors_of_connected (hK : graphConnected K) :
    graphConnected cut.leftGraph ∧ graphConnected cut.rightGraph :=
  ⟨cut.graph_connected_left_of_connected hK,
    cut.graph_connected_right_of_connected hK⟩

/-- Connected factors reconstruct a connected ambient graph. -/
theorem graph_connected_of_factors
    (hLeft : graphConnected cut.leftGraph)
    (hRight : graphConnected cut.rightGraph) : graphConnected K :=
  cut.graphIso.graph_connected_map
    (graph_connected_bridgeGraph cut.leftGraph cut.rightGraph
      cut.leftGlue cut.rightGlue hLeft hRight)

theorem graph_connected_iff_factors :
    graphConnected K ↔
      graphConnected cut.leftGraph ∧ graphConnected cut.rightGraph :=
  ⟨cut.graph_connected_factors_of_connected,
    fun h => cut.graph_connected_of_factors h.1 h.2⟩

end OneBridgeCut

end MarkedGraphs
