/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutWedge

/-!
# Connectivity of the factors of a one-vertex cut

The two induced graphs associated with a one-vertex cut inherit connectivity
from the ambient graph.
-/

namespace Utilities

open Finset

universe u

namespace OneVertexCut

variable {K : CFGraph.{u}} (cut : OneVertexCut K)

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`, so unifying
-- instance-implicit arguments through the semireducible `bridgeGraph`/`vertexWedge`
-- constructions no longer unfolds them; use the previous transparency locally.
theorem graph_connected_left_of_connected
    (hK : graphConnected K) :
    graphConnected cut.leftGraph := by
  classical
  intro A hSplit
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  by_cases hGlue : cut.leftGlue ∈ A
  · let S : Finset K.V := A.image Subtype.val ∪ cut.right
    have hSplitS : ∃ x y : K.V, x ∈ S ∧ y ∉ S := by
      refine ⟨inside.val, outside.val, ?_, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨inside, hInside, rfl⟩)
      · intro hOutsideS
        rw [Finset.mem_union] at hOutsideS
        rcases hOutsideS with hOutsideA | hOutsideRight
        · obtain ⟨a, ha, hValue⟩ := Finset.mem_image.mp hOutsideA
          exact hOutside (Subtype.ext hValue.symm ▸ ha)
        · have hGlueEq := cut.only_overlap outside.val outside.property hOutsideRight
          have hEqual : outside = cut.leftGlue := Subtype.ext hGlueEq
          exact hOutside (by simpa [hEqual] using hGlue)
    obtain ⟨x, hx, y, hy, hxy⟩ := hK S hSplitS
    have hyNotRight : y ∉ cut.right := by
      intro hyRight
      exact hy (Finset.mem_union_right _ hyRight)
    have hyLeft : y ∈ cut.left := by
      rcases cut.vertex_cover y with hyLeft | hyRight
      · exact hyLeft
      · exact (hyNotRight hyRight).elim
    have hxLeft : x ∈ cut.left := by
      rw [Finset.mem_union] at hx
      rcases hx with hxA | hxRight
      · obtain ⟨a, ha, hValue⟩ := Finset.mem_image.mp hxA
        rw [← hValue]
        exact a.property
      · by_contra hxLeft
        have hxNeGlue : x ≠ cut.glue := by
          intro hEq
          apply hxLeft
          rw [hEq]
          exact cut.glue_mem_left
        have hyNeGlue : y ≠ cut.glue := by
          intro hEq
          apply hyNotRight
          rw [hEq]
          exact cut.glue_mem_right
        have hZero := cut.no_cross y hyLeft hyNeGlue x hxRight hxNeGlue
        rw [num_edges_symmetric] at hZero
        omega
    let xLeft : cut.leftGraph.V := ⟨x, hxLeft⟩
    let yLeft : cut.leftGraph.V := ⟨y, hyLeft⟩
    have hxA : xLeft ∈ A := by
      rw [Finset.mem_union] at hx
      rcases hx with hxA | hxRight
      · obtain ⟨a, ha, hValue⟩ := Finset.mem_image.mp hxA
        change (⟨x, hxLeft⟩ : cut.leftGraph.V) ∈ A
        have hEqual : (⟨x, hxLeft⟩ : cut.leftGraph.V) = a :=
          Subtype.ext hValue.symm
        rw [hEqual]
        exact ha
      · have hGlueEq := cut.only_overlap x hxLeft hxRight
        have hEqual : xLeft = cut.leftGlue := by
          apply Subtype.ext
          exact hGlueEq
        rw [hEqual]
        exact hGlue
    have hyA : yLeft ∉ A := by
      intro hyA
      apply hy
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨yLeft, hyA, rfl⟩)
    refine ⟨xLeft, hxA, yLeft, hyA, ?_⟩
    have heq := num_edges_inducedSubgraph K cut.left cut.left_nonempty xLeft yLeft
    exact heq.symm ▸ hxy
  · let S : Finset K.V := A.image Subtype.val
    have hSplitS : ∃ x y : K.V, x ∈ S ∧ y ∉ S := by
      refine ⟨inside.val, outside.val, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨inside, hInside, rfl⟩
      · intro hOutsideS
        obtain ⟨a, ha, hValue⟩ := Finset.mem_image.mp hOutsideS
        exact hOutside (Subtype.ext hValue.symm ▸ ha)
    obtain ⟨x, hx, y, hy, hxy⟩ := hK S hSplitS
    obtain ⟨xLeft, hxA, hxValue⟩ := Finset.mem_image.mp hx
    have hxNeGlue : x ≠ cut.glue := by
      intro hEq
      apply hGlue
      have hEqual : xLeft = cut.leftGlue := Subtype.ext (hxValue.trans hEq)
      rw [← hEqual]
      exact hxA
    have hxLeftMem : x ∈ cut.left := by
      rw [← hxValue]
      exact xLeft.property
    have hyLeft : y ∈ cut.left := by
      rcases cut.vertex_cover y with hyLeft | hyRight
      · exact hyLeft
      · by_cases hyGlue : y = cut.glue
        · rw [hyGlue]
          exact cut.glue_mem_left
        · have hZero := cut.no_cross x hxLeftMem hxNeGlue y hyRight hyGlue
          exact False.elim (by rw [hZero] at hxy; omega)
    let yLeft : cut.leftGraph.V := ⟨y, hyLeft⟩
    have hyA : yLeft ∉ A := by
      intro hyA
      apply hy
      exact Finset.mem_image.mpr ⟨yLeft, hyA, rfl⟩
    refine ⟨xLeft, hxA, yLeft, hyA, ?_⟩
    have heq := num_edges_inducedSubgraph K cut.left cut.left_nonempty xLeft yLeft
    have hpositive : 0 < numEdges K xLeft.val yLeft.val := by
      simpa only [yLeft, hxValue] using! hxy
    exact heq.symm ▸ hpositive

/-- The same cut with its two factors exchanged. -/
def swap : OneVertexCut K where
  left := cut.right
  right := cut.left
  glue := cut.glue
  glue_mem_left := cut.glue_mem_right
  glue_mem_right := cut.glue_mem_left
  vertex_cover := by
    intro z
    rcases cut.vertex_cover z with hz | hz
    · exact Or.inr hz
    · exact Or.inl hz
  only_overlap := by
    intro z hzLeft hzRight
    exact cut.only_overlap z hzRight hzLeft
  no_cross := by
    intro a ha haGlue b hb hbGlue
    rw [num_edges_symmetric]
    exact cut.no_cross b hb hbGlue a ha haGlue

@[simp] theorem swap_leftGraph : cut.swap.leftGraph = cut.rightGraph := by
  rfl

@[simp] theorem swap_rightGraph : cut.swap.rightGraph = cut.leftGraph := by
  rfl

@[simp] theorem swap_leftGlue : cut.swap.leftGlue = cut.rightGlue := by
  rfl

@[simp] theorem swap_rightGlue : cut.swap.rightGlue = cut.leftGlue := by
  rfl

theorem graph_connected_right_of_connected
    (hK : graphConnected K) :
    graphConnected cut.rightGraph := by
  simpa using cut.swap.graph_connected_left_of_connected hK

theorem graph_connected_factors
    (hK : graphConnected K) :
    graphConnected cut.leftGraph ∧ graphConnected cut.rightGraph :=
  ⟨cut.graph_connected_left_of_connected hK,
    cut.graph_connected_right_of_connected hK⟩

theorem graph_connected_iff_factors :
    graphConnected K ↔
      graphConnected cut.leftGraph ∧ graphConnected cut.rightGraph :=
  ⟨cut.graph_connected_factors,
    fun h => cut.graph_connected_of_factors h.1 h.2⟩

end OneVertexCut

end Utilities
