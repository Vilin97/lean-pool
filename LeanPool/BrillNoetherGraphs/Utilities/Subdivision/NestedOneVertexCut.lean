/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutConnectivity
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCut

/-!
# Restricting a one-vertex cut through another cut

When the left side of a second cut lies in the right factor of a first cut,
the second cut restricts to that factor.  This is the elementary nesting step
needed to display successive wedge factors without making any assumptions on
their origin.
-/

namespace Utilities

open Finset
open Certificate ExplicitPotential SubdivisionGraph

universe u

namespace Certificate.CoreVertexCut.Data

variable {n p : ℕ} (spec : Spec n p)
variable (first second : CoreVertexCut.Data spec.core)

/-- Core-side nesting lifts uniformly through every positive subdivision.
If the second finite left side lies in the first finite right side, every
subdivision vertex belonging to the second left factor lies in the first
right factor. -/
theorem leftVertices_subset_rightVertices_of_left_subset_right
    (hSubset : second.left ⊆ first.right) :
    second.leftVertices spec ⊆ first.rightVertices spec := by
  intro vertex hVertex
  rw [first.mem_rightVertices_iff spec]
  rcases vertex with coreVertex | interior
  · have hSecond : coreVertex ∈ second.left :=
      (second.mem_leftVertices_core spec coreVertex).mp hVertex
    have hCoreRight : coreVertex = first.glue ∨ coreVertex ∉ first.left := by
      simpa [CoreVertexCut.Data.right] using hSubset hSecond
    rcases hCoreRight with hGlue | hNotLeft
    · exact Or.inl (by simpa [SubdivisionGraph.Spec.coreVertex] using hGlue)
    · exact Or.inr (fun hFirst =>
        hNotLeft ((first.mem_leftVertices_core spec coreVertex).mp hFirst))
  · obtain ⟨edge, offset⟩ := interior
    apply Or.inr
    intro hFirst
    have hSecondEnds := (second.mem_leftVertices_interior spec edge offset).mp hVertex
    have hFirstEnds := (first.mem_leftVertices_interior spec edge offset).mp hFirst
    have hTailRight : spec.core.tail edge = first.glue ∨
        spec.core.tail edge ∉ first.left := by
      simpa [CoreVertexCut.Data.right] using hSubset hSecondEnds.1
    have hHeadRight : spec.core.head edge = first.glue ∨
        spec.core.head edge ∉ first.left := by
      simpa [CoreVertexCut.Data.right] using hSubset hSecondEnds.2
    have hTailGlue : spec.core.tail edge = first.glue := by
      rcases hTailRight with h | h
      · exact h
      · exact False.elim (h hFirstEnds.1)
    have hHeadGlue : spec.core.head edge = first.glue := by
      rcases hHeadRight with h | h
      · exact h
      · exact False.elim (h hFirstEnds.2)
    exact spec.core_loopless edge (hTailGlue.trans hHeadGlue.symm)

end Certificate.CoreVertexCut.Data

namespace OneVertexCut

variable {K : CFGraph.{u}} (first second : OneVertexCut K)

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`, so unifying
-- instance-implicit arguments through the semireducible cut/induced-subgraph
-- constructions no longer unfolds them; use the previous transparency locally.
/-- The second cut may be viewed inside the right factor of the first when
its left side is contained in that factor. -/
noncomputable def restrictRight
    (hLeft : second.left ⊆ first.right) : OneVertexCut first.rightGraph where
  left := Finset.univ.filter fun z => z.val ∈ second.left
  right := Finset.univ.filter fun z => z.val ∈ second.right
  glue := ⟨second.glue, hLeft second.glue_mem_left⟩
  glue_mem_left := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, second.glue_mem_left⟩
  glue_mem_right := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, second.glue_mem_right⟩
  vertex_cover := by
    intro z
    rcases second.vertex_cover z.val with hz | hz
    · exact Or.inl (by simp [hz])
    · exact Or.inr (by simp [hz])
  only_overlap := by
    intro z hzLeft hzRight
    have hLeftMem : z.val ∈ second.left := by simpa using hzLeft
    have hRightMem : z.val ∈ second.right := by simpa using hzRight
    apply Subtype.ext
    exact second.only_overlap z.val hLeftMem hRightMem
  no_cross := by
    intro a ha haGlue b hb hbGlue
    have haLeft : a.val ∈ second.left := by simpa using ha
    have hbRight : b.val ∈ second.right := by simpa using hb
    have haNe : a.val ≠ second.glue := by
      intro h
      apply haGlue
      exact Subtype.ext h
    have hbNe : b.val ≠ second.glue := by
      intro h
      apply hbGlue
      exact Subtype.ext h
    exact (num_edges_inducedSubgraph K first.right first.right_nonempty a b).trans
      (second.no_cross a.val haLeft haNe b.val hbRight hbNe)

/-- Connectivity of the restricted-cut factors follows from connectivity of
the original ambient graph. -/
theorem restrictRight_graph_connected_factors
    (hLeft : second.left ⊆ first.right) (hK : graphConnected K) :
    graphConnected (first.restrictRight second hLeft).leftGraph ∧
      graphConnected (first.restrictRight second hLeft).rightGraph := by
  exact (first.restrictRight second hLeft).graph_connected_factors
    (first.graph_connected_right_of_connected hK)

/-- Flatten the two subtype layers of the restricted left factor. -/
def restrictRightLeftVertex (hLeft : second.left ⊆ first.right)
    (vertex : (first.restrictRight second hLeft).leftGraph.V) :
    second.leftGraph.V :=
  ⟨vertex.val.val, by
    have h : vertex.val ∈
        Finset.univ.filter (fun z : first.rightGraph.V => z.val ∈ second.left) :=
      vertex.property
    exact (Finset.mem_filter.mp h).2⟩

@[simp] theorem restrictRightLeftVertex_val (hLeft : second.left ⊆ first.right)
    (vertex : (first.restrictRight second hLeft).leftGraph.V) :
    (first.restrictRightLeftVertex second hLeft vertex).val = vertex.val.val := rfl

theorem restrictRightLeftVertex_bijective
    (hLeft : second.left ⊆ first.right) :
    Function.Bijective (first.restrictRightLeftVertex second hLeft) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : second.leftGraph.V => z.val) h
  · intro y
    let rightVertex : first.rightGraph.V := ⟨y.val, hLeft y.property⟩
    have hRestricted : rightVertex ∈ (first.restrictRight second hLeft).left := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.property⟩
    let x : (first.restrictRight second hLeft).leftGraph.V :=
      ⟨rightVertex, hRestricted⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rfl

/-- Flatten the left factor of a restricted cut back to the second cut's
original left factor.  This removes the two layers of induced-subgraph
subtypes without changing any edge multiplicity. -/
noncomputable def restrictRightLeftIso
    (hLeft : second.left ⊆ first.right) :
    CFGraphIso (first.restrictRight second hLeft).leftGraph second.leftGraph where
  vertexEquiv := Equiv.ofBijective
    (first.restrictRightLeftVertex second hLeft)
    (first.restrictRightLeftVertex_bijective second hLeft)
  map_num_edges := by
    intro x y
    calc
      numEdges second.leftGraph _ _ =
          numEdges K
            (first.restrictRightLeftVertex second hLeft x).val
            (first.restrictRightLeftVertex second hLeft y).val :=
        num_edges_inducedSubgraph K second.left second.left_nonempty _ _
      _ = numEdges K x.val.val y.val.val := by rfl
      _ = numEdges first.rightGraph x.val y.val := by
            symm
            exact num_edges_inducedSubgraph K first.right first.right_nonempty
              x.val y.val
      _ = numEdges (first.restrictRight second hLeft).leftGraph x y := by
            symm
            exact num_edges_inducedSubgraph first.rightGraph
              (first.restrictRight second hLeft).left
              (first.restrictRight second hLeft).left_nonempty x y

@[simp] theorem restrictRightLeftIso_apply_leftGlue
    (hLeft : second.left ⊆ first.right) :
    (first.restrictRightLeftIso second hLeft).vertexEquiv
      (first.restrictRight second hLeft).leftGlue = second.leftGlue := by
  apply Subtype.ext
  rfl

/-- The two successive cuts decompose the genus into the first left factor
and the two factors of the restricted second cut. -/
theorem genus_eq_nested_restrictRight
    (hLeft : second.left ⊆ first.right) :
    genus K = genus first.leftGraph +
      genus (first.restrictRight second hLeft).leftGraph +
        genus (first.restrictRight second hLeft).rightGraph := by
  have hFirst := first.genus_eq
  have hSecond := (first.restrictRight second hLeft).genus_eq
  omega

end OneVertexCut

end Utilities
