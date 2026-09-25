/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Segments.SegmentReflection
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance

/-!
# The endpoint pencil on a two-vertex subdivision core (light half)

Every slot of a loopless two-vertex core joins the same two core vertices.
The divisor consisting of one chip at each endpoint has rank at least one for
arbitrary positive integral slot lengths: a chip removed in the interior of a
slot is recovered by the exact segment-reflection potential on that slot.

This packages the uniform hyperelliptic argument for banana graphs.  It
depends only on the segment-reflection and rank-one layers.
-/

@[expose] public section

namespace Utilities.Certificate

open SubdivisionGraph

namespace SubdivisionGraph.Spec

variable {p : ℕ}

/-- The two endpoint chips on a subdivision whose loopless core has exactly
two vertices form a degree-two rank-one divisor.  Keeping the vertex-count
equality explicit makes this usable for dependent canonical contracted cores. -/
theorem bnExists_one_two_of_coreVertexCount_eq_two
    {n : ℕ} (spec : Spec n p) (hCount : n = 2) :
    BNExists spec.graph 1 2 := by
  classical
  let leftIndex : Fin n := ⟨0, by omega⟩
  let rightIndex : Fin n := ⟨1, by omega⟩
  let left : spec.graph.V := spec.coreVertex leftIndex
  let right : spec.graph.V := spec.coreVertex rightIndex
  let D : CFDiv spec.graph := oneChip left + oneChip right
  have hEffective : effective D :=
    (Eff spec.graph).add_mem (eff_one_chip left) (eff_one_chip right)
  have hDegree : deg D = 2 := by
    dsimp [D]
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hCoreValue (vertex : Fin n) : 1 ≤ D (spec.coreVertex vertex) := by
    have hCases : vertex.val = 0 ∨ vertex.val = 1 := by omega
    rcases hCases with hLeft | hRight
    · have hEq : vertex = leftIndex := Fin.ext hLeft
      subst vertex
      simp [D, left, right, leftIndex, rightIndex, oneChip, Spec.coreVertex]
    · have hEq : vertex = rightIndex := Fin.ext hRight
      subst vertex
      simp [D, left, right, leftIndex, rightIndex, oneChip, Spec.coreVertex]
  have hRank : rank spec.graph D ≥ 1 := by
    rw [rank_ge_one_iff_winnable_sub_one_chip]
    intro vertex
    rcases vertex with vertex | interior
    · apply winnable_of_effective
      intro q
      by_cases hq : q = spec.coreVertex vertex
      · subst q
        simpa [oneChip, Spec.coreVertex] using
          (sub_nonneg.mpr (hCoreValue vertex))
      · change q ≠ Sum.inl vertex at hq
        simpa [oneChip, hq] using hEffective q
    · rcases interior with ⟨edge, offset⟩
      let position : spec.PathPosition edge :=
        ⟨offset.val + 1, by have := offset.isLt; omega⟩
      have hPosition :
          spec.pathVertex edge position = spec.interiorVertex edge offset := by
        unfold Spec.pathVertex
        rw [dite_eq_right (by simp [position]), dite_eq_right (by
          have := offset.isLt
          simp only [position]
          omega)]
        congr 3
      change winnable spec.graph
        (D - oneChip (spec.interiorVertex edge offset))
      rw [← hPosition]
      exact SegmentReflection.reaches_pathPosition spec D edge position
        hEffective (hCoreValue (spec.core.tail edge))
        (hCoreValue (spec.core.head edge))
  exact ⟨D, hDegree, hRank⟩

/-- Convenient literally-two-vertex specialization. -/
theorem bnExists_one_two_of_two_core_vertices (spec : Spec 2 p) :
    BNExists spec.graph 1 2 :=
  spec.bnExists_one_two_of_coreVertexCount_eq_two rfl

/-- The endpoint pencil may be padded to any larger exact degree.  This is
useful when a two-vertex banana occurs as a low-genus structural case inside
a theorem whose critical degree is fixed by the ambient genus. -/
theorem bnExists_one_of_two_core_vertices_of_two_le
    (spec : Spec 2 p) {degree : ℤ} (hDegree : 2 ≤ degree) :
    BNExists spec.graph 1 degree :=
  BNExists_mono_degree hDegree spec.bnExists_one_two_of_two_core_vertices

/-- In particular every positive subdivision of a loopless two-vertex core
has the degree-four rank-one pencil required in genus five. -/
theorem bnExists_one_four_of_two_core_vertices (spec : Spec 2 p) :
    BNExists spec.graph 1 4 :=
  spec.bnExists_one_of_two_core_vertices_of_two_le (by norm_num)

end SubdivisionGraph.Spec

end Utilities.Certificate
