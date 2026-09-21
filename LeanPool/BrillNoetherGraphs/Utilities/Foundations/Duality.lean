/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Riemann--Roch duality for Brill--Noether existence

Graph Riemann--Roch identifies the rank condition for a divisor `D` with the
dual rank condition for `K_G - D`.  This module records both the pointwise
rank equivalence and the induced symmetry of `BNExists`.
-/

namespace Utilities

/-- Riemann--Roch converts a rank lower bound into the complementary one. -/
theorem rank_ge_iff_dual_rank_ge
    {G : CFGraph} (hG : graph_connected G) (D : CFDiv G) (r : ℤ) :
    rank G D ≥ r ↔
      rank G (canonical_divisor G - D) ≥ dualRank G r (deg D) := by
  unfold dualRank rectangleWidth
  constructor <;> intro hRank
  · linarith [riemann_roch_for_graphs hG D]
  · linarith [riemann_roch_for_graphs hG D]

/-- Duality transposes the Brill--Noether rectangle. -/
theorem rectangleWidth_dual (G : CFGraph) (r d : ℤ) :
    rectangleWidth G (dualRank G r d) (dualDegree G d) = r + 1 := by
  simp only [rectangleWidth, dualRank, dualDegree]
  ring

/-- The dual parameter operation preserves the Brill--Noether number. -/
theorem bnNumber_dual (G : CFGraph) (r d : ℤ) :
    bnNumber G (dualRank G r d) (dualDegree G d) = bnNumber G r d := by
  unfold bnNumber
  rw [rectangleWidth_dual]
  unfold dualRank
  ring

/-- Taking the dual degree twice recovers the original degree. -/
@[simp] theorem dualDegree_dualDegree (G : CFGraph) (d : ℤ) :
    dualDegree G (dualDegree G d) = d := by
  unfold dualDegree
  ring

/-- Taking dual parameters twice recovers the original rank. -/
@[simp] theorem dualRank_dual (G : CFGraph) (r d : ℤ) :
    dualRank G (dualRank G r d) (dualDegree G d) = r := by
  change rectangleWidth G (dualRank G r d) (dualDegree G d) - 1 = r
  rw [rectangleWidth_dual]
  ring

/-- Brill--Noether existence is invariant under Riemann--Roch duality. -/
theorem BNExists_dual_iff
    {G : CFGraph} (hG : graph_connected G) (r d : ℤ) :
    BNExists G r d ↔ BNExists G (dualRank G r d) (dualDegree G d) := by
  constructor
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨canonical_divisor G - D, ?_, ?_⟩
    · rw [deg.map_sub, degree_of_canonical_divisor, hDegree]
      rfl
    · have hDual := (rank_ge_iff_dual_rank_ge hG D r).mp hRank
      simpa [hDegree] using hDual
  · rintro ⟨E, hDegree, hRank⟩
    refine ⟨canonical_divisor G - E, ?_, ?_⟩
    · rw [deg.map_sub, degree_of_canonical_divisor, hDegree]
      unfold dualDegree
      ring
    · have hDual :=
        (rank_ge_iff_dual_rank_ge hG E (dualRank G r d)).mp hRank
      simpa [hDegree] using hDual

end Utilities
