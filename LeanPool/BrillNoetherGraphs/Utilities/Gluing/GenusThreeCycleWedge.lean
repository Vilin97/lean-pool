/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.CanonicalSlackPair
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeGenusOne

/-!
# A rigid genus-one wedge on a genus-three graph

The canonical slack-pair construction supplies a degree-three divisor `D` on
the genus-three factor with both rank one and `D - 2(x)` winnable.  The exact
rigid-wedge criterion therefore carries that same divisor across an attached
genus-one cycle without adding chips.

The theorem uses the established `MarkedGraphs` namespace for API compatibility.
-/

namespace MarkedGraphs

open Utilities

universe uOneCycle vOneCycle

/-- A rigid genus-one block attached to a connected genus-three base carries
the base's degree-three pencil without adding any chips on the genus-one
factor. -/
theorem BNExists_vertexWedge_rankOneDegreeThree_of_genus_three
    (G : CFGraph.{uOneCycle}) (H : CFGraph.{vOneCycle})
    (x : G.V) (y : H.V)
    (hG : graphConnected G) (hGenusG : genus G = 3)
    (hH : PointedGenusOneRigid H y) :
    BNExists (vertexWedge G H x y) 1 3 := by
  obtain ⟨D, _Ddual, hD, _hDdual, _hPair⟩ :=
    exists_canonical_slack_dual_pair G hG (by omega) x x
  have hResidualWin :
      winnable G (D - oneChip x - oneChip x) :=
    (rank_nonneg_iff_winnable G (D - oneChip x - oneChip x)).mp
      ((rank_geq_iff G (D - oneChip x - oneChip x) 0).mpr hD.2.2)
  have hTwoChipRewrite :
      D - oneChip x - oneChip x =
        D - (2 : ℤ) • oneChip x := by
    funext z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hTwoChipRewrite] at hResidualWin
  refine ⟨wedgeLiftLeftDivisor G H x y D, ?_, ?_⟩
  · rw [deg_wedgeLiftLeftDivisor, hD.1, hGenusG]
  · exact (rank_wedgeLiftLeft_ge_one_iff G H x y hH D).mpr
      ⟨hD.2.1, hResidualWin⟩

end MarkedGraphs
