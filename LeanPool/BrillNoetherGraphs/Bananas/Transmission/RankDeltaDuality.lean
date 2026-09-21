/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Riemann--Roch duality for the marked rank second difference

The four affine terms in graph Riemann--Roch cancel in the marked second
difference.  Consequently `rankDelta` is invariant under the involution
`D ↦ K + u + v - D`.
-/

namespace Bananas

open Utilities

/-- Riemann--Roch preserves the marked rank second difference after translating
the canonical complement by the two marked chips. -/
theorem rankDelta_canonical_dual
    (M : TwiceMarked) (hconn : graph_connected M.graph)
    (D : CFDiv M.graph) :
    rankDelta M D =
      rankDelta M
        (canonical_divisor M.graph + one_chip M.u + one_chip M.v - D) := by
  let E : CFDiv M.graph :=
    canonical_divisor M.graph + one_chip M.u + one_chip M.v - D
  have hCompD :
      canonical_divisor M.graph - D =
        E - one_chip M.u - one_chip M.v := by
    dsimp [E]
    abel
  have hCompDu :
      canonical_divisor M.graph - (D - one_chip M.u) =
        E - one_chip M.v := by
    dsimp [E]
    abel
  have hCompDv :
      canonical_divisor M.graph - (D - one_chip M.v) =
        E - one_chip M.u := by
    dsimp [E]
    abel
  have hCompDuv :
      canonical_divisor M.graph -
          (D - one_chip M.u - one_chip M.v) = E := by
    dsimp [E]
    abel
  have hD := riemann_roch_for_graphs hconn D
  have hDu := riemann_roch_for_graphs hconn (D - one_chip M.u)
  have hDv := riemann_roch_for_graphs hconn (D - one_chip M.v)
  have hDuv := riemann_roch_for_graphs hconn
    (D - one_chip M.u - one_chip M.v)
  rw [hCompD] at hD
  rw [hCompDu] at hDu
  rw [hCompDv] at hDv
  rw [hCompDuv] at hDuv
  simp only [deg.map_sub, deg_one_chip] at hDu hDv hDuv
  change rankDelta M D = rankDelta M E
  unfold rankDelta
  linarith

end Bananas
