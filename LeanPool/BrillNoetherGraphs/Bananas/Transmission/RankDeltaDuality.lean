/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Riemann--Roch duality for the marked rank second difference

The four affine terms in graph Riemann--Roch cancel in the marked second
difference.  Consequently `rankDelta` is invariant under the involution
`D ↦ K + u + v - D`.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Riemann--Roch preserves the marked rank second difference after translating
the canonical complement by the two marked chips. -/
theorem rankDelta_canonical_dual
    (M : TwiceMarked) (hconn : graphConnected M.graph)
    (D : CFDiv M.graph) :
    rankDelta M D =
      rankDelta M
        (canonicalDivisor M.graph + oneChip M.u + oneChip M.v - D) := by
  let E : CFDiv M.graph :=
    canonicalDivisor M.graph + oneChip M.u + oneChip M.v - D
  have hCompD :
      canonicalDivisor M.graph - D =
        E - oneChip M.u - oneChip M.v := by
    dsimp [E]
    abel
  have hCompDu :
      canonicalDivisor M.graph - (D - oneChip M.u) =
        E - oneChip M.v := by
    dsimp [E]
    abel
  have hCompDv :
      canonicalDivisor M.graph - (D - oneChip M.v) =
        E - oneChip M.u := by
    dsimp [E]
    abel
  have hCompDuv :
      canonicalDivisor M.graph -
          (D - oneChip M.u - oneChip M.v) = E := by
    dsimp [E]
    abel
  have hD := riemann_roch_for_graphs hconn D
  have hDu := riemann_roch_for_graphs hconn (D - oneChip M.u)
  have hDv := riemann_roch_for_graphs hconn (D - oneChip M.v)
  have hDuv := riemann_roch_for_graphs hconn
    (D - oneChip M.u - oneChip M.v)
  rw [hCompD] at hD
  rw [hCompDu] at hDu
  rw [hCompDv] at hDv
  rw [hCompDuv] at hDuv
  simp only [deg.map_sub, deg_one_chip] at hDu hDv hDuv
  change rankDelta M D = rankDelta M E
  unfold rankDelta
  linarith

end Bananas
