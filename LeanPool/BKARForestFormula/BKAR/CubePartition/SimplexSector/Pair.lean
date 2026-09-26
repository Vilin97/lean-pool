/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Finite

/-! # Two-edge specialization of finite simplex-sector conversion -/

public section

namespace BKAR.Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two-edge conversion is the corresponding instance of finite-order conversion. -/
theorem orderedContribution_pair_eq_orderedCubeSectorContribution
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedContribution [e₁, e₂] ρ =
      F.orderedCubeSectorContribution [e₁, e₂] ρ :=
  F.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff horder ρ hρ

end BKAR.Forest
