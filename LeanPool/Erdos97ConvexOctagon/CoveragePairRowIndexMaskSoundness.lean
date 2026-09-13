/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks
public import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoiceSoundness
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! # Soundness of the transposed legal-row pair masks -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence

/-- The transposed pair table records exactly which row choices contain each pair bit. -/
theorem pairRowIndexMasks_bit
    (centre : Vertex) (pairIndex : Fin 64) (rowIndex : Fin 35) :
    bitSetB ((pairRowIndexMasks.getD centre.val #[]).getD pairIndex.val 0)
        rowIndex.val =
      bitSetB (searchRowChoiceAt centre rowIndex).pairMask pairIndex.val := by
  revert centre pairIndex rowIndex
  decide +kernel

end Erdos97Octagon.RawIncidence
