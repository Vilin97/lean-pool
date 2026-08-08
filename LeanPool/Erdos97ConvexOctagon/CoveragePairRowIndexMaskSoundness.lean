/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks
import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoiceSoundness

/-! # Soundness of the transposed legal-row pair masks -/

namespace Erdos97Octagon.RawIncidence

private def pairRowIndexMasksValidAtB (centre : Vertex) : Bool :=
  (List.range 64).all fun pairIndex =>
    (List.range 35).all fun rowIndex =>
      bitSetB ((pairRowIndexMasks.getD centre.val #[]).getD pairIndex 0)
          rowIndex ==
        bitSetB ((searchRowChoices.getD centre.val #[]).getD rowIndex
          ⟨0, 0⟩).pairMask pairIndex

private theorem pairRowIndexMasks_valid (centre : Vertex) :
    pairRowIndexMasksValidAtB centre = true := by
  fin_cases centre <;> decide

/-- The transposed pair table records exactly which row choices contain each pair bit. -/
theorem pairRowIndexMasks_bit
    (centre : Vertex) (pairIndex : Fin 64) (rowIndex : Fin 35) :
    bitSetB ((pairRowIndexMasks.getD centre.val #[]).getD pairIndex.val 0)
        rowIndex.val =
      bitSetB (searchRowChoiceAt centre rowIndex).pairMask pairIndex.val := by
  have hpair := (List.all_eq_true.mp (pairRowIndexMasks_valid centre))
    pairIndex.val (List.mem_range.mpr pairIndex.isLt)
  have hrow := (List.all_eq_true.mp hpair)
    rowIndex.val (List.mem_range.mpr rowIndex.isLt)
  simpa only [pairRowIndexMasksValidAtB, beq_iff_eq, searchRowChoiceAt] using hrow

end Erdos97Octagon.RawIncidence
