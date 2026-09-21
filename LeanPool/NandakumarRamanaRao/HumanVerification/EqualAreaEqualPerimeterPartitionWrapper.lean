/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.HumanVerification.Transfer
import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.Theorem

/-! # Equal Area Equal Perimeter Partition Wrapper -/

open Set MeasureTheory

noncomputable section

namespace HumanVerification

/--
Internal generic wrapper.  Its conclusion is definitionally equal to the
human-facing statement once `Main.lean` supplies the model instance locally inside the proof of its
public theorem.
-/
theorem equalAreaEqualPerimeterPartitionWrapper
    {α : Type} [NRR.HumanExport.ConvexFigureModel α]
    (F : α) (n : ℕ) (hn : 0 < n) :
    ∃ pieces : Fin n → α,
      NRR.HumanExport.IsConvexPartition F pieces ∧
      (∀ i j,
        NRR.HumanExport.area (pieces i) =
          NRR.HumanExport.area (pieces j)) ∧
      (∀ i j,
        NRR.HumanExport.perimeter (pieces i) =
          NRR.HumanExport.perimeter (pieces j)) := by
  exact NRR.HumanExport.equalAreaEqualPerimeterPartition_of_cauchyCrofton
    CauchyCrofton.cauchyCroftonStatement F n hn

end HumanVerification
