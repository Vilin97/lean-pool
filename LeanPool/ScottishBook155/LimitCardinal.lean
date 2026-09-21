/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.ProtectedChainLimit
import LeanPool.ScottishBook155.RecursionCardinal

/-!
# Cardinal bounds at protected limit stages
-/

namespace ScottishBook155

universe u

namespace ProtectedChain

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable {r L : ℝ} (C : ProtectedChain (ι := ι) r L)

noncomputable local instance limitCardinalSourceDirectedSystem :
    DirectedSystem (fun i => (C.stage i).source)
      (C.sourceSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ C.sourceSystem

noncomputable local instance limitCardinalTargetDirectedSystem :
    DirectedSystem (fun i => (C.stage i).target)
      (C.targetSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ C.targetSystem

theorem limitSource_mk_le
    (hι : Cardinal.mk ι ≤ stageCardinal)
    (hstage : ∀ i, Cardinal.mk (C.stage i).source ≤ stageCardinal) :
    Cardinal.mk C.LimitSource ≤ stageCardinal := by
  apply CardinalControl.completedDirectLimit_mk_le
  · exact aleph0_le_stageCardinal
  · exact hι
  · exact hstage
  · exact stageCardinal_power_aleph0

theorem limitTarget_mk_le
    (hι : Cardinal.mk ι ≤ stageCardinal)
    (hstage : ∀ i, Cardinal.mk (C.stage i).target ≤ stageCardinal) :
    Cardinal.mk C.LimitTarget ≤ stageCardinal := by
  apply CardinalControl.completedDirectLimit_mk_le
  · exact aleph0_le_stageCardinal
  · exact hι
  · exact hstage
  · exact stageCardinal_power_aleph0

theorem limitStage_source_mk_le (hr : 0 < r) (hL : 0 < L)
    (hι : Cardinal.mk ι ≤ stageCardinal)
    (hstage : ∀ i, Cardinal.mk (C.stage i).source ≤ stageCardinal) :
    Cardinal.mk (C.limitStage hr hL).source ≤ stageCardinal :=
  C.limitSource_mk_le hι hstage

theorem limitStage_target_mk_le (hr : 0 < r) (hL : 0 < L)
    (hι : Cardinal.mk ι ≤ stageCardinal)
    (hstage : ∀ i, Cardinal.mk (C.stage i).target ≤ stageCardinal) :
    Cardinal.mk (C.limitStage hr hL).target ≤ stageCardinal :=
  C.limitTarget_mk_le hι hstage

end ProtectedChain

end ScottishBook155
