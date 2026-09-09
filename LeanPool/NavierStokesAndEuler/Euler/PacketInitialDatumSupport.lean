/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageInitialLimit

@[expose] public section

/-! The full smooth initial datum retains the common support of its
finite initial base and its actual summable packet increments. -/

noncomputable section

namespace EulerPacketInduction.Stage

open Set EulerSmoothLimit EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerNormalPacketParameters EulerPacketInitial EulerLpTranslation
  EulerLpTranslation.SmoothL2Field

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : ∀ n, Stage S n)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem initialDataLimit_support
    (hbase : tsupport (initialBase P).field ⊆ Metric.closedBall 0 2) :
    tsupport (initialDataLimit P hq hB).field ⊆ Metric.closedBall 0 2 := by
  let tail := initialLimit (initialTailInput P hq hB) (S.J+1)
    (by have h := S.stage_large; omega) (sourceConstant 4) 320 (sourceConstant_pos 4)
    (by norm_num) 20 1000 (scaleSequence S.J S.X 1) (S.sequence_one 1)
    (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
    (initialTail_four (S := S)) (initialTail_frequency P hq hB)
  have htail : tsupport tail.field ⊆ Metric.closedBall 0 2 :=
    initialLimit_support (initialTailInput P hq hB) (S.J+1)
      (by have h := S.stage_large; omega) (sourceConstant 4) 320 (sourceConstant_pos 4)
      (by norm_num) 20 1000 (scaleSequence S.J S.X 1) (S.sequence_one 1)
      (initialTail_parameter P hq hB) (initialTail_scale P hq hB) (initialTail_sigma P hq hB)
      (initialTail_four (S := S)) (initialTail_frequency P hq hB)
  change tsupport ((initialBase P).field+tail.field) ⊆ Metric.closedBall 0 2
  exact (tsupport_add _ _).trans (union_subset hbase htail)

theorem initialDataLimit_compact
    (hbase : tsupport (initialBase P).field ⊆ Metric.closedBall 0 2) :
    HasCompactSupport (initialDataLimit P hq hB).field :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _)
    (initialDataLimit_support P hq hB hbase)

theorem initialDataLimit_support_of_physical
    (hbase : tsupport (fun x => (P 1).state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2) :
    tsupport (initialDataLimit P hq hB).field ⊆ Metric.closedBall 0 2 := by
  apply initialDataLimit_support P hq hB
  have he : (initialBase P).field=(fun x => (P 1).state.evolution.velocity (0,x)) :=
    funext (fun x => ((P 1).state.regularity.velocity_match (P 1).parent.zeroTime x).symm)
  rwa [he]

end EulerPacketInduction.Stage
