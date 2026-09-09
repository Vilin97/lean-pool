/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardSuccessor

@[expose] public section

/-! The finite initial base used by the limiting construction is the
actual first normal forward packet over the actual first packet state. -/

noncomputable section

namespace EulerPacketInduction.Stage

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerPacketInductionScales EulerPacketLowConstants EulerParentNeighborThreshold
  EulerPacketSourceScaleSequence

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem forwardNext_initial_support
    (hP : tsupport (fun x => P.state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2) :
    tsupport (fun x => (P.forwardNext hq hB).state.evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 :=
  GeometryForwardChoice.initial_support (P.forwardInput hq hB) P.restrictedState
    (frequency S.J S.X 0) (S.normal_frequency 0) (supportScale S.J S.X 1)
    (S.support_pos 1) (S.support_one 1) (P.chooseForward hq hB) symmetric hP

theorem forwardNext_initial_field_support
    (hP : tsupport (fun x => P.state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2) :
    tsupport ((P.forwardNext hq hB).state.regularity.velocity
      (P.forwardNext hq hB).parent.zeroTime).field ⊆ Metric.closedBall 0 2 := by
  have he : ((P.forwardNext hq hB).state.regularity.velocity
      (P.forwardNext hq hB).parent.zeroTime).field =
      fun x => (P.forwardNext hq hB).state.evolution.velocity (0,x) :=
    funext (fun x => ((P.forwardNext hq hB).state.regularity.velocity_match
      (P.forwardNext hq hB).parent.zeroTime x).symm)
  rw [he]
  exact P.forwardNext_initial_support hq hB hP

end EulerPacketInduction.Stage

namespace EulerPacketInductionScales.Scales

open Set EulerSmoothLimit EulerPacketLowConstants EulerParentNeighborThreshold

variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem firstForwardStage_initial_support :
    tsupport (fun x => (S.firstStage.forwardNext hq hB).state.evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 :=
  S.firstStage.forwardNext_initial_support hq hB S.firstStage_initial_support

theorem firstForwardStage_initial_field_support :
    tsupport ((S.firstStage.forwardNext hq hB).state.regularity.velocity
      (S.firstStage.forwardNext hq hB).parent.zeroTime).field ⊆ Metric.closedBall 0 2 :=
  S.firstStage.forwardNext_initial_field_support hq hB S.firstStage_initial_support

end EulerPacketInductionScales.Scales
