/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInfiniteConstruction
public import LeanPool.NavierStokesAndEuler.Euler.PacketFirstStageSupport
public import LeanPool.NavierStokesAndEuler.Euler.CurlSupport

@[expose] public section

/-!
# Common initial support of every constructed packet stage

The selected forward and joined corrections retain the common initial
support. Therefore every finite stage has initial velocity, all its spatial
derivatives, and initial vorticity supported in the closed ball of radius two.
-/

noncomputable section

namespace EulerPacketInduction.Stage

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerPacketInductionScales EulerPacketLowConstants EulerParentNeighborThreshold
  EulerPacketSourceScaleSequence

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B}

theorem joinedNext_initial_support {n : ℕ} (P : Stage S n) (hn : n ≠ 0)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    (hP : tsupport (fun x => P.state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2) :
    tsupport (fun x => (P.joinedNext hn hq hB).state.evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 :=
  GeometryJoinedChoice.initial_support (P.joinedInput hn hq hB) P.restrictedState
    (frequency S.J S.X n) (S.normal_frequency n) (supportScale S.J S.X (n+1))
    (S.support_pos (n+1)) (S.support_one (n+1)) (P.chooseJoined hn hq hB) symmetric hP

theorem successor_initial_support {n : ℕ} (P : Stage S n)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    (hP : tsupport (fun x => P.state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2) :
    tsupport (fun x => (P.successor hq hB).state.evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 := by
  cases n with
  | zero => exact P.forwardNext_initial_support hq hB hP
  | succ n => exact P.joinedNext_initial_support (Nat.succ_ne_zero n) hq hB hP

end EulerPacketInduction.Stage

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketInductionScales
  EulerPacketLowConstants EulerParentNeighborThreshold EulerMeanCutoffCurl

variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem stages_initial_support (n : ℕ) :
    tsupport (fun x => (stages S hq hB n).state.evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 := by
  induction n with
  | zero => exact S.firstStage_initial_support
  | succ n ih => exact (stages S hq hB n).successor_initial_support hq hB ih

theorem stages_initial_derivatives_support (n m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (fun x => (stages S hq hB n).state.evolution.velocity (0,x))) ⊆
      Metric.closedBall 0 2 :=
  (tsupport_iteratedFDeriv_subset m).trans (stages_initial_support S hq hB n)

theorem stages_initial_curl_support (n : ℕ) :
    tsupport (vectorCurl (fun x => (stages S hq hB n).state.evolution.velocity (0,x))) ⊆
      Metric.closedBall 0 2 := by
  apply (tsupport_vectorCurl_subset _ ?_).trans (stages_initial_support S hq hB n)
  exact ((stages S hq hB n).state.evolution.velocity_smooth
    (stages S hq hB n).parent.zeroTime).differentiable (by simp)

theorem packets_initial_support (n : ℕ) :
    tsupport (fun x => (packets n).state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2 :=
  stages_initial_support constructionScales le_rfl le_rfl n

theorem packets_initial_curl_support (n : ℕ) :
    tsupport (vectorCurl (fun x => (packets n).state.evolution.velocity (0,x))) ⊆
      Metric.closedBall 0 2 :=
  stages_initial_curl_support constructionScales le_rfl le_rfl n

end EulerPacketInduction
