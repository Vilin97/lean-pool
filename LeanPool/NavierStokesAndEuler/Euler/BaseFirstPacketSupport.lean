/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseInductionStage
import LeanPool.NavierStokesAndEuler.Euler.ParentChoiceInitialSupport

/-! The actual finite initial base of the induction is compactly
supported: it is the compact smooth datum plus its first packet's
literal compact initial increment. -/

@[expose] public section


noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerPacketTerminalDatum EulerPacketSourceFrequency

theorem packetBase_initial_support (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime) :
    tsupport (fun x => (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 := by
  let A := packetBaseParent β hβ ell hell hell1 T hT hTB
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  have he : (fun x => S.evolution.velocity (0,x))=velocity (linear β) := by
    funext x
    have hm := S.evolution.velocity_match A.zeroTime x
    rw [A.position_initial] at hm
    exact hm.symm.trans (initial_velocity β hβ ell hell hell1 x)
  rw [he]
  exact velocity_support _

theorem support_of_pointwise_difference (f g : Space → Space) (r R : ℝ) (hr : r ≤ R)
    (hf : tsupport f ⊆ Metric.closedBall 0 R)
    (hd : tsupport (fun x => g x - f x) ⊆ Metric.closedBall 0 r) :
    tsupport g ⊆ Metric.closedBall 0 R :=
  support_of_difference f g R hf (hd.trans (Metric.closedBall_subset_closedBall hr))

namespace FirstPacketChoice

variable {β : ℝ} {hβ : |β| ≤ 1} {ell : ℝ} {hell : 0 < ell} {hell1 : ell ≤ 1}
  {T : ℝ} {hT : 0 < T} {hTB : T ≤ initialTime}
  {δ : ℝ} {hδ : 0 < δ} {hchild k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)

theorem initial_support :
    tsupport (fun x => F.state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2 := by
  -- The cutoff-support proof `hs` stays a variable: it is unified with the proof stored in
  -- `firstPacketState`, so the two packet velocities below agree syntactically (comparing them
  -- up to a differing proof term would unfold the whole correction field).
  have key := fun hs =>
    (packetBaseParent β hβ ell hell hell1 T hT hTB).exactForwardPacket_initial_increment_support
      (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)
      firstNormal firstNormal_unit firstFrame support compact δ hδ firstCoordinate
      hs (δ*hchild) (truncation k) F.hn k hk.four F.Q
      (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.inverse
      rfl (subset_halfBall.trans Metric.ball_subset_closedBall)
      (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.velocity
  unfold state firstPacketState SmoothState.forwardChild SmoothState.packetChild Evolution.child
  dsimp only
  exact support_of_pointwise_difference _ _ _ 2
    (by rw [packetBaseParent_scale]; linarith only [hell1])
    (packetBase_initial_support β hβ ell hell hell1 T hT hTB) (key _)

theorem initial_compact : HasCompactSupport (fun x => F.state.evolution.velocity (0,x)) :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) F.initial_support

end FirstPacketChoice
end EulerBaseDatum

namespace EulerPacketInductionScales.Scales

open Set EulerSmoothLimit

variable {c B : ℝ} (S : Scales c B)

theorem firstStage_state : S.firstStage.state = S.first.state S.j_one := rfl

theorem firstStage_initial_support :
    tsupport (fun x => S.firstStage.state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2 := by
  rw [firstStage_state, EulerBaseDatum.FirstScaleGuards.state]
  exact EulerBaseDatum.FirstPacketChoice.initial_support _

theorem firstStage_initial_compact :
    HasCompactSupport (fun x => S.firstStage.state.evolution.velocity (0,x)) :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _)
      S.firstStage_initial_support

theorem firstStage_initial_field_support :
    tsupport (S.firstStage.state.regularity.velocity S.firstStage.parent.zeroTime).field ⊆
      Metric.closedBall 0 2 := by
  have he : (S.firstStage.state.regularity.velocity S.firstStage.parent.zeroTime).field =
      fun x => S.firstStage.state.evolution.velocity (0,x) :=
    funext (fun x => (S.firstStage.state.regularity.velocity_match S.firstStage.parent.zeroTime
        x).symm)
  rw [he]
  exact S.firstStage_initial_support

end EulerPacketInductionScales.Scales
