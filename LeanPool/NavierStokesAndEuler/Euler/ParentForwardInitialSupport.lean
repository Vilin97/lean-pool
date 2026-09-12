/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketChildFieldMatch
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardExactFields
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitialSupport

/-! The same forward correction used by the actual child has the
literal compact initial support when the mean boundary parameter is zero. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.ParticleInverse

open EulerSmoothLimit Set

variable {A : Parent} (I : ParticleInverse A)

theorem normalized_initial (x : Space) : I.normalized A.zeroTime x=x := by
  simp only [normalized,Parent.packetInverse,Parent.zeroTime,
    projIcc_of_mem A.T_pos.le (show (0 : ℝ) ∈ Icc 0 A.T from ⟨le_rfl,A.T_pos.le⟩)]
  change A.ell⁻¹ • I.field A.zeroTime (A.ell • x)=x
  rw [I.field_initial,smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul]

end EulerParentPacketFrames.ParticleInverse

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransverseFrameCoordinates
  EulerAllOrderDriftCorrection EulerPacketTerminalDatum

variable (A : Parent) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ support) (α : ℝ)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period A.T_pos
    (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk))
  (I : ParticleInverse A)

theorem normalizedPacketVelocity_forwardInitialized (t : Icc (0 : ℝ) A.T) :
    A.normalizedPacketVelocity m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α
        (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I t =
    forwardInitializedExactPhysicalVelocity (A.meanData H) (A.transverseData m hm J support
        hSupport) rfl
      δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk Q t (I.normalized t) := rfl

theorem normalizedPacketPressure_forwardInitialized (t : Icc (0 : ℝ) A.T) :
    A.normalizedPacketPressure m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α
        (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I t =
    forwardInitializedExactPhysicalPressure (A.meanData H) (A.transverseData m hm J support
        hSupport) rfl
      δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk Q t (I.normalized t) := rfl


theorem exactForwardPacket_initial_increment_support (hL : H.L = 0)
    (hS : support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (u : ℝ × Space → Space) :
    tsupport (fun x => A.exactPacketVelocity m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I.field u (0,x)-u
            (0,x)) ⊆
      Metric.closedBall 0 (A.ell/2) := by
  have hi : I.normalized A.zeroTime=id := funext I.normalized_initial
  have hv := A.normalizedPacketVelocity_forwardInitialized H m hm J support hSupport
    δ hδ ξ hs α N hN k hk Q I A.zeroTime
  rw [hi] at hv
  have he : (fun x => A.exactPacketVelocity m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I.field u (0,x)-u
            (0,x)) =
    EulerPhysicalL2Scaling.scale A.ell
      (forwardInitializedExactPhysicalVelocity (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk Q A.zeroTime id) := by
    funext x
    calc
      _ = EulerPacketPhysicalLowBounds.addVelocity A.ell (fun y => u (0,y))
          (A.normalizedPacketVelocity m hm J support hSupport Q
            (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J
                support hSupport) rfl
              δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I A.zeroTime)
                  x-u (0,x) :=
        congrArg (fun v : Space => v-u (0,x))
          (A.exactPacketVelocity_eq_addVelocity m hm J support hSupport Q
            (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J
                support hSupport) rfl
              δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I u A.zeroTime
                  x)
      _ = _ := by
        simp only [EulerPacketPhysicalLowBounds.addVelocity, add_sub_cancel_left, hv,
            EulerPhysicalL2Scaling.scale]
  rw [he]
  exact forwardInitializedExactPhysicalVelocity_initial_support (A.meanData H)
    (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs α
    (A.sourceAgreement m hm J support hSupport H) N hN k hk Q hL hS

theorem exactForwardPacket_initial_gradient_exterior (hL : H.L = 0)
    (hS : support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (u : ℝ × Space → Space)
    (x : Space) (hx : A.ell ≤ ‖x‖) :
    fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I.field u (0,y)) x =
      fderiv ℝ (fun y => u (0,y)) x := by
  have hnot : x ∉ tsupport (fun y => A.exactPacketVelocity m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I.field u (0,y)-u
            (0,y)) := by
    intro h
    have hh := A.exactForwardPacket_initial_increment_support H m hm J support hSupport
      δ hδ ξ hs α N hN k hk Q I hL hS u h
    rw [Metric.mem_closedBall,dist_zero_right] at hh
    linarith only [hh,hx,A.ell_pos]
  have heq := notMem_tsupport_iff_eventuallyEq.mp hnot
  have hfun : (fun y => A.exactPacketVelocity m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I.field u (0,y))
            =ᶠ[nhds x]
      (fun y => u (0,y)) := by
    filter_upwards [heq] with y hy
    exact sub_eq_zero.mp hy
  exact hfun.fderiv_eq

end EulerParentPacketFrames.Parent
