/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds

/-! The actual initialized packet changes the initial velocity gradient
by the exponentially small early/history size plus its correction error.
These are the costs needed to preserve the localized source guards. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalLowBounds

open EulerSmoothLimit EulerPeriodicProfile

theorem norm_le_of_shear_error (V : Matrix) (amp δ θ ev size : ℝ) (r w : Space)
    (hamp : 0 ≤ amp) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : amp * (‖r‖ * ‖w‖) ≤ δ * size)
    (herr : ‖V - shearTerm amp (deriv (profile δ) θ) r w‖ ≤ ev) : ‖V‖ ≤ size+ev := by
  have hshear : ‖shearTerm amp (deriv (profile δ) θ) r w‖ ≤ size :=
    (shearTerm_norm_le amp _ δ r w hamp (profile_deriv_abs δ hδ hδ1 θ)).trans
      ((div_le_iff₀ hδ).2 (by nlinarith only [hsize]))
  have h := norm_of_remainder V 0 (shearTerm amp (deriv (profile δ) θ) r w) ev
    (by simpa only [sub_zero] using herr)
  simp only [norm_zero,zero_add] at h
  exact h.trans (add_le_add hshear le_rfl)

end EulerPacketPhysicalLowBounds

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketSourceGeometry EulerPacketMovingFrame EulerPacketGeometryLowBounds
  EulerPacketPhysicalLowBounds EulerPacketPrimaryFactorization EulerPeriodicProfile
  EulerSpatialCutoffs EulerPacketTerminalDatum
open scoped ContDiff

variable {A : Parent} (E : Evolution A)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower period A.T}
  (B : Budget period A.T_pos (correctionData (A.transverseData m hm J support hSupport) period κ hκ
      Z R))
  (residual : ApproximationResidual period A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) period κ hκ Z R))
  (k : ℝ) (hk : k * κ = 1)

section Joined

variable {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {F : ParentFrame (A.transverseData m hm J support hSupport) τ}
  {H : HistoryData ((A.transverseData m hm J support hSupport).initial τ hτ hτT.le)}
  (G : Guards hτ hτT F H) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hs : tsupport innerCutoff ⊆ support) (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)

include hk hδ hδ1 in
theorem exactPacket_bad_gradient_increment
    (ev ep : ℝ) (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime τ F.a F.epsilon t ≤ 1) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x -
      fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ G.hchild*G.badRatio+ev := by
  rw [(E.exactPacket_derivative_split m hm J support hSupport B residual k hk t
      x).1,add_sub_cancel_left]
  apply norm_le_of_shear_error _ (G.primaryAmplitude hball) G.δ
    (k*⟪m,E.inverse.normalized t (A.ell⁻¹ • x)⟫_ℝ) ev (G.hchild*G.badRatio)
    ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t (A.ell⁻¹ •
        x)))
    (canonicalVelocity τ hτ hτT H G.terminal hs t (E.inverse.normalized t (A.ell⁻¹ • x)))
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.bad_primary_size hball t ht (E.inverse.normalized t (A.ell⁻¹ •
      x)) hs
  · exact (herr t (A.ell⁻¹ • x)).1

include hk hδ hδ1 in
theorem exactPacket_initial_gradient_increment
    (ev ep : ℝ) (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (0,y)) x -
      fderiv ℝ (fun y => E.velocity (0,y)) x‖ ≤ G.hchild*G.badRatio+ev := by
  apply E.exactPacket_bad_gradient_increment m hm J support hSupport B residual k hk G hball hs hδ
      hδ1 ev ep herr A.zeroTime _ x
  change (F.a/F.epsilon)*(0-τ) ≤ 1
  have h : (F.a/F.epsilon)*(0-τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg G.a_pos.le G.epsilon_pos.le) (by linarith only [hτ])
  linarith only [h]

end Joined

section Forward

variable {F : ParentFrame (A.transverseData m hm J support hSupport) 0}
  (G : ForwardGuards F) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)

include hk hδ hδ1 in
theorem exactForwardPacket_early_gradient_increment
    (ev ep : ℝ) (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime 0 F.a F.epsilon t ≤ 1) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x -
      fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ G.hchild*G.earlyRatio+ev := by
  rw [(E.exactPacket_derivative_split m hm J support hSupport B residual k hk t
      x).1,add_sub_cancel_left]
  apply norm_le_of_shear_error _ (G.primaryAmplitude hball) G.δ
    (k*⟪m,E.inverse.normalized t (A.ell⁻¹ • x)⟫_ℝ) ev (G.hchild*G.earlyRatio)
    ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t (A.ell⁻¹ •
        x)))
    (EulerPacketForwardFactorization.canonicalVelocity (A.transverseData m hm J support hSupport)
        G.initialCoordinate t (E.inverse.normalized t (A.ell⁻¹ • x)))
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.early_primary_size hball t ht (E.inverse.normalized t (A.ell⁻¹ •
      x))
  · exact (herr t (A.ell⁻¹ • x)).1

include hk hδ hδ1 in
theorem exactForwardPacket_initial_gradient_increment
    (ev ep : ℝ) (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (0,y)) x -
      fderiv ℝ (fun y => E.velocity (0,y)) x‖ ≤ G.hchild*G.earlyRatio+ev := by
  apply E.exactForwardPacket_early_gradient_increment m hm J support hSupport B residual k hk G
      hball hδ hδ1 ev ep herr A.zeroTime _ x
  change (F.a/F.epsilon)*(0-0) ≤ 1
  norm_num

end Forward

end EulerParentPacketFrames.Evolution
