/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketInitialLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild

@[expose] public section

/-! The next packet's localized lower initial-gradient bounds and upper
pressure bound are consequences of the exact physical estimates. The
radius stays fixed, and the boundary parameter has a canonical value. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerMeanHarmonic
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerPacketTerminalDatum EulerSpatialCutoffs
  EulerPacketSourceGeometry EulerPacketGeometryLowBounds

variable {A : Parent} (E : Evolution A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower period A.T}
  (B : Budget period A.T_pos (correctionData (A.transverseData m hm J support hSupport) period κ hκ
    Z R))
  (residual : ApproximationResidual period A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) period κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field period A.T raw) (hV : Z=V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data period A.T) (hG : G.A=B.liftedPacketCoefficient period V)
  (k : ℝ) (hk : k*κ=1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

section Joined

variable {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {F : ParentFrame (A.transverseData m hm J support hSupport) τ}
  {D : HistoryData ((A.transverseData m hm J support hSupport).initial τ hτ hτT.le)}
  (C : Guards hτ hτT F D) (hball : (1/2 : ℝ) ≤ C.radius)
  (hs : tsupport EulerSpatialCutoffs.innerCutoff ⊆ support) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)

def joinedChildLowBounds (H : LowBounds A) (ev ep CM CH : ℝ)
    (herr : E.SourceErrors m hm J support hSupport B residual k C hball hs ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.badRatio)+ep)*(A.T^2/2)+
      (H.Be+(C.hchild*C.badRatio+ev))*A.T+
      boundaryLocalizationC2*(H.Bc+(C.hchild*C.badRatio+ev))*H.r^3*A.T ≤ 1/2) :
    LowBounds (A.child G k m hgraph nextEll hnext hnext1) := by
  have hev : 0 ≤ ev := (norm_nonneg _).trans (herr A.zeroTime 0).1
  have hep : 0 ≤ ep := (norm_nonneg _).trans (herr A.zeroTime 0).2
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM A.zeroTime 0)
  apply E.updateLowBounds
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1)
    H (C.hchild*C.badRatio+ev) (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.badRatio)+ep)
  · exact add_nonneg (mul_nonneg C.child_nonneg C.badRatio_nonneg) hev
  · positivity [H.K_nonneg,C.child_nonneg,C.delta_nonneg,goodRatio_pos,C.badRatio_nonneg]
  · intro x
    exact E.exactPacket_initial_gradient_increment m hm J support hSupport B residual k hk
      C hball hs hδ hδ1 ev ep herr x
  · intro t x z
    let EC := E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1
    rw [← EC.pressure_hessian_eq_force]
    exact (E.exactPacket_whole_horizon_low_bounds m hm J support hSupport B residual k hk
      C hball hs hδ hδ1 ev ep CM CH H.K herr hCM hCH
      (E.force_quadratic_upper_of_lowBounds H) t x).2.2 z
  · exact hsmall

end Joined

section Forward

variable {F : ParentFrame (A.transverseData m hm J support hSupport) 0}
  (C : ForwardGuards F) (hball : (1/2 : ℝ) ≤ C.radius)
  (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)

def forwardChildLowBounds (H : LowBounds A) (ev ep CM CH : ℝ)
    (herr : E.ForwardSourceErrors m hm J support hSupport B residual k C hball ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.earlyRatio)+ep)*(A.T^2/2)+
      (H.Be+(C.hchild*C.earlyRatio+ev))*A.T+
      boundaryLocalizationC2*(H.Bc+(C.hchild*C.earlyRatio+ev))*H.r^3*A.T ≤ 1/2) :
    LowBounds (A.child G k m hgraph nextEll hnext hnext1) := by
  have hev : 0 ≤ ev := (norm_nonneg _).trans (herr A.zeroTime 0).1
  have hep : 0 ≤ ep := (norm_nonneg _).trans (herr A.zeroTime 0).2
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM A.zeroTime 0)
  apply E.updateLowBounds
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1)
    H (C.hchild*C.earlyRatio+ev) (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.earlyRatio)+ep)
  · exact add_nonneg (mul_nonneg C.child_nonneg C.earlyRatio_nonneg) hev
  · positivity [H.K_nonneg,C.child_nonneg,C.delta_nonneg,goodRatio_pos,C.earlyRatio_nonneg]
  · intro x
    exact E.exactForwardPacket_initial_gradient_increment m hm J support hSupport B residual k hk
      C hball hδ hδ1 ev ep herr x
  · intro t x z
    let EC := E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1
    rw [← EC.pressure_hessian_eq_force]
    exact (E.exactForwardPacket_whole_horizon_low_bounds m hm J support hSupport B residual k hk
      C hball hδ hδ1 ev ep CM CH H.K herr hCM hCH
      (E.force_quadratic_upper_of_lowBounds H) t x).2.2 z
  · exact hsmall

end Forward

end EulerParentPacketFrames.Evolution
