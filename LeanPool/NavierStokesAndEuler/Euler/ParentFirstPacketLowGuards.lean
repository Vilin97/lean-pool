/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardInitialSupport
public import LeanPool.NavierStokesAndEuler.Euler.ParentHomogeneousPacketLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild

@[expose] public section

/-! The first packet preserves the exterior initial bound exactly and
creates the small core used by later stages. Its pressure guard comes
from the actual scalar pressure, and the exact correction adds no initial
support outside the packet ball. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerMeanHarmonic
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketPhysicalLowBounds EulerPacketFirstLowBounds

variable {A : Parent} (E : Evolution A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hchild : ℝ) (hhchild : 0 ≤ hchild)
  (ξ : U) (hs : tsupport EulerSpatialCutoffs.innerCutoff ⊆ support)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period A.T_pos
    (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      δ hδ ξ hs (δ*hchild) (A.sourceAgreement m hm J support hSupport H) N hN k hk))
  (G : EulerPhysicalGraphFlowBounds.Data period A.T)
  (hG : G.A=Q.liftedPacketCoefficient period
    (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      δ hδ ξ hs (δ*hchild) N k))
  (hgraph : ∀ t q, graphConstraint k m (G.A.field t q)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

def firstChildLowBounds (hL : H.L=0) (hquarter : A.ell ≤ 1/4)
    (hSupportBall : support ⊆ Metric.closedBall 0 (1/2 : ℝ))
    (ev ep CM CH : ℝ)
    (herr : E.HomogeneousSourceErrors m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
        hSupport) rfl
        δ hδ ξ hs (δ*hchild) (A.sourceAgreement m hm J support hSupport H) N hN k hk)
      k δ hchild ξ ev ep)
    (hsize : ∀ (t : Icc (0 : ℝ) A.T) x,
      ‖(A.transverseData m hm J support hSupport).normal.field t x‖*
        ‖EulerPacketForwardFactorization.canonicalVelocity
          (A.transverseData m hm J support hSupport) ξ t x‖ ≤ firstRatio)
    (hflux : ∀ (t : Icc (0 : ℝ) A.T) x,
      0 ≤ ⟪(A.transverseData m hm J support hSupport).normal.field t x,
        (A.transverseData m hm J support hSupport).M.field t x
          (EulerPacketForwardFactorization.canonicalVelocity
            (A.transverseData m hm J support hSupport) ξ t x)⟫_ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K+2*CM*δ*(hchild*firstRatio)+ep)*(A.T^2/2)+CM*A.T+
      boundaryLocalizationC2*(CM+hchild*firstRatio+ev)*A.ell^3*A.T ≤ 1/2) :
    LowBounds (A.child G k m hgraph nextEll hnext hnext1) := by
  let residual := forwardInitializedApproximationResidual (A.meanData H)
    (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs (δ*hchild)
    (A.sourceAgreement m hm J support hSupport H) N hN k hk
  let V := forwardInitializedNormalizedField (A.meanData H)
    (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs (δ*hchild) N k
  have hkinv : k*k⁻¹=1 := mul_inv_cancel₀ (by linarith : k ≠ 0)
  let EC := E.child m hm J support hSupport Q residual V rfl G hG k hkinv hgraph nextEll hnext
    hnext1
  let Cnew := CM+hchild*firstRatio+ev
  let Knew := H.K+2*CM*δ*(hchild*firstRatio)+ep
  have hev : 0 ≤ ev := (norm_nonneg _).trans (herr A.zeroTime 0).1
  have hep : 0 ≤ ep := (norm_nonneg _).trans (herr A.zeroTime 0).2
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM A.zeroTime 0)
  have hv (t : Icc (0 : ℝ) A.T) (x : Space) :
      ‖fderiv ℝ (fun y => EC.velocity (t,y)) x‖ ≤ Cnew ∧
      ‖fderiv ℝ (gradient (fun y => EC.pressure (t,y))) x‖ ≤ CH+2*CM*(hchild*firstRatio)+ep ∧
      ∀ z, ⟪fderiv ℝ (gradient (fun y => EC.pressure (t,y))) x z,z⟫_ℝ ≤ Knew*‖z‖^2 :=
    E.exactHomogeneousPacket_low_bounds m hm J support hSupport Q residual k hkinv
      δ hchild ξ hδ hδ1 hhchild ev ep CM CH H.K herr hsize hflux t x
      (hCM t x) (hCH t x) (E.force_quadratic_upper_of_lowBounds H t x)
  apply EC.lowBoundsFromPhysical CM Cnew (boundaryLocalizationC1*Cnew+1) A.ell Knew
    hCM0
  · dsimp [Cnew]
    positivity [firstRatio_pos]
  · linarith
  · exact A.ell_pos.le
  · exact hquarter
  · dsimp [Knew]
    positivity [H.K_nonneg,firstRatio_pos]
  · intro x hx z
    have he : fderiv ℝ (fun y => EC.velocity (0,y)) x=fderiv ℝ (fun y => E.velocity (0,y)) x :=
      A.exactForwardPacket_initial_gradient_exterior H m hm J support hSupport
        δ hδ ξ hs (δ*hchild) N hN k hk Q E.inverse hL hSupportBall E.velocity x hx
    rw [he]
    exact quadratic_lower_of_norm _ CM (hCM A.zeroTime x) z
  · intro x _ z
    exact quadratic_lower_of_norm _ Cnew (hv A.zeroTime x).1 z
  · intro t x z
    rw [← EC.pressure_hessian_eq_force]
    exact (hv t x).2.2 z
  · exact hsmall

end EulerParentPacketFrames.Evolution
