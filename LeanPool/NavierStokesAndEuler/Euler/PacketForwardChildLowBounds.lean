/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildFieldMatch
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds

/-! The time-zero amplification stage preserves the actual sharp
physical derivative and upper pressure bounds. The early interval keeps
its exponential gain, and the good interval retains the extra delta in
the upper pressure estimate. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalLowBounds

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerPacketForwardFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (ξ : U) (a slope : ℝ)

theorem forwardPressureTerm_eq_coefficient (t : Icc (0 : ℝ) D.T) (x : Space) :
    pressureTerm a slope (D.M.field t x) (D.normal.field t x)
      (canonicalVelocity D ξ t x) =
    (EulerPacketForwardShear.pressureCoefficient D ξ a t x*slope) •
      rankOne ℝ (D.normal.field t x) (D.normal.field t x) := by
  unfold pressureTerm EulerPacketForwardShear.pressureCoefficient
  congr 1
  ring

end EulerPacketPhysicalLowBounds

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketSourceGeometry EulerPacketMovingFrame EulerPacketGeometryLowBounds
  EulerPacketPhysicalLowBounds EulerPacketForwardFactorization EulerPeriodicProfile
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

variable {F : ParentFrame (A.transverseData m hm J support hSupport) 0}
  (G : ForwardGuards F) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)

/-- The exact source (20) errors, expressed on the same normalized
packet that defines the physical child. These are precisely the two
errors supplied by the same-Q packet choice. -/
def ForwardSourceErrors (ev ep : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
    ‖fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k E.inverse t) x -
      shearTerm (G.primaryAmplitude hball) (deriv (profile G.δ) (k*⟪m,E.inverse.normalized t x⟫_ℝ))
        ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))
        (canonicalVelocity (A.transverseData m hm J support hSupport) G.initialCoordinate t
            (E.inverse.normalized t x))‖ ≤ ev ∧
    ‖fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k E.inverse
        t)) x -
      pressureTerm (G.primaryAmplitude hball) (deriv (profile G.δ) (k*⟪m,E.inverse.normalized t
          x⟫_ℝ))
        ((A.transverseData m hm J support hSupport).M.field t (E.inverse.normalized t x))
        ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))
        (canonicalVelocity (A.transverseData m hm J support hSupport) G.initialCoordinate t
            (E.inverse.normalized t x))‖ ≤ ep

/-- The literal strict errors returned by the global same-Q packet
theorem imply the error record without any additional analytic bound. -/
theorem forwardSourceErrors_of_global (ev ep : ℝ)
    (herr : ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
      ‖fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k E.inverse t) x -
        (G.primaryAmplitude hball * deriv (profile G.δ) (k * ⟪m, E.inverse.normalized t x⟫_ℝ)) •
          rankOne ℝ (canonicalVelocity (A.transverseData m hm J support hSupport)
              G.initialCoordinate t (E.inverse.normalized t x))
            ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))‖
                < ev ∧
      ‖fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k
          E.inverse t)) x -
        (EulerPacketForwardShear.pressureCoefficient (A.transverseData m hm J support hSupport)
            G.initialCoordinate (G.primaryAmplitude hball) t
            (E.inverse.normalized t x) *
 deriv (profile G.δ) (k * ⟪m, E.inverse.normalized t x⟫_ℝ)) •
          rankOne ℝ ((A.transverseData m hm J support hSupport).normal.field t
              (E.inverse.normalized t x))
            ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))‖
                < ep) :
    E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep := by
  intro t x
  refine ⟨(herr t x).1.le,?_⟩
  erw [forwardPressureTerm_eq_coefficient]
  exact (herr t x).2.le

include hk hδ hδ1 in
theorem exactForwardPacket_good_low_bounds
    (ev ep CM CH Kupper : ℝ)
    (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : 1 ≤ scaledTime 0 F.a F.epsilon t) (x : Space)
    (hCM : ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hupper : ∀ z, ⟪fderiv ℝ (E.force t) x z, z⟫_ℝ ≤ Kupper * ‖z‖ ^ 2) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x‖ ≤
      CM+G.hchild*goodRatio+ev ∧
    ‖fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x‖ ≤
      CH+2*CM*(G.hchild*goodRatio)+ep ∧
    ∀ z, ⟪fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x z,z⟫_ℝ ≤
      (Kupper+2*CM*G.δ*(G.hchild*goodRatio)+ep)*‖z‖^2 := by
  let y := E.inverse.normalized t (A.ell⁻¹ • x)
  have herr' := herr t (A.ell⁻¹ • x)
  have he := E.exactPacket_derivative_split m hm J support hSupport B residual k hk t x
  have hm' : (A.transverseData m hm J support hSupport).M.field t y =
      fderiv ℝ (fun y => E.velocity (t,y)) x := E.strain_at_normalized_inverse t x
  apply good_step_bounds _ _ _ _ ((A.transverseData m hm J support hSupport).M.field t y)
    ((A.transverseData m hm J support hSupport).normal.field t y)
    (canonicalVelocity (A.transverseData m hm J support hSupport) G.initialCoordinate t y)
    (G.primaryAmplitude hball) G.δ (k*⟪m,y⟫_ℝ) ev ep CM CM CH (G.hchild*goodRatio)
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.good_primary_size hball t ht y
  · rw [hm']; exact hCM
  · exact hCM
  · exact hCH
  · rw [he.1,add_sub_cancel_left]
    exact herr'.1
  · rw [he.2,add_sub_cancel_left]
    exact herr'.2
  · exact G.good_primary_flux hball t ht y
  · exact hupper

include hk hδ hδ1 in
theorem exactForwardPacket_early_low_bounds
    (ev ep CM CH Kupper : ℝ)
    (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime 0 F.a F.epsilon t ≤ 1) (x : Space)
    (hCM : ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hupper : ∀ z, ⟪fderiv ℝ (E.force t) x z, z⟫_ℝ ≤ Kupper * ‖z‖ ^ 2) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x‖ ≤
      CM+G.hchild*G.earlyRatio+ev ∧
    ‖fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x‖ ≤
      CH+2*CM*(G.hchild*G.earlyRatio)+ep ∧
    ∀ z, ⟪fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x z,z⟫_ℝ ≤
      (Kupper+2*CM*(G.hchild*G.earlyRatio)+ep)*‖z‖^2 := by
  let y := E.inverse.normalized t (A.ell⁻¹ • x)
  have herr' := herr t (A.ell⁻¹ • x)
  have he := E.exactPacket_derivative_split m hm J support hSupport B residual k hk t x
  have hm' : (A.transverseData m hm J support hSupport).M.field t y =
      fderiv ℝ (fun y => E.velocity (t,y)) x := E.strain_at_normalized_inverse t x
  apply absolute_step_bounds _ _ _ _ ((A.transverseData m hm J support hSupport).M.field t y)
    ((A.transverseData m hm J support hSupport).normal.field t y)
    (canonicalVelocity (A.transverseData m hm J support hSupport) G.initialCoordinate t y)
    (G.primaryAmplitude hball) G.δ (k*⟪m,y⟫_ℝ) ev ep CM CM CH (G.hchild*G.earlyRatio)
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.early_primary_size hball t ht y
  · rw [hm']; exact hCM
  · exact hCM
  · exact hCH
  · rw [he.1,add_sub_cancel_left]
    exact herr'.1
  · rw [he.2,add_sub_cancel_left]
    exact herr'.2
  · exact hupper

include hk hδ hδ1 in
/-- The full horizon has one fixed absolute-size cost, while the upper
pressure cost retains delta on good times and the exponentially small
bad-time ratio. The parent constants remain the actual sharp CM and CH. -/
theorem exactForwardPacket_whole_horizon_low_bounds
    (ev ep CM CH Kupper : ℝ)
    (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hupper : ∀ (t : Icc (0 : ℝ) A.T) x z, ⟪fderiv ℝ (E.force t) x z, z⟫_ℝ ≤ Kupper * ‖z‖ ^ 2)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x‖ ≤
      CM+G.hchild*(goodRatio+G.earlyRatio)+ev ∧
    ‖fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x‖ ≤
      CH+2*CM*G.hchild*(goodRatio+G.earlyRatio)+ep ∧
    ∀ z, ⟪fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x z,z⟫_ℝ ≤
      (Kupper+2*CM*G.hchild*(G.δ*goodRatio+G.earlyRatio)+ep)*‖z‖^2 := by
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM t x)
  have hchild := G.child_nonneg
  have hbad := G.earlyRatio_nonneg
  have hgood := goodRatio_pos.le
  by_cases ht : 1 ≤ scaledTime 0 F.a F.epsilon t
  · obtain ⟨hv,hp,hq⟩ := E.exactForwardPacket_good_low_bounds m hm J support hSupport B residual k
      hk
      G hball hδ hδ1 ev ep CM CH Kupper herr t ht x (hCM t x) (hCH t x) (hupper t x)
    refine ⟨hv.trans ?_,hp.trans ?_,fun z => (hq z).trans ?_⟩
    · nlinarith only [mul_nonneg hchild hbad]
    · nlinarith only [mul_nonneg (mul_nonneg hCM0 hchild) hbad]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [mul_nonneg (mul_nonneg hCM0 hchild) hbad]
  · obtain ⟨hv,hp,hq⟩ := E.exactForwardPacket_early_low_bounds m hm J support hSupport B residual k
      hk
      G hball hδ hδ1 ev ep CM CH Kupper herr t (le_of_not_ge ht) x (hCM t x) (hCH t x) (hupper t x)
    refine ⟨hv.trans ?_,hp.trans ?_,fun z => (hq z).trans ?_⟩
    · nlinarith only [mul_nonneg hchild hgood]
    · nlinarith only [mul_nonneg (mul_nonneg hCM0 hchild) hgood]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hCM0 hchild) G.delta_nonneg) hgood]

end EulerParentPacketFrames.Evolution
