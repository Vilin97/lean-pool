/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFirstLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildFieldMatch
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardChildLowBounds

/-! Exact low-order propagation for the first homogeneous packet, whose
amplitude is delta times the desired initial shear. -/

@[expose] public section


noncomputable section

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

variable (δ hchild : ℝ) (ξ : U) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhchild : 0 ≤ hchild)

/-- The exact source (20) errors, expressed on the same normalized
packet that defines the physical child. These are precisely the two
errors supplied by the same-Q packet choice. -/
def HomogeneousSourceErrors (ev ep : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
    ‖fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k E.inverse t) x -
      shearTerm (δ*hchild) (deriv (profile δ) (k*⟪m,E.inverse.normalized t x⟫_ℝ))
        ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))
        (canonicalVelocity (A.transverseData m hm J support hSupport) ξ t (E.inverse.normalized t
            x))‖ ≤ ev ∧
    ‖fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k E.inverse
        t)) x -
      pressureTerm (δ*hchild) (deriv (profile δ) (k*⟪m,E.inverse.normalized t x⟫_ℝ))
        ((A.transverseData m hm J support hSupport).M.field t (E.inverse.normalized t x))
        ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))
        (canonicalVelocity (A.transverseData m hm J support hSupport) ξ t (E.inverse.normalized t
            x))‖ ≤ ep

/-- The literal strict errors returned by the global same-Q packet
theorem imply the error record without any additional analytic bound. -/
theorem homogeneousSourceErrors_of_global (ev ep : ℝ)
    (herr : ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
      ‖fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k E.inverse t) x -
        ((δ * hchild) * deriv (profile δ) (k * ⟪m, E.inverse.normalized t x⟫_ℝ)) •
          rankOne ℝ (canonicalVelocity (A.transverseData m hm J support hSupport) ξ t
              (E.inverse.normalized t x))
            ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))‖
                < ev ∧
      ‖fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k
          E.inverse t)) x -
        (EulerPacketForwardShear.pressureCoefficient (A.transverseData m hm J support hSupport) ξ
            (δ * hchild) t
            (E.inverse.normalized t x) *
 deriv (profile δ) (k * ⟪m, E.inverse.normalized t x⟫_ℝ)) •
          rankOne ℝ ((A.transverseData m hm J support hSupport).normal.field t
              (E.inverse.normalized t x))
            ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))‖
                < ep) :
    E.HomogeneousSourceErrors m hm J support hSupport B residual k δ hchild ξ ev ep := by
  intro t x
  refine ⟨(herr t x).1.le,?_⟩
  erw [forwardPressureTerm_eq_coefficient]
  exact (herr t x).2.le

include hk hδ hδ1 hhchild in
theorem exactHomogeneousPacket_low_bounds
    (ev ep CM CH Kupper : ℝ)
    (herr : E.HomogeneousSourceErrors m hm J support hSupport B residual k δ hchild ξ ev ep)
    (hsize : ∀ (s : Icc (0 : ℝ) A.T) y,
      ‖(A.transverseData m hm J support hSupport).normal.field s y‖ *
        ‖canonicalVelocity (A.transverseData m hm J support hSupport) ξ s y‖ ≤
            EulerPacketFirstLowBounds.firstRatio)
    (hflux : ∀ (s : Icc (0 : ℝ) A.T) y,
      0 ≤ ⟪(A.transverseData m hm J support hSupport).normal.field s y,
        (A.transverseData m hm J support hSupport).M.field s y
          (canonicalVelocity (A.transverseData m hm J support hSupport) ξ s y)⟫_ℝ)
    (t : Icc (0 : ℝ) A.T) (x : Space)
    (hCM : ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hupper : ∀ z, ⟪fderiv ℝ (E.force t) x z, z⟫_ℝ ≤ Kupper * ‖z‖ ^ 2) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x‖ ≤
      CM+hchild*EulerPacketFirstLowBounds.firstRatio+ev ∧
    ‖fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x‖ ≤
      CH+2*CM*(hchild*EulerPacketFirstLowBounds.firstRatio)+ep ∧
    ∀ z, ⟪fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
        E.inverse.field E.pressure (t,y))) x z,z⟫_ℝ ≤
      (Kupper+2*CM*δ*(hchild*EulerPacketFirstLowBounds.firstRatio)+ep)*‖z‖^2 := by
  let y := E.inverse.normalized t (A.ell⁻¹ • x)
  have herr' := herr t (A.ell⁻¹ • x)
  have he := E.exactPacket_derivative_split m hm J support hSupport B residual k hk t x
  have hm' : (A.transverseData m hm J support hSupport).M.field t y =
      fderiv ℝ (fun y => E.velocity (t,y)) x := E.strain_at_normalized_inverse t x
  apply good_step_bounds _ _ _ _ ((A.transverseData m hm J support hSupport).M.field t y)
    ((A.transverseData m hm J support hSupport).normal.field t y)
    (canonicalVelocity (A.transverseData m hm J support hSupport) ξ t y)
    (δ*hchild) δ (k*⟪m,y⟫_ℝ) ev ep CM CM CH (hchild*EulerPacketFirstLowBounds.firstRatio)
    (mul_nonneg hδ.le hhchild) hδ hδ1
  · have hh := mul_le_mul_of_nonneg_left (hsize t y) (mul_nonneg hδ.le hhchild)
    simpa only [mul_assoc] using hh
  · rw [hm']; exact hCM
  · exact hCM
  · exact hCH
  · rw [he.1,add_sub_cancel_left]
    exact herr'.1
  · rw [he.2,add_sub_cancel_left]
    exact herr'.2
  · exact hflux t y
  · exact hupper

end EulerParentPacketFrames.Evolution
