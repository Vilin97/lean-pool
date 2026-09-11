/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketScales
public import LeanPool.NavierStokesAndEuler.Euler.BasePacketSetup
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketGeometryFrame
import LeanPool.NavierStokesAndEuler.Euler.BaseEulerSign
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerLowBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentEulerParity
public import LeanPool.NavierStokesAndEuler.Euler.ParentStateGeometry
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildFieldMatch
public import LeanPool.NavierStokesAndEuler.Euler.BasePacketUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniversalFrequency
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardChildLowBounds
import LeanPool.NavierStokesAndEuler.Euler.ParentUniformForwardChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedState
public import LeanPool.NavierStokesAndEuler.Euler.PacketFirstLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardInitialSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPrimaryShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState

/-! The first stage of the actual induction is constructed from the
literal compact base solution and the first same-Q packet choice. -/

section

/-! One actual first-packet correction, its physical flow, labels and
source errors. The uniform scalar frequency guard constructs the record. -/

section

/-! The first packet preserves the exterior initial bound exactly and
creates the small core used by later stages. Its pressure guard comes
from the actual scalar pressure, and the exact correction adds no initial
support outside the packet ball. -/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerMeanHarmonic
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketPhysicalLowBounds EulerPacketFirstLowBounds

variable {A : Parent} (E : Evolution A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hchild : ℝ) (hhchild : 0 ≤ hchild)
  (ξ : U) (hs : tsupport EulerSpatialCutoffs.innerCutoff ⊆ support)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period A.T_pos
    (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      δ hδ ξ hs (δ * hchild) (A.sourceAgreement m hm J support hSupport H) N hN k hk))
  (G : EulerPhysicalGraphFlowBounds.Data period A.T)
  (hG : G.A =
 Q.liftedPacketCoefficient period
    (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      δ hδ ξ hs (δ * hchild) N k))
  (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- First child low bounds as an element of `LowBounds (A.child G k m hgraph nextEll hnext
hnext1)`. -/
def firstChildLowBounds (hL : H.L = 0) (hquarter : A.ell ≤ 1 / 4)
    (hSupportBall : support ⊆ Metric.closedBall 0 (1 / 2 : ℝ))
    (ev ep CM CH : ℝ)
    (herr : E.HomogeneousSourceErrors m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
          hSupport) rfl
        δ hδ ξ hs (δ * hchild) (A.sourceAgreement m hm J support hSupport H) N hN k hk)
      k δ hchild ξ ev ep)
    (hsize : ∀ (t : Icc (0 : ℝ) A.T) x,
      ‖(A.transverseData m hm J support hSupport).normal.field t x‖ *
        ‖EulerPacketForwardFactorization.canonicalVelocity
          (A.transverseData m hm J support hSupport) ξ t x‖ ≤ firstRatio)
    (hflux : ∀ (t : Icc (0 : ℝ) A.T) x,
      0 ≤ ⟪(A.transverseData m hm J support hSupport).normal.field t x,
        (A.transverseData m hm J support hSupport).M.field t x
          (EulerPacketForwardFactorization.canonicalVelocity
            (A.transverseData m hm J support hSupport) ξ t x)⟫_ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K + 2 * CM * δ * (hchild * firstRatio) + ep) * (A.T ^ 2 / 2) + CM * A.T +
      boundaryLocalizationC2 * (CM + hchild * firstRatio + ev) * A.ell ^ 3 * A.T ≤ 1 / 2) :
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

end
end

end

section

/-! The first packet over the concrete base solution produces an actual
smooth Euler state and its localized source bounds. All analytic input
comes from the same initialized correction, graph flow, and error bounds. -/

section

/-! The first packet's size and sign hypotheses are proved for the
concrete base solution on its actual restricted horizon. -/

@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Set InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseEulerGuards EulerPacketSupport EulerPacketFirstLowBounds

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

/-- First packet data, given by `(packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
firstNormal firstNormal_unit firstFrame support compact`. -/
def firstPacketData : EulerTransversePacketProvider.Data FirstPlane :=
  (packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
    firstNormal firstNormal_unit firstFrame support compact

theorem firstPacket_primary_size (t : Icc (0 : ℝ) T) (x : Space) :
    ‖(firstPacketData β hβ ell hell hell1 T hT hTB).normal.field t x‖*
      ‖EulerPacketForwardFactorization.canonicalVelocity
        (firstPacketData β hβ ell hell hell1 T hT hTB) firstCoordinate t x‖ ≤ firstRatio := by
  apply primary_size_le (firstPacketData β hβ ell hell hell1 T hT hTB)
    initialCoefficientCost initialCoefficientCost_nonneg x
    (fun s => packetBase_strain_bound β hβ ell hell hell1 T hT hTB s x)
    (packetBase_short T hTB) firstCoordinate
  · change ‖((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact).normal.field
        (packetBaseParent β hβ ell hell hell1 T hT hTB).zeroTime x‖=1
    rw [source_normal_initial]
    exact firstNormal_unit
  · change ‖((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact).frame.field
        (packetBaseParent β hβ ell hell hell1 T hT hTB).zeroTime x firstCoordinate‖=1
    rw [source_frame_initial,firstCoordinate_map]
    simp

theorem firstPacket_primary_flux (t : Icc (0 : ℝ) T) (x : Space) :
    0 ≤ ⟪(firstPacketData β hβ ell hell hell1 T hT hTB).normal.field t x,
      (firstPacketData β hβ ell hell hell1 T hT hTB).M.field t x
        (EulerPacketForwardFactorization.canonicalVelocity
          (firstPacketData β hβ ell hell hell1 T hT hTB) firstCoordinate t x)⟫_ℝ := by
  apply primary_flux_nonneg (firstPacketData β hβ ell hell hell1 T hT hTB) x firstCoordinate t
  intro hx
  exact (by norm_num : (0 : ℝ) ≤ 1/2).trans
    (firstPacket_pressure_numerator β hβ ell hell hell1 T hT hTB t x hx)

theorem packetBase_physical_strain (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (fun y => (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.velocity (t,y)) x‖
        ≤
      initialCoefficientCost := by
  rw [← (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.strain_at_normalized_inverse t x]
  exact packetBase_strain_bound β hβ ell hell hell1 T hT hTB t _

theorem packetBase_physical_force (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ ((packetBaseState β hβ ell hell hell1 T hT hTB).evolution.force t) x‖ ≤
      initialCoefficientCost := by
  let E := (packetBaseState β hβ ell hell hell1 T hT hTB).evolution
  have h := packetBase_curvature_bound β hβ ell hell hell1 T hT hTB t
    (ell⁻¹ • E.inverse.field t x)
  erw [E.curvature_eq] at h
  change ‖fderiv ℝ (E.force t)
    ((packetBaseParent β hβ ell hell hell1 T hT hTB).position t (ell • (ell⁻¹ • E.inverse.field t
        x)))‖ ≤ _ at h
  simp only [smul_smul,mul_inv_cancel₀ hell.ne',one_smul] at h
  erw [E.inverse.right_inverse] at h
  exact h

end EulerBaseDatum

end
end

end

@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketFirstLowBounds EulerMeanHarmonic

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

/-- First packet mean data, given by `(packetBaseParent β hβ ell hell hell1 T hT hTB).meanData
(packetBaseLowBounds β hβ ell hell hell1 T hT hTB)`. -/
def firstPacketMeanData : EulerMeanPacketProvider.Data :=
  (packetBaseParent β hβ ell hell hell1 T hT hTB).meanData
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)

theorem firstPacketAgreement : EulerPacketCylinderField.SourceCoefficientAgreement
    (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
    (firstPacketData β hβ ell hell hell1 T hT hTB) :=
  (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceAgreement
    firstNormal firstNormal_unit firstFrame support compact
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)

variable (δ : ℝ) (hδ : 0 < δ) (hchild : ℝ)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period hT
    (forwardInitializedCorrectionData (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate
      (subset_refl _) (δ * hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB) N hN k hk))
  (G : EulerPhysicalGraphFlowBounds.Data period T)
  (hG : G.A =
 Q.liftedPacketCoefficient period
    (forwardInitializedNormalizedField (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
          (δ * hchild) N k))
  (hgraph : ∀ t q, graphConstraint k firstNormal (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- First packet state as an element of `SmoothState ((packetBaseParent β hβ ell hell hell1 T hT
hTB).child G k firstNormal hgraph nextEll hnext hnext1)`. -/
def firstPacketState
    (labels : LabelData ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
      G k firstNormal hgraph nextEll hnext hnext1)) :
    SmoothState ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
      G k firstNormal hgraph nextEll hnext hnext1) :=
  (packetBaseState β hβ ell hell hell1 T hT hTB).forwardChild
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact symmetric
    δ hδ firstCoordinate (subset_refl _) (δ*hchild) N hN k hk Q G hG hgraph nextEll hnext hnext1
        labels

/-- First packet low bounds as an element of `LowBounds ((packetBaseParent β hβ ell hell hell1 T
hT hTB).child G k firstNormal hgraph nextEll hnext hnext1)`. -/
def firstPacketLowBounds (hquarter : ell ≤ 1 / 4) (hδ1 : δ ≤ 1) (hhchild : 0 ≤ hchild)
    (ev ep : ℝ)
    (herr : (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.HomogeneousSourceErrors
      firstNormal firstNormal_unit firstFrame support compact Q
      (forwardInitializedApproximationResidual (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
        (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
            (δ * hchild)
        (firstPacketAgreement β hβ ell hell hell1 T hT hTB) N hN k hk)
      k δ hchild firstCoordinate ev ep)
    (hsmall : (initialCoefficientCost + 2 * initialCoefficientCost * δ * (hchild * firstRatio) +
        ep) * (T ^ 2 / 2) + initialCoefficientCost * T + boundaryLocalizationC2 *
        (initialCoefficientCost + hchild * firstRatio + ev) * ell ^ 3 * T ≤ 1 / 2) :
    LowBounds ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
      G k firstNormal hgraph nextEll hnext hnext1) :=
  (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.firstChildLowBounds
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact δ hδ hδ1 hchild hhchild
    firstCoordinate (subset_refl _) N hN k hk Q G hG hgraph nextEll hnext hnext1
    rfl hquarter (subset_halfBall.trans Metric.ball_subset_closedBall)
    ev ep initialCoefficientCost initialCoefficientCost herr
    (firstPacket_primary_size β hβ ell hell hell1 T hT hTB)
    (firstPacket_primary_flux β hβ ell hell hell1 T hT hTB)
    (packetBase_physical_strain β hβ ell hell hell1 T hT hTB)
    (packetBase_physical_force β hβ ell hell hell1 T hT hTB) hsmall

end EulerBaseDatum

end
end

end

@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketSourceFrequency EulerPacketUniformSource EulerPacketPhysicalLowBounds
  EulerPacketFirstLowBounds EulerMeanHarmonic

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)
  (δ : ℝ) (hδ : 0 < δ) (hchild k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

section ConstructorInjectivity

attribute [local irreducible] Parent.child initialParent

/-- First packet choice data, collecting `hn`, `Q`, `G`, `graph`, `coefficient`, `labels` and
their compatibility conditions. -/
structure FirstPacketChoice where
  hn : 1 ≤ truncation k
  /-- Scale parameter supplied by `FirstPacketChoice`. -/
  Q : Budget period hT
    (forwardInitializedCorrectionData (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate
      (subset_refl _) (δ*hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB)
      (truncation k) hn k hk.four)
  /-- Geometric data of `FirstPacketChoice`, of type `EulerPhysicalGraphFlowBounds.Data period
  T`. -/
  G : EulerPhysicalGraphFlowBounds.Data period T
  graph : ∀ t q, graphConstraint k firstNormal (G.A.field t q)=0
  coefficient : G.A=Q.liftedPacketCoefficient period
    (forwardInitializedNormalizedField (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
      (δ*hchild) (truncation k) k)
  /-- Label type supplied by `FirstPacketChoice`. -/
  labels : LabelData ((packetBaseParent β hβ ell hell hell1 T hT hTB).child
    G k firstNormal graph nextEll hnext hnext1)
  label_constant : labels.K=k^80
  displacement_bound : ∀ (t : Icc (0 : ℝ) T) (x : Space),
    ‖(G.displacementField k firstNormal ell hell t).field x‖ ≤ k^(-(1/4 : ℝ))
  errors : (packetBaseState β hβ ell hell hell1 T hT hTB).evolution.HomogeneousSourceErrors
    firstNormal firstNormal_unit firstFrame support compact Q
    (forwardInitializedApproximationResidual (firstPacketMeanData β hβ ell hell hell1 T hT hTB)
      (firstPacketData β hβ ell hell hell1 T hT hTB) rfl δ hδ firstCoordinate (subset_refl _)
      (δ*hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB) (truncation k) hn k hk.four)
    k δ hchild firstCoordinate (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ)))

end ConstructorInjectivity

theorem exists_firstPacketChoice (hδ1 : δ ≤ 1) (hh : 0 < hchild)
    (hfrequency : EulerPacketInitializedOutputCost.uniformConstant *
      (profileEnvelope (firstParameterSize T δ
          hchild)) ^ EulerPacketInitializedOutputCost.uniformPower ≤
        smallPower k)
    (hKk : solutionLabelConstant ≤ k) (hinv : ell⁻¹ ≤ k ^ (3 / 4 : ℝ)) :
    Nonempty (FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)
        := by
  let A := packetBaseParent β hβ ell hell hell1 T hT hTB
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  let H := packetBaseLowBounds β hβ ell hell hell1 T hT hTB
  let J := firstPacketInputs β hβ ell hell hell1 T hT hTB
  have hp := firstPacket_uniform_primitives β hβ ell hell hell1 T hT hTB δ hδ hδ1 hchild hh.le
  obtain ⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,hLC⟩ := S.labels.forward_uniform_child
      S.evolution.inverse H
    firstNormal firstNormal_unit firstFrame support compact J δ hδ hδ1 firstCoordinate (subset_refl
        _)
    (δ*hchild) (mul_pos hδ hh) (profileEnvelope (firstParameterSize T δ hchild)) hp.1 hp.2.1
    k hk hfrequency hKk hinv nextEll hnext hnext1
  refine ⟨⟨hn,Q,G,hgraph,hG,LC,hLC,hdisplacement,?_⟩⟩
  intro t x
  constructor
  · erw [A.normalizedPacketVelocity_forwardInitialized H firstNormal firstNormal_unit
      firstFrame support compact δ hδ firstCoordinate (subset_refl _) (δ*hchild)
      (truncation k) hn k hk.four Q S.evolution.inverse t]
    exact (herror t x).1
  · erw [A.normalizedPacketPressure_forwardInitialized H firstNormal firstNormal_unit
      firstFrame support compact δ hδ firstCoordinate (subset_refl _) (δ*hchild)
      (truncation k) hn k hk.four Q S.evolution.inverse t]
    conv_lhs =>
      enter [1, 2]
      erw [forwardPressureTerm_eq_coefficient
        (D := A.transverseData firstNormal firstNormal_unit firstFrame support compact)
        firstCoordinate]
    exact (herror t x).2

namespace FirstPacketChoice

variable (F : FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)

/-- Parent, given by `(packetBaseParent β hβ ell hell hell1 T hT hTB).child F.G k firstNormal
F.graph nextEll hnext hnext1`. -/
def parent : Parent := (packetBaseParent β hβ ell hell hell1 T hT hTB).child
  F.G k firstNormal F.graph nextEll hnext hnext1

/-- State, constructed using `firstPacketState`. -/
def state : SmoothState F.parent :=
  firstPacketState β hβ ell hell hell1 T hT hTB δ hδ hchild (truncation k) F.hn k hk.four
    F.Q F.G F.coefficient F.graph nextEll hnext hnext1 F.labels

theorem state_label_constant : F.state.labels.K=k^80 := F.label_constant

/-- Low bounds, constructed using `firstPacketLowBounds`. -/
def lowBounds (hquarter : ell ≤ 1 / 4) (hδ1 : δ ≤ 1) (hh : 0 ≤ hchild)
    (hsmall : (initialCoefficientCost + 2 * initialCoefficientCost * δ * (hchild * firstRatio) +
        k ^ (-(1 / 4 : ℝ))) * (T ^ 2 / 2) + initialCoefficientCost * T +
        boundaryLocalizationC2 * (initialCoefficientCost + hchild * firstRatio + k ^ (-(1 /
        4 : ℝ))) * ell ^ 3 * T ≤ 1 / 2) :
    LowBounds F.parent :=
  firstPacketLowBounds β hβ ell hell hell1 T hT hTB δ hδ hchild (truncation k) F.hn k hk.four
    F.Q F.G F.coefficient F.graph nextEll hnext hnext1 hquarter hδ1 hh
    (k^(-(1 / 4 : ℝ))) (k^(-(1/4 : ℝ))) F.errors hsmall

end FirstPacketChoice
end EulerBaseDatum

end
end

end

section

/-! The first constructed packet supplies the physical low bounds and
the actual center expansion needed by the first normal stage. -/

section

/-! The physical increment between the actual packet states has exactly
the normalized packet's gradient. At the fixed center this is the same
quantity used by the source error bound and geometric renewal. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerCorrectionAssembly
open scoped ContDiff

variable {A : Parent} (S : SmoothState A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (symmetry : ParityData P (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1))

theorem packetChild_increment_fderiv (t : Icc (0 : ℝ) A.T) (x : Space) :
    fderiv ℝ (S.velocityIncrement
      (S.packetChild m hm J support hSupport B residual V hV symmetry G hG k hk hgraph
        nextEll hnext hnext1 labels) t) x =
      fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k S.evolution.inverse
          t)
        (A.ell⁻¹ • x) := by
  let F := S.packetChild m hm J support hSupport B residual V hV symmetry G hG k hk hgraph
    nextEll hnext hnext1 labels
  have hnew : DifferentiableAt ℝ (fun y => F.evolution.velocity (t,y)) x :=
    (F.evolution.velocity_smooth t).differentiable (by simp) x
  have hold : DifferentiableAt ℝ (fun y => S.evolution.velocity (t,y)) x :=
    (S.evolution.velocity_smooth t).differentiable (by simp) x
  change fderiv ℝ (fun y => F.evolution.velocity (t,y)-S.evolution.velocity (t,y)) x = _
  rw [fderiv_fun_sub hnew hold]
  have he : fderiv ℝ (fun y => F.evolution.velocity (t,y)) x =
      fderiv ℝ (fun y => S.evolution.velocity (t,y)) x +
        fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k
            S.evolution.inverse t)
          (A.ell⁻¹ • x) :=
    A.exactPacketVelocity_fderiv m hm J support hSupport B residual k S.evolution.inverse
      S.evolution.velocity t x hold
  rw [he,add_sub_cancel_left]

theorem packetChild_center_error (C : Icc (0 : ℝ) A.T → Space →L[ℝ] Space) (error : ℝ)
    (herr : ∀ t, ‖fderiv ℝ
      (A.normalizedPacketVelocity m hm J support hSupport B residual k S.evolution.inverse t) 0 - C
          t‖ ≤ error)
    (t : Icc (0 : ℝ) A.T) :
    ‖fderiv ℝ (S.velocityIncrement
      (S.packetChild m hm J support hSupport B residual V hV symmetry G hG k hk hgraph
        nextEll hnext hnext1 labels) t) 0-C t‖ ≤ error := by
  rw [S.packetChild_increment_fderiv m hm J support hSupport B residual V hV symmetry G hG k hk
      hgraph
    nextEll hnext hnext1 labels t 0,smul_zero]
  exact herr t

end EulerParentPacketFrames.SmoothState

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketProfileRecursion EulerSpatialCutoffs

variable {A : Parent} (S : SmoothState A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (hSym : ∀ x, -x ∈ support ↔ x ∈ support)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ support) (α : ℝ)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)

/-- Transfer the center error before specializing the parent to its concrete flow. -/
private theorem forwardChild_center_error
    (Q : Budget period A.T_pos
      (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk))
    (G : EulerPhysicalGraphFlowBounds.Data period A.T)
    (hG : G.A =
 Q.liftedPacketCoefficient period
      (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl δ hδ ξ hs α N k))
    (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
    (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1))
    (C : Icc (0 : ℝ) A.T → Space →L[ℝ] Space) (error : ℝ)
    (herr : ∀ t, ‖fderiv ℝ
      (A.normalizedPacketVelocity m hm J support hSupport Q
        (forwardInitializedApproximationResidual (A.meanData H)
          (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs α
          (A.sourceAgreement m hm J support hSupport H) N hN k hk)
        k S.evolution.inverse t) 0 -
 C t‖ ≤ error)
    (t : Icc (0 : ℝ) A.T) :
    ‖fderiv ℝ (S.velocityIncrement
      (S.forwardChild H m hm J support hSupport hSym δ hδ ξ hs α N hN k hk
        Q G hG hgraph nextEll hnext hnext1 labels) t) 0 -
 C t‖ ≤ error := by
  exact S.packetChild_center_error m hm J support hSupport Q
    (forwardInitializedApproximationResidual (A.meanData H)
      (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk)
    (forwardInitializedNormalizedField (A.meanData H)
      (A.transverseData m hm J support hSupport) rfl δ hδ ξ hs α N k) rfl
    (S.odd.forwardCorrectionParity H m hm J support hSupport hSym δ hδ ξ hs α N hN k hk)
    G hG k (mul_inv_cancel₀ (by linarith : k ≠ 0)) hgraph nextEll hnext hnext1 labels C error herr t

end EulerParentPacketFrames.SmoothState

namespace EulerBaseDatum.FirstPacketChoice

-- Keep type unification from expanding the concrete initial flow.
attribute [local irreducible] initialParent

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerParentPacketFrames
  EulerPacketSupport EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketFirstLowBounds EulerPacketPhysicalLowBounds EulerPacketSourceGeometry
  EulerPacketForwardFactorization EulerPeriodicProfile EulerTransverseFrameCoordinates

variable {β : ℝ} {hβ : |β| ≤ 1} {ell : ℝ} {hell : 0 < ell} {hell1 : ell ≤ 1}
  {T : ℝ} {hT : 0 < T} {hTB : T ≤ initialTime}
  {δ : ℝ} {hδ : 0 < δ} {hchild k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)

theorem physical_bounds (hδ1 : δ ≤ 1) (hh : 0 ≤ hchild)
    (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (fun y => F.state.evolution.velocity (t,y)) x‖ ≤
      initialCoefficientCost+hchild*firstRatio+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ (F.state.evolution.force t) x‖ ≤
      initialCoefficientCost+2*initialCoefficientCost*(hchild*firstRatio)+k^(-(1/4 : ℝ)) := by
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  let M := firstPacketMeanData β hβ ell hell hell1 T hT hTB
  let D := firstPacketData β hβ ell hell hell1 T hT hTB
  let res := forwardInitializedApproximationResidual M D rfl δ hδ firstCoordinate (subset_refl _)
    (δ*hchild) (firstPacketAgreement β hβ ell hell hell1 T hT hTB) (truncation k) F.hn k hk.four
  have h := S.evolution.exactHomogeneousPacket_low_bounds
    firstNormal firstNormal_unit firstFrame support compact F.Q res k (mul_inv_cancel₀ hk.pos.ne')
    δ hchild firstCoordinate hδ hδ1 hh
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) initialCoefficientCost initialCoefficientCost
        initialCoefficientCost
    F.errors (firstPacket_primary_size β hβ ell hell hell1 T hT hTB)
    (firstPacket_primary_flux β hβ ell hell hell1 T hT hTB) t x
    (packetBase_physical_strain β hβ ell hell hell1 T hT hTB t x)
    (packetBase_physical_force β hβ ell hell hell1 T hT hTB t x)
    (S.evolution.force_quadratic_upper_of_lowBounds (packetBaseLowBounds β hβ ell hell hell1 T hT
        hTB) t x)
  dsimp only [S, M, D, res, firstPacketMeanData, firstPacketData] at h
  constructor
  · dsimp only [state, firstPacketState, SmoothState.forwardChild,
      SmoothState.packetChild, Evolution.child]
    with_reducible exact h.1
  · refine (congrArg (fun M : Space →L[ℝ] Space => ‖M‖)
      (F.state.evolution.pressure_hessian_eq_force t x).symm).trans_le ?_
    dsimp only [state, firstPacketState, SmoothState.forwardChild,
      SmoothState.packetChild, Evolution.child]
    with_reducible exact h.2.1

theorem center_error (t : Icc (0 : ℝ) T) :
    ‖fderiv ℝ ((packetBaseState β hβ ell hell hell1 T hT hTB).velocityIncrement F.state t) 0 -
      ((δ*hchild)*deriv (profile δ)
        (k*⟪firstNormal,(packetBaseState β hβ ell hell hell1 T hT hTB).evolution.inverse.normalized
            t 0⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity (firstPacketData β hβ ell hell hell1 T hT hTB) firstCoordinate
            t
          ((packetBaseState β hβ ell hell hell1 T hT hTB).evolution.inverse.normalized t 0))
          ((firstPacketData β hβ ell hell hell1 T hT hTB).normal.field t
            ((packetBaseState β hβ ell hell hell1 T hT hTB).evolution.inverse.normalized t 0))‖ ≤
                k^(-(1/4 : ℝ)) := by
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  let H := packetBaseLowBounds β hβ ell hell hell1 T hT hTB
  let D := firstPacketData β hβ ell hell hell1 T hT hTB
  let C (s : Icc (0 : ℝ) T) : Space →L[ℝ] Space := shearTerm (δ*hchild)
    (deriv (profile δ) (k*⟪firstNormal,S.evolution.inverse.normalized s 0⟫_ℝ))
    (D.normal.field s (S.evolution.inverse.normalized s 0))
    (canonicalVelocity D firstCoordinate s (S.evolution.inverse.normalized s 0))
  dsimp only [state, firstPacketState]
  exact S.forwardChild_center_error H
    firstNormal firstNormal_unit firstFrame support compact symmetric δ hδ firstCoordinate
    (subset_refl _) (δ*hchild) (truncation k) F.hn k hk.four F.Q F.G F.coefficient F.graph
    nextEll hnext hnext1 F.labels C (k^(-(1/4 : ℝ))) (fun s => (F.errors s 0).1) t

end EulerBaseDatum.FirstPacketChoice

end
end

end

section

/-! Exact initial frame parameters for the first normal stage: its
coupling is one, tilt is beta, and shear is the prescribed first shear. -/

@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerParentPacketFrames
  EulerPacketSupport EulerBaseEulerGuards EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerPacketSourceGeometry EulerVolterraConvolution

theorem first_basis_cross : cross firstNormal (EuclideanSpace.single 1 1)=EuclideanSpace.single 2 1
    := by
  ext i
  fin_cases i <;> simp [cross,firstNormal,cross_apply]

theorem first_normalizedCoupling (β : ℝ) :
    normalizedCoupling (linear β) firstNormal (EuclideanSpace.single 1 1)=1 := by
  simp [normalizedCoupling,unit,firstNormal,EuclideanSpace.inner_single_left,
    PiLp.add_apply,PiLp.smul_apply]

theorem first_normalizedTilt (β : ℝ) :
    normalizedTilt (linear β) firstNormal (EuclideanSpace.single 1 1)=β := by
  rw [normalizedTilt,first_normalizedCoupling]
  have hp : unit firstNormal=firstNormal := by rw [unit,firstNormal_unit,inv_one,one_smul]
  have hq : unit (EuclideanSpace.single 1 1 : Space)=EuclideanSpace.single 1 1 := by simp [unit]
  rw [hp,hq,first_basis_cross,linear_q]
  simp [EuclideanSpace.inner_single_left,PiLp.add_apply,PiLp.smul_apply]

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

theorem packetBase_centerStrain_initial :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).centerStrain 0=linear β := by
  let A := packetBaseParent β hβ ell hell hell1 T hT hTB
  let S := packetBaseState β hβ ell hell hell1 T hT hTB
  change A.centerStrain 0=linear β
  have h0 : (0 : Space) ∈ support := subset_tsupport _ (by
    simp [Function.mem_support,EulerSpatialCutoffs.innerCutoff_zero])
  calc
    _ = A.strain.field A.zeroTime 0 := by
      change A.strain.field (projIcc 0 A.T A.T_pos.le 0) 0=A.strain.field A.zeroTime 0
      rw [projIcc_of_mem A.T_pos.le (show (0 : ℝ) ∈ Icc 0 A.T from ⟨le_rfl,A.T_pos.le⟩)]
      rfl
    _ = A.initialStrain.field 0 := by
      rw [S.evolution.strain_origin S.odd,S.evolution.initialStrain_eq,smul_zero]
      rfl
    _ = linear β := packetBase_initialStrain β hβ ell hell hell1 T hT hTB 0 h0

theorem packetBase_sourceNormal_initial :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceNormal firstNormal 0=firstNormal := by
  let A := packetBaseParent β hβ ell hell hell1 T hT hTB
  calc
    _ = (A.transverseData firstNormal firstNormal_unit firstFrame support compact).normal.field
        A.zeroTime 0 := (A.source_normal_eq firstNormal firstNormal_unit firstFrame support compact
            A.zeroTime).symm
    _ = _ := source_normal_initial firstNormal firstNormal_unit firstFrame support compact 0

theorem packetBase_sourceVelocity_initial :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceVelocity
      firstNormal firstNormal_unit firstFrame support compact firstCoordinate
          0=EuclideanSpace.single 1 1 := by
  change EulerPacketForwardFactorization.uncutVelocity
    ((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact) firstCoordinate 0 0=_
  rw [EulerPacketForwardFactorization.uncutVelocity_initial]
  exact (source_frame_initial (G := packetBaseParent β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact firstCoordinate 0).trans
        firstCoordinate_map

theorem first_frame_parameters {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    {D : EulerTransversePacketProvider.Data U} (P : ParentFrame D 0) (hchild : ℝ)
    (hB : P.B 0 = (packetBaseParent β hβ ell hell hell1 T hT hTB).centerStrain 0)
    (hm : P.m 0 = (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceNormal firstNormal 0)
    (hv : P.v 0 =
 (packetBaseParent β hβ ell hell hell1 T hT hTB).sourceVelocity
      firstNormal firstNormal_unit firstFrame support compact firstCoordinate 0)
    (hc : P.c = hchild) : P.a=1 ∧ P.sigma=Real.sqrt β ∧ P.shear=hchild := by
  have hB' := hB.trans (packetBase_centerStrain_initial β hβ ell hell hell1 T hT hTB)
  have hm' := hm.trans (packetBase_sourceNormal_initial β hβ ell hell hell1 T hT hTB)
  have hv' := hv.trans (packetBase_sourceVelocity_initial β hβ ell hell hell1 T hT hTB)
  refine ⟨?_,?_,?_⟩
  · rw [ParentFrame.a,hB',hm',hv',first_normalizedCoupling]
  · rw [ParentFrame.sigma,hB',hm',hv',first_normalizedTilt]
  · rw [ParentFrame.shear,primaryShear,hc,hm',hv',firstNormal_unit]
    simp

end EulerBaseDatum

end
end

end

section

/-! The literal base scale constructs the first actual smooth Euler
packet state and its localized source bounds. -/

@[expose] public section

noncomputable section

namespace EulerBaseDatum.FirstScaleGuards

open Real EulerParentPacketFrames EulerPacketBaseGuardScales EulerPacketSourceScaleSequence
  EulerPacketSourceScaleChoice EulerPacketFirstLowBounds

variable {J D : ℕ} {X : ℝ} (H : FirstScaleGuards J D X)

include H

theorem x_pos : 0 < X := zero_lt_one.trans_le H.x_one

theorem tilt_bound : |X^(-2 : ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (rpow_nonneg H.x_pos.le _)]
  exact rpow_le_one_of_one_le_of_nonpos H.x_one (by norm_num)

theorem core_pos : 0 < baseRadius X := baseRadius_pos H.x_pos

theorem core_one : baseRadius X ≤ 1 := H.radius_small.trans (by norm_num)

theorem time_pos (hJ : 1 ≤ J) : 0 < baseHorizon J X := baseHorizon_pos J hJ H.x_pos

theorem spike_pos : 0 < X^(-1010 : ℝ) := rpow_pos_of_pos H.x_pos _

theorem spike_one : X^(-1010 : ℝ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos H.x_one (by norm_num)

theorem shear_pos : 0 < X^1000 := pow_pos H.x_pos _

omit H in
theorem nextRadius_pos : 0 < supportScale J X 0 := exp_pos _

theorem nextRadius_one : supportScale J X 0 ≤ 1 := by
  unfold supportScale
  apply exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr H.x_pos.le)
    (rpow_nonneg (Nat.cast_nonneg _) _)

/-- Packet, constructed using `Classical.choice`. -/
def packet (hJ : 1 ≤ J) :
    FirstPacketChoice (X^(-2 : ℝ)) H.tilt_bound (baseRadius X) H.core_pos H.core_one
      (baseHorizon J X) (H.time_pos hJ) H.local_time
      (X^(-1010 : ℝ)) H.spike_pos (X^1000) (X^D) H.frequency
      (supportScale J X 0) nextRadius_pos H.nextRadius_one :=
  Classical.choice (exists_firstPacketChoice (X^(-2 : ℝ)) H.tilt_bound
    (baseRadius X) H.core_pos H.core_one (baseHorizon J X) (H.time_pos hJ) H.local_time
    (X^(-1010 : ℝ)) H.spike_pos (X^1000) (X^D) H.frequency
    (supportScale J X 0) nextRadius_pos H.nextRadius_one H.spike_one H.shear_pos
    H.source_frequency H.label_frequency H.radius_frequency)

/-- Parent, given by `(H.packet hJ).parent`. -/
def parent (hJ : 1 ≤ J) : Parent := (H.packet hJ).parent

/-- State, given by `(H.packet hJ).state`. -/
def state (hJ : 1 ≤ J) : SmoothState (H.parent hJ) := (H.packet hJ).state

theorem state_label (hJ : 1 ≤ J) : (H.state hJ).labels.K=(X^D)^80 :=
  (H.packet hJ).state_label_constant

theorem parent_time (hJ : 1 ≤ J) : (H.parent hJ).T=baseHorizon J X := rfl

theorem parent_scale (hJ : 1 ≤ J) : (H.parent hJ).ell=supportScale J X 0 := rfl

/-- Low bounds, constructed using `FirstPacketChoice.lowBounds`. -/
def lowBounds (hJ : 1 ≤ J) : LowBounds (H.parent hJ) :=
  FirstPacketChoice.lowBounds (X^(-2 : ℝ)) H.tilt_bound (baseRadius X) H.core_pos H.core_one
    (baseHorizon J X) (H.time_pos hJ) H.local_time
    (X^(-1010 : ℝ)) H.spike_pos (X^1000) (X^D) H.frequency
    (supportScale J X 0) nextRadius_pos H.nextRadius_one (H.packet hJ)
    H.radius_small H.spike_one H.shear_pos.le (by
    simpa only [literalInitialPressureCost,literalInitialError,← add_assoc] using H.localized)

theorem lowBounds_values (hJ : 1 ≤ J) :
    (H.lowBounds hJ).Be=initialCoefficientCost ∧
    (H.lowBounds hJ).Bc=initialCoefficientCost+X^1000*firstRatio+literalInitialError D X ∧
    (H.lowBounds hJ).r=baseRadius X ∧
    (H.lowBounds hJ).K=initialCoefficientCost+literalInitialPressureCost D X := by
  refine ⟨rfl,rfl,rfl,?_⟩
  change initialCoefficientCost+2*initialCoefficientCost*X^(-1010 : ℝ)*(X^1000*firstRatio) +
    (X^D)^(-(1/4 : ℝ))=initialCoefficientCost+literalInitialPressureCost D X
  unfold literalInitialPressureCost literalInitialError
  ring

end EulerBaseDatum.FirstScaleGuards

end
end

end

section

/-! The first actual packet has the precise initial frame parameters
a=1, sigma=sqrt(beta), and the prescribed polynomial shear. -/

@[expose] public section

noncomputable section

namespace EulerBaseDatum.FirstPacketChoice

open Set InnerProductSpace EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerPacketSourceFrequency EulerPacketSourceGeometry EulerTransverseFrameCoordinates

variable {β : ℝ} {hβ : |β| ≤ 1} {ell : ℝ} {hell : 0 < ell} {hell1 : ell ≤ 1}
  {T : ℝ} {hT : 0 < T} {hTB : T ≤ initialTime}
  {δ : ℝ} {hδ : 0 < δ} {hchild k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : FirstPacketChoice β hβ ell hell hell1 T hT hTB δ hδ hchild k hk nextEll hnext hnext1)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)

/-- Initial frame as an element of `ParentFrame (F.parent.transverseData m hm R S hS) 0`. -/
def initialFrame : ParentFrame (F.parent.transverseData m hm R S hS) 0 := by
  let B := packetBaseState β hβ ell hell hell1 T hT hTB
  have h0 := initialCoefficientCost_nonneg
  exact B.forwardRenewal F.state rfl firstNormal firstNormal_unit firstFrame support compact
    m hm R S hS 0 le_rfl initialCoefficientCost initialCoefficientCost (1+initialCoefficientCost)
    (k^(-(1/4 : ℝ))) h0 (le_add_of_nonneg_right h0) (Real.rpow_nonneg hk.pos.le _)
    (le_add_of_nonneg_left zero_le_one) (by linarith only [h0])
    (fun t _ => packetBase_strain_bound β hβ ell hell hell1 T hT hTB (projIcc 0 T hT.le t) 0)
    (fun t _ => packetBase_curvature_bound β hβ ell hell hell1 T hT hTB (projIcc 0 T hT.le t) 0)
    δ hδ (δ*hchild) k firstCoordinate
    (by intro h; have he := firstCoordinate_norm; rw [h,norm_zero] at he; norm_num at he)
    (fun t _ => F.center_error t)

theorem initialFrame_parameters :
    (F.initialFrame m hm R S hS).a=1 ∧
    (F.initialFrame m hm R S hS).sigma=Real.sqrt β ∧
    (F.initialFrame m hm R S hS).shear=hchild := by
  apply first_frame_parameters β hβ ell hell hell1 T hT hTB (F.initialFrame m hm R S hS) hchild
  · rfl
  · rfl
  · rfl
  · change (δ*hchild)/δ=hchild
    field_simp

theorem initialFrame_costs :
    (F.initialFrame m hm R S hS).G=1+initialCoefficientCost ∧
    (F.initialFrame m hm R S hS).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩

end EulerBaseDatum.FirstPacketChoice

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInductionScales.Scales

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketSupport EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketLowConstants EulerPacketInduction EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketBaseGuardScales
  EulerParentRenewalScale EulerMeanHarmonic

-- Limit elaboration of the concrete flow only within this namespace scope.
attribute [local irreducible] initialParent

variable {c B : ℝ} (S : Scales c B)

/-- First stage as an element of `Stage S 0`. -/
def firstStage : Stage S 0 := by
  let F := S.first.packet S.j_one
  let P := F.initialFrame firstNormal firstNormal_unit firstFrame support compact
  have hparam := F.initialFrame_parameters firstNormal firstNormal_unit firstFrame support compact
  have hcost := F.initialFrame_costs firstNormal firstNormal_unit firstFrame support compact
  have hlow := S.first.lowBounds_values S.j_one
  have hbounds := initial_bounds (S.X^1000) (literalInitialError S.D S.X)
    (one_le_pow₀ S.x_one) S.first.error_small
  have htilt : P.sigma^2*S.X^2=1 := by
    rw [show P.sigma=sqrt (S.X^(-2 : ℝ)) from hparam.2.1,
      sq_sqrt (rpow_nonneg S.x_pos.le _),rpow_neg S.x_pos.le]
    norm_num only [rpow_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero _ S.x_pos.ne')
  refine {
    parent := S.first.parent S.j_one
    state := S.first.state S.j_one
    low := S.first.lowBounds S.j_one
    time := 0
    time_nonneg := le_rfl
    time_zero := fun _ => rfl
    time_lower := fun h => (h rfl).elim
    horizon_eq := ?_
    horizon_le := le_rfl
    scale_eq := rfl
    label_eq := S.first.state_label S.j_one
    gradient_bound := ?_
    hessian_bound := ?_
    exterior_bound := ?_
    core_bound := ?_
    pressure_bound := ?_
    boundary_eq := rfl
    radius_eq := hlow.2.2.1
    frame := P
    frame_shear := hparam.2.2
    frame_bound := ?_
    frame_error := ?_
    coupling_error := ?_
    tilt_lower := ?_
    tilt_upper := ?_
    compression := fun h => (h rfl).elim }
  · change baseHorizon S.J S.X=0+2*timeWidth S.J S.X 0
    rw [zero_add,baseHorizon_eq_timeWidth S.J S.x_pos]
  · intro t x
    have h := (F.physical_bounds S.first.spike_one S.first.shear_pos.le t x).1
    dsimp only [FirstScaleGuards.state, previousShear]
    exact h.trans hbounds.1
  · intro t x
    have h := (F.physical_bounds S.first.spike_one S.first.shear_pos.le t x).2
    dsimp only [FirstScaleGuards.state, previousShear, olderShear]
    simpa only [mul_one] using h.trans hbounds.2
  · rw [hlow.1]
    simp only [sum_range_zero,add_zero,le_refl]
  · rw [hlow.2.1]
    simpa only [sum_range_zero,add_zero] using hbounds.1
  · rw [hlow.2.2.2]
    simp only [sum_range_zero,add_zero,le_refl]
  · change P.G ≤ frameConstant*(1+1)
    rw [show P.G=1+initialCoefficientCost from hcost.1]
    have hf := EulerPacketFirstLowBounds.firstRatio_pos
    have hm := gradient_properties.2.1
    have hc := frame_properties.2.1
    have h0 := frame_properties.1
    linarith only [hf,hm,hc,h0]
  · exact le_of_eq hcost.2
  · change |P.a-1| ≤ 2*∑ i ∈ range 0, renewalCost S.J S.D 4 c frameConstant S.X i
    rw [show P.a=1 from hparam.1]
    simp only [sub_self,abs_zero,sum_range_zero,mul_zero,le_refl]
  · change 1/2 ≤ P.sigma^2*S.X^2
    rw [htilt]
    norm_num
  · change P.sigma^2*S.X^2 ≤ 2
    rw [htilt]
    norm_num

theorem firstStage_time : S.firstStage.time=0 := rfl

theorem firstStage_horizon : S.firstStage.parent.T=baseHorizon S.J S.X := rfl

theorem firstStage_coupling : S.firstStage.frame.a=1 :=
  ((S.first.packet S.j_one).initialFrame_parameters firstNormal firstNormal_unit firstFrame
    support compact).1

end EulerPacketInductionScales.Scales
