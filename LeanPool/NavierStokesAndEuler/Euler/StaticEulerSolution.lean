/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerCorrection
public import LeanPool.NavierStokesAndEuler.Euler.ConstantEulerGraph
public import LeanPool.NavierStokesAndEuler.Euler.EulerTimeRescaling
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds

/-! A positive-time classical Euler solution constructed from a genuine
solenoidal Gevrey datum. The initial velocity is the original datum, not
its small multiple. All spatial derivative tensors remain continuous L²
paths after the actual Euler time/amplitude rescaling. -/

@[expose] public section


noncomputable section

namespace EulerStaticEuler

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerVolterraConvolution EulerSobolevPointEvaluation EulerLagrangian
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)

/-- Local velocity, given by `EulerTimeRescaling.velocity (amplitude P C R hC hR)
(EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv))`. -/
def localVelocity : ℝ × Space → Space :=
  EulerTimeRescaling.velocity (amplitude P C R hC hR)
    (EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv))

/-- Local pressure, given by `EulerTimeRescaling.pressure (amplitude P C R hC hR)
(EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv))`. -/
def localPressure : ℝ × Space → ℝ :=
  EulerTimeRescaling.pressure (amplitude P C R hC hR)
    (EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv))

/-- Local force as an element of `Space`. -/
def localForce (q : ℝ × Space) : Space :=
  ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q)

theorem unit_initial (x : Space) :
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (0,x) =
      amplitude P C R hC hR • u.field x := by
  have hh := congrArg (pointEvaluation P (x,(0 : AddCircle P)))
    (exactPacket_initial P u C R hC hR hu hdiv 3)
  change (exactPacket P u C R hC hR hu hdiv).velocity.pointField
      ⟨0,le_rfl,by norm_num⟩ (x,0) =
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)).toFieldTower.pointField
      ⟨0,le_rfl,by norm_num⟩ (x,0) at hh
  have hr := ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC
      hR)).toFieldTower_pointField_raw
    ⟨0,le_rfl,by norm_num⟩ x 0
  change _ = amplitude P C R hC hR • u.field x at hr
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl,by norm_num⟩
  simpa only [EulerConstantEuler.velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,
    projIcc_of_mem zero_le_one h0,coveringMap,AddCircle.coe_zero] using hh.trans hr

theorem localVelocity_initial (x : Space) : localVelocity P u C R hC hR hu hdiv (0,x)=u.field x :=
    by
  change (amplitude P C R hC hR)⁻¹ •
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) (0,x)) = _
  rw [EulerTimeRescaling.coordinates_apply,mul_zero,unit_initial,smul_smul,
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne',one_smul]

theorem localMomentum (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    momentumResidual (localVelocity P u C R hC hR hu hdiv)
      (localPressure P u C R hC hR hu hdiv) (t,x)=0 := by
  have hs := EulerTimeRescaling.scaled_time_interior (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) t ht
  exact EulerTimeRescaling.momentumResidual_zero (amplitude P C R hC hR) _ _ (t,x)
    (EulerConstantEuler.velocity_hasFDerivAt (exactPacket P u C R hC hR hu hdiv) _ hs
        x).differentiableAt
    ((EulerConstantEuler.pressure_smooth (exactPacket P u C R hC hR hu hdiv) _).differentiable (by
        simp) x)
    (EulerConstantEuler.momentum (exactPacket P u C R hC hR hu hdiv) _ hs x)

theorem localVelocity_differentiableAt (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    DifferentiableAt ℝ (localVelocity P u C R hC hR hu hdiv) (t,x) := by
  have hs := EulerTimeRescaling.scaled_time_interior (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) t ht
  exact (EulerTimeRescaling.velocity_hasFDerivAt (amplitude P C R hC hR) _ (t,x)
    (EulerConstantEuler.velocity_hasFDerivAt (exactPacket P u C R hC hR hu hdiv) _ hs
        x).differentiableAt).differentiableAt

theorem localVelocity_divergence (t : ℝ) (x : Space) :
    divergence (fun y => localVelocity P u C R hC hR hu hdiv (t,y)) x=0 := by
  rw [divergence_eq_coordinate_sum]
  have hd := EulerTimeRescaling.spatial_derivative (amplitude P C R hC hR)
    (EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)) t x
    ((EulerConstantEuler.velocity_smooth (exactPacket P u C R hC hR hu hdiv) _).differentiable (by
        simp) x)
  change (∑ i : Fin 3, (fderiv ℝ (fun y => EulerTimeRescaling.velocity (amplitude P C R hC hR)
    (EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)) (t,y)) x
      (EuclideanSpace.single i 1)) i)=0
  rw [hd]
  simp only [smul_apply,PiLp.smul_apply,smul_eq_mul,← Finset.mul_sum,
    ← divergence_eq_coordinate_sum]
  erw [EulerConstantEuler.velocity_divergence,mul_zero]

theorem localVelocity_joint_continuous : Continuous (localVelocity P u C R hC hR hu hdiv) := by
  change Continuous (fun q => (amplitude P C R hC hR)⁻¹ •
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q))
  exact ((EulerConstantEuler.velocity_joint_continuous (exactPacket P u C R hC hR hu hdiv)).comp
    (EulerTimeRescaling.coordinates (E := Space) (amplitude P C R hC hR)).continuous).const_smul
      ((amplitude P C R hC hR)⁻¹)

theorem localPressure_joint_continuous : Continuous (localPressure P u C R hC hR hu hdiv) := by
  change Continuous (fun q => ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q))
  exact ((EulerConstantEuler.pressure_joint_continuous (exactPacket P u C R hC hR hu hdiv)).comp
    (EulerTimeRescaling.coordinates (E := Space) (amplitude P C R hC hR)).continuous).const_smul
      (((amplitude P C R hC hR)⁻¹)^2)

theorem localForce_joint_continuous : Continuous (localForce P u C R hC hR hu hdiv) := by
  change Continuous (fun q => ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q))
  exact ((EulerConstantEuler.force_joint_continuous (exactPacket P u C R hC hR hu hdiv)).comp
    (EulerTimeRescaling.coordinates (E := Space) (amplitude P C R hC hR)).continuous).const_smul
      (((amplitude P C R hC hR)⁻¹)^2)

theorem localPressure_gradient (t : ℝ) (x : Space) :
    _root_.gradient (fun y => localPressure P u C R hC hR hu hdiv (t,y)) x =
      localForce P u C R hC hR hu hdiv (t,x) := by
  have h := EulerTimeRescaling.pressure_gradient (amplitude P C R hC hR)
    (EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv)) (t,x)
    ((EulerConstantEuler.pressure_smooth (exactPacket P u C R hC hR hu hdiv) _).differentiable (by
        simp) x)
  erw [EulerConstantEuler.pressure_gradient] at h
  exact h

theorem localPressure_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun x => localPressure P u C R hC hR hu hdiv (t,x)) := by
  change ContDiff ℝ ∞ (fun x => ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*t,x))
  exact (EulerConstantEuler.pressure_smooth (exactPacket P u C R hC hR hu hdiv) _).const_smul _

theorem localPressure_zero (t : ℝ) : localPressure P u C R hC hR hu hdiv (t,0)=0 := by
  change ((amplitude P C R hC hR)⁻¹)^2 *
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) (_,0)=0
  erw [EulerConstantEuler.pressure_zero,mul_zero]

/-- Local field, constructed using `SmoothL2Field.mapField`. -/
def localField (t : Icc (0 : ℝ) (amplitude P C R hC hR)) : SmoothL2Field Space :=
  SmoothL2Field.mapField ((amplitude P C R hC hR)⁻¹ • ContinuousLinearMap.id ℝ Space)
    (EulerConstantEuler.field (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t))

theorem localField_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (localField P u C R hC hR hu hdiv t).field x=localVelocity P u C R hC hR hu hdiv (t,x) := by
  change (amplitude P C R hC hR)⁻¹ •
    (EulerConstantEuler.field (exactPacket P u C R hC hR hu hdiv) _).field x = _
  erw [EulerConstantEuler.field_apply]
  change (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((t : ℝ)/amplitude P C R hC hR,x) =
    (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t : ℝ),x)
  rw [div_eq_mul_inv,mul_comm (t : ℝ)]

theorem localField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (localField P u C R hC hR hu hdiv t).jetLp n) :=
  SmoothL2Field.continuous_jetLp_mapField _ _
    (fun n => (EulerConstantEuler.field_jetLp_continuous (exactPacket P u C R hC hR hu hdiv) n).comp
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR)).continuous) n

theorem localVelocity_smooth (t : Icc (0 : ℝ) (amplitude P C R hC hR)) :
    ContDiff ℝ ∞ (fun x => localVelocity P u C R hC hR hu hdiv (t,x)) := by
  have he : (localField P u C R hC hR hu hdiv t).field =
      fun x => localVelocity P u C R hC hR hu hdiv (t,x) :=
    funext (localField_apply P u C R hC hR hu hdiv t)
  rw [← he]
  exact (localField P u C R hC hR hu hdiv t).smooth

end EulerStaticEuler
