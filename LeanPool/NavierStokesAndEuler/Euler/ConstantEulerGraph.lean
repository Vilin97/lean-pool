/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ConstantCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalContinuity
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField

@[expose] public section

/-! With spatial scale one and angular direction zero, the zero-angle
slice of the actual exact lifted solution solves ordinary three-dimensional
Euler. The scalar pressure is the canonical normalized graph potential. -/

noncomputable section

namespace EulerConstantEuler

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerConstantCorrection EulerMetricTransport EulerGraphPressurePotential
  EulerVolterraConvolution EulerLagrangian EulerLpTranslation
open scoped ContDiff

private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance
private local instance : NormedAddCommGroup LiftTangent := inferInstance
private local instance : NormedSpace ℝ LiftTangent := inferInstance

def inclusion : (ℝ × Space) →L[ℝ] (ℝ × LiftTangent) :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.inl ℝ Space ℝ)

@[simp] theorem inclusion_apply (t : ℝ) (x : Space) : inclusion (t,x)=(t,(x,0)) := rfl

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 < T} {F R : FieldTower P T}
  {B : Budget P hT (data P F R)} (S : ExactLiftedPacket P hT (data P F R) B)

def velocity (q : ℝ × Space) : Space := S.rawVelocity (q.1,(q.2,0))
def pressure (q : ℝ × Space) : ℝ := S.rawGraphPotential 1 q
def force (q : ℝ × Space) : Space := S.rawPressure (q.1,(q.2,0))

theorem velocity_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    HasFDerivAt (velocity S)
      ((fderiv ℝ S.rawVelocity (t,(x,0))).comp inclusion) (t,x) := by
  have hu := (S.rawVelocity_hasFDerivAt t ht (x,0)).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (inclusion : ℝ × Space → ℝ × LiftTangent) inclusion (t,x) :=
    inclusion.hasFDerivAt
  exact hu.comp (t,x) hi

theorem velocity_joint_continuous : Continuous (velocity S) := by
  have hc : Continuous (projIcc 0 T hT.le) := continuous_projIcc
  change Continuous (fun q : ℝ × Space => S.velocity.pointField
    (projIcc 0 T hT.le q.1) (coveringMap P (q.2,0)))
  exact S.velocity.pointField_joint_continuous.comp
    ((hc.comp continuous_fst).prodMk
      ((EulerLiftedGradientSpace.coveringMap_isOpenQuotient P).continuous.comp
        (continuous_snd.prodMk continuous_const)))

theorem force_joint_continuous : Continuous (force S) := by
  have hc : Continuous (projIcc 0 T hT.le) := continuous_projIcc
  change Continuous (fun q : ℝ × Space => S.pressure.pointField
    (projIcc 0 T hT.le q.1) (coveringMap P (q.2,0)))
  exact S.pressure.pointField_joint_continuous.comp
    ((hc.comp continuous_fst).prodMk
      ((EulerLiftedGradientSpace.coveringMap_isOpenQuotient P).continuous.comp
        (continuous_snd.prodMk continuous_const)))

theorem pressure_joint_continuous : Continuous (pressure S) := by
  have hc : Continuous (projIcc 0 T hT.le) := continuous_projIcc
  change Continuous (fun q : ℝ × Space => S.graphPotential 1 (projIcc 0 T hT.le q.1) q.2)
  have hi : Continuous (fun q : ℝ × Space => (projIcc 0 T hT.le q.1,q.2)) :=
    (hc.comp continuous_fst).prodMk continuous_snd
  have hh := (S.graphPotential_joint_continuous 1).comp hi
  exact hh

theorem pressure_smooth (t : ℝ) : ContDiff ℝ ∞ (fun x => pressure S (t,x)) :=
  S.rawGraphPotential_smooth 1 (by norm_num [data]) t

theorem pressure_gradient (t : ℝ) (x : Space) :
    _root_.gradient (fun y => pressure S (t,y)) x=force S (t,x) := by
  have h := S.rawGraphPotential_gradient 1 (by norm_num [data]) t x
  simpa only [data,pressure,force,one_smul,inner_zero_left,mul_zero] using h

theorem pressure_zero (t : ℝ) : pressure S (t,0)=0 :=
  S.graphPotential_zero 1 (projIcc 0 T hT.le t)

theorem velocity_divergence (t : ℝ) (x : Space) :
    divergence (fun y => velocity S (t,y)) x=0 := by
  rw [divergence_eq_coordinate_sum]
  have h := S.graphVelocity_divergence 1 (by norm_num [data]) (projIcc 0 T hT.le t) x
  simpa only [velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,
    cylinderGraph,coveringMap,data,inner_zero_left,mul_zero] using h

theorem momentum (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    momentumResidual (velocity S) (pressure S) (t,x)=0 := by
  unfold momentumResidual
  rw [(velocity_hasFDerivAt S t ht x).fderiv,comp_apply,inclusion_apply,pressure_gradient]
  have h := S.raw_normalized_equation t ht (x,0)
  simp only [data,tower,coefficient,zero_apply,smul_zero,Finset.sum_const_zero,
    add_zero,transportDirection,one_smul,inner_zero_left,id_apply] at h
  have hd : (1,(velocity S (t,x),0)) =
      ((1,0) : ℝ × LiftTangent)+(0,(velocity S (t,x),0)) := by simp
  rw [hd,map_add]
  exact h

def field (t : Icc (0 : ℝ) T) : SmoothL2Field Space where
  field := S.velocity.physicalPointField 1 0 t
  smooth := S.velocity.physicalPointField_smooth 1 0 t
  integrable n := S.velocity.physicalTensor_memLp 1 0 n t

theorem field_apply (t : Icc (0 : ℝ) T) (x : Space) :
    (field S t).field x=velocity S (t,x) := by
  simp only [field,FieldTower.physicalPointField,EulerCylinderPhysicalTensor.physicalField,
    velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,cylinderGraph,
    coveringMap,projIcc_of_mem hT.le t.property,inner_zero_left,mul_zero]

theorem field_jetLp (n : ℕ) (t : Icc (0 : ℝ) T) :
    (field S t).jetLp n=S.velocity.physicalTensorPath 1 0 n t := by
  apply Lp.ext
  exact (SmoothL2Field.jetLp_ae _ n).trans (S.velocity.physicalTensorPath_ae 1 0 n t).symm

theorem field_jetLp_continuous (n : ℕ) : Continuous (fun t => (field S t).jetLp n) := by
  simp only [field_jetLp]
  exact (S.velocity.physicalTensorPath 1 0 n).continuous

theorem velocity_smooth (t : ℝ) : ContDiff ℝ ∞ (fun x => velocity S (t,x)) := by
  have h := S.velocity.physicalPointField_smooth 1 0 (projIcc 0 T hT.le t)
  change ContDiff ℝ ∞ (fun x => S.velocity.pointField (projIcc 0 T hT.le t) (cylinderGraph P 1 0
    x)) at h
  simpa only [cylinderGraph,inner_zero_left,mul_zero,velocity,ExactLiftedPacket.rawVelocity,
    FieldTower.rawField,coveringMap] using h

theorem force_smooth (t : ℝ) : ContDiff ℝ ∞ (fun x => force S (t,x)) := by
  have h := S.pressure.physicalPointField_smooth 1 0 (projIcc 0 T hT.le t)
  change ContDiff ℝ ∞ (fun x => S.pressure.pointField (projIcc 0 T hT.le t) (cylinderGraph P 1 0
    x)) at h
  simpa only [cylinderGraph,inner_zero_left,mul_zero,force,ExactLiftedPacket.rawPressure,
    FieldTower.rawField,coveringMap] using h

end EulerConstantEuler
