/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphGevrey
public import LeanPool.NavierStokesAndEuler.Euler.SmoothPhysicalGraphFlow
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCylinderAccelerationComposition

@[expose] public section

/-! The actual physical graph flow has smooth square-integrable
displacement, velocity and acceleration, with explicit Gevrey bounds.
Every input estimate is on the original lifted velocity or its genuine
time derivative; no regularity of the output flow is assumed. -/

noncomputable section

namespace EulerPhysicalGraphFlowBounds

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey EulerGraphInvariantFlow
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerPhysicalGraphGevrey
  EulerCylinderGraphGevrey
open scoped ContDiff BoundedContinuousFunction

private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ]
  LiftTangent)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))
  := inferInstance

structure Data (P T : ℝ) [Fact (0 < P)] where
  time_nonneg : 0 ≤ T
  A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent
  A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent
  time_derivative : SmoothTimeField.TimeDerivative T time_nonneg A A₁
  periodic : ∀ (c : AddSubgroup.zmultiples P) t z, A.field t (z.1,(c : ℝ)+z.2)=A.field t z
  periodic_time : ∀ (c : AddSubgroup.zmultiples P) t z, A₁.field t (z.1,(c : ℝ)+z.2)=A₁.field t z
  divergence : ∀ t z,
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) z).toLinearMap=0
  B : ℝ
  R : ℝ
  C : ℝ
  S : ℝ
  C₁ : ℝ
  S₁ : ℝ
  B_nonneg : 0 ≤ B
  R_pos : 0 < R
  C_nonneg : 0 ≤ C
  S_nonneg : 0 ≤ S
  C₁_nonneg : 0 ≤ C₁
  S₁_nonneg : 0 ≤ S₁
  small : B*R*T ≤ 1/8
  sup_bound : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2
  integrable : ∀ t n,
    MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure P)
  lp_bound : ∀ t n,
    (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure
      P)).toReal ≤
      C*S^n*(n.factorial : ℝ)^2
  integrable_time : ∀ t n,
    MemLp (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure P)
  lp_bound_time : ∀ t n,
    (eLpNorm (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure
      P)).toReal ≤
      C₁*S₁^n*(n.factorial : ℝ)^2

namespace Data

variable {P T : ℝ} [Fact (0 < P)] (G : Data P T)

def velocityRadius : ℝ := flowRadius G.B G.R T G.S
def accelerationRadius : ℝ := flowRadius G.B G.R T (4*G.R+G.S+G.S₁)
def accelerationAmplitude : ℝ := G.C₁+3*G.B*G.R*G.C

theorem velocityRadius_nonneg : 0 ≤ G.velocityRadius := by
  have := G.B_nonneg
  have := G.R_pos
  have := G.S_nonneg
  have := G.time_nonneg
  unfold velocityRadius flowRadius
  positivity

theorem accelerationRadius_nonneg : 0 ≤ G.accelerationRadius := by
  have := G.B_nonneg
  have := G.R_pos
  have := G.S_nonneg
  have := G.S₁_nonneg
  have := G.time_nonneg
  unfold accelerationRadius flowRadius
  positivity

theorem accelerationAmplitude_nonneg : 0 ≤ G.accelerationAmplitude := by
  have := G.B_nonneg
  have := G.R_pos
  have := G.C_nonneg
  have := G.C₁_nonneg
  unfold accelerationAmplitude
  positivity

theorem displacement_cylinder_bound (t : Icc (0 : ℝ) T) (n : ℕ) :
    MemLp (fun q => jetSeries P (displacement T G.time_nonneg G.A t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (displacement T G.time_nonneg G.A t) q n)
        2 (liftMeasure P)).toReal ≤ (T*G.C)*G.velocityRadius^n*(n.factorial : ℝ)^2 := by
  obtain ⟨hi,hn⟩ := EulerSmoothCylinderFlow.displacementJet_memLp_and_bound
    P T G.time_nonneg G.A G.periodic G.divergence G.B G.R G.C G.S
    G.B_nonneg G.R_pos G.C_nonneg G.S_nonneg G.small G.sup_bound n
    (fun s j _ => G.integrable s j) (fun s j _ => G.lp_bound s j) t
  refine ⟨hi,hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right t.property.2 G.C_nonneg)
      (pow_nonneg G.velocityRadius_nonneg n)) (sq_nonneg _)

theorem velocity_periodic (t : Icc (0 : ℝ) T) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    materialVelocity T G.time_nonneg G.A t (z.1,(c : ℝ)+z.2)=
      materialVelocity T G.time_nonneg G.A t z :=
  comp_deck P (G.A.field t : LiftTangent → LiftTangent) (fun d y => G.periodic d t y)
    ((flowData T G.time_nonneg G.A).forward t)
    (EulerCylinderPeriodicFlow.flow_deck P (flowData T G.time_nonneg G.A)
      (EulerSmoothCylinderFlow.velocity_deck P T G.time_nonneg G.A G.periodic) 0 t) c z

theorem velocity_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (materialVelocity T G.time_nonneg G.A t) :=
  (G.A.smooth t).comp (forward_contDiff T G.time_nonneg G.A t)

theorem velocity_cylinder_bound (t : Icc (0 : ℝ) T) (n : ℕ) :
    MemLp (fun q => jetSeries P (materialVelocity T G.time_nonneg G.A t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (materialVelocity T G.time_nonneg G.A t) q n)
        2 (liftMeasure P)).toReal ≤ G.C*G.velocityRadius^n*(n.factorial : ℝ)^2 :=
  EulerSmoothCylinderFlow.composeJet_memLp_and_bound P T G.time_nonneg G.A G.periodic G.divergence
    (G.A.field t) (G.A.smooth t) (fun c z => G.periodic c t z) G.B G.R G.C G.S
    G.B_nonneg G.R_pos G.C_nonneg G.S_nonneg G.small G.sup_bound n
    (fun j _ => G.integrable t j) (fun j _ => G.lp_bound t j) t

theorem acceleration_periodic (t : Icc (0 : ℝ) T) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    materialAcceleration T G.time_nonneg G.A G.A₁ t (z.1,(c : ℝ)+z.2)=
      materialAcceleration T G.time_nonneg G.A G.A₁ t z :=
  comp_deck P (accelerationField T G.A G.A₁ t)
    (EulerSmoothCylinderFlow.accelerationField_deck P T G.A G.A₁ G.periodic G.periodic_time t)
    ((flowData T G.time_nonneg G.A).forward t)
    (EulerCylinderPeriodicFlow.flow_deck P (flowData T G.time_nonneg G.A)
      (EulerSmoothCylinderFlow.velocity_deck P T G.time_nonneg G.A G.periodic) 0 t) c z

theorem acceleration_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (materialAcceleration T G.time_nonneg G.A G.A₁ t) :=
  (accelerationField_contDiff T G.A G.A₁ t).comp (forward_contDiff T G.time_nonneg G.A t)

theorem acceleration_cylinder_bound (t : Icc (0 : ℝ) T) (n : ℕ) :
    MemLp (fun q => jetSeries P (materialAcceleration T G.time_nonneg G.A G.A₁ t) q n)
      2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (materialAcceleration T G.time_nonneg G.A G.A₁ t) q n)
        2 (liftMeasure P)).toReal ≤ G.accelerationAmplitude*G.accelerationRadius^n*(n.factorial :
          ℝ)^2 :=
  EulerSmoothCylinderFlow.materialAccelerationJet_memLp_and_bound P T G.time_nonneg G.A G.A₁
    G.periodic G.periodic_time G.divergence G.B G.R G.C G.S G.C₁ G.S₁
    G.B_nonneg G.R_pos G.C_nonneg G.S_nonneg G.C₁_nonneg G.S₁_nonneg
    G.small G.sup_bound G.integrable G.lp_bound G.integrable_time G.lp_bound_time n t

def displacementField (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) :
    SmoothL2Field Vector3 :=
  physicalField P (displacement T G.time_nonneg G.A t)
    (EulerSmoothCylinderFlow.coverDisplacement_deck P T G.time_nonneg G.A G.periodic t)
    (displacement_contDiff T G.time_nonneg G.A t) k m (T*G.C) G.velocityRadius
    (mul_nonneg G.time_nonneg G.C_nonneg) G.velocityRadius_nonneg
    (fun n => (G.displacement_cylinder_bound t n).1) (fun n => (G.displacement_cylinder_bound t
      n).2)
    ell hell (fst ℝ Vector3 ℝ)

def velocityField (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) :
    SmoothL2Field Vector3 :=
  physicalField P (materialVelocity T G.time_nonneg G.A t) (G.velocity_periodic t)
    (G.velocity_smooth t)
    k m G.C G.velocityRadius G.C_nonneg G.velocityRadius_nonneg
    (fun n => (G.velocity_cylinder_bound t n).1) (fun n => (G.velocity_cylinder_bound t n).2)
    ell hell (fst ℝ Vector3 ℝ)

def accelerationFieldL2 (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) :
    SmoothL2Field Vector3 :=
  physicalField P (materialAcceleration T G.time_nonneg G.A G.A₁ t)
    (G.acceleration_periodic t) (G.acceleration_smooth t) k m G.accelerationAmplitude
      G.accelerationRadius
    G.accelerationAmplitude_nonneg G.accelerationRadius_nonneg
    (fun n => (G.acceleration_cylinder_bound t n).1) (fun n => (G.acceleration_cylinder_bound t
      n).2)
    ell hell (fst ℝ Vector3 ℝ)

theorem displacementField_bound (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.displacementField k m ell hell t).HasJetBound
      (Real.sqrt (2/P+2*P)*(T*G.C)*(1+G.velocityRadius)) (ell⁻¹*(4*G.velocityRadius*graphFactor k
        m)) :=
  physicalField_bound P _ _ _ k m (T*G.C) G.velocityRadius
    (mul_nonneg G.time_nonneg G.C_nonneg) G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..)

theorem velocityField_bound (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.velocityField k m ell hell t).HasJetBound
      (Real.sqrt (2/P+2*P)*G.C*(1+G.velocityRadius)) (ell⁻¹*(4*G.velocityRadius*graphFactor k m)) :=
  physicalField_bound P _ _ _ k m G.C G.velocityRadius G.C_nonneg G.velocityRadius_nonneg
    _ _ ell hell hell1 (fst ℝ Vector3 ℝ) (norm_fst_le ..)

theorem accelerationField_bound (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.accelerationFieldL2 k m ell hell t).HasJetBound
      (Real.sqrt (2/P+2*P)*G.accelerationAmplitude*(1+G.accelerationRadius))
      (ell⁻¹*(4*G.accelerationRadius*graphFactor k m)) :=
  physicalField_bound P _ _ _ k m G.accelerationAmplitude G.accelerationRadius
    G.accelerationAmplitude_nonneg G.accelerationRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..)

variable (k : ℝ) (m : Vector3)
  (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0)

include hgraph in
theorem displacementField_eq (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.displacementField k m ell hell t).field x =
      displacement T G.time_nonneg (physicalCoefficient k m T G.A ell) t x :=
  (physical_displacement_eq k m T G.time_nonneg G.A hgraph ell hell.ne' t x).symm

include hgraph in
theorem velocityField_eq (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.velocityField k m ell hell t).field x =
      materialVelocity T G.time_nonneg (physicalCoefficient k m T G.A ell) t x :=
  (physical_materialVelocity_eq k m T G.time_nonneg G.A hgraph ell hell.ne' t x).symm

include hgraph in
theorem accelerationField_eq (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.accelerationFieldL2 k m ell hell t).field x =
      materialAcceleration T G.time_nonneg (physicalCoefficient k m T G.A ell)
        (physicalCoefficient k m T G.A₁ ell) t x :=
  (physical_materialAcceleration_eq k m T G.time_nonneg G.A G.A₁ hgraph ell hell.ne' t x).symm

end Data
end EulerPhysicalGraphFlowBounds
