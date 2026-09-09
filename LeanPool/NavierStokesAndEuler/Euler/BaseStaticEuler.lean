/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerGevrey
public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerParity
public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerLabelData
public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerParity
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState

@[expose] public section

/-! The locally constructed ordinary Euler solution supplies a concrete
first parent, its label budget and its genuine particle inverse. All
constants and the positive common horizon depend only on the input
Gevrey envelope, not on the particular initial datum. -/

noncomputable section

namespace EulerStaticEuler

open Set EulerSmoothLimit EulerLpTranslation EulerParentPacketFrames
  EulerTimeIntervalRestriction EulerParameterWordGevrey EulerSmoothFlowGevrey
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

def baseTime (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ :=
  EulerBaseEulerParent.horizon (amplitude P C R hC hR)
    (outputVelocitySize P C R) (outputRadius R)

theorem baseTime_pos (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 < baseTime P C R hC hR :=
  EulerBaseEulerParent.horizon_pos _ _ _ (amplitude_pos P C R hC hR)
    (outputVelocitySize_nonneg P C R hC hR) (outputRadius_pos R hR).le

theorem baseTime_le (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    baseTime P C R hC hR ≤ amplitude P C R hC hR :=
  EulerBaseEulerParent.horizon_le _ _ _

def baseInclusion (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) (baseTime P C R hC hR), Icc (0 : ℝ) (amplitude P C R hC hR)) :=
  initialInclusion _ _ (baseTime_le P C R hC hR)

def baseLabelConstant (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ :=
  let T := baseTime P C R hC hR
  let B := outputVelocitySize P C R
  let S := outputRadius R
  let C₁ := outputDerivativeSize P C R hC hR
  let V := flowRadius B S T S
  let M := C₁+3*(B*S)*B
  let A := flowRadius B S T (4*S+S+S)
  1+sobolevCoefficientAmplitude (Fin 3) 6 V (T*B)+
    sobolevCoefficientAmplitude (Fin 3) 6 V B+
    sobolevCoefficientAmplitude (Fin 3) 6 A M+
    sobolevCoefficientRadius (Fin 3) V+sobolevCoefficientRadius (Fin 3) A

variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x=0)

def baseInput : EulerBaseEulerParent.Input :=
  EulerBaseEulerParent.ofInterval (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (velocityCoefficient P u C R hC hR hu hdiv)
    (derivativeCoefficient P u C R hC hR hu hdiv)
    (coefficient_time P u C R hC hR hu hdiv)
    (fun t x => by
      have he : ((velocityCoefficient P u C R hC hR hu hdiv).field t : Space → Space)=
          fun y => localVelocity P u C R hC hR hu hdiv (t,y) :=
        funext (velocityCoefficient_apply P u C R hC hR hu hdiv t)
      rw [he]
      exact localVelocity_divergence P u C R hC hR hu hdiv t x)
    (outputVelocitySize P C R) (outputRadius R)
    (outputVelocitySize_nonneg P C R hC hR) (outputRadius_pos R hR)
    (velocityCoefficient_bound P u C R hC hR hu hdiv)

theorem baseInput_field (t : Icc (0 : ℝ) (baseTime P C R hC hR)) (x : Space) :
    (baseInput P u C R hC hR hu hdiv).field.field t x=
      localVelocity P u C R hC hR hu hdiv (t,x) :=
  velocityCoefficient_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t) x

def baseL2Data : EulerBaseEulerParent.L2Data (baseInput P u C R hC hR hu hdiv) where
  velocity t := localField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  derivative t := localDerivativeField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  velocity_match t x :=
    (localField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t) x).trans
      (baseInput_field P u C R hC hR hu hdiv t x).symm
  derivative_match t x :=
    localDerivativeField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t) x
  C := outputVelocitySize P C R
  S := outputRadius R
  C₁ := outputDerivativeSize P C R hC hR
  S₁ := outputRadius R
  C_nonneg := outputVelocitySize_nonneg P C R hC hR
  S_nonneg := (outputRadius_pos R hR).le
  C₁_nonneg := outputDerivativeSize_nonneg P C R hC hR
  S₁_nonneg := (outputRadius_pos R hR).le
  velocity_bound t := localField_bound P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  derivative_bound t := localDerivativeField_bound P u C R hC hR hu hdiv
    (baseInclusion P C R hC hR t)

variable (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)

def baseParent : Parent := (baseInput P u C R hC hR hu hdiv).parent ell hell hell1

def baseLabelData : LabelData (baseParent P u C R hC hR hu hdiv ell hell hell1) :=
  (baseL2Data P u C R hC hR hu hdiv).labelData ell hell hell1

theorem baseLabelData_constant :
    (baseLabelData P u C R hC hR hu hdiv ell hell hell1).K=baseLabelConstant P C R hC hR := rfl

include u hu hdiv ell hell hell1 in
theorem baseLabelConstant_one : 1 ≤ baseLabelConstant P C R hC hR :=
  (baseLabelData P u C R hC hR hu hdiv ell hell hell1).K_one

def baseInverse : ParticleInverse (baseParent P u C R hC hR hu hdiv ell hell hell1) :=
  (baseInput P u C R hC hR hu hdiv).particleInverse ell hell hell1

theorem baseParent_velocity_match (t : Icc (0 : ℝ) (baseTime P C R hC hR)) (x : Space) :
    (baseParent P u C R hC hR hu hdiv ell hell hell1).velocity.field t x=
      localVelocity P u C R hC hR hu hdiv
        (t,(baseParent P u C R hC hR hu hdiv ell hell hell1).position t x) := by
  have h := (baseInput P u C R hC hR hu hdiv).parent_velocity ell hell hell1 t x
  exact h.trans (baseInput_field P u C R hC hR hu hdiv t _)

def baseEvolution : Evolution (baseParent P u C R hC hR hu hdiv ell hell hell1) where
  inverse := baseInverse P u C R hC hR hu hdiv ell hell hell1
  velocity := localVelocity P u C R hC hR hu hdiv
  pressure := localPressure P u C R hC hR hu hdiv
  force t x := localForce P u C R hC hR hu hdiv (t,x)
  force_continuous := by
    have hc : Continuous (fun q : Icc (0 : ℝ) (baseTime P C R hC hR) × Space =>
        ((q.1 : ℝ),q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (localForce_joint_continuous P u C R hC hR hu hdiv).comp hc
  velocity_match := baseParent_velocity_match P u C R hC hR hu hdiv ell hell hell1
  velocity_differentiable t ht x := localVelocity_differentiableAt P u C R hC hR hu hdiv t
    ⟨ht.1,ht.2.trans_le (baseTime_le P C R hC hR)⟩ x
  pressure_differentiable t x :=
    (localPressure_smooth P u C R hC hR hu hdiv t).differentiable (by simp) x
  pressure_gradient t x := localPressure_gradient P u C R hC hR hu hdiv t x
  momentum_zero t ht x := localMomentum P u C R hC hR hu hdiv t
    ⟨ht.1,ht.2.trans_le (baseTime_le P C R hC hR)⟩ x
  divergence_zero t _ x := localVelocity_divergence P u C R hC hR hu hdiv t x

theorem baseParent_initial_velocity (x : Space) :
    (baseParent P u C R hC hR hu hdiv ell hell hell1).velocity.field
      ⟨0,le_rfl,(baseTime_pos P C R hC hR).le⟩ x=u.field x := by
  have h := baseParent_velocity_match P u C R hC hR hu hdiv ell hell hell1
    ⟨0,le_rfl,(baseTime_pos P C R hC hR).le⟩ x
  have hz : (baseParent P u C R hC hR hu hdiv ell hell hell1).position
      ⟨0,le_rfl,(baseTime_pos P C R hC hR).le⟩ x=x := by
    change x+(baseParent P u C R hC hR hu hdiv ell hell hell1).displacement.field _ x=x
    rw [(baseParent P u C R hC hR hu hdiv ell hell hell1).initial,add_zero]
  erw [hz,localVelocity_initial] at h
  exact h

theorem baseOddData (hodd : ∀ x, u.field (-x)= -u.field x) :
    OddData (baseParent P u C R hC hR hu hdiv ell hell hell1) := by
  apply (baseInput P u C R hC hR hu hdiv).oddData _ ell hell hell1
  intro t x
  erw [baseInput_field,baseInput_field]
  exact localVelocity_odd P u C R hC hR hu hdiv hodd t x

end EulerStaticEuler
