/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSpatialDerivativeAll
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC1Core
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.StartTimeDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Joint first-order regularity of a smooth nonautonomous flow. -/

@[expose] public section

open Homogenization
open Filter
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Spatial Fréchet derivative of the flow at a joint time-space-start-time point. -/
def JointC1.flowSpatialDerivativeAt
    (X : ℝ → Vec 2 → ℝ → Vec 2) (p : ℝ × Vec 2 × ℝ) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1

/-- Starting-time velocity given by minus the transported initial vector field. -/
def JointC1.flowStartVelocity
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  -(JointC1.flowSpatialDerivativeAt X p (b p.2.2 p.2.1))

/-- Starting-time differential as a continuous linear map from real times. -/
def JointC1.flowStartDerivativeCLM
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : ℝ →L[ℝ] Vec 2 :=
  ContinuousLinearMap.toSpanSingleton ℝ (JointC1.flowStartVelocity b X p)

/-- Differential in the initial position and starting time with observation time fixed. -/
def JointC1.flowPairDerivativeAt
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  ContinuousLinearMap.coprod (JointC1.flowSpatialDerivativeAt X p)
    (JointC1.flowStartDerivativeCLM b X p)

/-- Vector field evaluated at the endpoint of the flow. -/
def JointC1.flowTimeVelocity
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  b p.1 (X p.1 p.2.1 p.2.2)

/-- Observation-time differential as a continuous linear map from real times. -/
def JointC1.flowTimeDerivativeAt
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : ℝ →L[ℝ] Vec 2 :=
  ContinuousLinearMap.toSpanSingleton ℝ (JointC1.flowTimeVelocity b X p)

/-- Joint differential assembled from observation-time, spatial, and starting-time parts. -/
def JointC1.flowJointDerivativeAt
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (ℝ × Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (JointC1.flowTimeDerivativeAt b X p).coprod (JointC1.flowPairDerivativeAt b X p)

/-- Explicit joint differential formula for the three arguments of the flow. -/
def flowJointDerivativeFormula
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (ℝ × Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ (b p.1 (X p.1 p.2.1 p.2.2))).coprod
    ((fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ
        (-((fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1) (b p.2.2 p.2.1)))))

theorem JointC1.flowStartDerivativeCLM_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (JointC1.flowStartDerivativeCLM b X) := by
  have hspace : Continuous (JointC1.flowSpatialDerivativeAt X) :=
    flow_spatialFDeriv_jointContinuous hb hX
  have hfieldMap : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1)) :=
    (continuous_snd.comp continuous_snd).prodMk
      (continuous_fst.comp continuous_snd)
  have hfield : Continuous (fun p : ℝ × Vec 2 × ℝ => b p.2.2 p.2.1) :=
    hb.smooth.continuous.comp hfieldMap
  have hvelocity : Continuous (JointC1.flowStartVelocity b X) := by
    have happly : Continuous
        (fun q : (Vec 2 →L[ℝ] Vec 2) × Vec 2 => q.1 q.2) :=
      isBoundedBilinearMap_apply.continuous
    exact (happly.comp (hspace.prodMk hfield)).neg
  exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Vec 2)).continuous.comp
    hvelocity

theorem JointC1.flowPairDerivativeAt_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (JointC1.flowPairDerivativeAt b X) := by
  have hspace : Continuous (JointC1.flowSpatialDerivativeAt X) :=
    flow_spatialFDeriv_jointContinuous hb hX
  have hstart : Continuous (JointC1.flowStartDerivativeCLM b X) :=
    JointC1.flowStartDerivativeCLM_continuous hb hX
  change Continuous (fun p : ℝ × Vec 2 × ℝ =>
    ContinuousLinearMap.coprod (JointC1.flowSpatialDerivativeAt X p)
      (JointC1.flowStartDerivativeCLM b X p))
  exact (ContinuousLinearMap.coprodEquivL (S := ℝ) (E := Vec 2)
    (F := ℝ) (G := Vec 2)).continuous.comp (hspace.prodMk hstart)

theorem JointC1.flowTimeDerivativeAt_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (JointC1.flowTimeDerivativeAt b X) := by
  have hvel : Continuous (JointC1.flowTimeVelocity b X) :=
    flow_target_time_derivative_continuous hb hX
  change Continuous (fun p =>
    ContinuousLinearMap.toSpanSingleton ℝ (JointC1.flowTimeVelocity b X p))
  exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Vec 2)).continuous.comp hvel

theorem JointC1.flow_fixedTarget_pair_hasStrictFDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (t : ℝ) (x : Vec 2) (s : ℝ) :
    HasStrictFDerivAt (fun q : Vec 2 × ℝ => X t q.1 q.2)
      ((JointC1.flowSpatialDerivativeAt X (t, x, s)).coprod
        (JointC1.flowStartDerivativeCLM b X (t, x, s)))
      (x, s) := by
  exact hasStrictFDerivAt_uncurry_coprod
    (f := fun x s => X t x s)
    (f₁ := fun x s => JointC1.flowSpatialDerivativeAt X (t, x, s))
    (f₂ := fun x s => JointC1.flowStartDerivativeCLM b X (t, x, s))
    (Filter.Eventually.of_forall fun q => by
      change HasFDerivAt (fun y : Vec 2 => X t y q.2)
        (JointC1.flowSpatialDerivativeAt X (t, q.1, q.2)) q.1
      exact ((flow_spatial_contDiff_one hb hX q.2 t).differentiable
        (by norm_num) q.1).hasFDerivAt)
    (Filter.Eventually.of_forall fun q => by
      change HasFDerivAt (fun r : ℝ => X t q.1 r)
        (JointC1.flowStartDerivativeCLM b X (t, q.1, q.2)) q.2
      exact (flow_initialTime_hasDerivAt hb hX q.1 q.2 t).hasFDerivAt)
    (by
      have hmap : Continuous (fun q : Vec 2 × ℝ => (t, q.1, q.2)) := by fun_prop
      change ContinuousAt (fun q : Vec 2 × ℝ =>
        JointC1.flowSpatialDerivativeAt X (t, q.1, q.2)) (x, s)
      exact (flow_spatialFDeriv_jointContinuous hb hX).continuousAt.comp hmap.continuousAt)
    (by
      have hmap : Continuous (fun q : Vec 2 × ℝ => (t, q.1, q.2)) := by fun_prop
      change ContinuousAt (fun q : Vec 2 × ℝ =>
        JointC1.flowStartDerivativeCLM b X (t, q.1, q.2)) (x, s)
      exact (JointC1.flowStartDerivativeCLM_continuous hb hX).continuousAt.comp hmap.continuousAt)

/-- The full time, position, and initial-time map of a smooth periodic flow is
continuously Fréchet differentiable. Its partial derivatives are the vector
field and the jointly continuous spatial/start-time derivative. -/
theorem flow_joint_hasFDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (p : ℝ × Vec 2 × ℝ) :
    HasFDerivAt (fun q : ℝ × Vec 2 × ℝ => X q.1 q.2.1 q.2.2)
      (JointC1.flowJointDerivativeAt b X p) p := by
  exact hasStrictFDerivAt_uncurry_coprod
    (f := fun t q => X t q.1 q.2)
    (f₁ := fun t q =>
      ContinuousLinearMap.toSpanSingleton ℝ (JointC1.flowTimeVelocity b X (t, q.1, q.2)))
    (f₂ := fun t q => JointC1.flowPairDerivativeAt b X (t, q.1, q.2))
    (Filter.Eventually.of_forall fun q => by
      change HasFDerivAt (fun r : ℝ => X r q.2.1 q.2.2)
        (ContinuousLinearMap.toSpanSingleton ℝ
          (JointC1.flowTimeVelocity b X (q.1, q.2.1, q.2.2))) q.1
      exact (hX.2 q.2.1 q.2.2 q.1).hasFDerivAt)
    (Filter.Eventually.of_forall fun q => by
      change HasFDerivAt (fun z : Vec 2 × ℝ => X q.1 z.1 z.2)
        (JointC1.flowPairDerivativeAt b X (q.1, q.2.1, q.2.2)) q.2
      exact (JointC1.flow_fixedTarget_pair_hasStrictFDerivAt hb hX q.1 q.2.1 q.2.2).hasFDerivAt)
    (by
      have h := JointC1.flowTimeDerivativeAt_continuous hb hX
      change ContinuousAt (fun q : ℝ × (Vec 2 × ℝ) =>
        JointC1.flowTimeDerivativeAt b X (q.1, q.2.1, q.2.2)) (p.1, (p.2.1, p.2.2))
      exact h.continuousAt)
    (by
      have h := JointC1.flowPairDerivativeAt_continuous hb hX
      change ContinuousAt (fun q : ℝ × (Vec 2 × ℝ) =>
        JointC1.flowPairDerivativeAt b X (q.1, q.2.1, q.2.2)) (p.1, (p.2.1, p.2.2))
      exact h.continuousAt)
    |>.hasFDerivAt

/-- Explicit form of the total derivative of the joint flow map, with the
spatial and start-time components exposed for higher regularity bootstraps. -/
theorem flow_joint_hasFDerivAt_explicit
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (p : ℝ × Vec 2 × ℝ) :
    HasFDerivAt (fun q : ℝ × Vec 2 × ℝ => X q.1 q.2.1 q.2.2)
      (flowJointDerivativeFormula b X p) p := by
  have h := flow_joint_hasFDerivAt hb hX p
  simpa [flowJointDerivativeFormula, JointC1.flowJointDerivativeAt,
    JointC1.flowTimeDerivativeAt, JointC1.flowTimeVelocity, JointC1.flowPairDerivativeAt,
    JointC1.flowSpatialDerivativeAt, JointC1.flowStartDerivativeCLM, JointC1.flowStartVelocity]
        using h

/-- Joint `C¹` regularity of a smooth periodic nonautonomous flow. -/
theorem flow_joint_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) := by
  exact contDiff_one_of_time_and_parameter_derivatives
    (fun p : ℝ × (Vec 2 × ℝ) => X p.1 p.2.1 p.2.2)
    (fun p : ℝ × (Vec 2 × ℝ) => JointC1.flowTimeVelocity b X p)
    (fun p : ℝ × (Vec 2 × ℝ) => JointC1.flowPairDerivativeAt b X p)
    (by
      intro t z
      simpa [JointC1.flowTimeVelocity] using hX.2 z.1 z.2 t)
    (by
      intro t z
      exact JointC1.flow_fixedTarget_pair_hasStrictFDerivAt hb hX t z.1 z.2)
    (by
      simpa [JointC1.flowTimeVelocity] using flow_target_time_derivative_continuous hb hX)
    (JointC1.flowPairDerivativeAt_continuous hb hX)

/-- The inverse flow map is jointly `C¹` in target time, point, and initial
time; its spatial slice is the inverse of the forward flow map. -/
theorem flow_inverse_joint_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) := by
  have hperm : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1, p.1)) := by fun_prop
  simpa only [Function.comp_def] using
    (flow_joint_contDiff_one hb hX).comp hperm

end

end AVenhance.Infra.Flow
