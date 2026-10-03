/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JetStartDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC1

/-! Joint C² regularity of the nonautonomous flow. -/

@[expose] public section

open Homogenization
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Spatial Jacobian used in the joint C² bootstrap. -/
def JointC2All.flowJacobianC1
    (X : ℝ → Vec 2 → ℝ → Vec 2) (p : ℝ × Vec 2 × ℝ) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1

/-- Observation-time velocity used in the joint C² bootstrap. -/
def JointC2All.flowTimeVelocityC1
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  b p.1 (X p.1 p.2.1 p.2.2)

/-- Starting-time velocity used in the joint C² bootstrap. -/
def JointC2All.flowStartVelocityC1
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  -(JointC2All.flowJacobianC1 X p (b p.2.2 p.2.1))

/-- Continuous linear starting-time differential used in the joint C² bootstrap. -/
def JointC2All.flowStartCLMC1
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : ℝ →L[ℝ] Vec 2 :=
  ContinuousLinearMap.toSpanSingleton ℝ (JointC2All.flowStartVelocityC1 b X p)

/-- Position and starting-time differential used in the joint C² bootstrap. -/
def JointC2All.flowParameterDerivativeC1
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (JointC2All.flowJacobianC1 X p).coprod (JointC2All.flowStartCLMC1 b X p)

/-- Full joint differential used in the joint C² bootstrap. -/
def JointC2All.flowJointDerivativeC1
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (ℝ × Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ (JointC2All.flowTimeVelocityC1 b X p)).coprod
    (JointC2All.flowParameterDerivativeC1 b X p)

theorem JointC2All.flowJacobianC1_contDiff
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (JointC2All.flowJacobianC1 X) := by
  have hJ := flow_spatialFDeriv_contDiff_one_all hb hX
  have hperm : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 × ℝ => (p.1, (p.2.2, p.2.1))) := by fun_prop
  change ContDiff ℝ 1
      (fun p : ℝ × Vec 2 × ℝ =>
        fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1)
  simpa only [Function.comp_def] using hJ.comp hperm

theorem JointC2All.flowTimeVelocityC1_contDiff
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (JointC2All.flowTimeVelocityC1 b X) := by
  have hflow := flow_joint_contDiff_one hb hX
  have hflow' : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) := by
    exact hflow
  have hpair : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 × ℝ => (p.1, X p.1 p.2.1 p.2.2)) :=
    contDiff_fst.prodMk hflow'
  change ContDiff ℝ 1 (fun p : ℝ × Vec 2 × ℝ =>
    b p.1 (X p.1 p.2.1 p.2.2))
  simpa [Function.comp_def, Function.uncurry] using
    (hb.smooth.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).comp hpair

theorem JointC2All.flowStartCLMC1_contDiff
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (JointC2All.flowStartCLMC1 b X) := by
  have hJ : ContDiff ℝ 1 (JointC2All.flowJacobianC1 X) := JointC2All.flowJacobianC1_contDiff hb hX
  have hbvalue : ContDiff ℝ 1 (fun p : ℝ × Vec 2 × ℝ => b p.2.2 p.2.1) := by
    have hmap : ContDiff ℝ 1 (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1)) := by
      fun_prop
    exact (hb.smooth.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).comp hmap
  have hvelocity : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 × ℝ => -(JointC2All.flowJacobianC1 X p (b p.2.2 p.2.1))) := by
    exact (hJ.clm_apply hbvalue).neg
  change ContDiff ℝ 1 (fun p =>
    ContinuousLinearMap.toSpanSingleton ℝ
      (-(JointC2All.flowJacobianC1 X p (b p.2.2 p.2.1))))
  exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Vec 2)).contDiff.comp
    hvelocity

theorem JointC2All.flowParameterDerivativeC1_contDiff
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (JointC2All.flowParameterDerivativeC1 b X) := by
  have hJ : ContDiff ℝ 1 (JointC2All.flowJacobianC1 X) := JointC2All.flowJacobianC1_contDiff hb hX
  have hStart : ContDiff ℝ 1 (JointC2All.flowStartCLMC1 b X) := JointC2All.flowStartCLMC1_contDiff
      hb hX
  change ContDiff ℝ 1 (fun p =>
    (JointC2All.flowJacobianC1 X p).coprod (JointC2All.flowStartCLMC1 b X p))
  exact (ContinuousLinearMap.coprodEquivL (S := ℝ) (E := Vec 2)
    (F := ℝ) (G := Vec 2)).contDiff.comp (hJ.prodMk hStart)

theorem JointC2All.flowJointDerivativeC1_contDiff
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (JointC2All.flowJointDerivativeC1 b X) := by
  have htime := JointC2All.flowTimeVelocityC1_contDiff hb hX
  have htimeCLM : ContDiff ℝ 1 (fun p : ℝ × Vec 2 × ℝ =>
      ContinuousLinearMap.toSpanSingleton ℝ (JointC2All.flowTimeVelocityC1 b X p)) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Vec 2)).contDiff.comp htime
  have hparam := JointC2All.flowParameterDerivativeC1_contDiff hb hX
  change ContDiff ℝ 1 (fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ (JointC2All.flowTimeVelocityC1 b X p)).coprod
      (JointC2All.flowParameterDerivativeC1 b X p))
  exact (ContinuousLinearMap.coprodEquivL (S := ℝ) (E := ℝ)
    (F := Vec 2 × ℝ) (G := Vec 2)).contDiff.comp (htimeCLM.prodMk hparam)

/-- Joint `C²` regularity of the smooth flow in target time, initial point,
and start time. -/
theorem flow_joint_contDiff_two_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 2 (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) := by
  rw [show (2 : ℕ∞ω) = (1 : ℕ) + 1 by norm_num,
    contDiff_succ_iff_hasFDerivAt]
  exact ⟨JointC2All.flowJointDerivativeC1 b X,
    JointC2All.flowJointDerivativeC1_contDiff hb hX, fun p => by
      have h := flow_joint_hasFDerivAt_explicit hb hX p
      simpa [JointC2All.flowJointDerivativeC1, flowJointDerivativeFormula,
        JointC2All.flowParameterDerivativeC1,
        JointC2All.flowStartCLMC1, JointC2All.flowStartVelocityC1, JointC2All.flowTimeVelocityC1,
        JointC2All.flowJacobianC1] using h⟩

end

end AVenhance.Infra.Flow
