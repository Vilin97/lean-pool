/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Partial

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSecondContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC1
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Joint first-order regularity of the actual spatial flow Jacobian. -/

@[expose] public section

noncomputable section
open Homogenization Set Filter
open scoped Topology
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- An actual spatial Jacobian entry with a fixed initial time. -/
def amnrFlowJacobianEntry (X : ℝ → Vec 2 → ℝ → Vec 2) (s : ℝ)
    (i j : Fin 2) (z : ℝ × Vec 2) : ℝ :=
  fderiv ℝ (fun y => X z.1 y s) z.2 (basisVec i) j

/-- The spatial derivative of a Jacobian entry is an evaluation of the
actual second derivative, in the source row convention. -/
theorem amnrFlowJacobianEntry_spatial_fderiv_apply
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) (x v : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y => amnrFlowJacobianEntry X s i j (t, y)) x v =
      amnrFlowSecondEval X s v (basisVec i) (t, x) j := by
  have hF := flow_spatial_contDiff_two hb hX s t
  have hdf : DifferentiableAt ℝ (fderiv ℝ (fun y => X t y s)) x :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hconst : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec i) x := differentiableAt_const _
  have hd := hdf.clm_apply hconst
  change fderiv ℝ (fun y => (fderiv ℝ (fun w => X t w s) y (basisVec i)) j) x v = _
  rw [fderiv_apply hd j, fderiv_clm_apply hdf hconst]
  simp [amnrFlowSecondEval, ContinuousLinearMap.comp_apply]

/-- The derivative with respect to the initial point is jointly continuous
in target time and initial point. -/
theorem amnrFlowJacobianEntry_spatial_fderiv_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s : ℝ) (i j : Fin 2) :
    Continuous (fun z : ℝ × Vec 2 =>
      fderiv ℝ (fun y => amnrFlowJacobianEntry X s i j (z.1, y)) z.2) := by
  apply continuous_clm_apply.mpr
  intro v
  have hc := (continuous_apply j).comp (amnrFlowSecondEval_continuous hb hX s v (basisVec i))
  have heq : (fun z : ℝ × Vec 2 =>
      fderiv ℝ (fun y => amnrFlowJacobianEntry X s i j (z.1, y)) z.2 v) =
      fun z => amnrFlowSecondEval X s v (basisVec i) z j := by
    funext z
    exact amnrFlowJacobianEntry_spatial_fderiv_apply hb hX s z.1 z.2 v i j
  rw [heq]
  exact hc

/-- The Jacobian follows the actual linearized flow equation, at all times. -/
theorem amnrFlowJacobianEntry_hasDerivAt_time
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) (x : Vec 2) (i j : Fin 2) :
    HasDerivAt (fun r => amnrFlowJacobianEntry X s i j (r, x))
      (jointSpatialFDeriv b t (X t x s)
        (fderiv ℝ (fun y => X t y s) x (basisVec i)) j) t := by
  obtain ⟨V, hV, hUnique⟩ := existsUnique_flow_variationalEquation hb hX x s
  have heq (r : ℝ) : fderiv ℝ (fun y => X r y s) x (basisVec i) = V r (basisVec i) s := by
    obtain ⟨W, J, hW, hJ, hD⟩ := exists_flow_hasFDerivAt_spatial hb hX x s r
    rw [hD.fderiv, hJ, hUnique W hW]
  have hv := hV.2 (basisVec i) s t
  have hp := (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).hasFDerivAt.comp t hv.hasFDerivAt
  have htime : (fun r => amnrFlowJacobianEntry X s i j (r, x)) =
      fun r => V r (basisVec i) s j := by
    funext r
    exact congrArg (fun v : Vec 2 => v j) (heq r)
  rw [htime]
  simpa [ContinuousLinearMap.comp_apply,
    linearizedFieldAlongFlow, Function.comp_def, ← heq t] using hp.hasDerivAt

/-- The linearized equation's right side is jointly continuous. -/
theorem amnrFlowJacobianEntry_time_derivative_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s : ℝ) (i j : Fin 2) :
    Continuous (fun z : ℝ × Vec 2 => jointSpatialFDeriv b z.1 (X z.1 z.2 s)
      (fderiv ℝ (fun y => X z.1 y s) z.2 (basisVec i)) j) := by
  have hXc := flow_continuous_joint_of_smoothPeriodic hb hX
  have hXm : Continuous (fun z : ℝ × Vec 2 => X z.1 z.2 s) :=
    hXc.comp (show Continuous (fun z : ℝ × Vec 2 => (z.1, z.2, s)) by fun_prop)
  have hBc := (jointSpatialFDeriv_continuous hb).comp (continuous_fst.prodMk hXm)
  have hJc := (flow_spatialFDeriv_jointContinuous hb hX).comp
    (show Continuous (fun z : ℝ × Vec 2 => (z.1, z.2, s)) by fun_prop)
  exact (continuous_apply j).comp (hBc.clm_apply (hJc.clm_apply continuous_const))

/-- Combining the actual time and spatial derivatives gives joint C¹
regularity of every flow-Jacobian entry, including at the initial time. -/
theorem amnrFlowJacobianEntry_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s : ℝ) (i j : Fin 2) : ContDiff ℝ 1 (amnrFlowJacobianEntry X s i j) := by
  let f₁ := fun z : ℝ × Vec 2 => ContinuousLinearMap.toSpanSingleton ℝ
    (jointSpatialFDeriv b z.1 (X z.1 z.2 s)
      (fderiv ℝ (fun y => X z.1 y s) z.2 (basisVec i)) j)
  let f₂ := fun z : ℝ × Vec 2 =>
    fderiv ℝ (fun y => amnrFlowJacobianEntry X s i j (z.1, y)) z.2
  have h₁ : Continuous f₁ := by
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp
      (amnrFlowJacobianEntry_time_derivative_continuous hb hX s i j)
  have h₂ : Continuous f₂ := amnrFlowJacobianEntry_spatial_fderiv_continuous hb hX s i j
  have hd (z : ℝ × Vec 2) : HasFDerivAt (amnrFlowJacobianEntry X s i j)
      ((f₁ z).coprod (f₂ z)) z := by
    apply (hasStrictFDerivAt_uncurry_coprod (f := fun t x => amnrFlowJacobianEntry X s i j (t, x))
      (f₁ := fun t x => f₁ (t, x)) (f₂ := fun t x => f₂ (t, x)) ?_ ?_
      h₁.continuousAt h₂.continuousAt).hasFDerivAt
    · exact Eventually.of_forall fun y =>
        (amnrFlowJacobianEntry_hasDerivAt_time hb hX s y.1 y.2 i j).hasFDerivAt
    · apply Eventually.of_forall
      intro y
      have hh := (flow_spatial_contDiff_two hb hX s y.1).fderiv_right (m := 1) (by norm_num)
      have hv := hh.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => basisVec i))
      exact ((contDiff_pi.mp hv j).differentiable (by norm_num) y.2).hasFDerivAt
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨fun z => (f₁ z).coprod (f₂ z), h₁.continuousLinearMapCoprod h₂, hd⟩

end AVenhance.Infra.Section4
