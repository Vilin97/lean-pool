/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FlowIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Differentiability of a flow with respect to its initial-time parameter. -/

@[expose] public section

open Homogenization
open Filter
open Asymptotics
open MeasureTheory
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

theorem StartTimeDerivative.hasDerivAt_diagonalIntervalIntegral
    {g : ℝ × ℝ → Vec 2} (hg : Continuous g) (a : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ u in r..a, g (u, r)) (-g (a, a)) a := by
  let F : ℝ → Vec 2 := fun r => ∫ u in r..a, g (u, r)
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hnear : ∀ᶠ p in 𝓝 (a, a), ‖g p - g (a, a)‖ < c := by
    have hball := hg.continuousAt.eventually (Metric.ball_mem_nhds (g (a, a)) hc)
    simpa only [Metric.mem_ball, dist_eq_norm] using hball
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
  filter_upwards [Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun r hr => hr⟩] with r hr
  have hFa : F a = 0 := by simp [F]
  have hGint : IntervalIntegrable (fun u : ℝ => g (u, r)) volume r a := by
    exact (hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable r a
  have hCint : IntervalIntegrable (fun _ : ℝ => g (a, a)) volume r a :=
    intervalIntegrable_const
  have hrem :
      (F r - F a - (r - a) • (-g (a, a))) =
        ∫ u in r..a, (g (u, r) - g (a, a)) := by
    rw [hFa, sub_zero]
    change (∫ u in r..a, g (u, r)) - (r - a) • (-g (a, a)) = _
    rw [intervalIntegral.integral_sub hGint hCint, intervalIntegral.integral_const]
    rw [show r - a = -(a - r) by ring, neg_smul, smul_neg, neg_neg]
  have hbound : ∀ u ∈ Set.uIoc r a, ‖g (u, r) - g (a, a)‖ ≤ c := by
    intro u hu
    have huIcc : u ∈ uIcc r a := uIoc_subset_uIcc hu
    have huDist : dist u a ≤ dist r a := Real.dist_right_le_of_mem_uIcc huIcc
    have hprod : dist (u, r) (a, a) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (huDist.trans_lt hr) hr
    exact le_of_lt (hδbound hprod)
  have hIntBound := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    ‖F r - F a - (r - a) • (-g (a, a))‖ =
        ‖∫ u in r..a, (g (u, r) - g (a, a))‖ := congrArg norm hrem
    _ ≤ c * |a - r| := hIntBound
    _ = c * ‖r - a‖ := by rw [Real.norm_eq_abs, abs_sub_comm]

theorem StartTimeDerivative.hasDerivAt_flow_from_fixed_target
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (a : ℝ) :
    HasDerivAt (fun r => X a x r) (-(b a x)) a := by
  have hflow := flow_continuous_joint_of_smoothPeriodic hb hX
  let g : ℝ × ℝ → Vec 2 := fun p => b p.1 (X p.1 x p.2)
  have hg : Continuous g := by
    have hparam : Continuous (fun p : ℝ × ℝ => (p.1, x, p.2)) := by fun_prop
    exact hb.smooth.continuous.comp (continuous_fst.prodMk (hflow.comp hparam))
  have hformula (r : ℝ) : X a x r = x + ∫ u in r..a, g (u, r) := by
    simpa [g] using flow_eq_initial_add_intervalIntegral hb hX x r a
  have hdiag : HasDerivAt (fun r : ℝ => ∫ u in r..a, g (u, r)) (-g (a, a)) a :=
    StartTimeDerivative.hasDerivAt_diagonalIntervalIntegral hg a
  have hfunc : (fun r => X a x r) =
      (fun r => x + ∫ u in r..a, g (u, r)) := funext hformula
  rw [hfunc]
  simpa [g, hX.1] using hdiag

/-- The derivative with respect to the initial time is the negative spatial
Jacobian applied to the vector field at the initial point. -/
theorem flow_initialTime_hasDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    HasDerivAt (fun r => X t x r)
      (-(fderiv ℝ (fun y => X t y s) x) (b s x)) s := by
  let inner : ℝ → Vec 2 := fun r => X s x r
  let outer : Vec 2 → Vec 2 := fun y => X t y s
  have hinner : HasDerivAt inner (-(b s x)) s := by
    simpa [inner] using StartTimeDerivative.hasDerivAt_flow_from_fixed_target hb hX x s
  have houter : HasFDerivAt outer (fderiv ℝ outer x) x := by
    exact ((flow_spatial_contDiff_one hb hX s t).differentiable (by norm_num) x).hasFDerivAt
  have hinnerVal : inner s = x := by simp [inner, hX.1]
  have hcomp := houter.comp_hasDerivAt_of_eq s hinner hinnerVal.symm
  have hgroup (r : ℝ) : outer (inner r) = X t x r := by
    dsimp [outer, inner]
    exact flow_group_law b (by
      obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
      exact ⟨L, hL⟩) hX x r s t
  have hderiv := hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hgroup r).symm)
  simpa [inner, outer, ContinuousLinearMap.map_neg] using hderiv

end AVenhance.Infra.Flow
