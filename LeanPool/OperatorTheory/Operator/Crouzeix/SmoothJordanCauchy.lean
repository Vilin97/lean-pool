/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ContourIntegral
public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothJordanSupport
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cauchy's theorem on smooth convex Jordan domains

A function differentiable in a smooth convex Jordan carrier and continuous
on its closure has zero boundary contour integral.  A Poincaré primitive is
available only in the open carrier, so the proof first integrates along
strict inward homothetic copies of the boundary.  Compact-uniform convergence
of their integrands then transports the zero value to the original contour.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- A scalar function continuous on the closure of a smooth convex Jordan
domain and complex differentiable in its carrier has zero boundary contour
integral. -/
theorem contourIntegral_eq_zero_of_diffContOnCl_smoothJordan
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) :
    contourIntegral f Omega.boundaryParam = 0 := by
  obtain ⟨c, hc⟩ := Omega.carrier_nonempty
  obtain ⟨Fp, hFp⟩ :=
    Omega.strictConvex_carrier.convex.exists_forall_hasDerivWithinAt
      hf.differentiableOn
  let R : TopologicalSpace.Compacts ℝ := ⟨Icc (0 : ℝ) 1, isCompact_Icc⟩
  let T : TopologicalSpace.Compacts ℝ :=
    ⟨Icc (0 : ℝ) (2 * Real.pi), isCompact_Icc⟩
  let inward : R × T → ℂ := fun x =>
    (1 - (x.1 : ℝ)) • Omega.boundaryParam x.2 + (x.1 : ℝ) • c
  have hinward_mem (x : R × T) : inward x ∈ closure Omega.carrier := by
    have hfront : Omega.boundaryParam x.2 ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact ⟨(x.2 : ℝ), rfl⟩
    apply Omega.strictConvex_carrier.convex.closure
      (frontier_subset_closure hfront) (subset_closure hc)
    · exact sub_nonneg.mpr x.1.property.2
    · exact x.1.property.1
    · ring
  have hinward_cont : Continuous inward := by
    dsimp only [inward]
    exact
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (Omega.boundaryParam_contDiff.continuous.comp
          (continuous_subtype_val.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  let J : R × T → ℂ := fun x =>
    ((1 - (x.1 : ℝ)) • deriv Omega.boundaryParam x.2) *
      f (inward x)
  have hJ : Continuous J := by
    dsimp only [J]
    apply Continuous.mul
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        ((Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).comp
          (continuous_subtype_val.comp continuous_snd))
    · exact hf.continuousOn.comp_continuous hinward_cont hinward_mem
  let H : R → C(T, ℂ) := fun r =>
    ⟨fun t => J (r, t), hJ.comp (continuous_const.prodMk continuous_id)⟩
  have hH : Continuous H := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous J
    exact hJ
  let rn : ℕ → R := fun n =>
    ⟨1 / ((n : ℝ) + 1), by
      constructor
      · positivity
      · apply (div_le_one (by positivity)).2
        norm_num⟩
  let rzero : R := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  have hrn : Tendsto rn atTop (𝓝 rzero) := by
    rw [tendsto_subtype_rng]
    simpa only [rn, rzero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hHtendsto : Tendsto (fun n => H (rn n)) atTop (𝓝 (H rzero)) :=
    hH.tendsto rzero |>.comp hrn
  let curve : ℕ → ℝ → ℂ := fun n t =>
    (1 - (rn n : ℝ)) • Omega.boundaryParam t + (rn n : ℝ) • c
  have hrn_pos (n : ℕ) : 0 < (rn n : ℝ) := by
    dsimp only [rn]
    positivity
  have hrn_le (n : ℕ) : (rn n : ℝ) ≤ 1 := (rn n).property.2
  have hcurve_mem (n : ℕ) (t : ℝ) : curve n t ∈ Omega.carrier := by
    have hfront : Omega.boundaryParam t ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    have hcint : c ∈ interior Omega.carrier := by
      rwa [Omega.isOpen_carrier.interior_eq]
    apply interior_subset
    simpa only [curve] using
      Omega.strictConvex_carrier.convex.combo_closure_interior_mem_interior
        (frontier_subset_closure hfront) hcint
        (sub_nonneg.mpr (hrn_le n)) (hrn_pos n) (by ring)
  have hcurve_diff (n : ℕ) (t : ℝ) : DifferentiableAt ℝ (curve n) t := by
    dsimp only [curve]
    exact
      ((Omega.boundaryParam_contDiff.differentiable (by norm_num) t).const_smul
        (1 - (rn n : ℝ))).add (differentiableAt_const _)
  have hcurve_cont (n : ℕ) : Continuous (curve n) := by
    dsimp only [curve]
    have hscale : Continuous (fun _ : ℝ => 1 - (rn n : ℝ)) := continuous_const
    have hrscale : Continuous (fun _ : ℝ => (rn n : ℝ)) := continuous_const
    have hcconst : Continuous (fun _ : ℝ => c) := continuous_const
    exact (hscale.smul Omega.boundaryParam_contDiff.continuous).add
      (hrscale.smul hcconst)
  have hcurve_deriv (n : ℕ) (t : ℝ) :
      deriv (curve n) t =
        (1 - (rn n : ℝ)) • deriv Omega.boundaryParam t := by
    have hgamma :=
      (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
    have hscaled := hgamma.const_smul (1 - (rn n : ℝ))
    have htotal := hscaled.add_const ((rn n : ℝ) • c)
    exact htotal.deriv
  have hcurve_closed (n : ℕ) :
      curve n (2 * Real.pi) = curve n 0 := by
    have hperiod := Omega.boundaryParam_periodic 0
    simpa only [curve, zero_add] using congrArg
      (fun z => (1 - (rn n : ℝ)) • z + (rn n : ℝ) • c) hperiod
  have hcurve_integrable (n : ℕ) : ContourIntegrable f (curve n) := by
    apply ContourIntegrable.of_continuousOn
    · exact (hcurve_cont n).continuousOn
    · rw [show deriv (curve n) = fun t =>
          (1 - (rn n : ℝ)) • deriv Omega.boundaryParam t by
        funext t
        exact hcurve_deriv n t]
      have hscale : Continuous (fun _ : ℝ => 1 - (rn n : ℝ)) := continuous_const
      exact (hscale.smul
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num))).continuousOn
    · apply hf.continuousOn.mono
      rintro z ⟨t, _ht, rfl⟩
      exact subset_closure (hcurve_mem n t)
  have hzero (n : ℕ) : contourIntegral f (curve n) = 0 := by
    apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
      (fun t _ht => hcurve_diff n t)
      (fun t _ht => (hFp _ (hcurve_mem n t)).hasDerivAt
        (Omega.isOpen_carrier.mem_nhds (hcurve_mem n t)))
      (hcurve_integrable n) (hcurve_closed n)
  have huniform : TendstoUniformlyOn
      (fun n t =>
        ((1 - (rn n : ℝ)) • deriv Omega.boundaryParam t) *
          f (curve n t))
      (fun t => deriv Omega.boundaryParam t * f (Omega.boundaryParam t))
      atTop (Icc (0 : ℝ) (2 * Real.pi)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hevent : ∀ᶠ n in atTop,
        H (rn n) ∈ Metric.ball (H rzero) ε :=
      hHtendsto (Metric.ball_mem_nhds (H rzero) hε)
    filter_upwards [hevent] with n hn t ht
    have hn' : dist (H (rn n)) (H rzero) < ε := by
      simpa only [Metric.mem_ball] using hn
    let tT : T := ⟨t, ht⟩
    have hpoint : dist (H (rn n) tT) (H rzero tT) ≤
        dist (H (rn n)) (H rzero) :=
      ContinuousMap.dist_apply_le_dist tT
    have := hpoint.trans_lt hn'
    have hHrn : H (rn n) tT =
        ((1 - (rn n : ℝ)) • deriv Omega.boundaryParam t) *
          f (curve n t) := by
      rfl
    have hHzero : H rzero tT =
        deriv Omega.boundaryParam t * f (Omega.boundaryParam t) := by
      change ((1 - (0 : ℝ)) • deriv Omega.boundaryParam t) *
          f ((1 - (0 : ℝ)) • Omega.boundaryParam t + (0 : ℝ) • c) = _
      simp only [zero_smul, sub_zero, one_smul, add_zero]
    rw [hHrn, hHzero] at this
    simpa only [dist_comm] using this
  have hcont (n : ℕ) : ContinuousOn
      (fun t =>
        ((1 - (rn n : ℝ)) • deriv Omega.boundaryParam t) *
          f (curve n t))
      (Icc (0 : ℝ) (2 * Real.pi)) := by
    have hfcurve : ContinuousOn (fun t => f (curve n t))
        (Icc (0 : ℝ) (2 * Real.pi)) :=
      hf.continuousOn.comp (hcurve_cont n).continuousOn
        (fun t _ht => subset_closure (hcurve_mem n t))
    have hscale : Continuous (fun _ : ℝ => 1 - (rn n : ℝ)) := continuous_const
    exact
      ((hscale.smul
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num))).continuousOn).mul
          hfcurve
  have huniform' : TendstoUniformlyOn
      (fun n t =>
        ((1 - (rn n : ℝ)) • deriv Omega.boundaryParam t) *
          f (curve n t))
      (fun t => deriv Omega.boundaryParam t * f (Omega.boundaryParam t))
      atTop [[(0 : ℝ), 2 * Real.pi]] := by
    rw [uIcc_of_le Real.two_pi_pos.le]
    exact huniform
  have hintegral :=
    huniform'.tendsto_intervalIntegral_of_continuousOn (μ := volume)
      (Eventually.of_forall fun n => by
        rw [uIcc_of_le Real.two_pi_pos.le]
        exact hcont n)
  have hcontour : Tendsto (fun n => contourIntegral f (curve n)) atTop
      (𝓝 (contourIntegral f Omega.boundaryParam)) := by
    unfold contourIntegral
    simpa only [hcurve_deriv, smul_eq_mul] using hintegral
  have hcontour_zero : Tendsto (fun n => contourIntegral f (curve n)) atTop
      (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hcontour hcontour_zero

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
