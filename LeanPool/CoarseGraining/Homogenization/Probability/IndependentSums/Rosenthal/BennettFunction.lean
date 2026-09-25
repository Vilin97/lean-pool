/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.IndependentCopy
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.WeakOrlicz

/-! # Bennett Function -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The Bennett function `h(r) = (1 + r) log (1 + r) - r`. -/
noncomputable def bennettH (r : ℝ) : ℝ :=
  (1 + r) * Real.log (1 + r) - r

/-- The Bennett quotient `β(r) = h(r) / r` on `(0, ∞)`. -/
noncomputable def bennettBeta (r : ℝ) : ℝ :=
  bennettH r / r

/-- An explicit universal threshold for the large-scale Bennett lower bound. -/
noncomputable def bennettLargeScaleThreshold : ℝ :=
  Real.exp 4

@[simp] theorem bennettH_zero : bennettH 0 = 0 := by
  simp [bennettH]

theorem hasDerivAt_bennettH {r : ℝ} (hr : r ≠ -1) :
    HasDerivAt bennettH (Real.log (1 + r)) r := by
  have h1r : 1 + r ≠ 0 := by
    intro h
    apply hr
    linarith
  have hshift' :
      HasDerivAt (((fun x : ℝ => x * Real.log x) ∘ HAdd.hAdd 1))
        ((Real.log (1 + r) + 1) * 1) r := by
    exact (Real.hasDerivAt_mul_log (x := 1 + r) h1r).comp r
      ((hasDerivAt_id r).const_add 1)
  have hshift :
      HasDerivAt (fun t : ℝ => (1 + t) * Real.log (1 + t))
        (Real.log (1 + r) + 1) r := by
    have h2 := hshift'
    simp only [mul_one] at h2
    exact h2
  have hsub := hshift.sub (hasDerivAt_id r)
  have hval : Real.log (1 + r) + 1 - 1 = Real.log (1 + r) := by ring
  rw [hval] at hsub
  exact hsub

theorem differentiableAt_bennettH {r : ℝ} (hr : r ≠ -1) :
    DifferentiableAt ℝ bennettH r :=
  (hasDerivAt_bennettH hr).differentiableAt

theorem deriv_bennettH {r : ℝ} (hr : r ≠ -1) :
    deriv bennettH r = Real.log (1 + r) :=
  (hasDerivAt_bennettH hr).deriv

theorem differentiableOn_bennettH :
    DifferentiableOn ℝ bennettH (Set.Ioi (-1 : ℝ)) := by
  intro r hr
  have hr' : (-1 : ℝ) < r := hr
  exact (differentiableAt_bennettH (by
    intro h
    rw [h] at hr'
    exact (lt_irrefl (-1 : ℝ)) hr')).differentiableWithinAt

theorem deriv2_bennettH {r : ℝ} (hr : r ≠ -1) :
    deriv^[2] bennettH r = (1 + r)⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  suffices hEq : ∀ᶠ y in 𝓝 r, deriv bennettH y = Real.log (1 + y) by
    have h1r : 1 + r ≠ 0 := by
      intro h
      apply hr
      linarith
    refine (Filter.EventuallyEq.deriv_eq hEq).trans ?_
    have hlog' :
        HasDerivAt (Real.log ∘ HAdd.hAdd 1) ((1 + r)⁻¹ * 1) r := by
      exact (Real.hasDerivAt_log h1r).comp r ((hasDerivAt_id r).const_add 1)
    have h2 := hlog'.deriv
    simp only [mul_one] at h2
    exact h2
  filter_upwards [eventually_ne_nhds hr] with y hy
  exact deriv_bennettH hy

theorem bennettBeta_eq_slope_mul_log_sub_one {r : ℝ} (hr : r ≠ 0) :
    bennettBeta r = slope (fun x : ℝ => x * Real.log x) 1 (1 + r) - 1 := by
  rw [bennettBeta, slope_def_field, bennettH, Real.log_one]
  field_simp [hr]
  ring

theorem monotoneOn_bennettBeta : MonotoneOn bennettBeta (Set.Ioi 0) := by
  intro r hr s hs hrs
  have hr' : 0 < r := hr
  have hs' : 0 < s := hs
  have hmem_r : 1 + r ∈ {y ∈ Set.Ici (0 : ℝ) | 1 < y} := by
    constructor
    · show 0 ≤ 1 + r
      linarith
    · show 1 < 1 + r
      linarith
  have hmem_s : 1 + s ∈ {y ∈ Set.Ici (0 : ℝ) | 1 < y} := by
    constructor
    · show 0 ≤ 1 + s
      linarith
    · show 1 < 1 + s
      linarith
  have hslope :
      slope (fun x : ℝ => x * Real.log x) 1 (1 + r) ≤
        slope (fun x : ℝ => x * Real.log x) 1 (1 + s) := by
    exact Real.convexOn_mul_log.monotoneOn_slope_gt (by simp)
      hmem_r
      hmem_s
      (by linarith)
  rw [bennettBeta_eq_slope_mul_log_sub_one hr.ne',
    bennettBeta_eq_slope_mul_log_sub_one hs.ne']
  linarith

theorem bennettBeta_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ bennettBeta r := by
  have hslope : 1 ≤ slope (fun x : ℝ => x * Real.log x) 1 (1 + r) := by
    have hderiv : HasDerivAt (fun x : ℝ => x * Real.log x) 1 1 := by
      simpa using (Real.hasDerivAt_mul_log (x := 1) one_ne_zero)
    simpa [Real.log_one] using
      (Real.convexOn_mul_log.le_slope_of_hasDerivAt
        (hx := by simp)
        (hy := by
          show 0 ≤ 1 + r
          linarith)
        (hxy := by
          show 1 < 1 + r
          linarith)
        hderiv)
  rw [bennettBeta_eq_slope_mul_log_sub_one hr.ne']
  linarith

theorem bennettH_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ bennettH r := by
  by_cases hzero : r = 0
  · simp [hzero, bennettH]
  · have hr_pos : 0 < r := lt_of_le_of_ne hr (by simpa [eq_comm] using hzero)
    have hbeta : 0 ≤ bennettBeta r := bennettBeta_nonneg hr_pos
    calc
      0 ≤ r * bennettBeta r := mul_nonneg hr hbeta
      _ = bennettH r := by
        rw [bennettBeta]
        field_simp [hzero]

theorem one_quarter_sq_le_bennettH_of_mem_Icc {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    r ^ (2 : ℕ) / 4 ≤ bennettH r := by
  let k : ℝ → ℝ := fun t => bennettH t - t ^ (2 : ℕ) / 4
  have hk_cont : ContinuousOn k (Set.Icc 0 1) := by
    refine (((Real.continuous_mul_log.comp (continuous_const.add continuous_id')).sub
      continuous_id).sub ((continuous_id.pow 2).div_const (4 : ℝ))).continuousOn
  have hk_diff : DifferentiableOn ℝ k (interior (Set.Icc (0 : ℝ) 1)) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using hx
    have hxne : x ≠ -1 := by
      intro h
      have : (0 : ℝ) < -1 := by simpa [h] using hx'.1
      linarith
    exact ((differentiableAt_bennettH hxne).sub
      ((differentiableAt_id.pow 2).div_const (4 : ℝ))).differentiableWithinAt
  have hk_deriv_nonneg :
      ∀ x ∈ interior (Set.Icc (0 : ℝ) 1), 0 ≤ deriv k x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using hx
    have hxne : x ≠ -1 := by
      intro h
      have : (0 : ℝ) < -1 := by simpa [h] using hx'.1
      linarith
    have hx_nonneg : 0 ≤ x := le_of_lt hx'.1
    have hx_two_pos : 0 < x + 2 := by linarith
    have hquad : deriv (fun t : ℝ => t ^ (2 : ℕ) / 4) x = x / 2 := by
      rw [deriv_div_const]
      rw [deriv_fun_pow (f := fun t : ℝ => t) (x := x) differentiableAt_id 2]
      simp [pow_one, deriv_id'']
      ring
    have hk_deriv : deriv k x = Real.log (1 + x) - x / 2 := by
      have hsub :
          deriv k x = deriv bennettH x - deriv (fun t : ℝ => t ^ (2 : ℕ) / 4) x := by
        show deriv (bennettH - fun t : ℝ => t ^ (2 : ℕ) / 4) x =
            deriv bennettH x - deriv (fun t : ℝ => t ^ (2 : ℕ) / 4) x
        exact deriv_sub (f := bennettH) (g := fun t : ℝ => t ^ (2 : ℕ) / 4)
          (x := x) (hf := differentiableAt_bennettH hxne)
          (hg := (differentiableAt_id.pow 2).div_const (4 : ℝ))
      rw [hsub, deriv_bennettH hxne, hquad]
    have hlog_lower : x / 2 ≤ Real.log (1 + x) := by
      refine le_trans ?_ (Real.le_log_one_add_of_nonneg hx_nonneg)
      field_simp [hx_two_pos.ne']
      nlinarith [hx'.1, hx'.2]
    rw [hk_deriv]
    linarith
  have hk_mono : MonotoneOn k (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hk_cont hk_diff hk_deriv_nonneg
  have hk_nonneg : 0 ≤ k r := by
    have hmono := hk_mono (by simp) hr hr.1
    simpa [k, bennettH] using hmono
  dsimp [k] at hk_nonneg
  linarith

theorem log_sub_one_le_bennettBeta {r : ℝ} (hr : 0 < r) :
    Real.log r - 1 ≤ bennettBeta r := by
  have hcoef : 1 ≤ (1 + r) / r := by
    field_simp [hr.ne']
    nlinarith
  have hlog_mono : Real.log r ≤ Real.log (1 + r) := by
    exact Real.log_le_log hr (by linarith)
  have hlog_nonneg : 0 ≤ Real.log (1 + r) := by
    exact Real.log_nonneg (by linarith)
  have hmul :
      Real.log (1 + r) ≤ ((1 + r) / r) * Real.log (1 + r) := by
    simpa using mul_le_mul_of_nonneg_right hcoef hlog_nonneg
  calc
    Real.log r - 1 ≤ Real.log (1 + r) - 1 := by linarith
    _ ≤ ((1 + r) / r) * Real.log (1 + r) - 1 := by linarith
    _ = bennettBeta r := by
      unfold bennettBeta bennettH
      ring_nf
      field_simp [hr.ne']

theorem two_le_bennettLargeScaleThreshold :
    2 ≤ bennettLargeScaleThreshold := by
  dsimp [bennettLargeScaleThreshold]
  have h : (4 : ℝ) + 1 < Real.exp 4 := by
    exact Real.add_one_lt_exp (show (4 : ℝ) ≠ 0 by norm_num)
  linarith

theorem three_quarters_log_le_bennettBeta_of_bennettLargeScaleThreshold_le {r : ℝ}
    (hr : bennettLargeScaleThreshold ≤ r) :
    (3 / 4 : ℝ) * Real.log r ≤ bennettBeta r := by
  have hr' : Real.exp 4 ≤ r := by
    simpa [bennettLargeScaleThreshold] using hr
  have hr_pos : 0 < r := lt_of_lt_of_le (Real.exp_pos 4) hr'
  have hlog_ge_four : 4 ≤ Real.log r := by
    simpa using (Real.log_le_log (Real.exp_pos 4) hr')
  have hmain : Real.log r - 1 ≤ bennettBeta r :=
    log_sub_one_le_bennettBeta hr_pos
  have hcomp : (3 / 4 : ℝ) * Real.log r ≤ Real.log r - 1 := by
    linarith
  exact hcomp.trans hmain

theorem exists_bennettBeta_ge_three_quarters_log :
    ∃ r0 ∈ Set.Ici (2 : ℝ), ∀ {r : ℝ}, r0 ≤ r →
      (3 / 4 : ℝ) * Real.log r ≤ bennettBeta r := by
  refine ⟨bennettLargeScaleThreshold, two_le_bennettLargeScaleThreshold, ?_⟩
  intro r hr
  exact three_quarters_log_le_bennettBeta_of_bennettLargeScaleThreshold_le hr


end
end IndependentSums
end Homogenization
