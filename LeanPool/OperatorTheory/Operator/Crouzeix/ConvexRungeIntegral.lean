/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Polynomial approximation of continuous exterior Cauchy integrals

This file turns the exterior-kernel Runge theorem into an integral theorem.
A continuous family of kernels is integrated in the Banach space of
continuous functions on the compact set.  Closed-convex-hull approximation
gives finite sampled kernel sums, and a diagonal choice of their polynomial
approximants converges uniformly to the full integral.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ConvexRungeClosure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Compacts

open Complex Filter MeasureTheory Set
open scoped Topology Interval

private theorem exists_finset_sum_tendsto_setIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → E) {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b)) :
    ∃ (s : ℕ → Finset (Ioc a b)) (w : ℕ → Ioc a b → ℝ),
      Tendsto (fun n => ∑ t ∈ s n, w n t • F t) atTop
        (𝓝 (∫ t in Ioc a b, F t)) := by
  let v : Ioc a b → E := fun t => F t
  let S : Set E := Set.range v
  have hmeasure0 : volume (Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc, ENNReal.ofReal_ne_zero_iff]
    exact sub_pos.mpr hab
  have hmeasureTop : volume (Ioc a b) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hIntegrable : IntegrableOn F (Ioc a b) :=
    hF.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have havg : (⨍ t in Ioc a b, F t) ∈ closure (convexHull ℝ S) := by
    apply (convex_convexHull ℝ S).set_average_mem_closure
      hmeasure0 hmeasureTop
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply subset_convexHull ℝ S
      exact ⟨⟨t, ht⟩, rfl⟩
    · exact hIntegrable
  rw [mem_closure_iff_seq_limit] at havg
  obtain ⟨y, hyS, hy⟩ := havg
  have hyrepr : ∀ n, ∃ (sn : Finset (Ioc a b)) (wn : Ioc a b → ℝ),
      (∀ i ∈ sn, 0 ≤ wn i) ∧ sn.sum wn = 1 ∧
        sn.affineCombination ℝ v wn = y n := by
    intro n
    have hn := hyS n
    rw [show S = Set.range v by rfl,
      convexHull_range_eq_exists_affineCombination v] at hn
    exact hn
  choose sn wn _hwn_nonneg hwn_sum hwn using hyrepr
  let scale : ℝ := b - a
  refine ⟨sn, fun n t => scale * wn n t, ?_⟩
  have hscaled : Tendsto (fun n => scale • y n) atTop
        (𝓝 (scale • (⨍ t in Ioc a b, F t))) :=
    hy.const_smul scale
  have hscale : scale = volume.real (Ioc a b) := by
    dsimp only [scale]
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have htarget : scale • (⨍ t in Ioc a b, F t) =
      ∫ t in Ioc a b, F t := by
    rw [hscale]
    exact measure_smul_setAverage F hmeasureTop
  rw [htarget] at hscaled
  convert hscaled using 1
  funext n
  rw [← hwn n,
    Finset.affineCombination_eq_linear_combination _ _ _ (hwn_sum n),
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [v, mul_smul]

/-- A continuous exterior-kernel integral is the compact-uniform limit of
finite kernel sums sampled from its parameter interval. -/
theorem exists_cauchyKernel_finset_tendstoUniformlyOn_setIntegral
    (K : Set ℂ) (hK : IsCompact K)
    (coeff : ℝ → ℂ) (pole : ℝ → ℂ)
    (hcoeff : Continuous coeff) (hpole_cont : Continuous pole)
    (hpole : ∀ t, pole t ∉ K) {a b : ℝ} (hab : a < b) :
    ∃ (s : ℕ → Finset (Ioc a b)) (w : ℕ → Ioc a b → ℝ),
      TendstoUniformlyOn
        (fun n z ↦ ∑ t ∈ s n,
          ((w n t : ℝ) : ℂ) * coeff t * (pole t - z)⁻¹)
        (fun z ↦ ∫ t in Ioc a b, coeff t * (pole t - z)⁻¹)
        atTop K := by
  let Kc : TopologicalSpace.Compacts ℂ := ⟨K, hK⟩
  let F : ℝ → C(Kc, ℂ) := fun t =>
    ⟨fun z => coeff t * (pole t - (z : ℂ))⁻¹, by
      apply Continuous.mul continuous_const
      apply Continuous.inv₀
      · exact continuous_const.sub continuous_subtype_val
      · intro z
        rw [sub_ne_zero]
        intro heq
        apply hpole t
        rw [heq]
        exact z.property⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply Continuous.mul (hcoeff.comp continuous_fst)
    apply Continuous.inv₀
    · exact (hpole_cont.comp continuous_fst).sub
        (continuous_subtype_val.comp continuous_snd)
    · intro x
      rw [sub_ne_zero]
      intro heq
      apply hpole x.1
      rw [heq]
      exact x.2.property
  obtain ⟨s, w, hlim⟩ :=
    exists_finset_sum_tendsto_setIntegral F hab hF.continuousOn
  refine ⟨s, w, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hevent : ∀ᶠ n in atTop,
      dist (∑ t ∈ s n, w n t • F t) (∫ t in Ioc a b, F t) < ε :=
    hlim.eventually (by
      filter_upwards [Metric.ball_mem_nhds
        (∫ t in Ioc a b, F t) hε] with y hy
      simpa only [Metric.mem_ball, dist_comm] using hy)
  have hIntegrable : IntegrableOn F (Ioc a b) :=
    hF.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  filter_upwards [hevent] with n hn z hz
  let zK : Kc := ⟨z, hz⟩
  have hpoint :
      dist ((∑ t ∈ s n, w n t • F t) zK)
          ((∫ t in Ioc a b, F t) zK) ≤
        dist (∑ t ∈ s n, w n t • F t) (∫ t in Ioc a b, F t) :=
    ContinuousMap.dist_apply_le_dist zK
  rw [dist_comm]
  rw [ContinuousMap.integral_apply hIntegrable zK] at hpoint
  have hsum_apply : (∑ t ∈ s n, w n t • F t) zK =
      ∑ t ∈ s n, ((w n t : ℝ) : ℂ) * coeff t *
        (pole t - z)⁻¹ := by
    change (ContinuousMap.evalCLM ℝ zK)
      (∑ t ∈ s n, w n t • F t) = _
    rw [map_sum (ContinuousMap.evalCLM ℝ zK)]
    apply Finset.sum_congr rfl
    intro t _ht
    change (w n t) • (F t zK) = _
    rw [Complex.real_smul]
    dsimp only [F]
    change (w n t : ℂ) * (coeff t * (pole t - z)⁻¹) = _
    ring
  rw [hsum_apply] at hpoint
  exact hpoint.trans_lt hn

private theorem exists_polynomial_tendstoUniformlyOn_of_iterated_limits
    (K : Set ℂ) (f : ℂ → ℂ) (g : ℕ → ℂ → ℂ)
    (hg : TendstoUniformlyOn g f atTop K)
    (hpoly : ∀ n, ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun j z => Polynomial.eval z (q j))
        (g n) atTop K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => Polynomial.eval z (q n))
        f atTop K := by
  choose q hq using hpoly
  have hevent : ∀ n : ℕ, ∀ᶠ j in atTop,
      ∀ z ∈ K, dist (g n z) (Polynomial.eval z (q n j)) <
        1 / ((n : ℝ) + 1) := by
    intro n
    apply (Metric.tendstoUniformlyOn_iff.mp (hq n))
    positivity
  choose N hN using fun n => eventually_atTop.1 (hevent n)
  refine ⟨fun n => q n (N n), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hg_event : ∀ᶠ n in atTop,
      ∀ z ∈ K, dist (f z) (g n z) < ε / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hg) (ε / 2) (by positivity)
  have hrate : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrate_event : ∀ᶠ (n : ℕ) in atTop,
      1 / ((n : ℝ) + 1) < ε / 2 :=
    hrate.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hg_event, hrate_event] with n hgn hn z hz
  calc
    dist (f z) (Polynomial.eval z (q n (N n))) ≤
        dist (f z) (g n z) +
          dist (g n z) (Polynomial.eval z (q n (N n))) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add (hgn z hz) ((hN n (N n) le_rfl z hz).trans hn)
    _ = ε := by ring

/-- A continuous interval integral of Cauchy kernels whose poles stay outside
a compact convex planar set is a compact-uniform limit of polynomials. -/
theorem exists_polynomial_tendstoUniformlyOn_intervalIntegral_mul_inv_sub_of_isCompact_convex
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (coeff pole : ℝ → ℂ) (hcoeff : Continuous coeff)
    (hpole_cont : Continuous pole) (hpole : ∀ t, pole t ∉ K)
    {a b : ℝ} (hab : a < b) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z => Polynomial.eval z (q n))
        (fun z => ∫ t in a..b, coeff t * (pole t - z)⁻¹)
        atTop K := by
  obtain ⟨s, w, hquad⟩ :=
    exists_cauchyKernel_finset_tendstoUniformlyOn_setIntegral
      K hK coeff pole hcoeff hpole_cont hpole hab
  let g : ℕ → ℂ → ℂ := fun n z =>
    ∑ t ∈ s n, ((w n t : ℝ) : ℂ) * coeff t * (pole t - z)⁻¹
  have hquad' : TendstoUniformlyOn g
      (fun z => ∫ t in a..b, coeff t * (pole t - z)⁻¹) atTop K := by
    apply hquad.congr_right
    intro z _hz
    exact (intervalIntegral.integral_of_le hab.le).symm
  apply exists_polynomial_tendstoUniformlyOn_of_iterated_limits K
    (fun z => ∫ t in a..b, coeff t * (pole t - z)⁻¹) g hquad'
  intro n
  exact exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
    (s n) (fun t => ((w n t : ℝ) : ℂ) * coeff t)
      (fun t : Ioc a b => pole t)
      K hK hconvex (fun t _ht => hpole t)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
