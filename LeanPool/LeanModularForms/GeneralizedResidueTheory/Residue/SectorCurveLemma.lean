/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.SectorCurve

/-!
# Sector Curve PV Lemmas

Higher-order PV computations and the generalized winding number for the
model sector-curve defined in `SectorCurve.lean`.

## Main Results

* `pv_sector_higher_power` -- for n >= 1, `PV int z^{n-1} dz = 0` (angle condition)
* `cauchyPV_sectorCurve_simplePole` -- Lemma 3.1 for simple poles: PV = `I * alpha * residue`
* `cauchyPV_sectorCurve_eq_mul_residueSimplePole` -- variant for arbitrary `f = c/z + g`
* `pv_sector_negative_power` -- Equation (3.4): PV of `z^{-n}` is 0 under angle condition
* `generalizedWindingNumber_sectorCurve` -- winding number equals `alpha / (2 * pi)`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private theorem sectorCurve_differentiableAt_off_knots (r : ℝ) (α : ℝ)
    (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 3) (ht_not : t ∉ ({1, 2} : Set ℝ)) :
    DifferentiableAt ℝ (sectorCurve r α) t := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_not
  rcases lt_or_gt_of_ne ht_not.1 with h1 | h1
  · have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => (↑(s * r) : ℂ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      simp only [sectorCurve, if_pos (le_of_lt (mem_Iio.mp hs))]
    exact h_eq.differentiableAt_iff.mpr
      ((hasDerivAt_id t).mul_const r).ofReal_comp.differentiableAt
  · rcases lt_or_gt_of_ne ht_not.2 with h2 | h2
    · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
          fun s => (↑r : ℂ) * exp (I * ↑((s - 1) * α)) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with s hs
        exact sectorCurve_seg2 r α s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      refine h_eq.differentiableAt_iff.mpr ?_
      apply DifferentiableAt.const_mul; apply DifferentiableAt.cexp
      apply DifferentiableAt.const_mul
      exact (((hasDerivAt_id t).sub
        (hasDerivAt_const t (1 : ℝ))).mul_const α).ofReal_comp.differentiableAt
    · have h_eq : sectorCurve r α =ᶠ[𝓝 t]
          fun s => (↑((3 - s) * r) : ℂ) * exp (I * ↑α) := by
        filter_upwards [Ioi_mem_nhds h2] with s hs
        simp only [sectorCurve,
          if_neg (not_le.mpr (lt_trans one_lt_two (mem_Ioi.mp hs))),
          if_neg (not_le.mpr (mem_Ioi.mp hs))]
      refine h_eq.differentiableAt_iff.mpr ?_
      apply DifferentiableAt.mul_const
      exact (((hasDerivAt_const t (3 : ℝ)).sub
        (hasDerivAt_id t)).mul_const r).ofReal_comp.differentiableAt

private theorem pow_integrableOn_01 (r : ℝ) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) *
      deriv (sectorCurve r α) t) volume 0 1 :=
  ((show ContinuousOn (fun t => (↑(t * r) : ℂ) ^ (n - 1) * (↑r : ℂ))
    (Set.uIcc 0 1) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ht])

private theorem pow_integrableOn_12 (r : ℝ) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) *
      deriv (sectorCurve r α) t) volume 1 2 :=
  ((show ContinuousOn (fun t => ((↑r : ℂ) * exp (I * ↑((t - 1) * α))) ^ (n - 1) *
      (↑r * (I * ↑α) * exp (I * ↑((t - 1) * α))))
    (Set.uIcc 1 2) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht])

private theorem pow_integrableOn_23 (r : ℝ) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (n - 1) *
      deriv (sectorCurve r α) t) volume 2 3 :=
  ((show ContinuousOn (fun t => ((↑((3 - t) * r) : ℂ) * exp (I * ↑α)) ^ (n - 1) *
      (-(↑r : ℂ) * exp (I * ↑α)))
    (Set.uIcc 2 3) by rw [Set.uIcc_of_le (by norm_num)]; fun_prop).intervalIntegrable).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg3 r α t ht])

/-- For `n >= 1`, the integral of `z^(n-1) dz` along the sector curve is 0
when `n * alpha` is a multiple of `2 * pi`. -/
theorem pv_sector_higher_power (r : ℝ) (_hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi)
    (n : ℕ) (hn : 1 ≤ n) (_h_angle : ∃ k : ℤ, n * α = k * (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..3,
      (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t = 0 := by
  set f : ℝ → ℂ := fun t =>
    (sectorCurve r α t) ^ (n - 1) * deriv (sectorCurve r α) t
  set F : ℝ → ℂ := fun t => (sectorCurve r α t) ^ n / (↑n : ℂ)
  have hF_cont : ContinuousOn F (Icc 0 3) :=
    ((sectorCurve_continuousOn r α).pow n).div_const _
  have hS_count : ({1, 2} ∩ Ioo (0 : ℝ) 3 : Set ℝ).Countable :=
    (Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable
  have hγ_diff : ∀ t ∈ Ioo (0 : ℝ) 3,
      t ∉ ({1, 2} : Set ℝ) → DifferentiableAt ℝ (sectorCurve r α) t :=
    sectorCurve_differentiableAt_off_knots r α
  have hF_deriv : ∀ t ∈ Ioo (0 : ℝ) 3 \ ({1, 2} ∩ Ioo (0 : ℝ) 3),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not' : t ∉ ({1, 2} : Set ℝ) := fun h => ht_not ⟨h, ht⟩
    change HasDerivAt F (sectorCurve r α t ^ (n - 1) * deriv (sectorCurve r α) t) t
    convert ((hγ_diff t ht ht_not').hasDerivAt.pow n).div_const (↑n : ℂ) using 1
    rw [mul_assoc, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (by omega) : (↑n : ℂ) ≠ 0)]
  have hf_int : IntervalIntegrable f volume 0 3 :=
    (pow_integrableOn_01 r α n).trans (pow_integrableOn_12 r α n) |>.trans
      (pow_integrableOn_23 r α n)
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f (by norm_num : (0 : ℝ) ≤ 3) hS_count hF_cont hF_deriv hf_int]
  change F 3 - F 0 = 0
  simp only [F, sectorCurve_zero, sectorCurve_three, zero_pow (by omega : n ≠ 0),
    zero_div, sub_self]

private theorem sectorCurve_mem_ball (r : ℝ) (hr : 0 < r) (α : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) 3, sectorCurve r α t ∈ Metric.ball (0 : ℂ) (↑r + 1) := by
  have norm_exp_I : ∀ (x : ℝ), ‖Complex.exp (I * ↑x)‖ = 1 := by
    intro x; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  intro t ⟨ht0, ht3⟩
  simp only [Metric.mem_ball, dist_zero_right]
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_seg1 r α t ⟨ht0, h1⟩, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hr.le)]
    nlinarith
  · rcases le_or_gt t 2 with h2 | h2
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt h1, h2⟩, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        norm_exp_I, mul_one]
      linarith
    · rw [sectorCurve_seg3 r α t ⟨le_of_lt h2, ht3⟩, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith) hr.le),
        norm_exp_I, mul_one]
      nlinarith

private theorem φ_sectorCurve_integrableOn_01 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 0 1 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  have hc : ContinuousOn (fun t : ℝ => g ((t * r : ℝ) : ℂ) * (r : ℂ)) (Icc 0 1) := by
    apply ContinuousOn.mul
    · exact hg.continuousOn.comp
        ((continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousOn)
        (fun t ht => by
          have := hγ_in_ball t ⟨ht.1, by linarith [ht.2]⟩
          rwa [sectorCurve_seg1 r α t ht] at this)
    · exact continuousOn_const
  exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ht])

private theorem φ_sectorCurve_integrableOn_12 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 1 2 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  have hc : ContinuousOn (fun t : ℝ => g ((r : ℂ) * exp (I * ((t - 1) * α : ℝ))) *
      ((r : ℂ) * (I * (α : ℂ)) * exp (I * ((t - 1) * α : ℝ)))) (Icc 1 2) := by
    apply ContinuousOn.mul
    · exact hg.continuousOn.comp
        ((continuous_const.mul (continuous_exp.comp
          (continuous_const.mul (continuous_ofReal.comp
            ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn)
        (fun t ht => by
          have := hγ_in_ball t ⟨by linarith [ht.1], by linarith [ht.2]⟩
          rwa [sectorCurve_seg2 r α t ht] at this)
    · exact (continuous_const.mul (continuous_exp.comp
        (continuous_const.mul (continuous_ofReal.comp
          ((continuous_id.sub continuous_const).mul continuous_const))))).continuousOn
  exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht])

private theorem φ_sectorCurve_integrableOn_23 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 2 3 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  have hc : ContinuousOn (fun t : ℝ => g (((3 - t) * r : ℝ) * exp (I * (α : ℂ))) *
      (-(r : ℂ) * exp (I * (α : ℂ)))) (Icc 2 3) := by
    apply ContinuousOn.mul
    · exact hg.continuousOn.comp
        ((continuous_ofReal.comp ((continuous_const.sub continuous_id).mul
          continuous_const)).mul continuous_const).continuousOn
        (fun t ht => by
          have := hγ_in_ball t ⟨by linarith [ht.1], ht.2⟩
          rwa [sectorCurve_seg3 r α t ht] at this)
    · exact continuousOn_const
  exact (hc.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg3 r α t ht])

private theorem φ_sectorCurve_intervalIntegrable (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    IntervalIntegrable (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t)
      volume 0 3 :=
  (φ_sectorCurve_integrableOn_01 r hr α g hg).trans
    (φ_sectorCurve_integrableOn_12 r hr α g hg) |>.trans
    (φ_sectorCurve_integrableOn_23 r hr α g hg)

/-- The integral of an analytic function along the sector curve is zero,
because the sector starts and ends at 0, and analytic functions on
a convex open set have primitives. -/
private theorem integral_analytic_sectorCurve_eq_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    ∫ t in (0 : ℝ)..3, g (sectorCurve r α t) * deriv (sectorCurve r α) t = 0 := by
  have hγ_in_ball := sectorCurve_mem_ball r hr α
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive (convex_ball 0 _) Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (by positivity)⟩ hg.differentiableOn
  have hF_contOn : ContinuousOn F (Metric.ball (0 : ℂ) (↑r + 1)) :=
    fun z hz => (hF z hz).continuousAt.continuousWithinAt
  have hF_deriv : ∀ t ∈ Ioo (0 : ℝ) 3 \ ({1, 2} ∩ Ioo 0 3),
      HasDerivAt (F ∘ sectorCurve r α)
        (g (sectorCurve r α t) * deriv (sectorCurve r α) t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not' : t ∉ ({1, 2} : Set ℝ) := fun h => ht_not ⟨h, ht⟩
    exact (hF _ (hγ_in_ball t (Ioo_subset_Icc_self ht))).comp_of_eq t
      (sectorCurve_differentiableAt_off_knots r α t ht ht_not').hasDerivAt rfl
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (F ∘ sectorCurve r α) _ (by norm_num : (0 : ℝ) ≤ 3)
    ((Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable)
    (hF_contOn.comp (sectorCurve_continuousOn r α) hγ_in_ball) hF_deriv
    (φ_sectorCurve_intervalIntegrable r hr α g hg),
    Function.comp_apply, Function.comp_apply,
    sectorCurve_zero, sectorCurve_three, sub_self]

private theorem cauchyPV_g_aestronglyMeasurable (r : ℝ) (α : ℝ)
    (g : ℂ → ℂ) (ε : ℝ)
    (h_int_g : IntervalIntegrable (fun t => g (sectorCurve r α t) *
      deriv (sectorCurve r α) t) volume 0 3) :
    AEStronglyMeasurable
      (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε)
      (volume.restrict (Ioc 0 3)) := by
  exact (h_int_g.aestronglyMeasurable.indicator
    (measurableSet_pv_support (sectorCurve r α) 0 3 0 ε
      (sectorCurve_continuousOn r α))).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [cauchyPrincipalValueIntegrand', Set.indicator_apply]
    by_cases h : ‖sectorCurve r α t - 0‖ > ε
    · rw [if_pos (show t ∈ {t | ε < ‖sectorCurve r α t - 0‖} ∩ Icc 0 3 from
        ⟨h, Ioc_subset_Icc_self ht⟩), if_pos h]
    · rw [if_neg (show t ∉ {t | ε < ‖sectorCurve r α t - 0‖} ∩ Icc 0 3 from
        fun ⟨hm, _⟩ => h hm), if_neg h])

private theorem cauchyPV_g_norm_le (r : ℝ) (α : ℝ)
    (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    ‖cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t‖ ≤
    ‖g (sectorCurve r α t) * deriv (sectorCurve r α) t‖ := by
  simp only [cauchyPrincipalValueIntegrand', sub_zero]
  split_ifs with h
  · exact le_refl _
  · rw [norm_zero]; exact norm_nonneg _

private theorem sectorCurve_zero_set_finite (r : ℝ) (hr : 0 < r) (α : ℝ) :
    Set.Finite ({t ∈ Icc (0 : ℝ) 3 | sectorCurve r α t = 0}) := by
  apply Set.Finite.subset (Set.toFinite {(0 : ℝ), 3})
  intro t ⟨⟨ht0, ht3⟩, h0⟩
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_seg1 r α t ⟨ht0, h1⟩] at h0
    simp only [Complex.ofReal_eq_zero] at h0
    simp [(mul_eq_zero.mp h0).resolve_right hr.ne']
  · rcases le_or_gt t 2 with h2 | h2
    · exfalso; rw [sectorCurve_seg2 r α t ⟨le_of_lt h1, h2⟩] at h0
      simp only [mul_eq_zero, Complex.ofReal_eq_zero] at h0
      exact h0.elim (fun h => by linarith) (Complex.exp_ne_zero _)
    · rw [sectorCurve_seg3 r α t ⟨le_of_lt h2, ht3⟩] at h0
      simp only [mul_eq_zero, Complex.ofReal_eq_zero] at h0
      exact h0.elim (fun h => by
        rcases h with h | h
        · simp [show t = 3 from by linarith]
        · exact absurd h hr.ne') (fun h => absurd h (Complex.exp_ne_zero _))

private theorem cauchyPV_g_intervalIntegrable (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) (ε : ℝ) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε)
      volume 0 3 := by
  have h_int_g := φ_sectorCurve_intervalIntegrable r hr α g hg
  apply h_int_g.mono_fun
  · rw [show Ι (0 : ℝ) 3 = Ioc 0 3 from uIoc_of_le (by norm_num)]
    exact (cauchyPV_g_aestronglyMeasurable r α g ε h_int_g)
  · filter_upwards with t; exact cauchyPV_g_norm_le r α g ε t

private theorem cauchyPV_inv_integrableOn_0δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 0 (ε / r) := by
  exact (intervalIntegrable_const (c := (0 : ℂ))).congr (fun t ht => by
    rw [Set.uIoc_of_le (div_pos hε_pos hr).le] at ht
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_neg (not_lt.mpr _)]
    rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt ht.1,
      le_trans ht.2 (le_of_lt (by rwa [div_lt_one hr] : ε / r < 1))⟩]
    exact le_trans (mul_le_mul_of_nonneg_right ht.2 hr.le)
      (le_of_eq (div_mul_cancel₀ ε (ne_of_gt hr))))

private theorem cauchyPV_inv_integrableOn_3δ3 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume (3 - ε / r) 3 := by
  exact (intervalIntegrable_const (c := (0 : ℂ))).congr (fun t ht => by
    have hεr_pos : ε / r > 0 := div_pos hε_pos hr
    have hεr_lt_one : ε / r < 1 := (div_lt_one hr).mpr hε_lt_r
    rw [Set.uIoc_of_le (by linarith : 3 - ε / r ≤ 3)] at ht
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_neg (not_lt.mpr _)]
    rw [sectorCurve_norm_seg3' r hr α t ⟨by linarith [ht.1], ht.2⟩]
    have : (3 - t) * r ≤ ε / r * r :=
      mul_le_mul_of_nonneg_right (by linarith [ht.1]) hr.le
    linarith [div_mul_cancel₀ ε (ne_of_gt hr)])

private theorem cauchyPV_inv_integrableOn_δ1 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume (ε / r) 1 := by
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε_pos hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have hcont : ContinuousOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Set.uIcc δ 1) := by
    intro t ht; rw [Set.uIcc_of_le hδ1.le] at ht
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_inv₀ (ne_of_gt (lt_of_lt_of_le hδ ht.1)))).continuousWithinAt
  rw [intervalIntegrable_iff, Set.uIoc_of_le hδ1.le]
  have h_eq : ∀ t ∈ Ioo δ (1 : ℝ),
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
      (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_pos]; · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
    · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
      have hδr : δ * r = ε := div_mul_cancel₀ ε (ne_of_gt hr)
      calc ε = δ * r := hδr.symm
        _ < t * r := by nlinarith
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo δ 1)),
      (fun t : ℝ => (↑(t⁻¹) : ℂ)) t =
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  have h_int : IntegrableOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Ioc δ 1) volume := by
    rw [show (Ioc δ 1) = Set.uIoc δ 1 from (Set.uIoc_of_le hδ1.le).symm]
    exact intervalIntegrable_iff.mp hcont.intervalIntegrable
  exact Integrable.congr h_int h1

private theorem cauchyPV_inv_integrableOn_12 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 1 2 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  have h_eq : ∀ t ∈ Ioo (1 : ℝ) 2,
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
      I * ↑α := fun t ⟨ht1, ht2⟩ => by
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_pos]; · exact pv_integrand_seg2 r hr α t ⟨ht1, ht2⟩
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩]
      simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      rw [Complex.norm_of_nonneg (le_of_lt hr)]; exact hε_lt_r
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (1 : ℝ) 2)),
      (fun _ => I * (↑α : ℂ)) t =
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  exact Integrable.congr (integrableOn_const (hs := measure_Ioc_lt_top.ne)) h1

private theorem cauchyPV_inv_integrableOn_2_3δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 2 (3 - ε / r) := by
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε_pos hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h3δ : 2 < 3 - δ := by linarith
  have hcont : ContinuousOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ))
      (Set.uIcc 2 (3 - δ)) := by
    rw [Set.uIcc_of_le h3δ.le]
    intro t ht
    exact (continuous_neg.continuousAt.comp
      (Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_inv₀ (ne_of_gt (by linarith [ht.2] : (0 : ℝ) < 3 - t))).comp
         (continuousAt_const.sub continuousAt_id)))).continuousWithinAt
  rw [intervalIntegrable_iff, Set.uIoc_of_le h3δ.le]
  have h_eq : ∀ t ∈ Ioo (2 : ℝ) (3 - δ),
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t =
      -(↑((3 - t)⁻¹) : ℂ) := fun t ⟨ht2, ht3δ⟩ => by
    simp only [cauchyPrincipalValueIntegrand', sub_zero]
    rw [if_pos]
    · rw [sectorCurve_seg3 r α t ⟨le_of_lt ht2, by linarith⟩,
          deriv_sectorCurve_seg3 r α t ⟨ht2, by linarith⟩]
      have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      have : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
      have : (3 - t : ℝ) ≠ 0 := by linarith
      push_cast; field_simp
    · rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt ht2, by linarith⟩]
      have hδr : δ * r = ε := div_mul_cancel₀ ε (ne_of_gt hr)
      calc ε = δ * r := hδr.symm
        _ < (3 - t) * r := by nlinarith
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (2 : ℝ) (3 - δ))),
      (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ)) t =
      cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  have h_int : IntegrableOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ)) (Ioc 2 (3 - δ))
      volume := by
    rw [show Ioc 2 (3 - δ) = Set.uIoc 2 (3 - δ) from (Set.uIoc_of_le h3δ.le).symm]
    exact intervalIntegrable_iff.mp hcont.intervalIntegrable
  exact Integrable.congr h_int h1

private theorem cauchyPV_inv_intervalIntegrable (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε) volume 0 3 :=
  ((cauchyPV_inv_integrableOn_0δ r hr α ε hε_pos hε_lt_r).trans
    (cauchyPV_inv_integrableOn_δ1 r hr α ε hε_pos hε_lt_r)).trans
    (cauchyPV_inv_integrableOn_12 r hr α ε hε_lt_r) |>.trans
    (cauchyPV_inv_integrableOn_2_3δ r hr α ε hε_pos hε_lt_r) |>.trans
    (cauchyPV_inv_integrableOn_3δ3 r hr α ε hε_pos hε_lt_r)

private theorem cauchyPV_g_tendsto_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..3,
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 0) := by
  have h_int_g := φ_sectorCurve_intervalIntegrable r hr α g hg
  suffices h : Tendsto (fun ε => ∫ t in (0 : ℝ)..3,
      cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..3,
        (fun t => g (sectorCurve r α t) * deriv (sectorCurve r α) t) t)) by
    rwa [integral_analytic_sectorCurve_eq_zero r hr α g hg] at h
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖g (sectorCurve r α t) * deriv (sectorCurve r α) t‖)
    (by filter_upwards [self_mem_nhdsWithin] with ε _
        rw [show Ι (0 : ℝ) 3 = Ioc 0 3 from uIoc_of_le (by norm_num)]
        exact cauchyPV_g_aestronglyMeasurable r α g ε h_int_g)
    (by filter_upwards [self_mem_nhdsWithin] with ε _
        exact Eventually.of_forall fun t _ => cauchyPV_g_norm_le r α g ε t)
    h_int_g.norm
    (by filter_upwards [(sectorCurve_zero_set_finite r hr α).countable.ae_notMem _]
          with t ht ht_uIoc
        have h_ne : sectorCurve r α t ≠ 0 := fun heq =>
          ht ⟨Ioc_subset_Icc_self (uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3) ▸ ht_uIoc), heq⟩
        exact tendsto_const_nhds.congr' (by
          filter_upwards [Ioo_mem_nhdsGT
            (norm_pos_iff.mpr (sub_ne_zero.mpr h_ne))] with ε hε
          simp only [cauchyPrincipalValueIntegrand', sub_zero, gt_iff_lt]
          rw [if_pos (by rw [sub_zero] at hε; exact hε.2)]))

private theorem cauchyPV_simplePole_integral_split (r : ℝ) (hr : 0 < r) (α : ℝ)
    (c : ℂ) (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    ∀ᶠ ε in 𝓝[>] 0,
      (∫ t in (0 : ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
        (sectorCurve r α) 0 ε t) =
      c * (∫ t in (0 : ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
        (sectorCurve r α) 0 ε t) +
      (∫ t in (0 : ℝ)..3, cauchyPrincipalValueIntegrand' g
        (sectorCurve r α) 0 ε t) := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hr] with ε hε_lt_r hε_pos
  simp only [mem_Ioi] at hε_pos
  have h_decomp : ∀ t, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
      (sectorCurve r α) 0 ε t =
    c * cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t +
    cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t := by
    intro t; simp only [cauchyPrincipalValueIntegrand', sub_zero, div_eq_mul_inv]
    split_ifs <;> ring
  rw [show (∫ t in (0 : ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
      (sectorCurve r α) 0 ε t) =
    ∫ t in (0 : ℝ)..3, (c * cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε t +
    cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε t) from
    intervalIntegral.integral_congr (fun t _ => h_decomp t)]
  rw [show c * ∫ t in (0 : ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε t =
    ∫ t in (0 : ℝ)..3, c * cauchyPrincipalValueIntegrand' (fun z => z⁻¹)
      (sectorCurve r α) 0 ε t from
    (intervalIntegral.integral_const_mul c _).symm]
  exact intervalIntegral.integral_add
    ((cauchyPV_inv_intervalIntegrable r hr α ε hε_pos hε_lt_r).const_mul c)
    (cauchyPV_g_intervalIntegrable r hr α g hg ε)

/-- **Lemma 3.1 (Simple pole version)**:
For `f(z) = c/z + g(z)` where `g` is analytic on a ball containing the sector,
the principal value along the sector curve equals `I * α * c`.

The hypotheses require `g` analytic on a ball strictly containing the sector image
(to guarantee a primitive exists) and `f = c/z + g` at all nonzero points. -/
theorem cauchyPV_sectorCurve_simplePole (r : ℝ) (hr : 0 < r) (α : ℝ)
    (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2 * Real.pi)
    (c : ℂ) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1))) :
    CauchyPrincipalValueExists' (fun z => c / z + g z) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => c / z + g z) (sectorCurve r α) 0 3 0 = I * ↑α * c := by
  have hpv_inv := pv_sector_dz_over_z r hr α hα_nonneg hα_le
  obtain ⟨L_inv, hL_inv⟩ := hpv_inv.1
  rw [show L_inv = I * ↑α from hL_inv.limUnder_eq.symm.trans hpv_inv.2] at hL_inv
  have h_tendsto : Tendsto (fun ε => ∫ t in (0 : ℝ)..3,
      cauchyPrincipalValueIntegrand' (fun z => c / z + g z) (sectorCurve r α) 0 ε t)
      (𝓝[>] 0) (𝓝 (I * ↑α * c)) := by
    rw [show I * ↑α * c = c * (I * ↑α) + 0 from by ring]
    exact ((hL_inv.const_mul c).add (cauchyPV_g_tendsto_zero r hr α g hg)).congr'
      ((cauchyPV_simplePole_integral_split r hr α c g hg).mono (fun _ h => h.symm))
  refine ⟨⟨_, h_tendsto⟩, ?_⟩
  exact h_tendsto.limUnder_eq

/-- Variant of Lemma 3.1: for an arbitrary `f` equal to `c/z + g` at nonzero points,
with `g` analytic on a ball containing the sector, the PV equals `I * α * c`. -/
theorem cauchyPV_sectorCurve_eq_mul_residueSimplePole (r : ℝ) (hr : 0 < r) (α : ℝ)
    (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2 * Real.pi)
    (f : ℂ → ℂ) (c : ℂ) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (↑r + 1)))
    (hf_eq : ∀ z, z ≠ 0 → f z = c / z + g z)
    (hc : c = residueSimplePole f 0) :
    CauchyPrincipalValueExists' f (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' f (sectorCurve r α) 0 3 0 = I * ↑α * residueSimplePole f 0 := by
  have h_eq : ∀ ε > 0, ∀ t,
      (if ε < ‖sectorCurve r α t - 0‖
        then f (sectorCurve r α t) * deriv (sectorCurve r α) t
        else 0) =
      (if ε < ‖sectorCurve r α t - 0‖
        then (c / sectorCurve r α t + g (sectorCurve r α t)) *
          deriv (sectorCurve r α) t
        else 0) := by
    intro ε hε t; split_ifs with h
    · have hne : sectorCurve r α t ≠ 0 := by
        intro heq; simp [heq] at h; linarith
      rw [hf_eq _ hne]
    · rfl
  have h_sp := cauchyPV_sectorCurve_simplePole r hr α hα_nonneg hα_le c g hg
  have h_int_eq : ∀ᶠ ε in 𝓝[>] 0,
      (∫ t in (0 : ℝ)..3, cauchyPrincipalValueIntegrand' f (sectorCurve r α) 0 ε t) =
      (∫ t in (0 : ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => c / z + g z)
        (sectorCurve r α) 0 ε t) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    congr 1; ext t; exact h_eq ε (mem_Ioi.mp hε) t
  obtain ⟨L, hL⟩ := h_sp.1
  refine ⟨⟨L, hL.congr' (h_int_eq.mono (fun _ h => h.symm))⟩, ?_⟩
  have hpv_f : cauchyPrincipalValue' f (sectorCurve r α) 0 3 0 = L :=
    (hL.congr' (h_int_eq.mono (fun _ h => h.symm))).limUnder_eq
  have hpv_cg : cauchyPrincipalValue' (fun z => c / z + g z)
      (sectorCurve r α) 0 3 0 = L := hL.limUnder_eq
  rw [hpv_f, ← hpv_cg, h_sp.2, hc]

private theorem sectorCurve_ne_zero_of_Icc_δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) :
    ∀ t ∈ Icc δ (3 - δ), sectorCurve r α t ≠ 0 := by
  intro t ht h0
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_seg1 r α t ⟨le_trans hδ_pos.le ht.1, h1⟩] at h0
    have : t * r = 0 := Complex.ofReal_eq_zero.mp h0
    rcases mul_eq_zero.mp this with ht0 | hr0
    · linarith [ht.1]
    · linarith
  · rcases le_or_gt t 2 with h2 | h2
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt h1, h2⟩] at h0
      rcases mul_eq_zero.mp h0 with hr0 | hexp0
      · exact absurd (Complex.ofReal_eq_zero.mp hr0) (ne_of_gt hr)
      · exact absurd hexp0 (Complex.exp_ne_zero _)
    · rw [sectorCurve_seg3 r α t ⟨le_of_lt h2, by linarith [ht.2]⟩] at h0
      rcases mul_eq_zero.mp h0 with h3t | hexp0
      · have : (3 - t) * r = 0 := Complex.ofReal_eq_zero.mp h3t
        rcases mul_eq_zero.mp this with ht3 | hr0
        · linarith [ht.2]
        · linarith
      · exact absurd hexp0 (Complex.exp_ne_zero _)

private theorem sectorCurve_norm_le_near_zero (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (_hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ * r = ε) :
    ∀ t ∈ Icc 0 δ, ‖sectorCurve r α t‖ ≤ ε := by
  intro t ht
  rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1, le_trans ht.2 hδ_lt_1.le⟩]
  calc t * r ≤ δ * r := mul_le_mul_of_nonneg_right ht.2 hr.le
    _ = ε := hδr_eq

private theorem sectorCurve_norm_le_near_three (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_lt_1 : δ < 1) (ε : ℝ) (hδr_eq : δ * r = ε) :
    ∀ t ∈ Icc (3 - δ) 3, ‖sectorCurve r α t‖ ≤ ε := by
  intro t ht
  rw [sectorCurve_norm_seg3' r hr α t ⟨le_trans (by linarith : 2 ≤ 3 - δ) ht.1, ht.2⟩]
  calc (3 - t) * r ≤ δ * r := by
        apply mul_le_mul_of_nonneg_right _ hr.le; linarith [ht.1]
    _ = ε := hδr_eq

private theorem sectorCurve_norm_gt_mid (r : ℝ) (hr : 0 < r) (α : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_lt_1 : δ < 1) (ε : ℝ) (hε_lt_r : ε < r)
    (hδr_eq : δ * r = ε) :
    ∀ t ∈ Ioo δ (3 - δ), ε < ‖sectorCurve r α t‖ := by
  intro t ht
  rcases le_or_gt t 1 with h1 | h1
  · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ_pos ht.1), h1⟩]
    calc ε = δ * r := hδr_eq.symm
      _ < t * r := mul_lt_mul_of_pos_right ht.1 hr
  · rcases le_or_gt t 2 with h2 | h2
    · have : ‖sectorCurve r α t‖ = r :=
        sectorCurve_norm_on_arc r hr α t ⟨le_of_lt h1, h2⟩
      rw [this]; exact hε_lt_r
    · rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt h2, by linarith [ht.2]⟩]
      calc ε = δ * r := hδr_eq.symm
        _ < (3 - t) * r := by
          apply mul_lt_mul_of_pos_right _ hr; linarith [ht.2]

private theorem zpow_integrableOn_δ1 (r : ℝ) (hr : 0 < r) (α : ℝ)
    (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume δ 1 := by
  have : ContinuousOn (fun t => (↑(t * r) : ℂ) ^ (-(↑n : ℤ)) * (↑r : ℂ))
      (Icc δ 1) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.zpow₀
      · fun_prop
      · intro t ht
        left; exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (lt_of_lt_of_le hδ_pos ht.1) hr))
    · exact continuousOn_const
  exact (this.intervalIntegrable_of_Icc hδ_lt_1.le).congr_ae (by
    rw [Set.uIoc_of_le hδ_lt_1.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg1 r α t ⟨le_of_lt (lt_trans hδ_pos ht.1), le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ⟨lt_trans hδ_pos ht.1, ht.2⟩])

private theorem zpow_integrableOn_12 (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume 1 2 := by
  have : ContinuousOn (fun t => (↑r * exp (I * ↑((t - 1) * α))) ^ (-(↑n : ℤ)) *
      (↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)))) (Icc 1 2) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.zpow₀
      · fun_prop
      · intro t _; left
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) (Complex.exp_ne_zero _)
    · fun_prop
  exact (this.intervalIntegrable_of_Icc (by norm_num)).congr_ae (by
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht])

private theorem zpow_integrableOn_23δ (r : ℝ) (hr : 0 < r) (α : ℝ)
    (n : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    IntervalIntegrable (fun t => (sectorCurve r α t) ^ (-(↑n : ℤ)) *
      deriv (sectorCurve r α) t) volume 2 (3 - δ) := by
  have h3δ_gt_2 : 2 < 3 - δ := by linarith
  have : ContinuousOn (fun t => (↑((3 - t) * r) * exp (I * ↑α)) ^ (-(↑n : ℤ)) *
      (-(↑r) * exp (I * ↑α))) (Icc 2 (3 - δ)) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.zpow₀
      · fun_prop
      · intro t ht; left
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (by linarith [ht.2]) hr)))
          (Complex.exp_ne_zero _)
    · exact continuousOn_const
  exact (this.intervalIntegrable_of_Icc h3δ_gt_2.le).congr_ae (by
    rw [Set.uIoc_of_le h3δ_gt_2.le,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, by linarith [ht.2]⟩,
      deriv_sectorCurve_seg3 r α t ⟨ht.1, by linarith [ht.2]⟩])

private theorem zpow_primitive_hasDerivAt (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1) :
    let m : ℤ := 1 - ↑n
    let γ := sectorCurve r α
    let F := fun t => (γ t) ^ m / (m : ℂ)
    let f := fun t => (γ t) ^ (-(↑n : ℤ)) * deriv γ t
    ∀ t ∈ Ioo δ (3 - δ) \ ({1, 2} ∩ Ioo δ (3 - δ)),
      HasDerivAt F (f t) t := by
  intro m γ F f t ⟨ht, ht_not⟩
  have hm_ne : (m : ℂ) ≠ 0 := by
    have : m ≠ 0 := by simp [m]; omega
    exact_mod_cast this
  have ht_not' : t ∉ ({1, 2} : Set ℝ) := fun h => ht_not ⟨h, ht⟩
  have hγ_ne := sectorCurve_ne_zero_of_Icc_δ r hr α δ hδ_pos
    hδ_lt_1 t (Ioo_subset_Icc_self ht)
  have h_zpow : HasDerivAt (fun s => (γ s) ^ m)
      (((m : ℂ) * (γ t) ^ (m - 1)) • deriv γ t) t :=
    (hasDerivAt_zpow m (γ t) (Or.inl hγ_ne)).comp t
      (sectorCurve_differentiableAt_off_knots r α t
        ⟨lt_trans hδ_pos ht.1, lt_of_lt_of_le ht.2 (by linarith)⟩ ht_not').hasDerivAt
  have hm_sub : m - 1 = -(↑n : ℤ) := by simp [m]
  change HasDerivAt F ((γ t) ^ (-(↑n : ℤ)) * deriv γ t) t
  convert h_zpow.div_const (m : ℂ) using 1
  rw [smul_eq_mul, mul_assoc, mul_div_cancel_left₀ _ hm_ne, hm_sub]

private theorem zpow_ftc_vanishes (r : ℝ) (_hr : 0 < r) (α : ℝ) (n : ℕ) (_hn : 2 ≤ n)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_1 : δ < 1)
    (h_exp_one : exp (I * ↑((1 - (↑(n : ℤ) : ℤ)) * α)) = 1) :
    let m : ℤ := 1 - ↑n
    let γ := sectorCurve r α
    let F := fun t => (γ t) ^ m / (m : ℂ)
    F (3 - δ) - F δ = 0 := by
  intro m γ F
  have h3δ_gt_2 : 2 < 3 - δ := by linarith
  have hγ_δ : γ δ = ↑(δ * r) := sectorCurve_seg1 r α δ ⟨hδ_pos.le, hδ_lt_1.le⟩
  have hγ_3δ : γ (3 - δ) = ↑(δ * r) * exp (I * ↑α) := by
    have := sectorCurve_seg3 r α (3 - δ) ⟨h3δ_gt_2.le, by linarith⟩
    simp only [show 3 - (3 - δ) = δ from by ring] at this; exact this
  simp only [F, hγ_δ, hγ_3δ, mul_zpow]
  have hexp_m : (exp (I * ↑α)) ^ m = exp (I * ↑((1 - (↑n : ℤ)) * α)) := by
    rw [← Complex.exp_int_mul]; congr 1; push_cast [m]; ring
  rw [hexp_m, h_exp_one, mul_one, sub_self]

private theorem angle_condition_exp_eq_one (n : ℕ) (hn : 2 ≤ n) (α : ℝ)
    (k : ℤ) (hk : (↑(n - 1) : ℤ) * α = k * (2 * Real.pi)) :
    exp (I * ↑((1 - (↑n : ℤ)) * α)) = 1 := by
  suffices h : ∃ j : ℤ, I * ↑((1 - (↑n : ℤ)) * α) = ↑j * (2 * ↑Real.pi * I) by
    obtain ⟨j, hj⟩ := h; rw [hj]; exact Complex.exp_int_mul_two_pi_mul_I j
  exact ⟨-k, by
    have h1 : ((1 - (↑n : ℤ)) * α : ℝ) = ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hk ⊢; linarith
    rw [show (↑((1 - (↑n : ℤ)) * α) : ℂ) = ↑(((-k : ℤ) : ℝ) * (2 * Real.pi)) from
      congrArg _ h1]
    push_cast; ring⟩

private theorem pv_cutoff_integral_eq_mid (r : ℝ) (hr : 0 < r) (α : ℝ) (n : ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_r : ε < r) :
    let δ := ε / r
    let γ := sectorCurve r α
    let f := fun t => (γ t) ^ (-(↑n : ℤ)) * deriv γ t
    ∫ t in (0 : ℝ)..3,
      (if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0) =
    ∫ t in δ..(3 - δ), f t := by
  intro δ γ f
  set g : ℝ → ℂ := fun t =>
    if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0
  have hδ_pos : 0 < δ := div_pos hε_pos hr
  have hδ_lt_1 : δ < 1 := by rw [div_lt_one hr]; exact hε_lt_r
  have hδr_eq : δ * r = ε := div_mul_cancel₀ ε (ne_of_gt hr)
  have h_norm_le_0δ := sectorCurve_norm_le_near_zero r hr α δ hδ_pos hδ_lt_1 ε hδr_eq
  have h_norm_le_3δ3 := sectorCurve_norm_le_near_three r hr α δ hδ_lt_1 ε hδr_eq
  have h_norm_gt_mid := sectorCurve_norm_gt_mid r hr α δ hδ_pos hδ_lt_1 ε hε_lt_r hδr_eq
  have hf_int : IntervalIntegrable f volume δ (3 - δ) :=
    (zpow_integrableOn_δ1 r hr α n δ hδ_pos hδ_lt_1).trans
      (zpow_integrableOn_12 r hr α n) |>.trans
      (zpow_integrableOn_23δ r hr α n δ hδ_pos hδ_lt_1)
  have h_01 : ∫ t in (0 : ℝ)..δ, g t = 0 :=
    intervalIntegral.integral_zero_ae (ae_of_all _ (fun t ht => by
      simp only [g, sub_zero]
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hδ_pos.le] at ht'
      rw [if_neg (not_lt.mpr (h_norm_le_0δ t ht'))]))
  have h_3δ3 : ∫ t in (3 - δ)..3, g t = 0 :=
    intervalIntegral.integral_zero_ae (ae_of_all _ (fun t ht => by
      simp only [g, sub_zero]
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le (by linarith : 3 - δ ≤ 3)] at ht'
      rw [if_neg (not_lt.mpr (h_norm_le_3δ3 t ht'))]))
  have h_mid : ∫ t in δ..(3 - δ), g t = ∫ t in δ..(3 - δ), f t :=
    intervalIntegral.integral_congr_ae (by
      rw [Set.uIoc_of_le (by linarith : δ ≤ 3 - δ), ae_iff]
      apply measure_mono_null (t := {3 - δ})
      · intro x hx
        simp only [mem_setOf_eq] at hx; push Not at hx
        obtain ⟨hx_ioc, hx_ne⟩ := hx
        by_contra hne_3δ
        simp only [mem_singleton_iff] at hne_3δ
        have hx_ioo : x ∈ Ioo δ (3 - δ) := ⟨hx_ioc.1, lt_of_le_of_ne hx_ioc.2 hne_3δ⟩
        exact hx_ne (by simp only [g, sub_zero, f]; rw [if_pos (h_norm_gt_mid x hx_ioo)])
      · exact Real.volume_singleton)
  have hg_0δ : IntervalIntegrable g volume 0 δ :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      simp only [g, sub_zero]
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hδ_pos.le] at ht'
      rw [if_neg (not_lt.mpr (h_norm_le_0δ t ht'))])
  have hg_δ3δ : IntervalIntegrable g volume δ (3 - δ) :=
    hf_int.congr_ae (by
      rw [Set.uIoc_of_le (by linarith : δ ≤ 3 - δ)]
      apply Filter.EventuallyEq.symm
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc, ae_iff]
      apply measure_mono_null (t := {3 - δ})
      · intro x hx
        simp only [mem_setOf_eq] at hx; push Not at hx
        obtain ⟨hx_ioc, hx_ne⟩ := hx
        by_contra hne_3δ
        simp only [mem_singleton_iff] at hne_3δ
        have hx_ioo : x ∈ Ioo δ (3 - δ) := ⟨hx_ioc.1, lt_of_le_of_ne hx_ioc.2 hne_3δ⟩
        exact hx_ne (by simp only [f, g, sub_zero]; rw [if_pos (h_norm_gt_mid x hx_ioo)])
      · exact Real.volume_singleton)
  have hg_3δ3 : IntervalIntegrable g volume (3 - δ) 3 :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      simp only [g, sub_zero]
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le (by linarith : 3 - δ ≤ 3)] at ht'
      rw [if_neg (not_lt.mpr (h_norm_le_3δ3 t ht'))])
  rw [show ∫ t in (0 : ℝ)..3,
        (if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0) =
      ∫ t in (0 : ℝ)..3, g t from rfl]
  rw [← intervalIntegral.integral_add_adjacent_intervals hg_0δ (hg_δ3δ.trans hg_3δ3),
      ← intervalIntegral.integral_add_adjacent_intervals hg_δ3δ hg_3δ3,
      h_01, h_mid, h_3δ3, zero_add, add_zero]

/-- **Equation (3.4)**: The PV of `z^{-n}` along the sector curve is 0 when
`(n-1) * α` is a multiple of `2π`. The cutoff integral equals
`ε^{1-n} * (exp(i(1-n)α) - 1) / (1-n)`, which vanishes identically under
the angle condition. By FTC with primitive `F(t) = γ(t)^{1-n}/(1-n)`. -/
theorem pv_sector_negative_power (r : ℝ) (hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi)
    (n : ℕ) (hn : 2 ≤ n)
    (h_angle : ∃ k : ℤ, (↑(n - 1) : ℤ) * α = k * (2 * Real.pi)) :
    CauchyPrincipalValueExists' (fun z => z ^ (-(↑n : ℤ))) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => z ^ (-(↑n : ℤ))) (sectorCurve r α) 0 3 0 = 0 := by
  obtain ⟨k, hk⟩ := h_angle
  set γ := sectorCurve r α
  set m : ℤ := 1 - ↑n
  have h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in (0 : ℝ)..3,
        (if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0) =
      0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr] with ε hε hε_pos
    simp only [mem_Ioi] at hε_pos
    set δ := ε / r
    have hδ_pos : 0 < δ := div_pos hε_pos hr
    have hδ_lt_1 : δ < 1 := by rw [div_lt_one hr]; exact mem_Iio.mp hε
    have hγ_ne := sectorCurve_ne_zero_of_Icc_δ r hr α δ hδ_pos hδ_lt_1
    have hF_cont : ContinuousOn (fun t => (γ t) ^ m / (m : ℂ)) (Icc δ (3 - δ)) := by
      apply ContinuousOn.div_const; apply ContinuousOn.zpow₀
      · exact (sectorCurve_continuousOn r α).mono (by
          intro t ht; constructor <;> linarith [ht.1, ht.2, hδ_pos])
      · intro t ht; exact Or.inl (hγ_ne t ht)
    have hf_int : IntervalIntegrable
        (fun t => (γ t) ^ (-(↑n : ℤ)) * deriv γ t) volume δ (3 - δ) :=
      (zpow_integrableOn_δ1 r hr α n δ hδ_pos hδ_lt_1).trans
        (zpow_integrableOn_12 r hr α n) |>.trans
        (zpow_integrableOn_23δ r hr α n δ hδ_pos hδ_lt_1)
    rw [pv_cutoff_integral_eq_mid r hr α n ε hε_pos (mem_Iio.mp hε),
      MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        _ _ (by linarith : δ ≤ 3 - δ)
        ((Set.Finite.inter_of_left (Set.toFinite {1, 2}) _).countable) hF_cont
        (zpow_primitive_hasDerivAt r hr α n hn δ hδ_pos hδ_lt_1) hf_int]
    exact zpow_ftc_vanishes r hr α n hn δ hδ_pos hδ_lt_1
      (angle_condition_exp_eq_one n hn α k hk)
  have h_tendsto : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..3,
        if ‖γ t - 0‖ > ε then (γ t) ^ (-(↑n : ℤ)) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (h_ev.mono fun ε h => h.symm)
  exact ⟨⟨0, h_tendsto⟩, h_tendsto.limUnder_eq⟩

/-- The generalized winding number of the sector curve around 0
equals `alpha / (2 * pi)`. -/
theorem generalizedWindingNumber_sectorCurve (r : ℝ) (hr : 0 < r) (α : ℝ)
    (hα_nonneg : 0 ≤ α) (hα_le : α ≤ 2 * Real.pi)
    (_hPV : CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0) :
    generalizedWindingNumber' (sectorCurve r α) 0 3 0 = ↑α / (2 * ↑Real.pi) := by
  unfold generalizedWindingNumber'
  rw [show (fun t => sectorCurve r α t - 0) = sectorCurve r α from by ext; simp only [sub_zero],
    (pv_sector_dz_over_z r hr α hα_nonneg hα_le).2]
  field_simp

end
