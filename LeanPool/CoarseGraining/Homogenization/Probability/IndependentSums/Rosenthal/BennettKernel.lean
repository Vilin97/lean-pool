/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.BennettFunction

/-! # Bennett Kernel -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The Bennett kernel is pointwise dominated by the pure power `r^(p-1)` on
the nonnegative half-line. -/
theorem bennettKernel_le_rpow
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ)))) ≤ r ^ (p - 1) := by
  by_cases hr0 : r = 0
  · simp [hr0, bennettBeta, bennettH_zero]
  · have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hbeta : 0 ≤ bennettBeta (r ^ (2 : ℕ)) := by
      exact bennettBeta_nonneg (by positivity)
    have hexp_le_one : Real.exp (-(p * bennettBeta (r ^ (2 : ℕ)))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg hp hbeta)
    have hpow_nonneg : 0 ≤ r ^ (p - 1) := Real.rpow_nonneg hr _
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hexp_le_one hpow_nonneg

/-- Beyond the large-scale Bennett threshold `exp 2`, the Rosenthal kernel is
dominated by the integrable tail power `r^(-p/2 - 1)`. -/
theorem bennettKernel_le_rpowTail
    {p r : ℝ} (hp : 2 ≤ p) (hr : Real.exp 2 ≤ r) :
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ)))) ≤ r ^ (-p / 2 - 1) := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_two hp
  have hr_pos : 0 < r := lt_of_lt_of_le (by positivity : 0 < Real.exp 2) hr
  have hr_sq :
      bennettLargeScaleThreshold ≤ r ^ (2 : ℕ) := by
    calc
      bennettLargeScaleThreshold = (Real.exp 2) ^ (2 : ℕ) := by
        rw [bennettLargeScaleThreshold, show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add, pow_two]
      _ ≤ r ^ (2 : ℕ) := by
        gcongr
  have hbeta :
      (3 / 2 : ℝ) * Real.log r ≤ bennettBeta (r ^ (2 : ℕ)) := by
    have hmain := three_quarters_log_le_bennettBeta_of_bennettLargeScaleThreshold_le hr_sq
    have hlog : Real.log (r ^ (2 : ℕ)) = 2 * Real.log r := by
      rw [pow_two, Real.log_mul hr_pos.ne' hr_pos.ne']
      ring
    have hrewrite : (3 / 4 : ℝ) * Real.log (r ^ (2 : ℕ)) = (3 / 2 : ℝ) * Real.log r := by
      rw [hlog]
      ring
    calc
      (3 / 2 : ℝ) * Real.log r = (3 / 4 : ℝ) * Real.log (r ^ (2 : ℕ)) := by
        exact hrewrite.symm
      _ ≤ bennettBeta (r ^ (2 : ℕ)) := hmain
  have hexp_le :
      Real.exp (-(p * bennettBeta (r ^ (2 : ℕ)))) ≤
        Real.exp (-(p * ((3 / 2 : ℝ) * Real.log r))) := by
    apply Real.exp_monotone
    linarith [mul_le_mul_of_nonneg_left hbeta hp_nonneg]
  calc
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
      ≤ r ^ (p - 1) * Real.exp (-(p * ((3 / 2 : ℝ) * Real.log r))) := by
          gcongr
    _ = r ^ (p - 1) * r ^ (-(3 / 2 : ℝ) * p) := by
          have hexp_eq :
              Real.exp (-(p * ((3 / 2 : ℝ) * Real.log r))) = r ^ (-(3 / 2 : ℝ) * p) := by
            rw [Real.rpow_def_of_pos hr_pos]
            congr 1
            ring
          rw [hexp_eq]
    _ = r ^ (-p / 2 - 1) := by
          rw [← Real.rpow_add hr_pos]
          congr 1
          ring

private theorem bennett_kernel_integrable_regions
    {p : ℝ} (hp : 2 ≤ p) :
    let f : ℝ → ℝ := fun r =>
      r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
    IntegrableOn f (Set.Icc (0 : ℝ) 1) volume ∧
      IntegrableOn f (Set.Icc (1 : ℝ) (Real.exp 2)) volume ∧
      IntegrableOn (fun r : ℝ => r ^ (-p / 2 - 1)) (Set.Ioi (Real.exp 2)) volume ∧
      IntegrableOn f (Set.Ioi (Real.exp 2)) volume := by
  let f : ℝ → ℝ := fun r =>
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hp_sub_nonneg : 0 ≤ p - 1 := by linarith
  have hf_meas : Measurable f := by
    dsimp [f]
    have hpow_meas : Measurable (fun r : ℝ => r ^ (p - 1)) :=
      (Real.continuous_rpow_const hp_sub_nonneg).measurable
    have hbeta_meas : Measurable (fun r : ℝ => bennettBeta (r ^ (2 : ℕ))) := by
      dsimp [bennettBeta, bennettH]
      measurability
    exact hpow_meas.mul (Real.measurable_exp.comp ((measurable_const.mul hbeta_meas).neg))
  have hsmall_const :
      Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact integrableOn_const (μ := volume) (s := Set.Icc (0 : ℝ) 1) (C := (1 : ℝ))
      isCompact_Icc.measure_ne_top
  have hsmall_Icc :
      Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine Integrable.mono' hsmall_const hf_meas.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with r hr
    have hfr_le : f r ≤ r ^ (p - 1) := bennettKernel_le_rpow hp_nonneg hr.1
    have hrpow_le_one : r ^ (p - 1) ≤ 1 := Real.rpow_le_one hr.1 hr.2 hp_sub_nonneg
    have hnonneg : 0 ≤ f r := by
      dsimp [f]
      exact mul_nonneg (Real.rpow_nonneg hr.1 _) (by positivity)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hfr_le.trans hrpow_le_one
  have hmid_const :
      Integrable (fun _ : ℝ => (Real.exp 2) ^ (p - 1))
        (volume.restrict (Set.Icc (1 : ℝ) (Real.exp 2))) := by
    exact integrableOn_const (μ := volume) (s := Set.Icc (1 : ℝ) (Real.exp 2))
      (C := (Real.exp 2) ^ (p - 1)) isCompact_Icc.measure_ne_top
  have hmid_Icc :
      Integrable f (volume.restrict (Set.Icc (1 : ℝ) (Real.exp 2))) := by
    refine Integrable.mono' hmid_const hf_meas.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with r hr
    have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr.1
    have hfr_le : f r ≤ r ^ (p - 1) := bennettKernel_le_rpow hp_nonneg hr_nonneg
    have hrpow_le :
        r ^ (p - 1) ≤ (Real.exp 2) ^ (p - 1) := by
      exact Real.rpow_le_rpow hr_nonneg hr.2 hp_sub_nonneg
    have hnonneg : 0 ≤ f r := by
      dsimp [f]
      exact mul_nonneg (Real.rpow_nonneg hr_nonneg _) (by positivity)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hfr_le.trans hrpow_le
  have htail_dom :
      Integrable (fun r : ℝ => r ^ (-p / 2 - 1))
        (volume.restrict (Set.Ioi (Real.exp 2))) := by
    simpa using!
      (integrableOn_Ioi_rpow_of_lt (a := -p / 2 - 1) (by linarith) (by positivity : 0 < Real.exp 2))
  have htail_Ioi :
      Integrable f (volume.restrict (Set.Ioi (Real.exp 2))) := by
    refine Integrable.mono' htail_dom hf_meas.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hfr_le : f r ≤ r ^ (-p / 2 - 1) := bennettKernel_le_rpowTail hp (le_of_lt hr)
    have hr_nonneg : 0 ≤ r := le_trans (le_of_lt (by positivity : 0 < Real.exp 2)) (le_of_lt hr)
    have hnonneg : 0 ≤ f r := by
      dsimp [f]
      exact mul_nonneg (Real.rpow_nonneg hr_nonneg _) (by positivity)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hfr_le
  exact ⟨hsmall_Icc, hmid_Icc, htail_dom, htail_Ioi⟩

/-- A universal bound for the Bennett kernel integral appearing in the
tail-integration step of Rosenthal's inequality. -/
noncomputable def rosenthalBennettIntegralConst : ℝ :=
  4 * Real.exp 2

theorem rosenthal_bennett_kernel_integral_le
    {p : ℝ} (hp : 2 ≤ p) :
    p * ∫ r in Set.Ioi (0 : ℝ),
      r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ)))) ≤
        rosenthalBennettIntegralConst ^ p := by
  let f : ℝ → ℝ := fun r =>
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have h_one_exp_two : (1 : ℝ) ≤ Real.exp 2 := by
    exact le_of_lt ((Real.one_lt_exp_iff).2 (by norm_num))
  obtain ⟨hsmall_Icc, hmid_Icc, htail_dom, htail_Ioi⟩ :=
    bennett_kernel_integrable_regions hp
  have hsmall :
      IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume := by
    change Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1))
    exact hsmall_Icc.mono_set Ioc_subset_Icc_self
  have hmid :
      IntegrableOn f (Set.Ioc (1 : ℝ) (Real.exp 2)) volume := by
    change Integrable f (volume.restrict (Set.Ioc (1 : ℝ) (Real.exp 2)))
    exact hmid_Icc.mono_set Ioc_subset_Icc_self
  have htail :
      IntegrableOn f (Set.Ioi (Real.exp 2)) volume := by
    simpa [IntegrableOn] using htail_Ioi
  have hpow_small :
      IntervalIntegrable (fun r : ℝ => r ^ (p - 1)) volume 0 1 := by
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpow_mid :
      IntervalIntegrable (fun r : ℝ => r ^ (p - 1)) volume 1 (Real.exp 2) := by
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hsmall_bound :
      p * ∫ r in Set.Ioc (0 : ℝ) 1, f r ≤ 1 := by
    have hsmall_Icc_on : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume := by
      simpa [IntegrableOn] using hsmall_Icc
    have hle :
        ∫ r in Set.Ioc (0 : ℝ) 1, f r ≤ ∫ r in (0 : ℝ)..1, r ^ (p - 1) := by
      have hsmall_interval :
          IntervalIntegrable f volume (0 : ℝ) 1 :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 hsmall_Icc_on
      rw [← intervalIntegral.integral_of_le zero_le_one]
      exact intervalIntegral.integral_mono_on zero_le_one hsmall_interval hpow_small
        (fun r hr => bennettKernel_le_rpow hp_nonneg hr.1)
    have hcalc :
        ∫ r in (0 : ℝ)..1, r ^ (p - 1) = 1 / p := by
      rw [integral_rpow (a := (0 : ℝ)) (b := 1) (r := p - 1) (Or.inl (by linarith))]
      simp [hp_pos.ne']
    have hmul := mul_le_mul_of_nonneg_left hle hp_nonneg
    simpa [hcalc, div_eq_mul_inv, hp_pos.ne'] using hmul
  have hmid_bound :
      p * ∫ r in Set.Ioc (1 : ℝ) (Real.exp 2), f r ≤ (Real.exp 2) ^ p := by
    have hmid_Icc_on : IntegrableOn f (Set.Icc (1 : ℝ) (Real.exp 2)) volume := by
      simpa [IntegrableOn] using hmid_Icc
    have hle :
        ∫ r in Set.Ioc (1 : ℝ) (Real.exp 2), f r ≤ ∫ r in (1 : ℝ)..Real.exp 2, r ^ (p - 1) := by
      have hmid_interval :
          IntervalIntegrable f volume (1 : ℝ) (Real.exp 2) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le h_one_exp_two).2 hmid_Icc_on
      rw [← intervalIntegral.integral_of_le h_one_exp_two]
      exact intervalIntegral.integral_mono_on h_one_exp_two hmid_interval hpow_mid
        (fun r hr => bennettKernel_le_rpow hp_nonneg (le_trans zero_le_one hr.1))
    have hcalc :
        ∫ r in (1 : ℝ)..Real.exp 2, r ^ (p - 1) = ((Real.exp 2) ^ p - 1) / p := by
      rw [integral_rpow (a := (1 : ℝ)) (b := Real.exp 2) (r := p - 1)
        (Or.inl (by linarith))]
      simp
    have hmul := mul_le_mul_of_nonneg_left hle hp_nonneg
    rw [hcalc] at hmul
    have hbase : p * (((Real.exp 2) ^ p - 1) / p) = (Real.exp 2) ^ p - 1 := by
      field_simp [hp_pos.ne']
    rw [hbase] at hmul
    exact hmul.trans (by linarith)
  have htail_dom_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] fun r : ℝ => r ^ (-p / 2 - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (le_trans zero_le_one hr.le) _
  have htail_bound :
      p * ∫ r in Set.Ioi (Real.exp 2), f r ≤ 2 := by
    have htail_dom_on :
        IntegrableOn (fun r : ℝ => r ^ (-p / 2 - 1)) (Set.Ioi (Real.exp 2)) volume := by
      simpa [IntegrableOn] using htail_dom
    have hle :
        ∫ r in Set.Ioi (Real.exp 2), f r ≤
          ∫ r in Set.Ioi (Real.exp 2), r ^ (-p / 2 - 1) := by
      exact setIntegral_mono_on (f := f) (g := fun r : ℝ => r ^ (-p / 2 - 1))
        htail htail_dom_on measurableSet_Ioi
        (fun r hr => bennettKernel_le_rpowTail hp (le_of_lt hr))
    have hmono :
        ∫ r in Set.Ioi (Real.exp 2), r ^ (-p / 2 - 1) ≤
          ∫ r in Set.Ioi (1 : ℝ), r ^ (-p / 2 - 1) := by
      exact setIntegral_mono_set
        (f := fun r : ℝ => r ^ (-p / 2 - 1))
        (s := Set.Ioi (Real.exp 2)) (t := Set.Ioi (1 : ℝ))
        (μ := volume)
        (by simpa using (integrableOn_Ioi_rpow_of_lt (a := -p / 2 - 1) (by linarith) zero_lt_one))
        htail_dom_nonneg
        (Filter.Eventually.of_forall (fun r hr => lt_trans ((Real.one_lt_exp_iff).2 (by norm_num)) hr))
    have hcalc :
        ∫ r in Set.Ioi (1 : ℝ), r ^ (-p / 2 - 1) = 2 / p := by
      rw [integral_Ioi_rpow_of_lt (a := -p / 2 - 1) (by linarith) zero_lt_one]
      simp [div_eq_mul_inv]
    have hmul := mul_le_mul_of_nonneg_left (hle.trans hmono) hp_nonneg
    rw [hcalc] at hmul
    have hbase : p * (2 / p) = 2 := by
      field_simp [hp_pos.ne']
    rw [hbase] at hmul
    exact hmul
  have hsplit1 :
      Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    exact (Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one).symm
  have hsplit2 :
      Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) (Real.exp 2) ∪ Set.Ioi (Real.exp 2) := by
    exact (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := Real.exp 2) h_one_exp_two).symm
  have hIoi_one :
      IntegrableOn f (Set.Ioi (1 : ℝ)) volume := by
    rw [hsplit2, integrableOn_union]
    exact ⟨hmid, htail⟩
  have hdecomp :
      ∫ r in Set.Ioi (0 : ℝ), f r =
        (∫ r in Set.Ioc (0 : ℝ) 1, f r) +
          ((∫ r in Set.Ioc (1 : ℝ) (Real.exp 2), f r) +
            (∫ r in Set.Ioi (Real.exp 2), f r)) := by
    calc
      ∫ r in Set.Ioi (0 : ℝ), f r
          = (∫ r in Set.Ioc (0 : ℝ) 1, f r) + ∫ r in Set.Ioi (1 : ℝ), f r := by
              rw [hsplit1]
              rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hsmall hIoi_one]
      _ = (∫ r in Set.Ioc (0 : ℝ) 1, f r) +
            ((∫ r in Set.Ioc (1 : ℝ) (Real.exp 2), f r) +
              (∫ r in Set.Ioi (Real.exp 2), f r)) := by
              rw [hsplit2]
              rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hmid htail]
  have hsum :
      p * ∫ r in Set.Ioi (0 : ℝ), f r ≤ 1 + (Real.exp 2) ^ p + 2 := by
    calc
      p * ∫ r in Set.Ioi (0 : ℝ), f r
          = (p * ∫ r in Set.Ioc (0 : ℝ) 1, f r) +
              ((p * ∫ r in Set.Ioc (1 : ℝ) (Real.exp 2), f r) +
                (p * ∫ r in Set.Ioi (Real.exp 2), f r)) := by
                  rw [hdecomp]
                  ring
      _ ≤ 1 + (Real.exp 2) ^ p + 2 := by
            linarith [hsmall_bound, hmid_bound, htail_bound]
  have hexp_two_pow_one : 1 ≤ (Real.exp 2) ^ p := by
    exact Real.one_le_rpow h_one_exp_two hp_nonneg
  have hsum' : 1 + (Real.exp 2) ^ p + 2 ≤ 4 * (Real.exp 2) ^ p := by
    linarith
  have hfour_le : (4 : ℝ) ≤ (4 : ℝ) ^ p := by
    exact Real.self_le_rpow_of_one_le (by norm_num) (by linarith)
  have hfinal :
      4 * (Real.exp 2) ^ p ≤ rosenthalBennettIntegralConst ^ p := by
    calc
      4 * (Real.exp 2) ^ p ≤ (4 : ℝ) ^ p * (Real.exp 2) ^ p := by
        gcongr
      _ = rosenthalBennettIntegralConst ^ p := by
        rw [rosenthalBennettIntegralConst, ← Real.mul_rpow (by positivity) (by positivity)]
  exact hsum.trans (hsum'.trans hfinal)

/-- The universal Bennett kernel appearing in the Rosenthal proof is
integrable on `(0, ∞)`. -/
theorem integrableOn_rosenthal_bennett_kernel
    {p : ℝ} (hp : 2 ≤ p) :
    IntegrableOn
      (fun r : ℝ => r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ)))))
      (Set.Ioi (0 : ℝ)) volume := by
  let f : ℝ → ℝ := fun r =>
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
  have h_one_exp_two : (1 : ℝ) ≤ Real.exp 2 := by
    exact le_of_lt ((Real.one_lt_exp_iff).2 (by norm_num))
  obtain ⟨hsmall_Icc, hmid_Icc, _htail_dom, htail_Ioi⟩ :=
    bennett_kernel_integrable_regions hp
  have hsmall :
      IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume := by
    change Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1))
    exact hsmall_Icc.mono_set Ioc_subset_Icc_self
  have hmid :
      IntegrableOn f (Set.Ioc (1 : ℝ) (Real.exp 2)) volume := by
    change Integrable f (volume.restrict (Set.Ioc (1 : ℝ) (Real.exp 2)))
    exact hmid_Icc.mono_set Ioc_subset_Icc_self
  have htail :
      IntegrableOn f (Set.Ioi (Real.exp 2)) volume := by
    simpa [IntegrableOn] using htail_Ioi
  have hsplit1 :
      Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    exact (Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one).symm
  have hsplit2 :
      Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) (Real.exp 2) ∪ Set.Ioi (Real.exp 2) := by
    exact (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := Real.exp 2) h_one_exp_two).symm
  have hIoi_one :
      IntegrableOn f (Set.Ioi (1 : ℝ)) volume := by
    rw [hsplit2, integrableOn_union]
    exact ⟨hmid, htail⟩
  rw [hsplit1, integrableOn_union]
  exact ⟨hsmall, hIoi_one⟩

/-- After the moment-adapted truncation choice, the Bennett tail integral at
variance scale `σ²` is exactly a scaled copy of the universal Bennett kernel
integral. -/
theorem rosenthal_bennett_scaled_integral_le
    {p sigmaSq : ℝ} (hp : 2 ≤ p) (hSigma_pos : 0 < sigmaSq) :
    p * ∫ t in Set.Ioi (0 : ℝ),
      t ^ (p - 1) *
        Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))) ≤
          (rosenthalBennettIntegralConst * (Real.sqrt p * Real.sqrt sigmaSq)) ^ p := by
  let b : ℝ := Real.sqrt p * Real.sqrt sigmaSq
  let g : ℝ → ℝ := fun r =>
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
  let f : ℝ → ℝ := fun t =>
    t ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hb_pos : 0 < b := by
    dsimp [b]
    exact mul_pos (Real.sqrt_pos.2 hp_pos) (Real.sqrt_pos.2 hSigma_pos)
  have hb_nonneg : 0 ≤ b := hb_pos.le
  have hb_sq : b ^ (2 : ℕ) = p * sigmaSq := by
    dsimp [b]
    rw [pow_two]
    nlinarith [Real.sq_sqrt hp_nonneg, Real.sq_sqrt hSigma_pos.le]
  have hcomp :
      ∫ t in Set.Ioi (0 : ℝ), f (b * t) =
        ∫ t in Set.Ioi (0 : ℝ), b ^ (p - 1) * g t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.le
    have harg : (b * t) ^ (2 : ℕ) / (p * sigmaSq) = t ^ (2 : ℕ) := by
      calc
        (b * t) ^ (2 : ℕ) / (p * sigmaSq)
            = (b ^ (2 : ℕ) * t ^ (2 : ℕ)) / (p * sigmaSq) := by
                rw [pow_two, pow_two]
                ring
        _ = t ^ (2 : ℕ) := by
              rw [hb_sq]
              field_simp [hp_pos.ne', hSigma_pos.ne']
    calc
      f (b * t)
          = (b * t) ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ)))) := by
              dsimp [f]
              rw [harg]
      _ = (b ^ (p - 1) * t ^ (p - 1)) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ)))) := by
              rw [Real.mul_rpow hb_nonneg ht_nonneg]
      _ = b ^ (p - 1) * g t := by
              dsimp [g]
              ring
  have hscale :
      ∫ t in Set.Ioi (0 : ℝ), f t =
        b ^ p * ∫ r in Set.Ioi (0 : ℝ), g r := by
    calc
      ∫ t in Set.Ioi (0 : ℝ), f t
          = b * ∫ t in Set.Ioi (0 : ℝ), f (b * t) := by
              have hmul :
                  b * ∫ t in Set.Ioi (0 : ℝ), f (b * t) = ∫ t in Set.Ioi (0 : ℝ), f t := by
                rw [MeasureTheory.integral_comp_mul_left_Ioi (g := f) (a := (0 : ℝ)) hb_pos]
                simp [smul_eq_mul, hb_pos.ne']
              exact hmul.symm
      _ = b * ∫ t in Set.Ioi (0 : ℝ), b ^ (p - 1) * g t := by rw [hcomp]
      _ = b * (b ^ (p - 1) * ∫ t in Set.Ioi (0 : ℝ), g t) := by
            rw [MeasureTheory.integral_const_mul]
      _ = b ^ p * ∫ r in Set.Ioi (0 : ℝ), g r := by
            have hpow : b * b ^ (p - 1) = b ^ p := by
              simpa [mul_comm] using (Real.rpow_add hb_pos (1 : ℝ) (p - 1)).symm
            calc
              b * (b ^ (p - 1) * ∫ t in Set.Ioi (0 : ℝ), g t)
                  = (b * b ^ (p - 1)) * ∫ t in Set.Ioi (0 : ℝ), g t := by ring
              _ = b ^ p * ∫ r in Set.Ioi (0 : ℝ), g r := by rw [hpow]
  calc
    p * ∫ t in Set.Ioi (0 : ℝ), f t
        = b ^ p * (p * ∫ r in Set.Ioi (0 : ℝ), g r) := by
            rw [hscale]
            ring
    _ ≤ b ^ p * rosenthalBennettIntegralConst ^ p := by
          gcongr
          exact rosenthal_bennett_kernel_integral_le hp
    _ = (rosenthalBennettIntegralConst * b) ^ p := by
          have hC_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
            dsimp [rosenthalBennettIntegralConst]
            positivity
          rw [mul_comm, ← Real.mul_rpow hC_nonneg hb_nonneg]
    _ = (rosenthalBennettIntegralConst * (Real.sqrt p * Real.sqrt sigmaSq)) ^ p := by
          rfl

/-- The Bennett kernel at variance scale `σ²` is integrable on `(0, ∞)`. -/
theorem integrableOn_rosenthal_bennett_scaled_kernel
    {p sigmaSq : ℝ} (hp : 2 ≤ p) (hSigma_pos : 0 < sigmaSq) :
    IntegrableOn
      (fun t : ℝ =>
        t ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))))
      (Set.Ioi (0 : ℝ)) volume := by
  let b : ℝ := Real.sqrt p * Real.sqrt sigmaSq
  let g : ℝ → ℝ := fun r =>
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
  let f : ℝ → ℝ := fun t =>
    t ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hb_pos : 0 < b := by
    dsimp [b]
    exact mul_pos (Real.sqrt_pos.2 hp_pos) (Real.sqrt_pos.2 hSigma_pos)
  have hg : IntegrableOn g (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_rosenthal_bennett_kernel hp
  have hcomp :
      IntegrableOn (fun t : ℝ => f (b * t)) (Set.Ioi (0 : ℝ)) volume := by
    have hg' : IntegrableOn (fun t : ℝ => b ^ (p - 1) * g t) (Set.Ioi (0 : ℝ)) volume := by
      exact hg.const_mul (b ^ (p - 1))
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).2 hg'
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.le
    have hb_sq : b ^ (2 : ℕ) = p * sigmaSq := by
      dsimp [b]
      rw [pow_two]
      nlinarith [Real.sq_sqrt hp_pos.le, Real.sq_sqrt hSigma_pos.le]
    have harg : (b * t) ^ (2 : ℕ) / (p * sigmaSq) = t ^ (2 : ℕ) := by
      calc
        (b * t) ^ (2 : ℕ) / (p * sigmaSq)
            = (b ^ (2 : ℕ) * t ^ (2 : ℕ)) / (p * sigmaSq) := by
                rw [pow_two, pow_two]
                ring
        _ = t ^ (2 : ℕ) := by
              rw [hb_sq]
              field_simp [hp_pos.ne', hSigma_pos.ne']
    calc
      f (b * t)
          = (b * t) ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ)))) := by
              dsimp [f]
              rw [harg]
      _ = (b ^ (p - 1) * t ^ (p - 1)) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ)))) := by
              rw [Real.mul_rpow hb_pos.le ht_nonneg]
      _ = b ^ (p - 1) * g t := by
              dsimp [g]
              ring
  simpa using (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff f 0 hb_pos).mp hcomp

/-- Layer cake for the Rosenthal maximum term: applying the standard `L^p`
tail formula to the scaled maximum `p M` gives the exact `p^p E[M^p]`
contribution. -/
theorem lintegral_rpow_sup'_abs_eq_scaled_tail
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 0 < p) (h_meas : ∀ i, Measurable (X i)) :
    ENNReal.ofReal p *
      ∫⁻ t in Set.Ioi (0 : ℝ),
        μ {ω | t / p < s.sup' hs (fun i => |X i ω|)} * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (p ^ p) *
        ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ := by
  let Mfun : ι → Ω → ℝ := fun i ω => |X i ω|
  let M : Ω → ℝ := s.sup' hs Mfun
  let Y : Ω → ℝ := fun ω => p * M ω
  have hM_eq : M = fun ω => s.sup' hs (fun i => |X i ω|) := by
    funext ω
    change (s.sup' hs Mfun) ω = s.sup' hs (fun i => |X i ω|)
    exact Finset.sup'_apply (C := fun _ => ℝ) hs Mfun ω
  have hM_meas : Measurable M := by
    refine Finset.measurable_sup' (hs := hs) (f := Mfun) ?_
    intro i hi
    exact continuous_abs.measurable.comp (h_meas i)
  have hM_aemeas : AEMeasurable M μ := hM_meas.aemeasurable
  have hM_nonneg : ∀ ω, 0 ≤ M ω := by
    intro ω
    have hnonneg : 0 ≤ Mfun hs.choose ω := by
      simp [Mfun]
    have hle : Mfun hs.choose ω ≤ M ω := by
      rw [hM_eq]
      exact Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec
    exact le_trans hnonneg hle
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact mul_nonneg hp.le (hM_nonneg ω)
  have hY_aemeas : AEMeasurable Y μ := by
    simpa [Y] using hM_aemeas.const_mul p
  have hLayer :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
      (μ := μ) (f := Y) (Filter.Eventually.of_forall hY_nonneg) hY_aemeas hp
  have hLayer' :
      ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ =
        ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {ω | t / p < s.sup' hs (fun i => |X i ω|)} * ENNReal.ofReal (t ^ (p - 1)) := by
    rw [hLayer]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hset : {a | t < Y a} = {ω | t / p < s.sup' hs (fun i => |X i ω|)} := by
      ext ω
      simp [Y, hM_eq, div_lt_iff₀ hp, mul_comm]
    change μ {a | t < Y a} * ENNReal.ofReal (t ^ (p - 1)) =
      μ {ω | t / p < s.sup' hs (fun i => |X i ω|)} * ENNReal.ofReal (t ^ (p - 1))
    rw [hset]
  have hMp_aemeas : AEMeasurable (fun ω => M ω ^ p) μ :=
    (Real.continuous_rpow_const hp.le).measurable.comp_aemeasurable hM_aemeas
  have hLeft :
      ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ =
        ENNReal.ofReal (p ^ p) * ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ
          = ∫⁻ ω, ENNReal.ofReal (p ^ p) * ENNReal.ofReal (M ω ^ p) ∂μ := by
              apply lintegral_congr_ae
              refine Filter.Eventually.of_forall ?_
              intro ω
              dsimp [Y]
              rw [Real.mul_rpow hp.le (hM_nonneg ω)]
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _)]
      _ = ENNReal.ofReal (p ^ p) * ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ := by
            simpa using
              (MeasureTheory.lintegral_const_mul''
                (μ := μ) (r := ENNReal.ofReal (p ^ p))
                (f := fun ω => ENNReal.ofReal (M ω ^ p))
                (measurable_id.ennreal_ofReal.comp_aemeasurable hMp_aemeas))
  calc
    ENNReal.ofReal p *
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {ω | t / p < s.sup' hs (fun i => |X i ω|)} * ENNReal.ofReal (t ^ (p - 1))
      = ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ := by
          rw [hLayer']
    _ = ENNReal.ofReal (p ^ p) * ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ := hLeft
    _ = ENNReal.ofReal (p ^ p) *
          ∫⁻ ω, ENNReal.ofReal ((s.sup' hs (fun i => |X i ω|)) ^ p) ∂μ := by
          congr 2
          funext ω
          simp [hM_eq]

/-- The optimizing Chernoff parameter in the Bennett exponent. -/
noncomputable def bennettOptimalLambda (v y t : ℝ) : ℝ :=
  Real.log (1 + t * y / v) / y

end
end IndependentSums
end Homogenization
