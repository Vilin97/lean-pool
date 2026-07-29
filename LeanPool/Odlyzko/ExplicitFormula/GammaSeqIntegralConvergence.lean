/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GammaSeqIntegralUniform

/-!
# Gamma Seq Integral Convergence

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gamma seq scalar kernel used in the Odlyzko-bound argument. -/
noncomputable def gammaSeqScalarKernel (n : ℕ) (x : ℝ) : ℝ :=
  (Ioc 0 (n : ℝ)).indicator (fun x ↦ (1 - x / n) ^ n) x

/-- A gamma scalar kernel used in the Odlyzko-bound argument. -/
noncomputable def gammaScalarKernel (x : ℝ) : ℝ :=
  (Ioi 0).indicator (fun x ↦ Real.exp (-x)) x

/-- A gamma seq integral error used in the Odlyzko-bound argument. -/
noncomputable def gammaSeqIntegralError (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  |gammaSeqScalarKernel n x - gammaScalarKernel x| *
    (Ioi 0).indicator (fun x ↦ x ^ (a - 1) + x ^ (b - 1)) x

theorem integrable_gammaVerticalMajorant
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (gammaVerticalMajorant a b) := by
  change Integrable
    ((Ioi 0).indicator
      (fun x : ℝ ↦ Real.exp (-x) *
        (x ^ (a - 1) + x ^ (b - 1))))
  rw [integrable_indicator_iff measurableSet_Ioi]
  convert
    (Real.GammaIntegral_convergent ha).add
      (Real.GammaIntegral_convergent hb) using 1
  ext x
  simp only [Pi.add_apply]
  ring

private theorem gammaSeqScalarKernel_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ gammaSeqScalarKernel n x := by
  by_cases hx : x ∈ Ioc 0 (n : ℝ)
  · rw [gammaSeqScalarKernel, indicator_of_mem hx]
    exact pow_nonneg
      (sub_nonneg.mpr
        (div_le_one_of_le₀ hx.2 (Nat.cast_nonneg n))) n
  · rw [gammaSeqScalarKernel, indicator_of_notMem hx]

private theorem gammaScalarKernel_nonneg (x : ℝ) :
    0 ≤ gammaScalarKernel x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [gammaScalarKernel, indicator_of_mem hx]
    exact (Real.exp_pos _).le
  · rw [gammaScalarKernel, indicator_of_notMem hx]

theorem gammaSeqScalarKernel_le (n : ℕ) (x : ℝ) :
    gammaSeqScalarKernel n x ≤ gammaScalarKernel x := by
  by_cases hx : x ∈ Ioc 0 (n : ℝ)
  · have hxpos : x ∈ Ioi (0 : ℝ) := hx.1
    rw [gammaSeqScalarKernel, indicator_of_mem hx,
      gammaScalarKernel, indicator_of_mem hxpos]
    exact one_sub_div_pow_le_exp_neg hx.2
  · rw [gammaSeqScalarKernel, indicator_of_notMem hx]
    exact gammaScalarKernel_nonneg x

theorem tendsto_gammaSeqScalarKernel (x : ℝ) :
    Tendsto (fun n : ℕ ↦ gammaSeqScalarKernel n x)
      atTop (𝓝 (gammaScalarKernel x)) := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · apply Tendsto.congr'
    · filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      have hxn : x ≤ (n : ℝ) := by simp_all
      rw [gammaSeqScalarKernel,
        indicator_of_mem (show x ∈ Ioc 0 (n : ℝ) from ⟨hx, hxn⟩)]
    · rw [show gammaScalarKernel x = Real.exp (-x) by
        rw [gammaScalarKernel, indicator_of_mem hx]]
      convert Real.tendsto_one_add_div_pow_exp (-x) using 1
      grind
  · have hxnot : ∀ n : ℕ, x ∉ Ioc 0 (n : ℝ) :=
      fun _ h ↦ hx h.1
    simpa only [gammaSeqScalarKernel, gammaScalarKernel,
      indicator_of_notMem hx, indicator_of_notMem (hxnot _)] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

theorem tendsto_gammaSeqIntegralError (a b x : ℝ) :
    Tendsto (fun n : ℕ ↦ gammaSeqIntegralError a b n x)
      atTop (𝓝 0) := by
  unfold gammaSeqIntegralError
  have hsub :
      Tendsto
        (fun n : ℕ ↦ gammaSeqScalarKernel n x - gammaScalarKernel x)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_gammaSeqScalarKernel x).sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ gammaScalarKernel x)
            atTop (𝓝 (gammaScalarKernel x)))
  simpa using
    (hsub.abs.mul_const
      ((Ioi 0).indicator
        (fun x ↦ x ^ (a - 1) + x ^ (b - 1)) x))

theorem gammaSeqIntegralError_le_majorant
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    gammaSeqIntegralError a b n x ≤ gammaVerticalMajorant a b x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [gammaSeqIntegralError, gammaVerticalMajorant,
      indicator_of_mem hx, indicator_of_mem hx]
    have hnonneg :=
      gammaSeqScalarKernel_nonneg n x
    have hle :=
      gammaSeqScalarKernel_le n x
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hfactor :
        0 ≤ x ^ (a - 1) + x ^ (b - 1) :=
      add_nonneg (Real.rpow_nonneg hx.le _)
        (Real.rpow_nonneg hx.le _)
    exact mul_le_mul_of_nonneg_right
      (by
        rw [gammaScalarKernel, indicator_of_mem hx]
        linarith)
      hfactor
  · rw [gammaSeqIntegralError, gammaVerticalMajorant,
      indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

theorem gammaSeqIntegralError_nonneg
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ gammaSeqIntegralError a b n x := by
  unfold gammaSeqIntegralError
  apply mul_nonneg (abs_nonneg _)
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx]
    exact add_nonneg (Real.rpow_nonneg hx.le _)
      (Real.rpow_nonneg hx.le _)
  · simp_all

private theorem measurable_gammaSeqScalarKernel (n : ℕ) :
    Measurable (gammaSeqScalarKernel n) := by
  unfold gammaSeqScalarKernel
  apply Measurable.indicator _ measurableSet_Ioc
  fun_prop

private theorem measurable_gammaScalarKernel :
    Measurable gammaScalarKernel := by
  unfold gammaScalarKernel
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

theorem aestronglyMeasurable_gammaSeqIntegralError
    (a b : ℝ) (n : ℕ) :
    AEStronglyMeasurable (gammaSeqIntegralError a b n) := by
  unfold gammaSeqIntegralError
  apply AEStronglyMeasurable.mul
  · exact
      (continuous_abs.measurable.comp
        ((measurable_gammaSeqScalarKernel n).sub
          measurable_gammaScalarKernel)).aestronglyMeasurable
  · rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact
      ((continuousOn_id.rpow_const
          (fun x hx ↦ Or.inl hx.ne')).add
        (continuousOn_id.rpow_const
          (fun x hx ↦ Or.inl hx.ne'))).aestronglyMeasurable
        measurableSet_Ioi

theorem integrable_gammaSeqIntegralError
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (gammaSeqIntegralError a b n) := by
  apply (integrable_gammaVerticalMajorant ha hb).mono'
    (aestronglyMeasurable_gammaSeqIntegralError a b n)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (gammaSeqIntegralError_nonneg a b n x)]
  exact gammaSeqIntegralError_le_majorant a b n x

theorem tendsto_integral_gammaSeqIntegralError
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ ∫ x : ℝ, gammaSeqIntegralError a b n x)
      atTop (𝓝 0) := by
  have h :=
    tendsto_integral_of_dominated_convergence
      (gammaVerticalMajorant a b)
      (fun n ↦
        aestronglyMeasurable_gammaSeqIntegralError a b n)
      (integrable_gammaVerticalMajorant ha hb)
      (fun n ↦ ?_)
      (ae_of_all _ fun x ↦ tendsto_gammaSeqIntegralError a b x)
  · simpa using h
  · filter_upwards [] with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gammaSeqIntegralError_nonneg a b n x)]
    exact gammaSeqIntegralError_le_majorant a b n x

theorem integrable_gammaSeqApproxIntegrand
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Integrable (gammaSeqApproxIntegrand n s) := by
  change Integrable
    ((Ioc 0 (n : ℝ)).indicator
      (fun x ↦ ((1 - x / n) ^ n : ℝ) *
        (x : ℂ) ^ (s - 1)))
  rw [integrable_indicator_iff measurableSet_Ioc]
  change IntegrableOn
    (fun x ↦ ((1 - x / n) ^ n : ℝ) *
      (x : ℂ) ^ (s - 1)) (Ioc 0 (n : ℝ))
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
    (Nat.cast_nonneg n)]
  apply IntervalIntegrable.continuousOn_mul
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    simp_all
  · fun_prop

theorem integrable_gammaIntegralIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (gammaIntegralIntegrand s) := by
  change Integrable
    ((Ioi 0).indicator
      (fun x ↦ (Real.exp (-x) : ℂ) *
        (x : ℂ) ^ (s - 1)))
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact Complex.GammaIntegral_convergent hs

theorem norm_gammaSeqApproxIntegrand_sub_le_error
    {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    (n : ℕ) (x : ℝ) :
    ‖gammaSeqApproxIntegrand n s x -
        gammaIntegralIntegrand s x‖ ≤
      gammaSeqIntegralError a b n x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · have happ :
        gammaSeqApproxIntegrand n s x =
          (gammaSeqScalarKernel n x : ℂ) *
            (x : ℂ) ^ (s - 1) := by
      by_cases hxn : x ∈ Ioc 0 (n : ℝ)
      · rw [gammaSeqApproxIntegrand, indicator_of_mem hxn,
          gammaSeqScalarKernel, indicator_of_mem hxn]
      · rw [gammaSeqApproxIntegrand, indicator_of_notMem hxn,
          gammaSeqScalarKernel, indicator_of_notMem hxn,
          ofReal_zero, zero_mul]
    have hlim :
        gammaIntegralIntegrand s x =
          (gammaScalarKernel x : ℂ) *
            (x : ℂ) ^ (s - 1) := by
      rw [gammaIntegralIntegrand, indicator_of_mem hx,
        gammaScalarKernel, indicator_of_mem hx]
    rw [happ, hlim, ← sub_mul, norm_mul, ← ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx,
      sub_re, one_re, gammaSeqIntegralError,
      indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_left
      (rpow_re_sub_one_le_endpoint_sum hx ha hb)
      (abs_nonneg _)
  · have hxIoc : ∀ n : ℕ, x ∉ Ioc 0 (n : ℝ) :=
      fun _ h ↦ hx h.1
    rw [gammaSeqApproxIntegrand,
      indicator_of_notMem (hxIoc n),
      gammaIntegralIntegrand, indicator_of_notMem hx,
      sub_zero, norm_zero, gammaSeqIntegralError,
      indicator_of_notMem hx, mul_zero]

theorem norm_integral_gammaSeqApproxIntegrand_sub_le
    {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    (n : ℕ) :
    ‖(∫ x : ℝ, gammaSeqApproxIntegrand n s x) -
        ∫ x : ℝ, gammaIntegralIntegrand s x‖ ≤
      ∫ x : ℝ, gammaSeqIntegralError a b n x := by
  have hs : 0 < s.re := ha0.trans_le ha
  rw [← integral_sub
    (integrable_gammaSeqApproxIntegrand hs n)
    (integrable_gammaIntegralIntegrand hs)]
  exact norm_integral_le_of_norm_le
    (integrable_gammaSeqIntegralError ha0 hb0 n)
    (ae_of_all _ fun x ↦
      norm_gammaSeqApproxIntegrand_sub_le_error ha hb n x)

theorem tendstoUniformlyOn_integral_gammaSeqApproxIntegrand
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun n s ↦ ∫ x : ℝ, gammaSeqApproxIntegrand n s x)
      (fun s ↦ ∫ x : ℝ, gammaIntegralIntegrand s x)
      atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  have hb : 0 < b := ha.trans_le hab
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.1
      (tendsto_integral_gammaSeqIntegralError ha hb) ε hε
  filter_upwards [eventually_ge_atTop N] with n hn s hs
  rw [dist_eq_norm, norm_sub_rev]
  refine
    (norm_integral_gammaSeqApproxIntegrand_sub_le
      ha hb hs.1 hs.2 n).trans_lt ?_
  have hnonneg :
      0 ≤ ∫ x : ℝ, gammaSeqIntegralError a b n x :=
    integral_nonneg
      (fun x ↦ gammaSeqIntegralError_nonneg a b n x)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hN n hn

theorem tendstoUniformlyOn_GammaSeq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun n s ↦ Complex.GammaSeq s n)
      Complex.Gamma
      atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  have h :=
    tendstoUniformlyOn_integral_gammaSeqApproxIntegrand ha hab
  have h' := h.congr (by
    filter_upwards [eventually_ne_atTop 0] with n hn s hs
    exact integral_gammaSeqApproxIntegrand
      (ha.trans_le hs.1) hn)
  exact h'.congr_right fun s hs ↦
    integral_gammaIntegralIntegrand (ha.trans_le hs.1)

theorem tendstoLocallyUniformlyOn_GammaSeq :
    TendstoLocallyUniformlyOn
      (fun n s ↦ Complex.GammaSeq s n)
      Complex.Gamma
      atTop {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨smin, hsminK, hsmin⟩ :=
      hK.exists_isMinOn hKne continuous_re.continuousOn
    obtain ⟨smax, hsmaxK, hsmax⟩ :=
      hK.exists_isMaxOn hKne continuous_re.continuousOn
    have hamin : 0 < smin.re := hKsub hsminK
    have hab : smin.re ≤ smax.re :=
      isMinOn_iff.mp hsmin smax hsmaxK
    apply
      (tendstoUniformlyOn_GammaSeq hamin hab).mono
    intro s hsK
    exact
      ⟨isMinOn_iff.mp hsmin s hsK,
        isMaxOn_iff.mp hsmax s hsK⟩

end NumberField.Odlyzko
