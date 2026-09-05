/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all LeanPool.SpherePacking.SaddleAnalysis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# HarmonicAnalysis

Harmonic majorization and quantitative asymptotic estimates.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

private theorem saddleDigamma_add_one
    {m : ℝ} (hm : 0 < m) :
    saddleDigamma (m + 1) =
      saddleDigamma m + m⁻¹ := by
  unfold saddleDigamma
  rw [← deriv_comp_add_const,
    ← Real.deriv_log,
    ← deriv_add
      (saddleLogGamma_differentiableAt hm)
      (Real.differentiableAt_log hm.ne')]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hm]
    with x hx
  exact saddleLogGamma_add_one hx

private theorem saddleDigamma_add_nat
    {m : ℝ} (hm : 0 < m) (n : ℕ) :
    saddleDigamma (m + (n : ℝ)) =
      saddleDigamma m +
        ∑ k ∈ Finset.range n,
          (m + (k : ℝ))⁻¹ := by
  induction n with
  | zero => simp only [CharP.cast_eq_zero, add_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc,
      saddleDigamma_add_one (by positivity),
      ih, Finset.sum_range_succ]
    ring

private theorem tendsto_saddleEulerHarmonicCorrection
    {m : ℝ} (hm : 0 < m) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) -
          ∑ k ∈ Finset.range (n + 1),
            (m + (k : ℝ))⁻¹)
      atTop (𝓝 (saddleDigamma m)) := by
  have hcast := tendsto_natCast_atTop_atTop
    (R := ℝ)
  have hscale :
      Tendsto
        (fun n : ℕ => m + (n : ℝ) + 1)
        atTop atTop := by
    have h := hcast.atTop_add
      (tendsto_const_nhds (x := m + 1))
    convert! h using 1
    funext n
    ring
  have hdigamma :=
    tendsto_saddleDigamma_sub_log.comp hscale
  have hinv :=
    (tendsto_inv_atTop_nhds_zero_nat
      (𝕜 := ℝ)).const_mul (m + 1)
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (m + (n : ℝ) + 1) / (n : ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    have h :=
      (tendsto_const_nhds (x := (1 : ℝ))).add
        hinv
    have h' :
        Tendsto
          (fun n : ℕ =>
            1 + (m + 1) * (n : ℝ)⁻¹)
          atTop (𝓝 (1 : ℝ)) := by
      simpa only [mul_zero, add_zero] using! h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    have hnreal : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn.ne'
    field_simp [hnreal]
    ring
  have hlogratio := hratio.log
    (by norm_num : (1 : ℝ) ≠ 0)
  have hlogdiff :
      Tendsto
        (fun n : ℕ =>
          Real.log (m + (n : ℝ) + 1) -
            Real.log (n : ℝ))
        atTop (𝓝 0) := by
    have h :
        Tendsto
          (fun n : ℕ =>
            Real.log
              ((m + (n : ℝ) + 1) / (n : ℝ)))
          atTop (𝓝 0) := by
      simpa only [Real.log_one] using! hlogratio
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    have hnreal : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn.ne'
    have hmreal : m + (n : ℝ) + 1 ≠ 0 := by
      have : 0 < m + (n : ℝ) + 1 := by positivity
      exact this.ne'
    rw [Real.log_div hmreal hnreal]
  have hzero := (hdigamma.add hlogdiff).neg
  have hlimit := hzero.add_const (saddleDigamma m)
  have hlimit' :
      Tendsto
        (fun n : ℕ =>
          -((saddleDigamma (m + (n : ℝ) + 1) -
              Real.log (m + (n : ℝ) + 1)) +
            (Real.log (m + (n : ℝ) + 1) -
              Real.log (n : ℝ))) +
            saddleDigamma m)
        atTop (𝓝 (saddleDigamma m)) := by
    simpa only [sub_add_sub_cancel, neg_sub, Function.comp_apply, add_zero, neg_zero,
      zero_add] using! hlimit
  apply hlimit'.congr'
  filter_upwards [] with n
  have hrec := saddleDigamma_add_nat hm (n + 1)
  push_cast at hrec
  rw [show m + ((n : ℝ) + 1) =
    m + (n : ℝ) + 1 by ring] at hrec
  linarith

private noncomputable def upperCenteredLaplaceKernel
    (c T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
      Complex.I * ((a * T : ℝ) : ℂ)) *
    ((Real.exp (-c * a) / a : ℝ) : ℂ)

private theorem upperCenteredLaplaceKernel_eq_frullani_sub_laplace
    (c T : ℝ) {a : ℝ} (ha : a ≠ 0) :
    upperCenteredLaplaceKernel c T a =
      complexFrullaniKernel
        ((c : ℂ) - Complex.I * (T : ℂ))
        (c : ℂ) a -
      Complex.I * (T : ℂ) *
        Complex.exp (-(c : ℂ) * (a : ℂ)) := by
  have hbase :
      Complex.exp (-(c : ℂ) * (a : ℂ)) =
        (Real.exp (-c * a) : ℂ) := by
    calc
      Complex.exp (-(c : ℂ) * (a : ℂ)) =
          Complex.exp ((-c * a : ℝ) : ℂ) := by
        congr 1
        push_cast
        ring
      _ = (Real.exp (-c * a) : ℂ) := by
        exact (Complex.ofReal_exp (-c * a)).symm
  have hosc :
      Complex.exp
          (-((c : ℂ) - Complex.I * (T : ℂ)) *
            (a : ℂ)) =
        (Real.exp (-c * a) : ℂ) *
          upperImaginaryExp (a * T) := by
    have harg :
        -((c : ℂ) - Complex.I * (T : ℂ)) *
            (a : ℂ) =
          ((-c * a : ℝ) : ℂ) +
            Complex.I * ((a * T : ℝ) : ℂ) := by
      push_cast
      ring
    unfold upperImaginaryExp
    rw [harg, Complex.exp_add,
      ← Complex.ofReal_exp]
  unfold upperCenteredLaplaceKernel
    complexFrullaniKernel
  rw [hosc, hbase]
  push_cast
  have hac : (a : ℂ) ≠ 0 := by
    exact_mod_cast ha
  field_simp [hac]

private theorem upperCenteredLaplaceKernel_integrable
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    IntegrableOn (upperCenteredLaplaceKernel c T)
      (Ioi 0) := by
  let z : ℂ := (c : ℂ) - Complex.I * (T : ℂ)
  let w : ℂ := (c : ℂ)
  have hz : 0 < z.re := by simpa [z] using! hc
  have hw : 0 < w.re := by simpa only [Complex.ofReal_re] using! hc
  have hfrullani := complexFrullaniKernel_integrable hz hw
  have hlaplace :=
    (complexLaplaceKernel_integrable hw).const_mul
      (Complex.I * (T : ℂ))
  apply (hfrullani.sub hlaplace).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  exact (upperCenteredLaplaceKernel_eq_frullani_sub_laplace
    c T ha.ne').symm

private theorem integral_upperCenteredLaplaceKernel
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ a : ℝ in Ioi 0,
      upperCenteredLaplaceKernel c T a) =
      Complex.log (c : ℂ) -
        Complex.log ((c : ℂ) - Complex.I * (T : ℂ)) -
          Complex.I * (T : ℂ) * (c : ℂ)⁻¹ := by
  let z : ℂ := (c : ℂ) - Complex.I * (T : ℂ)
  let w : ℂ := (c : ℂ)
  have hz : 0 < z.re := by simpa [z] using! hc
  have hw : 0 < w.re := by simpa only [Complex.ofReal_re] using! hc
  have hfrullani := complexFrullaniKernel_integrable hz hw
  have hlaplace := complexLaplaceKernel_integrable hw
  calc
    (∫ a : ℝ in Ioi 0,
      upperCenteredLaplaceKernel c T a) =
        ∫ a : ℝ in Ioi 0,
          (complexFrullaniKernel z w a -
            Complex.I * (T : ℂ) *
              Complex.exp (-w * (a : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperCenteredLaplaceKernel_eq_frullani_sub_laplace
        c T ha.ne'
    _ = (∫ a : ℝ in Ioi 0,
          complexFrullaniKernel z w a) -
        Complex.I * (T : ℂ) *
          (∫ a : ℝ in Ioi 0,
            Complex.exp (-w * (a : ℂ))) := by
      rw [integral_sub hfrullani
        (hlaplace.const_mul (Complex.I * (T : ℂ))),
        integral_const_mul]
    _ = Complex.log (c : ℂ) -
        Complex.log ((c : ℂ) - Complex.I * (T : ℂ)) -
          Complex.I * (T : ℂ) * (c : ℂ)⁻¹ := by
      rw [integral_complexFrullaniKernel hz hw,
        integral_complexLaplaceKernel hw]

private noncomputable def upperGammaCenteredTruncatedKernel
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℂ :=
  upperCenteredLaplaceKernel η T a *
    ((∑ k ∈ Finset.range (n + 1),
      Real.exp (-(2 * a / ℓ)) ^ k : ℝ) : ℂ)

private theorem upperGammaCenteredTruncatedKernel_eq_sum
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    upperGammaCenteredTruncatedKernel ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCenteredLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by
  classical
  unfold upperGammaCenteredTruncatedKernel
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he :
      Complex.exp (-(η : ℂ) * (a : ℂ)) *
          Complex.exp (-(2 * (a : ℂ) / (ℓ : ℂ))) ^ k =
        Complex.exp
          (-((η : ℂ) + 2 * (k : ℂ) / (ℓ : ℂ)) *
            (a : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  unfold upperCenteredLaplaceKernel
  push_cast
  rw [← he]
  ring

private theorem upperGammaCenteredGeometricLimit_eq_kernel
    (ℓ η T a : ℝ) :
    upperCenteredLaplaceKernel η T a *
        (((1 - Real.exp (-(2 * a / ℓ)))⁻¹ : ℝ) : ℂ) =
      upperGammaCenteredKernel ℓ η T a := by
  simp only [upperCenteredLaplaceKernel, mul_comm, Complex.ofReal_mul, mul_neg, div_eq_mul_inv,
    Complex.ofReal_inv, Complex.ofReal_exp, Complex.ofReal_neg, mul_assoc, mul_left_comm,
      Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat, upperGammaCenteredKernel,
      upperGammaMeasureDensity, mul_inv_rev]

private theorem tendsto_integral_upperGammaCenteredTruncatedKernel
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ a : ℝ in Ioi 0,
          upperGammaCenteredTruncatedKernel ℓ η T n a)
      atTop (𝓝 (upperGammaCenteredPhase ℓ η T)) := by
  unfold upperGammaCenteredPhase
  refine tendsto_integral_of_dominated_convergence
    (fun a => ‖upperGammaCenteredKernel ℓ η T a‖) ?_
    ((upperGammaCenteredKernel_integrable hℓ hη T).norm) ?_ ?_
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold upperGammaCenteredTruncatedKernel
      upperCenteredLaplaceKernel upperImaginaryExp
    fun_prop
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hp : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          Real.exp (-(2 * a / ℓ)) ^ k) ≤
          (1 - Real.exp (-(2 * a / ℓ)))⁻¹ :=
      sum_le_hasSum (Finset.range (n + 1))
        (fun k hk => pow_nonneg hq0 k)
        (hasSum_geometric_of_lt_one hq0 hq1)
    have hsum0 :
        0 ≤ ∑ k ∈ Finset.range (n + 1),
          Real.exp (-(2 * a / ℓ)) ^ k :=
      Finset.sum_nonneg
        (fun k hk => pow_nonneg hq0 k)
    have hinv0 :
        0 ≤ (1 - Real.exp (-(2 * a / ℓ)))⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
    change
      ‖upperCenteredLaplaceKernel η T a *
          ((∑ k ∈ Finset.range (n + 1),
            Real.exp (-(2 * a / ℓ)) ^ k : ℝ) : ℂ)‖ ≤
        ‖upperGammaCenteredKernel ℓ η T a‖
    rw [← upperGammaCenteredGeometricLimit_eq_kernel,
      norm_mul, norm_mul,
      Complex.norm_of_nonneg hsum0,
      Complex.norm_of_nonneg hinv0]
    exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hp : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hgeo :=
      (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
    have hshift := hgeo.comp (tendsto_add_atTop_nat 1)
    have hlimit :=
      (tendsto_const_nhds
        (x := upperCenteredLaplaceKernel η T a)).mul
          hshift.ofReal
    simpa only [upperGammaCenteredTruncatedKernel,
      upperGammaCenteredGeometricLimit_eq_kernel,
      Function.comp_apply] using! hlimit

private theorem exp_integral_upperCenteredLaplaceKernel
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel c T a) =
      ((c : ℂ) / ((c : ℂ) - Complex.I * (T : ℂ))) *
        Complex.exp
          (-Complex.I * ((T / c : ℝ) : ℂ)) := by
  have hcn : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hzn : (c : ℂ) - Complex.I * (T : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.zero_re, ne_eq] using! hc.ne'
  have hphase :
      -(Complex.I * (T : ℂ) * (c : ℂ)⁻¹) =
        -Complex.I * ((T / c : ℝ) : ℂ) := by
    push_cast
    ring
  rw [integral_upperCenteredLaplaceKernel hc T]
  calc
    Complex.exp
        (Complex.log (c : ℂ) -
          Complex.log ((c : ℂ) - Complex.I * (T : ℂ)) -
          Complex.I * (T : ℂ) * (c : ℂ)⁻¹) =
        Complex.exp
          (Complex.log (c : ℂ) -
            Complex.log ((c : ℂ) - Complex.I * (T : ℂ))) *
          Complex.exp
            (-Complex.I * ((T / c : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [← hphase]
      ring
    _ = ((c : ℂ) / ((c : ℂ) - Complex.I * (T : ℂ))) *
        Complex.exp
          (-Complex.I * ((T / c : ℝ) : ℂ)) := by
      rw [Complex.exp_sub,
        Complex.exp_log hcn, Complex.exp_log hzn]

private theorem upperGammaEuler_centered_cpow_ratio
    (m b : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ ((m : ℂ) - Complex.I * (b : ℂ)) /
        (n : ℂ) ^ (m : ℂ) =
      Complex.exp
        (-Complex.I * ((b * Real.log (n : ℝ) : ℝ) : ℂ)) := by
  have hncomplex : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hncomplex,
    Complex.cpow_def_of_ne_zero hncomplex,
    ← Complex.exp_sub]
  rw [← Complex.natCast_log]
  congr 1
  push_cast
  ring

private theorem exp_integral_upperCenteredLaplaceKernel_scale
    {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (T : ℝ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel c T a) =
      (((s * c : ℝ) : ℂ) /
          (((s * c : ℝ) : ℂ) -
            Complex.I * ((s * T : ℝ) : ℂ))) *
        Complex.exp
          (-Complex.I *
            (((s * T / (s * c) : ℝ) : ℂ))) := by
  have hcn : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hsn : (s : ℂ) ≠ 0 := by
    exact_mod_cast hs.ne'
  have hzn : (c : ℂ) - Complex.I * (T : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.zero_re, ne_eq] using! hc.ne'
  have hratio :
      (c : ℂ) / ((c : ℂ) - Complex.I * (T : ℂ)) =
        (((s * c : ℝ) : ℂ) /
          (((s * c : ℝ) : ℂ) -
            Complex.I * ((s * T : ℝ) : ℂ))) := by
    push_cast
    field_simp [hcn, hsn, hzn]
  have hphase : T / c = s * T / (s * c) := by
    field_simp [hc.ne', hs.ne']
  rw [exp_integral_upperCenteredLaplaceKernel hc T,
    hratio, hphase]

private theorem exp_integral_upperGammaCenteredLaplaceRate
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (k : ℕ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperCenteredLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a) =
      ((((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) /
        (((ℓ * η / 2 : ℝ) : ℂ) -
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
            (k : ℂ)))) *
        Complex.exp
          (-Complex.I *
            (((ℓ * T / 2 /
              (ℓ * η / 2 + (k : ℝ)) : ℝ) : ℂ))) := by
  have hs : 0 < ℓ / 2 := by positivity
  have hc := upperGammaLaplaceRate_pos hℓ hη k
  have hreal :
      ℓ / 2 * (η + 2 * (k : ℝ) / ℓ) =
        ℓ * η / 2 + (k : ℝ) := by
    field_simp [hℓ.ne']
  have himag : ℓ / 2 * T = ℓ * T / 2 := by
    ring
  have harg :
      (((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) -
        Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) =
        ((ℓ * η / 2 : ℝ) : ℂ) -
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
            (k : ℂ) := by
    push_cast
    ring
  have h :=
    exp_integral_upperCenteredLaplaceKernel_scale
      hc hs T
  rw [hreal, himag, harg] at h
  exact h

private theorem upperGammaEuler_centered_ratio
    {m : ℝ} (hm : 0 < m) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    Complex.GammaSeq
        ((m : ℂ) - Complex.I * (b : ℂ)) n /
      Complex.GammaSeq (m : ℂ) n =
      Complex.exp
        (-Complex.I *
          ((b * Real.log (n : ℝ) : ℝ) : ℂ)) *
        ∏ k ∈ Finset.range (n + 1),
          (((m : ℂ) + (k : ℂ)) /
            ((m : ℂ) - Complex.I * (b : ℂ) + (k : ℂ))) := by
  classical
  let z : ℂ := (m : ℂ) - Complex.I * (b : ℂ)
  have hncomplex : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hpow : (n : ℂ) ^ (m : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hncomplex]
    exact Complex.exp_ne_zero _
  have hfactorial : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hreal (k : ℕ) :
      (m : ℂ) + (k : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.zero_re, ne_eq]
    exact (add_pos_of_pos_of_nonneg hm
      (Nat.cast_nonneg k)).ne'
  have hcomplex (k : ℕ) :
      z + (k : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.natCast_re,
        Complex.zero_re, ne_eq, z]
    exact (add_pos_of_pos_of_nonneg hm
      (Nat.cast_nonneg k)).ne'
  have hprodreal :
      (∏ k ∈ Finset.range (n + 1),
        ((m : ℂ) + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun k hk => hreal k)
  have hprodcomplex :
      (∏ k ∈ Finset.range (n + 1),
        (z + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun k hk => hcomplex k)
  change
    Complex.GammaSeq z n /
      Complex.GammaSeq (m : ℂ) n = _
  rw [← upperGammaEuler_centered_cpow_ratio m b hn,
    Finset.prod_div_distrib,
    Complex.GammaSeq, Complex.GammaSeq]
  change
    ((n : ℂ) ^ z * (n.factorial : ℂ) /
      (∏ k ∈ Finset.range (n + 1), (z + (k : ℂ)))) /
        ((n : ℂ) ^ (m : ℂ) * (n.factorial : ℂ) /
          (∏ k ∈ Finset.range (n + 1),
            ((m : ℂ) + (k : ℂ)))) =
      ((n : ℂ) ^ z / (n : ℂ) ^ (m : ℂ)) *
        ((∏ k ∈ Finset.range (n + 1),
          ((m : ℂ) + (k : ℂ))) /
          (∏ k ∈ Finset.range (n + 1),
            (z + (k : ℂ))))
  field_simp [hpow, hfactorial, hprodreal, hprodcomplex]

private theorem integral_upperGammaCenteredTruncatedKernel_eq_shell_sum
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (n : ℕ) :
    (∫ a : ℝ in Ioi 0,
      upperGammaCenteredTruncatedKernel ℓ η T n a) =
      ∑ k ∈ Finset.range (n + 1),
        (∫ a : ℝ in Ioi 0,
          upperCenteredLaplaceKernel
            (η + 2 * (k : ℝ) / ℓ) T a) := by
  classical
  calc
    (∫ a : ℝ in Ioi 0,
      upperGammaCenteredTruncatedKernel ℓ η T n a) =
        ∫ a : ℝ in Ioi 0,
          ∑ k ∈ Finset.range (n + 1),
            upperCenteredLaplaceKernel
              (η + 2 * (k : ℝ) / ℓ) T a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperGammaCenteredTruncatedKernel_eq_sum
        ℓ η T n a
    _ = ∑ k ∈ Finset.range (n + 1),
        (∫ a : ℝ in Ioi 0,
          upperCenteredLaplaceKernel
            (η + 2 * (k : ℝ) / ℓ) T a) := by
      apply integral_finsetSum
      intro k hk
      exact upperCenteredLaplaceKernel_integrable
        (upperGammaLaplaceRate_pos hℓ hη k) T

private theorem exp_integral_upperGammaCenteredTruncatedKernel_eq_product
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (n : ℕ) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
      (∏ k ∈ Finset.range (n + 1),
        ((((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) /
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
              (k : ℂ))))) *
        Complex.exp
          (-Complex.I *
            (((ℓ * T / 2 *
              (∑ k ∈ Finset.range (n + 1),
                (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
  classical
  rw [integral_upperGammaCenteredTruncatedKernel_eq_shell_sum
    hℓ hη T n, Complex.exp_sum]
  simp_rw [exp_integral_upperGammaCenteredLaplaceRate
    hℓ hη T]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  congr 1
  push_cast
  simp_rw [div_eq_mul_inv]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]

private theorem exp_integral_upperGammaCenteredTruncatedKernel
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) {n : ℕ} (hn : 0 < n) :
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
      (Complex.GammaSeq
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) n /
        Complex.GammaSeq
          ((ℓ * η / 2 : ℝ) : ℂ) n) *
        Complex.exp
          (Complex.I *
            (((ℓ * T / 2 *
              (Real.log (n : ℝ) -
                ∑ k ∈ Finset.range (n + 1),
                  (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
  classical
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hproduct :
      Complex.exp
        (∫ a : ℝ in Ioi 0,
          upperGammaCenteredTruncatedKernel ℓ η T n a) =
        (∏ k ∈ Finset.range (n + 1),
          (((m : ℂ) + (k : ℂ)) /
            ((m : ℂ) - Complex.I * (b : ℂ) +
              (k : ℂ)))) *
          Complex.exp
            (-Complex.I *
              (((b *
                (∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
    simpa [m, b] using!
      exp_integral_upperGammaCenteredTruncatedKernel_eq_product
        hℓ hη T n
  have hphase :
      Complex.exp
        (-Complex.I *
          (((b *
            (∑ k ∈ Finset.range (n + 1),
              (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) =
        Complex.exp
          (-Complex.I *
            ((b * Real.log (n : ℝ) : ℝ) : ℂ)) *
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  change
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
      (Complex.GammaSeq
          ((m : ℂ) - Complex.I * (b : ℂ)) n /
        Complex.GammaSeq (m : ℂ) n) *
        Complex.exp
          (Complex.I *
            (((b *
              (Real.log (n : ℝ) -
                ∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ)))
  calc
    Complex.exp
      (∫ a : ℝ in Ioi 0,
        upperGammaCenteredTruncatedKernel ℓ η T n a) =
        (∏ k ∈ Finset.range (n + 1),
          (((m : ℂ) + (k : ℂ)) /
            ((m : ℂ) - Complex.I * (b : ℂ) +
              (k : ℂ)))) *
          Complex.exp
            (-Complex.I *
              (((b *
                (∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := hproduct
    _ = (Complex.exp
          (-Complex.I *
            ((b * Real.log (n : ℝ) : ℝ) : ℂ)) *
          (∏ k ∈ Finset.range (n + 1),
            (((m : ℂ) + (k : ℂ)) /
              ((m : ℂ) - Complex.I * (b : ℂ) +
                (k : ℂ))))) *
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
      rw [hphase]
      ring
    _ = (Complex.GammaSeq
          ((m : ℂ) - Complex.I * (b : ℂ)) n /
        Complex.GammaSeq (m : ℂ) n) *
        Complex.exp
          (Complex.I *
            (((b *
              (Real.log (n : ℝ) -
                ∑ k ∈ Finset.range (n + 1),
                  (m + (k : ℝ))⁻¹) : ℝ) : ℂ))) := by
      rw [upperGammaEuler_centered_ratio hm b hn]

private theorem exp_upperGammaCenteredPhase
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Complex.exp (upperGammaCenteredPhase ℓ η T) =
      (Complex.Gamma
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) /
        (Real.Gamma (ℓ * η / 2) : ℂ)) *
        Complex.exp
          (Complex.I *
            ((ℓ * T / 2 *
              saddleDigamma (ℓ * η / 2) : ℝ) : ℂ)) := by
  classical
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hden : Complex.Gamma (m : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos
      (by simpa only [Complex.ofReal_re] using! hm)
  have hgamma :
      Tendsto
        (fun n : ℕ =>
          Complex.GammaSeq
              ((m : ℂ) - Complex.I * (b : ℂ)) n /
            Complex.GammaSeq (m : ℂ) n)
        atTop
        (𝓝 (Complex.Gamma
              ((m : ℂ) - Complex.I * (b : ℂ)) /
            Complex.Gamma (m : ℂ))) := by
    exact
      (Complex.GammaSeq_tendsto_Gamma
        ((m : ℂ) - Complex.I * (b : ℂ))).div
          (Complex.GammaSeq_tendsto_Gamma (m : ℂ))
          hden
  have hcorrection :
      Tendsto
        (fun n : ℕ =>
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ))))
        atTop
        (𝓝
          (Complex.exp
            (Complex.I *
              ((b * saddleDigamma m : ℝ) : ℂ)))) := by
    have hreal :=
      (tendsto_saddleEulerHarmonicCorrection hm).const_mul b
    have hcomplex := hreal.ofReal
    have himag := hcomplex.const_mul Complex.I
    simpa only [Function.comp_apply] using! himag.cexp
  have hright := hgamma.mul hcorrection
  have hleft :=
    (tendsto_integral_upperGammaCenteredTruncatedKernel
      hℓ hη T).cexp
  have hfinite :
      (fun n : ℕ =>
        Complex.exp
          (∫ a : ℝ in Ioi 0,
            upperGammaCenteredTruncatedKernel ℓ η T n a)) =ᶠ[atTop]
      (fun n : ℕ =>
        (Complex.GammaSeq
            ((m : ℂ) - Complex.I * (b : ℂ)) n /
          Complex.GammaSeq (m : ℂ) n) *
          Complex.exp
            (Complex.I *
              (((b *
                (Real.log (n : ℝ) -
                  ∑ k ∈ Finset.range (n + 1),
                    (m + (k : ℝ))⁻¹) : ℝ) : ℂ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    simpa [m, b] using!
      exp_integral_upperGammaCenteredTruncatedKernel
        hℓ hη T hn
  have hmatch :=
    Filter.Tendsto.congr' hfinite.symm hright
  have hidentity := tendsto_nhds_unique hleft hmatch
  rw [Complex.Gamma_ofReal] at hidentity
  exact hidentity

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private noncomputable def saddleSourceStationaryLogRadius
    (ε ℓ u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (ℓ * (1 + u) / 2) / 2 +
      saddleSourceShellDerivative ε u

private theorem saddleSourceStationaryLogRadius_eq_saddleLogRadius
    (ε : ℝ) (d : ℕ) (u : ℝ) :
    saddleSourceStationaryLogRadius ε ((d : ℝ) / 2) u =
      saddleLogRadius ε d u := by
  rw [saddleLogRadius_eq_digamma_add_shellDerivative]
  rfl

private noncomputable def saddleSourceCenteredPhase
    (ε ℓ u T : ℝ) : ℂ :=
  upperGammaCenteredPhase ℓ (1 + u) T +
    saddleSourceShellCenteredPhase ε ℓ u T

private theorem saddleSourceCenteredPhase_cubic_remainder_norm_le
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (T : ℝ) :
    ‖saddleSourceCenteredPhase ε ℓ u T +
        ((ℓ * saddleSourceGaussianVariance ε ℓ u / 2 *
          T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 := by
  have hη : 0 < 1 + u := by linarith
  have hgamma :=
    upperGammaCenteredPhase_cubic_remainder_norm_le
      hℓ hη T
  have hshell :=
    saddleSourceShellCenteredPhase_cubic_remainder_norm_le
      hε hℓ.le horder hmargin u T
  have heq :
      saddleSourceCenteredPhase ε ℓ u T +
          ((ℓ * saddleSourceGaussianVariance ε ℓ u / 2 *
            T ^ 2 : ℝ) : ℂ) =
        (upperGammaCenteredPhase ℓ (1 + u) T +
          ((ℓ * upperGammaVariance ℓ (1 + u) / 2 *
            T ^ 2 : ℝ) : ℂ)) +
        (saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ)) := by
    unfold saddleSourceCenteredPhase
      saddleSourceGaussianVariance upperSaddleVariance
    have harg : 2 + (u - 1) = 1 + u := by ring
    rw [harg]
    push_cast
    ring
  rw [heq]
  calc
    ‖(upperGammaCenteredPhase ℓ (1 + u) T +
          ((ℓ * upperGammaVariance ℓ (1 + u) / 2 *
            T ^ 2 : ℝ) : ℂ)) +
        (saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ))‖ ≤
      ‖upperGammaCenteredPhase ℓ (1 + u) T +
          ((ℓ * upperGammaVariance ℓ (1 + u) / 2 *
            T ^ 2 : ℝ) : ℂ)‖ +
        ‖saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ (ℓ * upperGammaThirdMoment ℓ (1 + u) / 6) *
          |T| ^ 3 +
        (ℓ * upperNetShellThirdMoment ε (u - 1) / 6) *
          |T| ^ 3 :=
          add_le_add hgamma hshell
    _ = (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 := by
          unfold upperSaddleThirdMoment
          have harg : 2 + (u - 1) = 1 + u := by ring
          rw [harg]
          ring

private theorem saddleSourceContour_piExponential_eq
    (ℓ u T : ℝ) :
    Complex.exp
        (((ℓ : ℂ) - saddleSourceMellinContour ℓ u T) *
          (Real.log Real.pi : ℂ) / 2) =
      (Real.exp (-(ℓ * u) * Real.log Real.pi / 2) : ℂ) *
        Complex.exp
          (Complex.I *
            ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold saddleSourceMellinContour
  push_cast
  ring

private theorem saddleSourceContour_shellExponential_eq
    (ε ℓ u T : ℝ) :
    Complex.exp
        ((ℓ : ℂ) *
          mellinShellPhase ε
            ((T : ℂ) + Complex.I * (u : ℂ))) =
      (Real.exp (ℓ * realHyperbolicShellPhase ε u) : ℂ) *
        Complex.exp
          ((ℓ : ℂ) *
            (mellinShellPhase ε
                ((T : ℂ) + Complex.I * (u : ℂ)) -
              (realHyperbolicShellPhase ε u : ℂ))) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem saddleSourceCenteredEnvelope_eq_gamma_shell
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (v T : ℝ) :
    saddleSourceCenteredEnvelope ε ℓ u v T =
      (Complex.Gamma
          (((ℓ * (1 + u) / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) /
        (Real.Gamma (ℓ * (1 + u) / 2) : ℂ)) *
      Complex.exp
        ((ℓ : ℂ) *
          (mellinShellPhase ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            (realHyperbolicShellPhase ε u : ℂ))) *
      (Complex.exp
        (Complex.I *
          ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) *
        Complex.exp
          (Complex.I * ((ℓ * T * v : ℝ) : ℂ))) := by
  have hη : 0 < 1 + u := by linarith
  have hm : 0 < ℓ * (1 + u) / 2 := by positivity
  have hG :
      (Real.Gamma (ℓ * (1 + u) / 2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.Gamma_pos_of_pos hm).ne'
  have hπ :
      (Real.exp (-(ℓ * u) * Real.log Real.pi / 2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hs :
      (Real.exp (ℓ * realHyperbolicShellPhase ε u) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  unfold saddleSourceCenteredEnvelope
    saddleSourceNormalizedEnvelope saddleMellinEnvelope
    saddleSourceContourEnvelopeScale
  rw [saddleSourceMellinContour_shellArgument hℓ,
    saddleSourceMellinContour_gammaArgument,
    saddleSourceContour_piExponential_eq,
    saddleSourceContour_shellExponential_eq]
  push_cast
  field_simp [hπ, hG, hs]

private theorem saddleSourceStationaryFrequencyPhase_eq
    (ε ℓ u T : ℝ) :
    Complex.exp
        (Complex.I *
          ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) *
      Complex.exp
        (Complex.I *
          ((ℓ * T *
            saddleSourceStationaryLogRadius ε ℓ u : ℝ) : ℂ)) =
    Complex.exp
        (Complex.I *
          ((ℓ * T / 2 *
            saddleDigamma (ℓ * (1 + u) / 2) : ℝ) : ℂ)) *
      Complex.exp
        (Complex.I *
          ((ℓ * T * saddleSourceShellDerivative ε u : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold saddleSourceStationaryLogRadius
  push_cast
  ring

private theorem exp_saddleSourceShellCenteredPhase
    (ε ℓ u T : ℝ) :
    Complex.exp (saddleSourceShellCenteredPhase ε ℓ u T) =
      Complex.exp
        ((ℓ : ℂ) *
          (mellinShellPhase ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            (realHyperbolicShellPhase ε u : ℂ))) *
        Complex.exp
          (Complex.I *
            ((ℓ * T * saddleSourceShellDerivative ε u : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  unfold saddleSourceShellCenteredPhase
  push_cast
  ring

private theorem saddleSourceCenteredEnvelope_stationary_eq_exp_phase
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (T : ℝ) :
    saddleSourceCenteredEnvelope ε ℓ u
        (saddleSourceStationaryLogRadius ε ℓ u) T =
      Complex.exp (saddleSourceCenteredPhase ε ℓ u T) := by
  have hη : 0 < 1 + u := by linarith
  rw [saddleSourceCenteredEnvelope_eq_gamma_shell
    hℓ hu]
  rw [saddleSourceStationaryFrequencyPhase_eq]
  unfold saddleSourceCenteredPhase
  rw [Complex.exp_add,
    exp_upperGammaCenteredPhase hℓ hη T,
    exp_saddleSourceShellCenteredPhase]
  ring

private noncomputable def saddleSourceGaussianPhaseRemainder
    (ε ℓ u T : ℝ) : ℂ :=
  saddleSourceCenteredPhase ε ℓ u T +
    ((ℓ * saddleSourceGaussianVariance ε ℓ u / 2 *
      T ^ 2 : ℝ) : ℂ)

private theorem exp_saddleSourceCenteredPhase_eq_gaussian_mul
    (ε ℓ u T : ℝ) :
    Complex.exp (saddleSourceCenteredPhase ε ℓ u T) =
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
        Complex.exp
          (saddleSourceGaussianPhaseRemainder ε ℓ u T) := by
  unfold saddleSourceGaussianKernel
    saddleSourceGaussianPhaseRemainder
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem saddleSourceCenteredEnvelope_stationary_gaussian_error_le
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (T : ℝ)
    (hsmall :
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ 1) :
    ‖saddleSourceCenteredEnvelope ε ℓ u
        (saddleSourceStationaryLogRadius ε ℓ u) T -
      (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
      2 * saddleSourceGaussianKernel ε ℓ u T *
        ((ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
          |T| ^ 3) := by
  let R : ℂ := saddleSourceGaussianPhaseRemainder ε ℓ u T
  let q : ℝ :=
    (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
      |T| ^ 3
  have hR : ‖R‖ ≤ q := by
    exact saddleSourceCenteredPhase_cubic_remainder_norm_le
      hε hℓ hu horder hmargin T
  have hRone : ‖R‖ ≤ 1 := hR.trans hsmall
  have hg : 0 < saddleSourceGaussianKernel ε ℓ u T := by
    unfold saddleSourceGaussianKernel
    exact Real.exp_pos _
  rw [saddleSourceCenteredEnvelope_stationary_eq_exp_phase
    hℓ hu T,
    exp_saddleSourceCenteredPhase_eq_gaussian_mul]
  have hfactor :
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
          Complex.exp R -
        (saddleSourceGaussianKernel ε ℓ u T : ℂ) =
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
        (Complex.exp R - 1) := by
    ring
  change
    ‖(saddleSourceGaussianKernel ε ℓ u T : ℂ) *
          Complex.exp R -
        (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
      2 * saddleSourceGaussianKernel ε ℓ u T * q
  rw [hfactor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hg]
  calc
    saddleSourceGaussianKernel ε ℓ u T *
        ‖Complex.exp R - 1‖ ≤
      saddleSourceGaussianKernel ε ℓ u T *
        (2 * ‖R‖) :=
      mul_le_mul_of_nonneg_left
        (Complex.norm_exp_sub_one_le hRone) hg.le
    _ ≤ saddleSourceGaussianKernel ε ℓ u T *
        (2 * q) := by
      gcongr
    _ = 2 * saddleSourceGaussianKernel ε ℓ u T * q := by
      ring

end

section

open Filter MeasureTheory Set
open scoped Topology

private theorem saddleSourceCenteredPolynomial_centralGaussianError_le
    {ε ℓ u R q p : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hp : 0 ≤ p)
    (P : ℂ → ℂ)
    (hsource : Integrable (fun T : ℝ =>
      saddleSourceCenteredEnvelope ε ℓ u
        (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + Complex.I * (u : ℂ))))
    (hcubic : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖P ((T : ℂ) + Complex.I * (u : ℂ)) -
        P (Complex.I * (u : ℂ))‖ ≤
          p * ‖P (Complex.I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + Complex.I * (u : ℂ)) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
              P (Complex.I * (u : ℂ)))‖ ≤
      (2 * q + (1 + 2 * q) * p) *
        ‖P (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  have _hR : 0 ≤ R := hR
  let z : ℂ := Complex.I * (u : ℂ)
  let c : ℝ :=
    (2 * q + (1 + 2 * q) * p) * ‖P z‖
  have hc : 0 ≤ c := by
    try dsimp [c]
    positivity
  have hgaussian := saddleSourceGaussianKernel_integrable hℓ hV
  have hgaussianPoly : Integrable (fun T : ℝ =>
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z) :=
    hgaussian.ofReal.mul_const (P z)
  have hintegrable : Integrable (fun T : ℝ =>
      saddleSourceCenteredEnvelope ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T *
        P ((T : ℂ) + z) -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z) := by
    exact hsource.sub hgaussianPoly
  have hmajor : Integrable
      (fun T : ℝ => c * saddleSourceGaussianKernel ε ℓ u T) :=
    hgaussian.const_mul c
  have hpoint : ∀ T ∈ Icc (-R) R,
      ‖saddleSourceCenteredEnvelope ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T *
        P ((T : ℂ) + z) -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z‖ ≤
        c * saddleSourceGaussianKernel ε ℓ u T := by
    intro T hT
    have hTabs : |T| ≤ R :=
      (abs_le).mpr ⟨hT.1, hT.2⟩
    have hthird := hcubic T hTabs
    have hsmall :
        (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
          |T| ^ 3 ≤ 1 := hthird.trans hqone
    have henv :=
      saddleSourceCenteredEnvelope_stationary_gaussian_error_le
        hε hℓ hu horder hmargin T hsmall
    have henvq :
        ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
          2 * saddleSourceGaussianKernel ε ℓ u T * q := by
      calc
        ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
          2 * saddleSourceGaussianKernel ε ℓ u T *
            ((ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
              |T| ^ 3) := henv
        _ ≤ 2 * saddleSourceGaussianKernel ε ℓ u T * q := by
          exact mul_le_mul_of_nonneg_left hthird (by
            unfold saddleSourceGaussianKernel
            positivity)
    have hpolyT :
        ‖P ((T : ℂ) + z) - P z‖ ≤ p * ‖P z‖ := by
      exact hpoly T hTabs
    have hpolynorm :
        ‖P ((T : ℂ) + z)‖ ≤ (1 + p) * ‖P z‖ := by
      calc
        ‖P ((T : ℂ) + z)‖ =
          ‖(P ((T : ℂ) + z) - P z) + P z‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖P ((T : ℂ) + z) - P z‖ + ‖P z‖ :=
          norm_add_le _ _
        _ ≤ p * ‖P z‖ + ‖P z‖ := by
          gcongr
        _ = (1 + p) * ‖P z‖ := by ring
    have hg : 0 ≤ saddleSourceGaussianKernel ε ℓ u T := by
      unfold saddleSourceGaussianKernel
      exact (Real.exp_pos _).le
    have hdecomp :
        saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + z) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z =
          (saddleSourceCenteredEnvelope ε ℓ u
              (saddleSourceStationaryLogRadius ε ℓ u) T -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ)) *
              P ((T : ℂ) + z) +
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
              (P ((T : ℂ) + z) - P z) := by
      ring
    rw [hdecomp]
    calc
      ‖(saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)) *
            P ((T : ℂ) + z) +
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
            (P ((T : ℂ) + z) - P z)‖ ≤
        ‖(saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)) *
            P ((T : ℂ) + z)‖ +
          ‖(saddleSourceGaussianKernel ε ℓ u T : ℂ) *
            (P ((T : ℂ) + z) - P z)‖ :=
          norm_add_le _ _
      _ = ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ *
            ‖P ((T : ℂ) + z)‖ +
          saddleSourceGaussianKernel ε ℓ u T *
            ‖P ((T : ℂ) + z) - P z‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hg]
      _ ≤ (2 * saddleSourceGaussianKernel ε ℓ u T * q) *
            ((1 + p) * ‖P z‖) +
          saddleSourceGaussianKernel ε ℓ u T *
            (p * ‖P z‖) := by
          gcongr
      _ = c * saddleSourceGaussianKernel ε ℓ u T := by
        try dsimp [c]
        ring
  have hcomparison := setIntegral_mono_on
    hintegrable.norm.integrableOn hmajor.integrableOn
      measurableSet_Icc hpoint
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ => c * saddleSourceGaussianKernel ε ℓ u T) := by
    exact Filter.Eventually.of_forall (fun T =>
      mul_nonneg hc (Real.exp_pos _).le)
  calc
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + Complex.I * (u : ℂ)) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
              P (Complex.I * (u : ℂ)))‖ ≤
      ∫ T : ℝ in Icc (-R) R,
        ‖saddleSourceCenteredEnvelope ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T *
          P ((T : ℂ) + z) -
            (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P z‖ := by
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ T : ℝ in Icc (-R) R,
      c * saddleSourceGaussianKernel ε ℓ u T := hcomparison
    _ ≤ ∫ T : ℝ,
      c * saddleSourceGaussianKernel ε ℓ u T :=
        setIntegral_le_integral hmajor hnonnegative
    _ = (2 * q + (1 + 2 * q) * p) *
        ‖P (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
      rw [integral_const_mul]

private theorem saddleSourceCenteredPlusIntegrand_centralGaussianError_le
    {ε ℓ u R q p : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hp : 0 ≤ p)
    (hcubic : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          p * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredPlusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ ≤
      (2 * q + (1 + 2 * q) * p) *
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  exact saddleSourceCenteredPolynomial_centralGaussianError_le
    hε hℓ hu horder hmargin hV hR hq hqone hp
    (plusPolynomial ε)
    (saddleSourceCenteredPlusIntegrand_integrable
      hε hℓ hu horder (saddleSourceStationaryLogRadius ε ℓ u))
    hcubic hpoly

private theorem saddleSourceCenteredMinusIntegrand_centralGaussianError_le
    {ε ℓ u R q p : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hp : 0 ≤ p)
    (hcubic : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          p * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredMinusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ ≤
      (2 * q + (1 + 2 * q) * p) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  exact saddleSourceCenteredPolynomial_centralGaussianError_le
    hε hℓ hu horder hmargin hV hR hq hqone hp
    (minusPolynomial ε)
    (saddleSourceCenteredMinusIntegrand_integrable
      hε hℓ hu horder (saddleSourceStationaryLogRadius ε ℓ u))
    hcubic hpoly

end

section

open Filter Set MeasureTheory
open scoped Topology

private noncomputable def saddleGaussianTailWeight (T : ℝ) : ℝ :=
  1 + |T| ^ 3

private theorem saddleGaussianTailWeight_nonneg (T : ℝ) :
    0 ≤ saddleGaussianTailWeight T := by
  unfold saddleGaussianTailWeight
  positivity

private theorem saddle_abs_le_exp_sq (T : ℝ) :
    |T| ≤ Real.exp (T ^ 2) := by
  have hsquare : (|T| - 1) ^ 2 ≥ 0 := sq_nonneg _
  have habs : |T| ^ 2 = T ^ 2 := sq_abs T
  have hlinear : |T| ≤ 1 + T ^ 2 := by
    linarith [abs_nonneg T, sq_nonneg T]
  exact hlinear.trans (by
    simpa only [add_comm] using! Real.add_one_le_exp (T ^ 2))

private theorem saddleGaussianTailWeight_le_two_exp_three_sq (T : ℝ) :
    saddleGaussianTailWeight T ≤
      2 * Real.exp (3 * T ^ 2) := by
  have habs := saddle_abs_le_exp_sq T
  have hcube : |T| ^ 3 ≤ (Real.exp (T ^ 2)) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg T) habs 3
  have hexpcube : (Real.exp (T ^ 2)) ^ 3 =
      Real.exp (3 * T ^ 2) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hone : 1 ≤ Real.exp (3 * T ^ 2) := by
    exact (Real.one_le_exp_iff).mpr (by positivity)
  unfold saddleGaussianTailWeight
  rw [hexpcube] at hcube
  linarith

private theorem saddleGaussianTailWeight_le_two_exp_three_abs (T : ℝ) :
    saddleGaussianTailWeight T ≤
      2 * Real.exp (3 * |T|) := by
  have hlinear : |T| ≤ Real.exp |T| := by
    calc
      |T| ≤ 1 + |T| := by linarith
      _ ≤ Real.exp |T| := by
        simpa only [add_comm] using! Real.add_one_le_exp |T|
  have hcube : |T| ^ 3 ≤ (Real.exp |T|) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg T) hlinear 3
  have hexpcube : (Real.exp |T|) ^ 3 =
      Real.exp (3 * |T|) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hone : 1 ≤ Real.exp (3 * |T|) := by
    exact (Real.one_le_exp_iff).mpr (by positivity)
  unfold saddleGaussianTailWeight
  rw [hexpcube] at hcube
  linarith

private theorem saddle_integral_exp_neg_mul_abs
    {a : ℝ} (ha : 0 < a) :
    (∫ T : ℝ, Real.exp (-a * |T|)) = 2 / a := by
  have hhalf := integral_exp_mul_Ioi
    (neg_lt_zero.mpr ha) (0 : ℝ)
  calc
    (∫ T : ℝ, Real.exp (-a * |T|)) =
        2 * ∫ T : ℝ in Ioi (0 : ℝ),
          Real.exp (-a * T) :=
      (integral_comp_abs
        (f := fun T : ℝ => Real.exp (-a * T)))
    _ = 2 / a := by
      rw [hhalf]
      simp only [mul_zero, Real.exp_zero, div_eq_mul_inv, inv_neg, mul_neg, neg_mul, one_mul,
        neg_neg]

private theorem saddleGaussianTailWeight_mul_gaussian_integrable
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2)) := by
  have hzero := integrable_exp_neg_mul_sq hk
  have hthree := integrable_rpow_mul_exp_neg_mul_sq
    hk (s := (3 : ℝ)) (by norm_num)
  have hpolynomial : Integrable
      (fun T : ℝ => T ^ 3 * Real.exp (-k * T ^ 2)) := by
    simpa only [neg_mul, Real.rpow_ofNat] using! hthree
  have hsum := hzero.add hpolynomial.norm
  apply hsum.congr
  filter_upwards [] with T
  simp only [neg_mul, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Pi.add_apply,
    saddleGaussianTailWeight, add_mul, one_mul]

private theorem saddleGaussianTailWeight_mul_exp_abs_integrable
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-k * |T|)) := by
  have hzero := integrable_exp_neg_mul_abs hk
  have hthree := integrable_abs_pow_mul_exp_neg_mul_abs 3 hk
  have hsum := hzero.add hthree
  apply hsum.congr
  filter_upwards [] with T
  simp only [neg_mul, Pi.add_apply, saddleGaussianTailWeight, add_mul, one_mul]

private noncomputable def saddleGaussianTailSet (R : ℝ) : Set ℝ :=
  {T : ℝ | R ≤ |T|}

private theorem saddleGaussianTailSet_measurable (R : ℝ) :
    MeasurableSet (saddleGaussianTailSet R) := by
  unfold saddleGaussianTailSet
  exact measurableSet_le measurable_const measurable_abs

private theorem saddleGaussian_cubic_tail_integral_le
    {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      2 * Real.exp (-(k / 4) * R ^ 2) *
        Real.sqrt (Real.pi / (k / 4)) := by
  have hkpos : 0 < k := by linarith
  have hquarter : 0 < k / 4 := by positivity
  let c : ℝ := 2 * Real.exp (-(k / 4) * R ^ 2)
  have hc : 0 ≤ c := by
    try dsimp [c]
    positivity
  have hsource :=
    saddleGaussianTailWeight_mul_gaussian_integrable hkpos
  have hgaussian := integrable_exp_neg_mul_sq hquarter
  have hmajor : Integrable
      (fun T : ℝ => c * Real.exp (-(k / 4) * T ^ 2)) :=
    hgaussian.const_mul c
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleGaussianTailWeight T * Real.exp (-k * T ^ 2) ≤
        c * Real.exp (-(k / 4) * T ^ 2) := by
    intro T hT
    change R ≤ |T| at hT
    have hsq : R ^ 2 ≤ T ^ 2 := by
      have h := pow_le_pow_left₀ hR hT 2
      simpa only [ge_iff_le, sq_abs] using! h
    have hexponent :
        3 * T ^ 2 + (-k * T ^ 2) ≤
          (-(k / 4) * R ^ 2) +
            (-(k / 4) * T ^ 2) := by
      linarith [
        mul_nonneg (show 0 ≤ k - 6 by linarith)
          (sq_nonneg T),
        mul_nonneg (show 0 ≤ k by linarith)
          (show 0 ≤ T ^ 2 - R ^ 2 by linarith)]
    calc
      saddleGaussianTailWeight T * Real.exp (-k * T ^ 2) ≤
          (2 * Real.exp (3 * T ^ 2)) *
            Real.exp (-k * T ^ 2) := by
              gcongr
              exact saddleGaussianTailWeight_le_two_exp_three_sq T
      _ = 2 * Real.exp
          (3 * T ^ 2 + (-k * T ^ 2)) := by
            rw [Real.exp_add]
            ring
      _ ≤ 2 * Real.exp
          (-(k / 4) * R ^ 2 +
            (-(k / 4) * T ^ 2)) := by
              gcongr
      _ = c * Real.exp (-(k / 4) * T ^ 2) := by
            try dsimp [c]
            rw [Real.exp_add]
            ring
  have hcompare := setIntegral_mono_on
    hsource.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R) hpoint
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ => c * Real.exp (-(k / 4) * T ^ 2)) :=
    Filter.Eventually.of_forall fun T =>
      mul_nonneg hc (Real.exp_pos _).le
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        c * Real.exp (-(k / 4) * T ^ 2) := hcompare
    _ ≤ ∫ T : ℝ,
        c * Real.exp (-(k / 4) * T ^ 2) :=
      setIntegral_le_integral hmajor hnonnegative
    _ = 2 * Real.exp (-(k / 4) * R ^ 2) *
        Real.sqrt (Real.pi / (k / 4)) := by
      rw [integral_const_mul, integral_gaussian]

private theorem saddleExponential_cubic_tail_integral_le
    {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      2 * Real.exp (-(k / 4) * R) *
        (2 / (k / 4)) := by
  have hkpos : 0 < k := by linarith
  have hquarter : 0 < k / 4 := by positivity
  let c : ℝ := 2 * Real.exp (-(k / 4) * R)
  have hc : 0 ≤ c := by
    try dsimp [c]
    positivity
  have hsource :=
    saddleGaussianTailWeight_mul_exp_abs_integrable hkpos
  have habs := integrable_exp_neg_mul_abs hquarter
  have hmajor : Integrable
      (fun T : ℝ => c * Real.exp (-(k / 4) * |T|)) :=
    habs.const_mul c
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleGaussianTailWeight T * Real.exp (-k * |T|) ≤
        c * Real.exp (-(k / 4) * |T|) := by
    intro T hT
    change R ≤ |T| at hT
    have hTabs : 0 ≤ |T| := hR.trans hT
    have hexponent :
        3 * |T| + (-k * |T|) ≤
          (-(k / 4) * R) + (-(k / 4) * |T|) := by
      linarith [
        mul_nonneg (show 0 ≤ k - 6 by linarith)
          hTabs,
        mul_nonneg (show 0 ≤ k by linarith)
          (show 0 ≤ |T| - R by linarith)]
    calc
      saddleGaussianTailWeight T * Real.exp (-k * |T|) ≤
          (2 * Real.exp (3 * |T|)) *
            Real.exp (-k * |T|) := by
              gcongr
              exact saddleGaussianTailWeight_le_two_exp_three_abs T
      _ = 2 * Real.exp
          (3 * |T| + (-k * |T|)) := by
            rw [Real.exp_add]
            ring
      _ ≤ 2 * Real.exp
          (-(k / 4) * R + (-(k / 4) * |T|)) := by
              gcongr
      _ = c * Real.exp (-(k / 4) * |T|) := by
            try dsimp [c]
            rw [Real.exp_add]
            ring
  have hcompare := setIntegral_mono_on
    hsource.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R) hpoint
  have hnonnegative :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ => c * Real.exp (-(k / 4) * |T|)) :=
    Filter.Eventually.of_forall fun T =>
      mul_nonneg hc (Real.exp_pos _).le
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        c * Real.exp (-(k / 4) * |T|) := hcompare
    _ ≤ ∫ T : ℝ,
        c * Real.exp (-(k / 4) * |T|) :=
      setIntegral_le_integral hmajor hnonnegative
    _ = 2 * Real.exp (-(k / 4) * R) *
        (2 / (k / 4)) := by
      rw [integral_const_mul,
        saddle_integral_exp_neg_mul_abs hquarter]

private noncomputable def saddleGaussianOuterPhi
    (B Q c ℓ δ : ℝ) : ℝ :=
  (B + 1) / 2 * δ + 4 * Real.log (2 + δ) -
    c * ℓ * Q * Real.exp (B * δ)

private theorem saddleGaussianOuterPhi_le_endpointBarrier
    {B Q c ℓ δ₀ δ : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hℓ : 0 ≤ ℓ) (hδ₀ : 0 ≤ δ₀) (hδ : δ₀ ≤ δ)
    (hscale :
      (B + 1) / 2 + 4 ≤
        c * ℓ * Q * B * Real.exp (B * δ₀)) :
    saddleGaussianOuterPhi B Q c ℓ δ ≤
      ((B + 1) / 2 + 4) * δ₀ + 4 -
        c * ℓ * Q * Real.exp (B * δ₀) := by
  have hδnonneg : 0 ≤ δ := hδ₀.trans hδ
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 2 + δ by linarith)
  have hexpstep :
      Real.exp (B * δ₀) *
          (1 + B * (δ - δ₀)) ≤
        Real.exp (B * δ) := by
    calc
      Real.exp (B * δ₀) *
          (1 + B * (δ - δ₀)) ≤
        Real.exp (B * δ₀) *
          Real.exp (B * (δ - δ₀)) := by
            gcongr
            simpa only [add_comm] using!
              Real.add_one_le_exp (B * (δ - δ₀))
      _ = Real.exp (B * δ) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hdifference :
      Real.exp (B * δ₀) * (B * (δ - δ₀)) ≤
        Real.exp (B * δ) - Real.exp (B * δ₀) := by
    linarith
  have hcoefficient : 0 ≤ c * ℓ * Q := by
    apply (mul_nonneg_iff_of_pos_right hB).mp
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hc.le hℓ) hQ.le) hB.le
  have hexpscaled :=
    mul_le_mul_of_nonneg_left hdifference hcoefficient
  have hlinearscaled :=
    mul_le_mul_of_nonneg_right hscale
      (show 0 ≤ δ - δ₀ by linarith)
  unfold saddleGaussianOuterPhi
  linarith

private theorem eventually_saddleGaussianOuterPhi_uniform
    {B Q c δ₀ : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hδ₀ : 0 ≤ δ₀) :
    ∀ κ : ℝ, 0 < κ →
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, δ₀ ≤ δ →
          Real.sqrt ℓ *
              Real.exp (saddleGaussianOuterPhi B Q c ℓ δ) < κ := by
  let s : ℝ := c * Q * Real.exp (B * δ₀)
  let A : ℝ := (B + 1) / 2 + 4
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have htendsto : Tendsto
      (fun ℓ : ℝ =>
        Real.sqrt ℓ *
          Real.exp (A * δ₀ + 4 - s * ℓ))
      atTop (𝓝 (0 : ℝ)) := by
    have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 / 2 : ℝ) s hs
    have hscaled : Tendsto
        (fun ℓ : ℝ =>
          Real.exp (A * δ₀ + 4) *
            (ℓ ^ (1 / 2 : ℝ) * Real.exp (-s * ℓ)))
        atTop (𝓝 (0 : ℝ)) := by
      convert!
        (tendsto_const_nhds
          (x := Real.exp (A * δ₀ + 4))).mul hbase using 1; simp only [mul_zero]
    apply hscaled.congr'
    filter_upwards [] with ℓ
    symm
    rw [Real.sqrt_eq_rpow]
    have hexp :
        Real.exp (A * δ₀ + 4 - s * ℓ) =
          Real.exp (A * δ₀ + 4) *
            Real.exp (-s * ℓ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  intro κ hκ
  have hsmall := htendsto.eventually
    (Iio_mem_nhds hκ)
  have hthreshold :
      ∀ᶠ ℓ : ℝ in atTop,
        A ≤ c * ℓ * Q * B * Real.exp (B * δ₀) := by
    have hfactor :
        0 < c * Q * B * Real.exp (B * δ₀) := by
      positivity
    filter_upwards
      [eventually_ge_atTop
        (A / (c * Q * B * Real.exp (B * δ₀)))]
      with ℓ hℓ
    apply (div_le_iff₀ hfactor).mp at hℓ
    linarith
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    hthreshold, hsmall] with ℓ hℓ hscale hbound
  intro δ hδ
  have hphi := saddleGaussianOuterPhi_le_endpointBarrier
    hB hQ hc hℓ hδ₀ hδ hscale
  have hcompare :
      Real.sqrt ℓ *
          Real.exp (saddleGaussianOuterPhi B Q c ℓ δ) ≤
        Real.sqrt ℓ *
          Real.exp (A * δ₀ + 4 - s * ℓ) := by
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg ℓ)
    apply Real.exp_le_exp.mpr
    try dsimp [A, s]
    linarith
  exact hcompare.trans_lt hbound

private theorem upperPositiveShellVariance_firstBranch_le
    {ε u : ℝ}
    (hε : 0 < ε) (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2) :
    upperPositiveShellVariance ε (u - 1) ≤
      upperPositiveShellVariance ε (ε / 2) := by
  let B : ℝ := (ε⁻¹ ^ 3)
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  have horder : B ≤ B + 1 := by linarith
  have huabs : |u| ≤ 1 + ε / 2 := by
    apply (abs_le).mpr
    constructor <;> linarith
  have hcont (v : ℝ) : Continuous
      (fun a : ℝ =>
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (v * a)) := by
    have hdensity := positiveShellDensity_continuous ε
    fun_prop
  have hpoint : ∀ a ∈ Icc B (B + 1),
      positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a) ≤
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + ε / 2) * a) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hdensity : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le
    have habs : |u * a| ≤ |(1 + ε / 2) * a| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0,
        abs_of_pos (by positivity : 0 < 1 + ε / 2)]
      exact mul_le_mul_of_nonneg_right huabs ha0
    exact mul_le_mul_of_nonneg_left
      (Real.cosh_le_cosh.mpr habs)
      (mul_nonneg hdensity (sq_nonneg a))
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    ((hcont u).intervalIntegrable _ _)
    ((hcont (1 + ε / 2)).intervalIntegrable _ _)
    hpoint
  simpa only [upperPositiveShellVariance, add_sub_cancel, ge_iff_le] using! hmono

private theorem upperFirstBranch_saddleSourceGaussianVariance_upper_bound
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)))
    (hscale : 1 ≤ ℓ * (1 + u)) :
    saddleSourceGaussianVariance ε ℓ u ≤
      ((3 / 2 : ℝ) +
          (2 + ε / 2) *
            upperPositiveShellVariance ε (ε / 2)) /
        (1 + u) := by
  let η : ℝ := 1 + u
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hηupper : η ≤ 2 + ε / 2 := by
    try dsimp [η]
    linarith
  have hgammabound :=
    (upperGammaVariance_bounds hℓ hη).2
  have hsmallterm : 1 / (ℓ * η ^ 2) ≤ 1 / η := by
    rw [div_le_div_iff₀ (by positivity : 0 < ℓ * η ^ 2) hη]
    try dsimp [η] at hscale ⊢
    nlinarith [hscale]
  have hgamma : upperGammaVariance ℓ η ≤
      (3 / 2 : ℝ) / η := by
    calc
      upperGammaVariance ℓ η ≤
          1 / (2 * η) + 1 / (ℓ * η ^ 2) := hgammabound
      _ ≤ 1 / (2 * η) + 1 / η := by gcongr
      _ = (3 / 2 : ℝ) / η := by ring_nf
  have hshort := upperShortShellVariance_nonneg
    (δ := u - 1) hε horder hmargin
  have hremote := upperPositiveShellVariance_firstBranch_le
    hε hulower huupper
  have hpositive :=
    saddleSourcePositiveShellVariance_nonneg ε (ε / 2)
  have hvariance :
      saddleSourceGaussianVariance ε ℓ u ≤
        (3 / 2 : ℝ) / η +
          upperPositiveShellVariance ε (ε / 2) := by
    unfold saddleSourceGaussianVariance
      upperSaddleVariance upperNetShellVariance
    have hargument : 2 + (u - 1) = η := by
      try dsimp [η]
      ring
    rw [hargument]
    linarith
  calc
    saddleSourceGaussianVariance ε ℓ u ≤
      (3 / 2 : ℝ) / η +
        upperPositiveShellVariance ε (ε / 2) := hvariance
    _ ≤ ((3 / 2 : ℝ) +
          (2 + ε / 2) *
            upperPositiveShellVariance ε (ε / 2)) / η := by
      apply (le_div_iff₀ hη).mpr
      field_simp
      linarith [
        mul_nonneg hpositive
          (show 0 ≤ (2 + ε / 2) - η by linarith)]
    _ = ((3 / 2 : ℝ) +
          (2 + ε / 2) *
            upperPositiveShellVariance ε (ε / 2)) /
          (1 + u) := by rfl

private theorem saddle_exp_neg_mul_min_le_add
    {a x y : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a * min x y) ≤
      Real.exp (-a * x) + Real.exp (-a * y) := by
  have hmax :
      Real.exp (-a * min x y) =
        max (Real.exp (-a * x)) (Real.exp (-a * y)) := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, max_eq_left]
      apply Real.exp_le_exp.mpr
      linarith [mul_nonneg ha (sub_nonneg.mpr hxy)]
    · rw [min_eq_right hyx, max_eq_right]
      apply Real.exp_le_exp.mpr
      linarith [mul_nonneg ha (sub_nonneg.mpr hyx)]
  rw [hmax]
  exact max_le_add_of_nonneg
    (Real.exp_pos (-a * x)).le (Real.exp_pos (-a * y)).le

private theorem saddleSourceNormalizedEnvelope_continuous
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (saddleSourceNormalizedEnvelope ε ℓ u) := by
  have harg : Continuous
      (fun T : ℝ => saddleSourceMellinContour ℓ u T) := by
    unfold saddleSourceMellinContour
    fun_prop
  have hgamma : Continuous
      (fun T : ℝ =>
        Complex.Gamma (saddleSourceMellinContour ℓ u T / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro T
    have hre :
        0 < (saddleSourceMellinContour ℓ u T).re := by
      unfold saddleSourceMellinContour
      simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one, Complex.sub_re,
        Complex.mul_re,
        Complex.ofReal_re, Complex.add_re, Complex.one_re, Complex.ofReal_im, Complex.add_im,
          Complex.one_im, add_zero,
        mul_zero, sub_zero, Complex.I_re, zero_mul, Complex.I_im, Complex.mul_im, sub_self]
      linarith [mul_pos hℓ (show 0 < 1 + u by linarith)]
    exact (saddleMellinGamma_differentiableAt_of_re_pos
      hre).continuousAt.comp_of_eq harg.continuousAt (by rfl)
  have hregular : Continuous
      (fun T : ℝ =>
        saddleRegularMellinFactor ε ℓ
          (saddleSourceMellinContour ℓ u T)) :=
    (saddleRegularMellinFactor_continuous
      hε horder ℓ).comp harg
  have henvelope : Continuous
      (fun T : ℝ =>
        saddleMellinEnvelope ε ℓ
          (saddleSourceMellinContour ℓ u T)) := by
    apply (hgamma.mul hregular).congr
    intro T
    change
      Complex.Gamma (saddleSourceMellinContour ℓ u T / 2) *
          saddleRegularMellinFactor ε ℓ
            (saddleSourceMellinContour ℓ u T) =
        saddleMellinEnvelope ε ℓ
          (saddleSourceMellinContour ℓ u T)
    unfold saddleMellinEnvelope saddleRegularMellinFactor
    ring
  unfold saddleSourceNormalizedEnvelope
  exact henvelope.div_const _

private theorem saddleSourceDampingExponential_continuous
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous
      (fun T : ℝ =>
        Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  have hnorm :=
    (saddleSourceNormalizedEnvelope_continuous
      hε hℓ hu horder).norm
  apply hnorm.congr
  intro T
  exact saddleSourceNormalizedEnvelope_norm
    hε hℓ hu horder T

private theorem saddleSourceTailIntegrand_continuous
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  have hweight : Continuous saddleGaussianTailWeight := by
    unfold saddleGaussianTailWeight
    fun_prop
  exact hweight.mul
    (saddleSourceDampingExponential_continuous
      hε hℓ hu horder)

private theorem saddleSourceContourDamping_firstBranch_min_lower_bound
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)))
    (T : ℝ) :
    (ε * ℓ / (2 * Real.exp 1)) *
        min (T ^ 2 / (1 + u)) |T| ≤
      saddleSourceContourDamping ε ℓ u T := by
  have hη : 0 < 1 + u := by linarith
  have hgamma := upperGammaDamping_lower_bound
    hℓ hη T
  have hfirst := upperFirstBranchSaddleDamping_lower_bound
    hε hεsmall hℓ hulower huupper horder hmargin T
  rw [saddleSourceContourDamping_eq_firstBranch]
  calc
    (ε * ℓ / (2 * Real.exp 1)) *
        min (T ^ 2 / (1 + u)) |T| =
      4 * ε *
        ((ℓ / (8 * Real.exp 1)) *
          min (T ^ 2 / (1 + u)) |T|) := by ring
    _ ≤ 4 * ε * upperGammaDamping ℓ (1 + u) T := by
      exact mul_le_mul_of_nonneg_left hgamma (by positivity)
    _ ≤ upperFirstBranchSaddleDamping ε ℓ u T := hfirst

private theorem saddleSource_firstBranch_weighted_integrable
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a))) :
    Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  let η : ℝ := 1 + u
  let a : ℝ := ε * ℓ / (2 * Real.exp 1)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hgaussian :=
    saddleGaussianTailWeight_mul_gaussian_integrable
      (div_pos ha hη)
  have hlinear :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have hmajor := hgaussian.add hlinear
  apply hmajor.mono'
    (saddleSourceTailIntegrand_continuous
      hε hℓ hulower horder).aestronglyMeasurable
  filter_upwards [] with T
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (saddleGaussianTailWeight_nonneg T)
      (Real.exp_pos _).le)]
  have hcoercive :=
    saddleSourceContourDamping_firstBranch_min_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin T
  have hmin := saddle_exp_neg_mul_min_le_add
    (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
  have hexp :
      Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
        Real.exp (-a * (T ^ 2 / η)) +
          Real.exp (-a * |T|) := by
    calc
      Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
          Real.exp (-a * min (T ^ 2 / η) |T|) := by
            apply Real.exp_le_exp.mpr
            simpa only [saddleSourceContourDamping_eq_firstBranch, neg_mul, neg_le_neg_iff, a,
              η] using! neg_le_neg hcoercive
      _ ≤ _ := hmin
  change
    saddleGaussianTailWeight T *
        Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
      saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
        saddleGaussianTailWeight T *
          Real.exp (-a * |T|)
  have hrearrange :
      -a * (T ^ 2 / η) = -(a / η) * T ^ 2 := by
    ring
  rw [hrearrange] at hexp
  linarith [mul_le_mul_of_nonneg_left hexp
    (saddleGaussianTailWeight_nonneg T)]

private theorem saddleSource_firstBranch_weighted_tail_le
    {ε ℓ u R : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)))
    (hR : 0 ≤ R)
    (hquadratic :
      6 ≤ (ε * ℓ / (2 * Real.exp 1)) / (1 + u))
    (hlinear : 6 ≤ ε * ℓ / (2 * Real.exp 1)) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      2 * Real.exp
          (-(((ε * ℓ / (2 * Real.exp 1)) /
            (1 + u)) / 4) * R ^ 2) *
        Real.sqrt
          (Real.pi /
            (((ε * ℓ / (2 * Real.exp 1)) /
              (1 + u)) / 4)) +
      2 * Real.exp
          (-((ε * ℓ / (2 * Real.exp 1)) / 4) * R) *
        (2 / ((ε * ℓ / (2 * Real.exp 1)) / 4)) := by
  let η : ℝ := 1 + u
  let a : ℝ := ε * ℓ / (2 * Real.exp 1)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hsource := saddleSource_firstBranch_weighted_integrable
    hε hεsmall hℓ hulower huupper horder hmargin
  have hgaussian :=
    saddleGaussianTailWeight_mul_gaussian_integrable
      (div_pos ha hη)
  have hlinearIntegrable :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have hmajor := hgaussian.add hlinearIntegrable
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
        saddleGaussianTailWeight T *
            Real.exp (-(a / η) * T ^ 2) +
          saddleGaussianTailWeight T *
            Real.exp (-a * |T|) := by
    intro T hT
    have hcoercive :=
      saddleSourceContourDamping_firstBranch_min_lower_bound
        hε hεsmall hℓ hulower huupper horder hmargin T
    have hmin := saddle_exp_neg_mul_min_le_add
      (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
    have hexp :
        Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
          Real.exp (-(a / η) * T ^ 2) +
            Real.exp (-a * |T|) := by
      calc
        Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
            Real.exp (-a * min (T ^ 2 / η) |T|) := by
              apply Real.exp_le_exp.mpr
              simpa only [saddleSourceContourDamping_eq_firstBranch, neg_mul, neg_le_neg_iff, a,
                η] using! neg_le_neg hcoercive
        _ ≤ Real.exp (-a * (T ^ 2 / η)) +
            Real.exp (-a * |T|) := hmin
        _ = Real.exp (-(a / η) * T ^ 2) +
            Real.exp (-a * |T|) := by
          have hrearrange :
              -a * (T ^ 2 / η) = -(a / η) * T ^ 2 := by
            ring
          rw [hrearrange]
    linarith [mul_le_mul_of_nonneg_left hexp
      (saddleGaussianTailWeight_nonneg T)]
  have hcompare := setIntegral_mono_on
    hsource.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R) hpoint
  have hsplit :
      (∫ T : ℝ in saddleGaussianTailSet R,
        (saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|))) =
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-(a / η) * T ^ 2)) +
          ∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|) := by
    rw [integral_add hgaussian.integrableOn
      hlinearIntegrable.integrableOn]
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        (saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|)) := hcompare
    _ = (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-(a / η) * T ^ 2)) +
          ∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|) := hsplit
    _ ≤ 2 * Real.exp (-(a / η / 4) * R ^ 2) *
            Real.sqrt (Real.pi / (a / η / 4)) +
          2 * Real.exp (-(a / 4) * R) *
            (2 / (a / 4)) := by
      gcongr
      · apply saddleGaussian_cubic_tail_integral_le
        · exact hquadratic
        · exact hR
      · apply saddleExponential_cubic_tail_integral_le
        · exact hlinear
        · exact hR
    _ = _ := by rfl

private theorem saddleFirstBranch_normalizedGaussian_prefactor_le
    {ℓ V η c C : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hc : 0 < c)
    (hupper : η * V ≤ C) :
    Real.sqrt (ℓ * V) *
        Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) ≤
      2 * Real.sqrt (Real.pi * C / c) := by
  have hinside :
      (ℓ * V) * (Real.pi / ((c * ℓ / η) / 4)) ≤
        4 * (Real.pi * C / c) := by
    calc
      (ℓ * V) * (Real.pi / ((c * ℓ / η) / 4)) =
          4 * Real.pi * (η * V) / c := by
            field_simp [hc.ne', hℓ.ne', hη.ne']
      _ ≤ 4 * Real.pi * C / c := by
        gcongr
      _ = 4 * (Real.pi * C / c) := by ring
  rw [← Real.sqrt_mul (mul_nonneg hℓ.le hV.le)]
  calc
    Real.sqrt
        ((ℓ * V) *
          (Real.pi / ((c * ℓ / η) / 4))) ≤
      Real.sqrt (4 * (Real.pi * C / c)) :=
        Real.sqrt_le_sqrt hinside
    _ = 2 * Real.sqrt (Real.pi * C / c) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

private theorem saddleFirstBranch_normalizedGaussian_exponent_le
    {ℓ V η c C z : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hc : 0 < c) (hC : 0 < C)
    (hupper : η * V ≤ C) :
    (c / (4 * C)) * z ^ 2 ≤
      ((c * ℓ / η) / 4) *
        (z / Real.sqrt (ℓ * V)) ^ 2 := by
  have hLV : 0 < ℓ * V := mul_pos hℓ hV
  have hinverse : 1 / C ≤ 1 / (η * V) := by
    exact (one_div_le_one_div hC (mul_pos hη hV)).mpr hupper
  have hscaled := mul_le_mul_of_nonneg_left hinverse
    (show 0 ≤ c * z ^ 2 / 4 by positivity)
  have hsquare :
      (z / Real.sqrt (ℓ * V)) ^ 2 =
        z ^ 2 / (ℓ * V) := by
    rw [div_pow, Real.sq_sqrt hLV.le]
  rw [hsquare]
  calc
    (c / (4 * C)) * z ^ 2 =
        (c * z ^ 2 / 4) * (1 / C) := by ring
    _ ≤ (c * z ^ 2 / 4) * (1 / (η * V)) := hscaled
    _ = ((c * ℓ / η) / 4) *
          (z ^ 2 / (ℓ * V)) := by
      field_simp [hℓ.ne', hV.ne', hη.ne']

private theorem saddleFirstBranch_normalizedLinear_prefactor_le
    {ℓ V η C : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hC : 0 < C)
    (hupper : η * V ≤ C) :
    Real.sqrt (ℓ * V) / ℓ ≤
      Real.sqrt (C / (ℓ * η)) := by
  have hfrac : V / ℓ ≤ C / (ℓ * η) := by
    apply (div_le_div_iff₀ hℓ (mul_pos hℓ hη)).mpr
    have hscaled :=
      mul_le_mul_of_nonneg_left hupper hℓ.le
    linarith
  have hidentity :
      Real.sqrt (ℓ * V) / ℓ = Real.sqrt (V / ℓ) := by
    calc
      Real.sqrt (ℓ * V) / ℓ =
          Real.sqrt ((ℓ * V) / ℓ ^ 2) := by
            rw [Real.sqrt_div (mul_nonneg hℓ.le hV.le),
              Real.sqrt_sq_eq_abs,
              abs_of_pos hℓ]
      _ = Real.sqrt (V / ℓ) := by
            congr 1
            field_simp [hℓ.ne']
  rw [hidentity]
  exact (Real.sqrt_le_sqrt_iff
    (div_pos hC (mul_pos hℓ hη)).le).mpr hfrac

private theorem saddleSource_firstBranch_normalized_tail_bound
    {ε ℓ u z C : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)))
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hC : 0 < C)
    (hupper :
      (1 + u) * saddleSourceGaussianVariance ε ℓ u ≤ C)
    (hz : 0 ≤ z)
    (hquadratic :
      6 ≤ (ε * ℓ / (2 * Real.exp 1)) / (1 + u))
    (hlinear : 6 ≤ ε * ℓ / (2 * Real.exp 1)) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)),
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      4 * Real.sqrt
          (Real.pi * C / (ε / (2 * Real.exp 1))) *
        Real.exp
          (-(ε / (2 * Real.exp 1) / (4 * C)) * z ^ 2) +
        (16 / (ε / (2 * Real.exp 1))) *
          Real.sqrt (C / (ℓ * (1 + u))) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let η : ℝ := 1 + u
  let c : ℝ := ε / (2 * Real.exp 1)
  let R : ℝ := z / Real.sqrt (ℓ * V)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hR : 0 ≤ R := by
    try dsimp [R]
    positivity
  have htail := saddleSource_firstBranch_weighted_tail_le
    hε hεsmall hℓ hulower huupper horder hmargin
    hR hquadratic hlinear
  have hscale :
      ε * ℓ / (2 * Real.exp 1) = c * ℓ := by
    try dsimp [c]
    ring
  have hpref := saddleFirstBranch_normalizedGaussian_prefactor_le
    hℓ hV hη hc hupper
  have hexponent :=
    saddleFirstBranch_normalizedGaussian_exponent_le
      (z := z) hℓ hV hη hc hC hupper
  have hlinearPref :=
    saddleFirstBranch_normalizedLinear_prefactor_le
      hℓ hV hη hC hupper
  have hsqrt : 0 ≤ Real.sqrt (ℓ * V) :=
    Real.sqrt_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left htail hsqrt
  have hexpgaussian :
      Real.exp
          (-((c * ℓ / η) / 4) * R ^ 2) ≤
        Real.exp (-(c / (4 * C)) * z ^ 2) := by
    apply Real.exp_le_exp.mpr
    try dsimp [R]
    linarith [hexponent]
  have hexplinear :
      Real.exp (-((c * ℓ) / 4) * R) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hcl : 0 ≤ c * ℓ :=
      (mul_pos hc hℓ).le
    linarith only [mul_nonneg hcl hR]
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      4 * Real.sqrt (Real.pi * C / c) *
          Real.exp (-(c / (4 * C)) * z ^ 2) +
        (16 / c) * Real.sqrt (C / (ℓ * η))
  rw [hscale] at hscaled
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      Real.sqrt (ℓ * V) *
        (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
            Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) +
          2 * Real.exp (-((c * ℓ) / 4) * R) *
            (2 / ((c * ℓ) / 4))) at hscaled
  calc
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      Real.sqrt (ℓ * V) *
        (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
            Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) +
          2 * Real.exp (-((c * ℓ) / 4) * R) *
            (2 / ((c * ℓ) / 4))) := hscaled
    _ ≤ 4 * Real.sqrt (Real.pi * C / c) *
          Real.exp (-(c / (4 * C)) * z ^ 2) +
        (16 / c) * Real.sqrt (C / (ℓ * η)) := by
      have hfirst :
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
              Real.sqrt (Real.pi / ((c * ℓ / η) / 4))) ≤
          4 * Real.sqrt (Real.pi * C / c) *
            Real.exp (-(c / (4 * C)) * z ^ 2) := by
        calc
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
              Real.sqrt (Real.pi / ((c * ℓ / η) / 4))) =
            2 *
              (Real.sqrt (ℓ * V) *
                Real.sqrt (Real.pi / ((c * ℓ / η) / 4))) *
              Real.exp (-((c * ℓ / η) / 4) * R ^ 2) := by
                ring
          _ ≤ 2 *
              (2 * Real.sqrt (Real.pi * C / c)) *
              Real.exp (-(c / (4 * C)) * z ^ 2) := by
                gcongr
          _ = _ := by ring
      have hsecond :
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ) / 4) * R) *
              (2 / ((c * ℓ) / 4))) ≤
          (16 / c) * Real.sqrt (C / (ℓ * η)) := by
        calc
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ) / 4) * R) *
              (2 / ((c * ℓ) / 4))) =
              (16 / c) *
                (Real.sqrt (ℓ * V) / ℓ) *
                Real.exp (-((c * ℓ) / 4) * R) := by
              field_simp [hc.ne', hℓ.ne']; ring
          _ ≤ (16 / c) *
                Real.sqrt (C / (ℓ * η)) * 1 := by
                gcongr
          _ = _ := by ring
      linarith [hfirst, hsecond]

private noncomputable def saddleSourceFirstBranchVarianceCoefficient
    (ε : ℝ) : ℝ :=
  (3 / 2 : ℝ) +
    (2 + ε / 2) *
      upperPositiveShellVariance ε (ε / 2)

private theorem saddleSourceFirstBranchVarianceCoefficient_pos
    {ε : ℝ} (hε : 0 < ε) :
    0 < saddleSourceFirstBranchVarianceCoefficient ε := by
  have hshell :=
    saddleSourcePositiveShellVariance_nonneg ε (ε / 2)
  unfold saddleSourceFirstBranchVarianceCoefficient
  linarith [mul_nonneg
    (show 0 ≤ 2 + ε / 2 by positivity) hshell]

private noncomputable def saddleFirstBranchTailLogMajorant
    (c C ℓ : ℝ) : ℝ :=
  4 * Real.sqrt (Real.pi * C / c) *
      Real.exp
        (-(c / (4 * C)) *
          (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) +
    (16 / c) *
      Real.sqrt (C / (Real.log ℓ / 4))

private theorem tendsto_saddleFirstBranchTailLogMajorant
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    Tendsto (saddleFirstBranchTailLogMajorant c C)
      atTop (𝓝 (0 : ℝ)) := by
  have hx : Tendsto
      (fun ℓ : ℝ => Real.log ℓ / 4)
      atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const
      (by norm_num : (0 : ℝ) < 4)
  have hpower : Tendsto
      (fun ℓ : ℝ =>
        (Real.log ℓ / 4) ^ (1 / 6 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 6)).comp hx
  have hrate : 0 < c / (4 * C) := by positivity
  have hnegative : Tendsto
      (fun ℓ : ℝ =>
        -(c / (4 * C)) *
          (Real.log ℓ / 4) ^ (1 / 6 : ℝ))
      atTop atBot :=
    hpower.const_mul_atTop_of_neg (by linarith)
  have hexp : Tendsto
      (fun ℓ : ℝ =>
        Real.exp
          (-(c / (4 * C)) *
            (Real.log ℓ / 4) ^ (1 / 6 : ℝ)))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hratio : Tendsto
      (fun ℓ : ℝ => C / (Real.log ℓ / 4))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hx
  have hsqrt : Tendsto
      (fun ℓ : ℝ =>
        Real.sqrt (C / (Real.log ℓ / 4)))
      atTop (𝓝 (0 : ℝ)) := by
    convert! hratio.sqrt using 1; simp only [Real.sqrt_zero]
  have hfirst := hexp.const_mul
    (4 * Real.sqrt (Real.pi * C / c))
  have hsecond := hsqrt.const_mul (16 / c)
  change Tendsto
    (fun ℓ : ℝ =>
      4 * Real.sqrt (Real.pi * C / c) *
          Real.exp
            (-(c / (4 * C)) *
              (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) +
        (16 / c) *
          Real.sqrt (C / (Real.log ℓ / 4)))
    atTop (𝓝 (0 : ℝ))
  simpa only [one_div, neg_mul, mul_zero, add_zero] using! hfirst.add hsecond

private theorem eventually_saddleSource_firstBranch_uniform_tail :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ,
            -1 < u →
            u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) /
                      Real.sqrt
                        (ℓ * saddleSourceGaussianVariance ε ℓ u)),
                  saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceContourDamping ε ℓ u T)) < κ := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards
      [hnear.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos]
    with ε hε hεsmall horder hmargin hVbranch
  change 0 < ε at hε
  intro κ hκ
  let c : ℝ := ε / (2 * Real.exp 1)
  let C : ℝ := saddleSourceFirstBranchVarianceCoefficient ε
  let U : ℝ := 2 + ε / 2
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hC : 0 < C :=
    saddleSourceFirstBranchVarianceCoefficient_pos hε
  have hU : 0 < U := by
    try dsimp [U]
    positivity
  have hlogtop : Tendsto
      (fun ℓ : ℝ => Real.log ℓ / 4)
      atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const
      (by norm_num : (0 : ℝ) < 4)
  have hlogone := hlogtop.eventually
    (eventually_ge_atTop (1 : ℝ))
  have htail :=
    (tendsto_saddleFirstBranchTailLogMajorant
      hc hC).eventually (Iio_mem_nhds hκ)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlogone,
    eventually_ge_atTop (6 / c),
    eventually_ge_atTop (6 * U / c),
    htail]
    with ℓ hℓ hlogoneℓ hlinbase hquadbase htailℓ
  intro u hulower huupper hlogscale
  let η : ℝ := 1 + u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let z : ℝ := (ℓ * η) ^ (1 / 12 : ℝ)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hηU : η ≤ U := by
    try dsimp [η, U]
    linarith
  have hscale : 1 ≤ ℓ * η :=
    hlogoneℓ.trans hlogscale
  have hV : 0 < V := by
    try dsimp [V]
    exact hVbranch ℓ hℓ u hulower huupper
  have hmargin' :
      ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
        0 ≤ (1 - 10 * ε * (1 + a)) := by
    intro a ha
    have h := hmargin a ha
    linarith
  have hvariance :=
    upperFirstBranch_saddleSourceGaussianVariance_upper_bound
      hε hℓ hulower huupper horder hmargin' hscale
  have hupper : η * V ≤ C := by
    have hbound : V ≤ C / η := by
      simpa only [saddleSourceFirstBranchVarianceCoefficient] using! hvariance
    calc
      η * V ≤ η * (C / η) :=
        mul_le_mul_of_nonneg_left hbound hη.le
      _ = C := by field_simp [hη.ne']
  have hlinear : 6 ≤ c * ℓ := by
    have h := (div_le_iff₀ hc).mp hlinbase
    linarith
  have hquadratic : 6 ≤ (c * ℓ) / η := by
    apply (le_div_iff₀ hη).mpr
    have h := (div_le_iff₀ hc).mp hquadbase
    linarith [mul_le_mul_of_nonneg_left hηU
      (by norm_num : (0 : ℝ) ≤ 6)]
  have hz : 0 ≤ z := by
    try dsimp [z]
    positivity
  have hsource := saddleSource_firstBranch_normalized_tail_bound
    (z := z) (C := C)
    hε hεsmall hℓ hulower huupper horder hmargin'
    hV hC hupper hz (by
      convert! hquadratic using 1; dsimp [c, η]; ring) (by
      convert! hlinear using 1; dsimp [c]; ring)
  have hlognonneg : 0 ≤ Real.log ℓ / 4 := by
    linarith
  have hpower :
      (Real.log ℓ / 4) ^ (1 / 6 : ℝ) ≤ z ^ 2 := by
    have hmono := Real.rpow_le_rpow
      hlognonneg hlogscale
      (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have hsquare :
        z ^ 2 = (ℓ * η) ^ (1 / 6 : ℝ) := by
      try dsimp [z]
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (mul_nonneg hℓ.le hη.le)]
      congr 1
      norm_num
    rw [hsquare]
    exact hmono
  have hrate : 0 < c / (4 * C) := by positivity
  have hexponential :
      Real.exp (-(c / (4 * C)) * z ^ 2) ≤
        Real.exp
          (-(c / (4 * C)) *
            (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith [mul_nonneg hrate.le
      (show 0 ≤ z ^ 2 -
        (Real.log ℓ / 4) ^ (1 / 6 : ℝ) by linarith)]
  have hsqrt :
      Real.sqrt (C / (ℓ * η)) ≤
        Real.sqrt (C / (Real.log ℓ / 4)) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left hC.le
      (by linarith : 0 < Real.log ℓ / 4)
      hlogscale
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) < κ
  calc
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      4 * Real.sqrt (Real.pi * C / c) *
        Real.exp (-(c / (4 * C)) * z ^ 2) +
          (16 / c) * Real.sqrt (C / (ℓ * η)) := by
        simpa only [saddleSourceContourDamping_eq_firstBranch, neg_mul, V, c, η] using! hsource
    _ ≤ saddleFirstBranchTailLogMajorant c C ℓ := by
      unfold saddleFirstBranchTailLogMajorant
      gcongr
    _ < κ := htailℓ

private theorem eventually_saddleGaussianOuterPhi_uniform_polynomial
    {B Q c δ₀ K : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hc : 0 < c)
    (hδ₀ : 0 ≤ δ₀) (hK : 0 ≤ K) :
    ∀ κ : ℝ, 0 < κ →
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, δ₀ ≤ δ →
          K * Real.sqrt ℓ *
              Real.exp (((B + 1) / 2) * δ) *
              (2 + δ) ^ 4 *
              Real.exp
                (-c * ℓ * Q * Real.exp (B * δ)) < κ := by
  intro κ hκ
  rcases hK.eq_or_lt with hKzero | hKpos
  · subst K
    filter_upwards [] with ℓ
    intro δ hδ
    simpa only [zero_mul, neg_mul] using! hκ
  · have hlimit :=
      eventually_saddleGaussianOuterPhi_uniform
        hB hQ hc hδ₀ (κ / K)
        (div_pos hκ hKpos)
    filter_upwards [hlimit] with ℓ hℓ
    intro δ hδ
    have hδnonnegative : 0 ≤ δ := hδ₀.trans hδ
    have hη : 0 < 2 + δ := by linarith
    have hpower :
        (2 + δ) ^ 4 =
          Real.exp (4 * Real.log (2 + δ)) := by
      calc
        (2 + δ) ^ 4 =
            (Real.exp (Real.log (2 + δ))) ^ 4 := by
              rw [Real.exp_log hη]
        _ = Real.exp (4 * Real.log (2 + δ)) := by
              rw [← Real.exp_nat_mul]
              norm_num
    have hproduct :
        Real.exp (((B + 1) / 2) * δ) *
            Real.exp (4 * Real.log (2 + δ)) *
            Real.exp
              (-c * ℓ * Q * Real.exp (B * δ)) =
          Real.exp (saddleGaussianOuterPhi B Q c ℓ δ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold saddleGaussianOuterPhi
      ring
    have hrewrite :
        K * Real.sqrt ℓ *
            Real.exp (((B + 1) / 2) * δ) *
            (2 + δ) ^ 4 *
            Real.exp
              (-c * ℓ * Q * Real.exp (B * δ)) =
          K *
            (Real.sqrt ℓ *
              Real.exp (saddleGaussianOuterPhi B Q c ℓ δ)) := by
      rw [hpower]
      calc
        K * Real.sqrt ℓ *
            Real.exp (((B + 1) / 2) * δ) *
            Real.exp (4 * Real.log (2 + δ)) *
            Real.exp
              (-c * ℓ * Q * Real.exp (B * δ)) =
          K * Real.sqrt ℓ *
            (Real.exp (((B + 1) / 2) * δ) *
              Real.exp (4 * Real.log (2 + δ)) *
              Real.exp
                (-c * ℓ * Q * Real.exp (B * δ))) := by
                ring
        _ = K *
            (Real.sqrt ℓ *
              Real.exp (saddleGaussianOuterPhi B Q c ℓ δ)) := by
            rw [hproduct]
            ring
    rw [hrewrite]
    calc
      K *
          (Real.sqrt ℓ *
            Real.exp (saddleGaussianOuterPhi B Q c ℓ δ)) <
        K * (κ / K) :=
          mul_lt_mul_of_pos_left (hℓ δ hδ) hKpos
      _ = κ := by field_simp

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private theorem saddleSourcePositiveShellThirdMoment_nonneg
    {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    0 ≤ upperPositiveShellThirdMoment ε δ := by
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  unfold upperPositiveShellThirdMoment
  apply intervalIntegral.integral_nonneg (by linarith)
  intro a ha
  have ha : 0 ≤ a := hB.trans ha.1
  have hdensity : 0 ≤ positiveShellDensity ε a := by
    unfold positiveShellDensity
    exact div_nonneg (shellWeight_pos ε).le
      (Real.cosh_pos a).le
  exact mul_nonneg
    (mul_nonneg hdensity (pow_nonneg ha 3))
    (Real.cosh_pos _).le

private theorem upperPositiveShellThirdMoment_firstBranch_le
    {ε u : ℝ}
    (hε : 0 < ε) (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2) :
    upperPositiveShellThirdMoment ε (u - 1) ≤
      upperPositiveShellThirdMoment ε (ε / 2) := by
  let B : ℝ := (ε⁻¹ ^ 3)
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  have horder : B ≤ B + 1 := by linarith
  have huabs : |u| ≤ 1 + ε / 2 := by
    apply (abs_le).mpr
    constructor <;> linarith
  have hcont (v : ℝ) : Continuous
      (fun a : ℝ =>
        positiveShellDensity ε a * a ^ 3 *
          Real.cosh (v * a)) := by
    have hdensity := positiveShellDensity_continuous ε
    fun_prop
  have hpoint : ∀ a ∈ Icc B (B + 1),
      positiveShellDensity ε a * a ^ 3 *
          Real.cosh (u * a) ≤
        positiveShellDensity ε a * a ^ 3 *
          Real.cosh ((1 + ε / 2) * a) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hdensity : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le
    have habs : |u * a| ≤ |(1 + ε / 2) * a| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0,
        abs_of_pos (by positivity : 0 < 1 + ε / 2)]
      exact mul_le_mul_of_nonneg_right huabs ha0
    exact mul_le_mul_of_nonneg_left
      (Real.cosh_le_cosh.mpr habs)
      (mul_nonneg hdensity (pow_nonneg ha0 3))
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    ((hcont u).intervalIntegrable _ _)
    ((hcont (1 + ε / 2)).intervalIntegrable _ _)
    hpoint
  simpa only [upperPositiveShellThirdMoment, add_sub_cancel, ge_iff_le] using! hmono

private theorem upperGammaVariance_firstBranch_scaled_le
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hscale : 1 ≤ ℓ * η) :
    η * upperGammaVariance ℓ η ≤ (3 / 2 : ℝ) := by
  have hone : 1 / (ℓ * η) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hℓ hη)).2
    simpa only [one_mul] using! hscale
  calc
    η * upperGammaVariance ℓ η ≤
        η * (1 / (2 * η) + 1 / (ℓ * η ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (upperGammaVariance_bounds hℓ hη).2 hη.le
    _ = 1 / 2 + 1 / (ℓ * η) := by
      field_simp [hℓ.ne', hη.ne']
    _ ≤ (3 / 2 : ℝ) := by linarith

private theorem upperGammaThirdMoment_firstBranch_scaled_le
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hscale : 1 ≤ ℓ * η) :
    η ^ 2 * upperGammaThirdMoment ℓ η ≤ (5 / 2 : ℝ) := by
  have hone : 1 / (ℓ * η) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hℓ hη)).2
    simpa only [one_mul] using! hscale
  have htwo : 2 / (ℓ * η) ≤ (2 : ℝ) := by
    calc
      2 / (ℓ * η) = 2 * (1 / (ℓ * η)) := by ring
      _ ≤ 2 * (1 : ℝ) := by gcongr
      _ = 2 := by ring
  calc
    η ^ 2 * upperGammaThirdMoment ℓ η ≤
        η ^ 2 *
          (1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3)) :=
      mul_le_mul_of_nonneg_left
        (upperGammaThirdMoment_bounds hℓ hη).2
        (sq_nonneg η)
    _ = 1 / 2 + 2 / (ℓ * η) := by
      field_simp [hℓ.ne', hη.ne']
    _ ≤ (5 / 2 : ℝ) := by linarith

private noncomputable def saddleSourceFirstBranchThirdMomentCoefficient
    (ε : ℝ) : ℝ :=
  (5 / 2 : ℝ) +
    (3 / 2 : ℝ) * (10 * Real.log (1 / ε)) * (2 + ε / 2) +
    (2 + ε / 2) ^ 2 *
      upperPositiveShellThirdMoment ε (ε / 2)

private theorem upperFirstBranch_saddleSourceThirdMoment_scaled_le
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)))
    (hscale : 1 ≤ ℓ * (1 + u)) :
    (1 + u) ^ 2 * upperSaddleThirdMoment ε ℓ (u - 1) ≤
      saddleSourceFirstBranchThirdMomentCoefficient ε := by
  let η : ℝ := 1 + u
  let U : ℝ := 2 + ε / 2
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hU : 0 < U := by
    try dsimp [U]
    positivity
  have hηU : η ≤ U := by
    try dsimp [η, U]
    linarith
  have hA : 0 ≤ (10 * Real.log (1 / ε)) := by
    have hcut : 0 < (ε ^ 3) := by
      positivity
    exact (hcut.trans_le horder).le
  have hgamma := upperGammaVariance_firstBranch_scaled_le
    hℓ hη (by simpa only [η] using! hscale)
  have hthirdgamma := upperGammaThirdMoment_firstBranch_scaled_le
    hℓ hη (by simpa only [η] using! hscale)
  have hgammanonneg : 0 ≤ upperGammaVariance ℓ η :=
    (show 0 ≤ 1 / (2 * η) by positivity).trans
      (upperGammaVariance_bounds hℓ hη).1
  have hshortvariance :=
    upperFirstBranch_shortVariance_le_gamma
      hε hεsmall hℓ hulower huupper horder hmargin
  have hshortvariance' :
      upperShortShellVariance ε (u - 1) ≤
        upperGammaVariance ℓ η := by
    try dsimp [η]
    linarith [mul_nonneg hε.le hgammanonneg]
  have hshortthird := upperShortShellThirdMoment_le
    (δ := u - 1) hε horder hmargin
  have hshort :
      η ^ 2 * upperShortShellThirdMoment ε (u - 1) ≤
        (3 / 2 : ℝ) * (10 * Real.log (1 / ε)) * U := by
    calc
      η ^ 2 * upperShortShellThirdMoment ε (u - 1) ≤
          η ^ 2 *
            ((10 * Real.log (1 / ε)) *
              upperShortShellVariance ε (u - 1)) :=
        mul_le_mul_of_nonneg_left hshortthird (sq_nonneg η)
      _ ≤ η ^ 2 *
          ((10 * Real.log (1 / ε)) * upperGammaVariance ℓ η) := by
        gcongr
      _ = (10 * Real.log (1 / ε)) * η *
          (η * upperGammaVariance ℓ η) := by ring
      _ ≤ (10 * Real.log (1 / ε)) * η * (3 / 2 : ℝ) := by
        gcongr
      _ ≤ (10 * Real.log (1 / ε)) * U * (3 / 2 : ℝ) := by
        gcongr
      _ = (3 / 2 : ℝ) * (10 * Real.log (1 / ε)) * U := by
        ring
  have hremote :=
    upperPositiveShellThirdMoment_firstBranch_le
      hε hulower huupper
  have hremote0 :=
    saddleSourcePositiveShellThirdMoment_nonneg
      hε (ε / 2)
  have hremoteScaled :
      η ^ 2 * upperPositiveShellThirdMoment ε (u - 1) ≤
        U ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) := by
    calc
      η ^ 2 * upperPositiveShellThirdMoment ε (u - 1) ≤
          η ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) :=
        mul_le_mul_of_nonneg_left hremote (sq_nonneg η)
      _ ≤ U ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) := by
        gcongr
  unfold saddleSourceFirstBranchThirdMomentCoefficient
  unfold upperSaddleThirdMoment upperNetShellThirdMoment
  have hargument : 2 + (u - 1) = η := by
    try dsimp [η]
    ring
  rw [hargument]
  change η ^ 2 *
      (upperGammaThirdMoment ℓ η +
        (upperPositiveShellThirdMoment ε (u - 1) +
          upperShortShellThirdMoment ε (u - 1))) ≤
    (5 / 2 : ℝ) +
      (3 / 2 : ℝ) * (10 * Real.log (1 / ε)) * U +
      U ^ 2 * upperPositiveShellThirdMoment ε (ε / 2)
  linarith

private noncomputable def saddleSourceSecondBranchVarianceFloor (ε : ℝ) : ℝ :=
  (99 / 200 : ℝ) * (ε⁻¹ ^ 3) ^ 2 *
    shellWeight ε *
      Real.exp ((ε / 2) * (ε⁻¹ ^ 3))

private theorem saddleSourceSecondBranchVarianceFloor_pos
    {ε : ℝ} (hε : 0 < ε) :
    0 < saddleSourceSecondBranchVarianceFloor ε := by
  unfold saddleSourceSecondBranchVarianceFloor
  have hweight := shellWeight_pos ε
  positivity

private theorem eventually_saddleSourceGaussianVariance_secondBranch_floor :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          saddleSourceSecondBranchVarianceFloor ε ≤
            saddleSourceGaussianVariance ε ℓ (1 + δ) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleVariance_bounds]
    with ε hε hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  have hfactor :
      0 ≤ (1 / 2 : ℝ) * (ε⁻¹ ^ 3) ^ 2 *
        shellWeight ε := by
    have hweight := shellWeight_pos ε
    positivity
  have hpositive :=
    (upperPositiveShellVariance_bounds hε hδ0).1
  have hfull := (hvariance ℓ hℓ δ hδ).1
  have hmono :
      Real.exp ((ε / 2) * (ε⁻¹ ^ 3)) ≤
        Real.exp (δ * (ε⁻¹ ^ 3)) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hδ hB)
  have hfloor :
      saddleSourceSecondBranchVarianceFloor ε ≤
        (99 / 100 : ℝ) *
          upperPositiveShellVariance ε δ := by
    calc
      saddleSourceSecondBranchVarianceFloor ε =
          (99 / 100 : ℝ) *
            ((1 / 2 : ℝ) *
              (ε⁻¹ ^ 3) ^ 2 *
                shellWeight ε *
                  Real.exp ((ε / 2) * (ε⁻¹ ^ 3))) := by
        unfold saddleSourceSecondBranchVarianceFloor
        ring
      _ ≤ (99 / 100 : ℝ) *
            ((1 / 2 : ℝ) *
              (ε⁻¹ ^ 3) ^ 2 *
                shellWeight ε *
                  Real.exp (δ * (ε⁻¹ ^ 3))) := by
        gcongr
      _ ≤ (99 / 100 : ℝ) *
            upperPositiveShellVariance ε δ := by
        gcongr
  have hη : 0 < 2 + δ := by linarith
  have hgamma : 0 ≤ 1 / (2 * (2 + δ)) := by
    positivity
  unfold saddleSourceGaussianVariance
  have hargument : 1 + δ - 1 = δ := by ring
  rw [hargument]
  linarith

private theorem saddleSource_cubic_window_le
    {ℓ V M C z T : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V)
    (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hM : M ≤ C * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := by
  have _hz : 0 ≤ z := hz
  have hs : 0 < Real.sqrt (ℓ * V) :=
    Real.sqrt_pos.2 (mul_pos hℓ hV)
  calc
    (ℓ * M / 6) * |T| ^ 3 ≤
        (ℓ * (C * V) / 6) * |T| ^ 3 := by
      gcongr
    _ ≤ (ℓ * (C * V) / 6) *
        (z / Real.sqrt (ℓ * V)) ^ 3 := by
      gcongr
    _ = (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := by
      field_simp [hs.ne']
      rw [Real.sq_sqrt (mul_nonneg hℓ.le hV.le)]
      ring

private theorem saddleSource_cubic_window_le_of_variance_floor
    {ℓ V M C V₀ z T : ℝ}
    (hℓ : 0 < ℓ) (hV₀ : 0 < V₀)
    (hfloor : V₀ ≤ V)
    (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hM : M ≤ C * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (C / 6) * z ^ 3 /
        (Real.sqrt ℓ * Real.sqrt V₀) := by
  have hV : 0 < V := hV₀.trans_le hfloor
  have hbase := saddleSource_cubic_window_le
    hℓ hV hC hz hM hT
  calc
    (ℓ * M / 6) * |T| ^ 3 ≤
        (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := hbase
    _ ≤ (C / 6) * z ^ 3 / Real.sqrt (ℓ * V₀) := by
      gcongr
    _ = (C / 6) * z ^ 3 /
        (Real.sqrt ℓ * Real.sqrt V₀) := by
      rw [Real.sqrt_mul hℓ.le]

end

section

open Filter Set
open scoped Topology

private theorem exists_plusPolynomial_uniform_weighted_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
        ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ ≤
          C * (1 + |T| ^ 3) *
            ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_plusPolynomial_uniform_norm_ratio hε
  refine ⟨C, hC, ?_⟩
  intro u hu T
  have hden : 0 <
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
    (div_pos hε four_pos).trans_le
      (plusPolynomial_imaginary_norm_ge_beta hε hu)
  exact (div_le_iff₀ hden).mp (hbound u hu T)

private theorem exists_minusPolynomial_uniform_weighted_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ ≤
          C * (1 + |T| ^ 3) *
            ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_minusPolynomial_uniform_norm_ratio hε
  refine ⟨C, hC, ?_⟩
  intro u hu T
  have hden : 0 <
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
    have hbeta := div_pos hε four_pos
    have hnorm :=
      minusPolynomial_imaginary_norm_ge_three_beta hε hu
    linarith
  exact (div_le_iff₀ hden).mp (hbound u hu T)

private theorem exists_plusPolynomial_uniform_difference_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
        ‖plusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          C * (|T| + |T| ^ 3) *
            ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_plusPolynomial_uniform_difference_ratio hε
  refine ⟨C, hC, ?_⟩
  intro u hu T
  have hden : 0 <
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
    (div_pos hε four_pos).trans_le
      (plusPolynomial_imaginary_norm_ge_beta hε hu)
  exact (div_le_iff₀ hden).mp (hbound u hu T)

private theorem exists_minusPolynomial_uniform_difference_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          C * (|T| + |T| ^ 3) *
            ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_minusPolynomial_uniform_difference_ratio hε
  refine ⟨C, hC, ?_⟩
  intro u hu T
  have hden : 0 <
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
    have hbeta := div_pos hε four_pos
    have hnorm :=
      minusPolynomial_imaginary_norm_ge_three_beta hε hu
    linarith
  exact (div_le_iff₀ hden).mp (hbound u hu T)

private theorem exists_plusPolynomial_uniform_central_window
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : ℝ, -1 ≤ u →
        ∀ T : ℝ, |T| ≤ R →
          ‖plusPolynomial ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_plusPolynomial_uniform_difference_bound hε
  let R : ℝ := min 1 (κ / (2 * C))
  have hR : 0 < R := by
    try dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro u hu T hT
  have hTunit : |T| ≤ 1 :=
    hT.trans (min_le_left _ _)
  have hcube : |T| ^ 3 ≤ |T| := by
    have hfactor :
        0 ≤ |T| * (1 - |T|) * (1 + |T|) := by
      exact mul_nonneg
        (mul_nonneg (abs_nonneg T) (sub_nonneg.mpr hTunit))
        (by positivity)
    linarith
  have hscale : 2 * C * R ≤ κ := by
    have hmin : R ≤ κ / (2 * C) := min_le_right _ _
    have hfactor : 0 < 2 * C := by positivity
    linarith [(le_div_iff₀ hfactor).mp hmin]
  calc
    ‖plusPolynomial ε
        ((T : ℂ) + Complex.I * (u : ℂ)) -
      plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      C * (|T| + |T| ^ 3) *
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      hbound u hu T
    _ ≤ (2 * C * R) *
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        C * (|T| + |T| ^ 3) ≤ C * (2 * R) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          linarith
        _ = 2 * C * R := by ring
    _ ≤ κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      exact mul_le_mul_of_nonneg_right hscale (norm_nonneg _)

private theorem exists_minusPolynomial_uniform_central_window
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u →
        ∀ T : ℝ, |T| ≤ R →
          ‖minusPolynomial ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_minusPolynomial_uniform_difference_bound hε
  let R : ℝ := min 1 (κ / (2 * C))
  have hR : 0 < R := by
    try dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro u hu T hT
  have hTunit : |T| ≤ 1 :=
    hT.trans (min_le_left _ _)
  have hcube : |T| ^ 3 ≤ |T| := by
    have hfactor :
        0 ≤ |T| * (1 - |T|) * (1 + |T|) := by
      exact mul_nonneg
        (mul_nonneg (abs_nonneg T) (sub_nonneg.mpr hTunit))
        (by positivity)
    linarith
  have hscale : 2 * C * R ≤ κ := by
    have hmin : R ≤ κ / (2 * C) := min_le_right _ _
    have hfactor : 0 < 2 * C := by positivity
    linarith [(le_div_iff₀ hfactor).mp hmin]
  calc
    ‖minusPolynomial ε
        ((T : ℂ) + Complex.I * (u : ℂ)) -
      minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      C * (|T| + |T| ^ 3) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      hbound u hu T
    _ ≤ (2 * C * R) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        C * (|T| + |T| ^ 3) ≤ C * (2 * R) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          linarith
        _ = 2 * C * R := by ring
    _ ≤ κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      exact mul_le_mul_of_nonneg_right hscale (norm_nonneg _)

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private noncomputable def saddleSourceFirstBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  (ℓ * (1 + u)) ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)

private noncomputable def saddleSourceSecondBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  ℓ ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)

private theorem saddleSource_central_rpow_cube_div_sqrt
    {x : ℝ} (hx : 0 < x) :
    (x ^ (1 / 12 : ℝ)) ^ 3 / Real.sqrt x =
      x ^ (-(1 / 4 : ℝ)) := by
  have hcube :
      (x ^ (1 / 12 : ℝ)) ^ 3 =
        x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  rw [hcube, Real.sqrt_eq_rpow,
    ← Real.rpow_sub hx]
  norm_num

private theorem saddleSource_central_rpow_div_sqrt
    {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 12 : ℝ) / Real.sqrt x =
      x ^ (-(5 / 12 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
  norm_num

private theorem saddleSource_scaled_cubic_window_le
    {ℓ η V M K c z T : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c)
    (hK : 0 ≤ K) (hz : 0 ≤ z)
    (hmoment : η ^ 2 * M ≤ K)
    (hvariance : c ≤ η * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (K / (6 * c * Real.sqrt c)) *
        (z ^ 3 / Real.sqrt (ℓ * η)) := by
  have hV : 0 < V := by
    nlinarith [hvariance, mul_pos hη hc]
  have hs : 0 < Real.sqrt (ℓ * V) :=
    Real.sqrt_pos.2 (mul_pos hℓ hV)
  have ht : 0 < Real.sqrt (ℓ * η) :=
    Real.sqrt_pos.2 (mul_pos hℓ hη)
  have hw : 0 < Real.sqrt (η * V) :=
    Real.sqrt_pos.2 (mul_pos hη hV)
  have hcroot : 0 < Real.sqrt c :=
    Real.sqrt_pos.2 hc
  have hm : M ≤ K / η ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hη)).2
    linarith
  have hcross :
      Real.sqrt (ℓ * V) * η =
        Real.sqrt (ℓ * η) * Real.sqrt (η * V) := by
    have heq :
        (Real.sqrt (ℓ * V) * η) ^ 2 =
          (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) ^ 2 := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hℓ.le hV.le),
        Real.sq_sqrt (mul_nonneg hℓ.le hη.le),
        Real.sq_sqrt (mul_nonneg hη.le hV.le)]
      ring
    nlinarith [mul_pos hs hη,
      mul_pos ht hw]
  have hwlower : Real.sqrt c ≤ Real.sqrt (η * V) :=
    Real.sqrt_le_sqrt hvariance
  have hratio :
      ℓ * Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3 =
        η ^ 2 * (Real.sqrt (ℓ * V)) ^ 3 := by
    have htsquare :
        (Real.sqrt (ℓ * η)) ^ 2 = ℓ * η :=
      Real.sq_sqrt (mul_nonneg hℓ.le hη.le)
    calc
      ℓ * Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3 =
        (((Real.sqrt (ℓ * η)) ^ 2 / η) *
          Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3) := by
        rw [htsquare]
        field_simp [hη.ne']
      _ =
        (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) ^ 3 /
          η := by ring
      _ =
        (Real.sqrt (ℓ * V) * η) ^ 3 / η := by
        rw [hcross]
      _ = η ^ 2 * (Real.sqrt (ℓ * V)) ^ 3 := by
        field_simp [hη.ne']
  calc
    (ℓ * M / 6) * |T| ^ 3 ≤
        (ℓ * (K / η ^ 2) / 6) *
          (z / Real.sqrt (ℓ * V)) ^ 3 := by
      gcongr
    _ = (K / 6) * z ^ 3 /
        (Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3) := by
      field_simp [hη.ne', hs.ne', ht.ne', hw.ne']
      calc
        ℓ * K * z ^ 3 * Real.sqrt (ℓ * η) *
            (Real.sqrt (η * V)) ^ 3 =
          K * z ^ 3 *
            (ℓ * Real.sqrt (ℓ * η) *
              (Real.sqrt (η * V)) ^ 3) := by ring
        _ = K * z ^ 3 *
          (η ^ 2 * (Real.sqrt (ℓ * V)) ^ 3) := by
          rw [hratio]
        _ = K * η ^ 2 * z ^ 3 *
          (Real.sqrt (ℓ * V)) ^ 3 := by ring
    _ ≤ (K / 6) * z ^ 3 /
        (Real.sqrt (ℓ * η) *
          (Real.sqrt c) ^ 3) := by
      gcongr
    _ = (K / (6 * c * Real.sqrt c)) *
        (z ^ 3 / Real.sqrt (ℓ * η)) := by
      have hcsquare : (Real.sqrt c) ^ 2 = c :=
        Real.sq_sqrt hc.le
      field_simp [ht.ne', hc.ne', hcroot.ne']
      rw [hcsquare]

private theorem upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a))) :
    2 * ε ≤ (1 + u) *
      saddleSourceGaussianVariance ε ℓ u := by
  have hη : 0 < 1 + u := by linarith
  have hgamma := (upperGammaVariance_bounds hℓ hη).1
  have hsource :=
    upperFirstBranch_saddleSourceGaussianVariance_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin
  calc
    2 * ε =
        (1 + u) * (4 * ε * (1 / (2 * (1 + u)))) := by
      field_simp [hη.ne']
      norm_num
    _ ≤ (1 + u) *
        (4 * ε * upperGammaVariance ℓ (1 + u)) := by
      gcongr
    _ ≤ (1 + u) *
        saddleSourceGaussianVariance ε ℓ u := by
      gcongr

private theorem saddleSourceFirstBranchThirdMomentCoefficient_pos
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    0 < saddleSourceFirstBranchThirdMomentCoefficient ε := by
  have hcut : 0 < (ε ^ 3) := by
    positivity
  have hA : 0 ≤ (10 * Real.log (1 / ε)) :=
    (hcut.trans_le horder).le
  have hremote :=
    saddleSourcePositiveShellThirdMoment_nonneg hε (ε / 2)
  unfold saddleSourceFirstBranchThirdMomentCoefficient
  positivity

private theorem saddleSourceFirstBranch_cubic_central_window_le
    {ε ℓ u T : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)))
    (hscale : 1 ≤ ℓ * (1 + u))
    (hT : |T| ≤ saddleSourceFirstBranchCentralRadius ε ℓ u) :
    (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤
      (saddleSourceFirstBranchThirdMomentCoefficient ε /
        (12 * ε * Real.sqrt (2 * ε))) *
          (ℓ * (1 + u)) ^ (-(1 / 4 : ℝ)) := by
  have hη : 0 < 1 + u := by linarith
  have hx : 0 < ℓ * (1 + u) := mul_pos hℓ hη
  have hK :=
    saddleSourceFirstBranchThirdMomentCoefficient_pos hε horder
  have hmoment := upperFirstBranch_saddleSourceThirdMoment_scaled_le
    hε hεsmall hℓ hulower huupper horder hmargin hscale
  have hvariance :=
    upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin
  have hcentral := saddleSource_scaled_cubic_window_le
    (ℓ := ℓ) (η := 1 + u)
    (V := saddleSourceGaussianVariance ε ℓ u)
    (M := upperSaddleThirdMoment ε ℓ (u - 1))
    (K := saddleSourceFirstBranchThirdMomentCoefficient ε)
    (c := 2 * ε)
    (z := (ℓ * (1 + u)) ^ (1 / 12 : ℝ))
    (T := T) hℓ hη (by positivity) hK.le
    (Real.rpow_nonneg hx.le _)
    hmoment hvariance (by
      simpa only [one_div, saddleSourceFirstBranchCentralRadius] using! hT)
  calc
    (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤
      (saddleSourceFirstBranchThirdMomentCoefficient ε /
          (6 * (2 * ε) * Real.sqrt (2 * ε))) *
        (((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) ^ 3 /
          Real.sqrt (ℓ * (1 + u))) := hcentral
    _ = (saddleSourceFirstBranchThirdMomentCoefficient ε /
        (12 * ε * Real.sqrt (2 * ε))) *
          (ℓ * (1 + u)) ^ (-(1 / 4 : ℝ)) := by
      rw [saddleSource_central_rpow_cube_div_sqrt hx]
      ring

private theorem eventually_saddleSourceSecondBranch_cubic_central_window_le :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            |T| ≤
              saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) →
            (ℓ * upperSaddleThirdMoment ε ℓ δ / 6) *
                |T| ^ 3 ≤
              ((2 + (100 / 99 : ℝ) *
                  upperSaddleShellThirdCoefficient ε) /
                (6 * Real.sqrt
                  (saddleSourceSecondBranchVarianceFloor ε))) *
                ℓ ^ (-(1 / 4 : ℝ)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_floor,
    eventually_upperSaddleThirdMoment_le_variance]
    with ε hε horder hfloor hmoment
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T hT
  have hℓpositive : 0 < ℓ := by linarith
  have hfloorpositive :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  have hvariance := hfloor ℓ hℓpositive δ hδ
  have hcut : 0 < (ε ^ 3) := by
    positivity
  have hA : 0 ≤ (10 * Real.log (1 / ε)) :=
    (hcut.trans_le horder).le
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  have hC :
      0 ≤ 2 + (100 / 99 : ℝ) *
        upperSaddleShellThirdCoefficient ε := by
    unfold upperSaddleShellThirdCoefficient
    positivity
  have hthird := hmoment ℓ hℓ δ hδ
  have hargument : 1 + δ - 1 = δ := by ring
  have hthird' :
      upperSaddleThirdMoment ε ℓ δ ≤
        (2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) *
          saddleSourceGaussianVariance ε ℓ (1 + δ) := by
    simpa only [saddleSourceGaussianVariance, hargument] using! hthird
  have hbase := saddleSource_cubic_window_le_of_variance_floor
    (ℓ := ℓ)
    (V := saddleSourceGaussianVariance ε ℓ (1 + δ))
    (M := upperSaddleThirdMoment ε ℓ δ)
    (C := 2 + (100 / 99 : ℝ) *
      upperSaddleShellThirdCoefficient ε)
    (V₀ := saddleSourceSecondBranchVarianceFloor ε)
    (z := ℓ ^ (1 / 12 : ℝ))
    (T := T)
    hℓpositive hfloorpositive hvariance hC
    (Real.rpow_nonneg hℓpositive.le _)
    hthird' (by
      simpa only [one_div, saddleSourceSecondBranchCentralRadius] using! hT)
  calc
    (ℓ * upperSaddleThirdMoment ε ℓ δ / 6) *
        |T| ^ 3 ≤
      ((2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) / 6) *
        (ℓ ^ (1 / 12 : ℝ)) ^ 3 /
          (Real.sqrt ℓ *
            Real.sqrt (saddleSourceSecondBranchVarianceFloor ε)) :=
      hbase
    _ = ((2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) /
            (6 * Real.sqrt
              (saddleSourceSecondBranchVarianceFloor ε))) *
          (((ℓ ^ (1 / 12 : ℝ)) ^ 3) /
            Real.sqrt ℓ) := by
      ring
    _ = ((2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) /
            (6 * Real.sqrt
              (saddleSourceSecondBranchVarianceFloor ε))) *
          ℓ ^ (-(1 / 4 : ℝ)) := by
      rw [saddleSource_central_rpow_cube_div_sqrt hℓpositive]

private theorem saddleSource_scaled_central_radius_le
    {ℓ η V c U z : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c) (hηU : η ≤ U)
    (hz : 0 ≤ z) (hvariance : c ≤ η * V) :
    z / Real.sqrt (ℓ * V) ≤
      (U / Real.sqrt c) *
        (z / Real.sqrt (ℓ * η)) := by
  have hV : 0 < V := by
    nlinarith [hvariance, mul_pos hη hc]
  have hs : 0 < Real.sqrt (ℓ * V) :=
    Real.sqrt_pos.2 (mul_pos hℓ hV)
  have ht : 0 < Real.sqrt (ℓ * η) :=
    Real.sqrt_pos.2 (mul_pos hℓ hη)
  have hw : 0 < Real.sqrt (η * V) :=
    Real.sqrt_pos.2 (mul_pos hη hV)
  have hcroot : 0 < Real.sqrt c :=
    Real.sqrt_pos.2 hc
  have hcross :
      Real.sqrt (ℓ * V) * η =
        Real.sqrt (ℓ * η) * Real.sqrt (η * V) := by
    have heq :
        (Real.sqrt (ℓ * V) * η) ^ 2 =
          (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) ^ 2 := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hℓ.le hV.le),
        Real.sq_sqrt (mul_nonneg hℓ.le hη.le),
        Real.sq_sqrt (mul_nonneg hη.le hV.le)]
      ring
    nlinarith [mul_pos hs hη, mul_pos ht hw]
  have hwlower : Real.sqrt c ≤ Real.sqrt (η * V) :=
    Real.sqrt_le_sqrt hvariance
  have hU : 0 ≤ U := hη.le.trans hηU
  calc
    z / Real.sqrt (ℓ * V) =
        η * z /
          (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) := by
      field_simp [hs.ne', ht.ne', hw.ne']
      calc
        z * Real.sqrt (ℓ * η) * Real.sqrt (V * η) =
          z * (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) := by
            rw [mul_comm V η]
            ring
        _ = z * (Real.sqrt (ℓ * V) * η) := by
          rw [hcross]
        _ = z * Real.sqrt (ℓ * V) * η := by ring
    _ ≤ U * z /
        (Real.sqrt (ℓ * η) * Real.sqrt c) := by
      gcongr
    _ = (U / Real.sqrt c) *
        (z / Real.sqrt (ℓ * η)) := by
      ring

private theorem saddleSourceFirstBranch_central_radius_le
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a))) :
    saddleSourceFirstBranchCentralRadius ε ℓ u ≤
      ((2 + ε / 2) / Real.sqrt (2 * ε)) *
        (ℓ * (1 + u)) ^ (-(5 / 12 : ℝ)) := by
  have hη : 0 < 1 + u := by linarith
  have hx : 0 < ℓ * (1 + u) := mul_pos hℓ hη
  have hvariance :=
    upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin
  have hbase := saddleSource_scaled_central_radius_le
    (ℓ := ℓ) (η := 1 + u)
    (V := saddleSourceGaussianVariance ε ℓ u)
    (c := 2 * ε) (U := 2 + ε / 2)
    (z := (ℓ * (1 + u)) ^ (1 / 12 : ℝ))
    hℓ hη (by positivity) (by linarith)
    (Real.rpow_nonneg hx.le _) hvariance
  calc
    saddleSourceFirstBranchCentralRadius ε ℓ u ≤
      ((2 + ε / 2) / Real.sqrt (2 * ε)) *
        ((ℓ * (1 + u)) ^ (1 / 12 : ℝ) /
          Real.sqrt (ℓ * (1 + u))) := by
      simpa only [saddleSourceFirstBranchCentralRadius, one_div, Nat.ofNat_nonneg,
        Real.sqrt_mul] using! hbase
    _ = ((2 + ε / 2) / Real.sqrt (2 * ε)) *
        (ℓ * (1 + u)) ^ (-(5 / 12 : ℝ)) := by
      rw [saddleSource_central_rpow_div_sqrt hx]

private theorem saddleSourceSecondBranch_central_radius_le
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hfloor : saddleSourceSecondBranchVarianceFloor ε ≤
      saddleSourceGaussianVariance ε ℓ u)
    (hfloorpos : 0 < saddleSourceSecondBranchVarianceFloor ε) :
    saddleSourceSecondBranchCentralRadius ε ℓ u ≤
      (1 / Real.sqrt
        (saddleSourceSecondBranchVarianceFloor ε)) *
          ℓ ^ (-(5 / 12 : ℝ)) := by
  have hV : 0 < saddleSourceGaussianVariance ε ℓ u :=
    hfloorpos.trans_le hfloor
  have hz : 0 ≤ ℓ ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg hℓ.le _
  calc
    saddleSourceSecondBranchCentralRadius ε ℓ u =
        ℓ ^ (1 / 12 : ℝ) /
          Real.sqrt
            (ℓ * saddleSourceGaussianVariance ε ℓ u) := rfl
    _ ≤ ℓ ^ (1 / 12 : ℝ) /
          Real.sqrt
            (ℓ * saddleSourceSecondBranchVarianceFloor ε) := by
      gcongr
    _ = (1 / Real.sqrt
          (saddleSourceSecondBranchVarianceFloor ε)) *
        (ℓ ^ (1 / 12 : ℝ) / Real.sqrt ℓ) := by
      rw [Real.sqrt_mul hℓ.le]
      ring
    _ = (1 / Real.sqrt
          (saddleSourceSecondBranchVarianceFloor ε)) *
        ℓ ^ (-(5 / 12 : ℝ)) := by
      rw [saddleSource_central_rpow_div_sqrt hℓ]

private theorem eventually_saddleSourceFirstBranch_cubic_window :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              ∀ T : ℝ,
                |T| ≤ saddleSourceFirstBranchCentralRadius ε ℓ u →
                (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
                    |T| ^ 3 < κ := by
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear :=
      (tendsto_id.mono_left
        (nhdsWithin_le_nhds :
          𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hnear] with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, heps,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)) := by
    intro a ha
    have h := hmargin a ha
    linarith
  intro κ hκ
  let A : ℝ := saddleSourceFirstBranchThirdMomentCoefficient ε /
    (12 * ε * Real.sqrt (2 * ε))
  have htendsto :
      Tendsto (fun x : ℝ => A * x ^ (-(1 / 4 : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    convert! tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 1 / 4)) using 1
    all_goals simp only [mul_zero]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (htendsto.eventually (Iio_mem_nhds hκ))
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * N),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)]
    with ℓ hℓ hlog hlogone
  intro u hu huupper hstar T hT
  have hxN : N ≤ ℓ * (1 + u) := by
    linarith
  have hxone : 1 ≤ ℓ * (1 + u) := by
    linarith
  have hbound := saddleSourceFirstBranch_cubic_central_window_le
    hε hεsmall hℓ hu huupper horder hmargin'
    hxone hT
  exact hbound.trans_lt (hN (ℓ * (1 + u)) hxN)

private theorem eventually_saddleSourceSecondBranch_cubic_window :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            ∀ T : ℝ,
              |T| ≤
                saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) →
              (ℓ * upperSaddleThirdMoment ε ℓ δ / 6) *
                  |T| ^ 3 < κ := by
  filter_upwards [
    eventually_saddleSourceSecondBranch_cubic_central_window_le]
    with ε hquant
  intro κ hκ
  let A : ℝ :=
    (2 + (100 / 99 : ℝ) *
      upperSaddleShellThirdCoefficient ε) /
        (6 * Real.sqrt
          (saddleSourceSecondBranchVarianceFloor ε))
  have htendsto :
      Tendsto (fun ℓ : ℝ => A * ℓ ^ (-(1 / 4 : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    convert! tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 1 / 4)) using 1
    all_goals simp only [mul_zero]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    htendsto.eventually (Iio_mem_nhds hκ)]
    with ℓ hℓ hsmall
  intro δ hδ T hT
  exact (hquant ℓ hℓ δ hδ T hT).trans_lt hsmall

private theorem eventually_saddleSourceFirstBranch_central_radius_lt :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              saddleSourceFirstBranchCentralRadius ε ℓ u < κ := by
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear :=
      (tendsto_id.mono_left
        (nhdsWithin_le_nhds :
          𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hnear] with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, heps,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)) := by
    intro a ha
    have h := hmargin a ha
    linarith
  intro κ hκ
  let A : ℝ := (2 + ε / 2) / Real.sqrt (2 * ε)
  have htendsto :
      Tendsto (fun x : ℝ => A * x ^ (-(5 / 12 : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    convert! tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 5 / 12)) using 1
    all_goals simp only [mul_zero]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (htendsto.eventually (Iio_mem_nhds hκ))
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * N)]
    with ℓ hℓ hlog
  intro u hu huupper hstar
  have hxN : N ≤ ℓ * (1 + u) := by
    linarith
  exact (saddleSourceFirstBranch_central_radius_le
    hε hεsmall hℓ hu huupper horder hmargin').trans_lt
      (hN (ℓ * (1 + u)) hxN)

private theorem eventually_saddleSourceSecondBranch_central_radius_lt :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) < κ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε hfloor
  change 0 < ε at hε
  have hfloorpos :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  intro κ hκ
  let A : ℝ :=
    1 / Real.sqrt (saddleSourceSecondBranchVarianceFloor ε)
  have htendsto :
      Tendsto (fun ℓ : ℝ => A * ℓ ^ (-(5 / 12 : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    convert! tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 5 / 12)) using 1
    all_goals simp only [mul_zero]
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htendsto.eventually (Iio_mem_nhds hκ)]
    with ℓ hℓ hsmall
  intro δ hδ
  exact (saddleSourceSecondBranch_central_radius_le
    hℓ (hfloor ℓ hℓ δ hδ) hfloorpos).trans_lt hsmall

private theorem exists_saddleSource_central_error_tolerance
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      2 * q + (1 + 2 * q) * q < κ := by
  let q : ℝ := min (1 / 4 : ℝ) (κ / 8)
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hquarter : q ≤ (1 / 4 : ℝ) := min_le_left _ _
  have hk : q ≤ κ / 8 := min_le_right _ _
  refine ⟨q, hq, by linarith, ?_⟩
  linarith [mul_nonneg hq.le
    (sub_nonneg.mpr hquarter)]

private theorem eventually_saddleSourceFirstBranch_centralGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              (‖∫ T : ℝ in
                Icc (-(saddleSourceFirstBranchCentralRadius ε ℓ u))
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                  (saddleSourceCenteredPlusIntegrand ε ℓ u
                    (saddleSourceStationaryLogRadius ε ℓ u) T -
                      saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
                κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
                  (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) ∧
              (1 + ε / 4 ≤ u →
                ‖∫ T : ℝ in
                  Icc (-(saddleSourceFirstBranchCentralRadius ε ℓ u))
                      (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    (saddleSourceCenteredMinusIntegrand ε ℓ u
                      (saddleSourceStationaryLogRadius ε ℓ u) T -
                        saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
                  κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
                    (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSourceFirstBranch_cubic_window,
    eventually_saddleSourceFirstBranch_central_radius_lt]
    with ε hε horder hmargin hvariance hcubic hradius
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)) := by
    intro a ha
    have h := hmargin a ha
    linarith
  intro κ hκ
  obtain ⟨q, hq, hqone, hfactor⟩ :=
    exists_saddleSource_central_error_tolerance hκ
  obtain ⟨Rp, hRp, hplus⟩ :=
    exists_plusPolynomial_uniform_central_window hε hq
  obtain ⟨Rm, hRm, hminus⟩ :=
    exists_minusPolynomial_uniform_central_window hε hq
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hcubic q hq,
    hradius Rp hRp,
    hradius Rm hRm]
    with ℓ hℓ hqc hsmallplus hsmallminus
  intro u hu huupper hstar
  let R : ℝ := saddleSourceFirstBranchCentralRadius ε ℓ u
  have hV := hvariance ℓ hℓ u hu huupper
  have hR : 0 ≤ R := by
    have hη : 0 ≤ 1 + u := by linarith
    try dsimp [R, saddleSourceFirstBranchCentralRadius]
    exact div_nonneg
      (Real.rpow_nonneg (mul_nonneg hℓ.le hη) _)
      (Real.sqrt_nonneg _)
  have hphase : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q := by
    intro T hT
    exact (hqc u hu huupper hstar T hT).le
  have hG : 0 < ∫ T : ℝ,
      saddleSourceGaussianKernel ε ℓ u T :=
    saddleSourceGaussianKernel_integral_pos hℓ hV
  constructor
  · have hpoly : ∀ T : ℝ, |T| ≤ R →
        ‖plusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          q * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      intro T hT
      exact hplus u hu.le T
        (hT.trans (hsmallplus u hu huupper hstar).le)
    have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hcentral :=
      saddleSourceCenteredPlusIntegrand_centralGaussianError_le
        hε hℓ hu horder hmargin' hV hR hq.le hqone hq.le
        hphase hpoly
    calc
      ‖∫ T : ℝ in Icc (-R) R,
          (saddleSourceCenteredPlusIntegrand ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
              saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ ≤
        (2 * q + (1 + 2 * q) * q) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) :=
        hcentral
      _ < κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
        gcongr
  · intro huminus
    have hpoly : ∀ T : ℝ, |T| ≤ R →
        ‖minusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          q * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      intro T hT
      exact hminus u huminus T
        (hT.trans (hsmallminus u hu huupper hstar).le)
    have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hbeta := div_pos hε four_pos
      have hbound :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    have hcentral :=
      saddleSourceCenteredMinusIntegrand_centralGaussianError_le
        hε hℓ hu horder hmargin' hV hR hq.le hqone hq.le
        hphase hpoly
    calc
      ‖∫ T : ℝ in Icc (-R) R,
          (saddleSourceCenteredMinusIntegrand ε ℓ u
            (saddleSourceStationaryLogRadius ε ℓ u) T -
              saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ ≤
        (2 * q + (1 + 2 * q) * q) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) :=
        hcentral
      _ < κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
        gcongr

private theorem eventually_saddleSourceSecondBranch_centralGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            (‖∫ T : ℝ in
              Icc (-(saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)))
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                (saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                  (saddleSourceStationaryLogRadius ε ℓ (1 + δ)) T -
                    saddleSourceGaussianPlusIntegrand
                      ε ℓ (1 + δ) T)‖ <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
            (‖∫ T : ℝ in
              Icc (-(saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)))
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                (saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                  (saddleSourceStationaryLogRadius ε ℓ (1 + δ)) T -
                    saddleSourceGaussianMinusIntegrand
                      ε ℓ (1 + δ) T)‖ <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ (1 + δ) T)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_cubic_window,
    eventually_saddleSourceSecondBranch_central_radius_lt]
    with ε hε horder hmargin hvariance hcubic hradius
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)) := by
    intro a ha
    have h := hmargin a ha
    linarith
  intro κ hκ
  obtain ⟨q, hq, hqone, hfactor⟩ :=
    exists_saddleSource_central_error_tolerance hκ
  obtain ⟨Rp, hRp, hplus⟩ :=
    exists_plusPolynomial_uniform_central_window hε hq
  obtain ⟨Rm, hRm, hminus⟩ :=
    exists_minusPolynomial_uniform_central_window hε hq
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hcubic q hq,
    hradius Rp hRp,
    hradius Rm hRm]
    with ℓ hℓ hqc hsmallplus hsmallminus
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  have hδzero : 0 ≤ δ := by linarith
  have hu : -1 < u := by
    try dsimp [u]
    linarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    linarith
  have hV : 0 < saddleSourceGaussianVariance ε ℓ u := by
    try dsimp [u]
    exact hvariance ℓ hℓ δ hδ
  have hR : 0 ≤ R := by
    try dsimp [R, saddleSourceSecondBranchCentralRadius]
    positivity
  have hphase : ∀ T : ℝ, |T| ≤ R →
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤ q := by
    intro T hT
    have h := hqc δ hδ T hT
    have huarg : u - 1 = δ := by
      try dsimp [u]
      ring
    rw [huarg]
    exact h.le
  have hG : 0 < ∫ T : ℝ,
      saddleSourceGaussianKernel ε ℓ u T :=
    saddleSourceGaussianKernel_integral_pos hℓ hV
  constructor
  · have hpoly : ∀ T : ℝ, |T| ≤ R →
        ‖plusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          q * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      intro T hT
      exact hplus u hu.le T
        (hT.trans (hsmallplus δ hδ).le)
    have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hcentral :=
      saddleSourceCenteredPlusIntegrand_centralGaussianError_le
        hε hℓ hu horder hmargin' hV hR hq.le hqone hq.le
        hphase hpoly
    change
      ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredPlusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)
    exact hcentral.trans_lt (by gcongr)
  · have hpoly : ∀ T : ℝ, |T| ≤ R →
        ‖minusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ)) -
          minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
          q * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      intro T hT
      exact hminus u huminus T
        (hT.trans (hsmallminus δ hδ).le)
    have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hbeta := div_pos hε four_pos
      have hbound :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    have hcentral :=
      saddleSourceCenteredMinusIntegrand_centralGaussianError_le
        hε hℓ hu horder hmargin' hV hR hq.le hqone hq.le
        hphase hpoly
    change
      ‖∫ T : ℝ in Icc (-R) R,
        (saddleSourceCenteredMinusIntegrand ε ℓ u
          (saddleSourceStationaryLogRadius ε ℓ u) T -
            saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)
    exact hcentral.trans_lt (by gcongr)

private theorem upperPositiveShellDamping_local_variance_lower
    {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ)
    (hT : |T| ≤ 1 / (2 * ((ε⁻¹ ^ 3) + 1))) :
    (ℓ / 4) * upperPositiveShellVariance ε δ * T ^ 2 ≤
      positiveShellDamping ε ℓ δ T := by
  let B : ℝ := (ε⁻¹ ^ 3)
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  have hB1 : 0 < B + 1 := by linarith
  have horder : B ≤ B + 1 := by linarith
  have hwindow : (B + 1) * |T| ≤ 1 / 2 := by
    calc
      (B + 1) * |T| ≤
          (B + 1) * (1 / (2 * (B + 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            simpa only [one_div, mul_inv_rev, B] using! hT
      _ = 1 / 2 := by
        field_simp [hB1.ne']
  have hdensity : Continuous (positiveShellDensity ε) :=
    positiveShellDensity_continuous ε
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hosc : Continuous
      (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hleft : Continuous
      (fun a : ℝ =>
        (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4)) :=
    ((hdensity.mul (continuous_id.pow 2)).mul
      hcosh).mul continuous_const
  have hright : Continuous
      (fun a : ℝ =>
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T))) :=
    (hdensity.mul hcosh).mul hosc
  have hpoint : ∀ a ∈ Icc B (B + 1),
      (positiveShellDensity ε a * a ^ 2 *
        Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4) ≤
          positiveShellDensity ε a *
            Real.cosh ((1 + δ) * a) *
              (1 - Real.cos (a * T)) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have haT : |a * T| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc
        a * |T| ≤ (B + 1) * |T| :=
          mul_le_mul_of_nonneg_right ha.2 (abs_nonneg T)
        _ ≤ 1 / 2 := hwindow
        _ ≤ 1 := by norm_num
    have hquadratic := upper_one_sub_cos_quadratic_lower haT
    have hw : 0 ≤
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) := by
      unfold positiveShellDensity
      positivity [shellWeight_pos ε]
    calc
      (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4) =
        (positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a)) *
            ((a * T) ^ 2 / 4) := by ring
      _ ≤ (positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a)) *
            (1 - Real.cos (a * T)) :=
        mul_le_mul_of_nonneg_left hquadratic hw
      _ = positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)) := by ring
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hleft.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _) hpoint
  have hleftvalue :
      (∫ a in B..B + 1,
        (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) * (T ^ 2 / 4)) =
        upperPositiveShellVariance ε δ * (T ^ 2 / 4) := by
    rw [intervalIntegral.integral_mul_const]
    rfl
  rw [hleftvalue] at hmono
  unfold positiveShellDamping
  change
    (ℓ / 4) * upperPositiveShellVariance ε δ * T ^ 2 ≤
      ℓ * ∫ a in B..B + 1,
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T))
  calc
    (ℓ / 4) * upperPositiveShellVariance ε δ * T ^ 2 =
        ℓ * (upperPositiveShellVariance ε δ * (T ^ 2 / 4)) := by
          ring
    _ ≤ ℓ * ∫ a in B..B + 1,
        positiveShellDensity ε a *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)) :=
      mul_le_mul_of_nonneg_left hmono hℓ

private theorem upperGammaVarianceDensity_laplace_linear_lower
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    a * Real.exp (-η * a) ≤
      a ^ 2 * upperGammaMeasureDensity ℓ η a := by
  let x : ℝ := 2 * a / ℓ
  have hx : 0 < x := by
    try dsimp [x]
    positivity
  have hden : 0 < 1 - Real.exp (-x) := by
    have h := Real.exp_lt_one_iff.mpr
      (show -x < 0 by linarith)
    linarith
  have hdenone : 1 - Real.exp (-x) ≤ 1 := by
    linarith [Real.exp_pos (-x)]
  have hinv : 1 ≤ (1 - Real.exp (-x))⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hden).2
    simpa only [one_mul, tsub_le_iff_right, le_add_iff_nonneg_right] using! hdenone
  have hfactor : 0 ≤ a * Real.exp (-η * a) := by
    positivity
  calc
    a * Real.exp (-η * a) =
        (a * Real.exp (-η * a)) * 1 := by ring
    _ ≤ (a * Real.exp (-η * a)) *
        (1 - Real.exp (-x))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hfactor
    _ = a ^ 2 * upperGammaMeasureDensity ℓ η a := by
      unfold upperGammaMeasureDensity
      try dsimp [x]
      field_simp [ha.ne', hden.ne']

private theorem upperGammaDamping_local_variance_lower
    {ℓ η T : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hT : |T| ≤ η) :
    (ℓ / (32 * Real.exp 1)) *
        upperGammaVariance ℓ η * T ^ 2 ≤
      upperGammaDamping ℓ η T := by
  let p : ℝ := 1 / (2 * η)
  let q : ℝ := 1 / η
  let C : ℝ :=
    ((ℓ / 4 + 1 / (4 * η)) * (Real.exp 1)⁻¹) *
      (T ^ 2 / 4)
  have hp : 0 < p := by
    try dsimp [p]
    positivity
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hpq : p ≤ q := by
    try dsimp [p, q]
    calc
      1 / (2 * η) = (1 / η) / 2 := by ring
      _ ≤ 1 / η := by
        linarith [inv_pos.mpr hη]
  have hsubset : Ioc p q ⊆ Ioi (0 : ℝ) := by
    intro a ha
    exact hp.trans ha.1
  have hfull := upperGammaDampingIntegrand_integrable
    hℓ hη T
  have hsmall := hfull.mono_set hsubset
  have hconstant : IntegrableOn
      (fun _ : ℝ => C) (Ioc p q) := by
    exact integrableOn_const (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hpoint : ∀ a ∈ Ioc p q,
      C ≤ upperGammaDampingIntegrand ℓ η T a := by
    intro a ha
    have ha0 : 0 < a := hp.trans ha.1
    have halower : 1 / (2 * η) ≤ a := by
      simpa [p] using! ha.1.le
    have haupper : a ≤ 1 / η := by
      simpa [q] using! ha.2
    have hquarter : 1 / (4 * η) ≤ a / 2 := by
      calc
        1 / (4 * η) = (1 / (2 * η)) / 2 := by ring
        _ ≤ a / 2 := by gcongr
    have heta : η * a ≤ 1 := by
      calc
        η * a ≤ η * (1 / η) :=
          mul_le_mul_of_nonneg_left haupper hη.le
        _ = 1 := by field_simp
    have hexp : (Real.exp 1)⁻¹ ≤
        Real.exp (-η * a) := by
      rw [← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      linarith
    have hmoment :
        (ℓ / 4 + 1 / (4 * η)) *
            (Real.exp 1)⁻¹ ≤
          a ^ 2 * upperGammaMeasureDensity ℓ η a := by
      have hbase : 0 ≤ ℓ / 4 + 1 / (4 * η) := by
        positivity
      have hgamma :=
        (upperGammaVarianceDensity_pointwise_bounds
          (η := η) hℓ ha0).1
      have hlinear :=
        upperGammaVarianceDensity_laplace_linear_lower
          (η := η) hℓ ha0
      calc
        (ℓ / 4 + 1 / (4 * η)) *
            (Real.exp 1)⁻¹ ≤
          (ℓ / 4 + 1 / (4 * η)) *
            Real.exp (-η * a) :=
          mul_le_mul_of_nonneg_left hexp hbase
        _ ≤ (ℓ / 4 + a / 2) *
            Real.exp (-η * a) := by
          gcongr
        _ ≤ a ^ 2 * upperGammaMeasureDensity ℓ η a := by
          linarith
    have haT : |a * T| ≤ 1 := by
      rw [abs_mul, abs_of_pos ha0]
      calc
        a * |T| ≤ a * η :=
          mul_le_mul_of_nonneg_left hT ha0.le
        _ = η * a := by ring
        _ ≤ 1 := heta
    have hcos := upper_one_sub_cos_quadratic_lower haT
    have hdensity := upperGammaMeasureDensity_pos
      (η := η) hℓ ha0
    calc
      C = (T ^ 2 / 4) *
          ((ℓ / 4 + 1 / (4 * η)) *
            (Real.exp 1)⁻¹) := by
            try dsimp [C]
            ring
      _ ≤ (T ^ 2 / 4) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a) :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = ((a * T) ^ 2 / 4) *
          upperGammaMeasureDensity ℓ η a := by
            ring
      _ ≤ (1 - Real.cos (a * T)) *
          upperGammaMeasureDensity ℓ η a :=
        mul_le_mul_of_nonneg_right hcos hdensity.le
      _ = upperGammaDampingIntegrand ℓ η T a := rfl
  have hmono := MeasureTheory.setIntegral_mono_on
    hconstant hsmall measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
        upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    unfold upperGammaDampingIntegrand
    exact mul_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))
      (upperGammaMeasureDensity_pos
        (η := η) hℓ ha).le
  have haesubset :
      Ioc p q ≤ᶠ[ae (volume : Measure ℝ)] Ioi 0 :=
    Filter.Eventually.of_forall
      (fun a ha => hsubset ha)
  have hrestrict := MeasureTheory.setIntegral_mono_set
    hfull hnonnegative haesubset
  have hmeasure :
      (volume : Measure ℝ).real (Ioc p q) = q - p := by
    change ((volume : Measure ℝ) (Ioc p q)).toReal = q - p
    rw [Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)]
  have hconstintegral :
      (∫ a : ℝ in Ioc p q, C) = (q - p) * C := by
    rw [setIntegral_const, hmeasure]
    rfl
  have hγupper := (upperGammaVariance_bounds hℓ hη).2
  have hscaled :
      ℓ * upperGammaVariance ℓ η ≤
        ℓ / η + 1 / η ^ 2 := by
    calc
      ℓ * upperGammaVariance ℓ η ≤
          ℓ * (1 / (2 * η) + 1 / (ℓ * η ^ 2)) :=
        mul_le_mul_of_nonneg_left hγupper hℓ.le
      _ = ℓ / (2 * η) + 1 / η ^ 2 := by
        field_simp [hℓ.ne', hη.ne']
      _ ≤ ℓ / η + 1 / η ^ 2 := by
        gcongr
        linarith
  have hidentity :
      (q - p) * C =
        ((ℓ / η + 1 / η ^ 2) /
          (32 * Real.exp 1)) * T ^ 2 := by
    try dsimp [p, q, C]
    field_simp [hη.ne', (Real.exp_pos 1).ne']; ring
  calc
    (ℓ / (32 * Real.exp 1)) *
        upperGammaVariance ℓ η * T ^ 2 =
      (ℓ * upperGammaVariance ℓ η /
        (32 * Real.exp 1)) * T ^ 2 := by
          ring
    _ ≤ ((ℓ / η + 1 / η ^ 2) /
        (32 * Real.exp 1)) * T ^ 2 := by
          gcongr
    _ = (q - p) * C := hidentity.symm
    _ = ∫ a : ℝ in Ioc p q, C :=
      hconstintegral.symm
    _ ≤ ∫ a : ℝ in Ioc p q,
        upperGammaDampingIntegrand ℓ η T a := hmono
    _ ≤ ∫ a : ℝ in Ioi 0,
        upperGammaDampingIntegrand ℓ η T a := hrestrict
    _ = upperGammaDamping ℓ η T := rfl

private theorem eventually_saddleSourceContourDamping_secondBranch_local_coercivity :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            |T| ≤ 1 / (2 * ((ε⁻¹ ^ 3) + 1)) →
              (ℓ / (100 * Real.exp 1)) *
                  saddleSourceGaussianVariance ε ℓ (1 + δ) *
                    T ^ 2 ≤
                saddleSourceContourDamping ε ℓ (1 + δ) T := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upperSaddleDamping_gamma_add_shell,
      eventually_upper_netShellVariance_bounds]
    with ε hε hdom hnet
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T hT
  have hδnonnegative : 0 ≤ δ := by
    linarith
  have hη : 0 < 2 + δ := by
    linarith
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  have hhalf :
      1 / (2 * ((ε⁻¹ ^ 3) + 1)) ≤ (1 / 2 : ℝ) := by
    have hb : 0 < 2 * ((ε⁻¹ ^ 3) + 1) := by
      positivity
    apply (div_le_iff₀ hb).2
    linarith
  have hTgamma : |T| ≤ 2 + δ := by
    have hsmall := hT.trans hhalf
    linarith
  have hgamma := upperGammaDamping_local_variance_lower
    hℓ hη hTgamma
  have hshell := upperPositiveShellDamping_local_variance_lower
    (δ := δ) hε hℓ.le hT
  have hS : 0 ≤ upperPositiveShellVariance ε δ :=
    (upperPositiveShellVariance_pos hε hδnonnegative).le
  have hG : 0 ≤ upperGammaVariance ℓ (2 + δ) := by
    have h := (upperGammaVariance_bounds hℓ hη).1
    have hpositive : 0 < 1 / (2 * (2 + δ)) := by
      positivity
    exact hpositive.le.trans h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hγcoefficient :
      (1 / (100 * Real.exp 1) : ℝ) ≤
        1 / (32 * Real.exp 1) := by
    gcongr
    norm_num
  have hγbase :
      0 ≤ ℓ * upperGammaVariance ℓ (2 + δ) * T ^ 2 := by
    positivity
  have hγscaled :
      (ℓ / (100 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 ≤
        upperGammaDamping ℓ (2 + δ) T := by
    calc
      (ℓ / (100 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 ≤
        (ℓ / (32 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 := by
            convert! mul_le_mul_of_nonneg_right
              hγcoefficient hγbase using 1 <;> ring
      _ ≤ upperGammaDamping ℓ (2 + δ) T := hgamma
  have heone : 1 ≤ Real.exp 1 :=
    (Real.one_le_exp_iff).mpr (by norm_num)
  have hscoefficient :
      (1 / (100 * Real.exp 1) : ℝ) ≤
        (99 / 100 : ℝ) * (1 / 4) := by
    calc
      (1 / (100 * Real.exp 1) : ℝ) ≤ 1 / 100 := by
        apply (div_le_iff₀ (by positivity :
          (0 : ℝ) < 100 * Real.exp 1)).2
        linarith
      _ ≤ (99 / 100 : ℝ) * (1 / 4) := by
        norm_num
  have hsbase :
      0 ≤ ℓ * upperPositiveShellVariance ε δ * T ^ 2 := by
    positivity
  have hsscaled :
      (ℓ / (100 * Real.exp 1)) *
          upperPositiveShellVariance ε δ * T ^ 2 ≤
        (99 / 100 : ℝ) *
          positiveShellDamping ε ℓ δ T := by
    calc
      (ℓ / (100 * Real.exp 1)) *
          upperPositiveShellVariance ε δ * T ^ 2 ≤
        (99 / 100 : ℝ) *
          ((ℓ / 4) *
            upperPositiveShellVariance ε δ * T ^ 2) := by
            convert! mul_le_mul_of_nonneg_right
              hscoefficient hsbase using 1 <;> ring
      _ ≤ (99 / 100 : ℝ) *
          positiveShellDamping ε ℓ δ T :=
        mul_le_mul_of_nonneg_left hshell (by norm_num)
  have hvariance :
      upperSaddleVariance ε ℓ δ ≤
        upperGammaVariance ℓ (2 + δ) +
          upperPositiveShellVariance ε δ := by
    unfold upperSaddleVariance
    linarith [(hnet δ hδ).2]
  have hfactor : 0 ≤
      (ℓ / (100 * Real.exp 1)) * T ^ 2 := by
    positivity
  calc
    (ℓ / (100 * Real.exp 1)) *
        saddleSourceGaussianVariance ε ℓ (1 + δ) *
          T ^ 2 =
      (ℓ / (100 * Real.exp 1)) *
        upperSaddleVariance ε ℓ δ * T ^ 2 := by
          simp only [saddleSourceGaussianVariance, add_sub_cancel_left]
    _ ≤ (ℓ / (100 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 +
        (ℓ / (100 * Real.exp 1)) *
          upperPositiveShellVariance ε δ * T ^ 2 := by
          convert! mul_le_mul_of_nonneg_left
            hvariance hfactor using 1 <;> ring
    _ ≤ upperGammaDamping ℓ (2 + δ) T +
        (99 / 100 : ℝ) *
          positiveShellDamping ε ℓ δ T :=
      add_le_add hγscaled hsscaled
    _ ≤ upperSaddleDamping ε ℓ δ T :=
      hdom ℓ hℓ δ hδ T
    _ = saddleSourceContourDamping ε ℓ (1 + δ) T :=
      (saddleSourceContourDamping_eq_secondBranch
        ε ℓ δ T).symm

private theorem eventually_saddleSourceContourDamping_secondBranch_min_lower_bound :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            (ℓ / (8 * Real.exp 1)) *
                min (T ^ 2 / (2 + δ)) |T| ≤
              saddleSourceContourDamping ε ℓ (1 + δ) T := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleDamping_gamma_add_shell]
    with ε hε hdom
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  have hδ0 : 0 ≤ δ := by linarith
  have hη : 0 < 2 + δ := by linarith
  have hgamma := upperGammaDamping_lower_bound
    hℓ hη T
  have hshell : 0 ≤ (99 / 100 : ℝ) *
      positiveShellDamping ε ℓ δ T := by
    positivity [positiveShellDamping_nonneg
      (ε := ε) (δ := δ) (T := T) hℓ.le]
  rw [saddleSourceContourDamping_eq_secondBranch]
  linarith [hdom ℓ hℓ δ hδ T]

private theorem eventually_saddleSource_secondBranch_weighted_integrable :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          Integrable
            (fun T : ℝ =>
              saddleGaussianTailWeight T *
                Real.exp
                  (-saddleSourceContourDamping
                    ε ℓ (1 + δ) T)) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSourceContourDamping_secondBranch_min_lower_bound]
    with ε hε horder hcoercive
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  let η : ℝ := 2 + δ
  let a : ℝ := ℓ / (8 * Real.exp 1)
  have hδ0 : 0 ≤ δ := by linarith
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hu : -1 < 1 + δ := by linarith
  have hgaussian :=
    saddleGaussianTailWeight_mul_gaussian_integrable
      (div_pos ha hη)
  have hlinear :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have hmajor := hgaussian.add hlinear
  apply hmajor.mono'
    (saddleSourceTailIntegrand_continuous
      hε hℓ hu horder).aestronglyMeasurable
  filter_upwards [] with T
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (saddleGaussianTailWeight_nonneg T)
      (Real.exp_pos _).le)]
  have hsource := hcoercive ℓ hℓ δ hδ T
  have hmin := saddle_exp_neg_mul_min_le_add
    (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
  have hexp :
      Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
        Real.exp (-(a / η) * T ^ 2) +
          Real.exp (-a * |T|) := by
    calc
      Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
        Real.exp (-a * min (T ^ 2 / η) |T|) := by
          apply Real.exp_le_exp.mpr
          simpa only [saddleSourceContourDamping_eq_firstBranch, neg_mul, neg_le_neg_iff, a,
            η] using! neg_le_neg hsource
      _ ≤ Real.exp (-a * (T ^ 2 / η)) +
          Real.exp (-a * |T|) := hmin
      _ = Real.exp (-(a / η) * T ^ 2) +
          Real.exp (-a * |T|) := by
        congr 2
        ring
  change
    saddleGaussianTailWeight T *
        Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
      saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
        saddleGaussianTailWeight T *
          Real.exp (-a * |T|)
  linarith [mul_le_mul_of_nonneg_left hexp
    (saddleGaussianTailWeight_nonneg T)]

private theorem saddleGaussian_weighted_integral_le_rescaled
    {k : ℝ} (hk : 0 < k) :
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      2 * max (1 : ℝ)
          ((Real.sqrt (k / 6) ^ 3)⁻¹) *
        Real.sqrt (Real.pi / (k / 2)) := by
  let s : ℝ := Real.sqrt (k / 6)
  let C : ℝ := max (1 : ℝ) (s ^ 3)⁻¹
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hCone : 1 ≤ C := le_max_left _ _
  have hCinv : (s ^ 3)⁻¹ ≤ C := le_max_right _ _
  have hCproduct : 1 ≤ C * s ^ 3 := by
    calc
      (1 : ℝ) = (s ^ 3)⁻¹ * s ^ 3 := by
        field_simp [hs.ne']
      _ ≤ C * s ^ 3 :=
        mul_le_mul_of_nonneg_right hCinv
          (by positivity)
  have hsquare : s ^ 2 = k / 6 := by
    try dsimp [s]
    rw [Real.sq_sqrt (by positivity)]
  have hweight (T : ℝ) :
      saddleGaussianTailWeight T ≤
        C * saddleGaussianTailWeight (s * T) := by
    unfold saddleGaussianTailWeight
    rw [abs_mul, abs_of_pos hs]
    have hcube : 0 ≤ |T| ^ 3 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right
      hCproduct hcube
    linarith
  have hpoint (T : ℝ) :
      saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2) ≤
        (2 * C) * Real.exp (-(k / 2) * T ^ 2) := by
    calc
      saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2) ≤
        (C * saddleGaussianTailWeight (s * T)) *
          Real.exp (-k * T ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (hweight T) (Real.exp_pos _).le
      _ ≤ (C * (2 * Real.exp (3 * (s * T) ^ 2))) *
          Real.exp (-k * T ^ 2) := by
            gcongr
            exact saddleGaussianTailWeight_le_two_exp_three_sq
              (s * T)
      _ = (2 * C) * Real.exp (-(k / 2) * T ^ 2) := by
        have hargument :
            3 * (s * T) ^ 2 + -k * T ^ 2 =
              -(k / 2) * T ^ 2 := by
          rw [mul_pow, hsquare]
          ring
        calc
          (C * (2 * Real.exp (3 * (s * T) ^ 2))) *
              Real.exp (-k * T ^ 2) =
            (2 * C) *
              (Real.exp (3 * (s * T) ^ 2) *
                Real.exp (-k * T ^ 2)) := by ring
          _ = (2 * C) *
              Real.exp (-(k / 2) * T ^ 2) := by
            rw [← Real.exp_add, hargument]
  have hsource :=
    saddleGaussianTailWeight_mul_gaussian_integrable hk
  have hmajor :=
    (integrable_exp_neg_mul_sq
      (show 0 < k / 2 by positivity)).const_mul (2 * C)
  have hmono := integral_mono_ae hsource hmajor
    (Filter.Eventually.of_forall hpoint)
  calc
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      ∫ T : ℝ,
        (2 * C) * Real.exp (-(k / 2) * T ^ 2) := hmono
    _ = 2 * max (1 : ℝ)
          ((Real.sqrt (k / 6) ^ 3)⁻¹) *
        Real.sqrt (Real.pi / (k / 2)) := by
      rw [MeasureTheory.integral_const_mul, integral_gaussian]

private theorem saddleExponential_weighted_integral_le_rescaled
    {k : ℝ} (hk : 0 < k) :
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      2 * max (1 : ℝ) (((k / 6) ^ 3)⁻¹) *
        (2 / (k / 2)) := by
  let s : ℝ := k / 6
  let C : ℝ := max (1 : ℝ) (s ^ 3)⁻¹
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hCone : 1 ≤ C := le_max_left _ _
  have hCinv : (s ^ 3)⁻¹ ≤ C := le_max_right _ _
  have hCproduct : 1 ≤ C * s ^ 3 := by
    calc
      (1 : ℝ) = (s ^ 3)⁻¹ * s ^ 3 := by
        field_simp [hs.ne']
      _ ≤ C * s ^ 3 :=
        mul_le_mul_of_nonneg_right hCinv
          (by positivity)
  have hweight (T : ℝ) :
      saddleGaussianTailWeight T ≤
        C * saddleGaussianTailWeight (s * T) := by
    unfold saddleGaussianTailWeight
    rw [abs_mul, abs_of_pos hs]
    have hcube : 0 ≤ |T| ^ 3 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right
      hCproduct hcube
    linarith
  have hpoint (T : ℝ) :
      saddleGaussianTailWeight T *
          Real.exp (-k * |T|) ≤
        (2 * C) * Real.exp (-(k / 2) * |T|) := by
    calc
      saddleGaussianTailWeight T *
          Real.exp (-k * |T|) ≤
        (C * saddleGaussianTailWeight (s * T)) *
          Real.exp (-k * |T|) := by
            exact mul_le_mul_of_nonneg_right
              (hweight T) (Real.exp_pos _).le
      _ ≤ (C * (2 * Real.exp (3 * |s * T|))) *
          Real.exp (-k * |T|) := by
            gcongr
            exact saddleGaussianTailWeight_le_two_exp_three_abs
              (s * T)
      _ = (2 * C) * Real.exp (-(k / 2) * |T|) := by
        have hargument :
            3 * |s * T| + -k * |T| =
              -(k / 2) * |T| := by
          rw [abs_mul, abs_of_pos hs]
          try dsimp [s]
          ring
        calc
          (C * (2 * Real.exp (3 * |s * T|))) *
              Real.exp (-k * |T|) =
            (2 * C) *
              (Real.exp (3 * |s * T|) *
                Real.exp (-k * |T|)) := by ring
          _ = (2 * C) *
              Real.exp (-(k / 2) * |T|) := by
            rw [← Real.exp_add, hargument]
  have hsource :=
    saddleGaussianTailWeight_mul_exp_abs_integrable hk
  have hmajor :=
    (integrable_exp_neg_mul_abs
      (show 0 < k / 2 by positivity)).const_mul (2 * C)
  have hmono := integral_mono_ae hsource hmajor
    (Filter.Eventually.of_forall hpoint)
  calc
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      ∫ T : ℝ,
        (2 * C) * Real.exp (-(k / 2) * |T|) := hmono
    _ = 2 * max (1 : ℝ) (((k / 6) ^ 3)⁻¹) *
        (2 / (k / 2)) := by
      rw [MeasureTheory.integral_const_mul,
        saddle_integral_exp_neg_mul_abs
          (show 0 < k / 2 by positivity)]

private noncomputable def saddleSourceSecondBranchLocalFrequency (ε : ℝ) : ℝ :=
  1 / (2 * ((ε⁻¹ ^ 3) + 1))

private noncomputable def saddleSourceSecondBranchGaussianRate
    (ε ℓ δ : ℝ) : ℝ :=
  (ℓ / (100 * Real.exp 1)) *
    saddleSourceGaussianVariance ε ℓ (1 + δ)

private noncomputable def saddleSourceSecondBranchGammaGaussianRate
    (ℓ δ : ℝ) : ℝ :=
  (ℓ / (8 * Real.exp 1)) / (2 + δ)

private noncomputable def saddleSourceSecondBranchGammaLinearRate
    (ℓ : ℝ) : ℝ :=
  ℓ / (8 * Real.exp 1)

private noncomputable def saddleSourceSecondBranchOuterBarrier
    (ε ℓ δ : ℝ) : ℝ :=
  (99 / 5000 : ℝ) * ℓ * shellWeight ε *
    Real.exp (δ * (ε⁻¹ ^ 3)) *
      saddleSourceSecondBranchLocalFrequency ε ^ 2

private theorem eventually_saddleSource_secondBranch_pointwise_gaussian_plus_outer :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            saddleGaussianTailWeight T *
                Real.exp
                  (-saddleSourceContourDamping
                    ε ℓ (1 + δ) T) ≤
              saddleGaussianTailWeight T *
                  Real.exp
                    (-saddleSourceSecondBranchGaussianRate
                      ε ℓ δ * T ^ 2) +
                Real.exp
                    (-saddleSourceSecondBranchOuterBarrier
                      ε ℓ δ) *
                  (saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceSecondBranchGammaGaussianRate
                        ℓ δ * T ^ 2) +
                    saddleGaussianTailWeight T *
                      Real.exp
                        (-saddleSourceSecondBranchGammaLinearRate
                          ℓ * |T|)) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleSourceContourDamping_secondBranch_local_coercivity,
      eventually_upperSaddleDamping_gamma_add_shell]
    with ε hε hlocal hdom
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  let t₀ : ℝ := saddleSourceSecondBranchLocalFrequency ε
  let a : ℝ := ℓ / (8 * Real.exp 1)
  let η : ℝ := 2 + δ
  have hδ0 : 0 ≤ δ := by linarith
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  have ht₀ : 0 < t₀ := by
    try dsimp [t₀, saddleSourceSecondBranchLocalFrequency]
    positivity
  have ht₀one : t₀ ≤ 1 := by
    try dsimp [t₀, saddleSourceSecondBranchLocalFrequency]
    apply (div_le_iff₀
      (show (0 : ℝ) < 2 * ((ε⁻¹ ^ 3) + 1) by
        positivity)).2
    linarith
  have hw : 0 ≤ saddleGaussianTailWeight T :=
    saddleGaussianTailWeight_nonneg T
  by_cases hinside : |T| ≤ t₀
  · have hquadratic := hlocal ℓ hℓ δ hδ T
      (by simpa only [one_div, mul_inv_rev, saddleSourceSecondBranchLocalFrequency,
        t₀] using! hinside)
    have hlocalexp :
        Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T) ≤
          Real.exp
            (-saddleSourceSecondBranchGaussianRate
              ε ℓ δ * T ^ 2) := by
      apply Real.exp_le_exp.mpr
      unfold saddleSourceSecondBranchGaussianRate
      linarith
    have hfirst := mul_le_mul_of_nonneg_left hlocalexp hw
    have houter : 0 ≤
        Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
          (saddleGaussianTailWeight T *
            Real.exp
              (-saddleSourceSecondBranchGammaGaussianRate
                ℓ δ * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp
                (-saddleSourceSecondBranchGammaLinearRate
                  ℓ * |T|)) := by
      positivity
    linarith
  · have houtside : t₀ ≤ |T| :=
      le_of_not_ge hinside
    have hsquare : t₀ ^ 2 ≤ T ^ 2 := by
      have h := pow_le_pow_left₀ ht₀.le houtside 2
      simpa only [ge_iff_le, sq_abs] using! h
    have hone : t₀ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [sq_nonneg (1 - t₀)]
    have hminimum : t₀ ^ 2 ≤ min (T ^ 2) 1 :=
      le_min hsquare hone
    have hshell := positiveShellDamping_lower_bound
      (ε := ε) (ℓ := ℓ) (δ := δ) (T := T)
        hε hℓ.le hδ0
    have hbarrier :
        saddleSourceSecondBranchOuterBarrier ε ℓ δ ≤
          (99 / 100 : ℝ) *
            positiveShellDamping ε ℓ δ T := by
      calc
        saddleSourceSecondBranchOuterBarrier ε ℓ δ =
            (99 / 100 : ℝ) *
              ((ℓ / 50) * shellWeight ε *
                Real.exp (δ * (ε⁻¹ ^ 3)) *
                  t₀ ^ 2) := by
              try dsimp [saddleSourceSecondBranchOuterBarrier, t₀]
              ring
        _ ≤ (99 / 100 : ℝ) *
              ((ℓ / 50) * shellWeight ε *
                Real.exp (δ * (ε⁻¹ ^ 3)) *
                  min (T ^ 2) 1) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hminimum
                (by positivity [shellWeight_pos ε])
        _ ≤ (99 / 100 : ℝ) *
            positiveShellDamping ε ℓ δ T := by
              exact mul_le_mul_of_nonneg_left hshell
                (by norm_num)
    have hgamma := upperGammaDamping_lower_bound
      hℓ hη T
    have hcombined :
        saddleSourceSecondBranchOuterBarrier ε ℓ δ +
            a * min (T ^ 2 / η) |T| ≤
          saddleSourceContourDamping ε ℓ (1 + δ) T := by
      rw [saddleSourceContourDamping_eq_secondBranch]
      have hfull := hdom ℓ hℓ δ hδ T
      try dsimp [a, η] at hgamma ⊢
      linarith
    have hmin := saddle_exp_neg_mul_min_le_add
      (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
    have hexp :
        Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T) ≤
          Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (Real.exp
              (-saddleSourceSecondBranchGammaGaussianRate
                ℓ δ * T ^ 2) +
              Real.exp
                (-saddleSourceSecondBranchGammaLinearRate
                  ℓ * |T|)) := by
      calc
        Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T) ≤
          Real.exp
            (-(saddleSourceSecondBranchOuterBarrier ε ℓ δ +
              a * min (T ^ 2 / η) |T|)) := by
            apply Real.exp_le_exp.mpr
            linarith
        _ = Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            Real.exp
              (-a * min (T ^ 2 / η) |T|) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (Real.exp (-a * (T ^ 2 / η)) +
              Real.exp (-a * |T|)) := by
            gcongr
        _ = Real.exp
              (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            (Real.exp
              (-saddleSourceSecondBranchGammaGaussianRate
                ℓ δ * T ^ 2) +
              Real.exp
                (-saddleSourceSecondBranchGammaLinearRate
                  ℓ * |T|)) := by
            congr 2
            unfold saddleSourceSecondBranchGammaGaussianRate
            try dsimp [a, η]
            congr 1
            ring
    have hweighted := mul_le_mul_of_nonneg_left hexp hw
    have hfirst : 0 ≤
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceSecondBranchGaussianRate
              ε ℓ δ * T ^ 2) := by
      positivity
    linarith

private theorem eventually_saddleSource_secondBranch_weighted_tail_explicit :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ R : ℝ, 0 ≤ R →
            6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ →
              (∫ T : ℝ in saddleGaussianTailSet R,
                saddleGaussianTailWeight T *
                  Real.exp
                    (-saddleSourceContourDamping
                      ε ℓ (1 + δ) T)) ≤
                2 * Real.exp
                    (-(saddleSourceSecondBranchGaussianRate
                      ε ℓ δ / 4) * R ^ 2) *
                  Real.sqrt
                    (Real.pi /
                      (saddleSourceSecondBranchGaussianRate
                        ε ℓ δ / 4)) +
                Real.exp
                    (-saddleSourceSecondBranchOuterBarrier
                      ε ℓ δ) *
                  (2 * max (1 : ℝ)
                    ((Real.sqrt
                      (saddleSourceSecondBranchGammaGaussianRate
                        ℓ δ / 6) ^ 3)⁻¹) *
                      Real.sqrt
                        (Real.pi /
                          (saddleSourceSecondBranchGammaGaussianRate
                            ℓ δ / 2)) +
                    2 * max (1 : ℝ)
                      (((saddleSourceSecondBranchGammaLinearRate
                        ℓ / 6) ^ 3)⁻¹) *
                        (2 /
                          (saddleSourceSecondBranchGammaLinearRate
                            ℓ / 2))) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleSource_secondBranch_weighted_integrable,
      eventually_saddleSource_secondBranch_pointwise_gaussian_plus_outer,
      eventually_saddleSourceGaussianVariance_secondBranch_pos]
    with ε hε hsource hpoint hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ R hR hk
  let k : ℝ := saddleSourceSecondBranchGaussianRate ε ℓ δ
  let q : ℝ := saddleSourceSecondBranchGammaGaussianRate ℓ δ
  let a : ℝ := saddleSourceSecondBranchGammaLinearRate ℓ
  let b : ℝ := saddleSourceSecondBranchOuterBarrier ε ℓ δ
  have hδ0 : 0 ≤ δ := by linarith
  have hη : 0 < 2 + δ := by linarith
  have hV := hvariance ℓ hℓ δ hδ
  have hkpos : 0 < k := by
    try dsimp [k, saddleSourceSecondBranchGaussianRate]
    positivity
  have hq : 0 < q := by
    try dsimp [q, saddleSourceSecondBranchGammaGaussianRate]
    positivity
  have ha : 0 < a := by
    try dsimp [a, saddleSourceSecondBranchGammaLinearRate]
    positivity
  have hactual := hsource ℓ hℓ δ hδ
  have hlocal :=
    saddleGaussianTailWeight_mul_gaussian_integrable hkpos
  have hgamma :=
    saddleGaussianTailWeight_mul_gaussian_integrable hq
  have hlinear :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have houter : Integrable
      (fun T : ℝ =>
        Real.exp (-b) *
          (saddleGaussianTailWeight T *
            Real.exp (-q * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|))) :=
    (hgamma.add hlinear).const_mul (Real.exp (-b))
  have hmajor : Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
            Real.exp (-k * T ^ 2) +
          Real.exp (-b) *
            (saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2) +
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|))) :=
    hlocal.add houter
  have hcompare := MeasureTheory.setIntegral_mono_on
    hactual.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R)
    (fun T _ => by
      simpa only [saddleSourceContourDamping_eq_firstBranch, neg_mul, k, b, q, a] using!
        hpoint ℓ hℓ δ hδ T)
  have hgaussianTail := saddleGaussian_cubic_tail_integral_le
    (k := k) (R := R) (by simpa only [k] using! hk) hR
  have hgammanonnegative :
      0 ≤ᶠ[ae (volume : Measure ℝ)]
        (fun T : ℝ =>
          saddleGaussianTailWeight T *
            Real.exp (-q * T ^ 2)) :=
    Filter.Eventually.of_forall
      (fun T => mul_nonneg
        (saddleGaussianTailWeight_nonneg T)
        (Real.exp_pos _).le)
  have hlinearnonnegative :
      0 ≤ᶠ[ae (volume : Measure ℝ)]
        (fun T : ℝ =>
          saddleGaussianTailWeight T *
            Real.exp (-a * |T|)) :=
    Filter.Eventually.of_forall
      (fun T => mul_nonneg
        (saddleGaussianTailWeight_nonneg T)
        (Real.exp_pos _).le)
  have hgammaTail := MeasureTheory.setIntegral_le_integral
    (s := saddleGaussianTailSet R)
    hgamma hgammanonnegative
  have hlinearTail := MeasureTheory.setIntegral_le_integral
    (s := saddleGaussianTailSet R)
    hlinear hlinearnonnegative
  have hgammaFull :=
    saddleGaussian_weighted_integral_le_rescaled hq
  have hlinearFull :=
    saddleExponential_weighted_integral_le_rescaled ha
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        (saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2) +
          Real.exp (-b) *
            (saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2) +
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|))) := hcompare
    _ = (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-k * T ^ 2)) +
        Real.exp (-b) *
          ((∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2)) +
            ∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|)) := by
      rw [MeasureTheory.integral_add
        hlocal.integrableOn houter.integrableOn,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add
          hgamma.integrableOn hlinear.integrableOn]
    _ ≤ 2 * Real.exp (-(k / 4) * R ^ 2) *
          Real.sqrt (Real.pi / (k / 4)) +
        Real.exp (-b) *
          ((∫ T : ℝ,
            saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2)) +
            ∫ T : ℝ,
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|)) := by
      gcongr
    _ ≤ 2 * Real.exp (-(k / 4) * R ^ 2) *
          Real.sqrt (Real.pi / (k / 4)) +
        Real.exp (-b) *
          (2 * max (1 : ℝ)
            ((Real.sqrt (q / 6) ^ 3)⁻¹) *
              Real.sqrt (Real.pi / (q / 2)) +
            2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
              (2 / (a / 2))) := by
      gcongr
    _ = _ := by rfl

private theorem saddleSourceSecondBranch_normalizedGaussian_prefactor
    {ε ℓ δ : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ (1 + δ)) :
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
      Real.sqrt
        (Real.pi /
          (saddleSourceSecondBranchGaussianRate ε ℓ δ / 4)) =
      Real.sqrt (400 * Real.exp 1 * Real.pi) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  have hLV : 0 < ℓ * V := mul_pos hℓ hV
  have hVne : V ≠ 0 := by
    exact hV.ne'
  rw [← Real.sqrt_mul hLV.le]
  congr 1
  unfold saddleSourceSecondBranchGaussianRate
  change
    (ℓ * V) *
        (Real.pi / (((ℓ / (100 * Real.exp 1)) * V) / 4)) =
      400 * Real.exp 1 * Real.pi
  field_simp [hℓ.ne', hVne, (Real.exp_pos 1).ne']; ring

private theorem saddleSourceSecondBranch_normalizedGaussian_exponent
    {ε ℓ δ z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ (1 + δ)) :
    (saddleSourceSecondBranchGaussianRate ε ℓ δ / 4) *
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))) ^ 2 =
      z ^ 2 / (400 * Real.exp 1) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  have hLV : 0 < ℓ * V := mul_pos hℓ hV
  have hVne : V ≠ 0 := by
    exact hV.ne'
  unfold saddleSourceSecondBranchGaussianRate
  change
    (((ℓ / (100 * Real.exp 1)) * V) / 4) *
        (z / Real.sqrt (ℓ * V)) ^ 2 =
      z ^ 2 / (400 * Real.exp 1)
  rw [div_pow, Real.sq_sqrt hLV.le]
  field_simp [hℓ.ne', hVne, (Real.exp_pos 1).ne']; ring

private theorem eventually_saddleSource_secondBranch_normalized_tail_bound :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ z : ℝ, 0 ≤ z →
            6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ →
              Real.sqrt
                  (ℓ * saddleSourceGaussianVariance
                    ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (z / Real.sqrt
                      (ℓ * saddleSourceGaussianVariance
                        ε ℓ (1 + δ))),
                  saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceContourDamping
                        ε ℓ (1 + δ) T)) ≤
                2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
                  Real.exp
                    (-(z ^ 2 / (400 * Real.exp 1))) +
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance
                      ε ℓ (1 + δ)) *
                  Real.exp
                    (-saddleSourceSecondBranchOuterBarrier
                      ε ℓ δ) *
                    (2 * max (1 : ℝ)
                      ((Real.sqrt
                        (saddleSourceSecondBranchGammaGaussianRate
                          ℓ δ / 6) ^ 3)⁻¹) *
                        Real.sqrt
                          (Real.pi /
                            (saddleSourceSecondBranchGammaGaussianRate
                              ℓ δ / 2)) +
                      2 * max (1 : ℝ)
                        (((saddleSourceSecondBranchGammaLinearRate
                          ℓ / 6) ^ 3)⁻¹) *
                          (2 /
                            (saddleSourceSecondBranchGammaLinearRate
                              ℓ / 2))) := by
  filter_upwards
    [eventually_saddleSource_secondBranch_weighted_tail_explicit,
      eventually_saddleSourceGaussianVariance_secondBranch_pos]
    with ε htail hvariance
  intro ℓ hℓ δ hδ z hz hk
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  let R : ℝ := z / Real.sqrt (ℓ * V)
  have hV : 0 < V := hvariance ℓ hℓ δ hδ
  have hR : 0 ≤ R := by
    try dsimp [R]
    positivity
  have hsource := htail ℓ hℓ δ hδ R hR hk
  have hpref := saddleSourceSecondBranch_normalizedGaussian_prefactor
    hℓ hV
  have hexponent :=
    saddleSourceSecondBranch_normalizedGaussian_exponent
      (z := z) hℓ hV
  have hs : 0 ≤ Real.sqrt (ℓ * V) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
      (∫ T : ℝ in saddleGaussianTailSet
          (z / Real.sqrt
            (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))),
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceContourDamping ε ℓ (1 + δ) T)) ≤
      Real.sqrt (ℓ * V) *
        (2 * Real.exp
            (-(saddleSourceSecondBranchGaussianRate
              ε ℓ δ / 4) * R ^ 2) *
              Real.sqrt
                (Real.pi /
                  (saddleSourceSecondBranchGaussianRate
                    ε ℓ δ / 4)) +
          Real.exp
              (-saddleSourceSecondBranchOuterBarrier
                ε ℓ δ) *
            (2 * max (1 : ℝ)
              ((Real.sqrt
                (saddleSourceSecondBranchGammaGaussianRate
                  ℓ δ / 6) ^ 3)⁻¹) *
                Real.sqrt
                  (Real.pi /
                    (saddleSourceSecondBranchGammaGaussianRate
                      ℓ δ / 2)) +
              2 * max (1 : ℝ)
                (((saddleSourceSecondBranchGammaLinearRate
                  ℓ / 6) ^ 3)⁻¹) *
                  (2 /
                    (saddleSourceSecondBranchGammaLinearRate
                      ℓ / 2)))) := by
        change Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp
                (-saddleSourceContourDamping
                  ε ℓ (1 + δ) T)) ≤ _
        exact mul_le_mul_of_nonneg_left hsource hs
    _ = _ := by
      have hexponent' :
          (saddleSourceSecondBranchGaussianRate
            ε ℓ δ / 4) *
            (z / Real.sqrt (ℓ * V)) ^ 2 =
              z ^ 2 / (400 * Real.exp 1) := by
        simpa only [V] using! hexponent
      have hnegative :
          -(saddleSourceSecondBranchGaussianRate
            ε ℓ δ / 4) *
            (z / Real.sqrt (ℓ * V)) ^ 2 =
              -(z ^ 2 / (400 * Real.exp 1)) := by
        linarith
      have hpref' :
          Real.sqrt (ℓ * V) *
            Real.sqrt
              (Real.pi /
                (saddleSourceSecondBranchGaussianRate
                  ε ℓ δ / 4)) =
            Real.sqrt (400 * Real.exp 1 * Real.pi) := by
        simpa only [V] using! hpref
      try dsimp [R]
      rw [hnegative]
      have hscaled := congrArg
        (fun x : ℝ =>
          2 * Real.exp
            (-(z ^ 2 / (400 * Real.exp 1))) * x)
        hpref'
      linarith

private theorem saddle_sqrt_le_one_add
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ 1 + x := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · linarith [sq_nonneg x]

private theorem saddle_inverse_sqrt_cube_le
    {q : ℝ} (hq : 0 < q) :
    (Real.sqrt (q / 6) ^ 3)⁻¹ ≤
      1 + (6 / q) ^ 3 := by
  let s : ℝ := Real.sqrt (q / 6)
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have hsquare : s ^ 2 = q / 6 := by
    try dsimp [s]
    rw [Real.sq_sqrt (by positivity)]
  have hcubed : (s ^ 2) ^ 3 = (q / 6) ^ 3 :=
    congrArg (fun x : ℝ => x ^ 3) hsquare
  have hidentity :
      ((s ^ 3)⁻¹) ^ 2 = (6 / q) ^ 3 := by
    field_simp [hq.ne', hs.ne']
    linarith [hcubed]
  have hnonnegative : 0 ≤ (s ^ 3)⁻¹ := by
    positivity
  change (s ^ 3)⁻¹ ≤ 1 + (6 / q) ^ 3
  rw [← hidentity]
  linarith [sq_nonneg ((s ^ 3)⁻¹ - (1 / 2 : ℝ))]

private theorem saddleSecondBranch_gammaWeightedCoefficient_le
    {q η C : ℝ}
    (hq : 0 < q)
    (hη : 1 ≤ η)
    (hC : 0 < C)
    (hrate : 1 / q ≤ C * η) :
    2 * max (1 : ℝ)
        ((Real.sqrt (q / 6) ^ 3)⁻¹) *
      Real.sqrt (Real.pi / (q / 2)) ≤
        (2 * (1 + (6 * C) ^ 3) *
          (1 + 2 * Real.pi * C)) * η ^ 4 := by
  have hη0 : 0 ≤ η := by linarith
  have hηthree : 1 ≤ η ^ 3 := by
    simpa only [one_pow] using!
      (pow_le_pow_left₀
        (show (0 : ℝ) ≤ 1 by norm_num) hη 3)
  have hinverse := saddle_inverse_sqrt_cube_le hq
  have hmax :
      max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) ≤
        1 + (6 / q) ^ 3 := by
    apply max_le
    · have : 0 ≤ (6 / q) ^ 3 := by positivity
      linarith
    · exact hinverse
  have hqscaled : 6 / q ≤ 6 * C * η := by
    calc
      6 / q = 6 * (1 / q) := by ring
      _ ≤ 6 * (C * η) := by gcongr
      _ = 6 * C * η := by ring
  have hmaxpoly :
      max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) ≤
        (1 + (6 * C) ^ 3) * η ^ 3 := by
    calc
      max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) ≤
          1 + (6 / q) ^ 3 := hmax
      _ ≤ 1 + (6 * C * η) ^ 3 := by
        gcongr
      _ ≤ (1 + (6 * C) ^ 3) * η ^ 3 := by
        linarith [mul_nonneg
          (show 0 ≤ (6 * C) ^ 3 by positivity)
          (show 0 ≤ η ^ 3 - 1 by linarith)]
  have hpiscaled :
      Real.pi / (q / 2) ≤
        2 * Real.pi * C * η := by
    calc
      Real.pi / (q / 2) =
          (2 * Real.pi) * (1 / q) := by
        field_simp [hq.ne']
      _ ≤ (2 * Real.pi) * (C * η) := by
        gcongr
      _ = 2 * Real.pi * C * η := by ring
  have hsqrt :
      Real.sqrt (Real.pi / (q / 2)) ≤
        (1 + 2 * Real.pi * C) * η := by
    calc
      Real.sqrt (Real.pi / (q / 2)) ≤
          1 + Real.pi / (q / 2) :=
        saddle_sqrt_le_one_add (by positivity)
      _ ≤ 1 + 2 * Real.pi * C * η := by
        linarith
      _ ≤ (1 + 2 * Real.pi * C) * η := by
        linarith
  calc
    2 * max (1 : ℝ)
        ((Real.sqrt (q / 6) ^ 3)⁻¹) *
      Real.sqrt (Real.pi / (q / 2)) ≤
      2 * ((1 + (6 * C) ^ 3) * η ^ 3) *
        ((1 + 2 * Real.pi * C) * η) := by
      gcongr
    _ = (2 * (1 + (6 * C) ^ 3) *
          (1 + 2 * Real.pi * C)) * η ^ 4 := by
      ring

private theorem saddleSecondBranch_linearWeightedCoefficient_le
    {a η C : ℝ}
    (ha : 0 < a)
    (hη : 1 ≤ η)
    (hC : 0 < C)
    (hrate : 1 / a ≤ C) :
    2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
        (2 / (a / 2)) ≤
      (8 * C * (1 + (6 * C) ^ 3)) * η ^ 4 := by
  have hηfour : 1 ≤ η ^ 4 := by
    simpa only [one_pow] using!
      (pow_le_pow_left₀
        (show (0 : ℝ) ≤ 1 by norm_num) hη 4)
  have hidentity :
      ((a / 6) ^ 3)⁻¹ = (6 / a) ^ 3 := by
    field_simp [ha.ne']
  have hbase : 6 / a ≤ 6 * C := by
    calc
      6 / a = 6 * (1 / a) := by ring
      _ ≤ 6 * C := by gcongr
  have hmax :
      max (1 : ℝ) (((a / 6) ^ 3)⁻¹) ≤
        1 + (6 * C) ^ 3 := by
    rw [hidentity]
    apply max_le
    · have : 0 ≤ (6 * C) ^ 3 := by positivity
      linarith
    · have hcubes : (6 / a) ^ 3 ≤ (6 * C) ^ 3 := by
        gcongr
      linarith
  have hlinear : 2 / (a / 2) ≤ 4 * C := by
    calc
      2 / (a / 2) = 4 * (1 / a) := by
        field_simp [ha.ne']; ring
      _ ≤ 4 * C := by gcongr
  calc
    2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
        (2 / (a / 2)) ≤
      2 * (1 + (6 * C) ^ 3) * (4 * C) := by
        gcongr
    _ ≤ (8 * C * (1 + (6 * C) ^ 3)) * η ^ 4 := by
      have hcoefficient :
          0 ≤ 8 * C * (1 + (6 * C) ^ 3) := by
        positivity
      linarith [mul_le_mul_of_nonneg_left
        hηfour hcoefficient]

private noncomputable def saddleSourceSecondBranchMomentCoefficient : ℝ :=
  let C : ℝ := 8 * Real.exp 1
  2 * (1 + (6 * C) ^ 3) *
      (1 + 2 * Real.pi * C) +
    8 * C * (1 + (6 * C) ^ 3)

private theorem saddleSourceSecondBranchMomentCoefficient_pos :
    0 < saddleSourceSecondBranchMomentCoefficient := by
  unfold saddleSourceSecondBranchMomentCoefficient
  positivity

private theorem saddleSourceSecondBranch_outerMoment_le
    {ℓ δ : ℝ} (hℓ : 1 ≤ ℓ) (hδ : 0 ≤ δ) :
    2 * max (1 : ℝ)
        ((Real.sqrt
          (saddleSourceSecondBranchGammaGaussianRate
            ℓ δ / 6) ^ 3)⁻¹) *
          Real.sqrt
            (Real.pi /
              (saddleSourceSecondBranchGammaGaussianRate
                ℓ δ / 2)) +
      2 * max (1 : ℝ)
        (((saddleSourceSecondBranchGammaLinearRate
          ℓ / 6) ^ 3)⁻¹) *
          (2 /
            (saddleSourceSecondBranchGammaLinearRate
              ℓ / 2)) ≤
        saddleSourceSecondBranchMomentCoefficient *
          (2 + δ) ^ 4 := by
  let C : ℝ := 8 * Real.exp 1
  let η : ℝ := 2 + δ
  let q : ℝ := saddleSourceSecondBranchGammaGaussianRate ℓ δ
  let a : ℝ := saddleSourceSecondBranchGammaLinearRate ℓ
  have hℓpositive : 0 < ℓ := by linarith
  have hη : 1 ≤ η := by
    try dsimp [η]
    linarith
  have hηpositive : 0 < η := by linarith
  have hC : 0 < C := by
    try dsimp [C]
    positivity
  have hq : 0 < q := by
    try dsimp [q, saddleSourceSecondBranchGammaGaussianRate]
    positivity
  have ha : 0 < a := by
    try dsimp [a, saddleSourceSecondBranchGammaLinearRate]
    positivity
  have hqrate : 1 / q ≤ C * η := by
    calc
      1 / q = (C * η) / ℓ := by
        try dsimp [q, C, η,
          saddleSourceSecondBranchGammaGaussianRate]
        field_simp [hℓpositive.ne',
          (Real.exp_pos 1).ne', hηpositive.ne']
      _ ≤ C * η := by
        apply (div_le_iff₀ hℓpositive).2
        linarith [mul_nonneg
          (mul_nonneg hC.le hηpositive.le)
          (show 0 ≤ ℓ - 1 by linarith)]
  have harate : 1 / a ≤ C := by
    calc
      1 / a = C / ℓ := by
        try dsimp [a, C,
          saddleSourceSecondBranchGammaLinearRate]
        field_simp [hℓpositive.ne',
          (Real.exp_pos 1).ne']
      _ ≤ C := by
        apply (div_le_iff₀ hℓpositive).2
        linarith [mul_nonneg hC.le
          (show 0 ≤ ℓ - 1 by linarith)]
  have hgamma := saddleSecondBranch_gammaWeightedCoefficient_le
    hq hη hC hqrate
  have hlinear := saddleSecondBranch_linearWeightedCoefficient_le
    ha hη hC harate
  change
    2 * max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) *
          Real.sqrt (Real.pi / (q / 2)) +
      2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
          (2 / (a / 2)) ≤
        saddleSourceSecondBranchMomentCoefficient * η ^ 4
  unfold saddleSourceSecondBranchMomentCoefficient
  change
    2 * max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) *
          Real.sqrt (Real.pi / (q / 2)) +
      2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
          (2 / (a / 2)) ≤
      (2 * (1 + (6 * C) ^ 3) *
          (1 + 2 * Real.pi * C) +
        8 * C * (1 + (6 * C) ^ 3)) * η ^ 4
  linarith

private noncomputable def saddleSourceSecondBranchVarianceCoefficient (ε : ℝ) : ℝ :=
  2 + ((ε⁻¹ ^ 3) + 1) ^ 2 * shellWeight ε

private theorem saddleSourceSecondBranchVarianceCoefficient_pos
    (ε : ℝ) :
    0 < saddleSourceSecondBranchVarianceCoefficient ε := by
  unfold saddleSourceSecondBranchVarianceCoefficient
  positivity [shellWeight_pos ε]

private theorem eventually_saddleSourceGaussianVariance_secondBranch_upper :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          saddleSourceGaussianVariance ε ℓ (1 + δ) ≤
            saddleSourceSecondBranchVarianceCoefficient ε *
              Real.exp
                (((ε⁻¹ ^ 3) + 1) * δ) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleVariance_bounds]
    with ε hε hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hℓpositive : 0 < ℓ := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  let η : ℝ := 2 + δ
  have hηtwo : 2 ≤ η := by
    try dsimp [η]
    linarith
  have hη : 0 < η := by linarith
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  have hexp : 1 ≤
      Real.exp (((ε⁻¹ ^ 3) + 1) * δ) := by
    apply (Real.one_le_exp_iff).2
    positivity
  have hfirst : 1 / (2 * η) ≤ (1 : ℝ) := by
    apply (div_le_iff₀
      (show 0 < 2 * η by positivity)).2
    linarith
  have hden : 0 < ℓ * η ^ 2 := by positivity
  have hsecond : 1 / (ℓ * η ^ 2) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hden).2
    have hηsquare : 1 ≤ η ^ 2 := by
      linarith [sq_nonneg (η - 1)]
    have hscaled := mul_le_mul_of_nonneg_right
      hℓ (sq_nonneg η)
    linarith
  have hshell :=
    (upperPositiveShellVariance_bounds hε hδ0).2
  have hfull := (hvariance ℓ hℓpositive δ hδ).2
  have hsource :
      saddleSourceGaussianVariance ε ℓ (1 + δ) ≤
        1 / (2 * η) + 1 / (ℓ * η ^ 2) +
          upperPositiveShellVariance ε δ := by
    simpa only [saddleSourceGaussianVariance, add_sub_cancel_left, one_div,
      mul_inv_rev] using! hfull
  have hshell' :
      upperPositiveShellVariance ε δ ≤
        ((ε⁻¹ ^ 3) + 1) ^ 2 *
          shellWeight ε *
            Real.exp (((ε⁻¹ ^ 3) + 1) * δ) := by
    convert! hshell using 1; ring_nf
  unfold saddleSourceSecondBranchVarianceCoefficient
  linarith

private theorem eventually_saddleSource_secondBranch_sqrtVariance_le :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          Real.sqrt
              (ℓ * saddleSourceGaussianVariance
                ε ℓ (1 + δ)) ≤
            Real.sqrt
                (saddleSourceSecondBranchVarianceCoefficient ε) *
              Real.sqrt ℓ *
                Real.exp
                  ((((ε⁻¹ ^ 3) + 1) / 2) * δ) := by
  filter_upwards
    [eventually_saddleSourceGaussianVariance_secondBranch_upper]
    with ε hupper
  intro ℓ hℓ δ hδ
  let C : ℝ := saddleSourceSecondBranchVarianceCoefficient ε
  have hC : 0 < C :=
    saddleSourceSecondBranchVarianceCoefficient_pos ε
  have hℓpositive : 0 < ℓ := by linarith
  have hsource := hupper ℓ hℓ δ hδ
  have hscaled := mul_le_mul_of_nonneg_left
    hsource hℓpositive.le
  calc
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) ≤
      Real.sqrt
        (ℓ * (C * Real.exp
          (((ε⁻¹ ^ 3) + 1) * δ))) := by
        apply Real.sqrt_le_sqrt
        simpa only [C] using! hscaled
    _ = Real.sqrt C * Real.sqrt ℓ *
        Real.exp
          ((((ε⁻¹ ^ 3) + 1) / 2) * δ) := by
      rw [Real.sqrt_mul hℓpositive.le,
        Real.sqrt_mul hC.le, ← Real.exp_half]
      have hargument :
          (((ε⁻¹ ^ 3) + 1) * δ) / 2 =
            (((ε⁻¹ ^ 3) + 1) / 2) * δ := by
        ring
      rw [hargument]
      ring

/-- The local-tail majorant for the second saddle branch vanishes asymptotically. -/
public
theorem tendsto_saddleSourceSecondBranchLocalTailMajorant :
    Tendsto
      (fun ℓ : ℝ =>
        2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
          Real.exp
            (-(ℓ ^ (1 / 6 : ℝ) /
              (400 * Real.exp 1))))
      atTop (𝓝 (0 : ℝ)) := by
  have hpower : Tendsto
      (fun ℓ : ℝ => ℓ ^ (1 / 6 : ℝ))
      atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hnegative : Tendsto
      (fun ℓ : ℝ =>
        (-(1 / (400 * Real.exp 1))) *
          ℓ ^ (1 / 6 : ℝ))
      atTop atBot :=
    hpower.const_mul_atTop_of_neg
      (neg_lt_zero.mpr
        (by positivity : (0 : ℝ) < 1 / (400 * Real.exp 1)))
  have hexp := Real.tendsto_exp_atBot.comp hnegative
  have hscaled := hexp.const_mul
    (2 * Real.sqrt (400 * Real.exp 1 * Real.pi))
  convert! hscaled using 1
  · funext ℓ
    congr 2
    ring
  · simp only [mul_zero]

private theorem eventually_saddleSource_secondBranch_uniform_tail :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            Real.sqrt
                (ℓ * saddleSourceGaussianVariance
                  ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (ℓ ^ (1 / 12 : ℝ) /
                    Real.sqrt
                      (ℓ * saddleSourceGaussianVariance
                        ε ℓ (1 + δ))),
                saddleGaussianTailWeight T *
                  Real.exp
                    (-saddleSourceContourDamping
                      ε ℓ (1 + δ) T)) < κ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleSource_secondBranch_normalized_tail_bound,
      eventually_saddleSource_secondBranch_sqrtVariance_le,
      eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε htail hsqrt hfloor
  change 0 < ε at hε
  intro κ hκ
  let B : ℝ := (ε⁻¹ ^ 3)
  let Q : ℝ := shellWeight ε
  let t₀ : ℝ := saddleSourceSecondBranchLocalFrequency ε
  let c : ℝ := (99 / 5000 : ℝ) * t₀ ^ 2
  let V₀ : ℝ := saddleSourceSecondBranchVarianceFloor ε
  let C : ℝ := saddleSourceSecondBranchVarianceCoefficient ε
  let K : ℝ :=
    Real.sqrt C * saddleSourceSecondBranchMomentCoefficient
  have hB : 0 < B := by
    try dsimp [B]
    positivity
  have hQ : 0 < Q := by
    try dsimp [Q]
    exact shellWeight_pos ε
  have ht₀ : 0 < t₀ := by
    try dsimp [t₀, saddleSourceSecondBranchLocalFrequency, B]
    positivity
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hV₀ : 0 < V₀ := by
    try dsimp [V₀]
    exact saddleSourceSecondBranchVarianceFloor_pos hε
  have hC : 0 < C := by
    try dsimp [C]
    exact saddleSourceSecondBranchVarianceCoefficient_pos ε
  have hK : 0 < K := by
    try dsimp [K]
    exact mul_pos (Real.sqrt_pos.2 hC)
      saddleSourceSecondBranchMomentCoefficient_pos
  have hhalf : 0 < κ / 2 := by positivity
  have houter :=
    eventually_saddleGaussianOuterPhi_uniform_polynomial
      hB hQ hc (by positivity : 0 ≤ ε / 2)
        hK.le (κ / 2) hhalf
  have hlocal :=
    tendsto_saddleSourceSecondBranchLocalTailMajorant.eventually
      (Iio_mem_nhds hhalf)
  filter_upwards
    [eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop
        ((600 * Real.exp 1) / V₀),
      hlocal, houter]
    with ℓ hℓ hone hlocalℓ houterℓ
  intro δ hδ
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  let z : ℝ := ℓ ^ (1 / 12 : ℝ)
  let η : ℝ := 2 + δ
  have hℓpositive : 0 < ℓ := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hη : 1 ≤ η := by
    try dsimp [η]
    linarith
  have hVfloor : V₀ ≤ V := by
    try dsimp [V₀, V]
    exact hfloor ℓ hℓpositive δ hδ
  have hV : 0 < V := hV₀.trans_le hVfloor
  have hz : 0 ≤ z := by
    try dsimp [z]
    positivity
  have hscale : 600 * Real.exp 1 ≤ ℓ * V₀ := by
    have h := (div_le_iff₀ hV₀).mp hone
    linarith
  have hfullscale : 600 * Real.exp 1 ≤ ℓ * V := by
    have h := mul_le_mul_of_nonneg_left
      hVfloor hℓpositive.le
    linarith
  have hk :
      6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ := by
    unfold saddleSourceSecondBranchGaussianRate
    change 6 ≤ (ℓ / (100 * Real.exp 1)) * V
    have hden : (0 : ℝ) < 100 * Real.exp 1 := by
      positivity
    have hgoal :
        (6 : ℝ) ≤ (ℓ * V) / (100 * Real.exp 1) := by
      apply (le_div_iff₀ hden).2
      linarith
    convert! hgoal using 1; ring
  have hsource := htail ℓ hℓpositive δ hδ z hz hk
  have hpower : z ^ 2 = ℓ ^ (1 / 6 : ℝ) := by
    try dsimp [z]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul hℓpositive.le]
    congr 1
    norm_num
  have hlocalterm :
      2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
        Real.exp
          (-(z ^ 2 / (400 * Real.exp 1))) < κ / 2 := by
    rw [hpower]
    exact hlocalℓ
  have hsqrtsource :
      Real.sqrt (ℓ * V) ≤
        Real.sqrt C * Real.sqrt ℓ *
          Real.exp (((B + 1) / 2) * δ) := by
    simpa only  using! hsqrt ℓ hℓ δ hδ
  have hmoment :=
    saddleSourceSecondBranch_outerMoment_le hℓ hδ0
  let M : ℝ :=
    2 * max (1 : ℝ)
        ((Real.sqrt (saddleSourceSecondBranchGammaGaussianRate ℓ δ / 6) ^ 3)⁻¹) *
          Real.sqrt (Real.pi / (saddleSourceSecondBranchGammaGaussianRate ℓ δ / 2)) +
      2 * max (1 : ℝ)
        (((saddleSourceSecondBranchGammaLinearRate ℓ / 6) ^ 3)⁻¹) *
          (2 / (saddleSourceSecondBranchGammaLinearRate ℓ / 2))
  have hmoment' : M ≤ saddleSourceSecondBranchMomentCoefficient * η ^ 4 := by
    simpa only [M, Nat.ofNat_nonneg, Real.sqrt_div'] using! hmoment
  have hqpositive :
      0 < saddleSourceSecondBranchGammaGaussianRate ℓ δ := by
    unfold saddleSourceSecondBranchGammaGaussianRate
    positivity
  have hapositive :
      0 < saddleSourceSecondBranchGammaLinearRate ℓ := by
    unfold saddleSourceSecondBranchGammaLinearRate
    positivity
  have hmomentnonnegative : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hbarrier :
      saddleSourceSecondBranchOuterBarrier ε ℓ δ =
        c * ℓ * Q * Real.exp (B * δ) := by
    try dsimp [saddleSourceSecondBranchOuterBarrier,
      c, Q, B, t₀]
    ring_nf
  have houterterm :
      Real.sqrt (ℓ * V) *
          Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            M < κ / 2 := by
    calc
      Real.sqrt (ℓ * V) *
          Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
            M ≤
        (Real.sqrt C * Real.sqrt ℓ *
          Real.exp (((B + 1) / 2) * δ)) *
          Real.exp
            (-saddleSourceSecondBranchOuterBarrier ε ℓ δ) *
              (saddleSourceSecondBranchMomentCoefficient *
                η ^ 4) := by
          gcongr
      _ = K * Real.sqrt ℓ *
          Real.exp (((B + 1) / 2) * δ) *
          (2 + δ) ^ 4 *
          Real.exp
            (-c * ℓ * Q * Real.exp (B * δ)) := by
          rw [hbarrier]
          try dsimp [K, η]
          ring_nf
      _ < κ / 2 := houterℓ δ hδ
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
          (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T)) < κ
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
          (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceContourDamping
              ε ℓ (1 + δ) T)) ≤ _ at hsource
  dsimp only [M] at houterterm
  linarith

end

section

open Filter MeasureTheory Set
open scoped Topology

private theorem saddleGaussian_central_compl_subset_tail
    (R : ℝ) :
    (Icc (-R) R)ᶜ ⊆ saddleGaussianTailSet R := by
  intro T hT
  change R ≤ |T|
  by_contra hnot
  have hsmall : |T| < R := lt_of_not_ge hnot
  have hinterior := (abs_lt).mp hsmall
  exact hT ⟨hinterior.1.le, hinterior.2.le⟩

private theorem saddleGaussian_fullLine_error_le_central_add_tails
    {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (R : ℝ) :
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ ≤
      ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := by
  let s : Set ℝ := Icc (-R) R
  let tail : Set ℝ := saddleGaussianTailSet R
  have hsub : sᶜ ⊆ tail :=
    saddleGaussian_central_compl_subset_tail R
  have hsubae : sᶜ ≤ᶠ[ae (volume : Measure ℝ)] tail :=
    Filter.Eventually.of_forall (fun T hT => hsub hT)
  have hdiff : Integrable (fun T : ℝ => F T - G T) :=
    hF.sub hG
  have hmonoF :
      (∫ T : ℝ in sᶜ, ‖F T‖) ≤
        ∫ T : ℝ in tail, ‖F T‖ := by
    apply setIntegral_mono_set hF.norm.integrableOn
    · exact Filter.Eventually.of_forall (fun T => norm_nonneg (F T))
    · exact hsubae
  have hmonoG :
      (∫ T : ℝ in sᶜ, ‖G T‖) ≤
        ∫ T : ℝ in tail, ‖G T‖ := by
    apply setIntegral_mono_set hG.norm.integrableOn
    · exact Filter.Eventually.of_forall (fun T => norm_nonneg (G T))
    · exact hsubae
  have hpoint : ∀ T ∈ sᶜ,
      ‖F T - G T‖ ≤ ‖F T‖ + ‖G T‖ := by
    intro T hT
    exact norm_sub_le _ _
  have hcompare := setIntegral_mono_on
    hdiff.norm.integrableOn
    (hF.norm.add hG.norm).integrableOn
    (measurableSet_Icc.compl) hpoint
  have htailbound :
      ‖∫ T : ℝ in sᶜ, (F T - G T)‖ ≤
        (∫ T : ℝ in tail, ‖F T‖) +
          (∫ T : ℝ in tail, ‖G T‖) := by
    calc
      ‖∫ T : ℝ in sᶜ, (F T - G T)‖ ≤
          ∫ T : ℝ in sᶜ, ‖F T - G T‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ T : ℝ in sᶜ, (‖F T‖ + ‖G T‖) := hcompare
      _ = (∫ T : ℝ in sᶜ, ‖F T‖) +
          (∫ T : ℝ in sᶜ, ‖G T‖) := by
        rw [integral_add hF.norm.integrableOn
          hG.norm.integrableOn]
      _ ≤ (∫ T : ℝ in tail, ‖F T‖) +
          (∫ T : ℝ in tail, ‖G T‖) :=
        add_le_add hmonoF hmonoG
  have hsplit := integral_add_compl
    (μ := volume) (f := fun T : ℝ => F T - G T) (s := s)
      (show MeasurableSet s from measurableSet_Icc) hdiff
  calc
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ =
        ‖∫ T : ℝ, (F T - G T)‖ := by
          rw [integral_sub hF hG]
    _ = ‖(∫ T : ℝ in s, (F T - G T)) +
          (∫ T : ℝ in sᶜ, (F T - G T))‖ := by
          rw [hsplit]
    _ ≤ ‖∫ T : ℝ in s, (F T - G T)‖ +
          ‖∫ T : ℝ in sᶜ, (F T - G T)‖ :=
          norm_add_le _ _
    _ ≤ ‖∫ T : ℝ in s, (F T - G T)‖ +
          ((∫ T : ℝ in tail, ‖F T‖) +
            (∫ T : ℝ in tail, ‖G T‖)) := by
          gcongr
    _ = ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := by
          try dsimp [s, tail]
          ring

private theorem saddleSourceGaussianKernel_scaled_integral
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      Real.sqrt (2 * Real.pi) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  have hV' : 0 < V := hV
  have hproduct : 0 < ℓ * V := mul_pos hℓ hV
  rw [saddleSourceGaussianKernel_integral]
  change
    Real.sqrt (ℓ * V) * Real.sqrt (Real.pi / (ℓ * V / 2)) =
      Real.sqrt (2 * Real.pi)
  rw [← Real.sqrt_mul hproduct.le]
  congr 1
  field_simp [hℓ.ne', hV'.ne', hproduct.ne']

private theorem saddleSource_scaled_tail_lt_relative_gaussian
    {ε ℓ u C A κ X W : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hC : 0 < C) (hA : 0 < A)
    (hbound : X ≤ C * A * W)
    (hnormalized :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        W < κ) :
    X < (C * κ / Real.sqrt (2 * Real.pi)) * A *
      (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hs : 0 <
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    positivity
  have hg : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hmass := saddleSourceGaussianKernel_scaled_integral hℓ hV
  have hgaussian :
      (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
        Real.sqrt (2 * Real.pi) /
          Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    apply (eq_div_iff hs.ne').mpr
    linarith
  have hW :
      W < κ /
        Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    apply (lt_div_iff₀ hs).mpr
    linarith
  calc
    X ≤ C * A * W := hbound
    _ < C * A *
        (κ / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)) := by
      exact mul_lt_mul_of_pos_left hW (mul_pos hC hA)
    _ = (C * κ / Real.sqrt (2 * Real.pi)) * A *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
      rw [hgaussian]
      field_simp [hs.ne', hg.ne']

private theorem saddleSource_weighted_tail_integral_le
    {F : ℝ → ℂ} {W : ℝ → ℝ} {C A R : ℝ}
    (hF : Integrable F)
    (hW : Integrable W)
    (hpoint : ∀ T ∈ saddleGaussianTailSet R,
      ‖F T‖ ≤ (C * A) * W T) :
    (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) ≤
      C * A * (∫ T : ℝ in saddleGaussianTailSet R, W T) := by
  have hmajor : Integrable (fun T : ℝ => (C * A) * W T) :=
    hW.const_mul (C * A)
  have hcompare := setIntegral_mono_on
    hF.norm.integrableOn hmajor.integrableOn
      (saddleGaussianTailSet_measurable R) hpoint
  calc
    (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        (C * A) * W T := hcompare
    _ = C * A *
        (∫ T : ℝ in saddleGaussianTailSet R, W T) := by
      rw [integral_const_mul]

private theorem exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ u : ℝ, -1 < u →
          ∀ v R : ℝ,
            Integrable (fun T : ℝ =>
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T)) →
            (∫ T : ℝ in saddleGaussianTailSet R,
              ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) ≤
              C * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
                (∫ T : ℝ in saddleGaussianTailSet R,
                  saddleGaussianTailWeight T *
                    Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  obtain ⟨C, hC, hpoly⟩ :=
    exists_plusPolynomial_uniform_weighted_bound hε
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ u hu v R hweighted
  apply saddleSource_weighted_tail_integral_le
    (saddleSourceCenteredPlusIntegrand_integrable
      hε hℓ hu horder v) hweighted
  intro T hT
  rw [saddleSourceCenteredPlusIntegrand_norm
    hε hℓ hu horder]
  have hp := hpoly u hu.le T
  unfold saddleGaussianTailWeight
  calc
    Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ ≤
      Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        (C * (1 + |T| ^ 3) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖) := by
        gcongr
    _ = (C * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖) *
        ((1 + |T| ^ 3) *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
        ring

private theorem exists_saddleSourceCenteredMinusIntegrand_weighted_tail_integral_bound
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ u : ℝ, 1 + ε / 4 ≤ u →
          ∀ v R : ℝ,
            Integrable (fun T : ℝ =>
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T)) →
            (∫ T : ℝ in saddleGaussianTailSet R,
              ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) ≤
              C * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
                (∫ T : ℝ in saddleGaussianTailSet R,
                  saddleGaussianTailWeight T *
                    Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  obtain ⟨C, hC, hpoly⟩ :=
    exists_minusPolynomial_uniform_weighted_bound hε
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ u hu v R hweighted
  have hu' : -1 < u := by linarith
  apply saddleSource_weighted_tail_integral_le
    (saddleSourceCenteredMinusIntegrand_integrable
      hε hℓ hu' horder v) hweighted
  intro T hT
  rw [saddleSourceCenteredMinusIntegrand_norm
    hε hℓ hu' horder]
  have hp := hpoly u hu T
  unfold saddleGaussianTailWeight
  calc
    Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ ≤
      Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        (C * (1 + |T| ^ 3) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖) := by
        gcongr
    _ = (C * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖) *
        ((1 + |T| ^ 3) *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
        ring

private theorem saddleSourceGaussianPlusIntegrand_tail_norm_eq
    (ε ℓ u R : ℝ) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) =
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) =
      ∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with T
      unfold saddleSourceGaussianPlusIntegrand
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < saddleSourceGaussianKernel ε ℓ u T by
          unfold saddleSourceGaussianKernel
          positivity)]
    _ = ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
      rw [integral_mul_const]
      ring

private theorem saddleSourceGaussianMinusIntegrand_tail_norm_eq
    (ε ℓ u R : ℝ) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) =
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) =
      ∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with T
      unfold saddleSourceGaussianMinusIntegrand
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < saddleSourceGaussianKernel ε ℓ u T by
          unfold saddleSourceGaussianKernel
          positivity)]
    _ = ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleSourceGaussianKernel ε ℓ u T) := by
      rw [integral_mul_const]
      ring

private theorem saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
    {ε ℓ u R A κcentral κsource κgaussian : ℝ}
    {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hcentral :
      ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ <
        κcentral * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T))
    (hsource :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) <
          κsource * A)
    (hgaussian :
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) <
          κgaussian * A) :
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ <
      (κcentral + (κsource + κgaussian) /
        Real.sqrt (2 * Real.pi)) * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hsplit := saddleGaussian_fullLine_error_le_central_add_tails
    hF hG R
  have hone : (0 : ℝ) < 1 := by norm_num
  have hsource' :=
    saddleSource_scaled_tail_lt_relative_gaussian
      (ε := ε) (u := u) (C := (1 : ℝ)) (A := (1 : ℝ))
      (κ := κsource * A)
      (X := ∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖)
      (W := ∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖)
      hℓ hV hone hone (by simp only [mul_one, one_mul, Std.le_refl]) hsource
  have hgaussian' :=
    saddleSource_scaled_tail_lt_relative_gaussian
      (ε := ε) (u := u) (C := (1 : ℝ)) (A := (1 : ℝ))
      (κ := κgaussian * A)
      (X := ∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖)
      (W := ∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖)
      hℓ hV hone hone (by simp only [mul_one, one_mul, Std.le_refl]) hgaussian
  calc
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ ≤
        ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
          (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
          (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := hsplit
    _ < (κcentral * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) +
        ((κsource * A /
            Real.sqrt (2 * Real.pi)) *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) +
        ((κgaussian * A /
            Real.sqrt (2 * Real.pi)) *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)) := by
      simpa only [Nat.ofNat_nonneg, Real.sqrt_mul, one_mul,
        mul_one] using! add_lt_add (add_lt_add hcentral hsource') hgaussian'
    _ = (κcentral + (κsource + κgaussian) /
        Real.sqrt (2 * Real.pi)) * A *
          (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
      ring

private theorem saddleSourceGaussianKernel_normalized_tail_le
    {ε ℓ u z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hz : 0 ≤ z)
    (hlarge : 12 ≤ ℓ * saddleSourceGaussianVariance ε ℓ u) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)),
          saddleSourceGaussianKernel ε ℓ u T) ≤
        4 * Real.sqrt (2 * Real.pi) *
          Real.exp (-(z ^ 2) / 8) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let k : ℝ := ℓ * V / 2
  let s : ℝ := Real.sqrt (ℓ * V)
  let R : ℝ := z / s
  have hproduct : 0 < ℓ * V := mul_pos hℓ hV
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have hk : 6 ≤ k := by
    try dsimp [k, V]
    linarith
  have hkpos : 0 < k := by linarith
  have hR : 0 ≤ R := by
    try dsimp [R]
    positivity
  have hgaussian := saddleSourceGaussianKernel_integrable hℓ hV
  have hweighted :=
    saddleGaussianTailWeight_mul_gaussian_integrable hkpos
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleSourceGaussianKernel ε ℓ u T ≤
        saddleGaussianTailWeight T * Real.exp (-k * T ^ 2) := by
    intro T hT
    have hw : 1 ≤ saddleGaussianTailWeight T := by
      unfold saddleGaussianTailWeight
      linarith [pow_nonneg (abs_nonneg T) 3]
    unfold saddleSourceGaussianKernel
    change Real.exp (-k * T ^ 2) ≤
      saddleGaussianTailWeight T * Real.exp (-k * T ^ 2)
    linarith [mul_le_mul_of_nonneg_right hw
      (Real.exp_pos (-k * T ^ 2)).le]
  have hcompare := setIntegral_mono_on
    hgaussian.integrableOn hweighted.integrableOn
      (saddleGaussianTailSet_measurable R) hpoint
  have htail := saddleGaussian_cubic_tail_integral_le hk hR
  have hexponent : (k / 4) * R ^ 2 = z ^ 2 / 8 := by
    have hsquare : s ^ 2 = ℓ * V := by
      try dsimp [s]
      exact Real.sq_sqrt hproduct.le
    try dsimp [k, R]
    field_simp [hs.ne']
    nlinarith [hsquare]
  have hroot :
      s * Real.sqrt (Real.pi / (k / 4)) =
        2 * Real.sqrt (2 * Real.pi) := by
    have hkquarter : 0 < k / 4 := by positivity
    have hratio : 0 ≤ Real.pi / (k / 4) := by positivity
    have hleft :
        0 ≤ s * Real.sqrt (Real.pi / (k / 4)) := by
      positivity
    have hright : 0 ≤ 2 * Real.sqrt (2 * Real.pi) := by
      positivity
    have hsquare :
        (s * Real.sqrt (Real.pi / (k / 4))) ^ 2 =
          (2 * Real.sqrt (2 * Real.pi)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hratio,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      have hsquare' : s ^ 2 = ℓ * V := by
        try dsimp [s]
        exact Real.sq_sqrt hproduct.le
      rw [hsquare']
      try dsimp [k]
      have hV' : 0 < V := hV
      field_simp [hℓ.ne', hV'.ne']
      norm_num
    nlinarith
  have hexponent' : -(k / 4) * R ^ 2 = -(z ^ 2) / 8 := by
    linarith [hexponent]
  change
    s * (∫ T : ℝ in saddleGaussianTailSet R,
      saddleSourceGaussianKernel ε ℓ u T) ≤
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(z ^ 2) / 8)
  calc
    s * (∫ T : ℝ in saddleGaussianTailSet R,
      saddleSourceGaussianKernel ε ℓ u T) ≤
      s * (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcompare hs.le
    _ ≤ s * (2 * Real.exp (-(k / 4) * R ^ 2) *
      Real.sqrt (Real.pi / (k / 4))) := by
      exact mul_le_mul_of_nonneg_left htail hs.le
    _ = 4 * Real.sqrt (2 * Real.pi) *
      Real.exp (-(z ^ 2) / 8) := by
      rw [hexponent']
      calc
        s * (2 * Real.exp (-(z ^ 2) / 8) *
          Real.sqrt (Real.pi / (k / 4))) =
          2 * Real.exp (-(z ^ 2) / 8) *
            (s * Real.sqrt (Real.pi / (k / 4))) := by ring
        _ = 2 * Real.exp (-(z ^ 2) / 8) *
          (2 * Real.sqrt (2 * Real.pi)) := by rw [hroot]
        _ = _ := by ring

private noncomputable def saddleSourceGaussianNormalizedTailMajorant (x : ℝ) : ℝ :=
  4 * Real.sqrt (2 * Real.pi) *
    Real.exp (-(x ^ (1 / 6 : ℝ)) / 8)

private theorem tendsto_saddleSourceGaussianNormalizedTailMajorant :
    Tendsto saddleSourceGaussianNormalizedTailMajorant
      atTop (𝓝 (0 : ℝ)) := by
  have hpower : Tendsto
      (fun x : ℝ => x ^ (1 / 6 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)
  have hnegative : Tendsto
      (fun x : ℝ => -(x ^ (1 / 6 : ℝ)) / 8)
      atTop atBot := by
    have h := hpower.const_mul_atTop_of_neg
      (by norm_num : -(1 / 8 : ℝ) < 0)
    convert! h using 1
    funext x
    ring
  have hexp := Real.tendsto_exp_atBot.comp hnegative
  have h := hexp.const_mul (4 * Real.sqrt (2 * Real.pi))
  change Tendsto
    (fun x : ℝ =>
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(x ^ (1 / 6 : ℝ)) / 8))
    atTop (𝓝 (0 : ℝ))
  simpa only [Function.comp_apply, mul_zero] using! h

private theorem eventually_saddleSource_firstBranch_uniform_gaussian_tail :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ,
            -1 < u → u ≤ 1 + ε / 2 →
              Real.log ℓ / 4 ≤ ℓ * (1 + u) →
                Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    saddleSourceGaussianKernel ε ℓ u T) < κ := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards [hnear.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos]
    with ε hε hεsmall horder hmargin hvariance
  change 0 < ε at hε
  intro κ hκ
  let U : ℝ := 2 + ε / 2
  have hU : 0 < U := by
    try dsimp [U]
    positivity
  have hlog : Tendsto (fun ℓ : ℝ => Real.log ℓ / 4)
      atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const
      (by norm_num : (0 : ℝ) < 4)
  have hdecay :=
    (tendsto_saddleSourceGaussianNormalizedTailMajorant.comp
      hlog).eventually (Iio_mem_nhds hκ)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (6 * U / ε),
    hlog.eventually (eventually_ge_atTop (0 : ℝ)),
    hdecay] with ℓ hℓ hthreshold hlognonneg hdecayℓ
  intro u hulower huupper hlogscale
  let η : ℝ := 1 + u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let z : ℝ := (ℓ * η) ^ (1 / 12 : ℝ)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hηupper : η ≤ U := by
    try dsimp [η, U]
    linarith
  have hV : 0 < V :=
    hvariance ℓ hℓ u hulower huupper
  have hmargin' :
      ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
        0 ≤ (1 - 10 * ε * (1 + a)) := by
    intro a ha
    have h := hmargin a ha
    linarith
  have hvar :=
    upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin'
  have hvarupper : 2 * ε ≤ U * V := by
    have hproduct :=
      mul_le_mul_of_nonneg_right hηupper hV.le
    change 2 * ε ≤ η * V at hvar
    exact hvar.trans hproduct
  have hthreshold' : 6 * U ≤ ℓ * ε := by
    have h := (div_le_iff₀ hε).mp hthreshold
    linarith
  have hlarge : 12 ≤ ℓ * V := by
    have hproduct := mul_le_mul_of_nonneg_left
      hvarupper hℓ.le
    have hmain : U * 12 ≤ U * (ℓ * V) := by
      linarith
    by_contra hnot
    have hlt : ℓ * V < 12 := lt_of_not_ge hnot
    have hcontradiction := mul_lt_mul_of_pos_left hlt hU
    linarith
  have hz : 0 ≤ z := by
    try dsimp [z]
    exact Real.rpow_nonneg
      (mul_nonneg hℓ.le hη.le) _
  have hgaussian := saddleSourceGaussianKernel_normalized_tail_le
    (ε := ε) (ℓ := ℓ) (u := u) (z := z)
    hℓ hV hz hlarge
  have hpower :
      (Real.log ℓ / 4) ^ (1 / 6 : ℝ) ≤ z ^ 2 := by
    have hmono := Real.rpow_le_rpow hlognonneg hlogscale
      (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have hsquare : z ^ 2 = (ℓ * η) ^ (1 / 6 : ℝ) := by
      try dsimp [z]
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (mul_nonneg hℓ.le hη.le)]
      congr 1
      norm_num
    rw [hsquare]
    exact hmono
  calc
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (saddleSourceFirstBranchCentralRadius ε ℓ u),
        saddleSourceGaussianKernel ε ℓ u T) ≤
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(z ^ 2) / 8) := by
      simpa only [saddleSourceFirstBranchCentralRadius, one_div, Nat.ofNat_nonneg,
        Real.sqrt_mul, z, η] using! hgaussian
    _ ≤ saddleSourceGaussianNormalizedTailMajorant
      (Real.log ℓ / 4) := by
      unfold saddleSourceGaussianNormalizedTailMajorant
      gcongr
    _ < κ := hdecayℓ

private theorem eventually_saddleSource_secondBranch_uniform_gaussian_tail :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            Real.sqrt
              (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                (saddleSourceSecondBranchCentralRadius
                  ε ℓ (1 + δ)),
                saddleSourceGaussianKernel ε ℓ (1 + δ) T) < κ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε hfloor
  change 0 < ε at hε
  intro κ hκ
  let V₀ : ℝ := saddleSourceSecondBranchVarianceFloor ε
  have hV₀ : 0 < V₀ :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  have hdecay :=
    tendsto_saddleSourceGaussianNormalizedTailMajorant.eventually
      (Iio_mem_nhds hκ)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (12 / V₀), hdecay]
    with ℓ hℓ hthreshold hdecayℓ
  intro δ hδ
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  let z : ℝ := ℓ ^ (1 / 12 : ℝ)
  have hVlower : V₀ ≤ V :=
    hfloor ℓ hℓ δ hδ
  have hV : 0 < V := hV₀.trans_le hVlower
  have hlarge : 12 ≤ ℓ * V := by
    have hbase := (div_le_iff₀ hV₀).mp hthreshold
    calc
      12 ≤ ℓ * V₀ := by linarith
      _ ≤ ℓ * V :=
        mul_le_mul_of_nonneg_left hVlower hℓ.le
  have hz : 0 ≤ z := by
    try dsimp [z]
    exact Real.rpow_nonneg hℓ.le _
  have hgaussian := saddleSourceGaussianKernel_normalized_tail_le
    (ε := ε) (ℓ := ℓ) (u := 1 + δ) (z := z)
    hℓ hV hz hlarge
  have hsquare : z ^ 2 = ℓ ^ (1 / 6 : ℝ) := by
    try dsimp [z]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul hℓ.le]
    congr 1
    norm_num
  calc
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
      (∫ T : ℝ in saddleGaussianTailSet
        (saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)),
        saddleSourceGaussianKernel ε ℓ (1 + δ) T) ≤
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(z ^ 2) / 8) := by
      simpa only [saddleSourceSecondBranchCentralRadius, one_div, Nat.ofNat_nonneg,
        Real.sqrt_mul, z] using! hgaussian
    _ = saddleSourceGaussianNormalizedTailMajorant ℓ := by
      unfold saddleSourceGaussianNormalizedTailMajorant
      rw [hsquare]
    _ < κ := hdecayℓ

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private theorem eventually_saddleSourceFirstBranch_sourceL1Tails :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                  ‖saddleSourceCenteredPlusIntegrand ε ℓ u
                      (saddleSourceStationaryLogRadius ε ℓ u) T‖) <
                κ * ‖plusPolynomial ε
                  (Complex.I * (u : ℂ))‖) ∧
              (1 + ε / 4 ≤ u →
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                      (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    ‖saddleSourceCenteredMinusIntegrand ε ℓ u
                        (saddleSourceStationaryLogRadius ε ℓ u) T‖) <
                  κ * ‖minusPolynomial ε
                    (Complex.I * (u : ℂ))‖) := by
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear :=
      (tendsto_id.mono_left
        (nhdsWithin_le_nhds :
          𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hnear] with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, heps,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSource_firstBranch_uniform_tail]
    with ε hε hεsmall horder hmargin hvariance htail
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a)) := by
    intro a ha
    have h := hmargin a ha
    linarith
  obtain ⟨Cp, hCp, hplus⟩ :=
    exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
      hε horder
  obtain ⟨Cm, hCm, hminus⟩ :=
    exists_saddleSourceCenteredMinusIntegrand_weighted_tail_integral_bound
      hε horder
  intro κ hκ
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htail (κ / Cp) (div_pos hκ hCp),
    htail (κ / Cm) (div_pos hκ hCm)]
    with ℓ hℓ hp hm
  intro u hu huupper hstar
  let R : ℝ := saddleSourceFirstBranchCentralRadius ε ℓ u
  let v : ℝ := saddleSourceStationaryLogRadius ε ℓ u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  have hV : 0 < V := hvariance ℓ hℓ u hu huupper
  have hs : 0 < Real.sqrt (ℓ * V) := by positivity
  have hweighted := saddleSource_firstBranch_weighted_integrable
    hε hεsmall hℓ hu huupper horder hmargin'
  have hpnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cp := by
    simpa [R, V, saddleSourceFirstBranchCentralRadius] using! hp u hu huupper hstar
  have hmnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cm := by
    simpa [R, V, saddleSourceFirstBranchCentralRadius] using! hm u hu huupper hstar
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hbound := hplus ℓ hℓ u hu v R hweighted
    change
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) <
        κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
    calc
      Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) ≤
        Real.sqrt (ℓ * V) *
          (Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          gcongr
      _ = Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (Real.sqrt (ℓ * V) *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          ring
      _ < Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (κ / Cp) := by
          gcongr
      _ = κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
          field_simp [hCp.ne']
  · intro huminus
    have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := div_pos hε four_pos
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    have hbound := hminus ℓ hℓ u huminus v R hweighted
    change
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) <
        κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
    calc
      Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) ≤
        Real.sqrt (ℓ * V) *
          (Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          gcongr
      _ = Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (Real.sqrt (ℓ * V) *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          ring
      _ < Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (κ / Cm) := by
          gcongr
      _ = κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
          field_simp [hCm.ne']

private theorem eventually_saddleSourceFirstBranch_gaussianL1Tails :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceFirstBranchCentralRadius ε ℓ u),
                  ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) <
                κ * ‖plusPolynomial ε
                  (Complex.I * (u : ℂ))‖) ∧
              (1 + ε / 4 ≤ u →
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                  (∫ T : ℝ in saddleGaussianTailSet
                      (saddleSourceFirstBranchCentralRadius ε ℓ u),
                    ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) <
                  κ * ‖minusPolynomial ε
                    (Complex.I * (u : ℂ))‖) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSource_firstBranch_uniform_gaussian_tail]
    with ε hε htail
  change 0 < ε at hε
  intro κ hκ
  filter_upwards [htail κ hκ]
    with ℓ hℓ
  intro u hu huupper hstar
  let R : ℝ := saddleSourceFirstBranchCentralRadius ε ℓ u
  let s : ℝ :=
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
  have hkernel :
      s * (∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T) < κ := by
    simpa [s, R, saddleSourceFirstBranchCentralRadius] using! hℓ u hu huupper hstar
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    change s *
      (∫ T : ℝ in saddleGaussianTailSet R,
        ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) <
      κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
    rw [saddleSourceGaussianPlusIntegrand_tail_norm_eq]
    linarith [mul_lt_mul_of_pos_left hkernel hden]
  · intro huminus
    have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := div_pos hε four_pos
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    change s *
      (∫ T : ℝ in saddleGaussianTailSet R,
        ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) <
      κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
    rw [saddleSourceGaussianMinusIntegrand_tail_norm_eq]
    linarith [mul_lt_mul_of_pos_left hkernel hden]

private theorem eventually_saddleSourceFirstBranch_fullGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
          Real.log ℓ / 4 ≤ ℓ * (1 + u) →
            (‖(∫ T : ℝ,
                saddleSourceCenteredPlusIntegrand ε ℓ u
                  (saddleSourceStationaryLogRadius ε ℓ u) T) -
              (∫ T : ℝ,
                saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
              ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ u T)) ∧
            (1 + ε / 4 ≤ u →
              ‖(∫ T : ℝ,
                  saddleSourceCenteredMinusIntegrand ε ℓ u
                    (saddleSourceStationaryLogRadius ε ℓ u) T) -
                (∫ T : ℝ,
                  saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
                ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
                  (∫ T : ℝ,
                    saddleSourceGaussianKernel ε ℓ u T)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSourceFirstBranch_centralGaussianErrors,
    eventually_saddleSourceFirstBranch_sourceL1Tails,
    eventually_saddleSourceFirstBranch_gaussianL1Tails]
    with ε hε horder hvariance hcentral hsource hgaussian
  change 0 < ε at hε
  let a : ℝ := Real.sqrt (2 * Real.pi) / 8
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hcentral (1 / 4 : ℝ) (by norm_num),
    hsource a ha, hgaussian a ha]
    with ℓ hℓ hc hs hg
  intro u hu huupper hstar
  let R : ℝ := saddleSourceFirstBranchCentralRadius ε ℓ u
  let v : ℝ := saddleSourceStationaryLogRadius ε ℓ u
  have hV := hvariance ℓ hℓ u hu huupper
  have hG := saddleSourceGaussianKernel_integral_pos hℓ hV
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  obtain ⟨hcplus, hcminus⟩ := hc u hu huupper hstar
  obtain ⟨hsplus, hsminus⟩ := hs u hu huupper hstar
  obtain ⟨hgplus, hgminus⟩ := hg u hu huupper hstar
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hfull :=
      saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
        (ε := ε) (ℓ := ℓ) (u := u) (R := R)
        (A := ‖plusPolynomial ε (Complex.I * (u : ℂ))‖)
        (κcentral := (1 / 4 : ℝ))
        (κsource := a) (κgaussian := a)
        (F := saddleSourceCenteredPlusIntegrand ε ℓ u v)
        (G := saddleSourceGaussianPlusIntegrand ε ℓ u)
        (saddleSourceCenteredPlusIntegrand_integrable
          hε hℓ hu horder v)
        (saddleSourceGaussianPlusIntegrand_integrable hℓ hV)
        hℓ hV hcplus hsplus hgplus
    calc
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        ((1 / 4 : ℝ) + (a + a) /
          Real.sqrt (2 * Real.pi)) *
            ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ u T) := hfull
      _ = (1 / 2 : ℝ) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ,
              saddleSourceGaussianKernel ε ℓ u T) := by
        try dsimp [a]
        field_simp [hsqrt.ne']
        ring
      _ < ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T) := by
        linarith [mul_pos hden hG]
  · intro huminus
    have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := div_pos hε four_pos
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    have hfull :=
      saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
        (ε := ε) (ℓ := ℓ) (u := u) (R := R)
        (A := ‖minusPolynomial ε (Complex.I * (u : ℂ))‖)
        (κcentral := (1 / 4 : ℝ))
        (κsource := a) (κgaussian := a)
        (F := saddleSourceCenteredMinusIntegrand ε ℓ u v)
        (G := saddleSourceGaussianMinusIntegrand ε ℓ u)
        (saddleSourceCenteredMinusIntegrand_integrable
          hε hℓ hu horder v)
        (saddleSourceGaussianMinusIntegrand_integrable hℓ hV)
        hℓ hV (hcminus huminus)
          (hsminus huminus) (hgminus huminus)
    calc
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        ((1 / 4 : ℝ) + (a + a) /
          Real.sqrt (2 * Real.pi)) *
            ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ u T) := hfull
      _ = (1 / 2 : ℝ) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ,
              saddleSourceGaussianKernel ε ℓ u T) := by
        try dsimp [a]
        field_simp [hsqrt.ne']
        ring
      _ < ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T) := by
        linarith [mul_pos hden hG]

private theorem eventually_saddleSourceSecondBranch_sourceL1Tails_of_uniform_tail
    (hweighted :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 0 < ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            Integrable
              (fun T : ℝ => saddleGaussianTailWeight T *
                Real.exp
                  (-saddleSourceContourDamping
                    ε ℓ (1 + δ) T)))
    (htail :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ κ : ℝ, 0 < κ →
          ∀ᶠ ℓ : ℝ in atTop,
            ∀ δ : ℝ, ε / 2 ≤ δ →
              Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceSecondBranchCentralRadius
                      ε ℓ (1 + δ)),
                  saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceContourDamping
                        ε ℓ (1 + δ) T)) < κ) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceCenteredPlusIntegrand
                    ε ℓ (1 + δ)
                    (saddleSourceStationaryLogRadius
                      ε ℓ (1 + δ)) T‖) <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) ∧
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceCenteredMinusIntegrand
                    ε ℓ (1 + δ)
                    (saddleSourceStationaryLogRadius
                      ε ℓ (1 + δ)) T‖) <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    hweighted, htail]
    with ε hε horder hvariance hweight htail'
  change 0 < ε at hε
  obtain ⟨Cp, hCp, hplus⟩ :=
    exists_saddleSourceCenteredPlusIntegrand_weighted_tail_integral_bound
      hε horder
  obtain ⟨Cm, hCm, hminus⟩ :=
    exists_saddleSourceCenteredMinusIntegrand_weighted_tail_integral_bound
      hε horder
  intro κ hκ
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htail' (κ / Cp) (div_pos hκ hCp),
    htail' (κ / Cm) (div_pos hκ hCm)]
    with ℓ hℓ hp hm
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  let v : ℝ := saddleSourceStationaryLogRadius ε ℓ u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  have hu : -1 < u := by
    try dsimp [u]
    linarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    linarith
  have hV : 0 < V := by
    try dsimp [V, u]
    exact hvariance ℓ hℓ δ hδ
  have hs : 0 < Real.sqrt (ℓ * V) := by positivity
  have hweighted' := hweight ℓ hℓ δ hδ
  have hpnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cp := by
    simpa only [saddleSourceContourDamping_eq_firstBranch] using! hp δ hδ
  have hmnormal :
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-saddleSourceContourDamping ε ℓ u T)) <
          κ / Cm := by
    simpa only [saddleSourceContourDamping_eq_firstBranch] using! hm δ hδ
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hbound := hplus ℓ hℓ u hu v R hweighted'
    change
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) <
        κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
    calc
      Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖) ≤
        Real.sqrt (ℓ * V) *
          (Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          gcongr
      _ = Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (Real.sqrt (ℓ * V) *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          ring
      _ < Cp * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (κ / Cp) := by
          gcongr
      _ = κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
          field_simp [hCp.ne']
  · have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := div_pos hε four_pos
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    have hbound := hminus ℓ hℓ u huminus v R hweighted'
    change
      Real.sqrt (ℓ * V) *
        (∫ T : ℝ in saddleGaussianTailSet R,
          ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) <
        κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
    calc
      Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖) ≤
        Real.sqrt (ℓ * V) *
          (Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          gcongr
      _ = Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (Real.sqrt (ℓ * V) *
            (∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-saddleSourceContourDamping ε ℓ u T))) := by
          ring
      _ < Cm * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (κ / Cm) := by
          gcongr
      _ = κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
          field_simp [hCm.ne']

private theorem eventually_saddleSourceSecondBranch_gaussianL1Tails :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceGaussianPlusIntegrand
                    ε ℓ (1 + δ) T‖) <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) ∧
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceGaussianMinusIntegrand
                    ε ℓ (1 + δ) T‖) <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_saddleSource_secondBranch_uniform_gaussian_tail]
    with ε hε htail
  change 0 < ε at hε
  intro κ hκ
  filter_upwards [htail κ hκ]
    with ℓ hℓ
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  let s : ℝ :=
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
  have hu : -1 < u := by
    try dsimp [u]
    linarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    linarith
  have hkernel :
      s * (∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T) < κ := by
    simpa [s, R, u, saddleSourceSecondBranchCentralRadius] using! hℓ δ hδ
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    change s *
      (∫ T : ℝ in saddleGaussianTailSet R,
        ‖saddleSourceGaussianPlusIntegrand ε ℓ u T‖) <
      κ * ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
    rw [saddleSourceGaussianPlusIntegrand_tail_norm_eq]
    linarith [mul_lt_mul_of_pos_left hkernel hden]
  · have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := div_pos hε four_pos
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    change s *
      (∫ T : ℝ in saddleGaussianTailSet R,
        ‖saddleSourceGaussianMinusIntegrand ε ℓ u T‖) <
      κ * ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
    rw [saddleSourceGaussianMinusIntegrand_tail_norm_eq]
    linarith [mul_lt_mul_of_pos_left hkernel hden]

private theorem eventually_saddleSourceSecondBranch_fullGaussianErrors_of_sourceL1
    (hsource :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ κ : ℝ, 0 < κ →
          ∀ᶠ ℓ : ℝ in atTop,
            ∀ δ : ℝ, ε / 2 ≤ δ →
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceSecondBranchCentralRadius
                      ε ℓ (1 + δ)),
                  ‖saddleSourceCenteredPlusIntegrand
                      ε ℓ (1 + δ)
                      (saddleSourceStationaryLogRadius
                        ε ℓ (1 + δ)) T‖) <
                κ * ‖plusPolynomial ε
                  (Complex.I * ((1 + δ : ℝ) : ℂ))‖) ∧
              (Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (saddleSourceSecondBranchCentralRadius
                      ε ℓ (1 + δ)),
                  ‖saddleSourceCenteredMinusIntegrand
                      ε ℓ (1 + δ)
                      (saddleSourceStationaryLogRadius
                        ε ℓ (1 + δ)) T‖) <
                κ * ‖minusPolynomial ε
                  (Complex.I * ((1 + δ : ℝ) : ℂ))‖)) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, ε / 2 ≤ δ →
          (‖(∫ T : ℝ,
              saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianPlusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖plusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
          (‖(∫ T : ℝ,
              saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianMinusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖minusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_centralGaussianErrors,
    hsource,
    eventually_saddleSourceSecondBranch_gaussianL1Tails]
    with ε hε horder hvariance hcentral hsource' hgaussian
  change 0 < ε at hε
  let a : ℝ := Real.sqrt (2 * Real.pi) / 8
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hcentral (1 / 4 : ℝ) (by norm_num),
    hsource' a ha, hgaussian a ha]
    with ℓ hℓ hc hs hg
  intro δ hδ
  let u : ℝ := 1 + δ
  let R : ℝ := saddleSourceSecondBranchCentralRadius ε ℓ u
  let v : ℝ := saddleSourceStationaryLogRadius ε ℓ u
  have hu : -1 < u := by
    try dsimp [u]
    linarith
  have huminus : 1 + ε / 4 ≤ u := by
    try dsimp [u]
    linarith
  have hV : 0 < saddleSourceGaussianVariance ε ℓ u := by
    try dsimp [u]
    exact hvariance ℓ hℓ δ hδ
  have hG := saddleSourceGaussianKernel_integral_pos hℓ hV
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  obtain ⟨hcplus, hcminus⟩ := hc δ hδ
  obtain ⟨hsplus, hsminus⟩ := hs δ hδ
  obtain ⟨hgplus, hgminus⟩ := hg δ hδ
  constructor
  · have hden : 0 <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
      (div_pos hε four_pos).trans_le
        (plusPolynomial_imaginary_norm_ge_beta hε hu.le)
    have hfull :=
      saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
        (ε := ε) (ℓ := ℓ) (u := u) (R := R)
        (A := ‖plusPolynomial ε (Complex.I * (u : ℂ))‖)
        (κcentral := (1 / 4 : ℝ))
        (κsource := a) (κgaussian := a)
        (F := saddleSourceCenteredPlusIntegrand ε ℓ u v)
        (G := saddleSourceGaussianPlusIntegrand ε ℓ u)
        (saddleSourceCenteredPlusIntegrand_integrable
          hε hℓ hu horder v)
        (saddleSourceGaussianPlusIntegrand_integrable hℓ hV)
        hℓ hV hcplus hsplus hgplus
    change
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T)
    calc
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        ((1 / 4 : ℝ) + (a + a) /
          Real.sqrt (2 * Real.pi)) *
            ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ u T) := hfull
      _ = (1 / 2 : ℝ) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ,
              saddleSourceGaussianKernel ε ℓ u T) := by
        try dsimp [a]
        field_simp [hsqrt.ne']
        ring
      _ < ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T) := by
        linarith [mul_pos hden hG]
  · have hden : 0 <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
      have hb := div_pos hε four_pos
      have hnorm :=
        minusPolynomial_imaginary_norm_ge_three_beta
          hε huminus
      linarith
    have hfull :=
      saddleGaussian_fullLine_error_lt_of_central_and_normalized_tails
        (ε := ε) (ℓ := ℓ) (u := u) (R := R)
        (A := ‖minusPolynomial ε (Complex.I * (u : ℂ))‖)
        (κcentral := (1 / 4 : ℝ))
        (κsource := a) (κgaussian := a)
        (F := saddleSourceCenteredMinusIntegrand ε ℓ u v)
        (G := saddleSourceGaussianMinusIntegrand ε ℓ u)
        (saddleSourceCenteredMinusIntegrand_integrable
          hε hℓ hu horder v)
        (saddleSourceGaussianMinusIntegrand_integrable hℓ hV)
        hℓ hV hcminus hsminus hgminus
    change
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T)
    calc
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        ((1 / 4 : ℝ) + (a + a) /
          Real.sqrt (2 * Real.pi)) *
            ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ u T) := hfull
      _ = (1 / 2 : ℝ) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
            (∫ T : ℝ,
              saddleSourceGaussianKernel ε ℓ u T) := by
        try dsimp [a]
        field_simp [hsqrt.ne']
        ring
      _ < ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
          (∫ T : ℝ,
            saddleSourceGaussianKernel ε ℓ u T) := by
        linarith [mul_pos hden hG]

private theorem eventually_saddleSourceSecondBranch_sourceL1Tails :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceCenteredPlusIntegrand
                    ε ℓ (1 + δ)
                    (saddleSourceStationaryLogRadius
                      ε ℓ (1 + δ)) T‖) <
              κ * ‖plusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) ∧
            (Real.sqrt
                (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
              (∫ T : ℝ in saddleGaussianTailSet
                  (saddleSourceSecondBranchCentralRadius
                    ε ℓ (1 + δ)),
                ‖saddleSourceCenteredMinusIntegrand
                    ε ℓ (1 + δ)
                    (saddleSourceStationaryLogRadius
                      ε ℓ (1 + δ)) T‖) <
              κ * ‖minusPolynomial ε
                (Complex.I * ((1 + δ : ℝ) : ℂ))‖) := by
  apply eventually_saddleSourceSecondBranch_sourceL1Tails_of_uniform_tail
    eventually_saddleSource_secondBranch_weighted_integrable
  simpa only [saddleSourceSecondBranchCentralRadius, one_div,
    saddleSourceContourDamping_eq_firstBranch,
    eventually_atTop] using!
    eventually_saddleSource_secondBranch_uniform_tail

private theorem eventually_saddleSourceSecondBranch_fullGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, ε / 2 ≤ δ →
          (‖(∫ T : ℝ,
              saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianPlusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖plusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
          (‖(∫ T : ℝ,
              saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianMinusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖minusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) :=
  eventually_saddleSourceSecondBranch_fullGaussianErrors_of_sourceL1
    eventually_saddleSourceSecondBranch_sourceL1Tails

end

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

private theorem saddleDigamma_eq_complexDigamma_re
    {x : ℝ} (hx : 0 < x) :
    saddleDigamma x = (Complex.digamma (x : ℂ)).re := by
  have hΓ : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hcomplex :
      DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    apply Complex.differentiableAt_Gamma
    intro n h
    have hre := congrArg Complex.re h
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith
  have hreal :
      HasDerivAt Real.Gamma
        (deriv Complex.Gamma (x : ℂ)).re x := by
    have h := hcomplex.hasDerivAt.real_of_complex
    simpa only [Complex.Gamma_ofReal, Complex.ofReal_re] using! h
  unfold saddleDigamma
  rw [Real.deriv_log_comp_eq_logDeriv
    hreal.differentiableAt hΓ.ne',
    logDeriv_apply, hreal.deriv,
    Complex.digamma_def, logDeriv_apply,
    Complex.Gamma_ofReal, Complex.div_ofReal_re]

private theorem complexGamma_differentiableOn_positiveHalfPlane :
    DifferentiableOn ℂ Complex.Gamma
      {z : ℂ | 0 < z.re} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply Complex.differentiableAt_Gamma
  intro n hn
  have hre := congrArg Complex.re hn
  have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  change 0 < z.re at hz
  linarith

private theorem complexDigamma_continuousOn_positiveHalfPlane :
    ContinuousOn Complex.digamma
      {z : ℂ | 0 < z.re} := by
  let s : Set ℂ := {z : ℂ | 0 < z.re}
  have hopen : IsOpen s := by
    exact Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hgamma : DifferentiableOn ℂ Complex.Gamma s :=
    complexGamma_differentiableOn_positiveHalfPlane
  have hderiv : ContinuousOn (deriv Complex.Gamma) s :=
    (hgamma.deriv hopen).continuousOn
  have hcont : ContinuousOn Complex.Gamma s :=
    hgamma.continuousOn
  have hratio :
      ContinuousOn
        (fun z : ℂ => deriv Complex.Gamma z /
          Complex.Gamma z) s :=
    hderiv.div hcont
      (fun z hz =>
        Complex.Gamma_ne_zero_of_re_pos hz)
  simpa only [Complex.digamma_def] using! hratio

private theorem saddleDigamma_continuousOn_Ioi :
    ContinuousOn saddleDigamma (Ioi (0 : ℝ)) := by
  have hmap :
      MapsTo (fun x : ℝ => (x : ℂ))
        (Ioi (0 : ℝ))
        {z : ℂ | 0 < z.re} := by
    intro x hx
    simpa only [mem_ofPred_eq, Complex.ofReal_re, mem_Ioi] using! hx
  have hcomplex :=
    complexDigamma_continuousOn_positiveHalfPlane.comp
      Complex.continuous_ofReal.continuousOn hmap
  have hre :
      ContinuousOn
        (fun x : ℝ => (Complex.digamma (x : ℂ)).re)
        (Ioi (0 : ℝ)) :=
    Complex.continuous_re.continuousOn.comp hcomplex
      (fun x hx => Set.mem_univ _)
  apply hre.congr
  intro x hx
  exact saddleDigamma_eq_complexDigamma_re hx

private theorem tendsto_saddleDigamma_atTop :
    Tendsto saddleDigamma atTop atTop := by
  have h := Real.tendsto_log_atTop.atTop_add
    tendsto_saddleDigamma_sub_log
  convert! h using 1
  funext x
  ring

private theorem saddleSinhShellInterval_hasDerivAt
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => ∫ x in a..b,
        w x * x * Real.sinh (x * v))
      (∫ x in a..b,
        w x * x ^ 2 * Real.cosh (x * u)) u := by
  let F : ℝ → ℝ → ℝ := fun v x =>
    w x * x * Real.sinh (x * v)
  let F' : ℝ → ℝ → ℝ := fun v x =>
    w x * x ^ 2 * Real.cosh (x * v)
  have hF (v : ℝ) : Continuous (F v) := by
    try dsimp [F]
    exact (hw.mul continuous_id).mul
      (Real.continuous_sinh.comp
        (continuous_id.mul continuous_const))
  have hF' (v : ℝ) : Continuous (F' v) := by
    try dsimp [F']
    exact (hw.mul (continuous_id.pow 2)).mul
      (Real.continuous_cosh.comp
        (continuous_id.mul continuous_const))
  have hF'joint : Continuous (Function.uncurry F') := by
    try dsimp [F', Function.uncurry]
    exact ((hw.comp continuous_snd).mul
      (continuous_snd.pow 2)).mul
        (Real.continuous_cosh.comp
          (continuous_snd.mul continuous_fst))
  have hderiv (x v : ℝ) :
      HasDerivAt (fun z : ℝ => F z x) (F' v x) v := by
    have hlinear : HasDerivAt
        (fun z : ℝ => x * z) x v := by
      simpa only [id_eq, mul_one] using! (hasDerivAt_id v).const_mul x
    have hsinh := (Real.hasDerivAt_sinh
      (x * v)).comp v hlinear
    simpa [F, F', pow_two, mul_assoc, mul_left_comm, mul_comm] using! hsinh.const_mul (w x * x)
  have hrewrite :
      (fun v : ℝ => ∫ x in a..b,
        w x * x * Real.sinh (x * v)) =
      (fun v : ℝ => ∫ x in Set.Icc a b, F v x) := by
    funext v
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  have hderivrewrite :
      (∫ x in a..b,
        w x * x ^ 2 * Real.cosh (x * u)) =
      (∫ x in Set.Icc a b, F' u x) := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  rw [hrewrite, hderivrewrite]
  have hcompact :
      IsCompact (Metric.closedBall u 1 ×ˢ Set.Icc a b) :=
    (isCompact_closedBall u 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hcompact.bddAbove_image hF'joint.norm.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      ∀ v ∈ Metric.ball u 1, ‖F' v x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc]
      with x hx
    intro v hv
    have hpair :
        (v, x) ∈ Metric.closedBall u 1 ×ˢ Set.Icc a b :=
      ⟨Metric.ball_subset_closedBall hv, hx⟩
    exact hC (Set.mem_image_of_mem
      (fun p : ℝ × ℝ => ‖F' p.1 p.2‖) hpair)
  have hmeas : ∀ᶠ v in 𝓝 u,
      AEStronglyMeasurable (F v)
        (volume.restrict (Set.Icc a b)) :=
    Eventually.of_forall
      (fun v => (hF v).aestronglyMeasurable)
  have hint : Integrable (F u)
      (volume.restrict (Set.Icc a b)) :=
    (hF u).integrableOn_Icc
  have hderivmeas : AEStronglyMeasurable (F' u)
      (volume.restrict (Set.Icc a b)) :=
    (hF' u).aestronglyMeasurable
  have hconstant : Integrable (fun _ : ℝ => C)
      (volume.restrict (Set.Icc a b)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hdifferentiable :
      ∀ᵐ x ∂volume.restrict (Set.Icc a b),
        ∀ v ∈ Metric.ball u 1,
          HasDerivAt (fun z : ℝ => F z x) (F' v x) v :=
    Eventually.of_forall (fun x v _ => hderiv x v)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b))
    (s := Metric.ball u 1) (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds u zero_lt_one)
    hmeas hint hderivmeas hbound hconstant
    hdifferentiable).2

private theorem saddleSourceShellDerivative_hasDerivAt
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (u : ℝ) :
    HasDerivAt (saddleSourceShellDerivative ε)
      (upperNetShellVariance ε (u - 1)) u := by
  have hcutoff : 0 < (ε ^ 3) := by
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (ε ^ 3))
  have hmax (a : ℝ) : 0 < max a (ε ^ 3) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        (1 - 10 * ε * (1 + (max a (ε ^ 3)))) *
          Real.exp (-2 * max a (ε ^ 3))) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (ε ^ 3)) ^ 2 *
          Real.cosh (max a (ε ^ 3))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by
      positivity [hmax a])).neg
  have hshort :
      HasDerivAt
        (fun v : ℝ =>
          ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            shortShellDensity ε a * a *
              Real.sinh (v * a))
        (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a * a ^ 2 *
            Real.cosh (u * a)) u := by
    have h := saddleSinhShellInterval_hasDerivAt
      w hw horder u
    convert! h using 1
    · funext v
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le horder] at ha
      try dsimp [w]
      rw [max_eq_left ha.1]
      congr 2
      ring
    · apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le horder] at ha
      try dsimp [w]
      rw [max_eq_left ha.1]
      congr 2
      ring
  have hremote : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
    linarith
  have hpositive :
      HasDerivAt
        (fun v : ℝ =>
          ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            positiveShellDensity ε a * a *
              Real.sinh (v * a))
        (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          positiveShellDensity ε a * a ^ 2 *
            Real.cosh (u * a)) u := by
    have h := saddleSinhShellInterval_hasDerivAt
      (positiveShellDensity ε)
      (positiveShellDensity_continuous ε)
      hremote u
    convert! h using 1
    · funext v
      apply intervalIntegral.integral_congr
      intro a ha
      ring_nf
    · apply intervalIntegral.integral_congr
      intro a ha
      ring_nf
  have hshortvariance :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
        -upperShortShellVariance ε (u - 1) := by
    unfold upperShortShellVariance
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hpositivevariance :
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
        upperPositiveShellVariance ε (u - 1) := by
    unfold upperPositiveShellVariance
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hsum := hshort.add hpositive
  unfold saddleSourceShellDerivative
  convert! hsum using 1
  rw [hshortvariance, hpositivevariance]
  unfold upperNetShellVariance
  ring

private theorem eventually_saddleSourceShellDerivative_monotone_secondBranch :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      MonotoneOn (saddleSourceShellDerivative ε)
        (Ici (1 + ε / 2)) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_netShellVariance_bounds]
    with ε hε horder hnet
  change 0 < ε at hε
  have hcont :
      ContinuousOn (saddleSourceShellDerivative ε)
        (Ici (1 + ε / 2)) :=
    (saddleSourceShellDerivative_contDiff_one hε horder).continuous.continuousOn
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici (1 + ε / 2)) hcont
  · intro u hu
    exact (saddleSourceShellDerivative_hasDerivAt
      hε horder u).hasDerivWithinAt
  · intro u hu
    have hthreshold : 1 + ε / 2 ≤ u := by
      have hmem : u ∈ Ici (1 + ε / 2) :=
        interior_subset hu
      exact hmem
    have hδ : ε / 2 ≤ u - 1 := by linarith
    have hδnonneg : 0 ≤ u - 1 := by linarith
    have hvariance :=
      (upperPositiveShellVariance_bounds hε hδnonneg).1
    have hpositive : 0 ≤ upperPositiveShellVariance ε (u - 1) := by
      exact (show
        0 ≤ (1 / 2 : ℝ) * (ε⁻¹ ^ 3) ^ 2 *
          shellWeight ε *
            Real.exp ((u - 1) * (ε⁻¹ ^ 3)) by
          positivity [shellWeight_pos ε]).trans hvariance
    have hnetlower := (hnet (u - 1) hδ).1
    linarith

private theorem saddleLogRadius_continuousOn_Ici
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {d : ℕ} (hd : 0 < d)
    {u₀ : ℝ} (hu₀ : -1 < u₀) :
    ContinuousOn (saddleLogRadius ε d) (Ici u₀) := by
  let g : ℝ → ℝ := fun u =>
    ((d : ℝ) / 2) * (1 + u) / 2
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hg : Continuous g := by
    try dsimp [g]
    fun_prop
  have hmap : MapsTo g (Ici u₀) (Ioi (0 : ℝ)) := by
    intro u hu
    try dsimp [g]
    have hu' : u₀ ≤ u := hu
    have hupositive : 0 < 1 + u := by
      linarith
    change 0 < ((d : ℝ) / 2) * (1 + u) / 2
    positivity
  have hdigamma :
      ContinuousOn (fun u => saddleDigamma (g u)) (Ici u₀) :=
    saddleDigamma_continuousOn_Ioi.comp
      hg.continuousOn hmap
  have hshell :
      ContinuousOn (saddleSourceShellDerivative ε)
        (Ici u₀) :=
    (saddleSourceShellDerivative_contDiff_one
      hε horder).continuous.continuousOn
  have hsum :
      ContinuousOn
        (fun u : ℝ =>
          -(Real.log Real.pi) / 2 +
            saddleDigamma (g u) / 2 +
              saddleSourceShellDerivative ε u)
        (Ici u₀) :=
    (continuousOn_const.add
      (hdigamma.div_const 2)).add hshell
  apply hsum.congr
  intro u hu
  simpa only  using!
    saddleLogRadius_eq_digamma_add_shellDerivative
      ε d u

private theorem tendsto_saddleGammaArgument_atTop
    {d : ℕ} (hd : 0 < d) :
    Tendsto
      (fun u : ℝ =>
        ((d : ℝ) / 2) * (1 + u) / 2)
      atTop atTop := by
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hslope : 0 < (d : ℝ) / 4 := by positivity
  have hlinear := tendsto_id.const_mul_atTop hslope
  have h := hlinear.atTop_add
    (tendsto_const_nhds (x := (d : ℝ) / 4))
  convert! h using 1
  funext u
  simp only [id_eq]
  ring

private theorem tendsto_saddleLogRadius_atTop_of_shell_monotone
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {d : ℕ} (hd : 0 < d)
    (hmono : MonotoneOn (saddleSourceShellDerivative ε)
      (Ici (1 + ε / 2))) :
    Tendsto (saddleLogRadius ε d) atTop atTop := by
  have _hε : 0 < ε := hε
  have _horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)) := horder
  let U : ℝ := 1 + ε / 2
  let C : ℝ := saddleSourceShellDerivative ε U
  have hargument := tendsto_saddleDigamma_atTop.comp
    (tendsto_saddleGammaArgument_atTop hd)
  have hhalf :=
    hargument.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hbaseline :=
    hhalf.atTop_add
      (tendsto_const_nhds
        (x := -(Real.log Real.pi) / 2 + C))
  have hcomparison :
      (fun u : ℝ =>
        saddleDigamma
          (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
          (-(Real.log Real.pi) / 2 + C)) ≤ᶠ[atTop]
        saddleLogRadius ε d := by
    filter_upwards [eventually_ge_atTop U]
      with u hu
    have hshell : C ≤ saddleSourceShellDerivative ε u := by
      apply hmono
      · change 1 + ε / 2 ≤ U
        try dsimp [U]
        exact le_rfl
      · simpa only [mem_Ici] using! hu
      · exact hu
    rw [saddleLogRadius_eq_digamma_add_shellDerivative]
    try dsimp [C]
    linarith
  exact tendsto_atTop_mono' atTop hcomparison hbaseline

private theorem eventually_tendsto_saddleLogRadius_atTop :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ d : ℕ, 0 < d →
        Tendsto (saddleLogRadius ε d) atTop atTop := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSourceShellDerivative_monotone_secondBranch]
    with ε hε horder hmono
  change 0 < ε at hε
  intro d hd
  exact tendsto_saddleLogRadius_atTop_of_shell_monotone
    hε horder hd hmono

private theorem saddleLogRadius_covers_Ici
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {d : ℕ} (hd : 0 < d)
    {u₀ : ℝ} (hu₀ : -1 < u₀)
    (htop : Tendsto (saddleLogRadius ε d) atTop atTop)
    {r : ℝ}
    (hr : Real.exp (saddleLogRadius ε d u₀) ≤ r) :
    ∃ u : ℝ, u₀ ≤ u ∧
      saddleLogRadius ε d u = Real.log r := by
  have hrpositive : 0 < r :=
    (Real.exp_pos _).trans_le hr
  have hlog :
      saddleLogRadius ε d u₀ ≤ Real.log r := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hrpositive]
    exact hr
  have hfilter :
      (atTop : Filter ℝ) ≤ 𝓟 (Ici u₀) :=
    Filter.le_principal_iff.mpr
      (eventually_ge_atTop u₀)
  have himage :
      Ici (saddleLogRadius ε d u₀) ⊆
        saddleLogRadius ε d '' Ici u₀ :=
    (isPreconnected_Ici : IsPreconnected (Ici u₀)).intermediate_value_Ici
      (show u₀ ∈ Ici u₀ from Set.mem_Ici.mpr (le_refl u₀))
      hfilter
      (saddleLogRadius_continuousOn_Ici
        hε horder hd hu₀)
      htop
  obtain ⟨u, hu, heq⟩ := himage hlog
  exact ⟨u, hu, heq⟩

private theorem eventually_saddleLogRadius_covers_Ici :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ d : ℕ, 0 < d →
        ∀ u₀ : ℝ, -1 < u₀ →
          ∀ r : ℝ,
            Real.exp (saddleLogRadius ε d u₀) ≤ r →
              ∃ u : ℝ, u₀ ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_tendsto_saddleLogRadius_atTop]
    with ε hε horder htop
  change 0 < ε at hε
  intro d hd u₀ hu₀ r hr
  exact saddleLogRadius_covers_Ici
    hε horder hd hu₀ (htop d hd) hr

private theorem eventually_saddleSmallRadiusStarOrdinate_gt_neg_one
    (ε : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      -1 < saddleSmallRadiusStarOrdinate ε d := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)]
    with d hd
  have hdreal : (3 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hdimension : 1 < (d : ℝ) / 2 := by
    linarith
  have hlog : 0 < Real.log ((d : ℝ) / 2) :=
    Real.log_pos hdimension
  have hdenominator : 0 < 4 * ((d : ℝ) / 2) := by
    positivity
  have hratio :
      0 < Real.log ((d : ℝ) / 2) /
        (4 * ((d : ℝ) / 2)) :=
    div_pos hlog hdenominator
  unfold saddleSmallRadiusStarOrdinate
  linarith

private theorem eventually_saddleSmallRadiusStar_log_coverage :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ,
          saddleSmallRadiusStar ε d ≤ r →
            ∃ u : ℝ,
              saddleSmallRadiusStarOrdinate ε d ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by
  filter_upwards
    [eventually_saddleLogRadius_covers_Ici]
    with ε hcoverage
  filter_upwards
    [eventually_saddleSmallRadiusStarOrdinate_gt_neg_one ε,
      eventually_gt_atTop (0 : ℕ)]
    with d hstar hd
  intro r hr
  apply hcoverage d hd
    (saddleSmallRadiusStarOrdinate ε d) hstar r
  exact hr

private theorem eventually_saddleSourceRadius_log_coverage :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ d : ℕ, 0 < d →
        ∀ r : ℝ,
          saddleSourceRadius ε d ≤ r →
            ∃ u : ℝ,
              1 + ε / 4 ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleLogRadius_covers_Ici]
    with ε hε hcoverage
  change 0 < ε at hε
  intro d hd r hr
  have hu₀ : -1 < 1 + ε / 4 := by linarith
  apply hcoverage d hd (1 + ε / 4) hu₀ r
  exact hr

end

section

open Filter
open scoped Topology

private noncomputable def EventualLowerBound : Prop :=
  ∀ c : ℝ, c < Real.pi⁻¹ →
    ∀ᶠ d : ℕ in atTop, c ≤ normalizedProgram d

private noncomputable def EventualUpperBound : Prop :=
  ∀ c : ℝ, Real.pi⁻¹ < c →
    ∀ᶠ d : ℕ in atTop, normalizedProgram d ≤ c

private noncomputable def UniformAdmissibleLowerBound : Prop :=
  ∀ c : ℝ, c < Real.pi⁻¹ →
    ∀ᶠ d : ℕ in atTop,
      ∀ f : Admissible d, c ≤ normalizedCost f

private noncomputable def ConstructivePrimalUpperBound : Prop :=
  ∀ c : ℝ, Real.pi⁻¹ < c →
    ∀ᶠ d : ℕ in atTop,
      ∃ f : Admissible d, normalizedCost f ≤ c

private theorem normalizedProgram_le_normalizedCost {d : ℕ}
    (f : Admissible d) :
    normalizedProgram d ≤ normalizedCost f := by
  unfold normalizedProgram
  exact csInf_le (normalizedCostSet_bddBelow d) ⟨f, rfl⟩

private theorem eventualUpperBound_of_constructivePrimal
    (hupper : ConstructivePrimalUpperBound) : EventualUpperBound := by
  intro c hc
  filter_upwards [hupper c hc] with d ⟨f, hf⟩
  exact (normalizedProgram_le_normalizedCost f).trans hf

private theorem eventualLowerBound_of_uniform_and_constructive
    (hlower : UniformAdmissibleLowerBound)
    (hupper : ConstructivePrimalUpperBound) : EventualLowerBound := by
  intro c hc
  have haux : Real.pi⁻¹ < Real.pi⁻¹ + 1 := by linarith
  filter_upwards [hlower c hc, hupper (Real.pi⁻¹ + 1) haux]
    with d hcost ⟨f, _⟩
  unfold normalizedProgram
  refine le_csInf ⟨normalizedCost f, f, rfl⟩ ?_
  rintro _ ⟨g, rfl⟩
  exact hcost g

private theorem sharpQuotient_of_eventual_bounds
    (hlower : EventualLowerBound)
    (hupper : EventualUpperBound) :
    SharpQuotientAsymptotic := by
  unfold SharpQuotientAsymptotic
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hmid : (a + Real.pi⁻¹) / 2 < Real.pi⁻¹ := by
      linarith
    filter_upwards [hlower _ hmid] with d hd
    linarith
  · intro b hb
    have hmid : Real.pi⁻¹ < (Real.pi⁻¹ + b) / 2 := by
      linarith
    filter_upwards [hupper _ hmid] with d hd
    linarith

private theorem sharpQuotient_of_uniform_lower_and_constructive_upper
    (hlower : UniformAdmissibleLowerBound)
    (hupper : ConstructivePrimalUpperBound) :
    SharpQuotientAsymptotic := by
  exact sharpQuotient_of_eventual_bounds
    (eventualLowerBound_of_uniform_and_constructive hlower hupper)
    (eventualUpperBound_of_constructivePrimal hupper)

private structure OrderedEpsilonUpperConstruction where
  epsilonBound : ℝ
  epsilonBound_pos : 0 < epsilonBound
  normalizedRadius : ℝ → ℕ → ℝ
  limitingRadius : ℝ → ℝ
  limitingRadius_tendsto :
    Tendsto limitingRadius (𝓝[>] (0 : ℝ)) (𝓝 Real.pi⁻¹)
  normalizedRadius_tendsto :
    ∀ ε : ℝ, 0 < ε → ε < epsilonBound →
      Tendsto (normalizedRadius ε) atTop (𝓝 (limitingRadius ε))
  admissibleWitness :
    ∀ ε : ℝ, 0 < ε → ε < epsilonBound →
      ∀ᶠ d : ℕ in atTop,
        ∃ f : Admissible d, normalizedCost f ≤ normalizedRadius ε d

private theorem constructivePrimal_of_orderedEpsilon
    (construction : OrderedEpsilonUpperConstruction) :
    ConstructivePrimalUpperBound := by
  intro c hc
  have hclose :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        construction.limitingRadius ε < c :=
    (tendsto_order.1 construction.limitingRadius_tendsto).2 c hc
  have hpositive :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ε < construction.epsilonBound := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds construction.epsilonBound_pos)
  obtain ⟨ε, hεclose, hεpositive, hεsmall⟩ :=
    (hclose.and (hpositive.and hsmall)).exists
  have hradius :
      ∀ᶠ d : ℕ in atTop,
        construction.normalizedRadius ε d < c :=
    (tendsto_order.1
      (construction.normalizedRadius_tendsto ε hεpositive hεsmall)).2
        c hεclose
  filter_upwards [construction.admissibleWitness ε hεpositive hεsmall,
    hradius] with d ⟨f, hf⟩ hr
  exact ⟨f, hf.trans hr.le⟩

private theorem sharpQuotient_of_uniform_lower_and_ordered_upper
    (hlower : UniformAdmissibleLowerBound)
    (construction : OrderedEpsilonUpperConstruction) :
    SharpQuotientAsymptotic := by
  exact sharpQuotient_of_uniform_lower_and_constructive_upper hlower
    (constructivePrimal_of_orderedEpsilon construction)

end
end CohnElkies
