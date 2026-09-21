/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.IntegralEvaluation
public import LeanPool.CarlsonFunctions.Carlson.R.Relations

import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dependence of Carlson's R-function on a small variable

This file develops [Carl77, Section 8.3].  Its core result identifies the sectorial limit as
one variable tends to zero with deletion of that variable and a beta-factor correction.

`tendsto_regCarlsonRContinued_update_zero_of_pos` allows arbitrary individual
Dirichlet parameters and any approach through the right half-plane. It still
assumes positive real parts for both endpoint exponents. The double-shift
recurrence 8.3(5) is available for removing those restrictions; the corresponding
induction on the limit, and continuation to larger slit-plane sectors, remain to
be proved.
-/

open Complex Filter ProbabilityTheory MeasureTheory
open scoped Topology
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A closed right-half-plane subsector used when a native R-integral variable approaches
zero.  Carlson's wider slit-plane sector is recovered only after continuation in the
variables. -/
def carlsonSmallVariableSector (δ r : ℝ) : Set ℂ :=
  {w | ‖w‖ ≤ r ∧ (w = 0 ∨ |arg w| ≤ Real.pi / 2 - δ)}

/-- Every point of Carlson's small-variable sector has norm at most its radius. -/
theorem norm_le_of_mem_carlsonSmallVariableSector {δ r : ℝ} {w : ℂ}
    (hw : w ∈ carlsonSmallVariableSector δ r) : ‖w‖ ≤ r :=
  hw.1

/-- The parameter vector obtained by deleting a distinguished coordinate. -/
def eraseCarlsonParameter (i : ι) (b : ι → ℂ) : {j // j ≠ i} → ℂ :=
  fun j => b j

/-- The variable vector obtained by deleting a distinguished coordinate. -/
def eraseCarlsonVariable (i : ι) (z : ι → ℂ) : {j // j ≠ i} → ℂ :=
  fun j => z j

private lemma unitIntervalIntegral_eq_gamma_mul_reg
    {κ : Type*} [Fintype κ] {a a' : ℂ} {b z : κ → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (hsum : a + a' = ∑ j, b j)
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      (Gamma a * Gamma a') * regCarlsonRIntegral (-a) b z := by
  rw [carlsonRUnitIntervalIntegral_eq ha ha' hsum hb hz,
    betaIntegral_eq_Gamma_mul_div _ _ ha ha', carlsonRIntegral, ← hsum]
  have hG := Gamma_ne_zero_of_re_pos (show 0 < (a + a').re by simpa using add_pos ha ha')
  field_simp

open scoped Classical in
private lemma tendsto_unitIntervalIntegral_update_zero
    (i : ι) {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re) (ha'i : 0 < (a' - b i).re)
    (hz : z ∈ carlsonRVariableDomain) :
    Tendsto (fun w => carlsonRUnitIntervalIntegral a a' b (Function.update z i w))
      (𝓝[ {w : ℂ | 0 ≤ w.re}] 0)
      (𝓝 (carlsonRUnitIntervalIntegral a (a' - b i)
        (eraseCarlsonParameter i b) (eraseCarlsonVariable i z))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  let P := fun u : ℝ => ∏ j : {j // j ≠ i},
    ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)
  have hbase (u : ℝ) (hu : u ∈ Set.Icc 0 1) (j : {j // j ≠ i}) :
      (1 - u : ℂ) + (u : ℂ) * z j ∈ slitPlane := by
    apply carlsonRightHalfPlane_subset_slitPlane
    have H : 0 < (z j).re := hz j
    change 0 < ((1 - u : ℂ) + (u : ℂ) * z j).re
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hu.2)
        (mul_pos (lt_of_le_of_ne hu.1 (Ne.symm hu0)) H)
  have hP : ContinuousOn P (Set.Icc 0 1) := by
    apply continuousOn_finsetProd
    intro j hj
    have hc : Continuous (fun u : ℝ => (1 - u : ℂ) + (u : ℂ) * z j) := by fun_prop
    exact hc.continuousOn.cpow_const (fun u hu => hbase u hu j)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hP
  let E := Real.exp (Real.pi * |(b i).im|)
  let B := fun u : ℝ => ‖(u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - b i - 1)‖
  let W := fun u : ℝ => ‖(u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)‖
  let D : ℝ := 2 ^ (-(b i).re)
  let F := fun w : ℂ => fun u : ℝ =>
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
      (((1 - u : ℂ) + (u : ℂ) * w) ^ (-b i) * P u)
  have hFint : ∀ᶠ w in 𝓝[{w : ℂ | 0 ≤ w.re}] 0, AEStronglyMeasurable (F w) μ := by
    filter_upwards with w
    apply Measurable.aestronglyMeasurable
    dsimp [F, P]
    fun_prop
  have hbound : ∀ᶠ w in 𝓝[{w : ℂ | 0 ≤ w.re}] 0,
      ∀ᵐ u ∂μ, ‖F w u‖ ≤ (B u + W u * D) * (E * max C 0) := by
    have hwsmall : ∀ᶠ w : ℂ in 𝓝[{w : ℂ | 0 ≤ w.re}] 0, ‖w‖ < 1 := by
      have hm : ∀ᶠ w : ℂ in 𝓝 0, w ∈ Metric.ball 0 1 :=
        Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
      simpa using hm.filter_mono
        (show 𝓝[{w : ℂ | 0 ≤ w.re}] 0 ≤ 𝓝 0 from inf_le_left)
    filter_upwards [self_mem_nhdsWithin, hwsmall] with w hw hsmall
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    have hu0 := hu.1
    have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
    let v : ℂ := (1 - u : ℂ) + (u : ℂ) * w
    have hvre : 1 - u ≤ v.re := by
      dsimp [v]
      simp only [ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
      exact le_add_of_nonneg_right (mul_nonneg hu0.le hw)
    have hvnorm : 1 - u ≤ ‖v‖ := hvre.trans (re_le_norm v)
    have hv : v ≠ 0 := ne_zero_of_re_pos (hu1.trans_le hvre)
    have hp : ‖v ^ (-b i)‖ ≤ ((1 - u) ^ (-(b i).re) + D) * E := by
      rw [norm_cpow_of_ne_zero hv, neg_re, neg_im, mul_neg, Real.exp_neg, div_inv_eq_mul]
      apply mul_le_mul
      · by_cases hbi : 0 ≤ (b i).re
        · exact (Real.rpow_le_rpow_of_nonpos hu1 hvnorm (neg_nonpos.mpr hbi)).trans
            (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
        · have hvle : ‖v‖ ≤ 2 := by
            calc
              ‖v‖ ≤ ‖(1 - u : ℂ)‖ + ‖(u : ℂ) * w‖ := norm_add_le _ _
              _ = (1 - u) + u * ‖w‖ := by
                rw [norm_mul, show (1 - u : ℂ) = ((1 - u : ℝ) : ℂ) by simp,
                  norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_pos hu1, abs_of_pos hu0]
              _ ≤ 2 := by nlinarith [hu.1, hu.2]
          exact (Real.rpow_le_rpow (norm_nonneg _) hvle (by linarith)).trans
            (le_add_of_nonneg_left (Real.rpow_nonneg hu1.le _))
      · apply Real.exp_le_exp.mpr
        exact (le_abs_self (arg v * (b i).im)).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_arg_le_pi v) (abs_nonneg _))
      · positivity
      · positivity
    have hbeta : ‖(u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)‖ *
        (1 - u) ^ (-(b i).re) = B u := by
      dsimp only [B]
      rw [norm_mul, norm_mul]
      have hone : (1 - u : ℂ) = ((1 - u : ℝ) : ℂ) := by simp
      simp only [hone, norm_cpow_eq_rpow_re_of_pos hu1, sub_re, one_re]
      rw [mul_assoc, ← Real.rpow_add hu1]
      congr 2
      ring
    calc
      ‖F w u‖ = ‖(u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)‖ *
          (‖v ^ (-b i)‖ * ‖P u‖) := by simp only [F, v, norm_mul]
      _ ≤ ‖(u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)‖ *
          ((((1 - u) ^ (-(b i).re) + D) * E) * max C 0) := by
        gcongr
        exact (hC u ⟨hu.1.le, hu.2.le⟩).trans (le_max_left _ _)
      _ = _ := by
        change W u * ((((1 - u) ^ (-(b i).re) + D) * E) * max C 0) = _
        have hb' : W u * (1 - u) ^ (-(b i).re) = B u := hbeta
        rw [← mul_assoc, ← mul_assoc, mul_add, hb']
        ring
  have hBint : Integrable (fun u => (B u + W u * D) * (E * max C 0)) μ := by
    exact (((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent ha ha'i).norm).add
      (((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        (betaIntegral_convergent ha ha').norm).mul_const D)).mul_const _
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun w => F w u) (𝓝[{w : ℂ | 0 ≤ w.re}] 0) (𝓝 (F 0 u)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    have hslit : (1 - u : ℂ) + (u : ℂ) * 0 ∈ slitPlane := by
      apply carlsonRightHalfPlane_subset_slitPlane
      simpa [carlsonRightHalfPlane] using sub_pos.mpr hu.2
    have hc : ContinuousAt (fun w : ℂ => (1 - u : ℂ) + (u : ℂ) * w) 0 := by fun_prop
    have hpow := (continuousAt_cpow_const (b := -b i) hslit).comp_of_eq hc rfl
    have H : ContinuousAt (fun w : ℂ => F w u) 0 :=
      continuousAt_const.mul (hpow.mul continuousAt_const)
    exact H.tendsto.mono_left inf_le_left
  have H := tendsto_integral_filter_of_dominated_convergence _ hFint hbound hBint hlim
  have hfull (w : ℂ) : (∫ u, F w u ∂μ) =
      carlsonRUnitIntervalIntegral a a' b (Function.update z i w) := by
    apply integral_congr_ae
    filter_upwards with u
    dsimp only [F, carlsonRUnitIntervalIntegral, μ]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [Function.update_self]
    congr 2
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne j.property]
  have hzero : (∫ u, F 0 u ∂μ) = carlsonRUnitIntervalIntegral a (a' - b i)
      (eraseCarlsonParameter i b) (eraseCarlsonVariable i z) := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    dsimp only [F, carlsonRUnitIntervalIntegral, eraseCarlsonParameter, eraseCarlsonVariable, P, μ]
    rw [mul_zero, add_zero]
    have hne : (1 - u : ℂ) ≠ 0 := by
      exact_mod_cast (sub_pos.mpr hu.2).ne'
    rw [← mul_assoc, mul_assoc ((u : ℂ) ^ (a - 1)), ← cpow_add _ _ hne]
    rw [show a' - 1 + -b i = a' - b i - 1 by ring]
  rw [hzero] at H
  simpa only [hfull] using H

open scoped Classical in
/-- Carlson's sectorial small-variable limit, Theorem 8.3-1, in regularized form.

The beta factors in Carlson's unregularized statement are absorbed by Gamma regularization;
the remaining shifted Gamma factor is displayed explicitly. -/
theorem tendsto_regCarlsonRIntegral_update_zero
     (i : ι) {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (ha'i : 0 < (a' - b i).re) (hsum : a + a' = ∑ j, b j)
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    Tendsto (fun w => regCarlsonRIntegral (-a) b (Function.update z i w))
      (𝓝[≠] 0 ⊓ 𝓟 (carlsonSmallVariableSector 1 1))
      (𝓝 (Gamma (a' - b i) / Gamma a' *
        regCarlsonRIntegral (-a) (eraseCarlsonParameter i b)
          (eraseCarlsonVariable i z))) := by
  let l := 𝓝[≠] (0 : ℂ) ⊓ 𝓟 (carlsonSmallVariableSector 1 1)
  have hwpos : ∀ᶠ w in l, 0 < w.re := by
    filter_upwards [(show {w : ℂ | w ≠ 0} ∈ l from
      mem_inf_of_left self_mem_nhdsWithin),
      (show carlsonSmallVariableSector 1 1 ∈ l from
      mem_inf_of_right (by simp))] with w hw hws
    apply (abs_arg_lt_pi_div_two_iff.mp (show |arg w| < Real.pi / 2 by
      rcases hws.2 with h | h
      · exact (hw h).elim
      · linarith)).resolve_right hw
  have hl : l ≤ 𝓝[{w : ℂ | 0 ≤ w.re}] 0 := by
    apply le_inf
    · exact inf_le_left.trans inf_le_left
    · exact le_principal_iff.mpr (hwpos.mono fun _ h => h.le)
  have H := (tendsto_unitIntervalIntegral_update_zero i ha ha' ha'i hz).mono_left hl
  have hs : a + (a' - b i) = ∑ j : {j // j ≠ i}, eraseCarlsonParameter i b j := by
    have H := Fintype.sum_eq_add_sum_subtype_ne b i
    rw [← hsum] at H
    dsimp only [eraseCarlsonParameter]
    linear_combination H
  have hb' : eraseCarlsonParameter i b ∈ mvBetaConvergent := fun j => hb j
  have hz' : eraseCarlsonVariable i z ∈ carlsonRVariableDomain := fun j => hz j
  rw [unitIntervalIntegral_eq_gamma_mul_reg ha ha'i hs hb' hz'] at H
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGa' := Gamma_ne_zero_of_re_pos ha'
  have H' := H.const_mul ((Gamma a * Gamma a')⁻¹)
  have heq : (fun w => (Gamma a * Gamma a')⁻¹ *
      carlsonRUnitIntervalIntegral a a' b (Function.update z i w)) =ᶠ[l]
      (fun w => regCarlsonRIntegral (-a) b (Function.update z i w)) := by
    filter_upwards [hwpos] with w hw
    have hzfull : Function.update z i w ∈ carlsonRVariableDomain := by
      intro j
      by_cases hji : j = i
      · subst j; simpa [carlsonRightHalfPlane] using hw
      · simpa [Function.update_of_ne hji] using hz j
    rw [unitIntervalIntegral_eq_gamma_mul_reg ha ha' hsum hb hzfull]
    field_simp
  have heqval : (Gamma a * Gamma a')⁻¹ *
      ((Gamma a * Gamma (a' - b i)) * regCarlsonRIntegral (-a)
        (eraseCarlsonParameter i b) (eraseCarlsonVariable i z)) =
      Gamma (a' - b i) / Gamma a' * regCarlsonRIntegral (-a)
        (eraseCarlsonParameter i b) (eraseCarlsonVariable i z) := by field_simp
  rw [heqval] at H'
  exact H'.congr' heq

omit [Fintype ι] in
open scoped Classical in
/-- Updating one node preserves the domain when the replacement has positive real part. -/
theorem carlsonRVariableDomain_update {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    (i : ι) {w : ℂ} (hw : 0 < w.re) :
    Function.update z i w ∈ carlsonRVariableDomain := by
  intro j
  by_cases hji : j = i
  · subst j; simpa [carlsonRightHalfPlane] using hw
  · simpa [Function.update_of_ne hji] using hz j

/-- Carlson's recurrence 8.3(5), used to move both endpoint exponents into
their convergence half-planes. This regularized form has no denominators. -/
theorem regCarlsonRContinued_eq_sum_double_shift (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    regCarlsonRContinued t z hz b =
      ∑ j, addDirichletUnit b i j * (((∑ k, b k) + t) * z j - t * z i) *
        regCarlsonRContinued (t - 1) z hz (addDirichletUnit (addDirichletUnit b i) j) := by
  have h := regCarlsonRContinued_add_one_eq_sum_mul_addDirichletUnit
    (t - 1) (addDirichletUnit b i) hz
  rw [sub_add_cancel] at h
  rw [regCarlsonRContinued_eq_addDirichletUnit t b hz i, h,
    regCarlsonRContinued_eq_sum_addDirichletUnit (t - 1) (addDirichletUnit b i) hz,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

open scoped Classical in
/-- The small-variable limit for the continued R-function with unrestricted
individual Dirichlet parameters. The approach can be any filter in the right
half-plane; no narrower angular sector is needed. The positive endpoint-exponent
hypotheses are still required here. -/
theorem tendsto_regCarlsonRContinued_update_zero_of_pos
    (i : ι) {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (ha'i : 0 < (a' - b i).re) (hsum : a + a' = ∑ j, b j)
    (hz : z ∈ carlsonRVariableDomain)
    {E : Type*} {l : Filter E} {w : E → ℂ}
    (hw : ∀ x, 0 < (w x).re) (hlim : Tendsto w l (𝓝 0)) :
    Tendsto (fun x => regCarlsonRContinued (-a) (Function.update z i (w x))
      (carlsonRVariableDomain_update hz i (hw x)) b) l
      (𝓝 (Gamma (a' - b i) / Gamma a' *
        regCarlsonRContinued (-a) (eraseCarlsonVariable i z)
          (fun j => hz j) (eraseCarlsonParameter i b))) := by
  have hwithin : Tendsto w l (𝓝[{v : ℂ | 0 ≤ v.re}] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun x => (hw x).le)⟩
  have H := (tendsto_unitIntervalIntegral_update_zero i ha ha' ha'i hz).comp hwithin
  have hs : a + (a' - b i) = ∑ j : {j // j ≠ i}, eraseCarlsonParameter i b j := by
    have h := Fintype.sum_eq_add_sum_subtype_ne b i
    rw [← hsum] at h
    dsimp only [eraseCarlsonParameter]
    linear_combination h
  have hz' : eraseCarlsonVariable i z ∈ carlsonRVariableDomain := fun j => hz j
  rw [carlsonRUnitIntervalIntegral_eq_gamma_mul_continued ha ha'i hs hz'] at H
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGa' := Gamma_ne_zero_of_re_pos ha'
  have H' := H.const_mul ((Gamma a * Gamma a')⁻¹)
  have hval : (Gamma a * Gamma a')⁻¹ *
      ((Gamma a * Gamma (a' - b i)) * regCarlsonRContinued (-a)
        (eraseCarlsonVariable i z) (fun j => hz j) (eraseCarlsonParameter i b)) =
      Gamma (a' - b i) / Gamma a' * regCarlsonRContinued (-a)
        (eraseCarlsonVariable i z) (fun j => hz j) (eraseCarlsonParameter i b) := by field_simp
  rw [hval] at H'
  apply H'.congr'
  filter_upwards with x
  dsimp only [Function.comp_def]
  rw [carlsonRUnitIntervalIntegral_eq_gamma_mul_continued ha ha' hsum
    (carlsonRVariableDomain_update hz i (hw x))]
  field_simp

/- Gauss's summation formula is a two-variable hypergeometric specialization of the theorem
above and is intentionally not included in the core R-function API. -/

end DirichletTransform
end CarlsonR
