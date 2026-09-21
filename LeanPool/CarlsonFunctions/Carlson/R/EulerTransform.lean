/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.Continuation
public import LeanPool.CarlsonFunctions.Carlson.R.JointParameter
public import LeanPool.CarlsonFunctions.Carlson.R.SlitJointAnalytic

/-! # Euler transformations of Carlson's R-function

Carlson's Theorem 6.8-3 is proved on the full product slit plane and for arbitrary
complex exponents and Dirichlet parameters, in the entire regularized normalization.
The proof first reflects the beta integral on right-half-plane nodes, then uses
permanence of functional relations in the parameters and in the nodes. Theorem
6.8-4's additional equal-parameter regularization remains a separate task.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Taking reciprocals preserves the right-half-plane node domain. -/
theorem carlsonRVariableDomain_inv {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    (fun i => (z i)⁻¹) ∈ carlsonRVariableDomain := by
  intro i
  change 0 < ((z i)⁻¹).re
  rw [inv_re]
  exact div_pos (hz i) (normSq_pos.mpr (ne_zero_of_re_pos (hz i)))

private theorem integral_Ioo_one_sub (f : ℝ → ℂ) :
    (∫ u : ℝ in Set.Ioo 0 1, f (1 - u)) = ∫ u : ℝ in Set.Ioo 0 1, f u := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) f 1
  simpa only [sub_self, sub_zero, intervalIntegral.integral_of_le zero_le_one,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] using h

/-- Reflection of the beta integral, with principal branches controlled by
positivity of the real parts of each factor. -/
theorem carlsonRUnitIntervalIntegral_inv (a a' : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      (∏ i, z i ^ (-b i)) *
        carlsonRUnitIntervalIntegral a' a b (fun i => (z i)⁻¹) := by
  unfold carlsonRUnitIntervalIntegral
  rw [← integral_Ioo_one_sub, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  simp only [ofReal_sub, ofReal_one, sub_sub_cancel]
  have hp : (∏ i, ((u : ℂ) + (1 - u : ℂ) * z i) ^ (-b i)) =
      (∏ i, z i ^ (-b i)) *
        ∏ i, ((1 - u : ℂ) + (u : ℂ) * (z i)⁻¹) ^ (-b i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hzi := ne_zero_of_re_pos (hz i)
    have hv : 0 < ((1 - u : ℂ) + (u : ℂ) * (z i)⁻¹).re := by
      have hi := carlsonRVariableDomain_inv hz i
      change 0 < ((z i)⁻¹).re at hi
      simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
      exact add_pos (sub_pos.mpr hu.2) (mul_pos hu.1 hi)
    rw [← mul_cpow_of_re_pos (hz i) hv]
    congr 1
    field_simp
    ring
  rw [hp]
  ring

private theorem regCarlsonRContinued_euler_of_pos
    {a a' : ℂ} {b z : ι → ℂ} (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued (-a) z hz b =
      (∏ i, z i ^ (-b i)) *
        regCarlsonRContinued (-a') (fun i => (z i)⁻¹) (carlsonRVariableDomain_inv hz) b := by
  apply mul_left_cancel₀ (mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos ha'))
  rw [← carlsonRUnitIntervalIntegral_eq_gamma_mul_continued ha ha' hsum hz,
    carlsonRUnitIntervalIntegral_inv a a' b hz,
    carlsonRUnitIntervalIntegral_eq_gamma_mul_continued ha' ha
      (by simpa [add_comm] using hsum) (carlsonRVariableDomain_inv hz)]
  ring

/-- Euler's transformation (Carlson 6.8-3), entire in the exponent and every
Dirichlet parameter. No Gamma-regularity or convergence assumptions are needed. -/
theorem regCarlsonRContinued_euler (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued t z hz b =
      (∏ i, z i ^ (-b i)) * regCarlsonRContinued (-(∑ i, b i) - t)
        (fun i => (z i)⁻¹) (carlsonRVariableDomain_inv hz) b := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have hzero (t : ℂ) (z : ι → ℂ) (hz : z ∈ carlsonRVariableDomain) :
        regCarlsonRContinued t z hz b = 0 := by
      rw [regCarlsonRContinued_eq_integral t hz (by intro i; exact isEmptyElim i)]
      simp [regCarlsonRIntegral, regCarlsonDirichletAverage, regDirichletIntegral]
    simp [hzero]
  | inr hι =>
    let L : (Option ι → ℂ) → ℂ := fun p =>
      regCarlsonRContinued (p none) z hz (fun i => p (some i))
    let R : (Option ι → ℂ) → ℂ := fun p =>
      (∏ i, z i ^ (-p (some i))) * regCarlsonRContinued
        (-(∑ i, p (some i)) - p none) (fun i => (z i)⁻¹)
        (carlsonRVariableDomain_inv hz) (fun i => p (some i))
    have hcoord (p : Option ι → ℂ) (i : Option ι) :
        AnalyticAt ℂ (fun q : Option ι → ℂ => q i) p :=
      (ContinuousLinearMap.proj i : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
    have hleft : AnalyticOnNhd ℂ L Set.univ := by
      intro p _
      exact analyticAt_regCarlsonRContinued_comp hz (hcoord p none)
        (analyticAt_pi_iff.mpr (fun i => hcoord p (some i)))
    have hright : AnalyticOnNhd ℂ R Set.univ := by
      intro p _
      apply AnalyticAt.mul
      · apply Finset.analyticAt_fun_prod
        intro i _
        simp only [cpow_def_of_ne_zero (ne_zero_of_re_pos (hz i))]
        exact (analyticAt_const.mul (hcoord p (some i)).neg).cexp
      · apply analyticAt_regCarlsonRContinued_comp (carlsonRVariableDomain_inv hz)
        · exact (Finset.analyticAt_fun_sum _ (fun i _ => hcoord p (some i))).neg.sub (hcoord p none)
        · exact analyticAt_pi_iff.mpr (fun i => hcoord p (some i))
    let o : Option ι → ℂ := fun i => i.elim (-1) (fun _ => 2)
    have hpos : ∀ᶠ p : Option ι → ℂ in 𝓝 o,
        0 < (-p none).re ∧ 0 < ((∑ i, p (some i)) + p none).re := by
      have hopen : IsOpen {p : Option ι → ℂ |
          0 < (-p none).re ∧ 0 < ((∑ i, p (some i)) + p none).re} := by
        exact (isOpen_lt continuous_const (by fun_prop :
          Continuous (fun p : Option ι → ℂ => (-p none).re))).inter
          (isOpen_lt continuous_const (by fun_prop :
            Continuous (fun p : Option ι → ℂ => ((∑ i, p (some i)) + p none).re)))
      apply hopen.eventually_mem
      have hc : 0 < Fintype.card ι := Fintype.card_pos
      have hc' : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hc
      change 0 < (-(-1 : ℂ)).re ∧ 0 < ((∑ _ : ι, (2 : ℂ)) + -1).re
      norm_num
      linarith
    have hevent : L =ᶠ[𝓝 o] R := by
      filter_upwards [hpos] with p hp
      have h := regCarlsonRContinued_euler_of_pos hp.1 hp.2
        (show -p none + ((∑ i, p (some i)) + p none) = ∑ i, p (some i) by ring) hz
      dsimp only [L, R]
      simpa only [neg_neg, neg_add, sub_eq_add_neg] using h
    exact congrFun (hleft.eq_of_eventuallyEq hright hevent) (fun i => i.elim t b)

/-- Euler inversion (Carlson's Theorem 6.8-3) on the full product slit plane, for all
complex exponents and Dirichlet parameters. -/
theorem regCarlsonRSlit_euler (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonRSlit t b z =
      (∏ i, z i ^ (-b i)) * regCarlsonRSlit (-(∑ i, b i) - t) b (fun i => (z i)⁻¹) := by
  have hinv : AnalyticOnNhd ℂ (fun w : ι → ℂ => fun i => (w i)⁻¹) carlsonRSlitDomain := by
    intro w hw
    apply analyticAt_pi_iff.mpr
    intro i
    exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w).inv
      (slitPlane_ne_zero (hw i))
  have hR := analyticOnNhd_regCarlsonRSlit_comp isOpen_carlsonRSlitDomain
    (t := fun _ => -(∑ i, b i) - t) (b := fun _ => b)
    analyticOnNhd_const analyticOnNhd_const hinv (fun _ hw => carlsonRSlitDomain_inv hw)
  have hprod : AnalyticOnNhd ℂ (fun w : ι → ℂ => ∏ i, w i ^ (-b i)) carlsonRSlitDomain := by
    intro w hw
    apply Finset.analyticAt_fun_prod
    intro i _
    exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w).cpow analyticAt_const (hw i)
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_regCarlsonRSlit t b) (hprod.mul hR) ?_ hz
  intro w hw
  change regCarlsonRSlit t b w =
    (∏ i, w i ^ (-b i)) * regCarlsonRSlit (-(∑ i, b i) - t) b (fun i => (w i)⁻¹)
  rw [regCarlsonRSlit_eq_continued t b hw,
    regCarlsonRSlit_eq_continued _ b (carlsonRVariableDomain_inv hw)]
  exact regCarlsonRContinued_euler t b hw

end DirichletTransform
end
