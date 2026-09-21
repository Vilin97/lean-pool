/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Deriv
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Associated

/-!
# Carlson's R-function: homogeneity and associated-function relations

This file proves the regularized forms of Carlson's formulas 5.9-3, 5.9-5, and 5.9-6 on
the native convergence region and right-half-plane node domain. The third associated
relation follows by summing the tangential integration-by-parts relation.
All three algebraic associated relations are also extended to arbitrary complex Dirichlet
parameters for `regCarlsonRContinued`. Node derivatives are still stated for the native integral.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Carlson's first associated-function relation 5.9-5, in regularized form.  Gamma
regularization absorbs Carlson's weights and leaves the coefficients `b i`. -/
theorem regCarlsonRIntegral_eq_sum_update_add_one (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral t b z =
      ∑ i, b i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z := by
  have hpow : ContinuousOn (fun u : ι → ℝ ↦ carlsonAffineForm z u ^ t)
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu ↦ carlsonAffineForm_mem_slitPlane hz hu)
  simpa only [regCarlsonRIntegral, addDirichletUnit] using
    regCarlsonDirichletAverage_eq_sum_addDirichletUnit hb z (fun w => w ^ t) hpow

/-- Carlson's second associated-function relation 5.9-5, in regularized form. -/
theorem regCarlsonRIntegral_add_one_eq_sum_mul_update (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral (t + 1) b z =
      ∑ i, b i * z i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z := by
  have hpow : ContinuousOn (fun u : ι → ℝ ↦ carlsonAffineForm z u ^ t)
      (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuous_carlsonAffineForm z).continuousOn.cpow_const
      (fun _ hu ↦ carlsonAffineForm_mem_slitPlane hz hu)
  have hterm (i : ι) :
      b i * z i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z =
        regDirichletIntegral b
          (fun u ↦ z i * ((u i : ℂ) * carlsonAffineForm z u ^ t)) := by
    calc
      b i * z i * regCarlsonRIntegral t (Function.update b i (b i + 1)) z =
          z i * (b i * regDirichletIntegral (Function.update b i (b i + 1))
            (fun u ↦ carlsonAffineForm z u ^ t)) := by
              simp only [regCarlsonRIntegral, regCarlsonDirichletAverage]
              ring
      _ = z i * regDirichletIntegral b
          (fun u ↦ (u i : ℂ) * carlsonAffineForm z u ^ t) := by
            rw [mul_regDirichletIntegral_update_add_one hb]
      _ = regDirichletIntegral b
          (fun u ↦ z i * ((u i : ℂ) * carlsonAffineForm z u ^ t)) := by
            have hfun :
                ((Complex.ofReal ∘ fun u : ι → ℝ ↦ u i) *
                    fun u ↦ carlsonAffineForm z u ^ t) =
                  fun u ↦ (u i : ℂ) * carlsonAffineForm z u ^ t := by
              funext u
              rfl
            rw [← hfun]
            exact (regDirichletIntegral_smul b
              (fun u ↦ (u i : ℂ) * carlsonAffineForm z u ^ t) (z i)).symm
  rw [show (∑ i, b i * z i *
      regCarlsonRIntegral t (Function.update b i (b i + 1)) z) =
      ∑ i, regDirichletIntegral b
        (fun u ↦ z i * ((u i : ℂ) * carlsonAffineForm z u ^ t)) by
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i]
  unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u hu
    dsimp only
    have hne : carlsonAffineForm z u ≠ 0 :=
      slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu)
    rw [cpow_add _ _ hne, cpow_one]
    rw [← Finset.mul_sum]
    congr 1
    rw [show ∑ i, z i * ((u i : ℂ) * carlsonAffineForm z u ^ t) =
        (∑ i, (u i : ℂ) * z i) * carlsonAffineForm z u ^ t by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    unfold carlsonAffineForm
    ring
  · intro i _
    exact integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const.mul
        ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hpow))

/-- The tangential contiguous relation for the power kernel, including equal indices. -/
theorem regCarlsonRIntegral_tangent (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) (i j : ι) :
    (z i - z j) * (t *
      regCarlsonRIntegral (t - 1) (addDirichletUnit (addDirichletUnit b i) j) z) =
      regCarlsonRIntegral t (addDirichletUnit b i) z -
        regCarlsonRIntegral t (addDirichletUnit b j) z := by
  by_cases hij : i = j
  · subst j
    simp
  have hpow : AnalyticOnNhd ℂ (fun w : ℂ ↦ w ^ t) carlsonRightHalfPlane := by
    intro w hw
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_slitPlane.eventually_mem
      (carlsonRightHalfPlane_subset_slitPlane hw)] with v hv
    exact differentiableAt_id.cpow_const hv
  have hderiv (q : ι → ℂ) :
      regCarlsonDirichletAverage q z (deriv (fun w : ℂ ↦ w ^ t)) =
        t * regCarlsonRIntegral (t - 1) q z := by
    rw [regCarlsonRIntegral, ← regCarlsonDirichletAverage_const_mul]
    apply regDirichletIntegral_congr
    intro u hu
    exact Complex.deriv_cpow_const (carlsonAffineForm_mem_slitPlane hz hu)
  have H := regCarlsonDirichletAverage_tangent convex_carlsonRightHalfPlane hpow hb
    (Set.range_subset_iff.mpr hz) i j hij
  rw [hderiv] at H
  have hcomm : addDirichletUnit (addDirichletUnit b j) i =
      addDirichletUnit (addDirichletUnit b i) j := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit, Function.update_apply]
  simpa only [hcomm, regCarlsonRIntegral] using H

private lemma sum_addDirichletUnit_mul (b : ι → ℂ) (i : ι) (f : ι → ℂ) :
    ∑ j, addDirichletUnit b i j * f j = (∑ j, b j * f j) + f i := by
  have hterm (j : ι) : addDirichletUnit b i j * f j =
      b j * f j + if j = i then f i else 0 := by
    by_cases hji : j = i <;> simp [addDirichletUnit, hji, add_mul]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp

/-- Carlson's third associated-function relation 5.9-5, equation (7), in regularized form.
No parameter is lowered, so the ordinary convergence hypothesis suffices. -/
theorem regCarlsonRIntegral_eq_update_add_one (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    regCarlsonRIntegral t b z =
      ((∑ j, b j) + t) * regCarlsonRIntegral t (addDirichletUnit b i) z -
        t * z i * regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z := by
  let q := addDirichletUnit b i
  let F : ι → ℂ := fun j ↦ regCarlsonRIntegral (t - 1) (addDirichletUnit q j) z
  have hq := addDirichletUnit_mem_mvBetaConvergent hb i
  have hfirst := regCarlsonRIntegral_eq_sum_update_add_one (t - 1) hq hz
  have hsecond := regCarlsonRIntegral_add_one_eq_sum_mul_update (t - 1) hq hz
  change regCarlsonRIntegral (t - 1) q z = ∑ j, q j * F j at hfirst
  change regCarlsonRIntegral (t - 1 + 1) q z = ∑ j, q j * z j * F j at hsecond
  rw [sub_add_cancel] at hsecond
  rw [sum_addDirichletUnit_mul b i F] at hfirst
  simp_rw [mul_assoc] at hsecond
  rw [sum_addDirichletUnit_mul b i (fun j ↦ z j * F j)] at hsecond
  have htangent := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ ↦ congrArg (fun w : ℂ ↦ b j * w)
      (regCarlsonRIntegral_tangent t hb hz i j))
  change (∑ j, b j * ((z i - z j) * (t * F j))) =
    ∑ j, b j * (regCarlsonRIntegral t q z -
      regCarlsonRIntegral t (addDirichletUnit b j) z) at htangent
  have hsum := regCarlsonRIntegral_eq_sum_update_add_one t hb hz
  change regCarlsonRIntegral t b z =
    ∑ j, b j * regCarlsonRIntegral t (addDirichletUnit b j) z at hsum
  have hleft : (∑ j, b j * ((z i - z j) * (t * F j))) =
      t * z i * (∑ j, b j * F j) - t * ∑ j, b j * (z j * F j) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hleft] at htangent
  simp_rw [mul_sub] at htangent
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hsum] at htangent
  change regCarlsonRIntegral t b z =
    ((∑ j, b j) + t) * regCarlsonRIntegral t q z -
      t * z i * regCarlsonRIntegral (t - 1) q z
  linear_combination t * z i * hfirst - t * hsecond + htangent

/-- Carlson's second differential relation 5.9-6, equation (10), in regularized form.
The first relation, equation (9), is `carlsonPartialDeriv_regCarlsonRIntegral`. -/
theorem mul_carlsonPartialDeriv_add_mul_regCarlsonRIntegral
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    z i * carlsonPartialDeriv i (regCarlsonRIntegral t b) z +
      b i * regCarlsonRIntegral t b z =
        b i * ((∑ j, b j) + t) * regCarlsonRIntegral t (addDirichletUnit b i) z := by
  rw [carlsonPartialDeriv_regCarlsonRIntegral t hb hz]
  linear_combination b i * regCarlsonRIntegral_eq_update_add_one t hb hz i

/-- Carlson's translation differential identity, the first equation of Theorem 5.9-2. -/
theorem sum_carlsonPartialDeriv_regCarlsonRIntegral
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    ∑ i, carlsonPartialDeriv i (regCarlsonRIntegral t b) z =
      t * regCarlsonRIntegral (t - 1) b z := by
  simp_rw [carlsonPartialDeriv_regCarlsonRIntegral t hb hz, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact (regCarlsonRIntegral_eq_sum_update_add_one (t - 1) hb hz).symm

/-- Carlson's Euler differential identity, the second equation of Theorem 5.9-2, for the
native regularized `R` integral. -/
theorem sum_mul_carlsonPartialDeriv_regCarlsonRIntegral
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    ∑ i, z i * carlsonPartialDeriv i (regCarlsonRIntegral t b) z =
      t * regCarlsonRIntegral t b z := by
  simp_rw [carlsonPartialDeriv_regCarlsonRIntegral t hb hz]
  calc
    ∑ i, z i * (t * b i *
        regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z) =
        t * ∑ i, b i * z i *
          regCarlsonRIntegral (t - 1) (addDirichletUnit b i) z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = t * regCarlsonRIntegral ((t - 1) + 1) b z := by
      congr 1
      simpa [addDirichletUnit] using
        (regCarlsonRIntegral_add_one_eq_sum_mul_update (t - 1) hb hz).symm
    _ = t * regCarlsonRIntegral t b z := by ring_nf

private lemma analyticAt_regCarlsonRContinued_shift (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (b : ι → ℂ) (i : ι) :
    AnalyticAt ℂ (fun c ↦ regCarlsonRContinued t z hz (addDirichletUnit c i)) b := by
  have hshift : AnalyticAt ℂ (fun c : ι → ℂ ↦ addDirichletUnit c i) b := by
    apply AnalyticAt.pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [addDirichletUnit] using!
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).add analyticAt_const
    · simpa [addDirichletUnit, hji] using!
        (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt b
  exact ((analyticOnNhd_regCarlsonRContinued t hz) _ (Set.mem_univ _)).comp_of_eq hshift rfl

/-- The first associated relation holds for the continued function at every complex
Dirichlet parameter, including points outside the native convergence region. -/
theorem regCarlsonRContinued_eq_sum_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued t z hz b =
      ∑ i, b i * regCarlsonRContinued t z hz (addDirichletUnit b i) := by
  have hright : AnalyticOnNhd ℂ
      (fun b : ι → ℂ ↦ ∑ i, b i * regCarlsonRContinued t z hz (addDirichletUnit b i))
      Set.univ := by
    intro b _
    exact Finset.analyticAt_fun_sum _ fun i _ ↦
      ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).mul
        (analyticAt_regCarlsonRContinued_shift t hz b i)
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonRContinued t hz) hright ?_) b
  intro c hc
  simp_rw [regCarlsonRContinued_eq_integral t hz hc,
    regCarlsonRContinued_eq_integral t hz (addDirichletUnit_mem_mvBetaConvergent hc _)]
  exact regCarlsonRIntegral_eq_sum_update_add_one t hc hz

/-- The second associated relation extends to all complex Dirichlet parameters. -/
theorem regCarlsonRContinued_add_one_eq_sum_mul_addDirichletUnit
    (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued (t + 1) z hz b =
      ∑ i, b i * z i * regCarlsonRContinued t z hz (addDirichletUnit b i) := by
  have hright : AnalyticOnNhd ℂ
      (fun b : ι → ℂ ↦ ∑ i, b i * z i * regCarlsonRContinued t z hz (addDirichletUnit b i))
      Set.univ := by
    intro b _
    exact Finset.analyticAt_fun_sum _ fun i _ ↦
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).mul analyticAt_const).mul
        (analyticAt_regCarlsonRContinued_shift t hz b i)
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonRContinued (t + 1) hz) hright ?_) b
  intro c hc
  simp_rw [regCarlsonRContinued_eq_integral (t + 1) hz hc,
    regCarlsonRContinued_eq_integral t hz (addDirichletUnit_mem_mvBetaConvergent hc _)]
  exact regCarlsonRIntegral_add_one_eq_sum_mul_update t hc hz

/-- Carlson's third associated relation holds everywhere in the Dirichlet parameters
after regularization; no division by the total parameter or by the exponent is needed. -/
theorem regCarlsonRContinued_eq_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    regCarlsonRContinued t z hz b =
      ((∑ j, b j) + t) * regCarlsonRContinued t z hz (addDirichletUnit b i) -
        t * z i * regCarlsonRContinued (t - 1) z hz (addDirichletUnit b i) := by
  have hright : AnalyticOnNhd ℂ (fun b : ι → ℂ ↦
      ((∑ j, b j) + t) * regCarlsonRContinued t z hz (addDirichletUnit b i) -
        t * z i * regCarlsonRContinued (t - 1) z hz (addDirichletUnit b i)) Set.univ := by
    intro b _
    have hsum : AnalyticAt ℂ (fun c : ι → ℂ ↦ ∑ j, c j) b :=
      Finset.analyticAt_fun_sum _ fun j _ ↦
        (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt b
    exact ((hsum.add analyticAt_const).mul
      (analyticAt_regCarlsonRContinued_shift t hz b i)).sub
        (analyticAt_const.mul (analyticAt_regCarlsonRContinued_shift (t - 1) hz b i))
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonRContinued t hz) hright ?_) b
  intro c hc
  simp_rw [regCarlsonRContinued_eq_integral t hz hc,
    regCarlsonRContinued_eq_integral t hz (addDirichletUnit_mem_mvBetaConvergent hc i),
    regCarlsonRContinued_eq_integral (t - 1) hz (addDirichletUnit_mem_mvBetaConvergent hc i)]
  exact regCarlsonRIntegral_eq_update_add_one t hc hz i

/-- Positive-real scaling commutes with the principal complex power. -/
theorem ofReal_pos_mul_cpow (t w : ℂ) {a : ℝ} (ha : 0 < a) (hw : w ≠ 0) :
    ((a : ℂ) * w) ^ t = (a : ℂ) ^ t * w ^ t := by
  have hloga : log (a : ℂ) = (Real.log a : ℂ) := by
    simpa using (log_ofReal_mul ha (x := 1) one_ne_zero)
  rw [cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hw)]
  rw [mul_comm (a : ℂ) w, log_mul_ofReal a ha w hw, add_mul, exp_add]
  rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')]
  rw [cpow_def_of_ne_zero hw]
  rw [hloga]

/-- Pointwise homogeneity of Carlson's power kernel for positive real scaling. -/
theorem cpow_carlsonAffineForm_smul (t : ℂ) {a : ℝ} (ha : 0 < a)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    carlsonAffineForm (fun i ↦ (a : ℂ) * z i) u ^ t =
      (a : ℂ) ^ t * carlsonAffineForm z u ^ t := by
  rw [show carlsonAffineForm (fun i ↦ (a : ℂ) * z i) u =
      (a : ℂ) * carlsonAffineForm z u by
    unfold carlsonAffineForm
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  exact ofReal_pos_mul_cpow t _ ha
    (slitPlane_ne_zero (carlsonAffineForm_mem_slitPlane hz hu))

/-- Carlson's homogeneity formula 5.9-3 for the native regularized integral, stated with
positive real scaling so that Mathlib's principal branch is preserved. -/
theorem regCarlsonRIntegral_smul_of_pos (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {a : ℝ} (ha : 0 < a) :
    regCarlsonRIntegral t b (fun i ↦ (a : ℂ) * z i) =
      (a : ℂ) ^ t * regCarlsonRIntegral t b z := by
  unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u hu
  dsimp only
  rw [cpow_carlsonAffineForm_smul t ha hz hu]
  ring

/-- The corresponding unregularized homogeneity formula. -/
theorem carlsonRIntegral_smul_of_pos (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) {a : ℝ} (ha : 0 < a) :
    carlsonRIntegral t b (fun i ↦ (a : ℂ) * z i) =
      (a : ℂ) ^ t * carlsonRIntegral t b z := by
  unfold carlsonRIntegral
  rw [regCarlsonRIntegral_smul_of_pos t hz ha]
  ring

/-- Two factors in the right half-plane have compatible principal logarithms. -/
theorem mul_cpow_of_re_pos {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) (t : ℂ) :
    (a * w) ^ t = a ^ t * w ^ t := by
  have ha0 := slitPlane_ne_zero (carlsonRightHalfPlane_subset_slitPlane ha)
  have hw0 := slitPlane_ne_zero (carlsonRightHalfPlane_subset_slitPlane hw)
  have haarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hwarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have hlog : log (a * w) = log a + log w :=
    Complex.log_mul ha0 hw0 ⟨by linarith [haarg.1, hwarg.1],
      by linarith [haarg.2, hwarg.2]⟩
  rw [cpow_def_of_ne_zero (mul_ne_zero ha0 hw0), cpow_def_of_ne_zero ha0,
    cpow_def_of_ne_zero hw0, hlog, add_mul, exp_add]

/-- Complex homogeneity on the right half-plane, with explicit principal-branch control.
The scaled variables need not themselves be in the right half-plane. -/
theorem regCarlsonRIntegral_smul_of_re_pos (t : ℂ) {a : ℂ} (ha : 0 < a.re)
    {b z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRIntegral t b (fun i => a * z i) =
      a ^ t * regCarlsonRIntegral t b z := by
  unfold regCarlsonRIntegral regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u hu
  dsimp only
  have hform : carlsonAffineForm (fun i => a * z i) u = a * carlsonAffineForm z u := by
    simp only [carlsonAffineForm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hform, mul_cpow_of_re_pos ha (carlsonAffineForm_mem_rightHalfPlane hz hu)]
  ring

/-- Unregularized complex homogeneity with the same principal-branch hypotheses. -/
theorem carlsonRIntegral_smul_of_re_pos (t : ℂ) {a : ℂ} (ha : 0 < a.re)
    {b z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    carlsonRIntegral t b (fun i => a * z i) = a ^ t * carlsonRIntegral t b z := by
  unfold carlsonRIntegral
  rw [regCarlsonRIntegral_smul_of_re_pos t ha hz]
  ring

end DirichletTransform
end CarlsonR
