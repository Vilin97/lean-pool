/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.CircleIntegral
import LeanPool.PoincareThreeBody.ChapterVILatticeReduction

/-!
# Finite Laurent coefficient extraction by a complex contour

Poincaré's §94 introduces a one-variable Laurent series and extracts its coefficients by
integrating around a circle.  This file verifies that contour extraction for finite Laurent
polynomials.  It is the complex-analytic counterpart of the finite lattice reduction in
`ChapterVILatticeReduction`.

The infinite-series theorem below justifies exchanging the contour integral with a Laurent series
under an explicit weighted absolute-summability hypothesis. The remaining §94 work is to prove
that hypothesis for Poincaré's perturbing series on its intended annulus.
-/

noncomputable section

open Complex
open Filter
open scoped BigOperators Real Topology

namespace LeanPool.PoincareThreeBody

/-- The circle integral of an integer monomial is `2 * pi * I` in degree `-1` and zero in every
other degree. -/
theorem chapterVI_circleIntegral_zpow
    (exponent : ℤ) {radius : ℝ} (hradius : radius ≠ 0) :
    (∮ z in C(0, radius), z ^ exponent) =
      if exponent = -1 then 2 * Real.pi * I else 0 := by
  by_cases hexponent : exponent = -1
  · subst exponent
    rw [if_pos rfl]
    simp only [zpow_neg_one]
    simpa only [sub_zero] using circleIntegral.integral_sub_center_inv 0 hradius
  · rw [if_neg hexponent]
    simpa only [sub_zero] using
      circleIntegral.integral_sub_zpow_of_ne hexponent 0 0 radius

/-- A finite Laurent coefficient table. -/
abbrev ChapterVIFiniteLaurentTable := ℤ →₀ ℂ

/-- The standard coefficient-extraction integrand, already multiplied by `z⁻ᵏ⁻¹`. -/
def chapterVIFiniteCoefficientIntegrand
    (coefficients : ChapterVIFiniteLaurentTable) (coefficientIndex : ℤ) (z : ℂ) : ℂ :=
  coefficients.sum fun exponent coefficient ↦
    coefficient * z ^ (exponent - coefficientIndex - 1)

/-- Every monomial in the finite coefficient integrand is integrable on a nonzero circle. -/
theorem circleIntegrable_chapterVIFiniteCoefficientMonomial
    (coefficient : ℂ) (exponent coefficientIndex : ℤ)
    {radius : ℝ} (hradius : radius ≠ 0) :
    CircleIntegrable
      (fun z : ℂ ↦ coefficient * z ^ (exponent - coefficientIndex - 1)) 0 radius := by
  have hzero : (0 : ℂ) ∉ Metric.sphere 0 |radius| := by
    simp only [Metric.mem_sphere, dist_self]
    exact (abs_ne_zero.mpr hradius).symm
  have hpower : CircleIntegrable
      (fun z : ℂ ↦ (z - 0) ^ (exponent - coefficientIndex - 1)) 0 radius := by
    rw [circleIntegrable_sub_zpow_iff]
    exact Or.inr (Or.inr hzero)
  simpa only [sub_zero, smul_eq_mul] using
    (hpower.const_fun_smul (a := coefficient))

/-- The normalized circle integral extracts exactly one coefficient from a finite Laurent
polynomial.  This is the finite contour calculation underlying Poincaré's `Phi(z)` in §94. -/
theorem chapterVI_finiteLaurent_circleCoefficient
    (coefficients : ChapterVIFiniteLaurentTable) (coefficientIndex : ℤ)
    {radius : ℝ} (hradius : radius ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, radius),
          chapterVIFiniteCoefficientIntegrand coefficients coefficientIndex z) =
      coefficients coefficientIndex := by
  classical
  have hintegral :
      (∮ z in C(0, radius),
        chapterVIFiniteCoefficientIntegrand coefficients coefficientIndex z) =
        coefficients coefficientIndex * (2 * Real.pi * I) := by
    unfold chapterVIFiniteCoefficientIntegrand
    simp only [Finsupp.sum]
    rw [circleIntegral.integral_fun_sum]
    · simp_rw [circleIntegral.integral_const_mul, chapterVI_circleIntegral_zpow _ hradius]
      have hindex : ∀ exponent : ℤ,
          exponent - coefficientIndex - 1 = -1 ↔ exponent = coefficientIndex := by
        intro exponent
        omega
      simp_rw [hindex]
      by_cases hmem : coefficientIndex ∈ coefficients.support
      · rw [Finset.sum_eq_single coefficientIndex]
        · simp
        · intro exponent hexponent hne
          simp [hne]
        · intro hnotmem
          exact (hnotmem hmem).elim
      · have hcoefficient : coefficients coefficientIndex = 0 :=
          Finsupp.notMem_support_iff.mp hmem
        rw [hcoefficient, zero_mul]
        apply Finset.sum_eq_zero
        intro exponent hexponent
        have hne : exponent ≠ coefficientIndex := by
          intro hequal
          exact hmem (hequal ▸ hexponent)
        simp [hne]
    · intro exponent hexponent
      exact circleIntegrable_chapterVIFiniteCoefficientMonomial
        (coefficients exponent) exponent coefficientIndex hradius
  rw [hintegral]
  have hnormalization : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [mul_comm (coefficients coefficientIndex), ← mul_assoc,
    inv_mul_cancel₀ hnormalization, one_mul]

/-- After Poincaré's shear reduction, the same contour extracts the requested coefficient of the
resulting finite one-variable Laurent polynomial. -/
theorem chapterVIReducedCoefficient_circleIntegral
    (coefficients : ChapterVIFiniteCoefficientTable) (a c : ℤ) (parameter : ℂ)
    (coefficientIndex : ℤ)
    {radius : ℝ} (hradius : radius ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, radius),
          chapterVIFiniteCoefficientIntegrand
            (chapterVIReducedCoefficientTable coefficients a c parameter) coefficientIndex z) =
      chapterVIReducedCoefficientTable coefficients a c parameter coefficientIndex :=
  chapterVI_finiteLaurent_circleCoefficient _ _ hradius

/-- A Laurent-series coefficient integrand. The summability assumption below ensures that this
series converges uniformly on the chosen circle. -/
def chapterVILaurentCoefficientIntegrand
    (coefficients : ℤ → ℂ) (coefficientIndex : ℤ) (z : ℂ) : ℂ :=
  ∑' exponent : ℤ, coefficients exponent * z ^ (exponent - coefficientIndex - 1)

/-- A circle integral commutes with a Laurent series when the monomial norms on that circle form
a summable majorant. This supplies the analytic infinite-series step in §94 under an explicit
absolute-convergence hypothesis. -/
theorem chapterVI_circleIntegral_laurent_tsum
    (coefficients : ℤ → ℂ) (coefficientIndex : ℤ)
    {radius : ℝ} (hradius : 0 < radius)
    (hsummable : Summable fun exponent : ℤ ↦
      ‖coefficients exponent‖ * radius ^ exponent) :
    (∮ z in C(0, radius),
        chapterVILaurentCoefficientIntegrand coefficients coefficientIndex z) =
      ∑' exponent : ℤ,
        ∮ z in C(0, radius),
          coefficients exponent * z ^ (exponent - coefficientIndex - 1) := by
  let term : ℤ → ℂ → ℂ := fun exponent z ↦
    coefficients exponent * z ^ (exponent - coefficientIndex - 1)
  let bound : ℤ → ℝ := fun exponent ↦
    ‖coefficients exponent‖ * radius ^ (exponent - coefficientIndex - 1)
  have hboundSummable : Summable bound := by
    have hscaled := hsummable.mul_right (radius ^ (-coefficientIndex - 1))
    apply hscaled.congr
    intro exponent
    simp only [bound]
    rw [mul_assoc, ← zpow_add₀ hradius.ne']
    congr 1
    ring_nf
  have htermBound : ∀ exponent z, z ∈ Metric.sphere (0 : ℂ) radius →
      ‖term exponent z‖ ≤ bound exponent := by
    intro exponent z hz
    simp only [term, bound, norm_mul, norm_zpow]
    rw [mem_sphere_zero_iff_norm.mp hz]
  have htermContinuous : ∀ exponent,
      ContinuousOn (term exponent) (Metric.sphere (0 : ℂ) radius) := by
    intro exponent
    apply continuousOn_const.mul
    apply continuousOn_id.zpow₀
    intro z hz
    apply Or.inl
    intro hzero
    change z = 0 at hzero
    subst z
    have := mem_sphere_zero_iff_norm.mp hz
    exact hradius.ne' (by simpa using this.symm)
  have hpartialContinuous : ∀ finite : Finset ℤ,
      ContinuousOn (fun z ↦ ∑ exponent ∈ finite, term exponent z)
        (Metric.sphere (0 : ℂ) radius) := by
    intro finite
    exact continuousOn_finsetSum finite fun exponent _ ↦ htermContinuous exponent
  have huniform : TendstoUniformlyOn
      (fun finite : Finset ℤ ↦ fun z ↦ ∑ exponent ∈ finite, term exponent z)
      (fun z ↦ ∑' exponent : ℤ, term exponent z) atTop
      (Metric.sphere (0 : ℂ) radius) :=
    tendstoUniformlyOn_tsum hboundSummable htermBound
  have hcircle := huniform.tendsto_circleIntegral_of_continuousOn hradius.le
    (Filter.Eventually.of_forall hpartialContinuous)
  have htermIntegrable : ∀ exponent,
      CircleIntegrable (term exponent) 0 radius := by
    intro exponent
    exact circleIntegrable_chapterVIFiniteCoefficientMonomial
      (coefficients exponent) exponent coefficientIndex hradius.ne'
  have hintegralSummable : Summable fun exponent : ℤ ↦
      ∮ z in C(0, radius), term exponent z := by
    apply (hboundSummable.mul_left (2 * Real.pi * radius)).of_norm_bounded
    intro exponent
    exact circleIntegral.norm_integral_le_of_norm_le_const hradius.le (htermBound exponent)
  have hpartialIntegral : ∀ finite : Finset ℤ,
      (∮ z in C(0, radius), ∑ exponent ∈ finite, term exponent z) =
        ∑ exponent ∈ finite, ∮ z in C(0, radius), term exponent z := by
    intro finite
    exact circleIntegral.integral_fun_sum (s := finite) fun exponent _ ↦
      htermIntegrable exponent
  have hcircle' : Tendsto
      (fun finite : Finset ℤ ↦
        ∑ exponent ∈ finite, ∮ z in C(0, radius), term exponent z)
      atTop
      (𝓝 (∮ z in C(0, radius), ∑' exponent : ℤ, term exponent z)) := by
    convert hcircle using 1
    funext finite
    exact (hpartialIntegral finite).symm
  change (∮ z in C(0, radius), ∑' exponent : ℤ, term exponent z) = _
  exact tendsto_nhds_unique hcircle' hintegralSummable.hasSum

/-- Under absolute convergence on a positive-radius circle, Poincaré's normalized contour
extracts the requested coefficient from an infinite Laurent series. -/
theorem chapterVI_laurentSeries_circleCoefficient
    (coefficients : ℤ → ℂ) (coefficientIndex : ℤ)
    {radius : ℝ} (hradius : 0 < radius)
    (hsummable : Summable fun exponent : ℤ ↦
      ‖coefficients exponent‖ * radius ^ exponent) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, radius),
          chapterVILaurentCoefficientIntegrand coefficients coefficientIndex z) =
      coefficients coefficientIndex := by
  rw [chapterVI_circleIntegral_laurent_tsum coefficients coefficientIndex hradius hsummable]
  simp_rw [circleIntegral.integral_const_mul,
    chapterVI_circleIntegral_zpow _ hradius.ne']
  have hindex : ∀ exponent : ℤ,
      exponent - coefficientIndex - 1 = -1 ↔ exponent = coefficientIndex := by
    intro exponent
    omega
  simp_rw [hindex]
  rw [tsum_eq_single coefficientIndex]
  · simp only [if_pos, mul_assoc]
    have hnormalization : (2 * Real.pi * I : ℂ) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    field_simp
  · intro exponent hne
    simp [hne]

end LeanPool.PoincareThreeBody
