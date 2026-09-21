/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Complex
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Polynomial Dirichlet transforms
-/

open Complex MeasureTheory ProbabilityTheory MeasureTheory.Measure Set Filter
open scoped Topology

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- A shorthand for the product of Pochhammer polynomials associated to a
multi-index. Since `ι` is finite, monomial multi-indices are represented by ordinary functions
`ι → ℕ`; the finitely supported indices used by `MvPolynomial` coerce to this type. -/
def mvPochhammer (b : ι → ℂ) (m : ι → ℕ) : ℂ :=
    ∏ i, (ascPochhammer ℂ (m i)).eval (b i)

/-- The regularized Dirichlet transform of the monomial with multi-index `m`.
This is an entire function of `b`. -/
def regDirichletMonomialTransform (m : ι → ℕ) (b : ι → ℂ) : ℂ :=
  mvPochhammer b m * (Gamma (∑ i, (b i + m i : ℂ)))⁻¹

/-- The explicit Pochhammer--Gamma formula for the regularized transform of a monomial.
This theorem exposes the useful formula while keeping the shorthand `mvPochhammer` local to
this file. -/
theorem regDirichletMonomialTransform_eq (m : ι → ℕ) (b : ι → ℂ) :
    regDirichletMonomialTransform m b =
      (∏ i, (ascPochhammer ℂ (m i)).eval (b i)) *
        (Gamma (∑ i, (b i + m i : ℂ)))⁻¹ := by
  rfl

/-- The regularized transform of the constant monomial is the reciprocal Gamma factor. -/
@[simp] theorem regDirichletMonomialTransform_zero (b : ι → ℂ) :
    regDirichletMonomialTransform (fun _ ↦ 0) b = (Gamma (∑ i, b i))⁻¹ := by
  rw [regDirichletMonomialTransform_eq]
  simp

/-- Multiplying an integrand by a monomial shifts its Dirichlet parameters. -/
theorem regDirichletIntegral_monomial_mul
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (m : ι → ℕ) (f : (ι → ℝ) → ℂ) :
    regDirichletIntegral b (fun u ↦ (∏ i, (u i : ℂ) ^ m i) * f u) =
      mvPochhammer b m * regDirichletIntegral (fun i ↦ b i + m i) f := by
  classical
  by_cases hι : Nonempty ι
  swap
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    simp [regDirichletIntegral, MeasureTheory.Measure.stdSimplexMeasure_empty]
  let _ := hι
  let b' : ι → ℂ := fun i ↦ b i + m i
  have hbpos (i : ι) : 0 < (b i).re := by
    simpa [mvBetaConvergent] using hb i
  have hb' : b' ∈ mvBetaConvergent := by
    intro i
    dsimp [b']
    simpa only [add_re, ofReal_natCast] using
      add_pos_of_pos_of_nonneg (hbpos i) (Nat.cast_nonneg (m i))
  have hgamma (i : ι) :
      Gamma (b' i) = (ascPochhammer ℂ (m i)).eval (b i) * Gamma (b i) := by
    dsimp [b']
    apply (div_eq_iff (Gamma_ne_zero_of_re_pos (hbpos i))).mp
    exact Gamma_add_nat_div_Gamma_eq (b i) (fun k h ↦ by
      have hi := hbpos i
      rw [h] at hi
      simp only [neg_re] at hi
      exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg k))) hi)
  have hpoch (i : ι) : (ascPochhammer ℂ (m i)).eval (b i) ≠ 0 := by
    intro hzero
    have hgzero : Gamma (b' i) = 0 := by rw [hgamma, hzero, zero_mul]
    exact (Gamma_ne_zero_of_re_pos (hb' i)) hgzero
  have hae := MeasureTheory.Measure.ae_zero_lt_of_mem_stdSimplex (ι := ι)
  have hfun :
      (fun u : ι → ℝ ↦ regDirichletDensity b u * ∏ i, (u i : ℂ) ^ m i)
        =ᵐ[(MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)]
      fun u ↦ mvPochhammer b m * regDirichletDensity b' u := by
    have hmem := self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure) (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    filter_upwards [hmem, hae] with u hu hupos
    have hinter : u ∈ stdSimplexInterior := ⟨hu, hupos⟩
    rw [regDirichletDensity, regDirichletDensity,
      Set.indicator_of_mem hinter, Set.indicator_of_mem hinter]
    unfold mvPochhammer
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [hgamma]
    have hu0 : (u i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hupos i).ne'
    rw [show b' i - 1 = (b i - 1) + m i by simp [b']; ring,
      cpow_add _ _ hu0]
    rw [cpow_natCast]
    field_simp [hpoch i]
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hfun] with u hu
  simpa only [mul_assoc] using congrArg (· * f u) hu

/-- On its domain of definition the regularized integral of a monomial equals its
explicit Pochhammer--Gamma transform. -/
theorem regDirichletIntegral_monomial
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (m : ι → ℕ) :
    regDirichletIntegral b (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ m i) =
      regDirichletMonomialTransform m b := by
  have hb' : (fun i ↦ b i + (m i : ℂ)) ∈ mvBetaConvergent := by
    intro i
    simpa only [add_re, natCast_re] using
      add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg (m i))
  simpa [regDirichletMonomialTransform, regDirichletIntegral,
    regDirichletIntegral_normalization _ hb'] using
    regDirichletIntegral_monomial_mul hb m (fun _ ↦ 1)

/-- Evaluation of a multivariate polynomial as the sum of its monomial terms. -/
private lemma eval_MvPolynomial_eq_sum_monomials (p : MvPolynomial ι ℂ) (x : ι → ℂ) :
    p.eval x = ∑ m ∈ p.support, p.coeff m * ∏ i, x i ^ m i := by
  calc
    p.eval x = MvPolynomial.eval x
        (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
          rw [← MvPolynomial.as_sum p]
    _ = ∑ m ∈ p.support, MvPolynomial.eval x
        (MvPolynomial.monomial m (p.coeff m)) := MvPolynomial.eval_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [MvPolynomial.eval_monomial, m.prod_fintype]
      simp

/-- The `regDirichletMonomialTransform` extended linearly to multivariate polynomials. The
finitely supported indices in `p.support` are coerced to ordinary functions `ι → ℕ`. -/
def regDirichletMvPolynomialTransform (p : MvPolynomial ι ℂ) (b : ι → ℂ) : ℂ :=
  ∑ m ∈ p.support, p.coeff m * regDirichletMonomialTransform m b

/-- On its domain of definition the `regDirichletIntegral` of a multivariate polynomial equals
its regularized Dirichlet polynomial transform. -/
theorem regDirichletIntegral_mvPolynomial (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    (p : MvPolynomial ι ℂ) :
    regDirichletIntegral b (fun u : ι → ℝ ↦ p.eval fun i ↦ (u i : ℂ)) =
      regDirichletMvPolynomialTransform p b := by
  unfold regDirichletIntegral regDirichletMvPolynomialTransform
  simp_rw [eval_MvPolynomial_eq_sum_monomials p, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    have hfun : (fun u : ι → ℝ ↦ regDirichletDensity b u *
        (p.coeff m * ∏ i, (u i : ℂ) ^ m i)) =
        fun u ↦ p.coeff m * (regDirichletDensity b u * ∏ i, (u i : ℂ) ^ m i) := by
      funext u
      ring
    rw [hfun]
    rw [integral_const_mul]
    change p.coeff m * regDirichletIntegral b
      (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ m i) = _
    rw [regDirichletIntegral_monomial hb (m : ι → ℕ)]
  · intro m hm
    exact integrableOn_regDirichletDensity_mul b hb
      (by fun_prop)

/-- The regularized Dirichlet monomial transform is entire in all Dirichlet parameters. -/
theorem differentiable_regDirichletMonomialTransform (m : ι → ℕ) :
    Differentiable ℂ (regDirichletMonomialTransform m) := by
  unfold regDirichletMonomialTransform mvPochhammer
  have hnumerator : Differentiable ℂ fun b : ι → ℂ ↦
      ∏ i, (ascPochhammer ℂ (m i)).eval (b i) := by
    fun_prop
  have hsum : Differentiable ℂ fun b : ι → ℂ ↦ ∑ i, (b i + m i : ℂ) := by
    fun_prop
  exact hnumerator.mul (Complex.differentiable_one_div_Gamma.comp hsum)

/-- The regularized Dirichlet monomial transform is analytic in all Dirichlet parameters. -/
theorem analyticOnNhd_regDirichletMonomialTransform (m : ι → ℕ) :
    AnalyticOnNhd ℂ (regDirichletMonomialTransform m) Set.univ := by
  intro b _
  unfold regDirichletMonomialTransform mvPochhammer
  have hp : AnalyticAt ℂ (fun b : ι → ℂ ↦
      ∏ i, (ascPochhammer ℂ (m i)).eval (b i)) b := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (ascPochhammer ℂ (m i)))
      (b i) (Set.mem_univ _)).comp_of_eq
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b) rfl
  have hs : AnalyticAt ℂ (fun b : ι → ℂ ↦ ∑ i, (b i + m i : ℂ)) b := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).add analyticAt_const
  have hGammaInv : AnalyticAt ℂ (fun z : ℂ ↦ (Gamma z)⁻¹)
      (∑ i, (b i + m i : ℂ)) :=
    (analyticOnNhd_univ_iff_differentiable.mpr
      Complex.differentiable_one_div_Gamma) _ (Set.mem_univ _)
  exact hp.mul (hGammaInv.comp_of_eq hs rfl)
/-- The regularized Dirichlet polynomial transform is entire in all Dirichlet parameters. -/
theorem differentiable_regDirichletMvPolynomialTransform (p : MvPolynomial ι ℂ) :
    Differentiable ℂ (regDirichletMvPolynomialTransform p) := by
  classical
  have heq : regDirichletMvPolynomialTransform p =
      ∑ m ∈ p.support, fun b : ι → ℂ ↦ p.coeff m *
        regDirichletMonomialTransform m b := by
    funext b
    simp only [regDirichletMvPolynomialTransform, Finset.sum_apply]
  rw [heq]
  exact Differentiable.sum fun m _ ↦
    (differentiable_const _).mul
      (differentiable_regDirichletMonomialTransform (m : ι → ℕ))
/-- The regularized Dirichlet transform of a multivariate polynomial is analytic in all
Dirichlet parameters. -/
theorem analyticOnNhd_regDirichletMvPolynomialTransform (p : MvPolynomial ι ℂ) :
    AnalyticOnNhd ℂ (regDirichletMvPolynomialTransform p) Set.univ := by
  intro b _
  unfold regDirichletMvPolynomialTransform
  apply Finset.analyticAt_fun_sum
  intro m _
  exact analyticAt_const.mul
    (analyticOnNhd_regDirichletMonomialTransform (m : ι → ℕ) b (Set.mem_univ b))

end DirichletTransform

end
