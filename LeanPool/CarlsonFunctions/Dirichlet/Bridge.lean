/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Real
public import LeanPool.CarlsonFunctions.Dirichlet.Complex

/-!
# Compatibility of real and complex Dirichlet integrals

At positive real parameters the normalized complex integral is a probability expectation;
the regularized integral differs by the Gamma factor of the total parameter.
These identities hold for arbitrary integrands as identities of totalized Bochner integrals.
They neither require nor invoke analytic continuation.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The complex multivariate beta function specializes to the real one. -/
@[simp] theorem mvBeta_ofReal (b : ι → ℝ) :
    mvBeta (fun i ↦ (b i : ℂ)) = (mvRealBeta b : ℂ) := by
  simp [mvBeta, mvRealBeta, ← Complex.ofReal_sum, Gamma_ofReal]

end Complex

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- For positive real parameters, the regularized complex density is the real Dirichlet
probability density divided by the Gamma factor of the total parameter. -/
theorem regDirichletDensity_ofReal_eq [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (u : ι → ℝ) :
    regDirichletDensity (fun i ↦ (b i : ℂ)) u =
      (dirichletPdfReal b u : ℂ) / Gamma (∑ i, (b i : ℂ)) := by
  by_cases hu : u ∈ stdSimplexInterior
  · rw [regDirichletDensity, Set.indicator_of_mem hu]
    rw [dirichletPdfReal, Set.indicator_of_mem hu]
    have hexp (i : ι) : (b i : ℂ) - 1 = ((b i - 1 : ℝ) : ℂ) := by norm_num
    have hpow (i : ι) : (u i : ℂ) ^ ((b i - 1 : ℝ) : ℂ) =
        (u i ^ (b i - 1) : ℝ) :=
      (Complex.ofReal_cpow (le_of_lt (hu.2 i)) _).symm
    simp_rw [hexp, hpow, Complex.Gamma_ofReal]
    rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, ← Complex.ofReal_prod]
    rw [show Gamma (∑ i, (b i : ℂ)) = (Real.Gamma (∑ i, b i) : ℂ) by
      rw [← Complex.ofReal_sum, Complex.Gamma_ofReal]]
    simp only [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_div]
    unfold mvRealBeta
    have hprod : (∏ i, Real.Gamma (b i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ ne_of_gt (Real.Gamma_pos_of_pos (hb i))
    have hsum : Real.Gamma (∑ i, b i) ≠ 0 := by
      apply ne_of_gt
      exact Real.Gamma_pos_of_pos
        (Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty)
    have hprodC : (∏ i, (Real.Gamma (b i) : ℂ)) ≠ 0 := by
      simpa only [← Complex.ofReal_prod, Complex.ofReal_ne_zero] using hprod
    have hsumC : (Real.Gamma (∑ i, b i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsum
    rw [Complex.ofReal_div]
    field_simp [hprodC, hsumC]
  · simp [regDirichletDensity, dirichletPdfReal, hu]

end DirichletTransform

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- At positive real parameters the normalized complex density is the real probability
density, regarded as complex-valued. -/
theorem complexDirichletDensity_ofReal [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (u : ι → ℝ) :
    complexDirichletDensity (fun i ↦ (b i : ℂ)) u = (dirichletPdfReal b u : ℂ) := by
  have hgamma : Gamma (∑ i, (b i : ℂ)) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent (fun i ↦ hb i))
  rw [complexDirichletDensity, DirichletTransform.regDirichletDensity_ofReal_eq hb]
  field_simp

/-- The normalized native complex Dirichlet integral is a probability expectation at
positive real parameters. -/
theorem complexDirichletIntegral_ofReal [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (f : (ι → ℝ) → ℂ) :
    complexDirichletIntegral (fun i ↦ (b i : ℂ)) f = ∫ u, f u ∂dirichletMeasure b := by
  rw [DirichletTransform.integral_dirichletMeasure_complex hb]
  unfold complexDirichletIntegral
  apply integral_congr_ae
  filter_upwards with u
  rw [complexDirichletDensity_ofReal hb]

/-- The regularized native complex Dirichlet integral is the probability expectation
divided by the Gamma factor of the total parameter. -/
theorem regDirichletIntegral_ofReal [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (f : (ι → ℝ) → ℂ) :
    regDirichletIntegral (fun i ↦ (b i : ℂ)) f =
      (∫ u, f u ∂dirichletMeasure b) / Gamma (∑ i, (b i : ℂ)) := by
  rw [DirichletTransform.integral_dirichletMeasure_complex hb]
  unfold regDirichletIntegral
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with u
  rw [DirichletTransform.regDirichletDensity_ofReal_eq hb]
  ring

/-- Real-valued probability expectations can be recovered by specializing the complex
Dirichlet integral in both its parameters and its integrand. -/
theorem complexDirichletIntegral_ofReal_ofReal [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (f : (ι → ℝ) → ℝ) :
    complexDirichletIntegral (fun i ↦ (b i : ℂ)) (fun u ↦ (f u : ℂ)) =
      ((∫ u, f u ∂dirichletMeasure b) : ℂ) := by
  rw [complexDirichletIntegral_ofReal hb, integral_complex_ofReal]

end ProbabilityTheory

end
