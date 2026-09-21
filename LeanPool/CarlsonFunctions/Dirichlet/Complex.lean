/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Integral.Complex
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Interior

/-!
# Regularized complex Dirichlet integrals on the standard simplex

This file defines regularized complex Dirichlet densities and their associated integral
functionals. These are complex-valued densities, not measures in the sense of Mathlib's
nonnegative `Measure` type. Parameter analyticity is in `Dirichlet.Complex.Analytic`,
and continuation beyond the convergence domain is in `Dirichlet.Transform`.

## Main definitions and results

* `Complex.mvBeta_eq_integral`: the simplex integral representation of the multivariate Beta
  function.
* `regDirichletDensity`: the pointwise entire regularized Dirichlet density.
* `complexDirichletDensity`: the corresponding normalized complex density.
* `regDirichletIntegral`: integration against the regularized density.
* `complexDirichletIntegral`: integration against the normalized density.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex Fintype Filter MeasureTheory MeasureTheory.Measure
open scoped Topology

@[expose] public noncomputable section ComplexDirichlet

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The regularized Dirichlet density with parameters `b` on `stdSimplexInterior`. For each
fixed `u`, this is an entire function of `b`. -/
def regDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  stdSimplexInterior.indicator (fun u ↦ ∏ i, (u i : ℂ) ^ (b i - 1) / Gamma (b i)) u

/-- The normalized complex Dirichlet density with parameters `b` on
`stdSimplexInterior`. -/
def complexDirichletDensity (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  Gamma (∑ i, b i) * regDirichletDensity b u

/-- Simultaneously permuting the parameters and coordinates leaves the regularized Dirichlet
density unchanged. -/
theorem regDirichletDensity_perm (b : ι → ℂ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    regDirichletDensity (b ∘ σ) (u ∘ σ) = regDirichletDensity b u := by
  unfold regDirichletDensity
  have hinter := mem_stdSimplexInterior_perm σ u
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hinter.mpr hu)]
    simpa [Function.comp_def] using
      (Equiv.prod_comp σ
        (fun i ↦ (u i : ℂ) ^ (b i - 1) / Gamma (b i)))
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hinter.mp hu)]

/-- The regularized Dirichlet density is a measurable function. -/
theorem measurable_regDirichletDensity (b : ι → ℂ) :
    Measurable (regDirichletDensity b) := by
  unfold regDirichletDensity
  apply Measurable.indicator _ measurableSet_stdSimplexInterior
  fun_prop

/-- The regularized Dirichlet density integrated over the standard simplex. -/
theorem regDirichletIntegral_normalization (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, regDirichletDensity b u ∂stdSimplexMeasure =
    1 / Gamma (∑ i, b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [regDirichletDensity, stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      have hbpos (i : ι) : 0 < (b i).re := by
        simpa [mvBetaConvergent] using hb i
      have hgamma (i : ι) : Gamma (b i) ≠ 0 := Gamma_ne_zero_of_re_pos (hbpos i)
      have hprod_gamma : (∏ i, Gamma (b i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hgamma i)
      have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
      have hfun :
          regDirichletDensity b =ᵐ[stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)]
            fun u ↦ (∏ i, (u i : ℂ) ^ (b i - 1)) / ∏ i, Gamma (b i) := by
        have hmem := self_mem_ae_restrict
          (μ := stdSimplexMeasure) (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
        filter_upwards [hmem, hae] with u hu hupos
        rw [regDirichletDensity, Set.indicator_of_mem]
        · rw [Finset.prod_div_distrib]
        · exact ⟨hu, hupos⟩
      rw [integral_congr_ae hfun, integral_div, ← mvBeta_eq_integral hb]
      rw [mvBeta]
      field_simp

/-- Continuous functions are integrable over the standard simplex with respect to the
regularized Dirichlet density. -/
theorem integrableOn_regDirichletDensity_mul
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    IntegrableOn
      (fun u => regDirichletDensity b u * f u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      rw [stdSimplexMeasure_empty]
      simpa [IntegrableOn] using
        (integrable_zero_measure (f := fun u => regDirichletDensity b u * f u))
  | inr hι =>
    let _ := hι
    let K := Convexity.StdSimplex.coordinateSet ℝ ι
    obtain ⟨C, hC⟩ := bddAbove_def.mp
      ((Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).bddAbove_image hf.norm)
    have hf_le : ∀ u ∈ K, ‖f u‖ ≤ max C 0 := by
      intro u hu
      exact (hC _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)
    have hmono := Complex.integrableOn_mvBetaMonomial b hb
    have hgamma : IntegrableOn
        (fun u : ι → ℝ ↦ (max C 0 / ∏ i, ‖Gamma (b i)‖) *
          ‖∏ i, (u i : ℂ) ^ (b i - 1)‖) K stdSimplexMeasure :=
      hmono.norm.const_mul _
    apply Integrable.mono hgamma
    · exact (measurable_regDirichletDensity b).aestronglyMeasurable.mul
        (hf.aestronglyMeasurable (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet)
    · filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
          (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet,
          ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
      have hinter : u ∈ stdSimplexInterior := ⟨hu, hupos⟩
      simp only [regDirichletDensity, Set.indicator_of_mem hinter, norm_mul, norm_prod,
        norm_div]
      have hden_pos : 0 < ∏ i, ‖Gamma (b i)‖ := Finset.prod_pos fun i _ ↦
        norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (hb i))
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0),
        abs_of_nonneg (norm_nonneg _)]
      calc
        (∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ / ‖Gamma (b i)‖) * ‖f u‖ =
            ‖f u‖ / (∏ i, ‖Gamma (b i)‖) *
              ∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ := by
          rw [Finset.prod_div_distrib]
          field_simp
        _ ≤ (max C 0 / ∏ i, ‖Gamma (b i)‖) *
              ∏ i, ‖(u i : ℂ) ^ (b i - 1)‖ := by
          gcongr
          exact hf_le u hu

/-- Integration of function `f` over the standard simplex with respect to the regularized
Dirichlet density. This is the native, totalized Bochner integral, not its analytic
continuation outside the convergence domain. -/
def regDirichletIntegral (b : ι → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, regDirichletDensity b u * f u
    ∂stdSimplexMeasure

/-- The normalized complex Dirichlet integral, defined using the native density.
Outside the absolute-convergence domain this is a totalized Bochner integral, not an
analytic continuation. -/
def complexDirichletIntegral (b : ι → ℂ) (f : (ι → ℝ) → ℂ) : ℂ :=
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, complexDirichletDensity b u * f u ∂stdSimplexMeasure

/-- Native normalization and regularization differ by the Gamma factor of the total
parameter. No assertion of analytic continuation is involved. -/
theorem complexDirichletIntegral_eq_gamma_mul (b : ι → ℂ) (f : (ι → ℝ) → ℂ) :
    complexDirichletIntegral b f = Gamma (∑ i, b i) * regDirichletIntegral b f := by
  simp only [complexDirichletIntegral, complexDirichletDensity, regDirichletIntegral,
    mul_assoc, integral_const_mul]

/-- Regularization amounts to multiplying the native, totalized simplex Mellin integral by
the product of reciprocal Gamma factors. This identity does not require convergence. -/
theorem regDirichletIntegral_eq_prod_invGamma_mul
    (b : ι → ℂ) (f : (ι → ℝ) → ℂ) :
    regDirichletIntegral b f =
      (∏ i, (Gamma (b i))⁻¹) *
        ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, (∏ i, (u i : ℂ) ^ (b i - 1)) * f u
          ∂stdSimplexMeasure := by
  classical
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_mem_stdSimplexInterior (ι := ι)] with u hinter
  rw [regDirichletDensity, Set.indicator_of_mem hinter]
  rw [Finset.prod_div_distrib, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  ring

/-- `regDirichletIntegral` is additive. -/
theorem regDirichletIntegral_add (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hb : b ∈ mvBetaConvergent) :
    regDirichletIntegral b (fun u => f u + g u) =
    regDirichletIntegral b f + regDirichletIntegral b g := by
  unfold regDirichletIntegral
  rw [← integral_add
    (integrableOn_regDirichletDensity_mul b hb hf)
    (integrableOn_regDirichletDensity_mul b hb hg)]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- `regDirichletIntegral` commutes with complex scalar multiplication. -/
theorem regDirichletIntegral_smul (b : ι → ℂ) (f : (ι → ℝ) → ℂ) (c : ℂ)
    : regDirichletIntegral b (fun u => c * f u) =
    c * regDirichletIntegral b f := by
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- The integral of `f` depends only on the values of `f` on the standard Simplex. -/
theorem regDirichletIntegral_congr
    (b : ι → ℂ) {f g : (ι → ℝ) → ℂ}
    (hfg : Set.EqOn f g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regDirichletIntegral b f =
      regDirichletIntegral b g := by
  unfold regDirichletIntegral
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u hu
  dsimp only
  rw [hfg hu]

end ProbabilityTheory

end ComplexDirichlet
