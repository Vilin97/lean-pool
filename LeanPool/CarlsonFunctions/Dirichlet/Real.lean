/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Intrinsic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Probability.Distributions.Beta
public import LeanPool.CarlsonFunctions.Dirichlet.Integral.Real
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Interior

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-!
# Real normalized Dirichlet measure on the standard simplex

The multivariate Dirichlet measure [KBJ00, Ch 49] is defined on the standard simplex in
symmetric variables, i.e. `Convexity.StdSimplex.coordinateSet ℝ ι`, or $E^{k-1}$ embedded in $ℝ^k$ where
`k = card ι`.

This file constructs the density and the probability measure, and records permutation
invariance and vector-valued integration against the density. The real monomial integral
theory is in `Dirichlet.Integral.Real`; moments, aggregation, and the beta marginal are in
`Dirichlet.Moments`. No complex Dirichlet integral or parameter continuation is imported.

The construction uses the standard-simplex coordinate measure and integral API exported by
`StdSimplexMeasure.Measure` and `StdSimplexMeasure.Integral`. The coordinate constructions are
provided transitively by `StdSimplexMeasure.Coordinates`.

## References

[KBJ00] Kotz, Samuel, Narayanaswamy Balakrishnan, and Norman L. Johnson. "Continuous
multivariate distributions, Volume 1: Models and applications." John Wiley & Sons, 2000.
Online: https://dx.doi.org/10.1002/0471722065.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The real-valued Dirichlet PDF with parameters `b`. This PDF is supported on
`stdSimplexInterior ι`. -/
def dirichletPdfReal (b : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 / mvRealBeta b) *
    stdSimplexInterior.indicator (fun u ↦ ∏ i, u i ^ (b i - 1)) u

/-- The `ENNReal`-valued Dirichlet PDF. -/
def dirichletPdf (b : ι → ℝ) (u : ι → ℝ) : ENNReal :=
  ENNReal.ofReal (dirichletPdfReal b u)

/-- The Dirichlet measure on the standard simplex. -/
def dirichletMeasure
    (b : ι → ℝ) : Measure (ι → ℝ) :=
  stdSimplexMeasure.withDensity (dirichletPdf b)

/-- The real-valued Dirichlet density is a measurable function. -/
theorem measurable_dirichletPdfReal (b : ι → ℝ) :
    Measurable (dirichletPdfReal b) := by
  unfold dirichletPdfReal
  exact measurable_const.mul
    ((by
      fun_prop :
      Measurable (fun u : ι → ℝ => ∏ i, u i ^ (b i - 1))).indicator
        (measurableSet_stdSimplexInterior (ι := ι)))

/-- The (ENNReal) Dirichlet density is a measurable function. -/
theorem measurable_dirichletPdf (b : ι → ℝ) :
    Measurable (dirichletPdf b) := by
  exact ENNReal.measurable_ofReal.comp
    (measurable_dirichletPdfReal b)



/-- The Radon-Nikodym derivative of the Dirichlet measure is almost everywhere
equal to the Dirichlet PDF. -/
theorem rnDeriv_dirichletMeasure {b : ι → ℝ} (_ : b ∈ mvRealBetaDomain) :
    (dirichletMeasure b).rnDeriv stdSimplexMeasure =ᵐ[stdSimplexMeasure]
      dirichletPdf b := by
  rw [dirichletMeasure]
  exact Measure.rnDeriv_withDensity _ (measurable_dirichletPdf b)

/-- The real-valued Dirichlet density is nonnegative. -/
theorem dirichletPdfReal_nonneg [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (u : ι → ℝ) :
    0 ≤ dirichletPdfReal b u := by
  unfold dirichletPdfReal
  refine mul_nonneg
    (le_of_lt (one_div_pos.mpr (mvRealBeta_pos hb))) ?_
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu]
    exact Finset.prod_nonneg fun i _ =>
      (rpow_pos_of_pos (hu.2 i) _).le
  · simp [Set.indicator_of_notMem hu]

/-- Unwraps an integral against the Dirichlet measure into an integral against the
standard simplex measure, explicitly multiplying the function by the Dirichlet density. -/
theorem integral_dirichletMeasure_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (f : (ι → ℝ) → E) :
    ∫ u, f u ∂(dirichletMeasure b) =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        dirichletPdfReal b u • f u ∂stdSimplexMeasure := by
  rw [dirichletMeasure]
  have hlt :
      ∀ᵐ u ∂stdSimplexMeasure, dirichletPdf b u < ⊤ := by
    filter_upwards with u
    simp [dirichletPdf]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_dirichletPdf b) hlt f]
  rw [← integral_indicator
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι
  · have hnonneg := dirichletPdfReal_nonneg hb u
    simp [hu, dirichletPdf,
      ENNReal.toReal_ofReal hnonneg]
  · simp [hu, dirichletPdf, dirichletPdfReal,
      stdSimplexInterior]

/-- Real-valued integration against the Dirichlet probability measure is integration
against its density on the simplex. -/
theorem integral_dirichletMeasure [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (f : (ι → ℝ) → ℝ) :
    ∫ u, f u ∂(dirichletMeasure b) =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        f u * dirichletPdfReal b u ∂stdSimplexMeasure := by
  simpa only [smul_eq_mul, mul_comm] using integral_dirichletMeasure_smul hb f

/-- The measure of the standard simplex under the Dirichlet measure equals 1. -/
theorem dirichletMeasure_stdSimplex
    [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    dirichletMeasure b (Convexity.StdSimplex.coordinateSet ℝ ι) = 1 := by
  let p : (ι → ℝ) → ℝ := fun u => ∏ i, u i ^ (b i - 1)
  have hp_int : IntegrableOn p (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure :=
    integrableOn_mvRealBetaMonomial hb
  have hd_int : IntegrableOn (dirichletPdfReal b) (Convexity.StdSimplex.coordinateSet ℝ ι)
      stdSimplexMeasure := by
    apply hp_int.const_mul (1 / mvRealBeta b) |>.congr
    have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    have hmem := self_mem_ae_restrict
      (μ := stdSimplexMeasure) (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    filter_upwards [hmem, hae] with u hu hpos
    simp [dirichletPdfReal, stdSimplexInterior, hu, hpos, p]
  have hd_integral :
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, dirichletPdfReal b u ∂stdSimplexMeasure = 1 := by
    have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    have hmem := self_mem_ae_restrict
      (μ := stdSimplexMeasure) (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    calc
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, dirichletPdfReal b u ∂stdSimplexMeasure =
          ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, (1 / mvRealBeta b) * p u ∂stdSimplexMeasure := by
            apply integral_congr_ae
            filter_upwards [hmem, hae] with u hu hpos
            simp [dirichletPdfReal, stdSimplexInterior, hu, hpos, p]
      _ = (1 / mvRealBeta b) * ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, p u ∂stdSimplexMeasure := by
        rw [MeasureTheory.integral_const_mul]
      _ = 1 := by
        rw [← mvRealBeta_eq_integral hb]
        field_simp [ne_of_gt (mvRealBeta_pos hb)]
  unfold dirichletMeasure
  rw [withDensity_apply _ (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  unfold dirichletPdf
  rw [← ofReal_integral_eq_lintegral_ofReal hd_int]
  · rw [hd_integral]
    simp
  · filter_upwards with u
    exact dirichletPdfReal_nonneg hb u

/-- The Dirichlet density vanishes outside `Convexity.StdSimplex.coordinateSet ℝ ι`. -/
theorem dirichletPdf_eq_zero_of_not_mem_stdSimplex
    (b : ι → ℝ) {u : ι → ℝ} (hu : u ∉ Convexity.StdSimplex.coordinateSet ℝ ι) :
    dirichletPdf b u = 0 := by
  simp [dirichletPdf, dirichletPdfReal, stdSimplexInterior, hu]

/-- The Dirichlet measure is restricted to the standard simplex. -/
theorem dirichletMeasure_restrict (b : ι → ℝ) :
    (dirichletMeasure b).restrict (Convexity.StdSimplex.coordinateSet ℝ ι) =
      dirichletMeasure b := by
  unfold dirichletMeasure
  rw [restrict_withDensity
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  rw [← withDensity_indicator
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  apply withDensity_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι
  · simp [hu]
  · simp [hu, dirichletPdf, dirichletPdfReal,
      stdSimplexInterior]

/-- The Dirichlet measure satisfies `isProbabilityMeasure`. -/
theorem isProbabilityMeasure_dirichletMeasure [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    IsProbabilityMeasure (dirichletMeasure b) := by
  refine ⟨?_⟩
  rw [← dirichletMeasure_restrict b]
  rw [Measure.restrict_apply_univ]
  exact dirichletMeasure_stdSimplex hb

/-- Every Dirichlet coordinate belongs to every `Lᵖ` space on the positive parameter domain. -/
theorem memLp_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) (p : ℝ≥0∞) :
    MemLp (fun u : ι → ℝ => u i) p (dirichletMeasure b) := by
  let : Nonempty ι := ⟨i⟩
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  exact memLp_coordinate_of_restrict_stdSimplex (dirichletMeasure_restrict b) i p

/-- The total mass / integral of the constant function 1 with respect to the Dirichlet
measure is 1. -/
theorem integral_dirichletMeasure_one [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    ∫ _, (1 : ℝ) ∂(dirichletMeasure b) = 1 := by
  let : IsProbabilityMeasure (dirichletMeasure b) :=
    isProbabilityMeasure_dirichletMeasure hb
  simp

/-- The Dirichlet measure is absolutely continuous with respect to `stdSimplexMeasure`. -/
theorem absolutelyContinuous_dirichletMeasure (b : ι → ℝ) :
    dirichletMeasure b ≪ stdSimplexMeasure :=
  withDensity_absolutelyContinuous _ _

/-- Defining the Dirichlet measure for the case of all `b` parameters equal. -/
def dirichletMeasureUniform (α : ℝ) : Measure (ι → ℝ) :=
  dirichletMeasure (fun _ => α)

/-- The case of all `b` parameters equal to 1 reduces to scaled Lebesgue measure. -/
theorem dirichletMeasureUniform_one :
    dirichletMeasureUniform (ι := ι) 1 =
      (1 / stdSimplexMeasure (Convexity.StdSimplex.coordinateSet ℝ ι)) •
      stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let : IsEmpty ι := hι
      simp [dirichletMeasureUniform, dirichletMeasure, stdSimplexMeasure_empty]
  | inr hι =>
      let : Nonempty ι := hι
      let b : ι → ℝ := fun _ => 1
      have hb : b ∈ mvRealBetaDomain := by simp [b, mvRealBetaDomain]
      have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
      rw [show dirichletMeasureUniform (ι := ι) 1 = dirichletMeasure b by rfl]
      rw [← dirichletMeasure_restrict b]
      unfold dirichletMeasure
      rw [restrict_withDensity hs]
      have hd : dirichletPdf b =ᵐ[stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)]
          fun _ => ENNReal.ofReal (1 / mvRealBeta b) := by
        have hmem := self_mem_ae_restrict (μ := stdSimplexMeasure) hs
        have hpos := ae_zero_lt_of_mem_stdSimplex (ι := ι)
        filter_upwards [hmem, hpos] with u hu hupos
        simp [dirichletPdf, dirichletPdfReal, stdSimplexInterior, hu, hupos, b]
      rw [withDensity_congr_ae hd, withDensity_const]
      congr 1
      rw [stdSimplexMeasure_stdSimplex]
      unfold mvRealBeta
      have hcpos : 0 < Fintype.card ι := Fintype.card_pos
      have hgamma : 0 < Gamma (Fintype.card ι : ℝ) :=
        Gamma_pos_of_pos (by exact_mod_cast hcpos)
      simp only [b, Finset.prod_const_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Gamma_one]
      have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
      rw [show (Fintype.card ι : ℝ) = ((Fintype.card ι - 1 : ℕ) : ℝ) + 1 by
        exact_mod_cast hcard]
      rw [Gamma_nat_eq_factorial]
      simp

/-- Simultaneously permuting the parameters and coordinates leaves the Dirichlet density
unchanged. -/
theorem dirichletPdf_perm (b : ι → ℝ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    dirichletPdf (b ∘ σ) (u ∘ σ) = dirichletPdf b u := by
  unfold dirichletPdf dirichletPdfReal
  have hbeta : mvRealBeta (b ∘ σ) = mvRealBeta b := by
    unfold mvRealBeta
    simp only [Function.comp_apply, Equiv.sum_comp]
    congr 1
    exact Equiv.prod_comp σ (fun i => Gamma (b i))
  have hinter := mem_stdSimplexInterior_perm σ u
  rw [hbeta]
  by_cases hu : u ∈ stdSimplexInterior
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hinter.mpr hu)]
    congr 2
    simpa [Function.comp_def] using
      (Equiv.prod_comp σ (fun i => u i ^ (b i - 1)))
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hinter.mp hu)]

/-- Permuting coordinates together with parameters is a measure-preserving transformation of
`dirichletMeasure`. -/
theorem measurePreserving_dirichletMeasure_perm (b : ι → ℝ) (σ : Equiv.Perm ι) :
  MeasurePreserving (fun x => x ∘ σ)
    (dirichletMeasure b) (dirichletMeasure (b ∘ σ)) := by
  let g : (ι → ℝ) ≃ᵐ (ι → ℝ) := {
    toFun x := x ∘ σ
    invFun x := x ∘ σ.symm
    left_inv x := by funext i; simp
    right_inv x := by funext i; simp
    measurable_toFun := continuous_pi (fun i => continuous_apply (σ i)) |>.measurable
    measurable_invFun := continuous_pi (fun i => continuous_apply (σ.symm i)) |>.measurable
  }
  have hg : MeasurePreserving g stdSimplexMeasure stdSimplexMeasure := by
    simpa [g] using measurePreserving_stdSimplexMeasure_perm σ
  refine ⟨g.measurable, ?_⟩
  change Measure.map g (dirichletMeasure b) = dirichletMeasure (b ∘ σ)
  unfold dirichletMeasure
  ext s hs
  rw [Measure.map_apply g.measurable hs]
  rw [withDensity_apply _ (g.measurable hs), withDensity_apply _ hs]
  have hchange := hg.setLIntegral_comp_preimage hs (measurable_dirichletPdf (b ∘ σ))
  rw [← hchange]
  apply setLIntegral_congr_fun (g.measurable hs)
  intro x hx
  exact (dirichletPdf_perm b σ x).symm

end ProbabilityTheory

namespace DirichletTransform

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- A complex-valued integral against a real Dirichlet measure can be written using its real
density and the standard-simplex measure. -/
theorem integral_dirichletMeasure_complex [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (f : (ι → ℝ) → ℂ) :
    ∫ u, f u ∂dirichletMeasure b =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, (dirichletPdfReal b u : ℂ) * f u
        ∂stdSimplexMeasure := by
  simpa only [Complex.real_smul] using integral_dirichletMeasure_smul hb f

end DirichletTransform

end DirichletDistribution
