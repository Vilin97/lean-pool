/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Smooth
public import LeanPool.CarlsonFunctions.Pochhammer.PositiveCpow

public import LeanPool.CarlsonFunctions.Dirichlet.Complex
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Integration by parts for regularized Dirichlet integrals

The normalized positive power `x₊ ^ (a - 1) / Gamma a` has derivative
`x₊ ^ (a - 2) / Gamma (a - 1)` when `2 < re a`, including at zero.
Products of these functions give the Dirichlet density in a free-coordinate chart,
extended by zero outside the simplex. Mathlib's integration-by-parts theorem on the
ambient coordinate space then gives `regDirichletIntegral_tangent_ibp` without a
boundary term. This result uses only the native integral theory.
-/

open Complex MeasureTheory ProbabilityTheory MeasureTheory.Measure Set Filter
open scoped Topology Classical

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The regularized density in a free-coordinate chart, extended by zero. -/
def dirichletChartDensity (i : ι) (b : ι → ℂ)
    (x : {j : ι // j ≠ i} → ℝ) : ℂ :=
  ∏ j, positiveGammaPower (b j) (stdSimplexCoordMap i x j)

theorem prod_positiveGammaPower_eq_regDirichletDensity (b : ι → ℂ)
    (u : ι → ℝ) (hu : ∑ j, u j = 1) :
    (∏ j, positiveGammaPower (b j) (u j)) = regDirichletDensity b u := by
  by_cases hp : ∀ j, 0 < u j
  · have hi : u ∈ stdSimplexInterior := ⟨⟨fun j => (hp j).le, hu⟩, hp⟩
    simp [regDirichletDensity, hi, positiveGammaPower, positiveCpow, hp]
  · have hi : u ∉ stdSimplexInterior := fun h => hp h.2
    rw [regDirichletDensity, Set.indicator_of_notMem hi]
    obtain ⟨j, hj⟩ := not_forall.mp hp
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [positiveGammaPower, positiveCpow, hj]

theorem dirichletChartDensity_eq (i : ι) (b : ι → ℂ)
    (x : {j : ι // j ≠ i} → ℝ) :
    dirichletChartDensity i b x = regDirichletDensity b (stdSimplexCoordMap i x) :=
  prod_positiveGammaPower_eq_regDirichletDensity b _ (sum_stdSimplexCoordMap i x)

theorem tsupport_dirichletChartDensity_subset (i : ι) (b : ι → ℂ) :
    tsupport (dirichletChartDensity i b) ⊆
      stdSimplexCoordMap i ⁻¹' Convexity.StdSimplex.coordinateSet ℝ ι := by
  apply closure_minimal ?_ ((Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).preimage
    (continuous_stdSimplexCoordMap i))
  intro x hx
  by_contra hn
  apply hx
  rw [dirichletChartDensity_eq, regDirichletDensity, Set.indicator_of_notMem]
  exact fun h => hn h.1

theorem dirichletChartDensity_mul_eq_indicator (i : ι) (b : ι → ℂ)
    (f : (ι → ℝ) → ℂ) :
    (fun x => dirichletChartDensity i b x * f (stdSimplexCoordMap i x)) =
      (stdSimplexFreeCoords (R := ℝ) i).indicator
        (fun x => regDirichletDensity b (stdSimplexCoordMap i x) *
          f (stdSimplexCoordMap i x)) := by
  funext x
  by_cases hx : x ∈ stdSimplexFreeCoords (R := ℝ) i
  · simp [hx, dirichletChartDensity_eq]
  · rw [Set.indicator_of_notMem hx, dirichletChartDensity_eq, regDirichletDensity,
      Set.indicator_of_notMem, zero_mul]
    intro h
    exact hx ((stdSimplexCoordMap_mem_stdSimplex_iff i x).mp h.1)

theorem integral_dirichletChartDensity_mul (i : ι) (b : ι → ℂ)
    (f : (ι → ℝ) → ℂ) :
    (∫ x, dirichletChartDensity i b x * f (stdSimplexCoordMap i x)) =
      regDirichletIntegral b f := by
  let : Nonempty ι := ⟨i⟩
  rw [dirichletChartDensity_mul_eq_indicator,
    integral_indicator (isClosed_stdSimplexFreeCoords i).measurableSet,
    regDirichletIntegral, integral_stdSimplex_eq_integral_freeCoords i]

theorem integrable_dirichletChartDensity_mul (i : ι) (b : ι → ℂ)
    (hb : b ∈ mvBetaConvergent) {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Integrable (fun x => dirichletChartDensity i b x * f (stdSimplexCoordMap i x)) := by
  let : Nonempty ι := ⟨i⟩
  have h := integrableOn_regDirichletDensity_mul b hb hf
  rw [IntegrableOn, Measure.stdSimplexMeasure_restrict_stdSimplex i] at h
  have h' := (isClosedEmbedding_stdSimplexCoordMap i).measurableEmbedding.integrable_map_iff.mp h
  rw [dirichletChartDensity_mul_eq_indicator,
    integrable_indicator_iff (isClosed_stdSimplexFreeCoords i).measurableSet]
  exact h'

theorem dirichletChartDensity_lower (i k : ι) (b : ι → ℂ)
    (x : {j : ι // j ≠ i} → ℝ) :
    dirichletChartDensity i (b - Pi.single k 1) x =
      positiveGammaPower (b k - 1) (stdSimplexCoordMap i x k) *
        ∏ l ∈ Finset.univ.erase k, positiveGammaPower (b l) (stdSimplexCoordMap i x l) := by
  rw [dirichletChartDensity, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro l hl
    simp [Pi.single_eq_of_ne (Finset.mem_erase.mp hl).1]

theorem hasLineDerivAt_dirichletChartDensity (i : ι) (j : {j : ι // j ≠ i})
    (b : ι → ℂ) (hb : ∀ k, 2 < (b k).re) (x : {j : ι // j ≠ i} → ℝ) :
    HasLineDerivAt ℝ (dirichletChartDensity i b)
      (dirichletChartDensity i (b - Pi.single (j : ι) 1) x -
        dirichletChartDensity i (b - Pi.single i 1) x) x (Pi.single j 1) := by
  let v : ι → ℝ := Pi.single (j : ι) 1 - Pi.single i 1
  have h (k : ι) : HasDerivAt
      (fun t : ℝ => positiveGammaPower (b k) (stdSimplexCoordMap i x k + t * v k))
      (v k • positiveGammaPower (b k - 1) (stdSimplexCoordMap i x k)) 0 := by
    simpa using! (hasDerivAt_positiveGammaPower (hb k) (stdSimplexCoordMap i x k)).scomp_of_eq 0
      ((hasDerivAt_const 0 (stdSimplexCoordMap i x k)).add
        ((hasDerivAt_id 0).mul_const (v k))) (by simp)
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun k _ => h k)
  have hd : (∑ k : ι,
      (∏ l ∈ Finset.univ.erase k, positiveGammaPower (b l) (stdSimplexCoordMap i x l)) •
        (v k • positiveGammaPower (b k - 1) (stdSimplexCoordMap i x k))) =
      dirichletChartDensity i (b - Pi.single (j : ι) 1) x -
        dirichletChartDensity i (b - Pi.single i 1) x := by
    simp only [smul_eq_mul, Complex.real_smul]
    have heq (k : ι) :
        (∏ l ∈ Finset.univ.erase k, positiveGammaPower (b l) (stdSimplexCoordMap i x l)) *
          ((v k : ℂ) * positiveGammaPower (b k - 1) (stdSimplexCoordMap i x k)) =
        (v k : ℂ) * dirichletChartDensity i (b - Pi.single k 1) x := by
      rw [dirichletChartDensity_lower]; ring
    simp_rw [heq]
    simp [v, Pi.single_apply, sub_mul, Finset.sum_sub_distrib,
      apply_ite Complex.ofReal, ite_mul]
  change HasDerivAt (fun t : ℝ => dirichletChartDensity i b (x + t • Pi.single j 1)) _ 0
  simp_rw [dirichletChartDensity, stdSimplexCoordMap_add_single]
  convert! hp using 1
  simpa [dirichletChartDensity] using hd.symm

/-- Tangential integration by parts, initially with exponents that vanish differentiably
at every boundary face. The Gamma normalization removes the usual exponent coefficients. -/
theorem regDirichletIntegral_tangent_ibp (i : ι) (j : {j : ι // j ≠ i})
    (b : ι → ℂ) (hb : ∀ k, 2 < (b k).re) {f : (ι → ℝ) → ℂ}
    (hf : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, DifferentiableAt ℝ f u)
    (hdf : ContinuousOn (fun u => fderiv ℝ f u (Pi.single (j : ι) 1 - Pi.single i 1))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regDirichletIntegral b (fun u => fderiv ℝ f u (Pi.single (j : ι) 1 - Pi.single i 1)) =
      regDirichletIntegral (b - Pi.single i 1) f -
        regDirichletIntegral (b - Pi.single (j : ι) 1) f := by
  have hfc : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hb0 : b ∈ mvBetaConvergent := fun k => lt_trans (by norm_num) (hb k)
  have hblower (k : ι) : b - Pi.single k 1 ∈ mvBetaConvergent := by
    intro l
    by_cases hl : l = k
    · subst l
      simp only [Pi.sub_apply, Pi.single_eq_same, sub_re, one_re]
      linarith [hb k]
    · simpa [Pi.single_eq_of_ne hl] using hb0 l
  have h1 := integrable_dirichletChartDensity_mul i _ (hblower (j : ι)) hfc
  have h2 := integrable_dirichletChartDensity_mul i _ (hblower i) hfc
  have h3 := integrable_dirichletChartDensity_mul i b hb0 hdf
  have h4 := integrable_dirichletChartDensity_mul i b hb0 hfc
  have hline (x : {j : ι // j ≠ i} → ℝ) (hx : x ∈ tsupport (dirichletChartDensity i b)) :
      HasLineDerivAt ℝ (fun y => f (stdSimplexCoordMap i y))
        (fderiv ℝ f (stdSimplexCoordMap i x) (Pi.single (j : ι) 1 - Pi.single i 1))
        x (Pi.single j 1) := by
    have hd := (hf _ (tsupport_dirichletChartDensity_subset i b hx)).hasFDerivAt.hasLineDerivAt
      (Pi.single (j : ι) 1 - Pi.single i 1)
    simpa only [HasLineDerivAt, stdSimplexCoordMap_add_single] using hd
  have H := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ)
    (by simpa only [ContinuousLinearMap.mul_apply', sub_mul] using! h1.sub h2)
    h3 h4 (fun x _ => hasLineDerivAt_dirichletChartDensity i j b hb x) hline
  simp only [ContinuousLinearMap.mul_apply', sub_mul] at H
  rw [integral_sub h1 h2] at H
  erw [← integral_dirichletChartDensity_mul i b
    (fun u => fderiv ℝ f u (Pi.single (j : ι) 1 - Pi.single i 1))]
  simpa only [integral_dirichletChartDensity_mul, neg_sub] using H

end DirichletTransform
