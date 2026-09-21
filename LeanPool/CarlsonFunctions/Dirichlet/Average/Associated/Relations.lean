/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Basic
public import LeanPool.CarlsonFunctions.Dirichlet.ParameterShift

/-! # Associated Dirichlet-average identities -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Regularized form of Carlson's relation 5.6-1(4): an average is the sum of its
one-coordinate positive parameter shifts. -/
theorem regCarlsonDirichletAverage_eq_sum_addDirichletUnit
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u : ι → ℝ ↦ f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regCarlsonDirichletAverage b z f =
      ∑ i, b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f := by
  simp_rw [regCarlsonDirichletAverage,
    mul_regDirichletIntegral_addDirichletUnit hb]
  unfold regDirichletIntegral
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u hu
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_mul]
    have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
    rw [hsum, one_mul]
  · intro i _
    exact integrableOn_regDirichletDensity_mul b hb
      ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf)

/-- Carlson's relation 5.6-1(4) in its original normalization: an average is the weighted
sum of its positive unit shifts, with weights `b i / ∑ j, b j`. -/
theorem carlsonDirichletAverage_eq_sum_addDirichletUnit [Nonempty ι]
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u : ι → ℝ ↦ f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    carlsonDirichletAverage b z f =
      ∑ i, (b i / ∑ j, b j) * carlsonDirichletAverage (addDirichletUnit b i) z f := by
  let c : ℂ := ∑ i, b i
  have hcpos : 0 < c.re := by
    simpa [c] using Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty
  have hc : c ≠ 0 := ne_zero_of_re_pos hcpos
  have hsum (i : ι) : ∑ j, addDirichletUnit b i j = c + 1 := sum_addDirichletUnit b i
  unfold carlsonDirichletAverage
  rw [regCarlsonDirichletAverage_eq_sum_addDirichletUnit hb z f hf]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsum, Gamma_add_one c hc]
  change Gamma c * (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f) =
    (b i / c) * (c * Gamma c * regCarlsonDirichletAverage (addDirichletUnit b i) z f)
  field_simp [hc]

end DirichletTransform
