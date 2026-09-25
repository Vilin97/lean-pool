/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Integral
public import LeanPool.CarlsonFunctions.Carlson.S

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Confluence of Carlson's R-function to the S-function

This file formalizes the confluence limit of [Carl77, Section 5.10]. Natural exponents are
used first: this is the branch-independent form of Carlson's limit and is directly supported by
Mathlib's theorem `Complex.tendsto_one_add_div_pow_exp`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.10,
  Academic Press, 1977.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped Topology
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The Carlson variables which coalesce at `1` in the confluence limit `R → S`. -/
def carlsonConfluentVariables (n : ℕ) (z : ι → ℂ) : ι → ℂ :=
  fun i ↦ 1 + z i / n

/-- Carlson's affine form turns confluent variables into the corresponding scalar confluent
variable. -/
theorem carlsonAffineForm_confluentVariables {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) (n : ℕ) (z : ι → ℂ) :
    carlsonAffineForm (carlsonConfluentVariables n z) u =
      1 + carlsonAffineForm z u / n := by
  simp only [carlsonAffineForm, carlsonConfluentVariables, mul_add, Finset.sum_add_distrib]
  rw [show ∑ i, (u i : ℂ) * 1 = 1 by simpa using congrArg Complex.ofReal hu.2]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pointwise confluence of the natural-power Carlson kernel to the exponential kernel. -/
theorem tendsto_carlsonAffineForm_confluentVariables_pow (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    Tendsto (fun n : ℕ ↦ carlsonAffineForm (carlsonConfluentVariables n z) u ^ n)
      atTop (𝓝 (exp (carlsonAffineForm z u))) := by
  apply (Complex.tendsto_one_add_div_pow_exp (carlsonAffineForm z u)).congr'
  filter_upwards with n
  rw [carlsonAffineForm_confluentVariables hu]

/-- A uniform bound for the natural-power kernels occurring in Carlson's confluence limit. -/
theorem norm_carlsonAffineForm_confluentVariables_pow_le (n : ℕ) (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    ‖carlsonAffineForm (carlsonConfluentVariables n z) u ^ n‖ ≤
      Real.exp (∑ i, ‖z i‖) := by
  let C : ℝ := ∑ i, ‖z i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  rw [carlsonAffineForm_confluentVariables hu, norm_pow]
  calc
    ‖1 + carlsonAffineForm z u / (n : ℂ)‖ ^ n ≤
        (1 + C / n) ^ n := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖1 + carlsonAffineForm z u / (n : ℂ)‖ ≤
            1 + ‖carlsonAffineForm z u‖ / n := by
          calc
            ‖1 + carlsonAffineForm z u / (n : ℂ)‖ ≤
                ‖(1 : ℂ)‖ + ‖carlsonAffineForm z u / (n : ℂ)‖ := norm_add_le _ _
            _ = 1 + ‖carlsonAffineForm z u‖ / n := by simp
        _ ≤ 1 + C / n := by
          gcongr
          exact norm_carlsonAffineForm_le_sum_norm z hu
    _ ≤ Real.exp C := by
      by_cases hn : n = 0
      · subst n
        simp [hC]
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        calc
          (1 + C / n) ^ n ≤ (Real.exp (C / n)) ^ n := by
            gcongr
            simpa [add_comm] using Real.add_one_le_exp (C / n)
          _ = Real.exp C := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp

/-- Carlson's confluence theorem 5.10-1 for the native regularized integrals: natural-power
`R` functions with variables coalescing at `1` converge to the `S` function. -/
theorem tendsto_regCarlsonRIntegral_confluent (b z : ι → ℂ)
    (hb : b ∈ mvBetaConvergent) :
    Tendsto (fun n : ℕ ↦ regCarlsonRIntegral (n : ℂ) b
        (carlsonConfluentVariables n z)) atTop
      (𝓝 (regCarlsonSIntegral b z)) := by
  let μ := (stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
  let C : ℝ := Real.exp (∑ i, ‖z i‖)
  let F : ℕ → (ι → ℝ) → ℂ := fun n u ↦
    regDirichletDensity b u * carlsonAffineForm (carlsonConfluentVariables n z) u ^ n
  let f : (ι → ℝ) → ℂ := fun u ↦
    regDirichletDensity b u * exp (carlsonAffineForm z u)
  have hdens : IntegrableOn (fun u ↦ regDirichletDensity b u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
    simpa using integrableOn_regDirichletDensity_mul b hb (continuousOn_const :
      ContinuousOn (fun _ : ι → ℝ ↦ (1 : ℂ)) (Convexity.StdSimplex.coordinateSet ℝ ι))
  have hbound : Integrable (fun u ↦ C * ‖regDirichletDensity b u‖) μ :=
    hdens.norm.const_mul C
  have hmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact (integrableOn_regDirichletDensity_mul b hb
      ((continuous_carlsonAffineForm (carlsonConfluentVariables n z)).continuousOn.pow n)).1
  have hdom : ∀ n, ∀ᵐ u ∂μ, ‖F n u‖ ≤ C * ‖regDirichletDensity b u‖ := by
    intro n
    filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    simp only [F, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      (norm_carlsonAffineForm_confluentVariables_pow_le n z hu) (norm_nonneg _)
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun n ↦ F n u) atTop (𝓝 (f u)) := by
    filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    exact tendsto_const_nhds.mul (tendsto_carlsonAffineForm_confluentVariables_pow z hu)
  have h := tendsto_integral_of_dominated_convergence
    (fun u ↦ C * ‖regDirichletDensity b u‖) hmeas hbound hdom hlim
  simpa [F, f, μ, regCarlsonRIntegral, regCarlsonSIntegral,
    regCarlsonDirichletAverage, regDirichletIntegral, cpow_natCast] using h

/-- Carlson's confluence theorem 5.10-1 for the native unregularized integrals. -/
theorem tendsto_carlsonRIntegral_confluent (b z : ι → ℂ)
    (hb : b ∈ mvBetaConvergent) :
    Tendsto (fun n : ℕ ↦ carlsonRIntegral (n : ℂ) b
        (carlsonConfluentVariables n z)) atTop
      (𝓝 (carlsonSIntegral b z)) := by
  simpa [carlsonRIntegral, carlsonSIntegral] using
    tendsto_const_nhds.mul (tendsto_regCarlsonRIntegral_confluent b z hb)

end DirichletTransform
end CarlsonR
