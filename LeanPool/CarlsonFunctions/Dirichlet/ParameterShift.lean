/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Complex

/-! # Unit shifts of Dirichlet parameters and their integral identities -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The Dirichlet parameter vector obtained by increasing coordinate `i` by one. -/
def addDirichletUnit (b : ι → ℂ) (i : ι) : ι → ℂ :=
  Function.update b i (b i + 1)

open scoped Classical in
/-- A unit parameter shift increases the total parameter by one. -/
@[simp] theorem sum_addDirichletUnit (b : ι → ℂ) (i : ι) :
    ∑ j, addDirichletUnit b i j = (∑ j, b j) + 1 := by
  unfold addDirichletUnit
  rw [Fintype.sum_eq_add_sum_subtype_ne (Function.update b i (b i + 1)) i,
    Fintype.sum_eq_add_sum_subtype_ne b i]
  have hsum : (∑ j : {j : ι // j ≠ i}, Function.update b i (b i + 1) j) =
      ∑ j : {j : ι // j ≠ i}, b j := by
    apply Finset.sum_congr rfl
    intro j _
    exact Function.update_of_ne j.property _ _
  rw [Function.update_self, hsum]
  ring

omit [Fintype ι] in
/-- A positive unit shift preserves the native convergence region. -/
theorem addDirichletUnit_mem_mvBetaConvergent {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) :
    addDirichletUnit b i ∈ mvBetaConvergent := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [addDirichletUnit] using add_pos_of_pos_of_nonneg (hb i) (by norm_num : 0 ≤ (1 : ℝ))
  · simpa [addDirichletUnit, hji] using hb j

open scoped Classical in
/-- Increasing one Dirichlet parameter by one multiplies the regularized density by the
corresponding simplex coordinate, up to the factor `b i`. -/
theorem mul_regDirichletDensity_addDirichletUnit {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (u : ι → ℝ) :
    b i * regDirichletDensity (addDirichletUnit b i) u =
      (u i : ℂ) * regDirichletDensity b u := by
  classical
  by_cases hu : u ∈ stdSimplexInterior
  · rw [regDirichletDensity, Set.indicator_of_mem hu]
    rw [regDirichletDensity, Set.indicator_of_mem hu]
    have hbi : b i ≠ 0 := ne_zero_of_re_pos (hb i)
    have hui : (u i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu.2 i).ne'
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j ↦ (u j : ℂ) ^ (addDirichletUnit b i j - 1) /
        Gamma (addDirichletUnit b i j))]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j ↦ (u j : ℂ) ^ (b j - 1) / Gamma (b j))]
    have hoff :
        ∏ j ∈ Finset.univ \ {i},
            (u j : ℂ) ^ (addDirichletUnit b i j - 1) /
              Gamma (addDirichletUnit b i j) =
          ∏ j ∈ Finset.univ \ {i}, (u j : ℂ) ^ (b j - 1) / Gamma (b j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        simp at hj
      simp [addDirichletUnit, hji]
    rw [hoff]
    simp only [addDirichletUnit, Function.update_self]
    rw [Gamma_add_one (b i) hbi]
    rw [show (u i : ℂ) ^ (b i + 1 - 1) = (u i : ℂ) ^ b i by ring_nf]
    rw [cpow_sub _ _ hui, cpow_one]
    field_simp
  · simp [regDirichletDensity, hu]

/-- Integral form of the regularized one-coordinate parameter-shift identity. -/
theorem mul_regDirichletIntegral_addDirichletUnit {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (f : (ι → ℝ) → ℂ) :
    b i * regDirichletIntegral (addDirichletUnit b i) f =
      regDirichletIntegral b (fun u ↦ (u i : ℂ) * f u) := by
  unfold regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u _
  dsimp only
  rw [← mul_assoc, mul_regDirichletDensity_addDirichletUnit hb]
  ring

open scoped Classical in
/-- Compatibility spelling for the density-shift lemma used by the earlier `R`-function
development. -/
theorem mul_regDirichletDensity_update_add_one {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (u : ι → ℝ) :
    b i * regDirichletDensity (Function.update b i (b i + 1)) u =
      (u i : ℂ) * regDirichletDensity b u := by
  simpa [addDirichletUnit] using mul_regDirichletDensity_addDirichletUnit hb i u

open scoped Classical in
/-- Compatibility spelling for the integral parameter-shift lemma. -/
theorem mul_regDirichletIntegral_update_add_one {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (i : ι) (f : (ι → ℝ) → ℂ) :
    b i * regDirichletIntegral (Function.update b i (b i + 1)) f =
      regDirichletIntegral b (fun u ↦ (u i : ℂ) * f u) := by
  simpa [addDirichletUnit] using mul_regDirichletIntegral_addDirichletUnit hb i f

end DirichletTransform
