/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Coefficients
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Continuation

import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Differentiation of Carlson's Pochhammer numerators

The coordinate derivative identity is first obtained from the native Dirichlet integral.
Joint analyticity of the finite Pochhammer sum then extends it to all parameters.
-/

open Complex Finset ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The Pochhammer numerator is jointly entire in its parameters and nodes. -/
theorem analyticOnNhd_carlsonRPolynomialNumerator_joint (n : ℕ) :
    AnalyticOnNhd ℂ (fun p : (ι → ℂ) × (ι → ℂ) =>
      carlsonRPolynomialNumerator n p.1 p.2) Set.univ := by
  intro p _
  simp only [carlsonRPolynomialNumerator_eq_multinomial_sum]
  apply Finset.analyticAt_fun_sum
  intro m hm
  apply AnalyticAt.mul
  · apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_fun_prod
    intro i hi
    exact (((ContinuousLinearMap.proj (R := ℂ) i).comp
      (ContinuousLinearMap.snd ℂ (ι → ℂ) (ι → ℂ))).analyticAt p).pow _
  · apply Finset.analyticAt_fun_prod
    intro i hi
    exact ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ (m i))) _
      (Set.mem_univ _)).comp (((ContinuousLinearMap.proj (R := ℂ) i).comp
        (ContinuousLinearMap.fst ℂ (ι → ℂ) (ι → ℂ))).analyticAt p)

/-- Coordinate differentiation of the numerator remains entire in the parameters. -/
private theorem analyticOnNhd_partial_carlsonRPolynomialNumerator
    (n : ℕ) (i : ι) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (fun b => carlsonPartialDeriv i
      (carlsonRPolynomialNumerator n b) z) Set.univ := by
  let F := fun p : (ι → ℂ) × (ι → ℂ) => carlsonRPolynomialNumerator n p.1 p.2
  have hF : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_carlsonRPolynomialNumerator_joint n
  have heq (b : ι → ℂ) : carlsonPartialDeriv i (carlsonRPolynomialNumerator n b) z =
      fderiv ℂ F (b, z) (0, Pi.single i 1) := by
    have hd : HasFDerivAt F (fderiv ℂ F (b, z)) (b, Function.update z i (z i)) := by
      simpa using (hF (b, z) (Set.mem_univ _)).differentiableAt.hasFDerivAt
    exact (hd.comp_hasDerivAt (z i)
      ((hasDerivAt_const (z i) b).prodMk (hasDerivAt_update z i (z i)))).deriv
  simp_rw [heq]
  intro b _
  have hmap : AnalyticAt ℂ (fun b : ι → ℂ => (b, z)) b :=
    analyticAt_id.prod analyticAt_const
  exact ((ContinuousLinearMap.apply ℂ ℂ (0, Pi.single i 1)).analyticAt _).comp
    (((hF _ (Set.mem_univ _)).fderiv).comp hmap)

/-- Differentiating a node lowers the degree and raises the corresponding parameter.
The numerator formulation has no exceptional-parameter exclusions. -/
theorem carlsonPartialDeriv_carlsonRPolynomialNumerator_succ
    (n : ℕ) (i : ι) (b z : ι → ℂ) :
    carlsonPartialDeriv i (carlsonRPolynomialNumerator (n + 1) b) z =
      (n + 1 : ℂ) * b i * carlsonRPolynomialNumerator n (addDirichletUnit b i) z := by
  have hright : AnalyticOnNhd ℂ (fun b =>
      (n + 1 : ℂ) * b i * carlsonRPolynomialNumerator n (addDirichletUnit b i) z) Set.univ := by
    intro b _
    apply (analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt b)).mul
    have hmap : AnalyticAt ℂ (fun b => (addDirichletUnit b i, z)) b := by
      apply AnalyticAt.prod _ analyticAt_const
      apply AnalyticAt.pi
      intro j
      by_cases hji : j = i
      · subst j
        simpa [addDirichletUnit] using!
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt b).add analyticAt_const
      · simpa [addDirichletUnit, hji] using!
          (ContinuousLinearMap.proj (R := ℂ) j).analyticAt b
    have H := (analyticOnNhd_carlsonRPolynomialNumerator_joint n
      (addDirichletUnit b i, z) (Set.mem_univ _)).comp_of_eq hmap rfl
    simpa only using! H
  have heq := analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_partial_carlsonRPolynomialNumerator (n + 1) i z) hright (by
      intro b hb
      dsimp only
      let : Nonempty ι := ⟨i⟩
      have hS : 0 < (∑ j, b j).re := by
        change 0 < Complex.reCLM (∑ j, b j)
        rw [map_sum]
        exact sum_pos (fun j _ => hb j) univ_nonempty
      have hG : Gamma ((∑ j, b j) + (n + 1 : ℕ)) ≠ 0 :=
        Gamma_ne_zero_of_re_pos (by simp only [add_re, natCast_re]; positivity)
      have hnum (w : ι → ℂ) : carlsonRPolynomialNumerator (n + 1) b w =
          Gamma ((∑ j, b j) + (n + 1 : ℕ)) * regCarlsonR (n + 1) w b := by
        rw [regCarlsonR, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma]
        field_simp
      have hfun : carlsonRPolynomialNumerator (n + 1) b = fun w =>
          Gamma ((∑ j, b j) + (n + 1 : ℕ)) *
            regCarlsonDirichletAverage b w (fun x => x ^ (n + 1)) := by
        funext w
        rw [hnum, regCarlsonDirichletAverage_pow _ _ hb]
      rw [hfun, carlsonPartialDeriv, deriv_const_mul_field]
      change Gamma _ * carlsonPartialDeriv i
        (fun w => regCarlsonDirichletAverage b w (fun x => x ^ (n + 1))) z = _
      have hpoly : AnalyticOnNhd ℂ (fun x : ℂ => x ^ (n + 1)) Set.univ := by
        simpa only [Pi.pow_apply, id_eq] using! (analyticOnNhd_id (𝕜 := ℂ)).pow (n + 1)
      rw [carlsonPartialDeriv_regCarlsonDirichletAverage_of_analyticOnNhd isOpen_univ
        (convex_univ : Convex ℝ (Set.univ : Set ℂ)) hpoly
        hb (Set.subset_univ _) i]
      have hdp : deriv (fun x : ℂ => x ^ (n + 1)) = fun x => (n + 1 : ℂ) * x ^ n := by
        funext x
        simp
      rw [hdp]
      rw [regCarlsonDirichletAverage_const_mul,
        regCarlsonDirichletAverage_pow _ _ (addDirichletUnit_mem_mvBetaConvergent hb i),
        regCarlsonR, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma]
      have hs : (∑ j, addDirichletUnit b i j) + n = (∑ j, b j) + (n + 1 : ℕ) := by
        simp only [addDirichletUnit, sum_update_of_mem (mem_univ i), Nat.cast_add, Nat.cast_one]
        have H := sum_erase_add univ b (mem_univ i)
        simp only [sdiff_singleton_eq_erase] at *
        rw [← H]
        ring
      rw [hs]
      field_simp)
  exact congrFun heq b

/-- Derivative form of the coordinate differentiation identity. -/
theorem hasDerivAt_carlsonRPolynomialNumerator_update_succ
    (n : ℕ) (i : ι) (b z : ι → ℂ) :
    HasDerivAt (fun w => carlsonRPolynomialNumerator (n + 1) b (Function.update z i w))
      ((n + 1 : ℂ) * b i * carlsonRPolynomialNumerator n (addDirichletUnit b i) z) (z i) := by
  have hd : DifferentiableAt ℂ
      (fun p : (ι → ℂ) × (ι → ℂ) => carlsonRPolynomialNumerator (n + 1) p.1 p.2)
      (b, Function.update z i (z i)) := by
    simpa using (analyticOnNhd_carlsonRPolynomialNumerator_joint (n + 1) (b, z)
      (Set.mem_univ _)).differentiableAt
  have H := hd.comp (z i)
    ((hasDerivAt_const (z i) b).prodMk (hasDerivAt_update z i (z i))).differentiableAt
  rw [← carlsonPartialDeriv_carlsonRPolynomialNumerator_succ n i b z]
  exact H.hasDerivAt

end DirichletTransform
end
