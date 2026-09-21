/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.S.Analytic

/-! # Differentiation of the entire Carlson S-function -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Carlson's differentiation formula for the analytically continued `S` function. -/
theorem carlsonPartialDeriv_regCarlsonSSeries (i : ι) (z b : ι → ℂ) :
    carlsonPartialDeriv i (fun z => regCarlsonSSeries z b) z =
      b i * regCarlsonSSeries z (addDirichletUnit b i) := by
  let F := fun q : Sum ι ι → ℂ =>
    regCarlsonSSeries (fun j => q (.inr j)) (fun j => q (.inl j))
  have hF : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_regCarlsonSSeries_joint
  have hpartial (b : ι → ℂ) :
      carlsonPartialDeriv i (fun z => regCarlsonSSeries z b) z =
        CarlsonFunctions.SeveralComplexVariables.partialDerivCarlson (.inr i) F (Sum.elim b z) := by
    simp only [carlsonPartialDeriv_eq_partialDeriv,
      CarlsonFunctions.SeveralComplexVariables.partialDerivCarlson,
      Sum.elim_inr]
    congr 1
    funext w
    dsimp only [F]
    congr 1 <;> funext j <;> simp
  have hleft : AnalyticOnNhd ℂ
      (fun b => carlsonPartialDeriv i (fun z => regCarlsonSSeries z b) z) Set.univ := by
    simp_rw [hpartial]
    intro b _
    have hmap : AnalyticAt ℂ (fun b : ι → ℂ => Sum.elim b z) b := by
      apply AnalyticAt.pi
      intro k
      cases k with
      | inl j => exact (ContinuousLinearMap.proj (R := ℂ) j).analyticAt b
      | inr j => exact analyticAt_const
    exact ((hF.partialDerivCarlson isOpen_univ (.inr i)) _ (Set.mem_univ _)).comp_of_eq hmap rfl
  have hright : AnalyticOnNhd ℂ
      (fun b => b i * regCarlsonSSeries z (addDirichletUnit b i)) Set.univ := by
    intro b _
    apply ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt b).mul
    apply (analyticOnNhd_regCarlsonSSeries z _ (Set.mem_univ _)).comp
    apply AnalyticAt.pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [addDirichletUnit] using!
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt b).add analyticAt_const
    · simpa [addDirichletUnit, hji] using!
        (ContinuousLinearMap.proj (R := ℂ) j).analyticAt b
  have heq := analyticOnNhd_eq_of_eqOn_mvBetaConvergent hleft hright (by
    intro b hb
    have hf : (fun z => regCarlsonSSeries z b) = regCarlsonSIntegral b :=
      funext fun z => regCarlsonSSeries_eq_regCarlsonSIntegral z hb
    dsimp only
    rw [hf, carlsonPartialDeriv_regCarlsonSIntegral hb,
      regCarlsonSSeries_eq_regCarlsonSIntegral z (addDirichletUnit_mem_mvBetaConvergent hb i)])
  exact congrFun heq b

end DirichletTransform
