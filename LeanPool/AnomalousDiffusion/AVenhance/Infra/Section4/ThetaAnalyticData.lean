/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaCommutatorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic

/-! Initial-data bounds in the ordered-word convention used by the energy
recursion. -/

@[expose] public section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section4

/-- The paper's analytic initial-data hypothesis gives the same factorial
bound for every ordered coordinate word. -/
theorem theta_initial_word_l2_le_of_analytic
    {R : ℝ} {θ₀ : Homogenization.Vec 2 → ℝ}
    (hθ₀ : AVenhance.IsThetaAnalytic R θ₀)
    {b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2} {κ : ℝ}
    {F : ℝ → Homogenization.Vec 2 → ℝ} {θ : ℝ → Homogenization.Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol b κ F θ₀ θ)
    (w : List (Fin 2)) :
    Real.sqrt (∫ x in AVenhance.unitCube,
      (classicalWordDerivative w θ₀ x) ^ 2) ≤
      Real.sqrt (AVenhance.l2NormSq θ₀) *
        ((w.length.factorial : ℝ) / R ^ w.length) := by
  by_cases hn0 : w.length = 0
  · have hw : w = [] := List.length_eq_zero_iff.mp hn0
    subst w
    simp [classicalWordDerivative, Classical.classicalWordDerivative, AVenhance.l2NormSq]
  · have hn : 1 ≤ w.length := by omega
    have hθ := hθ₀ w.length hn (fun j => w.get j)
    have hf : ContDiff ℝ (⊤ : ℕ∞) θ₀ := by
      have hslice := classicalSmooth_slice_nonneg hsol.1 (t := 0) le_rfl
      have hinit : θ 0 = θ₀ := funext hsol.2.2.1
      rw [← hinit]
      exact hslice
    have hword : classicalWordDerivative w θ₀ =
        fun x => iteratedFDeriv ℝ w.length θ₀ x
          (fun j => Homogenization.basisVec (w.get j)) := by
      funext x
      exact thetaWordDerivative_eq_iteratedFDeriv_get w θ₀ hf x
    have hInt :
        (∫ x in AVenhance.unitCube,
          (classicalWordDerivative w θ₀ x) ^ 2) =
        ∫ x in AVenhance.unitCube,
          (iteratedFDeriv ℝ w.length θ₀ x
            (fun j => Homogenization.basisVec (w.get j))) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hword]
    rw [hInt]
    simpa [AVenhance.l2NormSq] using hθ

end AVenhance.Infra.Section4
