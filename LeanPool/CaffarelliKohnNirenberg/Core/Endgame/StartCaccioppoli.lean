/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Consumers

/-! # Fixed constants for the initial gamma estimate

The gamma estimate uses its own numerical velocity constant. The force
constant is the same explicit q-dependent constant as in Caccioppoli.
Neither constant depends on the domain or the solution.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Endgame

/-- A common constant for the three velocity/pressure terms of the gamma estimate. -/
def startGammaConstant : ℝ :=
  Real.sqrt (max
    (6000 * ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
      ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
        6 * cutoffGradientConstant * 5000000)))
    (max (6000 * (3 * (1500 * cutoffGradientConstant + 900000)))
      (6000 * (3000 * cutoffGradientConstant + 1800000))))

/-- The initial gamma display with all numerical comparison premises discharged. -/
theorem caccioppoli_gamma_display_fixed
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) :
    ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      alpha u z r + beta u Du z r ≤
        startGammaConstant * ((r / ρ) * gamma u z ρ +
          (r / ρ) ^ (-1 : ℝ) * gamma u z ρ ^ (3 / 2 : ℝ) +
          (r / ρ) ^ (-1 : ℝ) * delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ)) +
        caccioppoliC₂₆ q * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ) := by
  have hcg : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hbase : 0 ≤ max
      (6000 * ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
        ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
          6 * cutoffGradientConstant * 5000000)))
      (max (6000 * (3 * (1500 * cutoffGradientConstant + 900000)))
        (6000 * (3000 * cutoffGradientConstant + 1800000))) :=
    le_max_of_le_right (le_max_of_le_right (by positivity))
  apply caccioppoli_gamma_display hsol
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rw [Real.sq_sqrt hbase]
    exact le_max_left _ _
  · rw [Real.sq_sqrt hbase]
    exact le_max_of_le_right (le_max_left _ _)
  · rw [Real.sq_sqrt hbase]
    exact le_max_of_le_right (le_max_right _ _)
  · rw [Real.sq_sqrt (by positivity)]

end CKN.Core.Endgame
