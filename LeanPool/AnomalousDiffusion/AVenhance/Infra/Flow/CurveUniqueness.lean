/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import Mathlib.Analysis.ODE.ExistUnique

/-! Basic uniqueness for global integral curves of uniformly Lipschitz fields. -/

@[expose] public section

open Homogenization
open scoped NNReal

namespace AVenhance.Infra.Flow

/-- A uniform spatial Lipschitz bound, stated with a real constant, gives a
nonnegative `LipschitzWith` constant for each time slice. -/
theorem lipschitzWith_of_uniform_bound
    (b : ℝ → Vec 2 → Vec 2) {L : ℝ}
    (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) :
    ∀ t, LipschitzWith ⟨max L (0 : ℝ), le_max_right L (0 : ℝ)⟩ (b t) := by
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖b t x - b t y‖ ≤ L * ‖x - y‖ := hL t x y
    _ ≤ max L 0 * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (le_max_left L (0 : ℝ)) (norm_nonneg _)

/-- Two global integral curves with the same value at one time coincide. -/
theorem integralCurve_unique
    (b : ℝ → Vec 2 → Vec 2) {L : ℝ}
    (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {γ η : ℝ → Vec 2}
    (hγ : ∀ t, HasDerivAt γ (b t (γ t)) t)
    (hη : ∀ t, HasDerivAt η (b t (η t)) t)
    {s : ℝ} (h₀ : γ s = η s) : γ = η := by
  let K : ℝ≥0 := ⟨max L (0 : ℝ), le_max_right L (0 : ℝ)⟩
  have hLip : ∀ t, LipschitzWith K (b t) := by
    simpa only [K] using lipschitzWith_of_uniform_bound b hL
  apply ODE_solution_unique_univ (K := K) (s := fun _ => Set.univ)
    (fun t => (hLip t).lipschitzOnWith)
  · exact fun t => ⟨hγ t, Set.mem_univ _⟩
  · exact fun t => ⟨hη t, Set.mem_univ _⟩
  · exact h₀

end AVenhance.Infra.Flow
