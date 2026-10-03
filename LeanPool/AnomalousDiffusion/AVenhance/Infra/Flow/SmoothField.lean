/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.GlobalExistence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.PeriodicSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Continuity
public import Mathlib.Analysis.Calculus.MeanValue

/-! Consequences of compact-cell derivative bounds for smooth periodic fields. -/

@[expose] public section

open Homogenization
open scoped NNReal Topology

namespace AVenhance.Infra.Flow

/-- The spatial slices of a smooth jointly periodic field have a common global
Lipschitz constant. -/
theorem exists_global_spatial_lipschitz
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL, hbound⟩ := exists_global_iteratedFDeriv_bound hb 1
  let K : ℝ≥0 := ⟨L, hL⟩
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  have hdiff : Differentiable ℝ F := by
    exact hb.smooth.differentiable (by simp)
  have hderiv : ∀ p, ‖fderiv ℝ F p‖₊ ≤ K := by
    intro p
    have hp := hbound p
    rw [norm_iteratedFDeriv_one] at hp
    change ‖fderiv ℝ F p‖₊ ≤ K
    exact_mod_cast hp
  have hLip : LipschitzWith K F :=
    lipschitzWith_of_nnnorm_fderiv_le hdiff hderiv
  refine ⟨L, hL, ?_⟩
  intro t x y
  have h := hLip.dist_le_mul (t, x) (t, y)
  change dist (b t x) (b t y) ≤ (K : ℝ) * dist (t, x) (t, y) at h
  calc
    ‖b t x - b t y‖ = dist (b t x) (b t y) := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist (t, x) (t, y) := h
    _ = L * ‖x - y‖ := by
      rw [dist_eq_norm, Prod.norm_def]
      simp only [Prod.fst_sub, sub_self, norm_zero, max_eq_right (norm_nonneg _)]
      rfl

/-- A smooth jointly periodic field satisfies the hypotheses of the global flow characterization. -/
theorem existsUnique_smoothPeriodic_flow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃! X : ℝ → Vec 2 → ℝ → Vec 2, AVenhance.IsFlow b X := by
  apply AVenhance.Infra.Flow.existsUnique_flow b
  · exact hb.smooth.continuous
  · obtain ⟨L, hL0, hL⟩ := exists_global_spatial_lipschitz hb
    exact ⟨L, hL⟩

/-- The flow is jointly continuous in target time, initial position, and
initial time for every characterized flow of a smooth periodic field. -/
theorem flow_continuous_joint_of_smoothPeriodic
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) := by
  obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
  exact flow_continuous_joint b hL hX

/-- The right-hand side of the target-time ODE is jointly
continuous in all flow parameters. -/
theorem flow_target_time_derivative_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (fun p : ℝ × Vec 2 × ℝ => b p.1 (X p.1 p.2.1 p.2.2)) := by
  have hflow := flow_continuous_joint_of_smoothPeriodic hb hX
  exact hb.smooth.continuous.comp (continuous_fst.prodMk hflow)

end AVenhance.Infra.Flow
