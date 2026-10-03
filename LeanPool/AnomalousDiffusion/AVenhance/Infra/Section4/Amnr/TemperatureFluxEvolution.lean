/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxGradient

/-! The actual iterate gradient equation in primitive flux form. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The source iterate equation has exactly two diffusion/flux spatial
letters and the actual velocity-gradient contraction. -/
theorem amnr_temperature_gradient_flux_equation
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {v u : ℝ → Vec 2 → ℝ} {u₀ v₀ : Vec 2 → ℝ} {Fv : ℝ → Vec 2 → ℝ}
    (hv : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev Fv v₀ v)
    (hu : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (I.TForcing hΦ m κm κprev v) u₀ u)
    (p : Fin 2) :
    EqOn (amnrOp (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) none (amnrTGradient u p))
      (fun z => κprev * (∑ q : Fin 2,
          amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
            [some q, some q] (amnrTGradient u p) z) +
        (∑ q : Fin 2, amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
          [some p, some q] (amnrTemperatureFlux I hΦ m κm κprev v q) z) -
        ∑ q : Fin 2, amnrVelocityGradient
          (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) q p z * amnrTGradient u q z)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  intro z hz
  have hb : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) :=
    contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ hm N)
  rw [amnr_classical_gradient_material_equation hu hb p hz.1,
    amnr_temperatureForcing_gradient_eq_flux I hΦ hm hκm hv _ hb p hz.1]

/-- The canonical material step preserves the total budget by spending two
units on diffusion or flux. Every lower canonical jet stays at material level
at most r; this is checked before applying normal ordering. -/
theorem amnr_temperature_material_step_budget (α : List (Fin 2)) {r N : ℕ}
    (hbudget : α.length + 2 * (r + 1) ≤ N) (p q : Fin 2) :
    amnrBudget (amnrMixedWord α r ++ [some p, some q]) ≤ N ∧
      amnrMaterialCount (amnrMixedWord α r ++ [some p, some q]) ≤ r ∧
      ∀ (η : List (Fin 2)) (s : ℕ), η.length + 2 * s ≤ amnrBudget (amnrMixedWord α r) → s ≤ r →
        η.length + 2 * s + 2 ≤ N := by
  simp only [amnrBudget_append, amnrMixedWord_budget]
  have htwo : amnrBudget ([some p, some q] : List (Option (Fin 2))) = 2 := by rfl
  have hcount : amnrMaterialCount (amnrMixedWord α r ++ [some p, some q]) = r := by
    rw [amnrMaterialCount_append, amnrMaterialCount_mixed]
    rfl
  rw [htwo, hcount]
  exact ⟨by omega, le_rfl, fun η s hs _ => by omega⟩

end AVenhance.Infra.Section4
