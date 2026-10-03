/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateGradientPDE

/-! Primitive regularity and lower flux jets for the actual iterate family. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

theorem amnr_tIterates_gradient_smooth {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (i : ℕ) (hi : i ≤ AVenhance.Nstar β) (p : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (amnrTGradient (T i) p) (Ioi (0 : ℝ) ×ˢ univ) := by
  obtain ⟨F, hu⟩ := amnr_tIterates_classical_family I hΦ hθprev hT i hi
  exact amnr_classical_gradient_smooth_infty hu p

theorem amnr_tIterates_flux_smooth {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm) {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (i : ℕ) (hi : i ≤ AVenhance.Nstar β) (q : Fin 2) :
    ContDiffOn ℝ (AVenhance.Nstar β) (amnrIterateFlux I hΦ m κm κprev T i q)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  by_cases hz : i = 0
  · simp only [amnrIterateFlux, ite_eq_left hz]
    exact contDiffOn_const
  · obtain ⟨F, hu⟩ := amnr_tIterates_classical_family I hΦ hθprev hT (i - 1) (by omega)
    simp only [amnrIterateFlux, ite_eq_right hz]
    exact amnr_temperatureFlux_contDiffOn I hΦ hm hκm hu q

/-- Only lower material levels of the preceding temperature enter a flux jet.
Both the zero starting flux and every forced flux are derived from the construction. -/
theorem amnr_tIterates_flux_mixed_bound_of_lower_gradients {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev : ℝ} (hκm : 0 < κm) {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict (Ioi (0 : ℝ) ×ˢ univ))
    {S H A G : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H) (hA : 0 ≤ A) (hG : 0 ≤ G) {cut : ℕ}
    (hAb : ∀ j p v, IsAmnrMixedWord v → amnrBudget v ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) v
        (amnrTemperatureCoefficient I hΦ m κm κprev j p) z| ≤ A * amnrWeight S H v)
    (hgb : ∀ i, i ≤ AVenhance.Nstar β → ∀ p α r,
      α.length + 2 * r ≤ AVenhance.Nstar β → r ≤ cut →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α r) (amnrTGradient (T i) p)) 2 μ ≤
          ENNReal.ofReal (G * amnrWeight S H (amnrMixedWord α r)))
    (i : ℕ) (hi : i ≤ AVenhance.Nstar β) (q : Fin 2) (α : List (Fin 2)) (r : ℕ)
    (hbudget : α.length + 2 * r ≤ AVenhance.Nstar β) (hr : r ≤ cut) :
    eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord α r) (amnrIterateFlux I hΦ m κm κprev T i q)) 2 μ ≤
        ENNReal.ofReal ((2 : ℝ) ^ (AVenhance.Nstar β + 1) * A * G *
          amnrWeight S H (amnrMixedWord α r)) := by
  by_cases hz : i = 0
  · simp only [amnrIterateFlux, ite_eq_left hz]
    change eLpNorm (amnrWord _ _ (0 : AmnrSpace → ℝ)) 2 μ ≤ _
    rw [amnrWord_zero, eLpNorm_zero]
    exact bot_le
  · obtain ⟨F, hu⟩ := amnr_tIterates_classical_family I hΦ hθprev hT (i - 1) (by omega)
    simp only [amnrIterateFlux, ite_eq_right hz]
    exact amnr_temperatureFlux_mixed_bound_of_gradients I hΦ hm hκm hu
      (isOpen_Ioi.prod isOpen_univ) (fun _ hz => hz) hμ hS hH hA hG
      (fun j p v hv hbudget z _ => hAb j p v hv hbudget z)
      (hgb (i - 1) (by omega)) q α r hbudget hr

end AVenhance.Infra.Section4
