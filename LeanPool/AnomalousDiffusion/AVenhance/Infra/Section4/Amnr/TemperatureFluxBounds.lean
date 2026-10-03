/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.LocalFiniteNormalOrderL2

/-! Actual canonical temperature flux jets at the finite source budget. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Temperature gradient contracted with the temperature coefficient matrix. -/
def amnrTemperatureFlux {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κm κprev : ℝ) (u : ℝ → Vec 2 → ℝ) (j : Fin 2) (z : AmnrSpace) : ℝ :=
  ∑ p : Fin 2, amnrTemperatureCoefficient I hΦ m κm κprev j p z * amnrTGradient u p z

/-- The canonical flux estimate is an actual finite Leibniz contraction.
This conditional calculus helper takes lower temperature jets, leaving their
PDE induction as a separate source proof. -/
theorem amnr_temperatureFlux_mixed_bound_of_gradients {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev : ℝ} (hκm : 0 < κm)
    {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev F u₀ u)
    {U : Set AmnrSpace} (hU : IsOpen U) (hUpos : U ⊆ Ioi (0 : ℝ) ×ˢ univ)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {S H A G : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H) (hA : 0 ≤ A) (hG : 0 ≤ G)
    {cut : ℕ}
    (hAb : ∀ j p v, IsAmnrMixedWord v → amnrBudget v ≤ AVenhance.Nstar β → ∀ z ∈ U,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) v
        (amnrTemperatureCoefficient I hΦ m κm κprev j p) z| ≤ A * amnrWeight S H v)
    (hgb : ∀ p α r, α.length + 2 * r ≤ AVenhance.Nstar β → r ≤ cut →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α r) (amnrTGradient u p)) 2 μ ≤
          ENNReal.ofReal (G * amnrWeight S H (amnrMixedWord α r)))
    (j : Fin 2) (α : List (Fin 2)) (r : ℕ)
    (hbudget : α.length + 2 * r ≤ AVenhance.Nstar β) (hcut : r ≤ cut) :
    eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord α r) (amnrTemperatureFlux I hΦ m κm κprev u j)) 2 μ ≤
        ENNReal.ofReal ((2 : ℝ) ^ (AVenhance.Nstar β + 1) * A * G *
          amnrWeight S H (amnrMixedWord α r)) := by
  apply amnrWord_sum_mul_L2_le hU hμ le_rfl
    (amnr_previous_velocity_contDiff I hΦ hm (AVenhance.Nstar β)).contDiffOn
    (fun p => (amnr_temperatureCoefficient_contDiff I hΦ hm hκm κprev j p).contDiffOn)
    (fun p => (amnr_classical_gradient_smooth hu p (AVenhance.Nstar β)).mono hUpos)
    hS hH hA hG (amnrMixedWord α r) (by rw [amnrMixedWord_budget]; exact hbudget)
  · intro p v hv z hz
    exact hAb j p v ((amnrMixedWord_mixed α r).sublist hv)
      ((amnrBudget_sublist hv).trans (by rw [amnrMixedWord_budget]; exact hbudget)) z hz
  · intro p v hv
    obtain ⟨η, s, rfl, hs, hbud⟩ := amnrMixedWord_subword_normalForm hv
    exact hgb p η s (hbud.trans hbudget) (hs.trans hcut)

end AVenhance.Infra.Section4
