/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticErrorGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxTimeEnergy

/-! Actual increment material-error gradient energy under the stream-regularity estimates. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The stream-regularity estimates and actual lower increment gradients imply the all-order
 material-error gradient estimate. No material energy estimate is assumed. -/
theorem iterate_increment_error_gradient_energy_bound_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (i : ℕ) (hi : i ≤ Nstar β) (w : List (Fin 2)) {G L : ℝ} (hL : 0 < L)
    (hg : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 2)
    (hE : ∀ q : List (Fin 2), q.length ≤ w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (iterateIncrement T i t))) ≤
        G ^ 2 * (((q.length + 2 * i).factorial : ℝ) * L ^ q.length) ^ 2) :
    spaceTimeGradNormSq (fun t x => spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2) w
      (fun z => iterateIncrement T i z.1 z.2) (t, y)) x) ≤
      136 * (8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) ^ 2 *
        (256 * (epsilon β I.Λ (m - 1))⁻¹) ^ 2 * G ^ 2 *
        (((w.length + 1 + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 := by
  obtain ⟨hφ, _⟩ := hΦ.2 m (by omega)
  have hb : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.contDiffOn
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ hi
  apply iterate_analytic_material_error_gradient_energy_bound hb hv w (2 * i) hL hg
    (B := 8192 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1)) (G := G)
  · intro t x q hq j
    exact iterate_velocity_analytic_profile_of_A3 I hΦ hm hA3 t q hq x j
  · exact hE

end AVenhance.Infra.Section4
