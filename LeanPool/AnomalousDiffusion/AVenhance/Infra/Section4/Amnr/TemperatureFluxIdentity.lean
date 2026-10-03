/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureSpatialWords

/-! The actual forcing in the ordered flux calculus. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Flux regularity uses only the proved finite Kmat order and actual
classical temperature regularity on the positive-time domain. -/
theorem amnr_temperatureFlux_contDiffOn {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {b : ℝ → Vec 2 → Vec 2} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κprev F u₀ u) (j : Fin 2) :
    ContDiffOn ℝ (AVenhance.Nstar β) (amnrTemperatureFlux I hΦ m κm κprev u j)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  apply ContDiffOn.sum
  intro p _
  exact (amnr_temperatureCoefficient_contDiff I hΦ hm hκm κprev j p).contDiffOn.mul
    (amnr_classical_gradient_smooth hu p (AVenhance.Nstar β))

/-- The matrix divergence equals the ordered coordinate divergence of
its actual flux, with no forcing estimate or evolution equation assumed. -/
theorem amnr_temperatureForcing_eq_flux_divergence {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {b : ℝ → Vec 2 → Vec 2} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κprev F u₀ u) (B : AmnrSpace → Vec 2) :
    EqOn (fun z => I.TForcing hΦ m κm κprev u z.1 z.2)
      (fun z => ∑ j : Fin 2, amnrOp B (some j) (amnrTemperatureFlux I hΦ m κm κprev u j) z)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  intro z hz
  have hvec : (fun y => (I.Kmat κm m z.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm z.1 y).mulVec (AVenhance.spaceGrad (u z.1) y)) =
      (fun y => fun j : Fin 2 => amnrTemperatureFlux I hΦ m κm κprev u j (z.1, y)) := by
    funext y j
    simp only [Matrix.mulVec, dotProduct, amnrTemperatureFlux, amnrTemperatureCoefficient,
      amnrTGradient]
  unfold AVenhance.Ingredients.TForcing
  dsimp only
  rw [hvec]
  unfold AVenhance.vecDiv
  apply Finset.sum_congr rfl
  intro j _
  have hN := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
  have hd := ((amnr_temperatureFlux_contDiffOn I hΦ hm hκm hu j).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hz)).differentiableAt
      (by exact_mod_cast (show AVenhance.Nstar β ≠ 0 by omega))
  exact (amnrOp_space (b := B) hd j).symm

end AVenhance.Infra.Section4
