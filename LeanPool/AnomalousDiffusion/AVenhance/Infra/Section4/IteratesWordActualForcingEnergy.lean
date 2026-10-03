/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingCoefficients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordForcingContinuity

/-! Actual all-order material forcing energy for the increments. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual differentiated TForcing gradient is bounded by preceding
increment energies and actual coefficient jets. Natural integrability and
regularity are discharged from the scalar carrier and flow smoothness. -/
theorem iterate_increment_word_TForcing_energy_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hm : 1 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (i : ℕ) (hi : i ≤ Nstar β) (w : List (Fin 2)) (D E : ℕ → ℝ)
    (hD : ∀ t x r, ∀ j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) r x j k| ≤ D r.length)
    (hE : ∀ r : List (Fin 2), r.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord r (iterateIncrement T i t))) ≤ E
          r.length) :
    spaceTimeGradNormSq (fun t => spaceGrad
      (iterateSpatialWord w (I.TForcing hΦ m κm κprev (iterateIncrement T i) t))) ≤
      64 * ∑ j ∈ Finset.range (w.length + 3),
        (Nat.choose (w.length + 2) j : ℝ) ^ 2 * (2 : ℝ) ^ j * (D j) ^ 2 * E (w.length + 2 - j) := by
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ hi
  have hfs (t : ℝ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hA (t : ℝ) (_ : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := contDiff_const.add
      (AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hfs t))
  have hc := iterate_TForcing_coefficient_word_continuousOn I hΦ hm hκm κprev hflow
  exact iterate_word_forcing_energy_bound hv (fun t ht => hA t ht.le) hc w D E hD hE
    (iterate_word_forcing_gradient_energy_integrable hv hA hc w)

end AVenhance.Infra.Section4
