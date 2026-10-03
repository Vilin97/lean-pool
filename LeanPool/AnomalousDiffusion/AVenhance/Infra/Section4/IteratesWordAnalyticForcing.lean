/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingCoefficients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordActualForcingEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingFactorials

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
theorem iterate_increment_analytic_TForcing_energy_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hm : 1 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (i : ℕ) (hi : i ≤ Nstar β) (w : List (Fin 2))
    (a : ℕ) {κ C B b L : ℝ} (hL : 0 < L)
    (hg : 2 * (b / L) ^ 2 ≤ 1 / 2)
    (hD : ∀ t x r, ∀ j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) r x j k| ≤ κ * C * (r.length.factorial : ℝ) * b ^ r.length)
    (hE : ∀ r : List (Fin 2), r.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord r (iterateIncrement T i t))) ≤
        B ^ 2 * (((r.length + a).factorial : ℝ) * L ^ r.length) ^ 2) :
    spaceTimeGradNormSq (fun t => spaceGrad
      (iterateSpatialWord w (I.TForcing hΦ m κm κprev (iterateIncrement T i) t))) ≤
      128 * κ ^ 2 * C ^ 2 * B ^ 2 *
        (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 := by
  have h := iterate_increment_word_TForcing_energy_bound I hΦ hT hθ hm hκm hflow
    i hi w (fun j => κ * C * (j.factorial : ℝ) * b ^ j)
    (fun r => B ^ 2 * (((r + a).factorial : ℝ) * L ^ r) ^ 2) hD hE
  have he : (64 * ∑ j ∈ Finset.range (w.length + 3),
      (Nat.choose (w.length + 2) j : ℝ) ^ 2 * (2 : ℝ) ^ j *
        (κ * C * (j.factorial : ℝ) * b ^ j) ^ 2 *
        (B ^ 2 * (((w.length + 2 - j + a).factorial : ℝ) * L ^ (w.length + 2 - j)) ^ 2)) =
      64 * κ ^ 2 * C ^ 2 * B ^ 2 * (∑ j ∈ Finset.range (w.length + 3),
      (Nat.choose (w.length + 2) j : ℝ) ^ 2 * (2 : ℝ) ^ j *
        ((j.factorial : ℝ) * b ^ j) ^ 2 *
        (((w.length + 2 - j + a).factorial : ℝ) * L ^ (w.length + 2 - j)) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  have ht := mul_le_mul_of_nonneg_left
    (iterate_forcing_factorial_profile_sum_le (w.length + 2) a hL hg)
    (by positivity : 0 ≤ 64 * κ ^ 2 * C ^ 2 * B ^ 2)
  apply h.trans
  convert ht using 1
  ring

end AVenhance.Infra.Section4
