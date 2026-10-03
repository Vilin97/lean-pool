/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordForcingContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingFactorials

/-! # Iterates Analytic Matrix Forcing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- An actual smooth matrix forcing has an analytic gradient budget from
its literal coefficient jets and the preceding scalar gradient energies. -/
theorem iterate_analytic_matrix_forcing_energy_bound
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : ∀ t, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (A t))
    (hcoef : ∀ r : List (Fin 2), ContinuousOn
      (fun z : AmnrSpace => iterateMatrixWord (A z.1) r z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    (a : ℕ) {κ C B b L : ℝ} (hL : 0 < L)
    (hg : 2 * (b / L) ^ 2 ≤ 1 / 2)
    (hD : ∀ t x r j k, |iterateMatrixWord (A t) r x j k| ≤
      κ * C * (r.length.factorial : ℝ) * b ^ r.length)
    (hE : ∀ r : List (Fin 2), r.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord r (v t))) ≤
        B ^ 2 * (((r.length + a).factorial : ℝ) * L ^ r.length) ^ 2) :
    spaceTimeGradNormSq (fun t => spaceGrad
      (iterateSpatialWord w (vecDiv (fun y => (A t y).mulVec (spaceGrad (v t) y))))) ≤
      128 * κ ^ 2 * C ^ 2 * B ^ 2 *
        (((w.length + 2 + a).factorial : ℝ) * L ^ (w.length + 2)) ^ 2 := by
  have h := iterate_word_forcing_energy_bound hv (fun t ht => hA t ht.le) hcoef w
    (fun j => κ * C * (j.factorial : ℝ) * b ^ j)
    (fun r => B ^ 2 * (((r + a).factorial : ℝ) * L ^ r) ^ 2) hD hE
    (iterate_word_forcing_gradient_energy_integrable hv hA hcoef w)
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
