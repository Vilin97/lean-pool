/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedAllocatedFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingFactorials

/-! Analytic forcing bound for the actual differentiated flux. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Conditional coefficient jets and preceding increment energies give an
actual flux estimate. No current energy or forcing estimate is assumed. -/
theorem iterate_terminal_small_analytic_word_flux_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2))
    (hcoef : ∀ p ∈ iterateSpatialSplits w,
      ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {κ C B ρ b L : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hg : 2 * (b / L) ^ 2 ≤ 1 / 2) (a : ℕ)
    (hD : ∀ t x p, p ∈ iterateSpatialSplits w → ∀ j k,
      |iterateMatrixWord (A t) p.1 x j k| ≤ κ * C * ρ * (p.1.length.factorial : ℝ) * b ^ p.1.length)
    (hE : ∀ p ∈ iterateSpatialSplits w,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤
        B ^ 2 * (((p.2.length + a).factorial : ℝ) * L ^ p.2.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateWordFlux (A z.1) (v z.1) w z.2)| ≤
      κ / 8 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      32 * κ * C ^ 2 * ρ ^ 2 * B ^ 2 *
        (((w.length + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have h := iterate_truncated_allocated_word_flux_bound hs1 hu hv w hcoef hκ
    (fun j => κ * C * ρ * (j.factorial : ℝ) * b ^ j)
    (fun r => B ^ 2 * (((r + a).factorial : ℝ) * L ^ r) ^ 2) hD hE
  have he : (16 / κ * ∑ j ∈ Finset.range (w.length + 1),
      (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j *
        (κ * C * ρ * (j.factorial : ℝ) * b ^ j) ^ 2 *
        (B ^ 2 * (((w.length - j + a).factorial : ℝ) * L ^ (w.length - j)) ^ 2)) =
      16 * κ * C ^ 2 * ρ ^ 2 * B ^ 2 * (∑ j ∈ Finset.range (w.length + 1),
      (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j *
        ((j.factorial : ℝ) * b ^ j) ^ 2 *
        (((w.length - j + a).factorial : ℝ) * L ^ (w.length - j)) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [he] at h
  have ht := mul_le_mul_of_nonneg_left
    (iterate_forcing_factorial_profile_sum_le w.length a hL hg)
    (by positivity : 0 ≤ 16 * κ * C ^ 2 * ρ ^ 2 * B ^ 2)
  apply h.trans
  apply add_le_add le_rfl
  convert ht using 1
  ring

end AVenhance.Infra.Section4
