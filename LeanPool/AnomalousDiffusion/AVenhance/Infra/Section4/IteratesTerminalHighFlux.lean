/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedFilteredFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHighStreamFactorials

/-! Actual high coefficient-order flux with the quadratic norm kernel. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Analytic high coefficient jets and lower scalar energies bound the
 actual high-order flux. All scalar premises have word length at most n-2. -/
theorem iterate_terminal_analytic_high_flux_bound
    {s : ℝ} (hs1 : s ≤ 1)
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (a : ℕ) {κ C B r L : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hg : 2 * (r / L) ^ 2 ≤ 1 / 4) (D : ℕ → ℝ)
    (hcoef : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => decide (2 ≤ p.1.length)),
      ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => decide (2 ≤ p.1.length)) → ∀ j k,
      |iterateMatrixWord (A t) p.1 x j k| ≤ κ * C * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hE : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => decide (2 ≤ p.1.length)),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤
        B ^ 2 * (((p.2.length + a).factorial : ℝ) * L ^ p.2.length) ^ 2 * D p.2.length ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateSplitFlux ((iterateSpatialSplits w).filter (fun p => decide (2 ≤ p.1.length)))
        (A z.1) (v z.1) z.2)| ≤
      κ / 8 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      16 * κ * C ^ 2 * B ^ 2 * (2 * (r / L) ^ 2) ^ 2 *
        (((w.length + a).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range (w.length - 1), (1 / (4 : ℝ)) ^ k * D (w.length - 2 - k) ^ 2 := by
  have ht := iterate_truncated_allocated_filtered_flux_bound hs1 hu hv w (fun j => decide (2 ≤ j))
    hcoef hκ (fun j => κ * C * (j.factorial : ℝ) * r ^ j)
    (fun j => B ^ 2 * (((j + a).factorial : ℝ) * L ^ j) ^ 2 * D j ^ 2) hjet hE
  have he : (16 / κ * ∑ j ∈ Finset.range (w.length + 1),
      (if decide (2 ≤ j) then (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j *
        (κ * C * (j.factorial : ℝ) * r ^ j) ^ 2 *
        (B ^ 2 * (((w.length - j + a).factorial : ℝ) * L ^ (w.length - j)) ^ 2 * D (w.length - j)
            ^ 2) else 0)) =
      16 * κ * C ^ 2 * B ^ 2 * (∑ j ∈ Finset.range (w.length + 1), if 2 ≤ j then
        (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j * ((j.factorial : ℝ) * r ^ j) ^ 2 *
        (((w.length - j + a).factorial : ℝ) * L ^ (w.length - j)) ^ 2 * D (w.length - j) ^ 2 else
            0) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : 2 ≤ j
    · simp only [hj, decide_true, ite_true]
      field_simp
    · simp [hj]
  rw [he] at ht
  have hs := mul_le_mul_of_nonneg_left
    (iterate_high_stream_factorial_series_le w.length a hL hg D)
    (by positivity : 0 ≤ 16 * κ * C ^ 2 * B ^ 2)
  exact ht.trans (add_le_add le_rfl (by simpa only [mul_assoc] using hs))

end AVenhance.Infra.Section4
