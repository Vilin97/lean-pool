/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualTerminalStream

/-! # Iterates Actual All Word Stream

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The complete current-stream recurrence uses strictly lower coordinate-word
orders and includes the vanishing order-zero contribution. -/
theorem iterate_increment_terminal_all_word_stream_recurrence_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (hm : 2 ≤ m) (hκ : 0 < κprev)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    (hθp : ∀ t, 0 ≤ t → IsZ2Periodic (θprev t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (i : ℕ) (hi : i ≤ Nstar β) (w : List (Fin 2)) {B L : ℝ} (hL : 0 < L)
    (hg : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 4)
    (D : ℕ → ℝ)
    (hlower : ∀ p : List (Fin 2), p.length < w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (iterateIncrement T i t))) ≤
        B ^ 2 * (((p.length + 2 * i).factorial : ℝ) * L ^ p.length) ^ 2 * D p.length ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (iterateIncrement T i
        z.1)) z.2)
      (iterateWordFlux (fun y => Φ (m - 1) z.1 y • sigmaMat) (iterateIncrement T i z.1) w z.2)| ≤
      κprev / 8 * spaceTimeGradNormSq
        (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T i t))) +
      2 * ((2 : ℝ) ^ 19 * a β I.Λ (m - 1)) * B ^ 2 / L ^ 2 *
        (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 *
        (if w = [] then 0 else D (w.length - 1) ^ 2) +
      16 / κprev * (32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2) ^ 2 * B ^ 2 *
        (2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2) ^ 2 *
        (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range (w.length - 1), (1 / (4 : ℝ)) ^ k * D (w.length - 2 - k) ^ 2 := by
  cases w with
  | nil =>
    have hz (z : AmnrSpace) : vecDot (spaceGrad (iterateSpatialWord [] (iterateIncrement T i z.1))
        z.2)
        (iterateWordFlux (fun y => Φ (m - 1) z.1 y • sigmaMat) (iterateIncrement T i z.1) [] z.2)
            = 0 := by
      simp [iterateWordFlux, iterateSpatialSplits, iterateSpatialWord, sigmaMat, vecDot,
        Fin.sum_univ_two]
      ring
    simp only [hz, integral_zero, abs_zero, ite_true, mul_zero, List.length_nil, Nat.zero_sub,
      Finset.range_zero, Finset.sum_empty, add_zero]
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun _ => vecNormSq_nonneg _)
  | cons j w =>
    have hp := iterate_increment_terminal_stream_flux_bound_of_A3 I hΦ hT hθ hm hκ hA3 hθp
      hs0 hs1 i hi j w hL hg D
      (fun p hp => by simpa only [hp] using hlower p (by simp only [List.length_cons]; omega))
      (fun p hp => hlower p.2 (by
        have ho := iterateSpatialSplits_orders (j :: w) (List.mem_filter.mp hp).1
        have ht : 2 ≤ p.1.length := by simpa using (List.mem_filter.mp hp).2
        omega))
    simpa only [List.length_cons, List.cons_ne_nil, ite_false, Nat.add_sub_cancel,
      show w.length + 1 - 2 = w.length - 1 by omega] using hp

end AVenhance.Infra.Section4
