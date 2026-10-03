/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalHighFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamJetProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxTimeEnergy

/-! High stream forcing for the actual finite increments under the stream-regularity estimates. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The stream-regularity estimates control the actual high stream-jet part of the increment
 energy recurrence. All scalar bounds are at least two orders below w. -/
theorem iterate_increment_terminal_high_stream_bound_of_A3 {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (hm : 2 ≤ m) (hκ : 0 < κprev)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {s : ℝ} (hs1 : s ≤ 1)
    (i : ℕ) (hi : i ≤ Nstar β) (w : List (Fin 2)) {B L : ℝ} (hL : 0 < L)
    (hg : 2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2 ≤ 1 / 4)
    (D : ℕ → ℝ)
    (hE : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => decide (2 ≤ p.1.length)),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (iterateIncrement T i t))) ≤
        B ^ 2 * (((p.2.length + 2 * i).factorial : ℝ) * L ^ p.2.length) ^ 2 * D p.2.length ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (iterateIncrement T i
        z.1)) z.2)
      (iterateSplitFlux ((iterateSpatialSplits w).filter (fun p => decide (2 ≤ p.1.length)))
        (fun y => Φ (m - 1) z.1 y • sigmaMat) (iterateIncrement T i z.1) z.2)| ≤
      κprev / 8 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement
          T i t))) +
      16 / κprev * (32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2) ^ 2 * B ^ 2 *
        (2 * ((256 * (epsilon β I.Λ (m - 1))⁻¹) / L) ^ 2) ^ 2 *
        (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 *
        ∑ k ∈ Finset.range (w.length - 1), (1 / (4 : ℝ)) ^ k * D (w.length - 2 - k) ^ 2 := by
  obtain ⟨hφ, _⟩ := hΦ.2 m (by omega)
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ hi
  have ht := iterate_terminal_analytic_high_flux_bound hs1 hu hu w (2 * i) hκ hL hg D
    (fun p _ => iterate_stream_matrix_word_continuousOn hφ.1.contDiffOn p.1)
    (κ := κprev) (C := (32 * a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ 2) / κprev)
    (B := B) (fun t x p hp j k => by
      have hh := iterate_stream_matrix_profile_of_A3 I hΦ hm hA3 t p.1
        (by simpa using (List.mem_filter.mp hp).2) x j k
      convert hh using 1
      field_simp) hE
  convert ht using 1
  field_simp

end AVenhance.Infra.Section4
