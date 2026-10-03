/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedStream

/-! Full nonnegative energies control each actual terminal stream pairing. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The terminal signed stream integral is bounded using full nonnegative
 energies, after the actual spatial skew transfer on that terminal cell. -/
theorem iterate_truncated_stream_pairing_bound_full
    {ψ u v : ℝ → Vec 2 → ℝ} {H : ℝ} (hH : 0 < H)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => ψ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hψp : ∀ t, 0 < t → IsZ2Periodic (ψ t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    (hjet : ∀ t x j, |spaceGrad (ψ t) x j| ≤ H) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
      ((ψ z.1 z.2 • sigmaMat).mulVec (spaceGrad (v z.1) z.2))| ≤
      H * ((∫ z in timeCube, u z.1 z.2 ^ 2) +
        spaceTimeGradNormSq (fun t => spaceGrad (v t))) := by
  have ht := iterate_truncated_stream_pairing_bound hH hψ hu hv hs hs1 hψp hup hvp hjet
  have hui := iterate_timeCube_integrable_of_continuousOn (hu.continuousOn.pow 2)
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 ^ 2) timeCube at hui
  have h₁ := iterate_truncated_nonnegative_integral_le hui (fun _ => sq_nonneg _) hs1
  have h₂ := iterate_truncated_nonnegative_integral_le
    (iterate_word_gradient_energy_integrable hv []) (fun _ => vecNormSq_nonneg _) hs1
  exact ht.trans (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hH.le)

end AVenhance.Infra.Section4
