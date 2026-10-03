/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Normie2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.ScaleTools

/-! Source-scale estimate for `normie2`, conditional on the Section 3/4
space-time L² estimate for its vector flux. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Conditional source-scale estimate for `normie2` from its flux bound. -/
theorem timeHMinusOneNorm_normie2_sourceScale
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm C : ℝ)
    (T : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞) (normie2Flux I hΦ m κm T t))
    (hper : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      IsZ2Periodic (normie2Flux I hΦ m κm T t))
    (hsource :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (normie2Flux I hΦ m κm T t))) ^ 2) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀)) :
    timeHMinusOneNorm (fun t => normie2 I hΦ m κm T t) ≤
      ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀) := by
  exact (timeHMinusOneNorm_normie2_le I hΦ m κm T hF hper).trans hsource

end AVenhance.Infra.Section5
end
