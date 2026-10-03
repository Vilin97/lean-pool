/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.ScaleTools

/-! Source-scale estimate for the additional transition-window remainder.
The transition-window flux L² estimate remains an explicit source input. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Conditional source-scale estimate for `R46`: the premise is the missing
space-time L² estimate on its exact transition-window flux. -/
theorem timeHMinusOneNorm_R46_sourceScale
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm C : ℝ)
    (T : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm T t))
    (hper : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      IsZ2Periodic (r46Flux I hΦ m κm T t))
    (hsource :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (r46Flux I hΦ m κm T t))) ^ 2) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀)) :
    timeHMinusOneNorm (fun t => R46 I hΦ m κm T t) ≤
      ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀) := by
  exact (timeHMinusOneNorm_R46_le I hΦ m κm T hF hper).trans hsource

end AVenhance.Infra.Section5
end
