/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.ScaleTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Source-scale estimate for the time-cutoff term. The missing §4 bound is
stated on its spatial L² norm; the negative-norm transfer is proved. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Conditional source-scale estimate for `cutoff1`, after inserting the
source-level spatial L² bound into Poincaré duality. -/
theorem timeHMinusOneNorm_cutoff1_sourceScale
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm C : ℝ)
    (T : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (hL2 : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      MemL2On unitCube (cutoff1 I hΦ m κm T t))
    (hmean : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      MeanZeroOn unitCube (cutoff1 I hΦ m κm T t))
    (hsource :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          Real.sqrt (l2NormSq (cutoff1 I hΦ m κm T t))) ^ 2) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀)) :
    timeHMinusOneNorm (fun t => cutoff1 I hΦ m κm T t) ≤
      ENNReal.ofReal (section5SourceScale β I.Λ m κm C θ₀) := by
  exact timeHMinusOneNorm_le_L2_of_sourceScale hL2 hmean hsource

end AVenhance.Infra.Section5
end
