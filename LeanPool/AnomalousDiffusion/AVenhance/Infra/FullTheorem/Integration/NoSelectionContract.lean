/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements

/-! # The no-selection argument

For the two `θ₀`-independent vanishing-viscosity families `κ_j^{(1)} = ½ ε_{2j+1}^p`,
`κ_j^{(2)} = 2 ε_{2j+1}^p` (`p = 2β/(qβ+1)`), with cosine data `c cos(2π n x₀)` for infinitely many
modes `n`, the two families have limits (transport weak solutions) which are `HolderTimeL2Le ν
    η`-close
for large `j`, and whose norms differ at some time in `[0,1]`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The no-selection statement (conditional-input form of the repaired no-selection argument). -/
def NoSelectionContract (β C₀ : ℝ) : Prop :=
  ∃ ν Λ₄ : ℝ, 0 < ν ∧
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₄ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
    ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
    ∃ S : Set ℕ, (∀ N : ℕ, ∃ n ∈ S, N ≤ n) ∧ (∀ n ∈ S, 1 ≤ n) ∧
    ∀ n ∈ S, ∀ c : ℝ, c ≠ 0 →
    ∀ θ : ℝ → ℝ → Vec 2 → ℝ,
      (∀ κ : ℝ, 0 < κ → IsWeakSolution (streamVel φ) κ
        (fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) (θ κ)) →
      ∃ θ₁ θ₂ : ℝ → Vec 2 → ℝ,
        IsTransportWeakSolution (streamVel φ)
          (fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) θ₁ ∧
        IsTransportWeakSolution (streamVel φ)
          (fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) θ₂ ∧
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, HolderTimeL2Le ν η
          (fun t x => θ (epsilon β I.Λ (2 * j + 1) ^ (2 * β / (q β + 1)) / 2) t x - θ₁ t x)) ∧
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, HolderTimeL2Le ν η
          (fun t x => θ (2 * epsilon β I.Λ (2 * j + 1) ^ (2 * β / (q β + 1))) t x - θ₂ t x)) ∧
        ∃ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ₁ t) ≠ l2NormSq (θ₂ t)

end AVenhance.Infra.FullTheorem
