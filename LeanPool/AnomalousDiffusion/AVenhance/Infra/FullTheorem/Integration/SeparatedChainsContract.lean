/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements

/-! # Separation persists for the two `θ₀`-independent vanishing-viscosity families

Step "separation persists" of the corrected no-selection argument. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- `p := 2β/(q+1)`; the two `θ₀`-independent diffusivity families `κ_j^{(1)} = ½ ε_{2j+1}^p`,
`κ_j^{(2)} = 2 ε_{2j+1}^p`. For infinitely many cosine modes the two vanishing-viscosity families
    stay
separated in `L²` norm at a fixed time, uniformly in large `j`. -/
def SeparatedChainsContract (β C₀ : ℝ) : Prop :=
  ∃ Λ₅ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₅ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
    ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
    ∃ S : Set ℕ, (∀ N : ℕ, ∃ n ∈ S, N ≤ n) ∧ ∀ n ∈ S, 1 ≤ n ∧
      ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ σ : ℝ, 0 < σ ∧ ∃ J : ℕ, ∀ c : ℝ, c ≠ 0 → ∀ j : ℕ, J ≤ j →
      ∀ θa θb : ℝ → Vec 2 → ℝ,
        IsWeakSolution (streamVel φ) (epsilon β I.Λ (2 * j + 1) ^ (2 * β / (q β + 1)) / 2)
          (fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) θa →
        IsWeakSolution (streamVel φ) (2 * epsilon β I.Λ (2 * j + 1) ^ (2 * β / (q β + 1)))
          (fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) θb →
        σ * |c| ≤ |Real.sqrt (l2NormSq (θa t)) - Real.sqrt (l2NormSq (θb t))|

end AVenhance.Infra.FullTheorem
