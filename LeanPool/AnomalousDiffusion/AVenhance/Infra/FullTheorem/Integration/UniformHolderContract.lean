/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements

/-! # general `H¹` case of `r.LeBron.2`

Uniform-in-`κ` time-Hölder bound in `L²` along `𝒦 = permissibleSet` for solutions with general
mean-zero `H¹` data: the exponent
`μ` and threshold `Λ₃` depend only on `β, C₀`; `C` depends only on the limit stream. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The general mean-zero `H¹` case of `r.LeBron.2`. -/
def UniformHolderContract (β C₀ : ℝ) : Prop :=
  ∃ μ Λ₃ : ℝ, 0 < μ ∧
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₃ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
    ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2), IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
    ∀ κ ∈ permissibleSet β I.Λ, ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolution (streamVel φ) κ θ₀ θ →
      HolderTimeL2Le μ (C * Real.sqrt (l2NormSq θ₀ + gradNormSq Dθ₀)) θ

end AVenhance.Infra.FullTheorem
