/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements

/-! # Analytic case of `r.LeBron.2`

Uniform-in-`κ` time-Hölder bound in `L²` along `𝒦 = permissibleSet` for solutions with analytic
`C^∞` data: for a limit stream
`φ`, every weak solution of the transport–diffusion equation with drift `streamVel φ`, `κ ∈ 𝒦`,
satisfies `‖θ(t) − θ(s)‖_{L²} ≤ K (1 + R^{-p}) ‖θ₀‖_{H¹} |t − s|^μ`, with `μ, p` depending only on
`β, C₀`, and `K` independent of `κ`, `R`, `θ₀`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The analytic case of `r.LeBron.2`. -/
def AnalyticUniformContract (β C₀ : ℝ) : Prop :=
  ∃ μ p Λ₂ : ℝ, 0 < μ ∧ 0 ≤ p ∧
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₂ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
    ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ κ ∈ permissibleSet β I.Λ, ∀ R : ℝ, 0 < R →
    ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
      IsThetaAnalytic R θ₀ →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolution (streamVel φ) κ θ₀ θ →
      IsHolderTimeL2 μ (K * (1 + R ^ (-p)) *
        Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀))) θ

end AVenhance.Infra.FullTheorem
