/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq

/-! # The flip-flop statement for the `kappaSeq` chains

With `sHat_m := κ_m / (√(9/80) ε_m^{β+γ})`, chains topped at `t ε_M^{2β/(q+1)}`, `t ∈ {1/2, 2}`,
satisfy: `log sHat_m` alternates around `± log (t √(80/9))` up to `O(ε_m^ρ)`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Flip-flop for `kappaSeq` chains topped at `t ε_M^{2β/(q+1)}`, `t ∈ {1/2, 2}`: with the
normalisation `sHat_m := κ_m / (√(9/80) ε_m^{β+γ})`, `log sHat_m` alternates around
`± log(t √(80/9))`. -/
def FlipFlopContract (β C₀ : ℝ) : Prop :=
  ∃ ρ C Λ₁ : ℝ, 0 < ρ ∧
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₁ ≤ (I.Λ : ℝ) →
    ∀ t : ℝ, (t = 1 / 2 ∨ t = 2) →
    ∀ M : ℕ, 2 ≤ M → ∀ m : ℕ, 1 ≤ m → m ≤ M - 1 →
      |Real.log (I.kappaSeq (t * epsilon β I.Λ M ^ (2 * β / (q β + 1))) M m /
          (Real.sqrt (9 / 80) * epsilon β I.Λ m ^ (β + gamma β))) -
        (-1 : ℝ) ^ (M - 1 - m) * Real.log (t * Real.sqrt (80 / 9))| ≤
        C * epsilon β I.Λ m ^ ρ

end AVenhance.Infra.FullTheorem
