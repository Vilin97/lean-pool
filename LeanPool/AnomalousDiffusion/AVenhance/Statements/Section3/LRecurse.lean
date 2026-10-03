/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.IsCorrectorSol
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Section3.LRecurse

/-! Statement file: `l_recurse` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- `l.recurse`. Constants `c < C` depend only on `β` (and the three cutoff-constant bounds
`C₀`), placed before `I`, `Λ = I.Λ`, `κ`, `M`, `m`. Ranges: see the errata
(`e.kappam.bound` for `m ∈ {1,…,M-1}`; `e.exprat.bound` for `m ∈ {2,…,M-1}`).
Corrected form: the exponent in `e.exprat.bound` is `4δ`, not the printed `2δ`
(the identity at source line 3715 gives `8δ`, not `4δ`). -/
theorem l_recurse (β : ℝ) (C₀ : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
        ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
        ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
          (∀ m : ℕ, 1 ≤ m → m < M →
            c * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) ≤ I.kappaAt κ m (M - m) ∧
            I.kappaAt κ m (M - m) ≤ C * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β))) ∧
          (∀ m : ℕ, 2 ≤ m → m < M →
            c * epsilon β I.Λ (m - 1) ^ (4 * delta β) ≤
              epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ∧
            epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤
              C * epsilon β I.Λ (m - 1) ^ (4 * delta β)) := by
  exact AVenhance.Proofs.l_recurse β C₀

end AVenhance
