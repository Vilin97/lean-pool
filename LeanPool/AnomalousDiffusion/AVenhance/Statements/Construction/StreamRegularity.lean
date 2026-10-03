/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Stream-function estimates (i): `p.SAMS.regularity` first display `e.phi.m.m-1.bounds`
    (1538-1547; constants
universal, as in the source), `e.phimbounds.subbed` (1746-1753, for `n ≥ 2` as in the source;
    universal constants; consumed
by `c.flowreg`), and `c.phim` `e.C1beta.phi.m` (1967-1982;
`C = C(β)`, placed before `I`, `m`). Uniform in `m ≥ 1` and `t ∈ ℝ`, `Λ = I.Λ`. -/
theorem stream_regularity (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
        ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
          (∀ n : ℕ,
            barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
              ENNReal.ofReal (10 * epsilon β I.Λ m ^ β)) ∧
          (∀ n : ℕ, 2 ≤ n →
            barNorm n (2 ^ 8 * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (2 ^ 5 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
                (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
          (∀ n : ℕ, n ≤ 1 →
            barNorm n (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
              ENNReal.ofReal (C * epsilon β I.Λ m ^ n)) := by
  exact AVenhance.Proofs.stream_regularity β

end AVenhance
