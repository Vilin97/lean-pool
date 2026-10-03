/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
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
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Construction.LimitFieldRegular

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Stream-function estimates (ii): the limit stream `φ = lim φ_m` and `b = ∇^⊥ φ` (`e.def.b`,
    1487-1500),
`c.phim` last sentence (1983-1984), `e.b.reg` (335), `e.phi.m.m-1.bounds` consumed at 9306-9310
(`‖φ - φ_M‖_∞ ≤ C ε_{M+1}^β`), `e.divfree`. Hölder exponents are `α < β - 1` only:
the source proves `C^{1,β'}` for `β' < β - 1` (endpoint not proved: sum of `ε_m^0`). -/
theorem limit_field_regular (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
        ∃ φ : ℝ → Vec 2 → ℝ,
          (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
          (∀ (M : ℕ) (t : ℝ) (x : Vec 2), |φ t x - Φ M t x| ≤ C * epsilon β I.Λ (M + 1) ^ β) ∧
          (∀ t, Differentiable ℝ (φ t)) ∧
          TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
            (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) atTop
            (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
          ∀ α : ℝ, 0 < α → α < β - 1 → IsHolderClass α (streamVel φ) ∧ IsDivFree (streamVel φ) := by
  exact AVenhance.Proofs.limit_field_regular β

end AVenhance
