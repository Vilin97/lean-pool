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

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

theorem IsStreamSeq.unique {β : ℝ} {I : Ingredients β} {Φ Ψ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (hΨ : IsStreamSeq I Ψ) : Φ = Ψ := by
  have key : ∀ n, Φ n = Ψ n := by
    intro n
    induction n with
    | zero => rw [hΦ.1, hΨ.1]
    | succ n ih =>
      obtain ⟨h1, e1⟩ := hΦ.2 (n + 1) (by omega)
      obtain ⟨h2, e2⟩ := hΨ.2 (n + 1) (by omega)
      rw [e1, e2]
      have : ∀ (φ ψ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (hψ : IsAdmissibleStream ψ),
          φ = ψ → I.nextStream (n + 1) φ hφ = I.nextStream (n + 1) ψ hψ := by
        rintro φ ψ hφ hψ rfl; rfl
      exact this _ _ _ _ ih
  exact funext key

end AVenhance
