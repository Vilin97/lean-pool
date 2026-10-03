/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialComposition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.RecursionIncrement
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents

/-! Quantitative material bounds for one transported term in the stream
recursion. The transport identity removes all spatial derivatives from the
time cutoffs; the remaining spatial seminorm is the App. B.2/B.3 composition
bound already used in the Section 2 induction. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

/-- Product of the two time cutoffs in the material recursion. -/
def MaterialRecursion.materialRecursionCutoff {β : ℝ} (I : Ingredients β)
    (m : ℕ) (k : ℤ) : ℝ → ℝ := fun t =>
  I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t

theorem MaterialRecursion.iteratedTimeDerivative_eq_iteratedDeriv
    {q : ℝ → ℝ} (ell : ℕ) :
    iteratedTimeDerivative ell q = iteratedDeriv ell q := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      funext t
      simp only [iteratedTimeDerivative, iteratedDeriv_succ]
      rw [ih]

end AVenhance.Infra.Construction

end
