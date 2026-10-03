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
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.NextStreamFinite

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Well-definedness of the series in `e.psi.recursion`: for every `(t,x)` the family of
terms is summable (indeed finitely supported, since `supp ζ_{m,k} ⊆ [(k-2/3)τ_m,(k+2/3)τ_m]`). -/
theorem Ingredients.nextStream_summable {β : ℝ} (I : Ingredients β) (m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (t : ℝ) (x : Vec 2) :
    Summable fun k : ℤ => I.nextStreamTerm m φ hφ t x k :=
  summable_of_hasFiniteSupport (Infra.Construction.nextStreamTerm_support_finite I m φ hφ t x)

end AVenhance
