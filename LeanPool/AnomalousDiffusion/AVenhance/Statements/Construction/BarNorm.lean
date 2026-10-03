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

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `e.barf` (source 933-936): `⟦f⟧_{n,R} = (n+1)²/(n! Rⁿ) · sup_{|α|=n} ‖∂^α f‖_{L^∞(ℝ²)}`,
for `f ∈ C^∞(ℝ²)` and radius `R > 0` (every use below has `R > 0`).
The supremum over multi-indices `|α| = n` is the supremum over ordered coordinate tuples
`i : Fin n → Fin 2` of the iterated derivative on basis vectors (for `C^n` functions all
orderings of one multi-index agree by symmetry of the derivative). `ℝ≥0∞`-valued, so no
supremum is junk; `R⁻ⁿ` is taken in `ℝ≥0∞`, so `R ≤ 0` gives `⊤` (never a vacuous bound). -/
def barNorm (n : ℕ) (R : ℝ) (f : Vec 2 → ℝ) : ENNReal :=
  ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * (ENNReal.ofReal R)⁻¹ ^ n *
    ⨆ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) ⊤ volume

end AVenhance
