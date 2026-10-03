/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiM

/-! Statement file: `psiM` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `ψ_m(t, x) := ∑_{k ∈ 2ℤ+1} ζ̂_{m,l_k}(t) ζ_{m,k}(t) ψ_{m,k}(x)`, `e.psi.m` (label 2755). -/
def psiM (m : ℕ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, I.zetaProd m k t * psi β I.Λ m k x

end Ingredients
end AVenhance
