/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.UShear

/-! Statement file: `zetaProd` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- The coefficient `ζ̂_{m,l_k}(s) ζ_{m,k}(s)` in `e.parabcorr.k`, `e.Chimk.formula`, `e.psi.m`. -/
def zetaProd (m : ℕ) (k : ℤ) (s : ℝ) : ℝ :=
  I.hatZetaML m (lIdx β I.Λ m k) s * I.zetaMK m k s

end Ingredients
end AVenhance
