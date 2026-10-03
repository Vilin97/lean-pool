/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.CorrTime

/-! Statement file: `chiMK` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `Χ^κ_{m,k}(t, x) = (χ_{m,k,e₁}, χ_{m,k,e₂})`, the explicit formula `e.Chimk.formula`
(label 2831), WITH THE SIGN FORCED BY `e.parabcorr.k` (label 2791); a correction to the source:
the printed formula lacks the minus sign. -/
def chiMK (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  (-(I.corrTime κ m k t)) • uShear β I.Λ m k x

end Ingredients
end AVenhance
