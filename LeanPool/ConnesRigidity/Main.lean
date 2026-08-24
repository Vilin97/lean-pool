/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
import LeanPool.ConnesRigidity.Core
import LeanPool.ConnesRigidity.Paper.Section7

/-!
Completion boundary for Zhou's Theorem A.
-/

namespace Connes

universe v

/-- Zhou's Theorem A. The only external mathematical input is the cited EJZK
property-(T) theorem for `EL₃(𝔽₂[t])`; every construction and all other
paper arguments are proved in this project. Paper: §7. -/
theorem theoremA
    (hEJZK : HasKazhdanPropertyT.{0, v} PaperPropertyT.elementaryGroup) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT.{0, v} Γ₁ ∧ HasKazhdanPropertyT.{0, v} Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ Nonempty (Γ₁ ≃* Γ₂) := by
  exact PaperTheoremACompletion.theoremA
    ⟨hEJZK⟩

end Connes
