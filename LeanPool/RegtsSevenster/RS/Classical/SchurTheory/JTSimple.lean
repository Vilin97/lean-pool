/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTIntChar
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTIrreducible

/-!
# The Jacobi–Trudi character is plus-or-minus a native character
-/

namespace RS

open scoped Classical in
/-- **The Jacobi–Trudi character is `±` a single native
character.** -/
theorem jtChar_pm_simple (μ : YoungDiagram) :
    ∃ S₀ : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))),
      IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
        S₀ ∧
      ((∀ π, jtChar μ π = nChar S₀ π) ∨
        (∀ π, jtChar μ π = - nChar S₀ π)) := by
  obtain ⟨J, hJ, ε, T, hT, hε, hchar⟩ := jtChar_eq_sum_sign_nChar μ
  let := hJ
  exact jt_pm_nChar μ ε T hT hchar

end RS
