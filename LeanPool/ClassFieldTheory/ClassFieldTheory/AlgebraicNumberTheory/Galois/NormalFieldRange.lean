/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Normal.Basic
/-!
# Ranges of embeddings of normal extensions

This file records the intrinsic image of a normal field extension inside an
ambient field: every embedding over the base has the same intermediate-field
range.
-/

namespace AlgHom

/-- Two embeddings of a normal extension into a common ambient field have the
same intermediate-field range. -/
theorem fieldRange_eq_of_normal
    {F L Ω : Type*} [Field F] [Field L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [Normal F L]
    (f g : L →ₐ[F] Ω) :
    f.fieldRange = g.fieldRange := by
  have fieldRange_le_of_normal
      (u v : L →ₐ[F] Ω) : u.fieldRange ≤ v.fieldRange := by
    let : Normal F v.fieldRange :=
      (AlgEquiv.transfer_normal v.equivFieldRange).mp
        (inferInstance : Normal F L)
    have hrange :
        (u.comp v.equivFieldRange.symm.toAlgHom).fieldRange =
          v.fieldRange :=
      AlgHom.fieldRange_of_normal _
    intro x hx
    rw [← hrange]
    rcases AlgHom.mem_fieldRange.mp hx with ⟨y, rfl⟩
    exact AlgHom.mem_fieldRange.mpr ⟨v.equivFieldRange y, by simp⟩
  exact le_antisymm
    (fieldRange_le_of_normal f g) (fieldRange_le_of_normal g f)

end AlgHom
