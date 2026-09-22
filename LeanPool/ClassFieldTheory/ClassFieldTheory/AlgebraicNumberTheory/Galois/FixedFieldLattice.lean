/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
/-!
# Fixed fields and subgroup lattice operations

Small order-theoretic facts about fixed fields of automorphism subgroups.
They do not depend on class field theory and belong with the general Galois
infrastructure rather than a concrete reciprocity construction.
-/

namespace IntermediateField

/-- Fixed fields turn a supremum of automorphism subgroups into the
intersection of their fixed fields. -/
theorem fixedField_sup_eq_inf
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (S T : Subgroup (Gal(Ω/k))) :
    IntermediateField.fixedField (S ⊔ T) =
      IntermediateField.fixedField S ⊓ IntermediateField.fixedField T := by
  apply le_antisymm
  · exact le_inf
      (IntermediateField.fixedField_le le_sup_left)
      (IntermediateField.fixedField_le le_sup_right)
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    let stabilizer : Subgroup (Gal(Ω/k)) :=
      MulAction.stabilizer (Gal(Ω/k)) x
    have hS : S ≤ stabilizer := by
      intro τ hτ
      change τ x = x
      exact (IntermediateField.mem_fixedField_iff S x).1 hx.1 τ hτ
    have hT : T ≤ stabilizer := by
      intro τ hτ
      change τ x = x
      exact (IntermediateField.mem_fixedField_iff T x).1 hx.2 τ hτ
    have hfix : σ ∈ stabilizer := (sup_le hS hT) hσ
    exact hfix

end IntermediateField
