/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarLinear

/-!
# The scalar-unit hypothesis from a scalar unit

Under the linear structure induced by a ring isomorphism
`ℂ ≃+* End (𝟙_ D)`, scaling the identity of the unit recovers the
isomorphism, so the scalar-unit hypothesis holds.  Applied to the
ind-completion this supplies the hypothesis upstairs from the one
downstairs.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- Scaling the identity of the unit recovers the scalar. -/
theorem scalarEnd_unit [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (c : ℂ) :
    scalarEnd φ c (𝟙_ D) = scalarHom φ c := by
  rw [scalarEnd, unitors_equal, unitors_inv_equal,
    rightUnitor_naturality, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- **The scalar-unit hypothesis holds** under the induced linear
structure. -/
theorem hasScalarUnit_of_scalarUnit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) :
    letI := linearOfScalarUnit φ
    HasScalarUnit D := by
  let := linearOfScalarUnit φ
  have hval : ∀ c : ℂ, (c • 𝟙 (𝟙_ D) : 𝟙_ D ⟶ 𝟙_ D) =
      scalarHom φ c := by
    intro c
    change scalarSmul φ c (𝟙 (𝟙_ D)) = scalarHom φ c
    rw [scalarSmul_eq, Category.comp_id, scalarEnd_unit]
  constructor
  · intro a b hab
    refine φ.injective ?_
    have h1 := (hval a).symm.trans (hab.trans (hval b))
    exact h1
  · intro f
    refine ⟨φ.symm f, ?_⟩
    change ((φ.symm f) • 𝟙 (𝟙_ D) : 𝟙_ D ⟶ 𝟙_ D) = f
    rw [hval]
    change (φ (φ.symm f) : 𝟙_ D ⟶ 𝟙_ D) = f
    rw [RingEquiv.apply_symm_apply]

end RS
