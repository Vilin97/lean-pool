/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
/-!
# The small Hilbert class field is a subfield of the big one

The extensions are intermediate fields of one separable closure, so the
result is literal containment, not only an abstract embedding.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

universe u

/-- Every small Hilbert class field is contained in every big Hilbert class
field inside the fixed separable closure. -/
theorem smallHilbertClassField_le_big
    (K : Type u) [Field K] [NumberField K]
    (E F : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E)
    (hF : IsBigHilbertClassField F) :
    E.1 ≤ F.1 := by
  obtain ⟨f⟩ := hF.2 E hE.1.1
  let σ : E →ₐ[K] SeparableClosure K := F.1.val.comp f
  have hσ : σ.fieldRange = E.1 := AlgHom.fieldRange_of_normal σ
  rw [← hσ]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  exact (f y).property

end ClassFieldTheory
