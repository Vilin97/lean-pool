/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
/-!
# Uniqueness of the small Hilbert class field inside a separable closure

The maximality condition determines an actual intermediate field, not merely
an isomorphism class.  It does not distinguish a unique field automorphism.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- Two small Hilbert class fields inside the same separable closure are
equal as intermediate fields. -/
theorem smallHilbertClassFields_eq
    (K : Type u) [Field K] [NumberField K]
    (E F : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E)
    (hF : IsSmallHilbertClassField F) :
    E.1 = F.1 := by
  have hEF : E.1 ≤ F.1 := by
    obtain ⟨f⟩ := hF.2 E hE.1
    let σ : E →ₐ[K] SeparableClosure K := F.1.val.comp f
    have hσ : σ.fieldRange = E.1 := AlgHom.fieldRange_of_normal σ
    rw [← hσ]
    intro x hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact (f y).property
  have hFE : F.1 ≤ E.1 := by
    obtain ⟨f⟩ := hE.2 F hF.1
    let σ : F →ₐ[K] SeparableClosure K := E.1.val.comp f
    have hσ : σ.fieldRange = F.1 := AlgHom.fieldRange_of_normal σ
    rw [← hσ]
    intro x hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact (f y).property
  exact le_antisymm hEF hFE

end ClassFieldTheory
