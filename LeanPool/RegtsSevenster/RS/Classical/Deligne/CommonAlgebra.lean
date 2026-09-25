/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndBigTensorUnit

/-!
# A common extension of a family of algebras

Any small family of nonzero commutative algebras of the
ind-completion sits inside a single nonzero commutative algebra:
their tensor product.  This is the device of Deligne 2.11, which
uses it to make every object mixed and every short exact sequence
split simultaneously.

The index type is put in bijection with a well-ordered one so
that the slot order required by the tensor product is available.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable {C : Type v}

/-- **A family of nonzero algebras has a common nonzero
extension**: their tensor product, into which each factor maps by
a morphism of monoid objects. -/
theorem exists_common_algebra [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [SymmetricCategory (Ind C)]
    (hu : HasScalarUnit C) {ι : Type v}
    (B : ι → Ind C) [∀ i, MonObj (B i)] [∀ i, IsCommMonObj (B i)]
    (hB : ∀ i, MonObj.one (X := B i) ≠ 0) :
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      ∀ i, ∃ φ : B i ⟶ 𝔸, IsMonHom φ := by
  let : DecidableRel (WellOrderingRel (α := ι)) :=
    Classical.decRel _
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  refine ⟨bigTensor B, bigTensorMon B, bigTensorCommMon B,
    bigTensorUnit_ne_zero_ind B hu hB, ?_⟩
  intro i
  exact ⟨bigTensorOf B i, isMonHom_bigTensorOf B i⟩

end RS
