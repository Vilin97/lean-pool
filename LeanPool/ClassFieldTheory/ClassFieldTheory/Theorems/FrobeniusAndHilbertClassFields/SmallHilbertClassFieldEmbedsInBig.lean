/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
/-!
# Inclusion of the small Hilbert class field in the big one

Everywhere-unramified extensions are unramified at finite places, so the
maximality property of a big Hilbert class field supplies the embedding.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- Every small Hilbert class field embeds over the base into every big
Hilbert class field. -/
theorem smallHilbertClassField_embedsInBig
    (K : Type u) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E)
    (F : FiniteAbelianExtension K) (hF : IsBigHilbertClassField F) :
    Nonempty (E →ₐ[K] F) :=
  hF.2 E hE.1.1

end ClassFieldTheory
