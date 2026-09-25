/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
/-!
# Principalization in the small Hilbert class field

The principal ideal theorem says that extension to the Hilbert class field
makes every integral ideal of the base number field principal.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every integral ideal becomes principal in a small Hilbert class field. -/
theorem ideals_becomePrincipalInSmallHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    ∀ I : Ideal (𝓞 K),
      (I.map (algebraMap (𝓞 K) (𝓞 E))).IsPrincipal := by
  exact GlobalClassFieldComparison.ideals_becomePrincipalInSmallHilbertClassField_of_isSmall K E hE

end ClassFieldTheory
