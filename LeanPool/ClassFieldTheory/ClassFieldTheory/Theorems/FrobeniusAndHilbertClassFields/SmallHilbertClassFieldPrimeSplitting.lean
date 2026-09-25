/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
/-!
# Prime splitting in the small Hilbert class field

A finite prime splits completely in the Hilbert class field precisely when
its fractional ideal class is trivial.  Both sides use Mathlib's native
ideal-theoretic objects.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

open GlobalClassFieldComparison renaming
  finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal_of_isSmall →
    finitePrime_splitsCompletely_iff_principal_of_isSmall in
/-- A finite prime splits completely in a small Hilbert class field exactly
when its fractional ideal is principal. -/
theorem finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K E v ↔
      finitePrimeFractionalIdeal v ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
  exact
    finitePrime_splitsCompletely_iff_principal_of_isSmall
    K E hE v

end ClassFieldTheory
