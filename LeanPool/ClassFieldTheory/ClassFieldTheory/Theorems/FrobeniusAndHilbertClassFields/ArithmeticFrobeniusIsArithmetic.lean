/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
/-!
# Arithmetic Frobenius satisfies the residue-field congruence

This statement exposes Mathlib's intrinsic arithmetic Frobenius, rather than
an element named through a particular implementation of the global Artin
map.  It is therefore the precise bridge to `IsArithFrobAt` that downstream
ramification arguments can use.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

universe u v

open NumberField IsDedekindDomain

/-- The chosen arithmetic Frobenius at `w` satisfies Mathlib's defining
residue-field Frobenius congruence. -/
theorem arithmeticFrobeniusAt_isArithFrobAt
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    IsArithFrobAt (𝓞 K) (arithmeticFrobeniusAt (K := K) w) w.asIdeal := by
  exact IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal

end ClassFieldTheory
