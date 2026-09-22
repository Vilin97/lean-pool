/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
/-!
# Arithmetic Frobenius at a finite prime
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

open scoped Classical in
/-- Mathlib's chosen arithmetic Frobenius lift at a finite prime of the
extension field.  At a ramified prime such a lift need not be unique. -/
def arithmeticFrobeniusAt
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (w : HeightOneSpectrum (𝓞 L)) : L ≃ₐ[K] L :=
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal

end ClassFieldTheory
