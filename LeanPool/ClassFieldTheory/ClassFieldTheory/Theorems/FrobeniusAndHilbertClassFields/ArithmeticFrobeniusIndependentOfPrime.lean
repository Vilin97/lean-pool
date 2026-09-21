/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Frobenius
/-!
# Independence of arithmetic Frobenius from the prime above

At an unramified prime of an abelian extension, all primes above the same
finite base prime give the same canonical arithmetic Frobenius element.
This is the equality, rather than merely conjugacy, needed to avoid choosing
an upstairs prime.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- At an unramified finite prime of an abelian extension, arithmetic
Frobenius is independent of the chosen prime above the base prime. -/
theorem arithmeticFrobeniusAt_eq_of_primesAbove
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hw' : w'.asIdeal.LiesOver v.asIdeal)
    (_hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    arithmeticFrobeniusAt (K := K) w =
      arithmeticFrobeniusAt (K := K) w' := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp
    (isConj_arithFrobAt (𝓞 K) (L ≃ₐ[K] L)
      w.asIdeal w'.asIdeal (hw.over.symm.trans hw'.over))
  calc
    arithmeticFrobeniusAt (K := K) w =
        τ * arithmeticFrobeniusAt (K := K) w * τ⁻¹ := by
      rw [IsMulCommutative.is_comm.comm τ
        (arithmeticFrobeniusAt (K := K) w), mul_assoc,
        mul_inv_cancel, mul_one]
    _ = arithmeticFrobeniusAt (K := K) w' := hτ

end ClassFieldTheory
