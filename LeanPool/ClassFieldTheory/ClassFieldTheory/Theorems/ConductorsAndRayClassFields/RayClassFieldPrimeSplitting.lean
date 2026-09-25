/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusEqOneIffSplitsCompletely
/-!
# Prime splitting in a ray class field

For a prime away from the modulus, the Frobenius-normalized Artin
isomorphism identifies complete splitting with triviality of the
corresponding ray class.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

universe u

open scoped Classical in
/-- A prime away from the modulus splits completely in its ray class field
exactly when its ray class is trivial. -/
theorem finitePrime_splitsCompletelyInRayClassField_iff
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K)
    (R : RayClassFieldRealization K m)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    FinitePrimeSplitsCompletely K R.extension v ↔
      rayClassOfFinitePrime m v hv = 1 := by
  have hunram : Algebra.IsUnramifiedIn (𝓞 R.extension) v.asIdeal :=
    R.unramifiedOutsideModulus.1 v hv
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 R.extension) v.asIdeal
  let : Q.LiesOver v.asIdeal := hQover
  let w : HeightOneSpectrum (𝓞 R.extension) :=
    ⟨Q, hQmax.isPrime,
      Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw : w.asIdeal.LiesOver v.asIdeal := hQover
  constructor
  · intro hsplit
    have hfrob : arithmeticFrobeniusAt (K := K) w = 1 :=
      (arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
        v w hw hunram).2 hsplit
    apply R.artinEquiv.injective
    rw [map_one, R.artin_frobenius v hv w hw]
    exact hfrob
  · intro hclass
    apply (arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
      v w hw hunram).1
    rw [← R.artin_frobenius v hv w hw, hclass, map_one]

end ClassFieldTheory
