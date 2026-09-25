/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusIndependentOfPrime
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
/-!
# Arithmetic Frobenius under transport of a prime

An automorphism of an abelian extension may move a prime above a fixed base
prime. At an unramified prime, the arithmetic Frobenius element is unchanged.
The prime transport is Mathlib's equivalence of height-one spectra induced by
the automorphism of the ring of integers.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- In an abelian extension, transporting an unramified prime by a
`K`-automorphism does not change its arithmetic Frobenius element. -/
theorem arithmeticFrobeniusAt_mapAlgEquiv
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (σ : L ≃ₐ[K] L)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    arithmeticFrobeniusAt (K := K)
        ((HeightOneSpectrum.equivOfRingEquiv
          (RingOfIntegers.mapAlgEquiv σ).toRingEquiv) w) =
      arithmeticFrobeniusAt (K := K) w := by
  let e : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 L) := RingOfIntegers.mapAlgEquiv σ
  have hwσ :
      ((HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv) w).asIdeal.LiesOver
        v.asIdeal := by
    change (w.asIdeal.comap e.symm.toRingHom).LiesOver v.asIdeal
    refine ⟨?_⟩
    change v.asIdeal =
      (w.asIdeal.comap e.symm.toRingHom).comap
        (algebraMap (𝓞 K) (𝓞 L))
    rw [Ideal.comap_comap]
    have he : e.symm.toRingHom.comp (algebraMap (𝓞 K) (𝓞 L)) =
        algebraMap (𝓞 K) (𝓞 L) := by
      apply RingHom.ext
      intro x
      exact e.symm.commutes x
    rw [he]
    exact hw.over
  exact (arithmeticFrobeniusAt_eq_of_primesAbove v w
    ((HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv) w)
    hw hwσ hunram).symm

end ClassFieldTheory
