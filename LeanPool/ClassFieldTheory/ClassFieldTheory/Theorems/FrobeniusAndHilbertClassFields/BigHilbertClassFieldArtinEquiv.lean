/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldMathlibArtin
/-!
# Artin isomorphism for the big Hilbert class field

The narrow ideal class group is isomorphic to the Galois group of the big
Hilbert class field.  The displayed compatibility with arithmetic Frobenius
fixes the Artin normalization of the isomorphism.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- The narrow class group acts through the Frobenius-normalized Artin
isomorphism on a big Hilbert class field. -/
theorem bigHilbertClassField_artinEquiv
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    ∃ artin : RayClassGroup (narrowRayClassModulus K) ≃*
        (E ≃ₐ[K] E),
      ∀ (v : HeightOneSpectrum (𝓞 K))
        (w : HeightOneSpectrum (𝓞 E)),
        w.asIdeal.LiesOver v.asIdeal →
          artin (narrowRayClassOfFinitePrime v) =
            arithmeticFrobeniusAt (K := K) w := by
  let g :=
    GlobalClassFieldComparison.arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOfIsBig E hE
  let artin : RayClassGroup (narrowRayClassModulus K) ≃* (E ≃ₐ[K] E) :=
    (GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup K).trans g.symm
  refine ⟨artin, ?_⟩
  intro v w hw
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    hE.1 v w.asIdeal inferInstance hw
  apply g.injective
  calc
    g (artin (narrowRayClassOfFinitePrime v)) =
        QuotientGroup.mk' (RayClass.narrowDenominator (K := K))
          (IdeleGroup.finitePrimeIdele v) := by
      rw [show g (artin (narrowRayClassOfFinitePrime v)) =
          GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup K
            (narrowRayClassOfFinitePrime v) from by
        simp only [artin, MulEquiv.trans_apply, g.apply_symm_apply]]
      exact GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup_prime v
    _ = g (arithmeticFrobeniusAt (K := K) w) := by
      rw [← GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := E) v w hw hunram]
      exact
        (GlobalClassFieldComparison.arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_prime
        E hE v).symm

end ClassFieldTheory
