/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMathlibArtin
/-!
# Artin isomorphism for the small Hilbert class field

The ordinary ideal class group is isomorphic to the Galois group of the
small Hilbert class field.  The displayed compatibility with arithmetic
Frobenius fixes the Artin normalization of the isomorphism.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- The ordinary class group acts through the Frobenius-normalized Artin
isomorphism on a small Hilbert class field. -/
theorem smallHilbertClassField_artinEquiv
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    ∃ artin : RayClassGroup (ordinaryRayClassModulus K) ≃*
        (E ≃ₐ[K] E),
      ∀ (v : HeightOneSpectrum (𝓞 K))
        (w : HeightOneSpectrum (𝓞 E)),
        w.asIdeal.LiesOver v.asIdeal →
          artin (ordinaryRayClassOfFinitePrime v) =
            arithmeticFrobeniusAt (K := K) w := by
  let g :=
    SmallHilbertClassFieldComparison.arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_of_isSmall E hE
  let artin : RayClassGroup (ordinaryRayClassModulus K) ≃* (E ≃ₐ[K] E) :=
    (ordinaryRayClassGroupEquivClassGroup (K := K)).trans g.symm
  refine ⟨artin, ?_⟩
  intro v w hw
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    hE.1.1 v w.asIdeal inferInstance hw
  apply g.injective
  calc
    g (artin (ordinaryRayClassOfFinitePrime v)) =
        ClassGroup.mk K (finitePrimeFractionalIdeal v) := by
      rw [show g (artin (ordinaryRayClassOfFinitePrime v)) =
          ordinaryRayClassGroupEquivClassGroup
            (ordinaryRayClassOfFinitePrime v) from by
        simp only [artin, MulEquiv.trans_apply, g.apply_symm_apply]]
      exact ordinaryRayClassGroupEquivClassGroup_prime v
    _ = g (arithmeticFrobeniusAt (K := K) w) := by
      rw [← GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := E) v w hw hunram]
      exact (SmallHilbertClassFieldComparison.arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_prime
        E hE v).symm

end ClassFieldTheory
