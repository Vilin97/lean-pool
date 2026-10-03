/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMathlibArtin
/-!
# Artin isomorphism for the small Hilbert class field

The ordinary ideal class group is isomorphic to the Galois group of the
small Hilbert class field.  The displayed compatibility with arithmetic
Frobenius fixes the Artin normalization of the isomorphism.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

open SmallHilbertClassFieldComparison renaming
  arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOfIsSmall →
    smallHilbertGaloisEquivClassGroupOfIsSmall in
open SmallHilbertClassFieldComparison renaming
  arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_prime →
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_prime in
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
    smallHilbertGaloisEquivClassGroupOfIsSmall E hE
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
      exact
        (arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_prime
        E hE v).symm

end ClassFieldTheory
