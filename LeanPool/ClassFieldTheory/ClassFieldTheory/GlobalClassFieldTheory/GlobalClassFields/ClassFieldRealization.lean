/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Mathlib.FieldTheory.Galois.Abelian
/-!
# Concrete realization of finite abelian subextensions

A finite abelian subextension in the abstract class-formation lattice is
represented by two nested closed subgroups of an ambient Galois group.  Its
upper relative fixed field is an actual finite extension of the lower fixed
field.  The quotient-to-Galois-group equivalence transports the commutativity
carried by the abstract package, so this actual extension is abelian Galois.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open scoped IsMulCommutative

universe u v w

private theorem algEquiv_commutes_algebraMap_of_base_equiv
    {K : Type u} {K' : Type v} {L : Type w}
    [Field K] [Field K'] [Field L]
    [Algebra K L] [Algebra K' L]
    (e : K ≃+* K')
    (h : ∀ x : K,
      algebraMap K L x =
        algebraMap K' L (e x))
    (f : L ≃ₐ[K] L)
    (x : K') :
    f (algebraMap K' L x) =
      algebraMap K' L x := by
  have hbase :
      algebraMap K L (e.symm x) =
        algebraMap K' L x := by
    calc
      algebraMap K L (e.symm x) =
          algebraMap K' L (e (e.symm x)) :=
        h (e.symm x)
      _ = algebraMap K' L x :=
        congrArg (algebraMap K' L) (e.apply_symm_apply x)
  calc
    f (algebraMap K' L x) =
        f (algebraMap K L (e.symm x)) :=
      congrArg f hbase.symm
    _ = algebraMap K L (e.symm x) :=
      f.commutes (e.symm x)
    _ = algebraMap K' L x := hbase

/-- Abelian Galois structure transports across an equivalence of base fields
when the two scalar maps into the common top field commute with that
equivalence. The Galois part is supplied separately, typically by Mathlib's
`IsGalois.of_equiv_equiv`; this theorem transports commutativity of the actual
automorphism group. -/
theorem IsAbelianGalois.of_base_equiv
    {K : Type u} {K' : Type v} {L : Type w}
    [Field K] [Field K'] [Field L]
    [Algebra K L] [Algebra K' L]
    [IsGalois K L] [IsAbelianGalois K' L]
    (e : K ≃+* K')
    (h : ∀ x : K,
      algebraMap K L x =
        algebraMap K' L (e x)) :
    IsAbelianGalois K L := by
  refine
    { is_comm.comm := fun σ τ => ?_ }
  let σ' : L ≃ₐ[K'] L :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (algEquiv_commutes_algebraMap_of_base_equiv e h σ)
  let τ' : L ≃ₐ[K'] L :=
    AlgEquiv.ofRingEquiv (f := τ.toRingEquiv)
      (algEquiv_commutes_algebraMap_of_base_equiv e h τ)
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun (mul_comm σ' τ') x

variable
    {k Ω : Type}
    [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    {K : ClosedSubgroup (Gal(Ω/k))}

/-- The relative fixed field represented by a finite abelian subextension is
finite-dimensional over the fixed field represented by its base subgroup. -/
noncomputable instance
    finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional
    [hKfinite : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(Ω / k)) K (le_baseField K))]
    (L : FiniteAbelianSubextension K) :
    FiniteDimensional
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω L.below) :=
  abstractRelativeFixedField_finiteDimensional
    k Ω K L.field L.below hKfinite L.finite

/-- The actual relative fixed field represented by a finite abelian
subextension is an abelian Galois extension of the actual base fixed field. -/
noncomputable instance
    finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (L : FiniteAbelianSubextension K) :
    IsAbelianGalois
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω L.below) := by
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω L.below
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      k Ω K L.field L.below L.normal
  let e : L.extensionQuotient ≃* Gal(E / F) :=
    L.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L.field L.below L.normal)
  refine { is_comm.comm := fun σ τ ↦ ?_ }
  exact e.symm.injective (by
    simpa only [map_mul] using
      mul_comm (e.symm σ) (e.symm τ))

end GlobalClassFields
end GlobalClassFieldTheory
