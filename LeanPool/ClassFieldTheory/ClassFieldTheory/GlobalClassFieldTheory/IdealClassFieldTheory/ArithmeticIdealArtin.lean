/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
/-!
# The ideal Artin map in arithmetic Frobenius normalization

For a defining modulus of a genuine finite abelian class field, this
module composes the ideal ray-class quotient with the topological
arithmetic global norm-residue equivalence.  The resulting map sends an
ordinary prime ideal to arithmetic Frobenius, has the genuine idèle
norm kernel, and induces the canonical ideal class-field isomorphism.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

attribute [local instance]
  ideleClassSubgroupNormal idealArtinKernelNormal

/-- The genuine Galois-valued ideal Artin map in arithmetic Frobenius
normalization. -/
noncomputable def arithmeticIdealArtinGaloisMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m →*
      (L ≃ₐ[K] L) :=
  (Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
      K L).toMulEquiv.toMonoidHom.comp
    (idealArtinMap m
      ((_root_.ideleClassNorm K L).range) hm)

/-- Evaluating the arithmetic ideal Artin map is evaluation of the ideal
class map followed by arithmetic global reciprocity. -/
@[simp]
theorem arithmeticIdealArtinGaloisMap_apply
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a =
      Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
        K L
        (idealArtinMap m
          ((_root_.ideleClassNorm K L).range) hm a) :=
  rfl

/-- The arithmetic ideal Artin map is exactly the inverse of the
geometrically normalized map on every ideal. -/
@[simp]
theorem arithmeticIdealArtinGaloisMap_eq_inv_idealArtinGaloisMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a =
      (idealArtinGaloisMap
        (K := K) (L := L) m hm a)⁻¹ := by
  rw [arithmeticIdealArtinGaloisMap_apply,
    Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply,
    Reciprocity.globalNormResidueContinuousMulEquiv_apply,
    idealArtinGaloisMap_apply]

/-- The arithmetic ideal Artin map is surjective. -/
theorem arithmeticIdealArtinGaloisMap_surjective
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    Function.Surjective
      (arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm) :=
  (Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
      K L).surjective.comp
    (idealArtinMap_surjective m
      ((_root_.ideleClassNorm K L).range) hm)

/-- Arithmetic normalization leaves the defining ideal group
unchanged. -/
@[simp]
theorem arithmeticIdealArtinGaloisMap_ker
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (arithmeticIdealArtinGaloisMap
      (K := K) (L := L) m hm).ker =
      idealArtinKernel m
        ((_root_.ideleClassNorm K L).range) hm := by
  ext a
  let e :=
    Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv K L
  let x :=
    idealArtinMap m
      ((_root_.ideleClassNorm K L).range) hm a
  change
    e x = 1 ↔ x = 1
  have hOne : e (1 : IdeleClassGroup K) = 1 :=
    e.map_one
  constructor
  · intro h
    exact e.injective (h.trans hOne.symm)
  · intro h
    exact (congrArg e h).trans hOne

/-- The canonical ideal class-field isomorphism in arithmetic
Frobenius normalization. -/
noncomputable def arithmeticIdealClassQuotientEquivGaloisGroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        idealArtinKernel m
          ((_root_.ideleClassNorm K L).range) hm ≃*
      (L ≃ₐ[K] L) :=
  (idealClassQuotientEquivNormQuotient m
      ((_root_.ideleClassNorm K L).range) hm).trans
    (Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
      K L).toMulEquiv

/-- The arithmetic ideal class-field equivalence sends a quotient
representative to its arithmetic ideal Artin symbol. -/
@[simp]
theorem arithmeticIdealClassQuotientEquivGaloisGroup_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealClassQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm) a) =
      arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a :=
  rfl

/-- The arithmetic ideal Artin map and the arithmetic idèlic Artin
map form the genuine ideal/idèle compatibility square. -/
theorem
    arithmeticIdealArtinGaloisMap_primeToIdealMap_eq_globalArtin
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm
        (RayClass.primeToIdealMap m a) =
      Reciprocity.arithmeticGlobalArtinMonoidHom
        K L (a : IdeleGroup K) := by
  rw [arithmeticIdealArtinGaloisMap_apply]
  rw [GlobalClassFields.idealArtinMap_primeToIdealMap]
  change
    Reciprocity.arithmeticGlobalNormResidueMonoidHom K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K)) =
      Reciprocity.arithmeticGlobalArtinMonoidHom
        K L (a : IdeleGroup K)
  exact
    DFunLike.congr_fun
      (Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
          (K := K) (L := L))
      (a : IdeleGroup K)

/-- A prime ideal outside the defining modulus maps to its genuine
arithmetic prime Artin element. -/
theorem
    arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm
        (RayClass.primeToModulusIdeal m v hv) =
      GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v := by
  rw [← GlobalClassFields.primeToIdealMap_finitePrimeIdele m v hv]
  exact
    arithmeticIdealArtinGaloisMap_primeToIdealMap_eq_globalArtin
      (K := K) (L := L) m hm
      ⟨IdeleGroup.finitePrimeIdele v,
        GlobalClassFields.finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩

/-- Direct local form: a prime ideal outside the modulus maps to the
arithmetic chosen local Artin value of normalized order one. -/
theorem
    arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticChosenFinitePlaceArtin
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm
        (RayClass.primeToModulusIdeal m v hv) =
      Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
        K L v (FiniteIdeleGroup.chosenLocalOrderSection v 1) := by
  rw [
    arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin,
    GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin]

/-- The arithmetic ideal class-field equivalence sends the class of a
prime ideal to its arithmetic Frobenius automorphism. -/
theorem
    arithmeticIdealClassQuotientEquivGaloisGroup_primeIdeal
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    arithmeticIdealClassQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm)
          (RayClass.primeToModulusIdeal m v hv)) =
      GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v := by
  rw [
    arithmeticIdealClassQuotientEquivGaloisGroup_mk,
    arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin]

end IdealClassFieldTheory
end GlobalClassFieldTheory
