/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.OrdinaryClassGroupComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallOriginal
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
/-!
# Arithmetic Artin reciprocity for any small Hilbert class field

The intrinsic small Hilbert class field is unique up to a base-field
equivalence.  Therefore its actual idèle-class norm subgroup is the same as
that of the selected class field.  Arithmetic global reciprocity then gives
the Artin map, with its prime normalization obtained from the prime idèle.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.SmallHilbertClassFieldComparison

variable {K : Type} [Field K] [NumberField K]

local instance smallHilbertArtinIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- All intrinsic small Hilbert class fields have the selected field's
actual idèle-class norm subgroup. -/
theorem smallHilbertClassField_ideleClassNorm_range_of_isSmall
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    (_root_.ideleClassNorm K E).range =
      GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroup
        (K := K) := by
  let H := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField K
  let e : E ≃ₐ[K] H := GlobalClassFieldComparison.smallHilbertClassFieldEquivOfIsSmall K E hE
  calc
    (_root_.ideleClassNorm K E).range =
        (RelativeIdeleGroup.classNorm K E).range :=
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := E)
    _ = (RelativeIdeleGroup.classNorm K H).range :=
      (ideleClassNorm_range_algEquiv (K := K) e).symm
    _ = (_root_.ideleClassNorm K H).range :=
      (ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := H)).symm
    _ = _ :=
      GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_ideleClassNorm_range_over_original
        (K := K)

private noncomputable def arithmeticHilbertClassGroupEquivOfNormRange
    (E : FiniteAbelianExtension K)
    (hNorm : (_root_.ideleClassNorm K E).range =
      GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroup
        (K := K)) :
    (E ≃ₐ[K] E) ≃* ClassGroup (𝓞 K) := by
  let N : Subgroup (IdeleClassGroup K) := (_root_.ideleClassNorm K E).range
  let S : Subgroup (IdeleClassGroup K) :=
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroup
      (K := K)
  have hNS : N = S := hNorm
  let e₁ : (E ≃ₐ[K] E) ≃* (IdeleClassGroup K ⧸ N) :=
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv
      K E).toMulEquiv
  let e₂ : (IdeleClassGroup K ⧸ N) ≃* (IdeleClassGroup K ⧸ S) :=
    QuotientGroup.quotientMulEquivOfEq hNS
  let e₃ : (IdeleClassGroup K ⧸ S) ≃* ClassGroup (𝓞 K) :=
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)
  exact (e₁.trans e₂).trans e₃

/-- Arithmetic reciprocity identifies the Galois group of any intrinsic
small Hilbert class field with the ordinary ideal class group. -/
noncomputable def arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_of_isSmall
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    (E ≃ₐ[K] E) ≃* ClassGroup (𝓞 K) :=
  arithmeticHilbertClassGroupEquivOfNormRange E
    (smallHilbertClassField_ideleClassNorm_range_of_isSmall E hE)

/-- Intrinsic arithmetic reciprocity sends a global norm-residue symbol to
its represented class in the small-Hilbert norm quotient. -/
theorem arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_globalNormResidue
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E)
    (c : IdeleClassGroup K) :
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_of_isSmall E hE
      (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
        K E c) =
      GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)
        (QuotientGroup.mk'
          (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroup
            (K := K)) c) := by
  change
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)
      (QuotientGroup.quotientMulEquivOfEq
        (smallHilbertClassField_ideleClassNorm_range_of_isSmall E hE)
        (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv
          K E
          (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
            K E c))) = _
  have hReciprocity :=
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue
      (K := K) (L := E) c
  calc
    _ = GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
          (K := K)
          (QuotientGroup.quotientMulEquivOfEq
            (smallHilbertClassField_ideleClassNorm_range_of_isSmall E hE)
            (QuotientGroup.mk' (_root_.ideleClassNorm K E).range c)) :=
      congrArg
        (fun q =>
          GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
            (K := K)
            (QuotientGroup.quotientMulEquivOfEq
              (smallHilbertClassField_ideleClassNorm_range_of_isSmall E hE) q))
        hReciprocity
    _ = _ := rfl

/-- At every finite prime, the arithmetic Artin symbol has the usual prime
ideal class under the intrinsic Hilbert reciprocity equivalence. -/
theorem arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_prime
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_of_isSmall E hE
      (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := E) v) =
      ClassGroup.mk K (finitePrimeFractionalIdeal v) := by
  let c : IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (IdeleGroup.finitePrimeIdele v)
  have hArtin :
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := E) v =
      GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
        K E c := by
    rw [GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin]
    exact (DFunLike.congr_fun
      (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
        (K := K) (L := E))
      (IdeleGroup.finitePrimeIdele v)).symm
  rw [hArtin]
  rw [arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_globalNormResidue]
  rw [GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk]
  rw [IdeleGroup.idealClass_finitePrimeIdele]
  rfl

end ClassFieldTheory.SmallHilbertClassFieldComparison
