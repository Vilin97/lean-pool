/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigOriginal
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
/-!
# Arithmetic Artin reciprocity for any big Hilbert class field

The maximal finite-prime-unramified abelian extension has the same idèle-class
norm subgroup as the selected big Hilbert class field.  Arithmetic global
reciprocity therefore gives its narrow-class-group Artin isomorphism.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

variable {K : Type} [Field K] [NumberField K]

local instance bigHilbertArtinIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- An intrinsic big Hilbert class field is equivalent over `K` to the
selected realization. -/
noncomputable def bigHilbertClassFieldEquivOfIsBig
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    E ≃ₐ[K] GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K := by
  let H := GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K
  let f := Classical.choice
    (GlobalClassFieldTheory.GlobalClassFields.finiteUnramifiedAbelianExtension_nonempty_algHom_bigHilbertClassField
      K E ((isUnramifiedAtFinitePlaces_iff_original K E).mp hE.1))
  have hdim : Module.finrank K E = Module.finrank K H :=
    (GlobalClassFieldComparison.bigHilbertClassField_degree_eq_narrowClassGroup_card_of_isBig K E hE).trans
      (GlobalClassFieldComparison.bigHilbertClassField_degree_eq_narrowClassGroup_card K).symm
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp f.injective
  exact AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩

/-- Every intrinsic big Hilbert class field has the selected field's
idèle-class norm subgroup. -/
theorem bigHilbertClassField_ideleClassNorm_range_of_isBig
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    (_root_.ideleClassNorm K E).range =
      GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup
        (K := K) := by
  let H := GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField K
  let e : E ≃ₐ[K] H := bigHilbertClassFieldEquivOfIsBig E hE
  calc
    (_root_.ideleClassNorm K E).range = (_root_.ideleClassNorm K H).range :=
      ordinaryIdeleClassNorm_range_algEquiv e
    _ = _ :=
      GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_ideleClassNorm_range_over_original
        (K := K)

/-- The arithmetic Artin isomorphism for an intrinsic big Hilbert class
field, with target the narrow ideal class group. -/
noncomputable def arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_of_isBig
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    (E ≃ₐ[K] E) ≃* RayClass.NarrowClassGroup K := by
  let reciprocity : (E ≃ₐ[K] E) ≃*
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K E).range) :=
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv
      K E).toMulEquiv
  let transport :
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K E).range) ≃*
      (IdeleClassGroup K ⧸
        GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup
          (K := K)) :=
    QuotientGroup.quotientMulEquivOfEq
      (bigHilbertClassField_ideleClassNorm_range_of_isBig E hE)
  let narrow :
      (IdeleClassGroup K ⧸
        GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup
          (K := K)) ≃* RayClass.NarrowClassGroup K :=
    GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)
  exact (reciprocity.trans transport).trans narrow

/-- The intrinsic arithmetic reciprocity equivalence sends a global
norm-residue symbol to the represented big-Hilbert norm class. -/
theorem arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_globalNormResidue
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E)
    (c : IdeleClassGroup K) :
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_of_isBig E hE
      (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
        K E c) =
      GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)
        (QuotientGroup.mk'
          (GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup
            (K := K)) c) := by
  change
    GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)
      (QuotientGroup.quotientMulEquivOfEq
        (bigHilbertClassField_ideleClassNorm_range_of_isBig E hE)
        (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv
          K E
          (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom
            K E c))) = _
  have hReciprocity :=
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue
      (K := K) (L := E) c
  calc
    _ = GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)
          (QuotientGroup.quotientMulEquivOfEq
            (bigHilbertClassField_ideleClassNorm_range_of_isBig E hE)
            (QuotientGroup.mk' (_root_.ideleClassNorm K E).range c)) :=
      congrArg
        (fun q =>
          GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := K)
            (QuotientGroup.quotientMulEquivOfEq
              (bigHilbertClassField_ideleClassNorm_range_of_isBig E hE) q))
        hReciprocity
    _ = _ := rfl

/-- The intrinsic arithmetic Artin symbol of a finite prime is represented
by its one-place prime idèle in the narrow class group. -/
theorem arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_prime
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_of_isBig E hE
      (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := E) v) =
      QuotientGroup.mk' (RayClass.narrowDenominator (K := K))
        (IdeleGroup.finitePrimeIdele v) := by
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
  rw [arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_globalNormResidue]
  exact GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
    (IdeleGroup.finitePrimeIdele v)

/-- The public narrow ideal ray class of a finite prime is its normalized
one-place prime idèle class. -/
theorem narrowRayClassGroupEquivNarrowClassGroup_prime
    (v : HeightOneSpectrum (𝓞 K)) :
    narrowRayClassGroupEquivNarrowClassGroup K
      (narrowRayClassOfFinitePrime v) =
      QuotientGroup.mk' (RayClass.narrowDenominator (K := K))
        (IdeleGroup.finitePrimeIdele v) := by
  change (RayClass.rayClassGroupNarrowZeroEquivNarrowClassGroup (K := K))
    (rayClassGroupEquivOriginalIdele K (narrowRayClassModulus K)
      (narrowRayClassOfFinitePrime v)) = _
  rw [narrowRayClassOfFinitePrime,
    rayClassGroupEquivOriginalIdele_prime]
  rfl

end ClassFieldTheory.GlobalClassFieldComparison
