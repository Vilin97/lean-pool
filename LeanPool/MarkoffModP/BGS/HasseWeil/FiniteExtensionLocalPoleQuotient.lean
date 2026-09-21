/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.DVRLocalPoleOrder
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionLocalPoleSpace
import LeanPool.MarkoffModP.BGS.HasseWeil.LocalPoleCumulativeQuotient
import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceInfinityPlaceIncrement

/-!
# Exact local principal-part dimensions at exhaustive places

The abstract DVR calculation in `LocalPoleFiltration` is instantiated at
both the finite and infinity places of a finite separable extension of
`K(X)`.  Thus every successive local pole layer has dimension exactly the
degree of the corresponding exhaustive place.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped nonZeroDivisors Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance localQuotientConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance localQuotientConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

section FinitePlace

local instance (priority := 10) localQuotientPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance localQuotientPolynomialTower : IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance localQuotientFiniteClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap K[X] (RatFuncFiniteIntegralClosure K L)).comp
      (algebraMap K K[X]))

local instance localQuotientFiniteClosureConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance localQuotientFiniteClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance localQuotientFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance localQuotientPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance localQuotientFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance localQuotientFiniteClosureDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance localQuotientFiniteClosureFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) L (RatFuncFiniteIntegralClosure K L)

/-- Every finite-place local principal-part layer has dimension exactly the
degree of that place. -/
theorem finiteExtensionLocalPoleSpace_inl_step_finrank
    (q : FiniteExtensionFinitePlace K L) (n : ℕ) :
    Module.finrank K
        (finiteExtensionLocalPoleSpace K L (.inl q) (n + 1) ⧸
          Submodule.comap
            (finiteExtensionLocalPoleSpace K L (.inl q) (n + 1)).subtype
            (finiteExtensionLocalPoleSpace K L (.inl q) n)) =
      finiteExtensionPlaceDegree K L (.inl q) := by
  let A := RatFuncFiniteIntegralClosure K L
  let R := FiniteExtensionFinitePlaceLocalRing K L q
  letI : Algebra A A := Algebra.id A
  let localA : Algebra A R := OreLocalization.instAlgebra
  letI := localA
  letI : SMul A R := localA.toSMul
  letI : Algebra K R := OreLocalization.instAlgebra
  letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  letI := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  letI : IsScalarTower K R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    symm
    change finiteExtensionFinitePlaceLocalizationToField
      (K := K) (L := L) q (algebraMap K R c) = algebraMap K L c
    rw [show algebraMap K R c = algebraMap A R (algebraMap K A c) by rfl]
    rw [show finiteExtensionFinitePlaceLocalizationToField
        (K := K) (L := L) q (algebraMap A R (algebraMap K A c)) =
      algebraMap A L (algebraMap K A c) by
        exact DFunLike.congr_fun
          (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
            (K := K) (L := L) q) (algebraMap K A c)]
    rfl
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A q.ne_bot R
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal :
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hspace (m : ℕ) :
      finiteExtensionLocalPoleSpace K L (.inl q) m =
        localPoleSpace (K := K) (L := L) π m := by
    ext x
    rw [mem_finiteExtensionLocalPoleSpace_iff,
      mem_localPoleSpace_iff_finitePlaceOrder π hπ hπIdeal]
    change (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionPrincipalDivisor K L x (.inl q))) ↔
      (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionFinitePlaceLocalOrder
          (K := K) (L := L) q x))
    rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder,
      ← finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
  letI : Finite (IsLocalRing.ResidueField R) := by
    simpa [R] using
      finiteExtensionFinitePlace_residueField_finite (K := K) (L := L) q
  letI : Module.Finite K (IsLocalRing.ResidueField R) := Module.Finite.of_finite
  rw [hspace (n + 1), hspace n]
  calc
    Module.finrank K
        (localPoleSpace (K := K) (L := L) π (n + 1) ⧸
          Submodule.comap
            (localPoleSpace (K := K) (L := L) π (n + 1)).subtype
            (localPoleSpace (K := K) (L := L) π n)) =
        Module.finrank K (IsLocalRing.ResidueField R) :=
      localPoleQuotient_finrank π hπ.ne_zero hπIdeal n
    _ = finiteExtensionPlaceDegree K L (.inl q) := by
      simpa [R] using
        (finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q).symm

/-- The finite-place principal parts through order `n` have dimension
`n` times the degree of the place. -/
theorem finiteExtensionLocalPoleSpace_inl_cumulative_finrank
    (q : FiniteExtensionFinitePlace K L) (n : ℕ) :
    Module.finrank K
        (finiteExtensionLocalPoleSpace K L (.inl q) n ⧸
          Submodule.comap
            (finiteExtensionLocalPoleSpace K L (.inl q) n).subtype
            (finiteExtensionLocalPoleSpace K L (.inl q) 0)) =
      n * finiteExtensionPlaceDegree K L (.inl q) := by
  let A := RatFuncFiniteIntegralClosure K L
  let R := FiniteExtensionFinitePlaceLocalRing K L q
  letI : Algebra A A := Algebra.id A
  let localA : Algebra A R := OreLocalization.instAlgebra
  letI := localA
  letI : SMul A R := localA.toSMul
  letI : Algebra K R := OreLocalization.instAlgebra
  letI := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  letI := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  letI : IsScalarTower K R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    symm
    change finiteExtensionFinitePlaceLocalizationToField
      (K := K) (L := L) q (algebraMap K R c) = algebraMap K L c
    rw [show algebraMap K R c = algebraMap A R (algebraMap K A c) by rfl]
    rw [show finiteExtensionFinitePlaceLocalizationToField
        (K := K) (L := L) q (algebraMap A R (algebraMap K A c)) =
      algebraMap A L (algebraMap K A c) by
        exact DFunLike.congr_fun
          (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
            (K := K) (L := L) q) (algebraMap K A c)]
    rfl
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A q.ne_bot R
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal :
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hspace (m : ℕ) :
      finiteExtensionLocalPoleSpace K L (.inl q) m =
        localPoleSpace (K := K) (L := L) π m := by
    ext x
    rw [mem_finiteExtensionLocalPoleSpace_iff,
      mem_localPoleSpace_iff_finitePlaceOrder π hπ hπIdeal]
    change (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionPrincipalDivisor K L x (.inl q))) ↔
      (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionFinitePlaceLocalOrder
          (K := K) (L := L) q x))
    rw [finiteExtensionFinitePlaceLocalOrder_eq_globalOrder,
      ← finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
  letI : Finite (IsLocalRing.ResidueField R) := by
    simpa [R] using
      finiteExtensionFinitePlace_residueField_finite (K := K) (L := L) q
  rw [hspace n, hspace 0]
  calc
    Module.finrank K
        (localPoleSpace (K := K) (L := L) π n ⧸
          Submodule.comap
            (localPoleSpace (K := K) (L := L) π n).subtype
            (localPoleSpace (K := K) (L := L) π 0)) =
        n * Module.finrank K (IsLocalRing.ResidueField R) :=
      localPoleCumulativeQuotient_finrank π hπ.ne_zero hπIdeal n
    _ = n * finiteExtensionPlaceDegree K L (.inl q) := by
      congr 1
      simpa [R] using
        (finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q).symm

end FinitePlace

section InfinityPlace

local instance localQuotientInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance localQuotientInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance localQuotientInfinityClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance localQuotientInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance localQuotientInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance localQuotientInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance localQuotientInfinityClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance localQuotientInfinityClosureDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance localQuotientInfinityClosureFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance localQuotientInfinityClosureConstantTowerToField :
    IsScalarTower K (RatFuncInfinityIntegralClosure K L) L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
  rfl

private noncomputable def localQuotientInfinityResidueFieldAlgEquivOfIdealEq
    {I J : Ideal (RatFuncInfinityIntegralClosure K L)}
    [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃ₐ[K] J.ResidueField := by
  subst J
  exact AlgEquiv.refl

private noncomputable def localQuotientInfinityResidueFieldAlgEquiv
    (P : FiniteExtensionInfinityPlace K L) :
    (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField
      ≃ₐ[K] P.1.ResidueField :=
  localQuotientInfinityResidueFieldAlgEquivOfIdealEq K L
    (primeOverHeightOne_asIdeal (ratFuncInfinityPlace K) P)

/-- Every infinity-place local principal-part layer has dimension exactly
the degree of that place. -/
theorem finiteExtensionLocalPoleSpace_inr_step_finrank
    (P : FiniteExtensionInfinityPlace K L) (n : ℕ) :
    Module.finrank K
        (finiteExtensionLocalPoleSpace K L (.inr P) (n + 1) ⧸
          Submodule.comap
            (finiteExtensionLocalPoleSpace K L (.inr P) (n + 1)).subtype
            (finiteExtensionLocalPoleSpace K L (.inr P) n)) =
      finiteExtensionPlaceDegree K L (.inr P) := by
  let A := RatFuncInfinityIntegralClosure K L
  let R := FiniteExtensionInfinityPlaceLocalRing K L P
  letI : Algebra A A := Algebra.id A
  let localA : Algebra A R := OreLocalization.instAlgebra
  letI := localA
  letI : SMul A R := localA.toSMul
  letI : Algebra K R := OreLocalization.instAlgebra
  letI := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing (K := K) (L := L) P
  letI : IsScalarTower K R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    symm
    change finiteExtensionInfinityPlaceLocalizationToField
      (K := K) (L := L) P (algebraMap K R c) = algebraMap K L c
    rw [show algebraMap K R c = algebraMap A R (algebraMap K A c) by rfl]
    rw [show finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) P (algebraMap A R (algebraMap K A c)) =
      algebraMap A L (algebraMap K A c) by
        exact DFunLike.congr_fun
          (finiteExtensionInfinityPlaceLocalizationToField_comp_algebraMap
            (K := K) (L := L) P) (algebraMap K A c)]
    exact (IsScalarTower.algebraMap_apply K A L c).symm
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot R
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal :
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hspace (m : ℕ) :
      finiteExtensionLocalPoleSpace K L (.inr P) m =
        localPoleSpace (K := K) (L := L) π m := by
    ext x
    rw [mem_finiteExtensionLocalPoleSpace_iff,
      mem_localPoleSpace_iff_finitePlaceOrder π hπ hπIdeal]
    change (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionPrincipalDivisor K L x (.inr P))) ↔
      (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionInfinityPlaceLocalOrder
          (K := K) (L := L) P x))
    rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder,
      ← finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder]
  letI : Finite (IsLocalRing.ResidueField R) := by
    letI : Finite P.1.ResidueField :=
      finiteExtensionInfinityPlace_residueField_finite (K := K) (L := L) P
    change Finite
      (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField
    exact Finite.of_injective
      (localQuotientInfinityResidueFieldAlgEquiv K L P)
      (localQuotientInfinityResidueFieldAlgEquiv K L P).injective
  letI : Module.Finite K (IsLocalRing.ResidueField R) := Module.Finite.of_finite
  rw [hspace (n + 1), hspace n]
  calc
    Module.finrank K
        (localPoleSpace (K := K) (L := L) π (n + 1) ⧸
          Submodule.comap
            (localPoleSpace (K := K) (L := L) π (n + 1)).subtype
            (localPoleSpace (K := K) (L := L) π n)) =
        Module.finrank K (IsLocalRing.ResidueField R) :=
      localPoleQuotient_finrank π hπ.ne_zero hπIdeal n
    _ = finiteExtensionPlaceDegree K L (.inr P) := by
      change Module.finrank K
          (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField = _
      calc
        Module.finrank K
            (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField =
            Module.finrank K P.1.ResidueField :=
          (localQuotientInfinityResidueFieldAlgEquiv K L P).toLinearEquiv.finrank_eq
        _ = finiteExtensionPlaceDegree K L (.inr P) :=
          (finiteExtensionInfinityPlace_degree_eq_finrank_residueField K L P).symm

/-- The infinity-place principal parts through order `n` have dimension
`n` times the degree of the place. -/
theorem finiteExtensionLocalPoleSpace_inr_cumulative_finrank
    (P : FiniteExtensionInfinityPlace K L) (n : ℕ) :
    Module.finrank K
        (finiteExtensionLocalPoleSpace K L (.inr P) n ⧸
          Submodule.comap
            (finiteExtensionLocalPoleSpace K L (.inr P) n).subtype
            (finiteExtensionLocalPoleSpace K L (.inr P) 0)) =
      n * finiteExtensionPlaceDegree K L (.inr P) := by
  let A := RatFuncInfinityIntegralClosure K L
  let R := FiniteExtensionInfinityPlaceLocalRing K L P
  letI : Algebra A A := Algebra.id A
  let localA : Algebra A R := OreLocalization.instAlgebra
  letI := localA
  letI : SMul A R := localA.toSMul
  letI : Algebra K R := OreLocalization.instAlgebra
  letI := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing (K := K) (L := L) P
  letI : IsScalarTower K R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    symm
    change finiteExtensionInfinityPlaceLocalizationToField
      (K := K) (L := L) P (algebraMap K R c) = algebraMap K L c
    rw [show algebraMap K R c = algebraMap A R (algebraMap K A c) by rfl]
    rw [show finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) P (algebraMap A R (algebraMap K A c)) =
      algebraMap A L (algebraMap K A c) by
        exact DFunLike.congr_fun
          (finiteExtensionInfinityPlaceLocalizationToField_comp_algebraMap
            (K := K) (L := L) P) (algebraMap K A c)]
    exact (IsScalarTower.algebraMap_apply K A L c).symm
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot R
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal :
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hspace (m : ℕ) :
      finiteExtensionLocalPoleSpace K L (.inr P) m =
        localPoleSpace (K := K) (L := L) π m := by
    ext x
    rw [mem_finiteExtensionLocalPoleSpace_iff,
      mem_localPoleSpace_iff_finitePlaceOrder π hπ hπIdeal]
    change (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionPrincipalDivisor K L x (.inr P))) ↔
      (x = 0 ∨ (x ≠ 0 ∧
        -(m : ℤ) ≤ finiteExtensionInfinityPlaceLocalOrder
          (K := K) (L := L) P x))
    rw [finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder,
      ← finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder]
  letI : Finite (IsLocalRing.ResidueField R) := by
    letI : Finite P.1.ResidueField :=
      finiteExtensionInfinityPlace_residueField_finite (K := K) (L := L) P
    change Finite
      (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField
    exact Finite.of_injective
      (localQuotientInfinityResidueFieldAlgEquiv K L P)
      (localQuotientInfinityResidueFieldAlgEquiv K L P).injective
  rw [hspace n, hspace 0]
  calc
    Module.finrank K
        (localPoleSpace (K := K) (L := L) π n ⧸
          Submodule.comap
            (localPoleSpace (K := K) (L := L) π n).subtype
            (localPoleSpace (K := K) (L := L) π 0)) =
        n * Module.finrank K (IsLocalRing.ResidueField R) :=
      localPoleCumulativeQuotient_finrank π hπ.ne_zero hπIdeal n
    _ = n * finiteExtensionPlaceDegree K L (.inr P) := by
      congr 1
      change Module.finrank K
          (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField = _
      calc
        Module.finrank K
            (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField =
            Module.finrank K P.1.ResidueField :=
          (localQuotientInfinityResidueFieldAlgEquiv K L P).toLinearEquiv.finrank_eq
        _ = finiteExtensionPlaceDegree K L (.inr P) :=
          (finiteExtensionInfinityPlace_degree_eq_finrank_residueField K L P).symm

end InfinityPlace

/-- At every exhaustive place, each successive local pole layer has exact
dimension equal to the place degree. -/
theorem finiteExtensionLocalPoleSpace_step_finrank
    (P : FiniteExtensionPlace K L) (n : ℕ) :
    Module.finrank K
        (finiteExtensionLocalPoleSpace K L P (n + 1) ⧸
          Submodule.comap
            (finiteExtensionLocalPoleSpace K L P (n + 1)).subtype
            (finiteExtensionLocalPoleSpace K L P n)) =
      finiteExtensionPlaceDegree K L P := by
  cases P with
  | inl q => exact finiteExtensionLocalPoleSpace_inl_step_finrank K L q n
  | inr P => exact finiteExtensionLocalPoleSpace_inr_step_finrank K L P n

/-- At every exhaustive place, the principal parts through order `n` have
dimension `n` times the place degree. -/
theorem finiteExtensionLocalPoleSpace_cumulative_finrank
    (P : FiniteExtensionPlace K L) (n : ℕ) :
    Module.finrank K
        (finiteExtensionLocalPoleSpace K L P n ⧸
          Submodule.comap
            (finiteExtensionLocalPoleSpace K L P n).subtype
            (finiteExtensionLocalPoleSpace K L P 0)) =
      n * finiteExtensionPlaceDegree K L P := by
  cases P with
  | inl q =>
      exact finiteExtensionLocalPoleSpace_inl_cumulative_finrank K L q n
  | inr P =>
      exact finiteExtensionLocalPoleSpace_inr_cumulative_finrank K L P n

end

end BGS.HasseWeil
