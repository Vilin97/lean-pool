/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceFinitePlaceIncrement

/-!
# Riemann-space increments at infinity

Identify the kernel of the leading-residue map and bound the dimension increase by the degree of
an infinite place.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

noncomputable section



section InfinityPlace

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The algebra structure from `K` to `L` used in the riemann space infinity place increment
    construction. -/
local instance infinityIncrementConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance infinityIncrementConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The algebra structure from `K` to `(RatFuncInfinityIntegers K)` used in the riemann
    space infinity place increment construction. -/
local instance upperInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

/-- The algebra structure from `K` to `(RatFuncInfinityIntegralClosure K L)` used in the
    riemann space infinity place increment construction. -/
local instance upperInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance upperInfinityClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance upperInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance upperInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance upperInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance upperInfinityClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance upperInfinityClosureDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance upperInfinityClosureFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance upperInfinityClosureConstantTowerToField :
    IsScalarTower K (RatFuncInfinityIntegralClosure K L) L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
  rfl

private noncomputable def infinityIncrementResidueFieldAlgEquivOfIdealEq
    {I J : Ideal (RatFuncInfinityIntegralClosure K L)}
    [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃ₐ[K] J.ResidueField := by
  subst J
  exact AlgEquiv.refl

private noncomputable def infinityIncrementResidueFieldAlgEquiv
    (P : FiniteExtensionInfinityPlace K L) :
    (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField
      ≃ₐ[K] P.1.ResidueField :=
  infinityIncrementResidueFieldAlgEquivOfIdealEq K L
    (primeOverHeightOne_asIdeal (ratFuncInfinityPlace K) P)

/-- Adding one infinity place to an effective divisor preserves finite
dimensionality.  The dimension jump is at most the degree of that place. -/
theorem finiteExtensionRiemannSpace_infinityPlace_increment
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v)
    (P : FiniteExtensionInfinityPlace K L)
    [Module.Finite K (finiteExtensionRiemannSpace K L D)] :
    Module.Finite K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single (.inr P) 1)) ∧
    Module.finrank K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single (.inr P) 1)) ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) +
        finiteExtensionPlaceDegree K L (.inr P) := by
  let A := RatFuncInfinityIntegralClosure K L
  let R := FiniteExtensionInfinityPlaceLocalRing K L P
  let Q : FiniteExtensionPlace K L := .inr P
  let : Algebra (RatFuncInfinityIntegralClosure K L)
      (RatFuncInfinityIntegralClosure K L) :=
    Algebra.id (RatFuncInfinityIntegralClosure K L)
  let upperInfinityClosureLocalAlgebra :
      Algebra (RatFuncInfinityIntegralClosure K L)
        (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    OreLocalization.instAlgebra
  let := upperInfinityClosureLocalAlgebra
  let : SMul (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    upperInfinityClosureLocalAlgebra.toSMul
  let : Algebra K (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    OreLocalization.instAlgebra
  let := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) P
  let := finiteExtensionInfinityPlaceLocalIsFractionRing (K := K) (L := L) P
  let : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).mpr (IsFractionRing.injective R L)
  let : IsScalarTower K R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    symm
    change finiteExtensionInfinityPlaceLocalizationToField
      (K := K) (L := L) P (algebraMap K R c) = algebraMap K L c
    rw [show algebraMap K R c =
      algebraMap A R (algebraMap K A c) by rfl]
    rw [show finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) P (algebraMap A R (algebraMap K A c)) =
      algebraMap A L (algebraMap K A c) by
        exact DFunLike.congr_fun
          (finiteExtensionInfinityPlaceLocalizationToField_comp_algebraMap
            (K := K) (L := L) P) (algebraMap K A c)]
    exact (IsScalarTower.algebraMap_apply K A L c).symm
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot R
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal :
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  let πL : L := algebraMap R L π
  have hπOrder :
      finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P πL =
        (1 : WithTop ℤ) := by
    change finitePlaceOrderTop
      (IsDiscreteValuationRing.maximalIdeal R) πL = (1 : WithTop ℤ)
    simpa [πL] using finitePlaceOrderTop_uniformizer_zpow
      (L := L) (IsDiscreteValuationRing.maximalIdeal R)
        π hπ hπIdeal (1 : ℤ)
  let m : ℕ := (D Q).toNat
  have hm : (m : ℤ) = D Q := by
    exact Int.toNat_of_nonneg (hD Q)
  let a : L := πL ^ (m + 1)
  have hscaleOrder (x : L) (hx0 : x ≠ 0) :
      finitePlaceOrderTop (IsDiscreteValuationRing.maximalIdeal R) (a * x) =
        ((D Q + 1 + finiteExtensionPrincipalDivisor K L x Q : ℤ) : WithTop ℤ) := by
    change finiteExtensionInfinityPlaceLocalOrderTop (K := K) (L := L) P (a * x) = _
    rw [finiteExtensionInfinityPlaceLocalOrderTop_mul,
      show a = πL ^ (m + 1) by rfl,
      finiteExtensionInfinityPlaceLocalOrderTop_pow, hπOrder,
          finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P x hx0,
          ← finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder
            (K := K) (L := L) x P]
    rw [show (m + 1) • (1 : WithTop ℤ) = ((m + 1 : ℕ) : WithTop ℤ) by simp]
    exact_mod_cast (show (m : ℤ) + 1 + finiteExtensionPrincipalDivisor K L x Q =
        D Q + 1 + finiteExtensionPrincipalDivisor K L x Q by rw [hm])
  have hResidueRank : Module.finrank K (IsLocalRing.ResidueField R) =
      finiteExtensionPlaceDegree K L (.inr P) := by
    change Module.finrank K
        (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField = _
    calc
      Module.finrank K
          (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField =
          Module.finrank K P.1.ResidueField :=
        (infinityIncrementResidueFieldAlgEquiv K L P).toLinearEquiv.finrank_eq
      _ = finiteExtensionPlaceDegree K L (.inr P) :=
        (finiteExtensionInfinityPlace_degree_eq_finrank_residueField K L P).symm
  let : Finite (IsLocalRing.ResidueField R) := by
    let : Finite P.1.ResidueField :=
      finiteExtensionInfinityPlace_residueField_finite (K := K) (L := L) P
    change Finite
      (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField
    exact Finite.of_injective
      (infinityIncrementResidueFieldAlgEquiv K L P)
      (infinityIncrementResidueFieldAlgEquiv K L P).injective
  let : Module.Finite K (IsLocalRing.ResidueField R) :=
    Module.Finite.of_finite
  have hbound := finiteExtensionRiemannSpace_increment_of_local_order
    K L (R := R) D Q a hscaleOrder
  refine ⟨hbound.1, ?_⟩
  rw [← hResidueRank]
  exact hbound.2

end InfinityPlace

end
end BGS.HasseWeil
