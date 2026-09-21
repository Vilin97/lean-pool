/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceFinitePlaceIncrement

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

local instance infinityIncrementConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance infinityIncrementConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance upperInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

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
  let S := finiteExtensionRiemannSpace K L D
  let T := finiteExtensionRiemannSpace K L (D + Finsupp.single Q 1)
  letI : Algebra (RatFuncInfinityIntegralClosure K L)
      (RatFuncInfinityIntegralClosure K L) :=
    Algebra.id (RatFuncInfinityIntegralClosure K L)
  let upperInfinityClosureLocalAlgebra :
      Algebra (RatFuncInfinityIntegralClosure K L)
        (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    OreLocalization.instAlgebra
  letI := upperInfinityClosureLocalAlgebra
  letI : SMul (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    upperInfinityClosureLocalAlgebra.toSMul
  letI : Algebra K (FiniteExtensionInfinityPlaceLocalRing K L P) :=
    OreLocalization.instAlgebra
  letI := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) P
  letI := finiteExtensionInfinityPlaceLocalIsFractionRing (K := K) (L := L) P
  letI : IsScalarTower K R L := by
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
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A (primeOverHeightOne (ratFuncInfinityPlace K) P).ne_bot R
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal :
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  let πL : L := algebraMap R L π
  have hπLNe : πL ≠ 0 := by
    dsimp [πL]
    simpa using (IsFractionRing.injective R L).ne hπ.ne_zero
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
  have hregular : ∀ x : T, ∃ r : R,
      a * x.1 = algebraMap R L r := by
    intro x
    apply finiteExtensionInfinityPlace_exists_local_lift_of_orderTop_nonnegative
      (K := K) (L := L) P (a * x.1)
    by_cases hx0 : x.1 = 0
    · simp [a, hx0, finiteExtensionInfinityPlaceLocalOrderTop]
    · have hxmem := (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp x.2
      rcases hxmem with hxmem | ⟨_, hxorders⟩
      · exact (hx0 hxmem).elim
      · have hxQ := hxorders Q
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hxQ
        rw [finiteExtensionInfinityPlaceLocalOrderTop_mul,
          show a = πL ^ (m + 1) by rfl,
          finiteExtensionInfinityPlaceLocalOrderTop_pow,
          hπOrder,
          finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P x.1 hx0,
          ← finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder
            (K := K) (L := L) x.1 P]
        rw [show (m + 1) • (1 : WithTop ℤ) =
          ((m + 1 : ℕ) : WithTop ℤ) by simp]
        exact_mod_cast (show 0 ≤ (m : ℤ) + 1 +
          finiteExtensionPrincipalDivisor K L x.1 Q by
            rw [hm]
            omega)
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
  let f := localLeadingResidueLinearMap (K := K) (R := R) (L := L)
    T a hregular
  have hST : S ≤ T := by
    apply finiteExtensionRiemannSpace_mono
    intro v
    classical
    by_cases hv : v = Q <;> simp [hv]
  have hkerPoint (x : T) : f x = 0 ↔ x.1 ∈ S := by
    rw [localLeadingResidueLinearMap_eq_zero_iff
      (K := K) (R := R) (L := L) T a hregular]
    constructor
    · intro hrMem
      by_cases hx0 : x.1 = 0
      · simpa [hx0] using S.zero_mem
      · have hrNe : localNormalizedLift (R := R) T a hregular x ≠ 0 := by
          intro hr0
          have hax0 : a * x.1 = 0 := by
            rw [localNormalizedLift_spec (R := R) T a hregular x,
              hr0, map_zero]
          exact hx0 ((mul_eq_zero.mp hax0).resolve_left (pow_ne_zero _ hπLNe))
        have hrOrder :
            (1 : ℤ) ≤ finitePlaceOrder
              (IsDiscreteValuationRing.maximalIdeal R)
              (algebraMap R L (localNormalizedLift (R := R) T a hregular x)) :=
          one_le_finitePlaceOrder_algebraMap_of_mem
            (R := R) (L := L)
            (IsDiscreteValuationRing.maximalIdeal R)
            (localNormalizedLift (R := R) T a hregular x) hrMem hrNe
        have hrMapNe :
            algebraMap R L (localNormalizedLift (R := R) T a hregular x) ≠ 0 :=
          by simpa using (IsFractionRing.injective R L).ne hrNe
        have haxOrder :
            (1 : WithTop ℤ) ≤
              finiteExtensionInfinityPlaceLocalOrderTop
                (K := K) (L := L) P (a * x.1) := by
          rw [localNormalizedLift_spec (R := R) T a hregular x]
          change (1 : WithTop ℤ) ≤ finitePlaceOrderTop
            (IsDiscreteValuationRing.maximalIdeal R)
            (algebraMap R L (localNormalizedLift (R := R) T a hregular x))
          rw [finitePlaceOrderTop_eq_coe _ _ hrMapNe]
          exact_mod_cast hrOrder
        have hxQ :
            0 ≤ finiteExtensionPrincipalDivisor K L x.1 Q + D Q := by
          rw [finiteExtensionInfinityPlaceLocalOrderTop_mul,
            show a = πL ^ (m + 1) by rfl,
            finiteExtensionInfinityPlaceLocalOrderTop_pow,
            hπOrder,
            finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P x.1 hx0,
            ← finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder
              (K := K) (L := L) x.1 P] at haxOrder
          rw [show (m + 1) • (1 : WithTop ℤ) =
            ((m + 1 : ℕ) : WithTop ℤ) by simp] at haxOrder
          have haxOrderInt : 1 ≤ (m : ℤ) + 1 +
              finiteExtensionPrincipalDivisor K L x.1 Q := by
            exact_mod_cast haxOrder
          rw [← hm]
          omega
        rw [mem_finiteExtensionRiemannSpace]
        refine Or.inr ⟨hx0, ?_⟩
        intro v
        by_cases hv : v = Q
        · simpa [hv] using hxQ
        · have hxmem :=
            (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp x.2
          rcases hxmem with hxmem | ⟨_, hxorders⟩
          · exact (hx0 hxmem).elim
          · have hxv := hxorders v
            simp only [Finsupp.add_apply,
              Finsupp.single_eq_of_ne hv] at hxv
            simpa using hxv
    · intro hxS
      by_cases hx0 : x.1 = 0
      · have hlift0 : localNormalizedLift (R := R) T a hregular x = 0 := by
          apply IsFractionRing.injective R L
          rw [map_zero,
            ← localNormalizedLift_spec (R := R) T a hregular x]
          simp [hx0]
        rw [hlift0]
        exact (IsLocalRing.maximalIdeal R).zero_mem
      · have hxmem :=
          (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp hxS
        rcases hxmem with hxmem | ⟨_, hxorders⟩
        · exact (hx0 hxmem).elim
        · have hxQ := hxorders Q
          have haxOrder :
              (1 : WithTop ℤ) ≤
                finiteExtensionInfinityPlaceLocalOrderTop
                  (K := K) (L := L) P (a * x.1) := by
            rw [finiteExtensionInfinityPlaceLocalOrderTop_mul,
              show a = πL ^ (m + 1) by rfl,
              finiteExtensionInfinityPlaceLocalOrderTop_pow,
              hπOrder,
              finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder P x.1 hx0,
              ← finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder
                (K := K) (L := L) x.1 P]
            rw [show (m + 1) • (1 : WithTop ℤ) =
              ((m + 1 : ℕ) : WithTop ℤ) by simp]
            exact_mod_cast (show 1 ≤ (m : ℤ) + 1 +
              finiteExtensionPrincipalDivisor K L x.1 Q by
                rw [hm]
                omega)
          rw [localNormalizedLift_spec (R := R) T a hregular x] at haxOrder
          by_cases hr0 : localNormalizedLift (R := R) T a hregular x = 0
          · rw [hr0]
            exact (IsLocalRing.maximalIdeal R).zero_mem
          · apply mem_heightOneSpectrum_of_one_le_finitePlaceOrder_algebraMap
              (R := R) (L := L)
              (IsDiscreteValuationRing.maximalIdeal R)
              (localNormalizedLift (R := R) T a hregular x)
            have hrMapNe :
                algebraMap R L (localNormalizedLift (R := R) T a hregular x) ≠ 0 :=
              by simpa using (IsFractionRing.injective R L).ne hr0
            change (1 : WithTop ℤ) ≤ finitePlaceOrderTop
              (IsDiscreteValuationRing.maximalIdeal R)
              (algebraMap R L (localNormalizedLift (R := R) T a hregular x)) at haxOrder
            rw [finitePlaceOrderTop_eq_coe _ _ hrMapNe] at haxOrder
            exact_mod_cast haxOrder
  have hker : f.ker = Submodule.comap T.subtype S := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    exact hkerPoint x
  letI : Finite (IsLocalRing.ResidueField R) := by
    letI : Finite P.1.ResidueField :=
      finiteExtensionInfinityPlace_residueField_finite (K := K) (L := L) P
    change Finite
      (primeOverHeightOne (ratFuncInfinityPlace K) P).asIdeal.ResidueField
    exact Finite.of_injective
      (infinityIncrementResidueFieldAlgEquiv K L P)
      (infinityIncrementResidueFieldAlgEquiv K L P).injective
  letI : Module.Finite K (IsLocalRing.ResidueField R) :=
    Module.Finite.of_finite
  letI : Module.Finite K f.range := inferInstance
  letI : Module.Finite K f.ker := by
    rw [hker]
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hST).symm
  letI : Module.Finite K (T ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  letI hTFinite : Module.Finite K T :=
    Module.Finite.of_submodule_quotient f.ker
  have hkerRank : Module.finrank K f.ker = Module.finrank K S := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hST).finrank_eq
  constructor
  · exact hTFinite
  · calc
      Module.finrank K T =
          Module.finrank K f.range + Module.finrank K f.ker :=
        f.finrank_range_add_finrank_ker.symm
      _ ≤ Module.finrank K (IsLocalRing.ResidueField R) +
          Module.finrank K S :=
        Nat.add_le_add f.range.finrank_le (le_of_eq hkerRank)
      _ = Module.finrank K S +
          finiteExtensionPlaceDegree K L (.inr P) := by
        rw [hResidueRank, Nat.add_comm]

end InfinityPlace

end
end BGS.HasseWeil
