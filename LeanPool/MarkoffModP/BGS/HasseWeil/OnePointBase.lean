/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalAuxiliaryInfinityPlace
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZeroCounting

/-!
# Finiteness of the height-zero one-point Riemann space

For a finite separable extension `L / K(X)` over a finite field, the functions
regular at every exhaustive place form a finite-dimensional `K`-vector space.

The proof chooses a branch above infinity and reduces a function modulo that
branch.  Every height-zero function has a lift to the corresponding local
ring.  If two such functions have the same residue, their difference has
positive order at the chosen branch and nonnegative order everywhere else.
The degree-weighted product formula rules this out unless the difference is
zero.  Thus the height-zero space injects into a finite residue field.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance onePointBaseConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance onePointBaseConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance onePointBaseInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance onePointBaseInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance onePointBaseInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance onePointBaseInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance onePointBaseInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance onePointBaseInfinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

/-- The height-zero member of the one-point filtration is finite-dimensional
over the finite constant field. -/
theorem finiteExtensionOnePointRiemannSpace_zero_moduleFinite
    (P : FiniteExtensionPlace K L) :
    Module.Finite K (finiteExtensionOnePointRiemannSpace K L P 0) := by
  let Q : FiniteExtensionInfinityPlace K L := Classical.choice
    (inferInstance : Nonempty (FiniteExtensionInfinityPlace K L))
  let : Algebra (RatFuncInfinityIntegralClosure K L)
      (RatFuncInfinityIntegralClosure K L) :=
    Algebra.id (RatFuncInfinityIntegralClosure K L)
  let _ : DistribMulAction (RatFuncInfinityIntegralClosure K L)
      (RatFuncInfinityIntegralClosure K L) :=
    (Algebra.toModule : Module (RatFuncInfinityIntegralClosure K L)
      (RatFuncInfinityIntegralClosure K L)).toDistribMulAction
  let : Algebra (RatFuncInfinityIntegralClosure K L)
      (FiniteExtensionInfinityPlaceLocalRing K L Q) :=
    OreLocalization.instAlgebra
  let R := FiniteExtensionInfinityPlaceLocalRing K L Q
  let := finiteExtensionInfinityPlaceLocalAlgebra (K := K) (L := L) Q
  let := finiteExtensionInfinityPlaceLocalIsFractionRing (K := K) (L := L) Q
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (RatFuncInfinityIntegralClosure K L)
      (primeOverHeightOne (ratFuncInfinityPlace K) Q).ne_bot R
  let : Finite Q.1.ResidueField :=
    finiteExtensionInfinityPlace_residueField_finite (K := K) (L := L) Q
  let V := finiteExtensionOnePointRiemannSpace K L P 0
  have hliftExists : ∀ x : V, ∃ r : R,
      (x.1 : L) = finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) Q r := by
    intro x
    apply finiteExtensionInfinityPlace_exists_local_lift_of_orderTop_nonnegative
      (K := K) (L := L) Q x.1
    by_cases hx0 : x.1 = 0
    · simp only [finiteExtensionInfinityPlaceLocalOrderTop, hx0]
      erw [finitePlaceOrderTop_zero]
      exact le_top
    · rw [finiteExtensionInfinityPlaceLocalOrderTop_eq_globalOrder Q x.1 hx0]
      have hxmem :=
        (mem_finiteExtensionOnePointRiemannSpace_iff K L P 0 x.1).mp x.2
      rcases hxmem with hxmem | ⟨_, hP, hAway⟩
      · exact (hx0 hxmem).elim
      · have hnonneg :
            0 ≤ finiteExtensionPrincipalDivisor K L x.1 (.inr Q) := by
          by_cases hQP : (Sum.inr Q : FiniteExtensionPlace K L) = P
          · rw [hQP]
            simpa using hP
          · exact hAway (.inr Q) hQP
        exact_mod_cast (by
          simpa only [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder]
            using hnonneg)
  let lift : V → R := fun x => Classical.choose (hliftExists x)
  have lift_spec (x : V) :
      (x.1 : L) = finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) Q (lift x) :=
    Classical.choose_spec (hliftExists x)
  let residue : V → Q.1.ResidueField := fun x =>
    IsLocalRing.residue R (lift x)
  have hresidueInjective : Function.Injective residue := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    let r : R := lift x - lift y
    have hrResidue : IsLocalRing.residue R r = 0 := by
      dsimp only [r]
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have hrMem : r ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.residue_eq_zero_iff r).mp hrResidue
    have hrMap : finiteExtensionInfinityPlaceLocalizationToField
        (K := K) (L := L) Q r = x.1 - y.1 := by
      dsimp [r]
      calc
        finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) Q (lift x - lift y) =
            finiteExtensionInfinityPlaceLocalizationToField
                (K := K) (L := L) Q (lift x) -
              finiteExtensionInfinityPlaceLocalizationToField
                (K := K) (L := L) Q (lift y) :=
          (finiteExtensionInfinityPlaceLocalizationToField
            (K := K) (L := L) Q).map_sub (lift x) (lift y)
        _ = x.1 - y.1 := by rw [← lift_spec x, ← lift_spec y]
    have hrNe : r ≠ 0 := by
      intro hr0
      apply hne
      apply sub_eq_zero.mp
      rw [← hrMap, hr0, map_zero]
    have hrOrder :
        (1 : ℤ) ≤ finitePlaceOrder
          (IsDiscreteValuationRing.maximalIdeal R)
          (algebraMap R L r) :=
      one_le_finitePlaceOrder_algebraMap_of_mem
        (R := R) (L := L)
        (IsDiscreteValuationRing.maximalIdeal R) r hrMem hrNe
    have hQOrder :
        0 < finiteExtensionPrincipalDivisor K L (x.1 - y.1) (.inr Q) := by
      rw [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder,
        ← hrMap, ← finiteExtensionInfinityPlaceLocalOrder_eq_globalOrder Q]
      change 0 < finitePlaceOrder
        (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R L r)
      omega
    have hdNe : x.1 - y.1 ≠ 0 := sub_ne_zero.mpr hne
    have hdMem : x.1 - y.1 ∈ V := V.sub_mem x.2 y.2
    have hdOrders : ∀ v : FiniteExtensionPlace K L,
        0 ≤ finiteExtensionPrincipalDivisor K L (x.1 - y.1) v := by
      intro v
      rcases (mem_finiteExtensionOnePointRiemannSpace_iff
        K L P 0 (x.1 - y.1)).mp hdMem with hd0 | ⟨_, hP, hAway⟩
      · exact (hdNe hd0).elim
      · by_cases hv : v = P
        · rw [hv]
          simpa using hP
        · exact hAway v hv
    have hDegreePos :
        0 < finiteExtensionPrincipalDivisorDegreeSum K L (x.1 - y.1) := by
      rw [finiteExtensionPrincipalDivisorDegreeSum]
      apply Finsupp.sum_pos'
      · intro v _hv
        exact mul_nonneg (hdOrders v) (by positivity)
      · refine ⟨.inr Q, ?_, ?_⟩
        · exact Finsupp.mem_support_iff.mpr (ne_of_gt hQOrder)
        · exact mul_pos hQOrder (by
            exact_mod_cast finiteExtensionPlaceDegree_pos K L (.inr Q))
    have hDegreeZero :=
      finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L (x.1 - y.1) hdNe
    omega
  let : Finite V := Finite.of_injective residue hresidueInjective
  change Module.Finite K V
  infer_instance

end

end BGS.HasseWeil
