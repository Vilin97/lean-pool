/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceResidueIncrement


public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointBase
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlaceCases
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlacePrincipalDivisor
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.Tactic

/-!
# Riemann-space increments at finite places

Use a normalized local lift and its leading residue to bound the dimension increase when one
finite place is added to a divisor.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

noncomputable section


section PlaceDegree

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The algebra structure from `K` to `L` used in the riemann space finite place increment
    construction. -/
local instance upperConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance upperConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The algebra structure from `K[X]` to `L` used in the riemann space finite place
    increment construction. -/
local instance (priority := 10) upperPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance upperPolynomialTower : IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The algebra structure from `K` to `(RatFuncFiniteIntegralClosure K L)` used in the
    riemann space finite place increment construction. -/
local instance upperFiniteClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap K[X] (RatFuncFiniteIntegralClosure K L)).comp
      (algebraMap K K[X]))

local instance upperFiniteClosureConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance upperFiniteClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance upperFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance upperPolynomialTorsionFreeTop : Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance upperFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance upperFiniteClosureDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance upperFiniteClosureFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) L (RatFuncFiniteIntegralClosure K L)

/-- Adding one finite place to an effective divisor preserves finite
dimensionality.  The dimension jump is at most the degree of that place. -/
theorem finiteExtensionRiemannSpace_finitePlace_increment
    (D : FiniteExtensionDivisor K L)
    (hD : ∀ v, 0 ≤ D v)
    (q : FiniteExtensionFinitePlace K L)
    [Module.Finite K (finiteExtensionRiemannSpace K L D)] :
    Module.Finite K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single (.inl q) 1)) ∧
    Module.finrank K (finiteExtensionRiemannSpace K L
      (D + Finsupp.single (.inl q) 1)) ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) +
        finiteExtensionPlaceDegree K L (.inl q) := by
  let A := RatFuncFiniteIntegralClosure K L
  let R := FiniteExtensionFinitePlaceLocalRing K L q
  let Q : FiniteExtensionPlace K L := .inl q
  let : Algebra (RatFuncFiniteIntegralClosure K L)
      (RatFuncFiniteIntegralClosure K L) :=
    Algebra.id (RatFuncFiniteIntegralClosure K L)
  let upperFiniteClosureLocalAlgebra :
      Algebra (RatFuncFiniteIntegralClosure K L)
        (FiniteExtensionFinitePlaceLocalRing K L q) :=
    OreLocalization.instAlgebra
  let := upperFiniteClosureLocalAlgebra
  let : SMul (RatFuncFiniteIntegralClosure K L)
      (FiniteExtensionFinitePlaceLocalRing K L q) :=
    upperFiniteClosureLocalAlgebra.toSMul
  let : Algebra K (FiniteExtensionFinitePlaceLocalRing K L q) :=
    OreLocalization.instAlgebra
  let := finiteExtensionFinitePlaceLocalAlgebra (K := K) (L := L) q
  let := finiteExtensionFinitePlaceLocalIsFractionRing (K := K) (L := L) q
  let _ : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).mpr (IsFractionRing.injective R L)
  let : IsScalarTower K R L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    symm
    change finiteExtensionFinitePlaceLocalizationToField
      (K := K) (L := L) q (algebraMap K R c) = algebraMap K L c
    rw [show algebraMap K R c =
      algebraMap A R (algebraMap K A c) by rfl]
    rw [show finiteExtensionFinitePlaceLocalizationToField
        (K := K) (L := L) q (algebraMap A R (algebraMap K A c)) =
      algebraMap A L (algebraMap K A c) by
        exact DFunLike.congr_fun
          (finiteExtensionFinitePlaceLocalizationToField_comp_algebraMap
            (K := K) (L := L) q) (algebraMap K A c)]
    rfl
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A q.ne_bot R
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal :
      (IsDiscreteValuationRing.maximalIdeal R).asIdeal = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  let πL : L := algebraMap R L π
  have hπOrder :
      finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q πL =
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
    change finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q (a * x) = _
    rw [finiteExtensionFinitePlaceLocalOrderTop_mul,
      show a = πL ^ (m + 1) by rfl,
      finiteExtensionFinitePlaceLocalOrderTop_pow, hπOrder,
          finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
            K L q x hx0]
    rw [show (m + 1) • (1 : WithTop ℤ) = ((m + 1 : ℕ) : WithTop ℤ) by simp]
    exact_mod_cast (show (m : ℤ) + 1 + finiteExtensionPrincipalDivisor K L x Q =
        D Q + 1 + finiteExtensionPrincipalDivisor K L x Q by rw [hm])
  have hResidueRank : Module.finrank K (IsLocalRing.ResidueField R) =
      finiteExtensionPlaceDegree K L (.inl q) := by
    simpa [R] using
      (finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q).symm
  let : Finite (IsLocalRing.ResidueField R) := by
    simpa [R] using
      finiteExtensionFinitePlace_residueField_finite (K := K) (L := L) q
  let : Module.Finite K (IsLocalRing.ResidueField R) :=
    Module.Finite.of_finite
  have hbound := finiteExtensionRiemannSpace_increment_of_local_order
    K L (R := R) D Q a hscaleOrder
  refine ⟨hbound.1, ?_⟩
  rw [← hResidueRank]
  exact hbound.2

end PlaceDegree

end
end BGS.HasseWeil
