/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


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


section LocalLift

variable {K R L : Type*} [Field K] [CommRing R]
  [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra K R] [Algebra R L] [Algebra K L]
  [IsScalarTower K R L] [IsFractionRing R L]

variable (T : Submodule K L) (a : L)
variable (hregular : ∀ x : T, ∃ r : R, a * x.1 = algebraMap R L r)

noncomputable def localNormalizedLift (x : T) : R :=
  Classical.choose (hregular x)

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [Algebra K R] [IsScalarTower K R L]
  [IsFractionRing R L] in
theorem localNormalizedLift_spec (x : T) :
    a * x.1 = algebraMap R L (localNormalizedLift T a hregular x) :=
  Classical.choose_spec (hregular x)

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [Algebra K R] [IsScalarTower K R L] in
theorem localNormalizedLift_add (x y : T) :
    localNormalizedLift T a hregular (x + y) =
      localNormalizedLift T a hregular x + localNormalizedLift T a hregular y := by
  apply IsFractionRing.injective R L
  rw [map_add]
  rw [← localNormalizedLift_spec T a hregular]
  rw [← localNormalizedLift_spec T a hregular]
  rw [← localNormalizedLift_spec T a hregular]
  simp only [Submodule.coe_add]
  ring

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] in
theorem localNormalizedLift_smul (c : K) (x : T) :
    localNormalizedLift T a hregular (c • x) =
      c • localNormalizedLift T a hregular x := by
  apply IsFractionRing.injective R L
  rw [show algebraMap R L (c • localNormalizedLift T a hregular x) =
      c • algebraMap R L (localNormalizedLift T a hregular x) by
    exact map_smul (IsScalarTower.toAlgHom K R L) c _]
  rw [← localNormalizedLift_spec T a hregular]
  rw [← localNormalizedLift_spec T a hregular]
  simp only [Submodule.coe_smul]
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

noncomputable def localNormalizedLiftLinearMap : T →ₗ[K] R where
  toFun := localNormalizedLift T a hregular
  map_add' := localNormalizedLift_add T a hregular
  map_smul' := localNormalizedLift_smul T a hregular

noncomputable def localLeadingResidueLinearMap :
    T →ₗ[K] IsLocalRing.ResidueField R :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal R)).toLinearMap.comp
    (localNormalizedLiftLinearMap T a hregular)

theorem localLeadingResidueLinearMap_eq_zero_iff (x : T) :
    localLeadingResidueLinearMap T a hregular x = 0 ↔
      localNormalizedLift T a hregular x ∈ IsLocalRing.maximalIdeal R := by
  exact IsLocalRing.residue_eq_zero_iff _

theorem mem_heightOneSpectrum_of_one_le_finitePlaceOrder_algebraMap
    (v : HeightOneSpectrum R) (r : R)
    (horder : (1 : ℤ) ≤ finitePlaceOrder v (algebraMap R L r)) :
    r ∈ v.asIdeal := by
  by_cases hr : r = 0
  · simp [hr]
  · have hrMap : algebraMap R L r ≠ 0 :=
      by simpa using (IsFractionRing.injective R L).ne hr
    have hvaluation :=
      valuation_eq_exp_neg_finitePlaceOrder v (algebraMap R L r) hrMap
    rw [HeightOneSpectrum.valuation_of_algebraMap] at hvaluation
    rw [← v.intValuation_lt_one_iff_mem]
    rw [hvaluation, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

end LocalLift

/-- A normalized lift has zero residue exactly when its local order is positive. -/
theorem localNormalizedLift_mem_maximalIdeal_iff
    {K R L : Type*} [Field K] [CommRing R]
  [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra K R] [Algebra R L] [Algebra K L]
  [IsScalarTower K R L] [IsFractionRing R L]
    (T : Submodule K L) (a : L)
    (hregular : ∀ x : T, ∃ r : R, a * x.1 = algebraMap R L r) (x : T) :
    localNormalizedLift T a hregular x ∈ IsLocalRing.maximalIdeal R ↔
      (1 : WithTop ℤ) ≤ finitePlaceOrderTop
        (IsDiscreteValuationRing.maximalIdeal R) (a * x.1) := by
  rw [localNormalizedLift_spec (R := R) T a hregular x]
  let r := localNormalizedLift (R := R) T a hregular x
  by_cases hr : r = 0
  · simp only [show localNormalizedLift T a hregular x = 0 from hr,
      map_zero, Submodule.zero_mem, true_iff]
    simp [finitePlaceOrderTop]
  · have hrMap : algebraMap R L r ≠ 0 :=
      by simpa using (IsFractionRing.injective R L).ne hr
    rw [finitePlaceOrderTop_eq_coe _ _ hrMap]
    constructor
    · intro hmem
      exact_mod_cast one_le_finitePlaceOrder_algebraMap_of_mem (R := R) (L := L)
        (IsDiscreteValuationRing.maximalIdeal R) r hmem hr
    · intro horder
      exact mem_heightOneSpectrum_of_one_le_finitePlaceOrder_algebraMap (R := R) (L := L)
        (IsDiscreteValuationRing.maximalIdeal R) r (by exact_mod_cast horder)


section PlaceDegree

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance upperConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance upperConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) upperPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance upperPolynomialTower : IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

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
  let S := finiteExtensionRiemannSpace K L D
  let T := finiteExtensionRiemannSpace K L (D + Finsupp.single Q 1)
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
  have hregular : ∀ x : T, ∃ r : R,
      a * x.1 = algebraMap R L r := by
    intro x
    apply finiteExtensionFinitePlace_exists_local_lift_of_orderTop_nonnegative
      (K := K) (L := L) q (a * x.1)
    by_cases hx0 : x.1 = 0
    · simp [a, hx0, finiteExtensionFinitePlaceLocalOrderTop]
    · have hxmem := (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp x.2
      rcases hxmem with hxmem | ⟨_, hxorders⟩
      · exact (hx0 hxmem).elim
      · have hxQ := hxorders Q
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hxQ
        rw [finiteExtensionFinitePlaceLocalOrderTop_mul,
          show a = πL ^ (m + 1) by rfl,
          finiteExtensionFinitePlaceLocalOrderTop_pow,
          hπOrder,
          finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
            K L q x.1 hx0]
        change (0 : WithTop ℤ) ≤
          (m + 1) • (1 : WithTop ℤ) +
            (finiteExtensionFinitePrincipalDivisor K L x.1 q : WithTop ℤ)
        rw [show (m + 1) • (1 : WithTop ℤ) =
          ((m + 1 : ℕ) : WithTop ℤ) by simp]
        exact_mod_cast (show 0 ≤ (m : ℤ) + 1 +
          finiteExtensionFinitePrincipalDivisor K L x.1 q by
            change 0 ≤ (m : ℤ) + 1 +
              finiteExtensionPrincipalDivisor K L x.1 Q
            rw [hm]
            omega)
  have hResidueRank : Module.finrank K (IsLocalRing.ResidueField R) =
      finiteExtensionPlaceDegree K L (.inl q) := by
    simpa [R] using
      (finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q).symm
  let f := localLeadingResidueLinearMap (K := K) (R := R) (L := L)
    T a hregular
  have hST : S ≤ T := by
    apply finiteExtensionRiemannSpace_mono
    intro v
    classical
    by_cases hv : v = Q <;> simp [hv]
  have hkerPoint (x : T) : f x = 0 ↔ x.1 ∈ S := by
    rw [localLeadingResidueLinearMap_eq_zero_iff
      (K := K) (R := R) (L := L) T a hregular,
      localNormalizedLift_mem_maximalIdeal_iff]
    constructor
    · intro haxOrder
      change (1 : WithTop ℤ) ≤
        finiteExtensionFinitePlaceLocalOrderTop (K := K) (L := L) q (a * x.1) at haxOrder
      by_cases hx0 : x.1 = 0
      · simp [hx0]
      · have hxQ :
            0 ≤ finiteExtensionPrincipalDivisor K L x.1 Q + D Q := by
          rw [finiteExtensionFinitePlaceLocalOrderTop_mul,
            show a = πL ^ (m + 1) by rfl,
            finiteExtensionFinitePlaceLocalOrderTop_pow,
            hπOrder,
            finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
              K L q x.1 hx0] at haxOrder
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
      · simp [hx0, finitePlaceOrderTop]
      · have hxmem :=
          (mem_finiteExtensionRiemannSpace (K := K) (L := L)).mp hxS
        rcases hxmem with hxmem | ⟨_, hxorders⟩
        · exact (hx0 hxmem).elim
        · have hxQ := hxorders Q
          have haxOrder :
              (1 : WithTop ℤ) ≤
                finiteExtensionFinitePlaceLocalOrderTop
                  (K := K) (L := L) q (a * x.1) := by
            rw [finiteExtensionFinitePlaceLocalOrderTop_mul,
              show a = πL ^ (m + 1) by rfl,
              finiteExtensionFinitePlaceLocalOrderTop_pow,
              hπOrder,
              finiteExtensionFinitePlaceLocalOrderTop_eq_principalDivisor
                K L q x.1 hx0]
            rw [show (m + 1) • (1 : WithTop ℤ) =
              ((m + 1 : ℕ) : WithTop ℤ) by simp]
            exact_mod_cast (show 1 ≤ (m : ℤ) + 1 +
              finiteExtensionPrincipalDivisor K L x.1 Q by
                rw [hm]
                omega)
          exact haxOrder
  have hker : f.ker = Submodule.comap T.subtype S := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    exact hkerPoint x
  let : Finite (IsLocalRing.ResidueField R) := by
    simpa [R] using
      finiteExtensionFinitePlace_residueField_finite (K := K) (L := L) q
  let : Module.Finite K (IsLocalRing.ResidueField R) :=
    Module.Finite.of_finite
  let : Module.Finite K f.range := inferInstance
  let : Module.Finite K f.ker := by
    rw [hker]
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hST).symm
  let : Module.Finite K (T ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  let hTFinite : Module.Finite K T :=
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
          finiteExtensionPlaceDegree K L (.inl q) := by
        rw [hResidueRank, Nat.add_comm]

end PlaceDegree

end
end BGS.HasseWeil
