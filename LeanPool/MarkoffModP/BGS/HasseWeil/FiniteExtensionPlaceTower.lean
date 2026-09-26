/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
public import LeanPool.MarkoffModP.BGS.HasseWeil.FixedPointAverage
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Restriction of function-field places in a finite tower

Stichtenoth's fixed-field proof of the Hasse--Weil lower bound compares
rational places in several intermediate fields of one Galois tower.  This file
starts that tower API for the repository's exhaustive place type.  It restricts
both finite places and places above infinity by contracting the corresponding
height-one prime through the integral closures.

The construction is intrinsic to the field tower.  It assumes no point-count
bound, zeta theorem, or Hasse--Weil statement.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise Polynomial
open IsDedekindDomain

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (M : Type*) [Field M] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra M L] [IsScalarTower (RatFunc K) M L]

local instance (priority := 10) finitePlaceTowerPolynomialAlgebraM : Algebra K[X] M :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) M).comp
    (algebraMap K[X] (RatFunc K)))

local instance (priority := 10) finitePlaceTowerPolynomialAlgebraL : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance finitePlaceTowerPolynomialRatFuncM :
    IsScalarTower K[X] (RatFunc K) M :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finitePlaceTowerPolynomialRatFuncL :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finitePlaceTowerPolynomialFields : IsScalarTower K[X] M L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) x) =
      algebraMap M L
        (algebraMap (RatFunc K) M (algebraMap K[X] (RatFunc K) x))
    exact IsScalarTower.algebraMap_apply (RatFunc K) M L _

/-- The field inclusion maps the finite integral closure in an intermediate
field into the finite integral closure in the top field. -/
def finiteIntegralClosureMap :
    RatFuncFiniteIntegralClosure K M →ₐ[K[X]]
      RatFuncFiniteIntegralClosure K L :=
  (IsScalarTower.toAlgHom K[X] M L).mapIntegralClosure

local instance finitePlaceTowerIntegralClosureAlgebra :
    Algebra (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  (finiteIntegralClosureMap K M L).toAlgebra

local instance finitePlaceTowerIntermediateIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isIntegral_algebra K[X] M

local instance finitePlaceTowerIntermediateModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K M) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K M)

local instance finitePlaceTowerIntermediateTorsionFree :
    Module.IsTorsionFree K[X] M :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) M

local instance finitePlaceTowerIntermediateClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isTorsionFree K[X] M

local instance finitePlaceTowerIntermediateDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) M
    (RatFuncFiniteIntegralClosure K M)

local instance finitePlaceTowerBaseIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance finitePlaceTowerTopModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerTopTorsionFree :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance finitePlaceTowerTopClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance finitePlaceTowerTopDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerIntegralClosures :
    IsScalarTower K[X] (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq fun _ => by
    apply Subtype.ext
    change algebraMap K[X] L _ = algebraMap M L (algebraMap K[X] M _)
    exact IsScalarTower.algebraMap_apply K[X] M L _

local instance finitePlaceTowerTopIntegral :
    Algebra.IsIntegral (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  Algebra.IsIntegral.tower_top K[X]

local instance finitePlaceTowerFaithful :
    FaithfulSMul (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap M L).injective
  exact congrArg Subtype.val hxy

local instance finitePlaceTowerRelativeModuleFinite :
    Module.Finite (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  Module.Finite.of_restrictScalars_finite K[X]
    (RatFuncFiniteIntegralClosure K M)
    (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerIntermediateFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K M) M :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) M (RatFuncFiniteIntegralClosure K M)

local instance finitePlaceTowerTopFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) L (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerIntermediateClosureFieldTower :
    IsScalarTower (RatFuncFiniteIntegralClosure K M) M L :=
  inferInstance

local instance finitePlaceTowerTopClosureFieldTower :
    IsScalarTower (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def, map_mul]
    rw [show algebraMap (RatFuncFiniteIntegralClosure K L) L
        (algebraMap (RatFuncFiniteIntegralClosure K M)
          (RatFuncFiniteIntegralClosure K L) r) =
        algebraMap (RatFuncFiniteIntegralClosure K M) L r by rfl]
    ring⟩

local instance finitePlaceTowerRelativeIsIntegralClosure :
    IsIntegralClosure (RatFuncFiniteIntegralClosure K L)
      (RatFuncFiniteIntegralClosure K M) L :=
  IsIntegralClosure.tower_top (R := K[X])

/-- Restriction of a finite place contracts its height-one prime to the
intermediate finite integral closure. -/
def finitePlaceUnder
    (P : FiniteExtensionFinitePlace K L) :
    FiniteExtensionFinitePlace K M :=
  HeightOneSpectrum.under (RatFuncFiniteIntegralClosure K M) P

omit [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finitePlaceUnder_asIdeal
    (P : FiniteExtensionFinitePlace K L) :
    (finitePlaceUnder K M L P).asIdeal =
      P.asIdeal.under (RatFuncFiniteIntegralClosure K M) := rfl

omit [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Restricting a finite place through the intermediate field preserves the
place below it in the rational function field. -/
@[simp]
theorem finitePlaceUnder_under
    (P : FiniteExtensionFinitePlace K L) :
    HeightOneSpectrum.under K[X] (finitePlaceUnder K M L P) =
      HeightOneSpectrum.under K[X] P := by
  apply HeightOneSpectrum.ext
  exact Ideal.under_under P.asIdeal

/-- The field inclusion maps the integral closure of the infinity valuation
ring in an intermediate field into the corresponding top integral closure. -/
def infinityIntegralClosureMap :
    RatFuncInfinityIntegralClosure K M →ₐ[RatFuncInfinityIntegers K]
      RatFuncInfinityIntegralClosure K L :=
  (IsScalarTower.toAlgHom (RatFuncInfinityIntegers K) M L).mapIntegralClosure

local instance infinityPlaceTowerIntegralClosureAlgebra :
    Algebra (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  (infinityIntegralClosureMap K M L).toAlgebra

local instance infinityPlaceTowerIntermediateIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) M

local instance infinityPlaceTowerIntermediateModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) M
    (RatFuncInfinityIntegralClosure K M)

local instance infinityPlaceTowerIntermediateClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) M

local instance infinityPlaceTowerIntermediateDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) M (RatFuncInfinityIntegralClosure K M)

local instance infinityPlaceTowerBaseIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance infinityPlaceTowerTopModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerTopClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance infinityPlaceTowerTopDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) L (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerIntegralClosures :
    IsScalarTower (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq fun _ => by
    apply Subtype.ext
    change algebraMap (RatFuncInfinityIntegers K) L _ =
      algebraMap M L (algebraMap (RatFuncInfinityIntegers K) M _)
    exact IsScalarTower.algebraMap_apply (RatFuncInfinityIntegers K) M L _

local instance infinityPlaceTowerTopIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  Algebra.IsIntegral.tower_top (RatFuncInfinityIntegers K)

local instance infinityPlaceTowerFaithful :
    FaithfulSMul (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap M L).injective
  exact congrArg Subtype.val hxy

local instance infinityPlaceTowerRelativeModuleFinite :
    Module.Finite (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  Module.Finite.of_restrictScalars_finite (RatFuncInfinityIntegers K)
    (RatFuncInfinityIntegralClosure K M)
    (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerIntermediateFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K M) M :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) M
    (RatFuncInfinityIntegralClosure K M)

local instance infinityPlaceTowerTopFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerIntermediateClosureFieldTower :
    IsScalarTower (RatFuncInfinityIntegralClosure K M) M L :=
  inferInstance

local instance infinityPlaceTowerTopClosureFieldTower :
    IsScalarTower (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def, map_mul]
    rw [show algebraMap (RatFuncInfinityIntegralClosure K L) L
        (algebraMap (RatFuncInfinityIntegralClosure K M)
          (RatFuncInfinityIntegralClosure K L) r) =
        algebraMap (RatFuncInfinityIntegralClosure K M) L r by rfl]
    ring⟩

local instance infinityPlaceTowerRelativeIsIntegralClosure :
    IsIntegralClosure (RatFuncInfinityIntegralClosure K L)
      (RatFuncInfinityIntegralClosure K M) L :=
  IsIntegralClosure.tower_top (R := RatFuncInfinityIntegers K)

/-- Restriction of a place above infinity contracts its prime to the
intermediate integral closure.  The tower law for ideals proves that the
contracted prime still lies above the distinguished infinity place. -/
def infinityPlaceUnder
    (P : FiniteExtensionInfinityPlace K L) :
    FiniteExtensionInfinityPlace K M := by
  let wL : HeightOneSpectrum (RatFuncInfinityIntegralClosure K L) :=
    primeOverHeightOne (ratFuncInfinityPlace K) P
  let wM : HeightOneSpectrum (RatFuncInfinityIntegralClosure K M) :=
    HeightOneSpectrum.under (RatFuncInfinityIntegralClosure K M) wL
  refine ⟨wM.asIdeal, wM.isPrime, ?_⟩
  have hwM : wM.asIdeal =
      wL.asIdeal.under (RatFuncInfinityIntegralClosure K M) := rfl
  let : wL.asIdeal.LiesOver wM.asIdeal := by
    rw [hwM]
    infer_instance
  let : wL.asIdeal.LiesOver (ratFuncInfinityPlace K).asIdeal := by
    change P.1.LiesOver (ratFuncInfinityPlace K).asIdeal
    infer_instance
  exact Ideal.LiesOver.tower_bot wL.asIdeal wM.asIdeal
    (ratFuncInfinityPlace K).asIdeal

omit [DecidableEq K] [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem infinityPlaceUnder_asIdeal
    (P : FiniteExtensionInfinityPlace K L) :
    (infinityPlaceUnder K M L P).1 =
      P.1.under (RatFuncInfinityIntegralClosure K M) := by
  rfl

/-- Restriction on the exhaustive sum of finite and above-infinity places. -/
def placeUnder : FiniteExtensionPlace K L → FiniteExtensionPlace K M
  | .inl P => .inl (finitePlaceUnder K M L P)
  | .inr P => .inr (infinityPlaceUnder K M L P)

omit [DecidableEq K] [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem placeUnder_inl
    (P : FiniteExtensionFinitePlace K L) :
    placeUnder K M L (.inl P) = .inl (finitePlaceUnder K M L P) := rfl

omit [DecidableEq K] [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem placeUnder_inr
    (P : FiniteExtensionInfinityPlace K L) :
    placeUnder K M L (.inr P) = .inr (infinityPlaceUnder K M L P) := rfl

omit [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Every finite place of the intermediate field has a finite place above it
in the top field.  This is lying-over for the induced integral-closure map. -/
theorem finitePlaceUnder_surjective :
    Function.Surjective (finitePlaceUnder K M L) := by
  intro P
  let Q : P.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) :=
    Classical.choice inferInstance
  let : Q.1.LiesOver P.asIdeal := Q.2.2
  have hQ0 : Q.1 ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2
  let q : FiniteExtensionFinitePlace K L := ⟨Q.1, Q.2.1, hQ0⟩
  refine ⟨q, ?_⟩
  apply HeightOneSpectrum.ext
  exact (Ideal.over_def Q.1 P.asIdeal).symm

omit [DecidableEq K] [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- Every place above infinity in the intermediate field has a place above it
in the top field. -/
theorem infinityPlaceUnder_surjective :
    Function.Surjective (infinityPlaceUnder K M L) := by
  intro P
  let Q : P.1.primesOver (RatFuncInfinityIntegralClosure K L) :=
    Classical.choice inferInstance
  let : Q.1.LiesOver P.1 := Q.2.2
  let : P.1.LiesOver (ratFuncInfinityPlace K).asIdeal := P.2.2
  let : Q.1.LiesOver (ratFuncInfinityPlace K).asIdeal :=
    Ideal.LiesOver.trans Q.1 P.1 (ratFuncInfinityPlace K).asIdeal
  let q : FiniteExtensionInfinityPlace K L :=
    ⟨Q.1, Q.2.1, inferInstance⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact (Ideal.over_def Q.1 P.1).symm

omit [DecidableEq K] [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- Restriction from the top field is surjective on the exhaustive place
type. -/
theorem placeUnder_surjective :
    Function.Surjective (placeUnder K M L) := by
  intro P
  rcases P with P | P
  · obtain ⟨Q, hQ⟩ := finitePlaceUnder_surjective K M L P
    exact ⟨.inl Q, congrArg Sum.inl hQ⟩
  · obtain ⟨Q, hQ⟩ := infinityPlaceUnder_surjective K M L P
    exact ⟨.inr Q, congrArg Sum.inr hQ⟩

/-- The finite places of the top field above a fixed intermediate finite
place. -/
abbrev FinitePlaceUnderFiber (P : FiniteExtensionFinitePlace K M) :=
  {Q : FiniteExtensionFinitePlace K L // finitePlaceUnder K M L Q = P}

/-- A restriction fiber is the usual finite set of primes lying over the
contracted prime ideal. -/
def finitePlaceUnderFiberEquivPrimesOver
    (P : FiniteExtensionFinitePlace K M) :
    FinitePlaceUnderFiber K M L P ≃
      P.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) where
  toFun Q := ⟨Q.1.asIdeal, Q.1.isPrime, ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal Q.2
    exact h.symm⟩⟩
  invFun Q := ⟨primeOverHeightOne P Q, by
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def Q.1 P.asIdeal).symm⟩
  left_inv Q := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    rfl

noncomputable instance finitePlaceUnderFiberFintype
    (P : FiniteExtensionFinitePlace K M) :
    Fintype (FinitePlaceUnderFiber K M L P) :=
  Fintype.ofEquiv
    (P.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L))
    (finitePlaceUnderFiberEquivPrimesOver K M L P).symm

/-- The places of the top field above a fixed intermediate place at
infinity. -/
abbrev InfinityPlaceUnderFiber (P : FiniteExtensionInfinityPlace K M) :=
  {Q : FiniteExtensionInfinityPlace K L //
    infinityPlaceUnder K M L Q = P}

/-- The restriction fiber above infinity is likewise the finite set of primes
over the corresponding intermediate prime. -/
def infinityPlaceUnderFiberEquivPrimesOver
    (P : FiniteExtensionInfinityPlace K M) :
    InfinityPlaceUnderFiber K M L P ≃
      P.1.primesOver (RatFuncInfinityIntegralClosure K L) where
  toFun Q := ⟨Q.1.1, Q.1.2.1, ⟨by
    have h := congrArg Subtype.val Q.2
    exact h.symm⟩⟩
  invFun Q := by
    letI : Q.1.LiesOver P.1 := Q.2.2
    letI : P.1.LiesOver (ratFuncInfinityPlace K).asIdeal := P.2.2
    letI : Q.1.LiesOver (ratFuncInfinityPlace K).asIdeal :=
      Ideal.LiesOver.trans Q.1 P.1 (ratFuncInfinityPlace K).asIdeal
    let q : FiniteExtensionInfinityPlace K L :=
      ⟨Q.1, Q.2.1, inferInstance⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact (Ideal.over_def Q.1 P.1).symm
  left_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    rfl

noncomputable instance infinityPlaceUnderFiberFintype
    (P : FiniteExtensionInfinityPlace K M) :
    Fintype (InfinityPlaceUnderFiber K M L P) :=
  Fintype.ofEquiv
    (P.1.primesOver (RatFuncInfinityIntegralClosure K L))
    (infinityPlaceUnderFiberEquivPrimesOver K M L P).symm

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Algebra.IsSeparable (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- The rank of the relative finite integral-closure extension is the field
degree of the top function field over the intermediate field. -/
theorem finiteIntegralClosure_relative_finrank_eq_field_finrank :
    Module.finrank (RatFuncFiniteIntegralClosure K M)
        (RatFuncFiniteIntegralClosure K L) =
      Module.finrank M L := by
  exact (IsFractionRing.finrank_eq
    (RatFuncFiniteIntegralClosure K M) M
    (RatFuncFiniteIntegralClosure K L) L).symm

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) L] in
/-- The infinity integral-closure model has the same relative rank, namely
the degree of the field extension. -/
theorem infinityIntegralClosure_relative_finrank_eq_field_finrank :
    Module.finrank (RatFuncInfinityIntegralClosure K M)
        (RatFuncInfinityIntegralClosure K L) =
      Module.finrank M L := by
  exact (IsFractionRing.finrank_eq
    (RatFuncInfinityIntegralClosure K M) M
    (RatFuncInfinityIntegralClosure K L) L).symm

/-- Ramification index of a top finite place over the intermediate finite
integral closure. -/
noncomputable def finitePlaceRelativeRamificationIdx
    (Q : FiniteExtensionFinitePlace K L) : ℕ :=
  Q.asIdeal.ramificationIdx (RatFuncFiniteIntegralClosure K M)

/-- Inertia degree of a top finite place over the intermediate finite
integral closure. -/
noncomputable def finitePlaceRelativeInertiaDeg
    (Q : FiniteExtensionFinitePlace K L) : ℕ :=
  Q.asIdeal.inertiaDeg (RatFuncFiniteIntegralClosure K M)

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The fundamental equality for the finite-place restriction fiber. -/
theorem sum_finitePlaceUnderFiber_ramification_inertia_eq_finrank
    (P : FiniteExtensionFinitePlace K M) :
    ∑ Q : FinitePlaceUnderFiber K M L P,
        finitePlaceRelativeRamificationIdx K M L Q.1 *
          finitePlaceRelativeInertiaDeg K M L Q.1 =
      Module.finrank (RatFuncFiniteIntegralClosure K M)
        (RatFuncFiniteIntegralClosure K L) := by
  classical
  let e := finitePlaceUnderFiberEquivPrimesOver K M L P
  calc
    _ = ∑ Q : P.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L),
        Q.1.ramificationIdx (RatFuncFiniteIntegralClosure K M) *
          Q.1.inertiaDeg (RatFuncFiniteIntegralClosure K M) := by
      apply Fintype.sum_equiv e
      intro Q
      rfl
    _ = _ := Ideal.sum_ramification_inertia_eq_finrank P.asIdeal
      (RatFuncFiniteIntegralClosure K L)

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Field-degree form of the finite-place fundamental equality. -/
theorem sum_finitePlaceUnderFiber_ramification_inertia_eq_field_finrank
    (P : FiniteExtensionFinitePlace K M) :
    ∑ Q : FinitePlaceUnderFiber K M L P,
        finitePlaceRelativeRamificationIdx K M L Q.1 *
          finitePlaceRelativeInertiaDeg K M L Q.1 =
      Module.finrank M L := by
  rw [sum_finitePlaceUnderFiber_ramification_inertia_eq_finrank K M L P,
    finiteIntegralClosure_relative_finrank_eq_field_finrank K M L]

/-- Ramification index of a top place above infinity over the intermediate
infinity integral closure. -/
noncomputable def infinityPlaceRelativeRamificationIdx
    (Q : FiniteExtensionInfinityPlace K L) : ℕ :=
  Q.1.ramificationIdx (RatFuncInfinityIntegralClosure K M)

/-- Inertia degree of a top place above infinity over the intermediate
infinity integral closure. -/
noncomputable def infinityPlaceRelativeInertiaDeg
    (Q : FiniteExtensionInfinityPlace K L) : ℕ :=
  Q.1.inertiaDeg (RatFuncInfinityIntegralClosure K M)

omit [DecidableEq K] in
/-- The fundamental equality for the restriction fiber above infinity. -/
theorem sum_infinityPlaceUnderFiber_ramification_inertia_eq_finrank
    (P : FiniteExtensionInfinityPlace K M) :
    ∑ Q : InfinityPlaceUnderFiber K M L P,
        infinityPlaceRelativeRamificationIdx K M L Q.1 *
          infinityPlaceRelativeInertiaDeg K M L Q.1 =
      Module.finrank (RatFuncInfinityIntegralClosure K M)
        (RatFuncInfinityIntegralClosure K L) := by
  classical
  let : P.1.IsPrime := P.2.1
  let e := infinityPlaceUnderFiberEquivPrimesOver K M L P
  calc
    _ = ∑ Q : P.1.primesOver (RatFuncInfinityIntegralClosure K L),
        Q.1.ramificationIdx (RatFuncInfinityIntegralClosure K M) *
          Q.1.inertiaDeg (RatFuncInfinityIntegralClosure K M) := by
      apply Fintype.sum_equiv e
      intro Q
      rfl
    _ = _ := Ideal.sum_ramification_inertia_eq_finrank P.1
      (RatFuncInfinityIntegralClosure K L)

omit [DecidableEq K] in
/-- Field-degree form of the fundamental equality above infinity. -/
theorem sum_infinityPlaceUnderFiber_ramification_inertia_eq_field_finrank
    (P : FiniteExtensionInfinityPlace K M) :
    ∑ Q : InfinityPlaceUnderFiber K M L P,
        infinityPlaceRelativeRamificationIdx K M L Q.1 *
          infinityPlaceRelativeInertiaDeg K M L Q.1 =
      Module.finrank M L := by
  rw [sum_infinityPlaceUnderFiber_ramification_inertia_eq_finrank K M L P,
    infinityIntegralClosure_relative_finrank_eq_field_finrank K M L]

omit [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- Place degree is multiplicative when a finite place is restricted through
an intermediate function field.  The second factor is the residue-field
degree in the relative extension. -/
theorem finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg
    (Q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPlaceDegree K L (.inl Q) =
      finiteExtensionPlaceDegree K M
          (.inl (finitePlaceUnder K M L Q)) *
        finitePlaceRelativeInertiaDeg K M L Q := by
  let P := finitePlaceUnder K M L Q
  let : Q.asIdeal.LiesOver P.asIdeal :=
    ⟨finitePlaceUnder_asIdeal K M L Q⟩
  rw [finiteExtensionPlaceDegree, finiteExtensionPlaceDegree,
    finitePlaceRelativeInertiaDeg]
  rw [Ideal.inertiaDeg_tower (R := K[X]) P.asIdeal Q.asIdeal]
  rw [finitePlaceUnder_under]
  ring

omit [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- The analogous degree-tower formula for places above infinity. -/
theorem finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg
    (Q : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPlaceDegree K L (.inr Q) =
      finiteExtensionPlaceDegree K M
          (.inr (infinityPlaceUnder K M L Q)) *
        infinityPlaceRelativeInertiaDeg K M L Q := by
  let P := infinityPlaceUnder K M L Q
  let : Q.1.LiesOver P.1 :=
    ⟨infinityPlaceUnder_asIdeal K M L Q⟩
  rw [finiteExtensionPlaceDegree, finiteExtensionPlaceDegree,
    infinityPlaceRelativeInertiaDeg]
  exact Ideal.inertiaDeg_tower P.1 Q.1

omit [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- Exhaustive place degree is multiplicative under restriction through an
intermediate function field. -/
theorem finiteExtensionPlaceDegree_eq_under_mul_relativeInertiaDeg
    (Q : FiniteExtensionPlace K L) :
    finiteExtensionPlaceDegree K L Q =
      finiteExtensionPlaceDegree K M (placeUnder K M L Q) *
        match Q with
        | .inl q => finitePlaceRelativeInertiaDeg K M L q
        | .inr q => infinityPlaceRelativeInertiaDeg K M L q := by
  cases Q with
  | inl Q =>
      exact finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg K M L Q
  | inr Q =>
      exact finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M L Q

section Galois

variable [IsGalois M L]

/-- The field Galois group acts on the finite integral closure in the top
field, relative to the intermediate finite integral closure. -/
@[implicit_reducible]
noncomputable def finiteIntegralClosureGalAction :
    MulSemiringAction Gal(L/M) (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.MulSemiringAction
    (RatFuncFiniteIntegralClosure K M) M L
    (RatFuncFiniteIntegralClosure K L)

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- The relative Galois action fixes the intermediate finite integral
closure. -/
theorem finiteIntegralClosureGalSmulComm :
    letI := finiteIntegralClosureGalAction K M L
    SMulCommClass Gal(L/M) (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) := by
  let := finiteIntegralClosureGalAction K M L
  constructor
  intro g r s
  change galRestrict (RatFuncFiniteIntegralClosure K M) M L
      (RatFuncFiniteIntegralClosure K L) g
        (algebraMap (RatFuncFiniteIntegralClosure K M)
          (RatFuncFiniteIntegralClosure K L) r * s) =
    algebraMap (RatFuncFiniteIntegralClosure K M)
        (RatFuncFiniteIntegralClosure K L) r *
      galRestrict (RatFuncFiniteIntegralClosure K M) M L
        (RatFuncFiniteIntegralClosure K L) g s
  rw [map_mul, AlgEquiv.commutes]

/-- The relative Galois action on a finite place, obtained by acting on its
height-one prime ideal. -/
noncomputable def finitePlaceGalSmul
    (g : Gal(L/M)) (P : FiniteExtensionFinitePlace K L) :
    FiniteExtensionFinitePlace K L := by
  letI := finiteIntegralClosureGalAction K M L
  refine ⟨g • P.asIdeal, P.isPrime.smul g, ?_⟩
  intro hbot
  apply P.ne_bot
  have h := congrArg
    (fun I : Ideal (RatFuncFiniteIntegralClosure K L) => g⁻¹ • I) hbot
  simpa [smul_smul] using h

/-- The relative Galois group acts on finite places of the top function
field. -/
@[implicit_reducible]
noncomputable def finitePlaceGalAction :
    MulAction Gal(L/M) (FiniteExtensionFinitePlace K L) := by
  letI := finiteIntegralClosureGalAction K M L
  exact
    { smul := finitePlaceGalSmul K M L
      one_smul := fun P => by
        apply HeightOneSpectrum.ext
        change (1 : Gal(L/M)) • P.asIdeal = P.asIdeal
        simp
      mul_smul := fun g h P => by
        apply HeightOneSpectrum.ext
        change (g * h) • P.asIdeal = g • h • P.asIdeal
        rw [mul_smul] }

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- Relative Galois conjugation does not change the restricted finite place. -/
@[simp]
theorem finitePlaceUnder_finitePlaceGalSmul
    (g : Gal(L/M)) (P : FiniteExtensionFinitePlace K L) :
    finitePlaceUnder K M L (finitePlaceGalSmul K M L g P) =
      finitePlaceUnder K M L P := by
  let := finiteIntegralClosureGalAction K M L
  let := finiteIntegralClosureGalSmulComm K M L
  apply HeightOneSpectrum.ext
  change (g • P.asIdeal).under (RatFuncFiniteIntegralClosure K M) =
    P.asIdeal.under (RatFuncFiniteIntegralClosure K M)
  exact P.asIdeal.under_smul (RatFuncFiniteIntegralClosure K M) g

/-- The relative Galois action restricts to every finite-place fiber. -/
@[implicit_reducible]
noncomputable def finitePlaceUnderFiberGalAction
    (P : FiniteExtensionFinitePlace K M) :
    MulAction Gal(L/M) (FinitePlaceUnderFiber K M L P) := by
  letI := finiteIntegralClosureGalAction K M L
  exact
    { smul := fun g Q => ⟨finitePlaceGalSmul K M L g Q.1, by
        rw [finitePlaceUnder_finitePlaceGalSmul, Q.2]⟩
      one_smul := fun Q => by
        apply Subtype.ext
        apply HeightOneSpectrum.ext
        change (1 : Gal(L/M)) • Q.1.asIdeal = Q.1.asIdeal
        simp
      mul_smul := fun g h Q => by
        apply Subtype.ext
        apply HeightOneSpectrum.ext
        change (g * h) • Q.1.asIdeal = g • h • Q.1.asIdeal
        rw [mul_smul] }

/-- Galois conjugacy of finite places, expressed on their prime ideals. -/
def FinitePlacesGaloisConjugate
    (P Q : FiniteExtensionFinitePlace K L) : Prop :=
  letI := finiteIntegralClosureGalAction K M L
  ∃ g : Gal(L/M), Q.asIdeal = g • P.asIdeal

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Algebra.IsSeparable (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Two finite places above the same intermediate place are conjugate under
the relative field Galois group. -/
theorem exists_gal_smul_finitePlace_asIdeal_of_same_under
    (P Q : FiniteExtensionFinitePlace K L)
    (hPQ : finitePlaceUnder K M L P = finitePlaceUnder K M L Q) :
    FinitePlacesGaloisConjugate K M L P Q := by
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := finiteIntegralClosureGalAction K M L
  change ∃ g : Gal(L/M), Q.asIdeal = g • P.asIdeal
  let := finiteIntegralClosureGalSmulComm K M L
  let : Algebra.IsInvariant (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) Gal(L/M) :=
    Algebra.isInvariant_of_isGalois
      (RatFuncFiniteIntegralClosure K M) M L
      (RatFuncFiniteIntegralClosure K L)
  let : P.asIdeal.IsPrime := P.isPrime
  let : Q.asIdeal.IsPrime := Q.isPrime
  apply Algebra.IsInvariant.exists_smul_of_under_eq
    (RatFuncFiniteIntegralClosure K M)
    (RatFuncFiniteIntegralClosure K L) Gal(L/M)
  simpa only [finitePlaceUnder_asIdeal] using
    congrArg HeightOneSpectrum.asIdeal hPQ

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Algebra.IsSeparable (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Each finite-place restriction fiber is a transitive relative Galois
set. -/
theorem finitePlaceUnderFiberGalAction_isPretransitive
    (P : FiniteExtensionFinitePlace K M) :
    letI := finitePlaceUnderFiberGalAction K M L P
    MulAction.IsPretransitive Gal(L/M) (FinitePlaceUnderFiber K M L P) := by
  let := finiteIntegralClosureGalAction K M L
  let := finitePlaceUnderFiberGalAction K M L P
  constructor
  intro Q R
  obtain ⟨g, hg⟩ :=
    exists_gal_smul_finitePlace_asIdeal_of_same_under
      K M L Q.1 R.1 (Q.2.trans R.2.symm)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  change g • Q.1.asIdeal = R.1.asIdeal
  exact hg.symm

/-- Finite places in a restriction fiber fixed by one relative Galois
automorphism. -/
noncomputable def finitePlaceUnderFiberFixedBy
    (P : FiniteExtensionFinitePlace K M) (g : Gal(L/M)) : Type _ :=
  letI := finitePlaceUnderFiberGalAction K M L P
  MulAction.fixedBy (FinitePlaceUnderFiber K M L P) g

/-- The exact local fixed-point trace identity for a finite-place restriction
fiber. -/
theorem sum_card_finitePlaceUnderFiberFixedBy_eq_card_galoisGroup
    (P : FiniteExtensionFinitePlace K M) :
    letI : Module.Finite M L :=
      Module.Finite.of_restrictScalars_finite (RatFunc K) M L
    (∑ g : Gal(L/M), Nat.card (finitePlaceUnderFiberFixedBy K M L P g)) =
      Nat.card Gal(L/M) := by
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := finitePlaceUnderFiberGalAction K M L P
  let : MulAction.IsPretransitive Gal(L/M)
      (FinitePlaceUnderFiber K M L P) :=
    finitePlaceUnderFiberGalAction_isPretransitive K M L P
  let : Nonempty (FinitePlaceUnderFiber K M L P) := by
    obtain ⟨Q, hQ⟩ := finitePlaceUnder_surjective K M L P
    exact ⟨⟨Q, hQ⟩⟩
  change (∑ g : Gal(L/M),
    Nat.card (MulAction.fixedBy (FinitePlaceUnderFiber K M L P) g)) = _
  exact sum_card_fixedBy_eq_card_group_of_isPretransitive
    Gal(L/M) (FinitePlaceUnderFiber K M L P)

/-- The same relative Galois group acts on the integral closure of the
infinity valuation ring. -/
@[implicit_reducible]
noncomputable def infinityIntegralClosureGalAction :
    MulSemiringAction Gal(L/M) (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.MulSemiringAction
    (RatFuncInfinityIntegralClosure K M) M L
    (RatFuncInfinityIntegralClosure K L)

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- The relative Galois action fixes the intermediate infinity integral
closure. -/
theorem infinityIntegralClosureGalSmulComm :
    letI := infinityIntegralClosureGalAction K M L
    SMulCommClass Gal(L/M) (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) := by
  let := infinityIntegralClosureGalAction K M L
  constructor
  intro g r s
  change galRestrict (RatFuncInfinityIntegralClosure K M) M L
      (RatFuncInfinityIntegralClosure K L) g
        (algebraMap (RatFuncInfinityIntegralClosure K M)
          (RatFuncInfinityIntegralClosure K L) r * s) =
    algebraMap (RatFuncInfinityIntegralClosure K M)
        (RatFuncInfinityIntegralClosure K L) r *
      galRestrict (RatFuncInfinityIntegralClosure K M) M L
        (RatFuncInfinityIntegralClosure K L) g s
  rw [map_mul, AlgEquiv.commutes]

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- The relative Galois action also commutes with scalars from the base
infinity valuation ring. -/
theorem ratFuncInfinityIntegersGalSmulComm :
    letI := infinityIntegralClosureGalAction K M L
    SMulCommClass Gal(L/M) (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) := by
  let := infinityIntegralClosureGalAction K M L
  let := infinityIntegralClosureGalSmulComm K M L
  constructor
  intro g r s
  calc
    g • (r • s) = g • ((algebraMap (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K M) r) • s) := by
      congr 1
      simp only [Algebra.smul_def,
        IsScalarTower.algebraMap_apply (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K M)
          (RatFuncInfinityIntegralClosure K L)]
    _ = (algebraMap (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K M) r) • (g • s) :=
      smul_comm g
        (algebraMap (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K M) r) s
    _ = r • (g • s) := by
      simp only [Algebra.smul_def,
        IsScalarTower.algebraMap_apply (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K M)
          (RatFuncInfinityIntegralClosure K L)]

/-- The relative Galois action on a place above infinity, obtained by acting
on its prime ideal. -/
noncomputable def infinityPlaceGalSmul
    (g : Gal(L/M)) (P : FiniteExtensionInfinityPlace K L) :
    FiniteExtensionInfinityPlace K L := by
  letI := infinityIntegralClosureGalAction K M L
  letI := ratFuncInfinityIntegersGalSmulComm K M L
  refine ⟨g • P.1, P.2.1.smul g, ?_⟩
  exact P.2.2.smul g

/-- The relative Galois group acts on places above infinity of the top
function field. -/
@[implicit_reducible]
noncomputable def infinityPlaceGalAction :
    MulAction Gal(L/M) (FiniteExtensionInfinityPlace K L) := by
  letI := infinityIntegralClosureGalAction K M L
  exact
    { smul := infinityPlaceGalSmul K M L
      one_smul := fun P => by
        apply Subtype.ext
        change (1 : Gal(L/M)) • P.1 = P.1
        simp
      mul_smul := fun g h P => by
        apply Subtype.ext
        change (g * h) • P.1 = g • h • P.1
        rw [mul_smul] }

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Relative Galois conjugation does not change the restricted infinity
place. -/
@[simp]
theorem infinityPlaceUnder_infinityPlaceGalSmul
    (g : Gal(L/M)) (P : FiniteExtensionInfinityPlace K L) :
    infinityPlaceUnder K M L (infinityPlaceGalSmul K M L g P) =
      infinityPlaceUnder K M L P := by
  let := infinityIntegralClosureGalAction K M L
  let := infinityIntegralClosureGalSmulComm K M L
  apply Subtype.ext
  change (g • P.1).under (RatFuncInfinityIntegralClosure K M) =
    P.1.under (RatFuncInfinityIntegralClosure K M)
  exact P.1.under_smul (RatFuncInfinityIntegralClosure K M) g

/-- The relative Galois action restricts to every infinity-place fiber. -/
@[implicit_reducible]
noncomputable def infinityPlaceUnderFiberGalAction
    (P : FiniteExtensionInfinityPlace K M) :
    MulAction Gal(L/M) (InfinityPlaceUnderFiber K M L P) := by
  letI := infinityIntegralClosureGalAction K M L
  exact
    { smul := fun g Q => ⟨infinityPlaceGalSmul K M L g Q.1, by
        rw [infinityPlaceUnder_infinityPlaceGalSmul, Q.2]⟩
      one_smul := fun Q => by
        apply Subtype.ext
        apply Subtype.ext
        change (1 : Gal(L/M)) • Q.1.1 = Q.1.1
        simp
      mul_smul := fun g h Q => by
        apply Subtype.ext
        apply Subtype.ext
        change (g * h) • Q.1.1 = g • h • Q.1.1
        rw [mul_smul] }

/-- Galois conjugacy of places above infinity, expressed on their prime
ideals. -/
def InfinityPlacesGaloisConjugate
    (P Q : FiniteExtensionInfinityPlace K L) : Prop :=
  letI := infinityIntegralClosureGalAction K M L
  ∃ g : Gal(L/M), Q.1 = g • P.1

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) L] in
/-- Two places above infinity with the same intermediate restriction are
conjugate under the relative field Galois group. -/
theorem exists_gal_smul_infinityPlace_asIdeal_of_same_under
    (P Q : FiniteExtensionInfinityPlace K L)
    (hPQ : infinityPlaceUnder K M L P = infinityPlaceUnder K M L Q) :
    InfinityPlacesGaloisConjugate K M L P Q := by
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := infinityIntegralClosureGalAction K M L
  change ∃ g : Gal(L/M), Q.1 = g • P.1
  let := infinityIntegralClosureGalSmulComm K M L
  let : Algebra.IsInvariant (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) Gal(L/M) :=
    Algebra.isInvariant_of_isGalois
      (RatFuncInfinityIntegralClosure K M) M L
      (RatFuncInfinityIntegralClosure K L)
  let : P.1.IsPrime := P.2.1
  let : Q.1.IsPrime := Q.2.1
  apply Algebra.IsInvariant.exists_smul_of_under_eq
    (RatFuncInfinityIntegralClosure K M)
    (RatFuncInfinityIntegralClosure K L) Gal(L/M)
  simpa only [infinityPlaceUnder_asIdeal] using
    congrArg Subtype.val hPQ

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) L] in
/-- Each infinity-place restriction fiber is a transitive relative Galois
set. -/
theorem infinityPlaceUnderFiberGalAction_isPretransitive
    (P : FiniteExtensionInfinityPlace K M) :
    letI := infinityPlaceUnderFiberGalAction K M L P
    MulAction.IsPretransitive Gal(L/M) (InfinityPlaceUnderFiber K M L P) := by
  let := infinityIntegralClosureGalAction K M L
  let := infinityPlaceUnderFiberGalAction K M L P
  constructor
  intro Q R
  obtain ⟨g, hg⟩ :=
    exists_gal_smul_infinityPlace_asIdeal_of_same_under
      K M L Q.1 R.1 (Q.2.trans R.2.symm)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change g • Q.1.1 = R.1.1
  exact hg.symm

/-- Places above infinity in a restriction fiber fixed by one relative Galois
automorphism. -/
noncomputable def infinityPlaceUnderFiberFixedBy
    (P : FiniteExtensionInfinityPlace K M) (g : Gal(L/M)) : Type _ :=
  letI := infinityPlaceUnderFiberGalAction K M L P
  MulAction.fixedBy (InfinityPlaceUnderFiber K M L P) g

/-- The exact local fixed-point trace identity for an infinity-place
restriction fiber. -/
theorem sum_card_infinityPlaceUnderFiberFixedBy_eq_card_galoisGroup
    (P : FiniteExtensionInfinityPlace K M) :
    letI : Module.Finite M L :=
      Module.Finite.of_restrictScalars_finite (RatFunc K) M L
    (∑ g : Gal(L/M), Nat.card (infinityPlaceUnderFiberFixedBy K M L P g)) =
      Nat.card Gal(L/M) := by
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := infinityPlaceUnderFiberGalAction K M L P
  let : MulAction.IsPretransitive Gal(L/M)
      (InfinityPlaceUnderFiber K M L P) :=
    infinityPlaceUnderFiberGalAction_isPretransitive K M L P
  let : Nonempty (InfinityPlaceUnderFiber K M L P) := by
    obtain ⟨Q, hQ⟩ := infinityPlaceUnder_surjective K M L P
    exact ⟨⟨Q, hQ⟩⟩
  change (∑ g : Gal(L/M),
    Nat.card (MulAction.fixedBy (InfinityPlaceUnderFiber K M L P) g)) = _
  exact sum_card_fixedBy_eq_card_group_of_isPretransitive
    Gal(L/M) (InfinityPlaceUnderFiber K M L P)

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Algebra.IsSeparable (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Ramification index and inertia degree are constant on each finite-place
restriction fiber in a Galois tower. -/
theorem finitePlaceRelative_ramificationIdx_inertiaDeg_eq_of_same_under
    (P Q : FiniteExtensionFinitePlace K L)
    (hPQ : finitePlaceUnder K M L P = finitePlaceUnder K M L Q) :
    finitePlaceRelativeRamificationIdx K M L P =
        finitePlaceRelativeRamificationIdx K M L Q ∧
      finitePlaceRelativeInertiaDeg K M L P =
        finitePlaceRelativeInertiaDeg K M L Q := by
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := finiteIntegralClosureGalAction K M L
  let := finiteIntegralClosureGalSmulComm K M L
  obtain ⟨g, hg⟩ :=
    exists_gal_smul_finitePlace_asIdeal_of_same_under K M L P Q hPQ
  constructor
  · unfold finitePlaceRelativeRamificationIdx
    rw [hg, Ideal.ramificationIdx_smul]
  · unfold finitePlaceRelativeInertiaDeg
    rw [hg, Ideal.inertiaDeg_smul]

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) L] in
/-- Ramification index and inertia degree are constant on each restriction
fiber above infinity in a Galois tower. -/
theorem infinityPlaceRelative_ramificationIdx_inertiaDeg_eq_of_same_under
    (P Q : FiniteExtensionInfinityPlace K L)
    (hPQ : infinityPlaceUnder K M L P = infinityPlaceUnder K M L Q) :
    infinityPlaceRelativeRamificationIdx K M L P =
        infinityPlaceRelativeRamificationIdx K M L Q ∧
      infinityPlaceRelativeInertiaDeg K M L P =
        infinityPlaceRelativeInertiaDeg K M L Q := by
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := infinityIntegralClosureGalAction K M L
  let := infinityIntegralClosureGalSmulComm K M L
  obtain ⟨g, hg⟩ :=
    exists_gal_smul_infinityPlace_asIdeal_of_same_under K M L P Q hPQ
  constructor
  · unfold infinityPlaceRelativeRamificationIdx
    rw [hg, Ideal.ramificationIdx_smul]
  · unfold infinityPlaceRelativeInertiaDeg
    rw [hg, Ideal.inertiaDeg_smul]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- In a Galois tower, the number of finite places in a restriction fiber
times their common ramification index and inertia degree is the relative field
degree. -/
theorem finitePlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
    (P : FiniteExtensionFinitePlace K M)
    (Q₀ : FinitePlaceUnderFiber K M L P) :
    Fintype.card (FinitePlaceUnderFiber K M L P) *
          finitePlaceRelativeRamificationIdx K M L Q₀.1 *
        finitePlaceRelativeInertiaDeg K M L Q₀.1 =
      Module.finrank M L := by
  rw [← sum_finitePlaceUnderFiber_ramification_inertia_eq_field_finrank K M L P]
  calc
    _ = Fintype.card (FinitePlaceUnderFiber K M L P) *
        (finitePlaceRelativeRamificationIdx K M L Q₀.1 *
          finitePlaceRelativeInertiaDeg K M L Q₀.1) := by
      rw [Nat.mul_assoc]
    _ = ∑ _Q : FinitePlaceUnderFiber K M L P,
        (finitePlaceRelativeRamificationIdx K M L Q₀.1 *
          finitePlaceRelativeInertiaDeg K M L Q₀.1) := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Q _
      obtain ⟨he, hf⟩ :=
        finitePlaceRelative_ramificationIdx_inertiaDeg_eq_of_same_under
          K M L Q.1 Q₀.1 (Q.2.trans Q₀.2.symm)
      rw [he, hf]

omit [DecidableEq K] in
/-- The analogous Galois decomposition formula for a restriction fiber above
infinity. -/
theorem infinityPlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
    (P : FiniteExtensionInfinityPlace K M)
    (Q₀ : InfinityPlaceUnderFiber K M L P) :
    Fintype.card (InfinityPlaceUnderFiber K M L P) *
          infinityPlaceRelativeRamificationIdx K M L Q₀.1 *
        infinityPlaceRelativeInertiaDeg K M L Q₀.1 =
      Module.finrank M L := by
  rw [← sum_infinityPlaceUnderFiber_ramification_inertia_eq_field_finrank K M L P]
  calc
    _ = Fintype.card (InfinityPlaceUnderFiber K M L P) *
        (infinityPlaceRelativeRamificationIdx K M L Q₀.1 *
          infinityPlaceRelativeInertiaDeg K M L Q₀.1) := by
      rw [Nat.mul_assoc]
    _ = ∑ _Q : InfinityPlaceUnderFiber K M L P,
        (infinityPlaceRelativeRamificationIdx K M L Q₀.1 *
          infinityPlaceRelativeInertiaDeg K M L Q₀.1) := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Q _
      obtain ⟨he, hf⟩ :=
        infinityPlaceRelative_ramificationIdx_inertiaDeg_eq_of_same_under
          K M L Q.1 Q₀.1 (Q.2.trans Q₀.2.symm)
      rw [he, hf]

/-- The decomposition group of a finite place in the relative Galois group. -/
noncomputable def finitePlaceDecompositionGroup
    (P : FiniteExtensionFinitePlace K L) : Subgroup Gal(L/M) :=
  letI := finiteIntegralClosureGalAction K M L
  MulAction.stabilizer Gal(L/M) P.asIdeal

/-- The inertia group of a finite place in the relative Galois group. -/
noncomputable def finitePlaceInertiaGroup
    (P : FiniteExtensionFinitePlace K L) : Subgroup Gal(L/M) :=
  letI := finiteIntegralClosureGalAction K M L
  P.asIdeal.inertia Gal(L/M)

/-- The decomposition group of a place above infinity in the relative Galois
group. -/
noncomputable def infinityPlaceDecompositionGroup
    (P : FiniteExtensionInfinityPlace K L) : Subgroup Gal(L/M) :=
  letI := infinityIntegralClosureGalAction K M L
  MulAction.stabilizer Gal(L/M) P.1

/-- The inertia group of a place above infinity in the relative Galois group. -/
noncomputable def infinityPlaceInertiaGroup
    (P : FiniteExtensionInfinityPlace K L) : Subgroup Gal(L/M) :=
  letI := infinityIntegralClosureGalAction K M L
  P.1.inertia Gal(L/M)

section FiniteConstants

variable [Fintype K]

omit [DecidableEq K] [Fintype K] in
omit [DecidableEq (RatFunc K)] in
private theorem ratFuncFinitePlaceResidueField_finite [Finite K]
    (p : HeightOneSpectrum K[X]) : Finite p.asIdeal.ResidueField := by
  classical
  let r := finitePlaceNormalizedPrime p
  have hr0 : (r : K[X]) ≠ 0 := r.property.1.ne_zero
  have hrmonic : (r : K[X]).Monic :=
    (Polynomial.normalize_eq_self_iff_monic hr0).mp r.property.2
  have hp : p.asIdeal = Ideal.span ({(r : K[X])} : Set K[X]) := by
    calc
      p.asIdeal = (normalizedPrimeFinitePlace (K := K) r).asIdeal := by
        rw [normalizedPrimeFinitePlace_finitePlaceNormalizedPrime]
      _ = Ideal.span ({(r : K[X])} : Set K[X]) := rfl
  let : Module.Finite K (K[X] ⧸ p.asIdeal) := by
    rw [hp]
    exact hrmonic.finite_quotient
  let : Finite (K[X] ⧸ p.asIdeal) := Module.finite_of_finite K
  infer_instance

omit [DecidableEq K] [Fintype K] in
omit [DecidableEq (RatFunc K)] in
private theorem finitePlaceResidueField_finite [Finite K]
    (P : FiniteExtensionFinitePlace K M) : Finite P.asIdeal.ResidueField := by
  classical
  let p := HeightOneSpectrum.under K[X] P
  let : Finite p.asIdeal.ResidueField :=
    ratFuncFinitePlaceResidueField_finite K p
  let : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal P.asIdeal
  have : IsScalarTower K[X] (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime P.asIdeal) := inferInstance
  let : Algebra.QuasiFiniteAt K[X] P.asIdeal := inferInstance
  let : Module.Finite p.asIdeal.ResidueField P.asIdeal.ResidueField :=
    inferInstance
  exact Module.finite_of_finite p.asIdeal.ResidueField

omit [DecidableEq K] [Fintype K] in
private theorem infinityPlaceResidueField_finite [Finite K]
    (P : FiniteExtensionInfinityPlace K M) : Finite P.1.ResidueField := by
  classical
  let : Algebra K (RatFuncInfinityIntegers K) :=
    (ratFuncInfinityConstantRingHom K).toAlgebra
  let : IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
    .of_algebraMap_eq' rfl
  let p := (ratFuncInfinityPlace K).asIdeal
  let : Finite p.ResidueField :=
    Finite.of_injective (ratFuncInfinityPlaceResidueEquiv K)
      (ratFuncInfinityPlaceResidueEquiv K).injective
  let : P.1.LiesOver p := by
    simpa [p] using Ideal.primesOver.liesOver
      (ratFuncInfinityPlace K).asIdeal P
  let := Localization.AtPrime.algebraOfLiesOver p P.1
  have : IsScalarTower (RatFuncInfinityIntegers K) (Localization.AtPrime p)
      (Localization.AtPrime P.1) := inferInstance
  let : Algebra.QuasiFiniteAt (RatFuncInfinityIntegers K) P.1 := inferInstance
  let : Module.Finite p.ResidueField P.1.ResidueField := inferInstance
  exact Module.finite_of_finite p.ResidueField

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Fintype K] in
/-- The inertia-group cardinality is the ramification index at a finite
place. -/
theorem finitePlaceInertiaGroup_card_eq_ramificationIdx [Finite K]
    (P : FiniteExtensionFinitePlace K L) :
    Nat.card (finitePlaceInertiaGroup K M L P) =
      finitePlaceRelativeRamificationIdx K M L P := by
  classical
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := finiteIntegralClosureGalAction K M L
  let := finiteIntegralClosureGalSmulComm K M L
  let : IsGaloisGroup Gal(L/M) (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ M L
  let p := finitePlaceUnder K M L P
  let : P.asIdeal.LiesOver p.asIdeal := ⟨finitePlaceUnder_asIdeal K M L P⟩
  let : Finite p.asIdeal.ResidueField :=
    finitePlaceResidueField_finite K M p
  let : PerfectField p.asIdeal.ResidueField := inferInstance
  change Nat.card (P.asIdeal.inertia Gal(L/M)) =
    P.asIdeal.ramificationIdx (RatFuncFiniteIntegralClosure K M)
  rw [Ideal.card_inertia_eq_ramificationIdxIn p.asIdeal P.asIdeal]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal P.asIdeal Gal(L/M)

omit [DecidableEq K] [DecidableEq (RatFunc K)] [Fintype K] in
/-- The decomposition-group cardinality is ramification index times inertia
degree at a finite place. -/
theorem finitePlaceDecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg [Finite K]
    (P : FiniteExtensionFinitePlace K L) :
    Nat.card (finitePlaceDecompositionGroup K M L P) =
      finitePlaceRelativeRamificationIdx K M L P *
        finitePlaceRelativeInertiaDeg K M L P := by
  classical
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := finiteIntegralClosureGalAction K M L
  let := finiteIntegralClosureGalSmulComm K M L
  let : IsGaloisGroup Gal(L/M) (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ M L
  let p := finitePlaceUnder K M L P
  let : P.asIdeal.LiesOver p.asIdeal := ⟨finitePlaceUnder_asIdeal K M L P⟩
  let : Finite p.asIdeal.ResidueField :=
    finitePlaceResidueField_finite K M p
  let : PerfectField p.asIdeal.ResidueField := inferInstance
  change Nat.card (MulAction.stabilizer Gal(L/M) P.asIdeal) =
    P.asIdeal.ramificationIdx (RatFuncFiniteIntegralClosure K M) *
      P.asIdeal.inertiaDeg (RatFuncFiniteIntegralClosure K M)
  rw [Ideal.card_stabilizer_eq p.asIdeal P.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal P.asIdeal Gal(L/M),
    Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal P.asIdeal Gal(L/M)]

omit [DecidableEq K] [Fintype K] in
/-- The inertia-group cardinality is the ramification index above infinity. -/
theorem infinityPlaceInertiaGroup_card_eq_ramificationIdx [Finite K]
    (P : FiniteExtensionInfinityPlace K L) :
    Nat.card (infinityPlaceInertiaGroup K M L P) =
      infinityPlaceRelativeRamificationIdx K M L P := by
  classical
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := infinityIntegralClosureGalAction K M L
  let := infinityIntegralClosureGalSmulComm K M L
  let : IsGaloisGroup Gal(L/M) (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ M L
  let p := infinityPlaceUnder K M L P
  let : P.1.LiesOver p.1 := ⟨infinityPlaceUnder_asIdeal K M L P⟩
  let : Finite p.1.ResidueField :=
    infinityPlaceResidueField_finite K M p
  let : PerfectField p.1.ResidueField := inferInstance
  change Nat.card (P.1.inertia Gal(L/M)) =
    P.1.ramificationIdx (RatFuncInfinityIntegralClosure K M)
  rw [Ideal.card_inertia_eq_ramificationIdxIn p.1 P.1]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx p.1 P.1 Gal(L/M)

omit [DecidableEq K] [Fintype K] in
/-- The decomposition-group cardinality is ramification index times inertia
degree above infinity. -/
theorem infinityPlaceDecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg [Finite K]
    (P : FiniteExtensionInfinityPlace K L) :
    Nat.card (infinityPlaceDecompositionGroup K M L P) =
      infinityPlaceRelativeRamificationIdx K M L P *
        infinityPlaceRelativeInertiaDeg K M L P := by
  classical
  let : Module.Finite M L :=
    Module.Finite.of_restrictScalars_finite (RatFunc K) M L
  let := infinityIntegralClosureGalAction K M L
  let := infinityIntegralClosureGalSmulComm K M L
  let : IsGaloisGroup Gal(L/M) (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ M L
  let p := infinityPlaceUnder K M L P
  let : P.1.LiesOver p.1 := ⟨infinityPlaceUnder_asIdeal K M L P⟩
  let : Finite p.1.ResidueField :=
    infinityPlaceResidueField_finite K M p
  let : PerfectField p.1.ResidueField := inferInstance
  change Nat.card (MulAction.stabilizer Gal(L/M) P.1) =
    P.1.ramificationIdx (RatFuncInfinityIntegralClosure K M) *
      P.1.inertiaDeg (RatFuncInfinityIntegralClosure K M)
  rw [Ideal.card_stabilizer_eq p.1 P.1,
    Ideal.ramificationIdxIn_eq_ramificationIdx p.1 P.1 Gal(L/M),
    Ideal.inertiaDegIn_eq_inertiaDeg p.1 P.1 Gal(L/M)]

end FiniteConstants

end Galois

end

end BGS.HasseWeil
