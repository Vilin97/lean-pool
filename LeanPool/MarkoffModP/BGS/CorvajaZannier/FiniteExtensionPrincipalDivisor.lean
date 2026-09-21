/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExhaustiveProductFormula
import LeanPool.MarkoffModP.BGS.CorvajaZannier.GlobalWronskianWeightedPlaceSum
import LeanPool.MarkoffModP.BGS.CorvajaZannier.InfinityInertiaDegree
import Mathlib.Tactic

/-!
# Principal divisors on the exhaustive places of a finite function field

This file packages the finite primes and the primes above infinity of a finite
separable extension `L / K(X)` into one place type.  Principal divisors on that
type have finite support.  Their degree-weighted sum is proved to vanish by
regrouping finite primes below `K[X]` and applying the exhaustive norm product
formula.

It also provides common finite supports for arbitrary finite families,
degree-weighted product formulas on those family place types, and the positive
degree / pole-height decomposition.  Over an algebraically closed constant
field, all finite and above-infinity residue degrees are proved equal to one,
so the ordinary-order specialization has no residual place-degree hypothesis.
-/

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) principalDivisorPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance principalDivisorPolynomialScalarTower : IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

local instance principalDivisorFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance principalDivisorFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance principalDivisorPolynomialTorsionFreeTop : Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance principalDivisorFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance principalDivisorInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance principalDivisorInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance principalDivisorInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance principalDivisorInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

def finitePlaceFiberEquivPrimesOver (p : HeightOneSpectrum K[X]) :
    {q : HeightOneSpectrum (RatFuncFiniteIntegralClosure K L) //
      HeightOneSpectrum.under K[X] q = p} ≃
      p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) where
  toFun q := ⟨q.1.asIdeal, q.1.isPrime, ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal q.2
    exact h.symm⟩⟩
  invFun P := ⟨primeOverHeightOne p P, by
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def P.1 p.asIdeal).symm⟩
  left_inv q := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    rfl
  right_inv P := by
    apply Subtype.ext
    rfl

abbrev FiniteExtensionFinitePlace :=
  HeightOneSpectrum (RatFuncFiniteIntegralClosure K L)

abbrev FiniteExtensionInfinityPlace :=
  (ratFuncInfinityPlace K).asIdeal.primesOver
    (RatFuncInfinityIntegralClosure K L)

abbrev FiniteExtensionPlace :=
  FiniteExtensionFinitePlace K L ⊕ FiniteExtensionInfinityPlace K L

local instance principalDivisorInfinityPlaceFintype :
    Fintype (FiniteExtensionInfinityPlace K L) :=
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))

def finiteExtensionFinitePrincipalDivisor (x : L) :
    FiniteExtensionFinitePlace K L →₀ ℤ :=
  finitePrincipalDivisor
    ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)

@[simp] theorem finiteExtensionFinitePrincipalDivisor_apply
    (x : L) (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionFinitePrincipalDivisor K L x q =
      finitePlaceOrder q
        ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x) := by
  simp [finiteExtensionFinitePrincipalDivisor]

def finiteExtensionInfinityPrincipalDivisor (x : L) :
    FiniteExtensionInfinityPlace K L →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun P =>
    finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
      ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x))

@[simp] theorem finiteExtensionInfinityPrincipalDivisor_apply
    (x : L) (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionInfinityPrincipalDivisor K L x P =
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
        ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x) := by
  simp [finiteExtensionInfinityPrincipalDivisor]

def finiteExtensionPrincipalDivisor (x : L) :
    FiniteExtensionPlace K L →₀ ℤ :=
  (finiteExtensionFinitePrincipalDivisor K L x).sumElim
    (finiteExtensionInfinityPrincipalDivisor K L x)

@[simp] theorem finiteExtensionPrincipalDivisor_inl
    (x : L) (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPrincipalDivisor K L x (.inl q) =
      finitePlaceOrder q
        ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x) := by
  simp [finiteExtensionPrincipalDivisor]

@[simp] theorem finiteExtensionPrincipalDivisor_inr
    (x : L) (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPrincipalDivisor K L x (.inr P) =
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
        ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x) := by
  simp [finiteExtensionPrincipalDivisor]

def finiteExtensionFiniteResidueWeightedDivisor (x : L) :
    FiniteExtensionFinitePlace K L →₀ ℤ :=
  (finiteExtensionFinitePrincipalDivisor K L x).sum (fun q n =>
    Finsupp.single q ((q.asIdeal.inertiaDeg K[X] : ℤ) * n))

@[simp] theorem finiteExtensionFiniteResidueWeightedDivisor_apply
    (x : L) (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionFiniteResidueWeightedDivisor K L x q =
      (q.asIdeal.inertiaDeg K[X] : ℤ) *
        finitePlaceOrder q
          ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x) := by
  classical
  rw [finiteExtensionFiniteResidueWeightedDivisor, Finsupp.sum_apply]
  unfold Finsupp.sum
  by_cases hq : q ∈ (finiteExtensionFinitePrincipalDivisor K L x).support
  · rw [Finset.sum_eq_single q]
    · simp
    · intro b hb hbq
      simp [hbq]
    · exact fun hnot => (hnot hq).elim
  · rw [Finset.sum_eq_zero]
    · change 0 = (q.asIdeal.inertiaDeg K[X] : ℤ) *
          finiteExtensionFinitePrincipalDivisor K L x q
      rw [Finsupp.notMem_support_iff.mp hq]
      simp
    · intro b hb
      have hbq : b ≠ q := by
        intro h
        subst h
        exact hq hb
      simp [hbq]

def finiteExtensionFiniteDivisorBelow (x : L) :
    HeightOneSpectrum K[X] →₀ ℤ :=
  (finiteExtensionFiniteResidueWeightedDivisor K L x).mapDomain
    (HeightOneSpectrum.under K[X])

theorem finiteExtensionFiniteDivisorBelow_apply
    (x : L) (p : HeightOneSpectrum K[X]) :
    finiteExtensionFiniteDivisorBelow K L x p =
      ∑ P : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L),
        (P.1.inertiaDeg K[X] : ℤ) *
          finitePlaceOrder (primeOverHeightOne p P)
            ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x) := by
  classical
  let e := finitePlaceFiberEquivPrimesOver K L p
  letI : Fintype {q : FiniteExtensionFinitePlace K L //
      HeightOneSpectrum.under K[X] q = p} :=
    Fintype.ofEquiv (p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) e.symm
  let P₀ : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) :=
    Classical.choice (Set.nonempty_coe_sort.mpr
      (Set.nonempty_iff_ne_empty.mpr (by
        intro hempty
        have hncard := IsDedekindDomain.primesOver_ncard_ne_zero p.asIdeal
          (RatFuncFiniteIntegralClosure K L)
        exact hncard (by simp [hempty]))))
  let q₀ : FiniteExtensionFinitePlace K L := primeOverHeightOne p P₀
  have hq₀ : HeightOneSpectrum.under K[X] q₀ = p := by
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def P₀.1 p.asIdeal).symm
  rw [finiteExtensionFiniteDivisorBelow, show p =
    HeightOneSpectrum.under K[X] q₀ from hq₀.symm,
    Finsupp.mapDomain_apply_eq_sum]
  let D := finiteExtensionFiniteResidueWeightedDivisor K L x
  have hfilter :
      (∑ q ∈ D.support with HeightOneSpectrum.under K[X] q =
          HeightOneSpectrum.under K[X] q₀, D q) =
        ∑ q : {q : FiniteExtensionFinitePlace K L //
          HeightOneSpectrum.under K[X] q = p}, D q := by
    rw [hq₀]
    calc
      _ = ∑ q ∈ Finset.subtype
            (fun q => HeightOneSpectrum.under K[X] q = p) D.support,
            D q := (Finset.sum_subtype_eq_sum_filter (s := D.support)
              (fun q => D q)).symm
      _ = ∑ q : {q : FiniteExtensionFinitePlace K L //
          HeightOneSpectrum.under K[X] q = p}, D q := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro q _ hq
        have hnot : q.1 ∉ D.support := by
          intro hmem
          exact hq (Finset.mem_subtype.mpr hmem)
        exact Finsupp.notMem_support_iff.mp hnot
  rw [hfilter]
  rw [hq₀]
  apply Fintype.sum_equiv e
  intro q
  have hplace : primeOverHeightOne p (e q) = q.1 := by
    apply HeightOneSpectrum.ext
    rfl
  simp only [D, finiteExtensionFiniteResidueWeightedDivisor_apply]
  rw [hplace]
  rfl

theorem finiteExtensionFiniteDivisorBelow_eq_normDivisor
    (x : L) (hx : x ≠ 0) :
    finiteExtensionFiniteDivisorBelow K L x =
      ratFuncFiniteDivisor (Algebra.norm (RatFunc K) x) := by
  ext p
  rw [finiteExtensionFiniteDivisorBelow_apply K L x p,
    finitePrimesAbove_weightedOrder_eq_normOrder K L p x hx,
    ratFuncFiniteDivisor_apply]

/-- The finite-place degree sum written directly on the height-one primes of
the finite integral closure. -/
def finiteExtensionFiniteDirectDegreeSum (x : L) : ℤ :=
  (finiteExtensionFinitePrincipalDivisor K L x).sum (fun q n =>
    n * (q.asIdeal.inertiaDeg K[X] : ℤ) *
      (ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q) : ℤ))

theorem finiteExtensionFiniteDirectDegreeSum_eq_grouped
    (x : L) (hx : x ≠ 0) :
    finiteExtensionFiniteDirectDegreeSum K L x =
      finiteExtensionFinitePlaceDegreeSum K L x := by
  classical
  let D := finiteExtensionFinitePrincipalDivisor K L x
  let DW := finiteExtensionFiniteResidueWeightedDivisor K L x
  let DB := finiteExtensionFiniteDivisorBelow K L x
  calc
    finiteExtensionFiniteDirectDegreeSum K L x =
        DW.sum (fun q n => n *
          (ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q) : ℤ)) := by
      rw [finiteExtensionFiniteDirectDegreeSum]
      change D.sum _ = DW.sum _
      dsimp only [DW]
      rw [finiteExtensionFiniteResidueWeightedDivisor,
        Finsupp.sum_sum_index (fun _ => by simp)
          (fun _ _ _ => by ring)]
      apply Finsupp.sum_congr
      intro q _
      rw [Finsupp.sum_single_index]
      · ring
      · simp
    _ = DB.sum (fun p n => n * (ratFuncFinitePlaceDegree p : ℤ)) := by
      dsimp only [DB, DW]
      rw [finiteExtensionFiniteDivisorBelow]
      symm
      apply Finsupp.sum_mapDomain_index
      · intro
        simp
      · intro _ _ _
        ring
    _ = finiteExtensionFinitePlaceDegreeSum K L x := by
      dsimp only [DB]
      rw [finiteExtensionFiniteDivisorBelow_eq_normDivisor K L x hx,
        finiteExtensionFinitePlaceDegreeSum]
      apply Finsupp.sum_congr
      intro p _
      rw [ratFuncFiniteDivisor_apply,
        finitePrimesAbove_weightedOrder_eq_normOrder K L p x hx]

/-- The above-infinity order sum written as a `Finsupp.sum` on the infinity
part of the principal divisor. -/
def finiteExtensionInfinityDirectDegreeSum (x : L) : ℤ :=
  (finiteExtensionInfinityPrincipalDivisor K L x).sum (fun P n =>
    n * (P.1.inertiaDeg (RatFuncInfinityIntegers K) : ℤ))

theorem finiteExtensionInfinityDirectDegreeSum_eq_grouped (x : L) :
    finiteExtensionInfinityDirectDegreeSum K L x =
      finiteExtensionInfinityOrderSum K L x := by
  classical
  rw [finiteExtensionInfinityDirectDegreeSum,
    Finsupp.sum_fintype _ _ (fun _ => by simp),
    finiteExtensionInfinityOrderSum]
  apply Finset.sum_congr rfl
  intro P _
  rw [finiteExtensionInfinityPrincipalDivisor_apply]
  ring

/-- Degree of a place of `L`: residue degree times the degree of the place
below it.  The place at infinity of `K(X)` has degree one. -/
def finiteExtensionPlaceDegree : FiniteExtensionPlace K L → ℕ
  | .inl q => q.asIdeal.inertiaDeg K[X] *
      ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)
  | .inr P => P.1.inertiaDeg (RatFuncInfinityIntegers K)

/-- Degree of the exhaustive principal divisor, summed on the actual finite
and above-infinity places of `L`. -/
def finiteExtensionPrincipalDivisorDegreeSum (x : L) : ℤ :=
  (finiteExtensionPrincipalDivisor K L x).sum (fun v n =>
    n * (finiteExtensionPlaceDegree K L v : ℤ))

theorem finiteExtensionPrincipalDivisorDegreeSum_eq_grouped
    (x : L) (hx : x ≠ 0) :
    finiteExtensionPrincipalDivisorDegreeSum K L x =
      finiteExtensionFinitePlaceDegreeSum K L x +
        finiteExtensionInfinityOrderSum K L x := by
  rw [finiteExtensionPrincipalDivisorDegreeSum,
    finiteExtensionPrincipalDivisor, Finsupp.sum_sumElim,
    ← finiteExtensionFiniteDirectDegreeSum_eq_grouped K L x hx,
    ← finiteExtensionInfinityDirectDegreeSum_eq_grouped K L x]
  rw [finiteExtensionFiniteDirectDegreeSum,
    finiteExtensionInfinityDirectDegreeSum]
  congr 1
  · apply Finsupp.sum_congr
    intro q _
    simp only [Function.comp_apply, finiteExtensionPlaceDegree, Nat.cast_mul]
    ring

/-- Product formula on the actual place type, rather than grouped below the
base places. -/
theorem finiteExtensionPrincipalDivisorDegreeSum_eq_zero
    (x : L) (hx : x ≠ 0) :
    finiteExtensionPrincipalDivisorDegreeSum K L x = 0 := by
  rw [finiteExtensionPrincipalDivisorDegreeSum_eq_grouped K L x hx]
  exact finiteExtension_exhaustivePrincipalDivisor_productFormula K L x hx

/-- Positive degree of the principal divisor of `x`. -/
def finiteExtensionPositiveDegree (x : L) : ℕ :=
  ∑ v ∈ (finiteExtensionPrincipalDivisor K L x).support.filter
      (fun v => 0 < finiteExtensionPrincipalDivisor K L x v),
    (finiteExtensionPrincipalDivisor K L x v).toNat *
      finiteExtensionPlaceDegree K L v

/-- Pole height of `x`, i.e. the degree of the negative part of its principal
divisor. -/
def finiteExtensionHeight (x : L) : ℕ :=
  ∑ v ∈ (finiteExtensionPrincipalDivisor K L x).support.filter
      (fun v => finiteExtensionPrincipalDivisor K L x v < 0),
    (-finiteExtensionPrincipalDivisor K L x v).toNat *
      finiteExtensionPlaceDegree K L v

theorem finiteExtensionPositiveDegree_cast
    (x : L) :
    (finiteExtensionPositiveDegree K L x : ℤ) =
      ∑ v ∈ (finiteExtensionPrincipalDivisor K L x).support.filter
          (fun v => 0 < finiteExtensionPrincipalDivisor K L x v),
        finiteExtensionPrincipalDivisor K L x v *
          (finiteExtensionPlaceDegree K L v : ℤ) := by
  rw [finiteExtensionPositiveDegree, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hpos : 0 < finiteExtensionPrincipalDivisor K L x v :=
    (Finset.mem_filter.mp hv).2
  rw [Nat.cast_mul, Int.toNat_of_nonneg (le_of_lt hpos)]

theorem finiteExtensionHeight_negativeSum
    (x : L) :
    -((finiteExtensionHeight K L x : ℕ) : ℤ) =
      ∑ v ∈ (finiteExtensionPrincipalDivisor K L x).support.filter
          (fun v => finiteExtensionPrincipalDivisor K L x v < 0),
        finiteExtensionPrincipalDivisor K L x v *
          (finiteExtensionPlaceDegree K L v : ℤ) := by
  rw [finiteExtensionHeight, Nat.cast_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hneg : finiteExtensionPrincipalDivisor K L x v < 0 :=
    (Finset.mem_filter.mp hv).2
  rw [Nat.cast_mul, Int.toNat_of_nonneg (Int.neg_nonneg.mpr (le_of_lt hneg))]
  ring

theorem finiteExtensionPositiveDegree_eq_height
    (x : L) (hx : x ≠ 0) :
    finiteExtensionPositiveDegree K L x = finiteExtensionHeight K L x := by
  have hproduct := finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L x hx
  rw [finiteExtensionPrincipalDivisorDegreeSum] at hproduct
  have hsplit :
      (finiteExtensionPrincipalDivisor K L x).sum (fun v n =>
        n * (finiteExtensionPlaceDegree K L v : ℤ)) =
        (∑ v ∈ (finiteExtensionPrincipalDivisor K L x).support.filter
            (fun v => 0 < finiteExtensionPrincipalDivisor K L x v),
          finiteExtensionPrincipalDivisor K L x v *
            (finiteExtensionPlaceDegree K L v : ℤ)) +
        (∑ v ∈ (finiteExtensionPrincipalDivisor K L x).support.filter
            (fun v => finiteExtensionPrincipalDivisor K L x v < 0),
          finiteExtensionPrincipalDivisor K L x v *
            (finiteExtensionPlaceDegree K L v : ℤ)) := by
    rw [Finsupp.sum]
    rw [← Finset.sum_filter_add_sum_filter_not
      (finiteExtensionPrincipalDivisor K L x).support
      (fun v => 0 < finiteExtensionPrincipalDivisor K L x v)]
    congr 1
    have hfilters :
        (finiteExtensionPrincipalDivisor K L x).support.filter
            (fun v => ¬ 0 < finiteExtensionPrincipalDivisor K L x v) =
          (finiteExtensionPrincipalDivisor K L x).support.filter
            (fun v => finiteExtensionPrincipalDivisor K L x v < 0) := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨hv, hnotpos⟩
        have hvne : finiteExtensionPrincipalDivisor K L x v ≠ 0 :=
          Finsupp.mem_support_iff.mp hv
        exact ⟨hv, lt_of_le_of_ne (le_of_not_gt hnotpos) hvne⟩
      · intro ⟨hv, hneg⟩
        exact ⟨hv, not_lt_of_ge (le_of_lt hneg)⟩
    rw [hfilters]
  have hcast : (finiteExtensionPositiveDegree K L x : ℤ) =
      (finiteExtensionHeight K L x : ℤ) := by
    rw [finiteExtensionPositiveDegree_cast]
    rw [hsplit, ← finiteExtensionHeight_negativeSum K L x] at hproduct
    omega
  exact_mod_cast hcast

section Families

variable {A : Type*} [Fintype A]

local instance familyPlaceDecidableEq : DecidableEq (FiniteExtensionPlace K L) :=
  Classical.decEq _

/-- A single finite place set supporting the principal divisors of every
member of a finite family. -/
def finiteExtensionFamilySupport (f : A → L) :
    Finset (FiniteExtensionPlace K L) := by
  classical
  exact Finset.univ.biUnion (fun a =>
    (finiteExtensionPrincipalDivisor K L (f a)).support)

abbrev FiniteExtensionFamilyPlace (f : A → L) :=
  {v : FiniteExtensionPlace K L // v ∈ finiteExtensionFamilySupport K L f}

/-- Ordinary order of a family member on the common finite place set. -/
def finiteExtensionFamilyOrder (f : A → L) (a : A)
    (v : FiniteExtensionFamilyPlace K L f) : ℤ :=
  finiteExtensionPrincipalDivisor K L (f a) v.1

/-- Degree-weighted order.  These are the values whose unweighted sum is zero
without any algebraic-closedness assumption on the constant field. -/
def finiteExtensionFamilyWeightedOrder (f : A → L) (a : A)
    (v : FiniteExtensionFamilyPlace K L f) : ℤ :=
  finiteExtensionFamilyOrder K L f a v *
    (finiteExtensionPlaceDegree K L v.1 : ℤ)

theorem finiteExtensionPrincipalDivisor_support_subset_familySupport
    (f : A → L) (a : A) :
    (finiteExtensionPrincipalDivisor K L (f a)).support ⊆
      finiteExtensionFamilySupport K L f := by
  intro v hv
  simp only [finiteExtensionFamilySupport, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  exact ⟨a, hv⟩

theorem finiteExtensionFamilyOrder_eq_zero_of_not_mem_support
    (f : A → L) (a : A) (v : FiniteExtensionFamilyPlace K L f)
    (hv : v.1 ∉ (finiteExtensionPrincipalDivisor K L (f a)).support) :
    finiteExtensionFamilyOrder K L f a v = 0 := by
  exact Finsupp.notMem_support_iff.mp hv

/-- Product formula for any member of an arbitrary finite family, on the one
common finite place type attached to that family. -/
theorem finiteExtensionFamilyWeightedOrder_sum_eq_zero
    (f : A → L) (a : A) (ha : f a ≠ 0) :
    ∑ v : FiniteExtensionFamilyPlace K L f,
      finiteExtensionFamilyWeightedOrder K L f a v = 0 := by
  let D := finiteExtensionPrincipalDivisor K L (f a)
  let S := finiteExtensionFamilySupport K L f
  calc
    ∑ v : FiniteExtensionFamilyPlace K L f,
        finiteExtensionFamilyWeightedOrder K L f a v =
      ∑ v ∈ S, D v * (finiteExtensionPlaceDegree K L v : ℤ) := by
        symm
        apply Finset.sum_subtype S (fun _ => Iff.rfl)
    _ = ∑ v ∈ D.support,
        D v * (finiteExtensionPlaceDegree K L v : ℤ) := by
      symm
      apply Finset.sum_subset
        (finiteExtensionPrincipalDivisor_support_subset_familySupport K L f a)
      intro v _ hv
      have hzero : D v = 0 := by
        apply Finsupp.notMem_support_iff.mp
        exact hv
      simp [hzero]
    _ = finiteExtensionPrincipalDivisorDegreeSum K L (f a) := by
      rfl
    _ = 0 := finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L (f a) ha

theorem finiteExtensionFamilyWeightedPositiveSum
    (f : A → L) (a : A) :
    ∑ v ∈ Finset.univ.filter
        (fun v : FiniteExtensionFamilyPlace K L f =>
          0 < finiteExtensionFamilyOrder K L f a v),
      finiteExtensionFamilyWeightedOrder K L f a v =
        (finiteExtensionPositiveDegree K L (f a) : ℤ) := by
  let D := finiteExtensionPrincipalDivisor K L (f a)
  let S := finiteExtensionFamilySupport K L f
  rw [finiteExtensionPositiveDegree_cast K L (f a)]
  calc
    _ = ∑ v : FiniteExtensionFamilyPlace K L f,
        if 0 < finiteExtensionFamilyOrder K L f a v then
          finiteExtensionFamilyWeightedOrder K L f a v else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ v ∈ S, if 0 < D v then
        D v * (finiteExtensionPlaceDegree K L v : ℤ) else 0 := by
      symm
      apply Finset.sum_subtype S (fun _ => Iff.rfl)
    _ = ∑ v ∈ S.filter (fun v => 0 < D v),
        D v * (finiteExtensionPlaceDegree K L v : ℤ) := by
      rw [Finset.sum_filter]
    _ = ∑ v ∈ D.support.filter (fun v => 0 < D v),
        D v * (finiteExtensionPlaceDegree K L v : ℤ) := by
      symm
      apply Finset.sum_subset
      · intro v hv
        exact Finset.mem_filter.mpr ⟨
          finiteExtensionPrincipalDivisor_support_subset_familySupport K L f a
            (Finset.mem_filter.mp hv).1,
          (Finset.mem_filter.mp hv).2⟩
      · intro v hvS hvD
        have hnotSupport : v ∉ D.support := by
          intro hv
          exact hvD (Finset.mem_filter.mpr ⟨hv, (Finset.mem_filter.mp hvS).2⟩)
        have hzero := Finsupp.notMem_support_iff.mp hnotSupport
        simp [hzero]

theorem finiteExtensionFamilyWeightedNegativeSum
    (f : A → L) (a : A) :
    ∑ v ∈ Finset.univ.filter
        (fun v : FiniteExtensionFamilyPlace K L f =>
          finiteExtensionFamilyOrder K L f a v < 0),
      finiteExtensionFamilyWeightedOrder K L f a v =
        -((finiteExtensionHeight K L (f a) : ℕ) : ℤ) := by
  let D := finiteExtensionPrincipalDivisor K L (f a)
  let S := finiteExtensionFamilySupport K L f
  rw [finiteExtensionHeight_negativeSum K L (f a)]
  calc
    _ = ∑ v : FiniteExtensionFamilyPlace K L f,
        if finiteExtensionFamilyOrder K L f a v < 0 then
          finiteExtensionFamilyWeightedOrder K L f a v else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ v ∈ S, if D v < 0 then
        D v * (finiteExtensionPlaceDegree K L v : ℤ) else 0 := by
      symm
      apply Finset.sum_subtype S (fun _ => Iff.rfl)
    _ = ∑ v ∈ S.filter (fun v => D v < 0),
        D v * (finiteExtensionPlaceDegree K L v : ℤ) := by
      rw [Finset.sum_filter]
    _ = ∑ v ∈ D.support.filter (fun v => D v < 0),
        D v * (finiteExtensionPlaceDegree K L v : ℤ) := by
      symm
      apply Finset.sum_subset
      · intro v hv
        exact Finset.mem_filter.mpr ⟨
          finiteExtensionPrincipalDivisor_support_subset_familySupport K L f a
            (Finset.mem_filter.mp hv).1,
          (Finset.mem_filter.mp hv).2⟩
      · intro v hvS hvD
        have hnotSupport : v ∉ D.support := by
          intro hv
          exact hvD (Finset.mem_filter.mpr ⟨hv, (Finset.mem_filter.mp hvS).2⟩)
        have hzero := Finsupp.notMem_support_iff.mp hnotSupport
        simp [hzero]

/-- Pole height outside a caller-specified exceptional set.  This is the
quantity occurring on the right of the global Wronskian inequality. -/
def finiteExtensionFamilyOutsideHeight
    (f : A → L) (S : Finset (FiniteExtensionFamilyPlace K L f))
    (a : A) : ℕ := by
  classical
  exact ∑ v ∈ Finset.univ.filter (fun v => v ∉ S ∧
    finiteExtensionFamilyOrder K L f a v < 0),
      (finiteExtensionFamilyWeightedOrder K L f a v).natAbs

theorem finiteExtensionFamilyOutsideHeight_negativeSum
    (f : A → L) (S : Finset (FiniteExtensionFamilyPlace K L f))
    (a : A) :
    ∑ v ∈ Finset.univ.filter (fun v => v ∉ S ∧
        finiteExtensionFamilyOrder K L f a v < 0),
      finiteExtensionFamilyWeightedOrder K L f a v =
        -((finiteExtensionFamilyOutsideHeight K L f S a : ℕ) : ℤ) := by
  classical
  rw [finiteExtensionFamilyOutsideHeight, Nat.cast_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hneg : finiteExtensionFamilyOrder K L f a v < 0 :=
    (Finset.mem_filter.mp hv).2.2
  have hdegree : 0 ≤ (finiteExtensionPlaceDegree K L v.1 : ℤ) := by
    positivity
  have hweighted : finiteExtensionFamilyWeightedOrder K L f a v ≤ 0 := by
    rw [finiteExtensionFamilyWeightedOrder]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) hdegree
  rw [Int.natCast_natAbs, abs_of_nonpos hweighted]
  ring

end Families

section WeightedFamilies

variable {A : Type*} [Fintype A]

/-- The residue-degree-weighted Corvaja--Zannier summation on the exhaustive
family place type.  Unlike the later degree-one specialization, this theorem
does not assume that the constant field is algebraically closed. -/
theorem globalWronskianInequality_of_finiteExtensionWeightedPlacewiseBounds
    (f : A → L) (iU iV iRho iGrid iW : A)
    (S : Finset (FiniteExtensionFamilyPlace K L f))
    (h k n sigma chi : ℕ) (canonicalDegree : ℤ)
    (hUne : f iU ≠ 0) (hGridne : f iGrid ≠ 0)
    (hUOutside : ∀ i, i ∉ S →
      finiteExtensionFamilyOrder K L f iU i = 0)
    (hGridOutside : ∀ i, i ∉ S →
      finiteExtensionFamilyOrder K L f iGrid i = 0)
    (hVPositiveSupport : ∀ i,
      0 < finiteExtensionFamilyOrder K L f iV i → i ∈ S)
    (hCanonical :
      ∑ i, finiteExtensionFamilyWeightedOrder K L f iW i =
        (sigma : ℤ) * canonicalDegree)
    (hEuler : canonicalDegree +
      (∑ i ∈ S, finiteExtensionPlaceDegree K L i.1 : ℕ) ≤ (chi : ℤ))
    (hRhoSupport :
      -((finiteExtensionPositiveDegree K L (f iU) : ℤ) +
          (finiteExtensionPositiveDegree K L (f iV) : ℤ)) ≤
        ∑ i ∈ S, finiteExtensionFamilyWeightedOrder K L f iRho i)
    (hCaseI : ∀ i, i ∉ S →
      finiteExtensionFamilyOrder K L f iRho i < 0 →
      (n : ℤ) * finiteExtensionFamilyOrder K L f iRho i ≤
        finiteExtensionFamilyOrder K L f iW i)
    (hCaseII : ∀ i, i ∉ S →
      0 ≤ finiteExtensionFamilyOrder K L f iRho i →
      0 ≤ finiteExtensionFamilyOrder K L f iW i)
    (hCaseIII : ∀ i, i ∈ S →
      0 < finiteExtensionFamilyOrder K L f iV i →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionFamilyOrder K L f iU i +
        ((h * k : ℕ) : ℤ) * finiteExtensionFamilyOrder K L f iV i +
        (k : ℤ) * finiteExtensionFamilyOrder K L f iRho i +
        finiteExtensionFamilyOrder K L f iGrid i - (sigma : ℤ) ≤
          finiteExtensionFamilyOrder K L f iW i)
    (hCaseIV : ∀ i, i ∈ S →
      finiteExtensionFamilyOrder K L f iV i ≤ 0 →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionFamilyOrder K L f iU i +
        (k : ℤ) * finiteExtensionFamilyOrder K L f iRho i +
        finiteExtensionFamilyOrder K L f iGrid i - (sigma : ℤ) ≤
          finiteExtensionFamilyOrder K L f iW i) :
    ((h * k : ℕ) : ℤ) *
          (finiteExtensionPositiveDegree K L (f iV) : ℤ) -
        (k : ℤ) *
          ((finiteExtensionPositiveDegree K L (f iU) : ℤ) +
            (finiteExtensionPositiveDegree K L (f iV) : ℤ)) -
        (sigma : ℤ) * (chi : ℤ) ≤
      (n : ℤ) *
        (finiteExtensionFamilyOutsideHeight K L f S iRho : ℤ) := by
  classical
  have hUSum :
      ∑ i, finiteExtensionFamilyOrder K L f iU i *
        (finiteExtensionPlaceDegree K L i.1 : ℤ) = 0 := by
    simpa only [finiteExtensionFamilyWeightedOrder] using
      finiteExtensionFamilyWeightedOrder_sum_eq_zero K L f iU hUne
  have hGridSum :
      ∑ i, finiteExtensionFamilyOrder K L f iGrid i *
        (finiteExtensionPlaceDegree K L i.1 : ℤ) = 0 := by
    simpa only [finiteExtensionFamilyWeightedOrder] using
      finiteExtensionFamilyWeightedOrder_sum_eq_zero K L f iGrid hGridne
  have hPositiveAll := finiteExtensionFamilyWeightedPositiveSum K L f iV
  have hDegreeV :
      ∑ i ∈ S.filter (fun i ↦
          0 < finiteExtensionFamilyOrder K L f iV i),
        finiteExtensionFamilyOrder K L f iV i *
          (finiteExtensionPlaceDegree K L i.1 : ℤ) =
            finiteExtensionPositiveDegree K L (f iV) := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i ↦
          0 < finiteExtensionFamilyOrder K L f iV i),
          finiteExtensionFamilyWeightedOrder K L f iV i := by
        rw [show (∑ i ∈ S.filter (fun i ↦
            0 < finiteExtensionFamilyOrder K L f iV i),
              finiteExtensionFamilyOrder K L f iV i *
                (finiteExtensionPlaceDegree K L i.1 : ℤ)) =
            ∑ i ∈ S.filter (fun i ↦
              0 < finiteExtensionFamilyOrder K L f iV i),
                finiteExtensionFamilyWeightedOrder K L f iV i by
          apply Finset.sum_congr rfl
          intro i _
          rfl]
        apply Finset.sum_subset
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
            (Finset.mem_filter.mp hi).2⟩
        · intro i hi hiS
          have hpos := (Finset.mem_filter.mp hi).2
          exact False.elim
            (hiS (Finset.mem_filter.mpr ⟨hVPositiveSupport i hpos, hpos⟩))
      _ = _ := hPositiveAll
  have hOutside := finiteExtensionFamilyOutsideHeight_negativeSum K L f S iRho
  have hOutside' :
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧
          finiteExtensionFamilyOrder K L f iRho i < 0),
        finiteExtensionFamilyOrder K L f iRho i *
          (finiteExtensionPlaceDegree K L i.1 : ℤ) =
            -((finiteExtensionFamilyOutsideHeight K L f S iRho : ℕ) : ℤ) := by
    rw [show (∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧
        finiteExtensionFamilyOrder K L f iRho i < 0),
          finiteExtensionFamilyOrder K L f iRho i *
            (finiteExtensionPlaceDegree K L i.1 : ℤ)) =
        ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧
          finiteExtensionFamilyOrder K L f iRho i < 0),
            finiteExtensionFamilyWeightedOrder K L f iRho i by
      apply Finset.sum_congr rfl
      intro i _
      rfl]
    convert hOutside using 1
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro i hi
      rfl
  apply globalWronskianInequality_of_weightedPlacewiseBounds
    (fun i ↦ finiteExtensionPlaceDegree K L i.1) S
    (finiteExtensionFamilyOrder K L f iU)
    (finiteExtensionFamilyOrder K L f iV)
    (finiteExtensionFamilyOrder K L f iRho)
    (finiteExtensionFamilyOrder K L f iGrid)
    (finiteExtensionFamilyOrder K L f iW)
    h k n sigma
    (finiteExtensionPositiveDegree K L (f iU))
    (finiteExtensionPositiveDegree K L (f iV))
    chi (finiteExtensionFamilyOutsideHeight K L f S iRho)
    canonicalDegree
  · exact hUOutside
  · exact hGridOutside
  · exact hUSum
  · exact hGridSum
  · exact hDegreeV
  · exact hOutside'
  · simpa only [finiteExtensionFamilyWeightedOrder] using hCanonical
  · exact hEuler
  · simpa only [finiteExtensionFamilyWeightedOrder] using hRhoSupport
  · exact hCaseI
  · exact hCaseII
  · exact hCaseIII
  · exact hCaseIV

end WeightedFamilies

section AlgebraicallyClosedProbe

variable [IsAlgClosed K]

local instance finiteIntegralClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X] (RatFuncFiniteIntegralClosure K L)).comp
    (algebraMap K K[X]))

local instance finiteIntegralClosureConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  .of_algebraMap_eq' rfl

noncomputable def ratFuncFinitePlaceResidueEquiv (p : HeightOneSpectrum K[X]) :
    p.asIdeal.ResidueField ≃ₐ[K] K := by
  let r := finitePlaceNormalizedPrime p
  have hr0 : (r : K[X]) ≠ 0 := r.property.1.ne_zero
  have hrmonic : (r : K[X]).Monic :=
    (Polynomial.normalize_eq_self_iff_monic hr0).mp r.property.2
  have hrdegree : (r : K[X]).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K r.property.1.irreducible
  let c : K := -(r : K[X]).coeff 0
  have hrlinear : (r : K[X]) = Polynomial.X - Polynomial.C c := by
    rw [Polynomial.eq_X_add_C_of_degree_eq_one hrdegree, hrmonic.leadingCoeff]
    simp [c]
  have hpideal : p.asIdeal = Ideal.span
      ({Polynomial.X - Polynomial.C c} : Set K[X]) := by
    calc
      p.asIdeal = (normalizedPrimeFinitePlace (K := K) r).asIdeal := by
        rw [normalizedPrimeFinitePlace_finitePlaceNormalizedPrime]
      _ = Ideal.span ({(r : K[X])} : Set K[X]) := rfl
      _ = Ideal.span ({Polynomial.X - Polynomial.C c} : Set K[X]) := by
        rw [hrlinear]
  let eQuot : (K[X] ⧸ p.asIdeal) ≃ₐ[K] K :=
    (Ideal.quotientEquivAlgOfEq K hpideal).trans
      (Polynomial.quotientSpanXSubCAlgEquiv c)
  let eResidue : (K[X] ⧸ p.asIdeal) ≃ₐ[K] p.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K (K[X] ⧸ p.asIdeal) p.asIdeal.ResidueField)
      p.asIdeal.bijective_algebraMap_quotient_residueField
  exact eResidue.symm.trans eQuot

theorem ratFuncFinitePlaceDegree_eq_one (p : HeightOneSpectrum K[X]) :
    ratFuncFinitePlaceDegree p = 1 := by
  let r := finitePlaceNormalizedPrime p
  have hrdegree : (r : K[X]).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K r.property.1.irreducible
  rw [ratFuncFinitePlaceDegree]
  exact Polynomial.natDegree_eq_of_degree_eq_some hrdegree

theorem finiteExtensionFinitePlace_inertiaDeg_eq_one
    (q : FiniteExtensionFinitePlace K L) :
    q.asIdeal.inertiaDeg K[X] = 1 := by
  let p := HeightOneSpectrum.under K[X] q
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : Localization.AtPrime.IsLiesOverAlgebra p.asIdeal q.asIdeal :=
    ⟨rfl⟩
  letI : IsAlgClosed p.asIdeal.ResidueField :=
    IsAlgClosed.of_ringEquiv K p.asIdeal.ResidueField
      (ratFuncFinitePlaceResidueEquiv K p).symm.toRingEquiv
  letI : Algebra.QuasiFiniteAt K[X] q.asIdeal := inferInstance
  letI : Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    inferInstance
  letI : Algebra.IsIntegral p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    Algebra.IsIntegral.of_finite _ _
  rw [Ideal.inertiaDeg_eq p.asIdeal q.asIdeal,
    Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Over an algebraically closed constant field, all actual places of the
extension have degree one. -/
theorem finiteExtensionPlaceDegree_eq_one
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPlaceDegree K L v = 1 := by
  cases v with
  | inl q =>
      simp [finiteExtensionPlaceDegree,
        finiteExtensionFinitePlace_inertiaDeg_eq_one K L q,
        ratFuncFinitePlaceDegree_eq_one K
          (HeightOneSpectrum.under K[X] q)]
  | inr P =>
      simpa [finiteExtensionPlaceDegree] using
        finiteExtensionInfinityPlace_inertiaDeg_eq_one K L P

section AlgebraicallyClosedFamilies

variable {A : Type*} [Fintype A]

/-- Ordinary (unweighted) product formula on the common family place type. -/
theorem finiteExtensionFamilyOrder_sum_eq_zero
    (f : A → L) (a : A) (ha : f a ≠ 0) :
    ∑ v : FiniteExtensionFamilyPlace K L f,
      finiteExtensionFamilyOrder K L f a v = 0 := by
  have hweighted := finiteExtensionFamilyWeightedOrder_sum_eq_zero K L f a ha
  simpa only [finiteExtensionFamilyWeightedOrder,
    finiteExtensionPlaceDegree_eq_one K L,
    Int.ofNat_eq_natCast, Nat.cast_one, mul_one] using hweighted

theorem finiteExtensionFamilyWeightedOrder_eq_order
    (f : A → L) (a : A) (v : FiniteExtensionFamilyPlace K L f) :
    finiteExtensionFamilyWeightedOrder K L f a v =
      finiteExtensionFamilyOrder K L f a v := by
  rw [finiteExtensionFamilyWeightedOrder,
    finiteExtensionPlaceDegree_eq_one K L]
  simp

/-- The global Corvaja--Zannier summation specialized to the exhaustive family
place type.  Principal-divisor sums, the positive degree of `V`, and the pole
height of `rho` outside `S` are discharged by this file.  The exceptional-set
support conditions, canonical-divisor identity and bound, rho support bound,
and the four local Wronskian estimates remain explicit inputs. -/
theorem globalWronskianInequality_of_finiteExtensionPlacewiseBounds
    (f : A → L) (iU iV iRho iGrid iW : A)
    (S : Finset (FiniteExtensionFamilyPlace K L f))
    (h k n sigma chi : ℕ) (canonicalDegree : ℤ)
    (hUne : f iU ≠ 0) (hGridne : f iGrid ≠ 0)
    (hUOutside : ∀ i, i ∉ S →
      finiteExtensionFamilyOrder K L f iU i = 0)
    (hGridOutside : ∀ i, i ∉ S →
      finiteExtensionFamilyOrder K L f iGrid i = 0)
    (hVPositiveSupport : ∀ i,
      0 < finiteExtensionFamilyOrder K L f iV i → i ∈ S)
    (hCanonical :
      ∑ i, finiteExtensionFamilyOrder K L f iW i =
        (sigma : ℤ) * canonicalDegree)
    (hEuler : canonicalDegree + S.card ≤ (chi : ℤ))
    (hRhoSupport :
      -((finiteExtensionPositiveDegree K L (f iU) : ℤ) +
          (finiteExtensionPositiveDegree K L (f iV) : ℤ)) ≤
        ∑ i ∈ S, finiteExtensionFamilyOrder K L f iRho i)
    (hCaseI : ∀ i, i ∉ S →
      finiteExtensionFamilyOrder K L f iRho i < 0 →
      (n : ℤ) * finiteExtensionFamilyOrder K L f iRho i ≤
        finiteExtensionFamilyOrder K L f iW i)
    (hCaseII : ∀ i, i ∉ S →
      0 ≤ finiteExtensionFamilyOrder K L f iRho i →
      0 ≤ finiteExtensionFamilyOrder K L f iW i)
    (hCaseIII : ∀ i, i ∈ S →
      0 < finiteExtensionFamilyOrder K L f iV i →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionFamilyOrder K L f iU i +
        ((h * k : ℕ) : ℤ) * finiteExtensionFamilyOrder K L f iV i +
        (k : ℤ) * finiteExtensionFamilyOrder K L f iRho i +
        finiteExtensionFamilyOrder K L f iGrid i - (sigma : ℤ) ≤
          finiteExtensionFamilyOrder K L f iW i)
    (hCaseIV : ∀ i, i ∈ S →
      finiteExtensionFamilyOrder K L f iV i ≤ 0 →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionFamilyOrder K L f iU i +
        (k : ℤ) * finiteExtensionFamilyOrder K L f iRho i +
        finiteExtensionFamilyOrder K L f iGrid i - (sigma : ℤ) ≤
          finiteExtensionFamilyOrder K L f iW i) :
    ((h * k : ℕ) : ℤ) *
          (finiteExtensionPositiveDegree K L (f iV) : ℤ) -
        (k : ℤ) *
          ((finiteExtensionPositiveDegree K L (f iU) : ℤ) +
            (finiteExtensionPositiveDegree K L (f iV) : ℤ)) -
        (sigma : ℤ) * (chi : ℤ) ≤
      (n : ℤ) *
        (finiteExtensionFamilyOutsideHeight K L f S iRho : ℤ) := by
  classical
  have hUSum : ∑ i, finiteExtensionFamilyOrder K L f iU i = 0 :=
    finiteExtensionFamilyOrder_sum_eq_zero K L f iU hUne
  have hGridSum : ∑ i, finiteExtensionFamilyOrder K L f iGrid i = 0 :=
    finiteExtensionFamilyOrder_sum_eq_zero K L f iGrid hGridne
  have hPositiveAll := finiteExtensionFamilyWeightedPositiveSum K L f iV
  simp_rw [finiteExtensionFamilyWeightedOrder_eq_order K L f iV] at hPositiveAll
  have hDegreeV :
      ∑ i ∈ S.filter (fun i =>
          0 < finiteExtensionFamilyOrder K L f iV i),
        finiteExtensionFamilyOrder K L f iV i =
          finiteExtensionPositiveDegree K L (f iV) := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i =>
          0 < finiteExtensionFamilyOrder K L f iV i),
          finiteExtensionFamilyOrder K L f iV i := by
        apply Finset.sum_subset
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
            (Finset.mem_filter.mp hi).2⟩
        · intro i hi hiS
          have hpos := (Finset.mem_filter.mp hi).2
          exact False.elim
            (hiS (Finset.mem_filter.mpr ⟨hVPositiveSupport i hpos, hpos⟩))
      _ = _ := hPositiveAll
  have hOutside := finiteExtensionFamilyOutsideHeight_negativeSum K L f S iRho
  simp_rw [finiteExtensionFamilyWeightedOrder_eq_order K L f iRho] at hOutside
  have hOutside' :
      ∑ i ∈ Finset.univ.filter (fun i => i ∉ S ∧
          finiteExtensionFamilyOrder K L f iRho i < 0),
        finiteExtensionFamilyOrder K L f iRho i =
          -((finiteExtensionFamilyOutsideHeight K L f S iRho : ℕ) : ℤ) := by
    convert hOutside using 1
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro i hi
      rfl
  exact globalWronskianInequality_of_placewiseBounds
    S
    (finiteExtensionFamilyOrder K L f iU)
    (finiteExtensionFamilyOrder K L f iV)
    (finiteExtensionFamilyOrder K L f iRho)
    (finiteExtensionFamilyOrder K L f iGrid)
    (finiteExtensionFamilyOrder K L f iW)
    h k n sigma
    (finiteExtensionPositiveDegree K L (f iU))
    (finiteExtensionPositiveDegree K L (f iV))
    chi (finiteExtensionFamilyOutsideHeight K L f S iRho)
    canonicalDegree hUOutside hGridOutside hUSum hGridSum hDegreeV
    hOutside' hCanonical hEuler hRhoSupport hCaseI hCaseII hCaseIII hCaseIV

end AlgebraicallyClosedFamilies

end AlgebraicallyClosedProbe

end
end BGS.CorvajaZannier
