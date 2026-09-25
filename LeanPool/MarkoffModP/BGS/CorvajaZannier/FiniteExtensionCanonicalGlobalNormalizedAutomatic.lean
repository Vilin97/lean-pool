/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalAuxiliaryInfinityPlace
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalGlobalNormalized
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalDerivationExtension
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PerfectConstants
public import Mathlib.Tactic

/-!
# Normalized global derivations for the canonical argument

Construct the rational-function derivations and reciprocal-chart estimates used to normalize the
global canonical Wronskian argument.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section


open scoped Polynomial nonZeroDivisors
open Multiplicative WithZero IsDedekindDomain

variable (K : Type*) [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

local instance automaticInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance automaticInfinityConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable def probeRatFuncDerivation :
    Derivation K (RatFunc K) (RatFunc K) := by
  letI : IsScalarTower K K[X] (RatFunc K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization K[X]⁰
  exact formallyEtaleDerivationExtension (Polynomial.mkDerivation K 1)

@[simp] theorem probeRatFuncDerivation_algebraMap (f : K[X]) :
    probeRatFuncDerivation K (algebraMap K[X] (RatFunc K) f) =
      algebraMap K[X] (RatFunc K) f.derivative := by
  let : IsScalarTower K K[X] (RatFunc K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization K[X]⁰
  simpa only [probeRatFuncDerivation,
    Polynomial.mkDerivation_apply, smul_eq_mul, mul_one] using
      formallyEtaleDerivationExtension_algebraMap
        (T := RatFunc K) (Polynomial.mkDerivation K 1) f

example : probeRatFuncDerivation K RatFunc.X = 1 := by
  rw [← RatFunc.algebraMap_X]
  rw [probeRatFuncDerivation_algebraMap]
  simp

theorem probeRatFuncDerivation_eq (x : RatFunc K) :
    probeRatFuncDerivation K x =
      (algebraMap K[X] (RatFunc K) x.denom)⁻¹ ^ 2 *
        algebraMap K[X] (RatFunc K)
          (x.denom * x.num.derivative - x.num * x.denom.derivative) := by
  conv_lhs => rw [← RatFunc.num_div_denom x]
  rw [Derivation.leibniz_div,
    probeRatFuncDerivation_algebraMap,
    probeRatFuncDerivation_algebraMap]
  rw [map_sub, map_mul, map_mul]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]

omit [DecidableEq (RatFunc K)] in
private theorem natDegree_derivativeNumerator_le
    (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hN : q * p.derivative - p * q.derivative ≠ 0) :
    (q * p.derivative - p * q.derivative).natDegree ≤
      p.natDegree + q.natDegree - 1 := by
  have hsum : 0 < p.natDegree + q.natDegree := by
    by_contra h
    have hpdeg : p.natDegree = 0 := by omega
    have hqdeg : q.natDegree = 0 := by omega
    have hpder : p.derivative = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hpdeg,
        Polynomial.derivative_C]
    have hqder : q.derivative = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hqdeg,
        Polynomial.derivative_C]
    simp [hpder, hqder] at hN
  have hleft : (q * p.derivative).natDegree ≤
      p.natDegree + q.natDegree - 1 := by
    by_cases hpder : p.derivative = 0
    · rw [hpder, mul_zero, Polynomial.natDegree_zero]
      omega
    · have hpdeg : p.natDegree ≠ 0 := by
        intro hzero
        apply hpder
        rw [Polynomial.eq_C_of_natDegree_eq_zero hzero,
          Polynomial.derivative_C]
      rw [Polynomial.natDegree_mul hq hpder]
      have hder := Polynomial.natDegree_derivative_le p
      omega
  have hright : (p * q.derivative).natDegree ≤
      p.natDegree + q.natDegree - 1 := by
    by_cases hqder : q.derivative = 0
    · rw [hqder, mul_zero, Polynomial.natDegree_zero]
      omega
    · have hqdeg : q.natDegree ≠ 0 := by
        intro hzero
        apply hqder
        rw [Polynomial.eq_C_of_natDegree_eq_zero hzero,
          Polynomial.derivative_C]
      rw [Polynomial.natDegree_mul hp hqder]
      have hder := Polynomial.natDegree_derivative_le q
      omega
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le hleft hright)

theorem probeRatFuncDerivation_intDegree_le_sub_one
    (x : RatFunc K) (hx : x ≠ 0)
    (hDx : probeRatFuncDerivation K x ≠ 0) :
    (probeRatFuncDerivation K x).intDegree ≤ x.intDegree - 1 := by
  let N := x.denom * x.num.derivative - x.num * x.denom.derivative
  have hden : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero x.denom_ne_zero
  have hN : N ≠ 0 := by
    intro hzero
    apply hDx
    rw [probeRatFuncDerivation_eq]
    change _ * algebraMap K[X] (RatFunc K) N = 0
    rw [hzero, map_zero, mul_zero]
  have hrepr : probeRatFuncDerivation K x =
      algebraMap K[X] (RatFunc K) N /
        algebraMap K[X] (RatFunc K) (x.denom ^ 2) := by
    rw [probeRatFuncDerivation_eq, map_pow]
    change _ * algebraMap K[X] (RatFunc K) N = _
    field_simp
  rw [hrepr, RatFunc.intDegree_div
    (RatFunc.algebraMap_ne_zero hN)
    (RatFunc.algebraMap_ne_zero (pow_ne_zero 2 x.denom_ne_zero)),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
    Polynomial.natDegree_pow, RatFunc.intDegree]
  have hdegree := natDegree_derivativeNumerator_le
    K x.num x.denom (RatFunc.num_ne_zero hx) x.denom_ne_zero hN
  have hsum : 0 < x.num.natDegree + x.denom.natDegree := by
    by_contra h
    have hnumDegree : x.num.natDegree = 0 := by omega
    have hdenDegree : x.denom.natDegree = 0 := by omega
    apply hN
    change x.denom * x.num.derivative -
      x.num * x.denom.derivative = 0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hnumDegree,
      Polynomial.eq_C_of_natDegree_eq_zero hdenDegree,
      Polynomial.derivative_C, Polynomial.derivative_C]
    simp
  have hdegreeInt :
      ((x.denom * x.num.derivative -
          x.num * x.denom.derivative).natDegree : ℤ) ≤
        ((x.num.natDegree + x.denom.natDegree - 1 : ℕ) : ℤ) := by
    exact_mod_cast hdegree
  rw [Nat.cast_sub (by omega : 1 ≤
    x.num.natDegree + x.denom.natDegree)] at hdegreeInt
  simp only [N] at hdegree ⊢
  omega

noncomputable def probeRatFuncReciprocalDerivation :
    Derivation K (RatFunc K) (RatFunc K) :=
  (-RatFunc.X ^ 2 : RatFunc K) • probeRatFuncDerivation K

@[simp] theorem probeRatFuncReciprocalDerivation_apply (x : RatFunc K) :
    probeRatFuncReciprocalDerivation K x =
      -RatFunc.X ^ 2 * probeRatFuncDerivation K x := by
  simp only [probeRatFuncReciprocalDerivation, Derivation.smul_apply,
    Algebra.smul_def, Algebra.algebraMap_self_apply]

theorem probeRatFuncReciprocalDerivation_intDegree_nonpositive_of_negative
    (x : RatFunc K) (hxDegree : x.intDegree < 0) :
    (probeRatFuncReciprocalDerivation K x).intDegree ≤ 0 := by
  by_cases hEx : probeRatFuncReciprocalDerivation K x = 0
  · simp [hEx]
  have hx : x ≠ 0 := by
    intro hzero
    apply hEx
    simp [hzero]
  have hDx : probeRatFuncDerivation K x ≠ 0 := by
    intro hzero
    apply hEx
    rw [probeRatFuncReciprocalDerivation_apply, hzero, mul_zero]
  rw [probeRatFuncReciprocalDerivation_apply,
    RatFunc.intDegree_mul
      (neg_ne_zero.mpr (pow_ne_zero 2 RatFunc.X_ne_zero)) hDx,
    RatFunc.intDegree_neg,
    show (RatFunc.X ^ 2 : RatFunc K).intDegree = 2 by
      rw [pow_two,
        RatFunc.intDegree_mul RatFunc.X_ne_zero RatFunc.X_ne_zero,
        RatFunc.intDegree_X]
      norm_num]
  have hder := probeRatFuncDerivation_intDegree_le_sub_one K x hx hDx
  omega

theorem probeRatFuncReciprocalDerivation_mem_infinityIntegers
    (r : RatFuncInfinityIntegers K) :
    probeRatFuncReciprocalDerivation K (r : RatFunc K) ∈
      RatFuncInfinityIntegers K := by
  obtain ⟨c, hc⟩ :=
    ratFuncInfinityIntegers_exists_constant_mod_maximalIdeal K r
  let y : RatFuncInfinityIntegers K :=
    r - algebraMap K (RatFuncInfinityIntegers K) c
  have hyMax : y ∈ (ratFuncInfinityPlace K).asIdeal := by
    simpa only [y] using hc
  have hEr : probeRatFuncReciprocalDerivation K (r : RatFunc K) =
      probeRatFuncReciprocalDerivation K (y : RatFunc K) := by
    rw [show (y : RatFunc K) = (r : RatFunc K) - RatFunc.C c by rfl]
    rw [map_sub]
    have hconst : probeRatFuncReciprocalDerivation K (RatFunc.C c) = 0 := by
      exact (probeRatFuncReciprocalDerivation K).map_algebraMap c
    rw [hconst, sub_zero]
  rw [hEr]
  by_cases hy : (y : RatFunc K) = 0
  · simp [hy]
  have hyDegree : (y : RatFunc K).intDegree < 0 := by
    change y ∈ IsLocalRing.maximalIdeal
      (RatFuncInfinityIntegers K) at hyMax
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hyMax
    change RatFunc.inftyValuation K (y : RatFunc K) < 1 at hyMax
    rw [RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero K hy,
      ← exp_zero, exp_lt_exp] at hyMax
    exact hyMax
  by_cases hEy : probeRatFuncReciprocalDerivation K (y : RatFunc K) = 0
  · simp [hEy]
  change RatFunc.inftyValuation K
    (probeRatFuncReciprocalDerivation K (y : RatFunc K)) ≤ 1
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero K hEy,
    ← exp_zero, exp_le_exp]
  exact probeRatFuncReciprocalDerivation_intDegree_nonpositive_of_negative
    K (y : RatFunc K) hyDegree

noncomputable def probeInfinityRingDerivation :
    Derivation K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegers K) where
  toLinearMap :=
    { toFun := fun r =>
        ⟨probeRatFuncReciprocalDerivation K (r : RatFunc K),
          probeRatFuncReciprocalDerivation_mem_infinityIntegers K r⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (probeRatFuncReciprocalDerivation K)
          (x : RatFunc K) (y : RatFunc K)
      map_smul' := by
        intro c x
        apply Subtype.ext
        change probeRatFuncReciprocalDerivation K
            (algebraMap K (RatFunc K) c * (x : RatFunc K)) =
          algebraMap K (RatFunc K) c *
            probeRatFuncReciprocalDerivation K (x : RatFunc K)
        simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply] using
          (probeRatFuncReciprocalDerivation K).map_smul c (x : RatFunc K) }
  map_one_eq_zero' := by
    apply Subtype.ext
    exact (probeRatFuncReciprocalDerivation K).map_one_eq_zero
  leibniz' := by
    intro x y
    apply Subtype.ext
    exact (probeRatFuncReciprocalDerivation K).leibniz
      (x : RatFunc K) (y : RatFunc K)

@[simp] theorem probeInfinityRingDerivation_coe
    (r : RatFuncInfinityIntegers K) :
    ((probeInfinityRingDerivation K r : RatFuncInfinityIntegers K) :
      RatFunc K) = probeRatFuncReciprocalDerivation K (r : RatFunc K) :=
  rfl

section AmbientExtension

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
  [PerfectField K]

local instance probeConstantAlgebraL : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance probeConstantRatFuncTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance probeInfinityConstantLTower :
    IsScalarTower K (RatFuncInfinityIntegers K) L :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := RatFuncInfinityIntegers K) (A := L) rfl

local instance automaticInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance probeInfinityClosureConstantBaseTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := RatFuncInfinityIntegers K)
      (A := RatFuncInfinityIntegralClosure K L) rfl

local instance probeInfinityClosureToFieldTower :
    IsScalarTower (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) L :=
  IsScalarTower.of_algebraMap_eq'
    (R := RatFuncInfinityIntegers K)
      (S := RatFuncInfinityIntegralClosure K L) (A := L) rfl

local instance probeInfinityClosureConstantToFieldTower :
    IsScalarTower K (RatFuncInfinityIntegralClosure K L) L :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := RatFuncInfinityIntegralClosure K L) (A := L) rfl

local instance probeInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance probeInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance probeInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance probeInfinityClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance probeInfinityClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance probeInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance (priority := 10) probePolynomialLAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance probePolynomialRatFuncLTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq'
    (R := K[X]) (S := RatFunc K) (A := L) rfl

local instance probePolynomialConstantLTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance probeFrobeniusConstantAlgebra :
    Algebra K (frobeniusSubfield L p) :=
  (perfectConstantsToFrobeniusSubfield
    (K := K) (L := L) (p := p)).toAlgebra

local instance probeFrobeniusConstantTower :
    IsScalarTower K (frobeniusSubfield L p) L :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
theorem probe_normalizedDerivation_comp_ratFunc
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1) :
    (D.restrictScalars K).compAlgebraMap (RatFunc K) =
      (Algebra.linearMap (RatFunc K) L).compDer
        (probeRatFuncDerivation K) := by
  let : IsScalarTower K K[X] (RatFunc K) :=
    IsScalarTower.of_algebraMap_eq'
      (R := K) (S := K[X]) (A := RatFunc K) rfl
  let : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization K[X]⁰
  apply derivation_ext_of_formallyUnramified (S := K[X])
  intro f
  change (D.restrictScalars K)
      (algebraMap (RatFunc K) L
        (algebraMap K[X] (RatFunc K) f)) =
    algebraMap (RatFunc K) L
      (probeRatFuncDerivation K
        (algebraMap K[X] (RatFunc K) f))
  rw [show algebraMap (RatFunc K) L
      (algebraMap K[X] (RatFunc K) f) = algebraMap K[X] L f by
    rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) L]]
  have hpoly : (D.restrictScalars K).compAlgebraMap K[X] =
      (Algebra.linearMap K[X] L).compDer
        (Polynomial.mkDerivation K 1) := by
    apply Polynomial.derivation_ext
    calc
      ((D.restrictScalars K).compAlgebraMap K[X]) Polynomial.X =
          D (algebraMap (RatFunc K) L RatFunc.X) := by
        change D (algebraMap K[X] L Polynomial.X) = _
        rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) L,
          RatFunc.algebraMap_X]
      _ = 1 := hDX
      _ = ((Algebra.linearMap K[X] L).compDer
          (Polynomial.mkDerivation K 1)) Polynomial.X := by simp
  have hpolyf := Derivation.congr_fun hpoly f
  change (D.restrictScalars K) (algebraMap K[X] L f) =
    algebraMap K[X] L ((Polynomial.mkDerivation K 1) f) at hpolyf
  rw [hpolyf]
  change algebraMap K[X] L ((Polynomial.mkDerivation K 1) f) = _
  rw [show (probeRatFuncDerivation K)
      (algebraMap K[X] (RatFunc K) f) =
        algebraMap K[X] (RatFunc K) ((Polynomial.mkDerivation K 1) f) by
    simpa only [Polynomial.mkDerivation_apply, smul_eq_mul, mul_one] using
      probeRatFuncDerivation_algebraMap K f]
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) L]

noncomputable def probeAmbientReciprocalDerivation
    (D : Derivation (frobeniusSubfield L p) L L) :
    Derivation K L L :=
  (-(algebraMap (RatFunc K) L RatFunc.X) ^ 2) •
    D.restrictScalars K

theorem probeAmbientReciprocalDerivation_extends
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (r : RatFuncInfinityIntegers K) :
    probeAmbientReciprocalDerivation K L D
        (algebraMap (RatFuncInfinityIntegers K) L r) =
      algebraMap (RatFuncInfinityIntegers K) L
        (probeInfinityRingDerivation K r) := by
  have hcomp := Derivation.congr_fun
    (probe_normalizedDerivation_comp_ratFunc K L D hDX)
    (r : RatFunc K)
  change (D.restrictScalars K)
      (algebraMap (RatFunc K) L (r : RatFunc K)) =
    algebraMap (RatFunc K) L
      (probeRatFuncDerivation K (r : RatFunc K)) at hcomp
  rw [probeAmbientReciprocalDerivation,
    Derivation.smul_apply, Algebra.smul_def,
    Algebra.algebraMap_self_apply]
  change -(algebraMap (RatFunc K) L RatFunc.X) ^ 2 *
      (D.restrictScalars K)
        (algebraMap (RatFunc K) L (r : RatFunc K)) =
    algebraMap (RatFunc K) L
      ((probeInfinityRingDerivation K r :
        RatFuncInfinityIntegers K) : RatFunc K)
  rw [hcomp]
  change -(algebraMap (RatFunc K) L RatFunc.X) ^ 2 *
      algebraMap (RatFunc K) L
        (probeRatFuncDerivation K (r : RatFunc K)) =
    algebraMap (RatFunc K) L
      (probeRatFuncReciprocalDerivation K (r : RatFunc K))
  rw [probeRatFuncReciprocalDerivation_apply, map_mul, map_neg, map_pow]

omit [DecidableEq K] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
theorem probeAmbientReciprocalDerivation_changeParameter
    (D : Derivation (frobeniusSubfield L p) L L) :
    D.restrictScalars K =
      (-(algebraMap (RatFuncInfinityIntegers K) L
        (ratFuncInfinityUniformizer K)) ^ 2) •
        probeAmbientReciprocalDerivation K L D := by
  let sL : L := algebraMap (RatFuncInfinityIntegers K) L
    (ratFuncInfinityUniformizer K)
  let xL : L := algebraMap (RatFunc K) L RatFunc.X
  have hsx : sL * xL = 1 := by
    rw [show sL = algebraMap (RatFunc K) L (1 / RatFunc.X) by rfl,
      ← map_mul, div_mul_cancel₀ _ RatFunc.X_ne_zero, map_one]
  have hscalar : -(sL ^ 2) * -(xL ^ 2) = 1 := by
    calc
      -(sL ^ 2) * -(xL ^ 2) = (sL * xL) ^ 2 := by ring
      _ = 1 := by rw [hsx]; simp
  apply Derivation.ext
  intro z
  simp only [probeAmbientReciprocalDerivation,
    Derivation.smul_apply, Algebra.smul_def,
    Algebra.algebraMap_self_apply]
  change (D.restrictScalars K) z =
    -(sL ^ 2) * (-(xL ^ 2) * (D.restrictScalars K) z)
  rw [← mul_assoc, hscalar, one_mul]

theorem probe_exists_normalizedInfinityScaling
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (P : FiniteExtensionInfinityPlace K L) :
    ∃ c : L, c ≠ 0 ∧
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) c =
        finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) (.inr P) ∧
      ∀ r : FiniteExtensionInfinityPlaceLocalRing K L P,
        ∃ s : FiniteExtensionInfinityPlaceLocalRing K L P,
          (c • D) (finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P r) =
            finiteExtensionInfinityPlaceLocalizationToField
              (K := K) (L := L) P s := by
  let : IsScalarTower K (RatFuncInfinityIntegers K) L :=
    probeInfinityConstantLTower K L
  exact exists_finiteExtensionInfinityPlace_canonicalDifferent_scaling_certificate
    (K := K) (L := L) D (probeInfinityRingDerivation K)
      (probeAmbientReciprocalDerivation K L D)
      (probeAmbientReciprocalDerivation_extends K L D hDX)
      (probeAmbientReciprocalDerivation_changeParameter K L D) P

end AmbientExtension

section GlobalNormalized

variable [Fintype K]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

local instance globalInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance globalInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance globalInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance globalInfinityClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance globalInfinityClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance globalInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

/-- The exact exhaustive Proposition 2 gcd estimate from a normalized
Frobenius-constant derivation.  The infinity-place hypotheses of
`finiteExtensionGcdBound_of_normalizedCanonicalInfinityPlacewiseBounds` are
automatic: the reciprocal derivation at infinity gives the change of
parameter, and the different supplies the canonical clearing scalar. -/
theorem finiteExtensionGcdBound_of_normalizedCanonicalPlacewiseBounds
    (D : Derivation (frobeniusSubfield L p) L L)
    (hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1)
    (h k : ℕ) (hn : 0 < h * k + h + k) (chi : ℕ)
    (hWronskian :
      (indexedDedekindLocalWronskian D
        (auxiliaryFamilyDerivativeOrder h k)
        (auxiliaryFamily u v h k)).det ≠ 0)
    (hEuler :
      finiteExtensionDivisorDegree K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) +
        (∑ P ∈ propositionTwoExceptionalPlaces K L u v,
          finiteExtensionPlaceDegree K L P : ℤ) ≤ (chi : ℤ)) :
    (finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) : ℝ) ≤
      ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
          (finiteExtensionPositiveDegree K L v : ℝ) +
        (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
          (finiteExtensionPositiveDegree K L u : ℝ) +
        ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := by
  apply finiteExtensionGcdBound_of_normalizedCanonicalInfinityPlacewiseBounds
    K L D hDX u v hu hv huone hvone h k hn chi hWronskian hEuler
  · intro P hP hrho
    obtain ⟨c, hc, hcOrder, hScaledLocal⟩ :=
      probe_exists_normalizedInfinityScaling K L D hDX P
    have huOrder :
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) u = 0 := by
      simpa only [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using
        finiteExtensionPrincipalDivisor_u_eq_zero_outside_propositionTwoExceptionalPlaces
          K L u v (.inr P) hP
    have hvOrder :
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) v = 0 := by
      simpa only [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using
        finiteExtensionPrincipalDivisor_v_eq_zero_outside_propositionTwoExceptionalPlaces
          K L u v (.inr P) hP
    exact finiteExtensionInfinityPlace_canonicalAuxiliary_caseI_of_scaling
      (K := K) (L := L) P D c hc hcOrder hScaledLocal h k hn
        u v hu hv huone hvone huOrder hvOrder
        (by simpa only [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder]
          using hrho)
        hWronskian
  · intro P hP hrho
    obtain ⟨c, hc, hcOrder, hScaledLocal⟩ :=
      probe_exists_normalizedInfinityScaling K L D hDX P
    have huOrder :
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) u = 0 := by
      simpa only [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using
        finiteExtensionPrincipalDivisor_u_eq_zero_outside_propositionTwoExceptionalPlaces
          K L u v (.inr P) hP
    have hvOrder :
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) v = 0 := by
      simpa only [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder] using
        finiteExtensionPrincipalDivisor_v_eq_zero_outside_propositionTwoExceptionalPlaces
          K L u v (.inr P) hP
    exact finiteExtensionInfinityPlace_canonicalAuxiliary_caseII_of_scaling
      (K := K) (L := L) P D c hc hcOrder hScaledLocal h k
        u v hu hv huone hvone huOrder.ge hvOrder.ge
        (by simpa only [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder]
          using hrho)
        hWronskian
  · intro P _hP _hvP
    obtain ⟨c, hc, hcOrder, hScaledLocal⟩ :=
      probe_exists_normalizedInfinityScaling K L D hDX P
    exact finiteExtensionInfinityPlace_canonicalAuxiliary_caseIII_of_scaling
      (K := K) (L := L) P D c hc hcOrder hScaledLocal h k
        u v hu hv huone hvone hWronskian
  · intro P _hP _hvP
    obtain ⟨c, hc, hcOrder, hScaledLocal⟩ :=
      probe_exists_normalizedInfinityScaling K L D hDX P
    exact finiteExtensionInfinityPlace_canonicalAuxiliary_caseIV_of_scaling
      (K := K) (L := L) P D c hc hcOrder hScaledLocal h k
        u v hu hv huone hvone hWronskian

end GlobalNormalized

end

end BGS.CorvajaZannier
