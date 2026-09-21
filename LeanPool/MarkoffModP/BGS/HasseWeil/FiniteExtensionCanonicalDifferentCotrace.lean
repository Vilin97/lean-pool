/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentCanonicalityCriterion
import LeanPool.MarkoffModP.BGS.HasseWeil.DedekindDifferentLocalTrace
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncCanonicalInfinityDivisor
import LeanPool.MarkoffModP.BGS.HasseWeil.LinearFunctionalGluing

/-!
# Cotrace construction for the finite-extension canonical different

This file constructs a surjective cotrace on fiber-constant adeles and uses
the trace codifferent bounds to build a nonzero Weil differential whose
maximal vanishing divisor contains the explicit finite-extension different.
Nothing in this file is an assumption.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain Multiplicative WithZero
open scoped Polynomial nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- The exhaustive rational-function places used as the base of the finite
extension place map. -/
abbrev RatFuncExhaustivePlace :=
  HeightOneSpectrum K[X] ⊕ HeightOneSpectrum (RatFuncInfinityIntegers K)

/-- The polynomial ring is the integral closure of itself in its fraction
field, so its height-one primes are exactly the finite chart places of
`K(X)`. -/
def ratFuncFiniteBaseRingEquivChart :
    K[X] ≃+* FunctionField.ringOfIntegers K (RatFunc K) :=
  (IsIntegralClosure.equiv K[X] K[X] (RatFunc K)
    (FunctionField.ringOfIntegers K (RatFunc K))).toRingEquiv

@[simp]
theorem ratFuncFiniteBaseRingEquivChart_algebraMap
    (r : K[X]) :
    algebraMap (FunctionField.ringOfIntegers K (RatFunc K))
        (RatFunc K) (ratFuncFiniteBaseRingEquivChart K r) =
      algebraMap K[X] (RatFunc K) r :=
  IsIntegralClosure.algebraMap_equiv K[X] K[X]
    (RatFunc K) (FunctionField.ringOfIntegers K (RatFunc K)) r

/-- The BGS infinity valuation ring and the chart infinity integral closure
inside `K(X)` are canonically equivalent. -/
def ratFuncInfinityBaseRingEquivChart :
    RatFuncInfinityIntegers K ≃+*
      FunctionField.Chart.infiniteIntegers K (RatFunc K) :=
  (finiteExtensionInfinityBaseRingEquiv K).trans
    (IsIntegralClosure.equiv
      (FunctionField.Chart.inftyValuationSubring K)
      (FunctionField.Chart.inftyValuationSubring K) (RatFunc K)
      (FunctionField.Chart.infiniteIntegers K (RatFunc K))).toRingEquiv

@[simp]
theorem ratFuncInfinityBaseRingEquivChart_algebraMap
    (r : RatFuncInfinityIntegers K) :
    algebraMap (FunctionField.Chart.infiniteIntegers K (RatFunc K))
        (RatFunc K) (ratFuncInfinityBaseRingEquivChart K r) =
      algebraMap (RatFuncInfinityIntegers K) (RatFunc K) r := by
  calc
    _ = algebraMap (FunctionField.Chart.inftyValuationSubring K)
        (RatFunc K) (finiteExtensionInfinityBaseRingEquiv K r) :=
      IsIntegralClosure.algebraMap_equiv
        (FunctionField.Chart.inftyValuationSubring K)
        (FunctionField.Chart.inftyValuationSubring K) (RatFunc K)
        (FunctionField.Chart.infiniteIntegers K (RatFunc K))
        (finiteExtensionInfinityBaseRingEquiv K r)
    _ = (r : RatFunc K) := rfl
    _ = algebraMap (RatFuncInfinityIntegers K) (RatFunc K) r := rfl

/-- Reindex the exhaustive BGS rational-function places as chart places. -/
def ratFuncExhaustivePlaceEquivChart :
    RatFuncExhaustivePlace K ≃ FunctionField.Chart.PlaceA K (RatFunc K) :=
  Equiv.sumCongr
    (HeightOneSpectrum.equivOfRingEquiv
      (ratFuncFiniteBaseRingEquivChart K))
    (HeightOneSpectrum.equivOfRingEquiv
      (ratFuncInfinityBaseRingEquivChart K))

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance cotraceConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance cotraceConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) cotracePolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance cotracePolynomialTower : IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance cotraceConstantPolynomialTower : IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance cotraceFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.finite K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance cotraceFiniteClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance cotraceFiniteBaseTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance cotraceFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance cotraceInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance cotraceInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance cotraceInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance cotraceInfinityClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance cotraceInfinityClosureIsDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance cotraceInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

/-- Transport the condition of belonging to a height-one valuation ring
across an identity-on-fraction-field ring equivalence. -/
theorem heightOneValuation_le_one_of_ringEquiv
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F]
    [IsFractionRing S F] [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm)
    {x : F} (hx : q.valuation F x ≤ 1) : q'.valuation F x ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := q.exists_primeCompl_mul_eq_of_integer x hx
  have hd' : e d.1 ∉ q'.asIdeal := by
    intro hmem
    have hd : (d.1 : R) ∉ q.asIdeal := d.2
    apply hd
    rw [hideal] at hmem
    change e.symm (e d.1) ∈ q.asIdeal at hmem
    simpa using hmem
  have hnd' :
      x * algebraMap S F (e d.1) = algebraMap S F (e n) := by
    simpa only [halg] using hnd
  have hval := congrArg (q'.valuation F) hnd'
  rw [map_mul, q'.valuation_eq_one_iff_notMem (K := F).2 hd'] at hval
  simp only [mul_one] at hval
  rw [hval]
  exact q'.valuation_le_one (K := F) (e n)

/-- Identity-on-fraction-field equivalences identify the valuation rings of
corresponding height-one primes. -/
theorem heightOneValuation_isEquiv_of_ringEquiv
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F]
    [IsFractionRing S F] [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm) :
    (q.valuation F).IsEquiv (q'.valuation F) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  constructor
  · exact heightOneValuation_le_one_of_ringEquiv
      e halg q q' hideal
  · intro hx
    have halg' : ∀ s : S,
        algebraMap R F (e.symm s) = algebraMap S F s := by
      intro s
      rw [← halg (e.symm s), e.apply_symm_apply]
    have hideal' : q.asIdeal = q'.asIdeal.comap e := by
      ext r
      rw [Ideal.mem_comap, hideal, Ideal.mem_comap]
      simp
    exact heightOneValuation_le_one_of_ringEquiv
      e.symm halg' q' q hideal' hx

/-- Equivalent surjective valuations with value group `ℤᵐ⁰` have the same
normalization. -/
theorem normalizedIntValuation_eq_of_isEquiv_of_surjective
    {F : Type*} [Field F] (v w : Valuation F ℤᵐ⁰)
    (hvw : v.IsEquiv w) (hv : Function.Surjective v)
    (hw : Function.Surjective w) : v = w := by
  obtain ⟨π, hvπ⟩ := hv (WithZero.exp (-1 : ℤ))
  have hπ : π ≠ 0 := by
    apply (Valuation.ne_zero_iff v).mp
    rw [hvπ]
    exact WithZero.exp_ne_zero
  have hwπ0 : w π ≠ 0 :=
    (hvw.eq_zero.ne).mp ((Valuation.ne_zero_iff v).2 hπ)
  let m : ℤ := -WithZero.log (w π)
  have hmpos : 0 < m := by
    have hvπlt : v π < 1 := by
      rw [hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hwπlt : w π < 1 := hvw.lt_one_iff_lt_one.mp hvπlt
    have hlog : WithZero.log (w π) < 0 := by
      rw [← WithZero.log_one]
      exact (WithZero.log_lt_log hwπ0 one_ne_zero).2 hwπlt
    dsimp only [m]
    omega
  have hformula (x : F) (hx : x ≠ 0) :
      w x = WithZero.exp (m * WithZero.log (v x)) := by
    have hvx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
    let n : ℤ := WithZero.log (v x)
    have hvpow : v (π ^ (-n)) = v x := by
      rw [map_zpow₀, hvπ, ← WithZero.exp_zsmul]
      rw [← WithZero.exp_log hvx0]
      congr 1
      dsimp only [n]
      simp
    have hwpow : w (π ^ (-n)) = w x := hvw.eq_iff.mp hvpow
    calc
      w x = w (π ^ (-n)) := hwpow.symm
      _ = (w π) ^ (-n) := by rw [map_zpow₀]
      _ = WithZero.exp ((-n) • WithZero.log (w π)) := by
        rw [WithZero.exp_zsmul, WithZero.exp_log hwπ0]
      _ = WithZero.exp (m * WithZero.log (v x)) := by
        congr 1
        dsimp only [m, n]
        ring
  obtain ⟨y, hwy⟩ := hw (WithZero.exp (1 : ℤ))
  have hy : y ≠ 0 := by
    apply (Valuation.ne_zero_iff w).mp
    rw [hwy]
    exact WithZero.exp_ne_zero
  have hm : m * WithZero.log (v y) = 1 := by
    apply WithZero.exp_injective
    rw [← hformula y hy, hwy]
  have hm1 : m = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hm with h | h
    · exact h.1
    · omega
  ext x
  by_cases hx : x = 0
  · subst x
    simp
  · rw [hformula x hx, hm1, one_mul,
      WithZero.exp_log ((Valuation.ne_zero_iff v).2 hx)]

/-- Corresponding height-one primes have exactly the same normalized
`ℤᵐ⁰`-valued valuation under an identity-on-fraction-field equivalence. -/
theorem heightOneValuation_eq_of_ringEquiv
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F]
    [IsFractionRing S F] [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm) :
    q.valuation F = q'.valuation F := by
  apply normalizedIntValuation_eq_of_isEquiv_of_surjective
  · exact heightOneValuation_isEquiv_of_ringEquiv e halg q q' hideal
  · exact HeightOneSpectrum.valuation_surjective (K := F) q
  · exact HeightOneSpectrum.valuation_surjective (K := F) q'

/-- Integrality at a height-one prime pulls up along a finite extension to
every prime above it. -/
theorem heightOneValuation_algebraMap_le_one_of_under
    {R S F E : Type*} [CommRing R] [CommRing S] [Field F] [Field E]
    [Algebra R S] [Algebra R F] [Algebra R E] [Algebra S E]
    [Algebra F E] [IsScalarTower R S E] [IsScalarTower R F E]
    [Algebra.IsIntegral R S]
    [IsFractionRing R F] [IsFractionRing S E]
    [IsDedekindDomain R] [IsDedekindDomain S]
    (q : HeightOneSpectrum S) (p : HeightOneSpectrum R)
    (hunder : q.under R = p) {x : F}
    (hx : p.valuation F x ≤ 1) :
    q.valuation E (algebraMap F E x) ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer x hx
  have hunderIdeal : q.asIdeal.under R = p.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal hunder
  have hdq : algebraMap R S d.1 ∉ q.asIdeal := by
    intro hdq
    have hdUnder : (d.1 : R) ∈ q.asIdeal.under R := hdq
    have hdP : (d.1 : R) ∈ p.asIdeal := by
      simpa only [hunderIdeal] using hdUnder
    exact d.2 hdP
  have hndE := congrArg (algebraMap F E) hnd
  have hndE' : algebraMap F E x * algebraMap S E (algebraMap R S d.1) =
      algebraMap S E (algebraMap R S n) := by
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply R F E,
      ← IsScalarTower.algebraMap_apply R S E] using hndE
  have hval := congrArg (q.valuation E) hndE'
  have hdval : q.valuation E (algebraMap S E (algebraMap R S d.1)) = 1 :=
    q.valuation_eq_one_iff_notMem (K := E).2 hdq
  rw [map_mul, hdval, mul_one] at hval
  rw [hval]
  exact q.valuation_le_one (K := E) (algebraMap R S n)

/-- Integrality at a height-one place is the nonnegativity of its principal
fractional-ideal count. -/
theorem zero_le_count_spanSingleton_of_valuation_le_one
    {R F : Type*} [CommRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] [IsDedekindDomain R]
    (q : HeightOneSpectrum R) {x : F} (hx : x ≠ 0)
    (hval : q.valuation F x ≤ 1) :
    0 ≤ FractionalIdeal.count F q
      (FractionalIdeal.spanSingleton R⁰ x) := by
  have hvaluation := FractionalIdeal.valuation_eq_exp_neg_count
    q (Units.mk0 x hx)
  have hval' : q.valuation F (↑(Units.mk0 x hx) : F) ≤ 1 := by
    simpa using hval
  rw [hvaluation, ← WithZero.exp_zero] at hval'
  exact neg_nonpos.mp (WithZero.exp_le_exp.mp hval')

/-- Forget an extension place down to its rational-function place. -/
def finiteExtensionUnderPlace :
    FiniteExtensionPlace K L → RatFuncExhaustivePlace K
  | .inl q => .inl (q.under K[X])
  | .inr _ => .inr (ratFuncInfinityPlace K)

/-- Every rational-function place has an extension place above it. -/
theorem finiteExtensionUnderPlace_surjective :
    Function.Surjective (finiteExtensionUnderPlace K L) := by
  intro p
  rcases p with p | p
  · obtain ⟨P, hP, hunder⟩ :=
      p.asIdeal.exists_ideal_over_prime_of_isIntegral_of_isDomain
        (S := RatFuncFiniteIntegralClosure K L) (by simp)
    have hPbot : P ≠ ⊥ := by
      intro hbot
      have hpbot : p.asIdeal = ⊥ := by
        calc
          p.asIdeal = Ideal.comap
              (algebraMap K[X] (RatFuncFiniteIntegralClosure K L)) P :=
            hunder.symm
          _ = Ideal.comap
              (algebraMap K[X] (RatFuncFiniteIntegralClosure K L)) ⊥ := by
            rw [hbot]
          _ = ⊥ := Ideal.comap_bot_of_injective _
            (FaithfulSMul.algebraMap_injective K[X]
              (RatFuncFiniteIntegralClosure K L))
      exact p.ne_bot hpbot
    let q : HeightOneSpectrum (RatFuncFiniteIntegralClosure K L) :=
      ⟨P, hP, hPbot⟩
    refine ⟨.inl q, ?_⟩
    apply congrArg Sum.inl
    apply HeightOneSpectrum.ext
    exact hunder
  · have hpEq : p = ratFuncInfinityPlace K := by
      apply HeightOneSpectrum.ext
      exact (IsLocalRing.eq_maximalIdeal
        (p.isPrime.isMaximal p.ne_bot)).trans
          (IsLocalRing.eq_maximalIdeal
            ((ratFuncInfinityPlace K).isPrime.isMaximal
              (ratFuncInfinityPlace K).ne_bot)).symm
    obtain ⟨P, hPmax, hPover⟩ :=
      (ratFuncInfinityPlace K).asIdeal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := RatFuncInfinityIntegralClosure K L)
    let P' : FiniteExtensionInfinityPlace K L :=
      ⟨P, hPmax.isPrime, hPover⟩
    refine ⟨.inr P', ?_⟩
    simp only [finiteExtensionUnderPlace]
    exact congrArg Sum.inr hpEq.symm

/-- Every fiber of the exhaustive place map is finite. -/
theorem finiteExtensionUnderPlace_finite_preimage_singleton
    (p : RatFuncExhaustivePlace K) :
    Set.Finite ((finiteExtensionUnderPlace K L) ⁻¹' {p}) := by
  rcases p with p | p
  · have hfiber : Set.Finite {q : FiniteExtensionFinitePlace K L |
        q.under K[X] = p} := by
      rw [← Set.finite_coe_iff]
      letI : Finite
          (p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) :=
        Set.finite_coe_iff.mpr
          (IsDedekindDomain.primesOver_finite p.asIdeal
            (RatFuncFiniteIntegralClosure K L))
      exact Finite.of_equiv
        (p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L))
        (finitePlaceFiberEquivPrimesOver K L p).symm
    refine (hfiber.image (fun q =>
      (Sum.inl q : FiniteExtensionPlace K L))).subset ?_
    intro q hq
    rcases q with q | q
    · refine ⟨q, ?_, rfl⟩
      change q.under K[X] = p
      simpa only [Set.mem_preimage, Set.mem_singleton_iff,
        finiteExtensionUnderPlace, Sum.inl.injEq] using hq
    · simp only [Set.mem_preimage, Set.mem_singleton_iff,
        finiteExtensionUnderPlace, Sum.inr.injEq, reduceCtorEq] at hq
  · letI : Finite (FiniteExtensionInfinityPlace K L) :=
      Set.finite_coe_iff.mpr
        (IsDedekindDomain.primesOver_finite
          (ratFuncInfinityPlace K).asIdeal
          (RatFuncInfinityIntegralClosure K L))
    refine (Set.finite_range (fun q : FiniteExtensionInfinityPlace K L =>
      (Sum.inr q : FiniteExtensionPlace K L))).subset ?_
    intro q hq
    rcases q with q | q
    · simp only [Set.mem_preimage, Set.mem_singleton_iff,
        finiteExtensionUnderPlace, Sum.inl.injEq, reduceCtorEq] at hq
    · exact Set.mem_range_self q

/-- Pullback along the exhaustive place map preserves cofinite eventual
properties. -/
theorem finiteExtensionUnderPlace_tendstoCofinite :
    Filter.TendstoCofinite (finiteExtensionUnderPlace K L) :=
  (Filter.tendstoCofinite_iff_finite_preimage_singleton
    (finiteExtensionUnderPlace K L)).mpr
      (finiteExtensionUnderPlace_finite_preimage_singleton K L)

/-- The place below a top chart place, expressed in the base chart. -/
def finiteExtensionUnderPlaceChart
    (q : FunctionField.Chart.PlaceA K L) :
    FunctionField.Chart.PlaceA K (RatFunc K) :=
  ratFuncExhaustivePlaceEquivChart K
    (finiteExtensionUnderPlace K L
      ((finiteExtensionPlaceEquivChart K L).symm q))

/-- Every rational-function chart place has an upstairs chart place. -/
theorem finiteExtensionUnderPlaceChart_surjective :
    Function.Surjective (finiteExtensionUnderPlaceChart K L) := by
  intro p
  let p' := (ratFuncExhaustivePlaceEquivChart K).symm p
  obtain ⟨q, hq⟩ := finiteExtensionUnderPlace_surjective K L p'
  refine ⟨finiteExtensionPlaceEquivChart K L q, ?_⟩
  simp only [finiteExtensionUnderPlaceChart, Equiv.symm_apply_apply, hq, p']
  exact (ratFuncExhaustivePlaceEquivChart K).apply_symm_apply p

/-- Pullback along the chart place map preserves cofinite eventual
properties. -/
theorem finiteExtensionUnderPlaceChart_tendstoCofinite :
    Filter.TendstoCofinite (finiteExtensionUnderPlaceChart K L) := by
  letI : Filter.TendstoCofinite (finiteExtensionUnderPlace K L) :=
    finiteExtensionUnderPlace_tendstoCofinite K L
  change Filter.TendstoCofinite
    ((ratFuncExhaustivePlaceEquivChart K) ∘
      (finiteExtensionUnderPlace K L) ∘
        (finiteExtensionPlaceEquivChart K L).symm)
  infer_instance

/-- A base element integral at a chart place remains integral at every
upstairs chart place above it. -/
theorem finiteExtension_placeValuation_algebraMap_le_one
    (q : FunctionField.Chart.PlaceA K L) {x : RatFunc K}
    (hx : FunctionField.Chart.placeValuation K (RatFunc K)
      (finiteExtensionUnderPlaceChart K L q) x ≤ 1) :
    FunctionField.Chart.placeValuation K L q
      (algebraMap (RatFunc K) L x) ≤ 1 := by
  let P := (finiteExtensionPlaceEquivChart K L).symm q
  have hP : finiteExtensionPlaceEquivChart K L P = q :=
    (finiteExtensionPlaceEquivChart K L).apply_symm_apply q
  rw [← hP] at hx ⊢
  rcases P with q | P
  · let p₀ := q.under K[X]
    let pChart := HeightOneSpectrum.equivOfRingEquiv
      (ratFuncFiniteBaseRingEquivChart K) p₀
    have hbaseEq : p₀.valuation (RatFunc K) =
        pChart.valuation (RatFunc K) :=
      heightOneValuation_eq_of_ringEquiv
        (ratFuncFiniteBaseRingEquivChart K)
        (ratFuncFiniteBaseRingEquivChart_algebraMap K)
        p₀ pChart rfl
    have hunderChart : finiteExtensionUnderPlaceChart K L
        (finiteExtensionPlaceEquivChart K L (.inl q)) =
          Sum.inl pChart := by
      simp only [finiteExtensionUnderPlaceChart, Equiv.symm_apply_apply,
        finiteExtensionUnderPlace]
      rfl
    have hx₀ : p₀.valuation (RatFunc K) x ≤ 1 := by
      rw [hbaseEq]
      rw [hunderChart] at hx
      exact hx
    exact heightOneValuation_algebraMap_le_one_of_under
      q p₀ rfl hx₀
  · let p₀ := ratFuncInfinityPlace K
    let pChart := HeightOneSpectrum.equivOfRingEquiv
      (ratFuncInfinityBaseRingEquivChart K) p₀
    let q₀ := primeOverHeightOne (ratFuncInfinityPlace K) P
    have hbaseEq : p₀.valuation (RatFunc K) =
        pChart.valuation (RatFunc K) :=
      heightOneValuation_eq_of_ringEquiv
        (ratFuncInfinityBaseRingEquivChart K)
        (ratFuncInfinityBaseRingEquivChart_algebraMap K)
        p₀ pChart rfl
    have hunderChart : finiteExtensionUnderPlaceChart K L
        (finiteExtensionPlaceEquivChart K L (.inr P)) =
          Sum.inr pChart := by
      simp only [finiteExtensionUnderPlaceChart, Equiv.symm_apply_apply,
        finiteExtensionUnderPlace]
      rfl
    have hx₀ : p₀.valuation (RatFunc K) x ≤ 1 := by
      rw [hbaseEq]
      rw [hunderChart] at hx
      exact hx
    have hqUnder : q₀.under (RatFuncInfinityIntegers K) = p₀ := by
      apply HeightOneSpectrum.ext
      exact (Ideal.over_def P.1 (ratFuncInfinityPlace K).asIdeal).symm
    have htop : q₀.valuation L (algebraMap (RatFunc K) L x) ≤ 1 :=
      heightOneValuation_algebraMap_le_one_of_under q₀ p₀ hqUnder hx₀
    have htopEq := congrArg
      (fun v : Valuation L ℤᵐ⁰ => v (algebraMap (RatFunc K) L x))
      (finiteExtensionPlaceValuation_eq_chart K L (.inr P))
    rw [← htopEq]
    exact htop

/-- A chosen place of `L` above each rational-function chart place. -/
def finiteExtensionPlaceSectionChart
    (p : FunctionField.Chart.PlaceA K (RatFunc K)) :
    FunctionField.Chart.PlaceA K L :=
  Classical.choose (finiteExtensionUnderPlaceChart_surjective K L p)

@[simp]
theorem finiteExtensionUnderPlaceChart_section
    (p : FunctionField.Chart.PlaceA K (RatFunc K)) :
    finiteExtensionUnderPlaceChart K L
      (finiteExtensionPlaceSectionChart K L p) = p :=
  Classical.choose_spec (finiteExtensionUnderPlaceChart_surjective K L p)

/-- Adeles whose components are constant on every fiber over a base place. -/
def finiteExtensionFiberConstantAdeleSubmodule :
    Submodule K (FunctionField.Chart.AdeleSpace K L) where
  carrier := {a | ∀ q r,
    finiteExtensionUnderPlaceChart K L q =
      finiteExtensionUnderPlaceChart K L r → a.1 q = a.1 r}
  zero_mem' := by simp
  add_mem' {a b} ha hb q r hqr := by
    change a.1 q + b.1 q = a.1 r + b.1 r
    rw [ha q r hqr, hb q r hqr]
  smul_mem' c a ha q r hqr := by
    change c • a.1 q = c • a.1 r
    rw [ha q r hqr]

/-- A fiber-constant adele has the chosen component at the base place of
every upstairs place. -/
theorem fiberConstant_component_eq_section
    (a : finiteExtensionFiberConstantAdeleSubmodule K L)
    (q : FunctionField.Chart.PlaceA K L) :
    a.1.1 q = a.1.1 (finiteExtensionPlaceSectionChart K L
      (finiteExtensionUnderPlaceChart K L q)) := by
  apply a.2
  rw [finiteExtensionUnderPlaceChart_section]

/-- Componentwise field trace of a fiber-constant adele, before proving that
the resulting tuple is a rational-function adele. -/
def finiteExtensionFiberTraceRaw :
    finiteExtensionFiberConstantAdeleSubmodule K L →ₗ[K]
      (FunctionField.Chart.PlaceA K (RatFunc K) → RatFunc K) where
  toFun a p := Algebra.trace (RatFunc K) L
    (a.1.1 (finiteExtensionPlaceSectionChart K L p))
  map_add' a b := by
    funext p
    exact map_add (Algebra.trace (RatFunc K) L) _ _
  map_smul' c a := by
    funext p
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
    simp only [RingHom.id_apply]
    simpa [Algebra.smul_def] using
      (Algebra.trace (RatFunc K) L).map_smul
        (algebraMap K (RatFunc K) c)
        (a.1.1 (finiteExtensionPlaceSectionChart K L p))

/-- Top chart places at which a given adele is not integral. -/
def finiteExtensionAdeleExceptionalSet
    (a : FunctionField.Chart.AdeleSpace K L) :
    Set (FunctionField.Chart.PlaceA K L) :=
  {q | a.1 q ∉ FunctionField.Chart.placeValuationSubring K L q}

theorem finiteExtensionAdeleExceptionalSet_finite
    (a : FunctionField.Chart.AdeleSpace K L) :
    (finiteExtensionAdeleExceptionalSet K L a).Finite := by
  have ha := a.2
  change ∀ᶠ q : FunctionField.Chart.PlaceA K L in Filter.cofinite,
    a.1 q ∈ FunctionField.Chart.placeValuationSubring K L q at ha
  simpa only [Filter.eventually_cofinite,
    finiteExtensionAdeleExceptionalSet] using ha

/-- Finite chart places in the support of the finite different. -/
def finiteExtensionDifferentExceptionalSet :
    Set (FunctionField.Chart.PlaceA K L) :=
  finiteExtensionPlaceEquivChart K L ''
    (Sum.inl '' {q : FiniteExtensionFinitePlace K L |
      multiplicity q.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) ≠ 0})

theorem finiteExtensionDifferentExceptionalSet_finite :
    (finiteExtensionDifferentExceptionalSet K L).Finite := by
  have hdiff : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥ :=
    finiteExtensionFiniteDifferentIdeal_ne_bot K L
  have hcountFinite : Set.Finite {q : FiniteExtensionFinitePlace K L |
      FractionalIdeal.count L q
        ((differentIdeal K[X] (RatFuncFiniteIntegralClosure K L) :
          Ideal (RatFuncFiniteIntegralClosure K L)) :
          FractionalIdeal (RatFuncFiniteIntegralClosure K L)⁰ L) ≠ 0} := by
    simpa only [Filter.eventually_cofinite] using
      FractionalIdeal.finite_factors (K := L)
        ((differentIdeal K[X] (RatFuncFiniteIntegralClosure K L) :
          Ideal (RatFuncFiniteIntegralClosure K L)) :
          FractionalIdeal (RatFuncFiniteIntegralClosure K L)⁰ L)
  have hmultFinite : Set.Finite {q : FiniteExtensionFinitePlace K L |
      multiplicity q.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) ≠ 0} := by
    refine hcountFinite.subset ?_
    intro q hq
    change FractionalIdeal.count L q
      ((differentIdeal K[X] (RatFuncFiniteIntegralClosure K L) :
        Ideal (RatFuncFiniteIntegralClosure K L)) :
        FractionalIdeal (RatFuncFiniteIntegralClosure K L)⁰ L) ≠ 0
    rw [FractionalIdeal.count_coeIdeal_eq_multiplicity
      (K := L) (differentIdeal K[X]
        (RatFuncFiniteIntegralClosure K L)) hdiff]
    exact_mod_cast hq
  exact (hmultFinite.image Sum.inl).image
    (finiteExtensionPlaceEquivChart K L)

/-- The unique base infinity chart place, expressed through the exhaustive
place equivalence. -/
def ratFuncInfinityPlaceChart :
    FunctionField.Chart.PlaceA K (RatFunc K) :=
  ratFuncExhaustivePlaceEquivChart K (.inr (ratFuncInfinityPlace K))

/-- The finite exceptional set outside which the componentwise trace is
integral. -/
def finiteExtensionCotraceBadBaseSet
    (a : FunctionField.Chart.AdeleSpace K L) :
    Set (FunctionField.Chart.PlaceA K (RatFunc K)) :=
  finiteExtensionUnderPlaceChart K L ''
      (finiteExtensionAdeleExceptionalSet K L a ∪
        finiteExtensionDifferentExceptionalSet K L) ∪
    {ratFuncInfinityPlaceChart K}

theorem finiteExtensionCotraceBadBaseSet_finite
    (a : FunctionField.Chart.AdeleSpace K L) :
    (finiteExtensionCotraceBadBaseSet K L a).Finite := by
  apply Set.Finite.union
  · exact ((finiteExtensionAdeleExceptionalSet_finite K L a).union
      (finiteExtensionDifferentExceptionalSet_finite K L)).image
        (finiteExtensionUnderPlaceChart K L)
  · exact Set.finite_singleton _

/-- The infinity component of the rational-function chart contains only the
place transported from the BGS infinity valuation ring. -/
theorem ratFunc_infinite_chart_place_eq
    (p : HeightOneSpectrum
      (FunctionField.Chart.infiniteIntegers K (RatFunc K))) :
    (Sum.inr p : FunctionField.Chart.PlaceA K (RatFunc K)) =
      ratFuncInfinityPlaceChart K := by
  let e := HeightOneSpectrum.equivOfRingEquiv
    (ratFuncInfinityBaseRingEquivChart K)
  have hsource : e.symm p = ratFuncInfinityPlace K := by
    apply HeightOneSpectrum.ext
    exact (IsLocalRing.eq_maximalIdeal
      ((e.symm p).isPrime.isMaximal (e.symm p).ne_bot)).trans
        (IsLocalRing.eq_maximalIdeal
          ((ratFuncInfinityPlace K).isPrime.isMaximal
            (ratFuncInfinityPlace K).ne_bot)).symm
  change Sum.inr p = Sum.inr (e (ratFuncInfinityPlace K))
  apply congrArg Sum.inr
  rw [← hsource, e.apply_symm_apply]

/-- Outside the explicit finite exceptional set, the raw componentwise trace
is integral at the base chart place. -/
theorem finiteExtensionFiberTraceRaw_mem_placeValuationSubring_of_not_bad
    (a : finiteExtensionFiberConstantAdeleSubmodule K L)
    (p : FunctionField.Chart.PlaceA K (RatFunc K))
    (hp : p ∉ finiteExtensionCotraceBadBaseSet K L a.1) :
    finiteExtensionFiberTraceRaw K L a p ∈
      FunctionField.Chart.placeValuationSubring K (RatFunc K) p := by
  rcases p with p | p
  · let e := HeightOneSpectrum.equivOfRingEquiv
      (ratFuncFiniteBaseRingEquivChart K)
    let p₀ : HeightOneSpectrum K[X] := e.symm p
    let q₀ := finiteExtensionPlaceSectionChart K L
      (Sum.inl p : FunctionField.Chart.PlaceA K (RatFunc K))
    let y : L := a.1.1 q₀
    by_cases hy : y = 0
    · change Algebra.trace (RatFunc K) L y ∈ _
      rw [hy, map_zero]
      exact zero_mem _
    have hnotTop (q : FunctionField.Chart.PlaceA K L)
        (hq : finiteExtensionUnderPlaceChart K L q = Sum.inl p) :
        q ∉ finiteExtensionAdeleExceptionalSet K L a.1 ∪
          finiteExtensionDifferentExceptionalSet K L := by
      intro hqbad
      apply hp
      apply Or.inl
      exact ⟨q, hqbad, hq⟩
    have hlocal : ∀ q : HeightOneSpectrum
        (RatFuncFiniteIntegralClosure K L),
        q.under K[X] = p₀ →
          -(multiplicity q.asIdeal
            (differentIdeal K[X]
              (RatFuncFiniteIntegralClosure K L)) : ℤ) ≤
            FractionalIdeal.count L q
              (FractionalIdeal.spanSingleton
                (RatFuncFiniteIntegralClosure K L)⁰ y) := by
      intro q hqUnder
      let qChart : FunctionField.Chart.PlaceA K L :=
        finiteExtensionPlaceEquivChart K L (.inl q)
      have hpImage : e p₀ = p := e.apply_symm_apply p
      have hqBelow : finiteExtensionUnderPlaceChart K L qChart =
          Sum.inl p := by
        change ratFuncExhaustivePlaceEquivChart K
            (Sum.inl (q.under K[X])) = Sum.inl p
        rw [hqUnder]
        change Sum.inl (e p₀) = Sum.inl p
        rw [hpImage]
      have hqGood := hnotTop qChart hqBelow
      have hqAdele : qChart ∉
          finiteExtensionAdeleExceptionalSet K L a.1 := by
        exact fun h => hqGood (Or.inl h)
      have hqDifferent : qChart ∉
          finiteExtensionDifferentExceptionalSet K L := by
        exact fun h => hqGood (Or.inr h)
      have hyEq : a.1.1 qChart = y := by
        have hcomponent := fiberConstant_component_eq_section K L a qChart
        rw [hqBelow] at hcomponent
        exact hcomponent
      have hqMem : a.1.1 qChart ∈
          FunctionField.Chart.placeValuationSubring K L qChart := by
        exact Classical.not_not.mp hqAdele
      have hqValChart : FunctionField.Chart.placeValuation K L qChart
          (a.1.1 qChart) ≤ 1 := by
        rwa [← Valuation.mem_valuationSubring_iff]
      have hqVal : q.valuation L y ≤ 1 := by
        rw [← hyEq]
        simpa [qChart, finiteExtensionPlaceEquivChart,
          FunctionField.Chart.placeValuation] using hqValChart
      have hqCount : 0 ≤ FractionalIdeal.count L q
          (FractionalIdeal.spanSingleton
            (RatFuncFiniteIntegralClosure K L)⁰ y) :=
        zero_le_count_spanSingleton_of_valuation_le_one q hy hqVal
      have hqMultiplicity : multiplicity q.asIdeal
          (differentIdeal K[X]
            (RatFuncFiniteIntegralClosure K L)) = 0 := by
        by_contra hne
        apply hqDifferent
        exact ⟨Sum.inl q, ⟨q, hne, rfl⟩, rfl⟩
      rw [hqMultiplicity]
      simpa using hqCount
    have htraceBase : p₀.valuation (RatFunc K)
        (Algebra.trace (RatFunc K) L y) ≤ 1 :=
      valuation_trace_le_one_of_different_count_bounds_over
        (A := K[X]) (K₀ := RatFunc K)
        (B := RatFuncFiniteIntegralClosure K L) (L := L)
        p₀ hy hlocal
    have htraceChart : (e p₀).valuation (RatFunc K)
        (Algebra.trace (RatFunc K) L y) ≤ 1 := by
      apply heightOneValuation_le_one_of_ringEquiv
        (ratFuncFiniteBaseRingEquivChart K)
        (ratFuncFiniteBaseRingEquivChart_algebraMap K)
        p₀ (e p₀) rfl htraceBase
    change p.valuation (RatFunc K)
        (Algebra.trace (RatFunc K) L y) ≤ 1
    have hpImage : e p₀ = p := e.apply_symm_apply p
    rw [hpImage] at htraceChart
    exact htraceChart
  · exfalso
    apply hp
    apply Or.inr
    exact Set.mem_singleton_iff.mpr (ratFunc_infinite_chart_place_eq K p)

/-- Componentwise field trace as an actual rational-function adele. -/
def finiteExtensionFiberTrace :
    finiteExtensionFiberConstantAdeleSubmodule K L →ₗ[K]
      FunctionField.Chart.AdeleSpace K (RatFunc K) where
  toFun a := ⟨finiteExtensionFiberTraceRaw K L a, by
    change ∀ᶠ p : FunctionField.Chart.PlaceA K (RatFunc K) in
      Filter.cofinite,
        finiteExtensionFiberTraceRaw K L a p ∈
          FunctionField.Chart.placeValuationSubring K (RatFunc K) p
    rw [Filter.eventually_cofinite]
    refine (finiteExtensionCotraceBadBaseSet_finite K L a.1).subset ?_
    intro p hp
    by_contra hpBad
    exact hp (finiteExtensionFiberTraceRaw_mem_placeValuationSubring_of_not_bad
      K L a p hpBad)⟩
  map_add' a b := by
    apply Subtype.ext
    exact congrArg (fun f => f) ((finiteExtensionFiberTraceRaw K L).map_add a b)
  map_smul' c a := by
    apply Subtype.ext
    exact congrArg (fun f => f) ((finiteExtensionFiberTraceRaw K L).map_smul c a)

/-- Lift a base adele to a fiber-constant upstairs adele after multiplying by
a fixed extension-field element. -/
def finiteExtensionFiberLift (z : L)
    (b : FunctionField.Chart.AdeleSpace K (RatFunc K)) :
    finiteExtensionFiberConstantAdeleSubmodule K L := by
  letI : Filter.TendstoCofinite (finiteExtensionUnderPlaceChart K L) :=
    finiteExtensionUnderPlaceChart_tendstoCofinite K L
  let a : FunctionField.Chart.AdeleSpace K L :=
    ⟨fun q => z * algebraMap (RatFunc K) L
        (b.1 (finiteExtensionUnderPlaceChart K L q)), by
      have hz := FunctionField.Chart.eventually_mem_placeValuationSubring K L z
      have hb : ∀ᶠ q : FunctionField.Chart.PlaceA K L in Filter.cofinite,
          b.1 (finiteExtensionUnderPlaceChart K L q) ∈
            FunctionField.Chart.placeValuationSubring K (RatFunc K)
              (finiteExtensionUnderPlaceChart K L q) :=
        Filter.TendstoCofinite.tendsto_cofinite
          (finiteExtensionUnderPlaceChart K L) b.2
      filter_upwards [hz, hb] with q hzq hbq
      apply mul_mem hzq
      exact finiteExtension_placeValuation_algebraMap_le_one K L q hbq⟩
  refine ⟨a, ?_⟩
  intro q r hqr
  change z * algebraMap (RatFunc K) L
      (b.1 (finiteExtensionUnderPlaceChart K L q)) =
    z * algebraMap (RatFunc K) L
      (b.1 (finiteExtensionUnderPlaceChart K L r))
  rw [hqr]

/-- Cotrace of the lifted adele is scalar multiplication by `Tr(z)`. -/
theorem finiteExtensionFiberTrace_lift (z : L)
    (b : FunctionField.Chart.AdeleSpace K (RatFunc K)) :
    finiteExtensionFiberTrace K L (finiteExtensionFiberLift K L z b) =
      (Algebra.trace (RatFunc K) L z) • b := by
  apply Subtype.ext
  funext p
  change Algebra.trace (RatFunc K) L
      ((finiteExtensionFiberLift K L z b).1.1
        (finiteExtensionPlaceSectionChart K L p)) =
    Algebra.trace (RatFunc K) L z * b.1 p
  change Algebra.trace (RatFunc K) L
      (z * algebraMap (RatFunc K) L
        (b.1 (finiteExtensionUnderPlaceChart K L
          (finiteExtensionPlaceSectionChart K L p)))) = _
  rw [finiteExtensionUnderPlaceChart_section]
  simpa [Algebra.smul_def, mul_comm] using
    (Algebra.trace (RatFunc K) L).map_smul (b.1 p) z

/-- Componentwise cotrace is onto the base adele space. -/
theorem finiteExtensionFiberTrace_surjective :
    Function.Surjective (finiteExtensionFiberTrace K L) := by
  intro b
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (RatFunc K) L (1 : RatFunc K)
  refine ⟨finiteExtensionFiberLift K L z b, ?_⟩
  rw [finiteExtensionFiberTrace_lift K L z b, hz, one_smul]

/-- At a finite base place, the componentwise trace of a fiber-constant
adele in the explicit different filtration is integral. -/
theorem finiteExtensionFiberTrace_finite_valuation_le_one
    (a : finiteExtensionFiberConstantAdeleSubmodule K L)
    (ha : a.1 ∈ FunctionField.Chart.adeleFilt K L
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L))))
    (p : HeightOneSpectrum
      (FunctionField.ringOfIntegers K (RatFunc K))) :
    p.valuation (RatFunc K)
      ((finiteExtensionFiberTrace K L a).1 (.inl p)) ≤ 1 := by
  let e := HeightOneSpectrum.equivOfRingEquiv
    (ratFuncFiniteBaseRingEquivChart K)
  let p₀ : HeightOneSpectrum K[X] := e.symm p
  let q₀ := finiteExtensionPlaceSectionChart K L
    (Sum.inl p : FunctionField.Chart.PlaceA K (RatFunc K))
  let y : L := a.1.1 q₀
  by_cases hy : y = 0
  · change p.valuation (RatFunc K) (Algebra.trace (RatFunc K) L y) ≤ 1
    rw [hy, map_zero, Valuation.map_zero]
    exact zero_le
  have hlocal : ∀ q : HeightOneSpectrum
      (RatFuncFiniteIntegralClosure K L),
      q.under K[X] = p₀ →
        -(multiplicity q.asIdeal
          (differentIdeal K[X]
            (RatFuncFiniteIntegralClosure K L)) : ℤ) ≤
          FractionalIdeal.count L q
            (FractionalIdeal.spanSingleton
              (RatFuncFiniteIntegralClosure K L)⁰ y) := by
    intro q hqUnder
    let qChart : FunctionField.Chart.PlaceA K L :=
      finiteExtensionPlaceEquivChart K L (.inl q)
    have hpImage : e p₀ = p := e.apply_symm_apply p
    have hqBelow : finiteExtensionUnderPlaceChart K L qChart =
        Sum.inl p := by
      change ratFuncExhaustivePlaceEquivChart K
          (Sum.inl (q.under K[X])) = Sum.inl p
      rw [hqUnder]
      change Sum.inl (e p₀) = Sum.inl p
      rw [hpImage]
    have hyEq : a.1.1 qChart = y := by
      have hcomponent := fiberConstant_component_eq_section K L a qChart
      rw [hqBelow] at hcomponent
      exact hcomponent
    have hqFilter := ha qChart
    have hqFilter' : q.valuation L y ≤
        WithZero.exp
          (multiplicity q.asIdeal
            (differentIdeal K[X]
              (RatFuncFiniteIntegralClosure K L)) : ℤ) := by
      rw [← hyEq]
      simpa [qChart, finiteExtensionPlaceEquivChart,
        FunctionField.Chart.placeValuation,
        finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply,
        finiteExtensionCanonicalDifferentDivisor_inl] using hqFilter
    have hqValuation := valuation_eq_exp_neg_finitePlaceOrder q y hy
    rw [hqValuation] at hqFilter'
    have hqExp := WithZero.exp_le_exp.mp hqFilter'
    change -FractionalIdeal.count L q
      (FractionalIdeal.spanSingleton
        (RatFuncFiniteIntegralClosure K L)⁰ y) ≤
      (multiplicity q.asIdeal
        (differentIdeal K[X]
          (RatFuncFiniteIntegralClosure K L)) : ℤ) at hqExp
    omega
  have htraceBase : p₀.valuation (RatFunc K)
      (Algebra.trace (RatFunc K) L y) ≤ 1 :=
    valuation_trace_le_one_of_different_count_bounds_over
      (A := K[X]) (K₀ := RatFunc K)
      (B := RatFuncFiniteIntegralClosure K L) (L := L)
      p₀ hy hlocal
  have htraceChart : (e p₀).valuation (RatFunc K)
      (Algebra.trace (RatFunc K) L y) ≤ 1 := by
    apply heightOneValuation_le_one_of_ringEquiv
      (ratFuncFiniteBaseRingEquivChart K)
      (ratFuncFiniteBaseRingEquivChart_algebraMap K)
      p₀ (e p₀) rfl htraceBase
  have hpImage : e p₀ = p := e.apply_symm_apply p
  change p.valuation (RatFunc K)
    (Algebra.trace (RatFunc K) L y) ≤ 1
  rw [hpImage] at htraceChart
  exact htraceChart

/-- At the infinite base place, the componentwise trace of a fiber-constant
adele in the explicit different filtration has order at least two. -/
theorem finiteExtensionFiberTrace_infinite_valuation_le_exp_neg_two
    (a : finiteExtensionFiberConstantAdeleSubmodule K L)
    (ha : a.1 ∈ FunctionField.Chart.adeleFilt K L
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L))))
    (p : HeightOneSpectrum
      (FunctionField.Chart.infiniteIntegers K (RatFunc K))) :
    p.valuation (RatFunc K)
      ((finiteExtensionFiberTrace K L a).1 (.inr p)) ≤
        WithZero.exp (-2 : ℤ) := by
  let pInf := ratFuncInfinityPlace K
  let pChart := HeightOneSpectrum.equivOfRingEquiv
    (ratFuncInfinityBaseRingEquivChart K) pInf
  have hpChart : p = pChart := by
    apply Sum.inr_injective
    calc
      Sum.inr p = ratFuncInfinityPlaceChart K :=
        ratFunc_infinite_chart_place_eq K p
      _ = Sum.inr pChart := rfl
  let q₀ := finiteExtensionPlaceSectionChart K L
    (Sum.inr p : FunctionField.Chart.PlaceA K (RatFunc K))
  let y : L := a.1.1 q₀
  by_cases hy : y = 0
  · change p.valuation (RatFunc K) (Algebra.trace (RatFunc K) L y) ≤ _
    rw [hy, map_zero, Valuation.map_zero]
    exact zero_le
  let s := ratFuncInfinityUniformizer K
  have hs : s ≠ 0 := by
    intro h
    have hcoe := congrArg Subtype.val h
    exact (one_div_ne_zero RatFunc.X_ne_zero) hcoe
  let t : RatFunc K := algebraMap (RatFuncInfinityIntegers K) (RatFunc K) s
  let tL : L := algebraMap (RatFuncInfinityIntegers K) L s
  have htL : tL ≠ 0 := by
    simpa only [tL, map_zero] using
      (FaithfulSMul.algebraMap_injective
        (RatFuncInfinityIntegers K) L).ne hs
  let z : L := (tL ^ 2)⁻¹ * y
  have hz : z ≠ 0 := mul_ne_zero (inv_ne_zero (pow_ne_zero 2 htL)) hy
  have hlocal : ∀ q : HeightOneSpectrum
      (RatFuncInfinityIntegralClosure K L),
      q.under (RatFuncInfinityIntegers K) = pInf →
        -(multiplicity q.asIdeal
          (differentIdeal (RatFuncInfinityIntegers K)
            (RatFuncInfinityIntegralClosure K L)) : ℤ) ≤
          FractionalIdeal.count L q
            (FractionalIdeal.spanSingleton
              (RatFuncInfinityIntegralClosure K L)⁰ z) := by
    intro q hqUnder
    letI : q.asIdeal.LiesOver pInf.asIdeal := ⟨by
      have hideal := congrArg HeightOneSpectrum.asIdeal hqUnder
      exact hideal.symm⟩
    let P : FiniteExtensionInfinityPlace K L :=
      (finiteExtensionInfinityPrimesOverEquivHeightOne K L).symm q
    have hPq : primeOverHeightOne (ratFuncInfinityPlace K) P = q :=
      (finiteExtensionInfinityPrimesOverEquivHeightOne K L).apply_symm_apply q
    let qChart : FunctionField.Chart.PlaceA K L :=
      finiteExtensionPlaceEquivChart K L (.inr P)
    have hqBelow : finiteExtensionUnderPlaceChart K L qChart =
        Sum.inr p := by
      calc
        finiteExtensionUnderPlaceChart K L qChart =
            ratFuncInfinityPlaceChart K := by rfl
        _ = Sum.inr p := (ratFunc_infinite_chart_place_eq K p).symm
    have hyEq : a.1.1 qChart = y := by
      have hcomponent := fiberConstant_component_eq_section K L a qChart
      rw [hqBelow] at hcomponent
      exact hcomponent
    have hqFilter := ha qChart
    have hcoeff :
        (finiteExtensionDivisorEquivChart K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) qChart =
          (multiplicity P.1
            (differentIdeal (RatFuncInfinityIntegers K)
              (RatFuncInfinityIntegralClosure K L)) : ℤ) -
            2 * (P.1.ramificationIdx
              (RatFuncInfinityIntegers K) : ℤ) := by
      simp [qChart, finiteExtensionDivisorEquivChart,
        Finsupp.domCongr_apply,
        finiteExtensionCanonicalDifferentDivisor_inr]
    rw [hcoeff] at hqFilter
    have hvaluationEq :
        (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L y =
          FunctionField.Chart.placeValuation K L qChart y := by
      simpa only [finiteExtensionPlaceValuation, qChart] using
        congrArg (fun v : Valuation L ℤᵐ⁰ => v y)
          (finiteExtensionPlaceValuation_eq_chart K L (.inr P))
    have hqFilterBGS :
        (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L y ≤
          WithZero.exp
            ((multiplicity P.1
              (differentIdeal (RatFuncInfinityIntegers K)
                (RatFuncInfinityIntegralClosure K L)) : ℤ) -
              2 * (P.1.ramificationIdx
                (RatFuncInfinityIntegers K) : ℤ)) := by
      rw [hvaluationEq]
      simpa only [hyEq] using hqFilter
    rw [hPq] at hqFilterBGS
    have hqValuation := valuation_eq_exp_neg_finitePlaceOrder q y hy
    rw [hqValuation] at hqFilterBGS
    have hqOrderBound := WithZero.exp_le_exp.mp hqFilterBGS
    change -finitePlaceOrder q y ≤
      (multiplicity P.1
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) : ℤ) -
        2 * (P.1.ramificationIdx
          (RatFuncInfinityIntegers K) : ℤ) at hqOrderBound
    have htOrder : finitePlaceOrder q tL =
        (q.asIdeal.ramificationIdx
          (RatFuncInfinityIntegers K) : ℤ) := by
      simpa only [tL, IsScalarTower.algebraMap_apply
        (RatFuncInfinityIntegers K)
        (RatFuncInfinityIntegralClosure K L) L] using
        finitePlaceOrder_algebraMap_uniformizer_eq_ramificationIdx
          (R := RatFuncInfinityIntegers K)
          (A := RatFuncInfinityIntegralClosure K L) (F := L)
          pInf q s hs (ratFuncInfinityPlace_span_uniformizer K)
    have htSquareOrder := finitePlaceOrder_mul_eq_add q tL tL htL htL
    rw [← pow_two] at htSquareOrder
    have htInvOrder := finitePlaceOrder_inv_eq_neg' q (tL ^ 2)
      (pow_ne_zero 2 htL)
    have hzOrder := finitePlaceOrder_mul_eq_add q (tL ^ 2)⁻¹ y
      (inv_ne_zero (pow_ne_zero 2 htL)) hy
    have hram : P.1.ramificationIdx (RatFuncInfinityIntegers K) =
        q.asIdeal.ramificationIdx (RatFuncInfinityIntegers K) := by
      rw [← hPq]
      rfl
    have hPideal : P.1 = q.asIdeal := by
      rw [← hPq]
      rfl
    change -(multiplicity q.asIdeal
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) : ℤ) ≤
      finitePlaceOrder q ((tL ^ 2)⁻¹ * y)
    rw [hzOrder, htInvOrder, htSquareOrder, htOrder]
    rw [hPideal] at hqOrderBound
    omega
  have htraceScaled : pInf.valuation (RatFunc K)
      (Algebra.trace (RatFunc K) L z) ≤ 1 :=
    valuation_trace_le_one_of_different_count_bounds_over
      (A := RatFuncInfinityIntegers K) (K₀ := RatFunc K)
      (B := RatFuncInfinityIntegralClosure K L) (L := L)
      pInf hz hlocal
  have htTower : tL = algebraMap (RatFunc K) L t := by
    exact (IsScalarTower.algebraMap_apply
      (RatFuncInfinityIntegers K) (RatFunc K) L s).symm
  have htraceZ : Algebra.trace (RatFunc K) L z =
      (t ^ 2)⁻¹ * Algebra.trace (RatFunc K) L y := by
    have hscalar : (tL ^ 2)⁻¹ * y = ((t ^ 2)⁻¹) • y := by
      rw [Algebra.smul_def, htTower, map_inv₀, map_pow]
    change Algebra.trace (RatFunc K) L ((tL ^ 2)⁻¹ * y) =
      ((t ^ 2)⁻¹) • Algebra.trace (RatFunc K) L y
    rw [hscalar]
    exact (Algebra.trace (RatFunc K) L).map_smul ((t ^ 2)⁻¹) y
  rw [htraceZ, map_mul, map_inv₀, map_pow] at htraceScaled
  have htVal : pInf.valuation (RatFunc K) t = WithZero.exp (-1 : ℤ) := by
    change pInf.valuation (RatFunc K)
      (algebraMap (RatFuncInfinityIntegers K) (RatFunc K) s) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact pInf.intValuation_singleton hs
      (ratFuncInfinityPlace_span_uniformizer K)
  rw [htVal] at htraceScaled
  have hbase : pInf.valuation (RatFunc K)
      (Algebra.trace (RatFunc K) L y) ≤ WithZero.exp (-2 : ℤ) := by
    apply le_of_mul_le_mul_left ?_ (WithZero.exp_pos :
      0 < WithZero.exp (2 : ℤ))
    calc
      WithZero.exp (2 : ℤ) * pInf.valuation (RatFunc K)
          (Algebra.trace (RatFunc K) L y) =
          ((WithZero.exp (-1 : ℤ)) ^ 2)⁻¹ *
            pInf.valuation (RatFunc K)
              (Algebra.trace (RatFunc K) L y) := by norm_num
      _ ≤ 1 := htraceScaled
      _ = WithZero.exp (2 : ℤ) * WithZero.exp (-2 : ℤ) := by
        rw [← WithZero.exp_add]
        norm_num
  have hchart : pChart.valuation (RatFunc K)
      (Algebra.trace (RatFunc K) L y) ≤ WithZero.exp (-2 : ℤ) := by
    have hvaluation : pInf.valuation (RatFunc K) =
        pChart.valuation (RatFunc K) :=
      heightOneValuation_eq_of_ringEquiv
        (ratFuncInfinityBaseRingEquivChart K)
        (ratFuncInfinityBaseRingEquivChart_algebraMap K)
        pInf pChart rfl
    rw [← hvaluation]
    exact hbase
  change p.valuation (RatFunc K)
    (Algebra.trace (RatFunc K) L y) ≤ WithZero.exp (-2 : ℤ)
  rw [hpChart]
  exact hchart

/-- The infinity place selected for the identity extension is the unique
infinity place in the base chart. -/
theorem ratFuncInfinityChartPlace_eq_baseChart :
    ratFuncInfinityChartPlace K = ratFuncInfinityPlaceChart K := by
  let p : HeightOneSpectrum
      (FunctionField.Chart.infiniteIntegers K (RatFunc K)) :=
    finiteExtensionInfinityPlaceEquivChart K (RatFunc K)
      (ratFuncIdentityInfinityPlace K)
  change Sum.inr p = ratFuncInfinityPlaceChart K
  exact ratFunc_infinite_chart_place_eq K p

/-- The cotrace sends the explicit different filtration into the canonical
`-2∞` filtration on the rational function field. -/
theorem finiteExtensionFiberTrace_mem_ratFuncCanonicalInfinityAdeleFilt
    (a : finiteExtensionFiberConstantAdeleSubmodule K L)
    (ha : a.1 ∈ FunctionField.Chart.adeleFilt K L
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)))) :
    finiteExtensionFiberTrace K L a ∈
      FunctionField.Chart.adeleFilt K (RatFunc K)
        (ratFuncCanonicalInfinityDivisor K) := by
  intro v
  rcases v with p | p
  · have h := finiteExtensionFiberTrace_finite_valuation_le_one K L a ha p
    have hcoeff : ratFuncCanonicalInfinityDivisor K (Sum.inl p) = 0 := by
      rw [ratFuncCanonicalInfinityDivisor,
        Finsupp.single_eq_of_ne]
      change Sum.inl p ≠ Sum.inr _
      exact Sum.inl_ne_inr
    rw [hcoeff, WithZero.exp_zero]
    exact h
  · have h := finiteExtensionFiberTrace_infinite_valuation_le_exp_neg_two
      K L a ha p
    have hp : (Sum.inr p : FunctionField.Chart.PlaceA K (RatFunc K)) =
        ratFuncInfinityChartPlace K := by
      rw [ratFuncInfinityChartPlace_eq_baseChart K]
      exact ratFunc_infinite_chart_place_eq K p
    have hcoeff : ratFuncCanonicalInfinityDivisor K (Sum.inr p) = -2 := by
      rw [ratFuncCanonicalInfinityDivisor, hp, Finsupp.single_eq_same]
    rw [hcoeff]
    exact h

/-- Principal adeles are fiber-constant. -/
theorem finiteExtension_diagonal_mem_fiberConstant (x : L) :
    FunctionField.Chart.diagonal K L x ∈
      finiteExtensionFiberConstantAdeleSubmodule K L := by
  intro q r _hqr
  rfl

/-- Cotrace carries a principal adele to the principal adele of the field
trace. -/
theorem finiteExtensionFiberTrace_diagonal (x : L) :
    finiteExtensionFiberTrace K L
        ⟨FunctionField.Chart.diagonal K L x,
          finiteExtension_diagonal_mem_fiberConstant K L x⟩ =
      FunctionField.Chart.diagonal K (RatFunc K)
        (Algebra.trace (RatFunc K) L x) := by
  apply Subtype.ext
  funext p
  rfl

/-- The base canonical functional composed with cotrace vanishes on the
intersection of fiber-constant adeles with the explicit different
filtration plus principal adeles. -/
theorem finiteExtensionFiberCotrace_vanishes_on_intersection
    (ω : FunctionField.Chart.WeilDifferential K (RatFunc K))
    (hωvan : ratFuncCanonicalInfinityDivisor K ∈
      FunctionField.Chart.WeilDifferential.vanishingDivisors ω)
    (x : ↥(finiteExtensionFiberConstantAdeleSubmodule K L ⊓
      (FunctionField.Chart.adeleFilt K L
          (finiteExtensionDivisorEquivChart K L
            (finiteExtensionCanonicalDifferentDivisor K L
              (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) +
        FunctionField.Chart.diagonalSubmodule K L))) :
    (ω.toFun.comp (finiteExtensionFiberTrace K L))
        ⟨x.1, x.2.1⟩ = 0 := by
  let U := finiteExtensionFiberConstantAdeleSubmodule K L
  let D := finiteExtensionDivisorEquivChart K L
    (finiteExtensionCanonicalDifferentDivisor K L
      (finiteExtensionFiniteDifferentIdeal_ne_bot K L))
  have hxsum : x.1 ∈ FunctionField.Chart.adeleFilt K L D ⊔
      FunctionField.Chart.diagonalSubmodule K L := by
    rw [← Submodule.add_eq_sup]
    exact x.2.2
  rcases Submodule.mem_sup.mp hxsum with ⟨a, ha, d, hd, had⟩
  obtain ⟨y, rfl⟩ := hd
  let dU : U :=
    ⟨FunctionField.Chart.diagonal K L y,
      finiteExtension_diagonal_mem_fiberConstant K L y⟩
  have haUmem : a ∈ U := by
    have hsub := U.sub_mem x.2.1 dU.2
    have haEq : x.1 - FunctionField.Chart.diagonal K L y = a := by
      rw [← had]
      abel
    rw [haEq] at hsub
    exact hsub
  let aU : U := ⟨a, haUmem⟩
  have hxEq : (⟨x.1, x.2.1⟩ : U) = aU + dU := by
    apply Subtype.ext
    exact had.symm
  have htraceA : finiteExtensionFiberTrace K L aU ∈
      FunctionField.Chart.adeleFilt K (RatFunc K)
        (ratFuncCanonicalInfinityDivisor K) :=
    finiteExtensionFiberTrace_mem_ratFuncCanonicalInfinityAdeleFilt
      K L aU ha
  have htraceD : finiteExtensionFiberTrace K L dU ∈
      FunctionField.Chart.diagonalSubmodule K (RatFunc K) := by
    rw [finiteExtensionFiberTrace_diagonal K L y]
    exact ⟨Algebra.trace (RatFunc K) L y, rfl⟩
  apply hωvan
  rw [hxEq, map_add]
  rw [Submodule.add_eq_sup]
  exact Submodule.add_mem_sup htraceA htraceD

/-- A nonzero base Weil functional stays nonzero after composition with the
surjective fiber cotrace. -/
theorem finiteExtensionFiberCotrace_ne_zero
    (ω : FunctionField.Chart.WeilDifferential K (RatFunc K))
    (hω : ω.toFun ≠ 0) :
    ω.toFun.comp (finiteExtensionFiberTrace K L) ≠ 0 := by
  intro hzero
  apply hω
  apply LinearMap.ext
  intro b
  obtain ⟨a, ha⟩ := finiteExtensionFiberTrace_surjective K L b
  have hz := LinearMap.congr_fun hzero a
  change ω.toFun ((finiteExtensionFiberTrace K L) a) = 0 at hz
  rw [ha] at hz
  exact hz

/-- The explicit finite-extension different divisor is a vanishing divisor
of a nonzero Weil differential.  Consequently it is bounded above by the
maximal divisor of that differential. -/
theorem finiteExtensionCanonicalDifferent_le_divOmega
    [FunctionField.IsFullConstantField K L] :
    ∃ (ωTop : FunctionField.Chart.WeilDifferential K L)
        (hωTop : FunctionField.Chart.WeilDifferential.IsNonzero ωTop),
      finiteExtensionDivisorEquivChart K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) ≤
        FunctionField.Chart.WeilDifferential.divOmega ωTop hωTop := by
  obtain ⟨ωBase, hωBase, hdivBase⟩ :=
    ratFuncCanonicalInfinityDivisor_isCanonical K
  have hmaxBase :
      FunctionField.Chart.WeilDifferential.divOmega ωBase hωBase ∈
          FunctionField.Chart.WeilDifferential.vanishingDivisors ωBase ∧
        ∀ D ∈ FunctionField.Chart.WeilDifferential.vanishingDivisors ωBase,
          D ≤ FunctionField.Chart.WeilDifferential.divOmega ωBase hωBase := by
    simpa only [FunctionField.Chart.WeilDifferential.divOmega] using
      (Classical.choose_spec
        (FunctionField.Chart.WeilDifferential.exists_max_vanishingDivisor
          (k := K) (K := RatFunc K) hωBase)).1
  have hbaseVan : ratFuncCanonicalInfinityDivisor K ∈
      FunctionField.Chart.WeilDifferential.vanishingDivisors ωBase := by
    rw [hdivBase] at hmaxBase
    exact hmaxBase.1
  let U := finiteExtensionFiberConstantAdeleSubmodule K L
  let D := finiteExtensionDivisorEquivChart K L
    (finiteExtensionCanonicalDifferentDivisor K L
      (finiteExtensionFiniteDifferentIdeal_ne_bot K L))
  let V := FunctionField.Chart.adeleFilt K L D +
    FunctionField.Chart.diagonalSubmodule K L
  let f := ωBase.toFun.comp (finiteExtensionFiberTrace K L)
  have hfVan : ∀ x : ↥(U ⊓ V), f ⟨x, x.property.1⟩ = 0 := by
    intro x
    exact finiteExtensionFiberCotrace_vanishes_on_intersection
      K L ωBase hbaseVan x
  have hfNe : f ≠ 0 :=
    finiteExtensionFiberCotrace_ne_zero K L ωBase hωBase
  obtain ⟨g, hgU, hgV, hgNe⟩ :=
    exists_ne_zero_linearMap_extending_eq_zero_on_inf U V f hfVan hfNe
  let ωTop : FunctionField.Chart.WeilDifferential K L :=
    ⟨g, ⟨D, fun a ha => LinearMap.mem_ker.mp (hgV ha)⟩⟩
  have hωTop : FunctionField.Chart.WeilDifferential.IsNonzero ωTop := by
    exact hgNe
  have hDvan : D ∈
      FunctionField.Chart.WeilDifferential.vanishingDivisors ωTop := by
    intro a ha
    exact LinearMap.mem_ker.mp (hgV ha)
  have hmaxTop :
      FunctionField.Chart.WeilDifferential.divOmega ωTop hωTop ∈
          FunctionField.Chart.WeilDifferential.vanishingDivisors ωTop ∧
        ∀ D' ∈ FunctionField.Chart.WeilDifferential.vanishingDivisors ωTop,
          D' ≤ FunctionField.Chart.WeilDifferential.divOmega ωTop hωTop := by
    simpa only [FunctionField.Chart.WeilDifferential.divOmega] using
      (Classical.choose_spec
        (FunctionField.Chart.WeilDifferential.exists_max_vanishingDivisor
          (k := K) (K := L) hωTop)).1
  exact ⟨ωTop, hωTop, hmaxTop.2 D hDvan⟩

end

end BGS.HasseWeil
