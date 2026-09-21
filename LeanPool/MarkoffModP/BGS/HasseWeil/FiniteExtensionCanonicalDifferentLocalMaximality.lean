/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCotraceLocalTraceImage
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentCanonicalityCriterion

/-!
# Local maximality of the canonical different by cotrace

This file connects the generic trace-image theorem formalizing Stichtenoth,
Theorem 3.4.6, Step (b1), to the explicit `-2∞` base differential and the
extension-place filtration.  A one-place witness detects every divisor not
bounded by the trace-different divisor.  Applied to the glued cotrace Weil
functional, this proves that the trace-different divisor is its exact maximal
vanishing divisor, without assuming a Riemann--Hurwitz degree identity.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain Multiplicative WithZero
open scoped Polynomial nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- At every base chart place, maximality of the canonical `-2∞`
differential supplies a one-component adele at the first filtration step on
which the differential is nonzero. -/
theorem ratFuncCanonicalWeil_exists_singlePlace_witness
    (ω : FunctionField.Chart.WeilDifferential K (RatFunc K))
    (hω : FunctionField.Chart.WeilDifferential.IsNonzero ω)
    (hdiv : FunctionField.Chart.WeilDifferential.divOmega ω hω =
      ratFuncCanonicalInfinityDivisor K)
    (p : FunctionField.Chart.PlaceA K (RatFunc K)) :
    ∃ a : FunctionField.Chart.AdeleSpace K (RatFunc K),
      a ∈ FunctionField.Chart.adeleFilt K (RatFunc K)
          (ratFuncCanonicalInfinityDivisor K + Finsupp.single p 1) ∧
      ω.toFun a ≠ 0 ∧
      (∀ v ≠ p, a.1 v = 0) ∧
      FunctionField.Chart.placeValuation K (RatFunc K) p (a.1 p) =
        WithZero.exp (ratFuncCanonicalInfinityDivisor K p + 1) := by
  classical
  let D := ratFuncCanonicalInfinityDivisor K
  let E := D + Finsupp.single p 1
  have hmax :
      FunctionField.Chart.WeilDifferential.divOmega ω hω ∈
          FunctionField.Chart.WeilDifferential.vanishingDivisors ω ∧
        ∀ D' ∈ FunctionField.Chart.WeilDifferential.vanishingDivisors ω,
          D' ≤ FunctionField.Chart.WeilDifferential.divOmega ω hω := by
    simpa only [FunctionField.Chart.WeilDifferential.divOmega] using
      (Classical.choose_spec
        (FunctionField.Chart.WeilDifferential.exists_max_vanishingDivisor
          (k := K) (K := RatFunc K) hω)).1
  rw [hdiv] at hmax
  have hEnot : E ∉
      FunctionField.Chart.WeilDifferential.vanishingDivisors ω := by
    intro hE
    have hle := hmax.2 E hE p
    simp only [E, D, Finsupp.add_apply, Finsupp.single_eq_same] at hle
    omega
  change ¬ ∀ a, a ∈
      FunctionField.Chart.adeleFilt K (RatFunc K) E +
        FunctionField.Chart.diagonalSubmodule K (RatFunc K) →
      ω.toFun a = 0 at hEnot
  push Not at hEnot
  obtain ⟨x, hx, hωx⟩ := hEnot
  rw [Submodule.add_eq_sup] at hx
  rcases Submodule.mem_sup.mp hx with ⟨b, hb, d, hd, hbd⟩
  have hωd : ω.toFun d = 0 := by
    apply hmax.1
    rw [Submodule.add_eq_sup]
    exact Submodule.mem_sup_right hd
  have hωb : ω.toFun b ≠ 0 := by
    intro hzero
    apply hωx
    rw [← hbd, map_add, hzero, hωd, add_zero]
  let a := FunctionField.Chart.adeleUpdate K (RatFunc K)
    (FunctionField.Chart.zeroAdele K (RatFunc K)) p (b.1 p)
  have haE : a ∈ FunctionField.Chart.adeleFilt K (RatFunc K) E := by
    intro v
    by_cases hv : v = p
    · subst v
      simpa [a, FunctionField.Chart.adeleUpdate] using hb p
    · simp [a, FunctionField.Chart.adeleUpdate,
        FunctionField.Chart.zeroAdele, hv]
  have hsubD : b - a ∈
      FunctionField.Chart.adeleFilt K (RatFunc K) D := by
    intro v
    by_cases hv : v = p
    · subst v
      simp [a, FunctionField.Chart.adeleUpdate,
        FunctionField.Chart.zeroAdele]
    · have hbv := hb v
      simpa [E, D, a, FunctionField.Chart.adeleUpdate,
        FunctionField.Chart.zeroAdele, hv] using hbv
  have hωsub : ω.toFun (b - a) = 0 := by
    apply hmax.1
    rw [Submodule.add_eq_sup]
    exact Submodule.mem_sup_left hsubD
  have hωa : ω.toFun a ≠ 0 := by
    intro hzero
    apply hωb
    have hmap := ω.toFun.map_sub b a
    rw [hωsub, hzero, sub_zero] at hmap
    exact hmap.symm
  have haSupport : ∀ v ≠ p, a.1 v = 0 := by
    intro v hv
    simp [a, FunctionField.Chart.adeleUpdate,
      FunctionField.Chart.zeroAdele, hv]
  have hap0 : a.1 p ≠ 0 := by
    intro hzero
    apply hωa
    have haZero : a = 0 := by
      apply Subtype.ext
      funext v
      by_cases hv : v = p
      · subst v
        exact hzero
      · exact haSupport v hv
    rw [haZero, map_zero]
  have haUpper : FunctionField.Chart.placeValuation K (RatFunc K) p (a.1 p) ≤
      WithZero.exp (D p + 1) := by
    have := haE p
    simpa [E, Finsupp.add_apply, Finsupp.single_eq_same] using this
  have haNotLower : ¬ FunctionField.Chart.placeValuation K (RatFunc K) p (a.1 p) ≤
      WithZero.exp (D p) := by
    intro hlower
    apply hωa
    apply hmax.1
    rw [Submodule.add_eq_sup]
    apply Submodule.mem_sup_left
    intro v
    by_cases hv : v = p
    · subst v
      exact hlower
    · simp [haSupport v hv]
  have haLower : WithZero.exp (D p) <
      FunctionField.Chart.placeValuation K (RatFunc K) p (a.1 p) :=
    lt_of_not_ge haNotLower
  let m : ℤ := WithZero.log
    (FunctionField.Chart.placeValuation K (RatFunc K) p (a.1 p))
  have hval0 : FunctionField.Chart.placeValuation K (RatFunc K) p (a.1 p) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hap0
  have hvalExp : WithZero.exp m =
      FunctionField.Chart.placeValuation K (RatFunc K) p (a.1 p) := by
    exact WithZero.exp_log hval0
  have hmLower : D p < m := by
    rw [← hvalExp, WithZero.exp_lt_exp] at haLower
    exact haLower
  have hmUpper : m ≤ D p + 1 := by
    rw [← hvalExp, WithZero.exp_le_exp] at haUpper
    exact haUpper
  have hm : m = D p + 1 := by omega
  refine ⟨a, ?_, hωa, haSupport, ?_⟩
  · simpa only [E, D] using haE
  · rw [← hvalExp, hm]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance detectionConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance detectionConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) detectionPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance detectionPolynomialTower : IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance detectionConstantPolynomialTower : IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance detectionFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.finite K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance detectionFiniteClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance detectionFiniteBaseTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance detectionFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance detectionInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance detectionInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance detectionInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance detectionInfinityClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance detectionInfinityClosureIsDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance detectionInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

/-- A fiber lift supported over one base place lies in an arbitrary divisor
filtration once its common nonzero fiber value satisfies the local bounds. -/
theorem finiteExtensionFiberLift_mem_adeleFilt_of_supported
    (Btop : FunctionField.Chart.DivisorA K L)
    (p : FunctionField.Chart.PlaceA K (RatFunc K))
    (b : FunctionField.Chart.AdeleSpace K (RatFunc K))
    (z : L)
    (hbp : b.1 p = 1)
    (hbAway : ∀ v ≠ p, b.1 v = 0)
    (hz : ∀ q, finiteExtensionUnderPlaceChart K L q = p →
      FunctionField.Chart.placeValuation K L q z ≤
        WithZero.exp (Btop q)) :
    (finiteExtensionFiberLift K L z b).1 ∈
      FunctionField.Chart.adeleFilt K L Btop := by
  intro q
  by_cases hq : finiteExtensionUnderPlaceChart K L q = p
  · change FunctionField.Chart.placeValuation K L q
        (z * algebraMap (RatFunc K) L
          (b.1 (finiteExtensionUnderPlaceChart K L q))) ≤ _
    rw [hq, hbp, map_one, mul_one]
    exact hz q hq
  · change FunctionField.Chart.placeValuation K L q
        (z * algebraMap (RatFunc K) L
          (b.1 (finiteExtensionUnderPlaceChart K L q))) ≤ _
    rw [hbAway _ hq, map_zero, mul_zero, Valuation.map_zero]
    exact zero_le

/-- Normalize a one-component base adele and lift a trace preimage without
changing its cotrace. -/
theorem finiteExtensionFiberLift_normalized_trace
    (ω : FunctionField.Chart.WeilDifferential K (RatFunc K))
    (p : FunctionField.Chart.PlaceA K (RatFunc K))
    (a : FunctionField.Chart.AdeleSpace K (RatFunc K))
    (haNonzero : ω.toFun a ≠ 0)
    (haAway : ∀ v ≠ p, a.1 v = 0)
    (x : RatFunc K) (hx : x = a.1 p) (hx0 : x ≠ 0)
    (z : L) (hzTrace : Algebra.trace (RatFunc K) L z = x) :
    let b := x⁻¹ • a
    (b.1 p = 1) ∧
      (∀ v ≠ p, b.1 v = 0) ∧
      ω.toFun (finiteExtensionFiberTrace K L
        (finiteExtensionFiberLift K L z b)) ≠ 0 := by
  dsimp only
  have hbp : (x⁻¹ • a).1 p = 1 := by
    change x⁻¹ * a.1 p = 1
    rw [← hx, inv_mul_cancel₀ hx0]
  have hbAway : ∀ v ≠ p, (x⁻¹ • a).1 v = 0 := by
    intro v hv
    change x⁻¹ * a.1 v = 0
    rw [haAway v hv, mul_zero]
  refine ⟨hbp, hbAway, ?_⟩
  rw [finiteExtensionFiberTrace_lift K L z (x⁻¹ • a), hzTrace,
    smul_smul, mul_inv_cancel₀ hx0, one_smul]
  exact haNonzero

/-- Step (b1), finite-place branch: any coefficient strictly above the finite
different is detected by the cotrace functional on a fiber-constant adele in
that divisor filtration. -/
theorem finiteExtensionFiberCotrace_detects_finite_excess
    (ω : FunctionField.Chart.WeilDifferential K (RatFunc K))
    (hω : FunctionField.Chart.WeilDifferential.IsNonzero ω)
    (hdiv : FunctionField.Chart.WeilDifferential.divOmega ω hω =
      ratFuncCanonicalInfinityDivisor K)
    (Btop : FunctionField.Chart.DivisorA K L)
    (q₀ : HeightOneSpectrum (RatFuncFiniteIntegralClosure K L))
    (hbad :
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)))
          (finiteExtensionPlaceEquivChart K L (.inl q₀)) <
        Btop (finiteExtensionPlaceEquivChart K L (.inl q₀))) :
    ∃ β : finiteExtensionFiberConstantAdeleSubmodule K L,
      β.1 ∈ FunctionField.Chart.adeleFilt K L Btop ∧
      ω.toFun (finiteExtensionFiberTrace K L β) ≠ 0 := by
  classical
  let e := HeightOneSpectrum.equivOfRingEquiv
    (ratFuncFiniteBaseRingEquivChart K)
  let p₀ : HeightOneSpectrum K[X] := q₀.under K[X]
  let pChart : HeightOneSpectrum
      (FunctionField.ringOfIntegers K (RatFunc K)) := e p₀
  let p : FunctionField.Chart.PlaceA K (RatFunc K) := .inl pChart
  obtain ⟨a, haFilt, hωa, haAway, haVal⟩ :=
    ratFuncCanonicalWeil_exists_singlePlace_witness K ω hω hdiv p
  let x : RatFunc K := a.1 p
  have hpCoeff : ratFuncCanonicalInfinityDivisor K p = 0 := by
    rw [ratFuncCanonicalInfinityDivisor, Finsupp.single_eq_of_ne]
    change Sum.inl pChart ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hx0 : x ≠ 0 := by
    apply (Valuation.ne_zero_iff
      (FunctionField.Chart.placeValuation K (RatFunc K) p)).mp
    rw [show FunctionField.Chart.placeValuation K (RatFunc K) p x =
      WithZero.exp (1 : ℤ) by
        simpa [x, hpCoeff] using haVal]
    exact WithZero.exp_ne_zero
  have hxValChart : pChart.valuation (RatFunc K) x =
      WithZero.exp (1 : ℤ) := by
    simpa [x, p, FunctionField.Chart.placeValuation,
      hpCoeff] using haVal
  have hbaseEq : p₀.valuation (RatFunc K) =
      pChart.valuation (RatFunc K) :=
    heightOneValuation_eq_of_ringEquiv
      (ratFuncFiniteBaseRingEquivChart K)
      (ratFuncFiniteBaseRingEquivChart_algebraMap K)
      p₀ pChart rfl
  have hxVal : p₀.valuation (RatFunc K) x =
      WithZero.exp (1 : ℤ) := by
    rw [hbaseEq]
    exact hxValChart
  let n : HeightOneSpectrum (RatFuncFiniteIntegralClosure K L) → ℤ :=
    fun q => -Btop (finiteExtensionPlaceEquivChart K L (.inl q))
  have hbad' : n q₀ <
      -(multiplicity q₀.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) : ℤ) := by
    have hcoeff :
        (finiteExtensionDivisorEquivChart K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)))
            (finiteExtensionPlaceEquivChart K L (.inl q₀)) =
          (multiplicity q₀.asIdeal
            (differentIdeal K[X]
              (RatFuncFiniteIntegralClosure K L)) : ℤ) := by
      simp [finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply,
        finiteExtensionCanonicalDifferentDivisor_inl]
    rw [hcoeff] at hbad
    dsimp only [n]
    omega
  obtain ⟨z, hz0, hzTrace, hzCount⟩ :=
    exists_trace_eq_of_count_threshold_lt_neg_different
      (A := K[X]) (K₀ := RatFunc K)
      (B := RatFuncFiniteIntegralClosure K L) (L := L)
      p₀ n q₀ rfl hbad' x hx0 hxVal
  let b : FunctionField.Chart.AdeleSpace K (RatFunc K) := x⁻¹ • a
  have hnorm := finiteExtensionFiberLift_normalized_trace
    K L ω p a hωa haAway x rfl hx0 z hzTrace
  have hbp : b.1 p = 1 := by simpa only [b] using hnorm.1
  have hbAway : ∀ v ≠ p, b.1 v = 0 := by
    simpa only [b] using hnorm.2.1
  let β := finiteExtensionFiberLift K L z b
  have hβFilt : β.1 ∈ FunctionField.Chart.adeleFilt K L Btop := by
    apply finiteExtensionFiberLift_mem_adeleFilt_of_supported
      K L Btop p b z hbp hbAway
    intro q hq
    let Q := (finiteExtensionPlaceEquivChart K L).symm q
    have hQq : finiteExtensionPlaceEquivChart K L Q = q :=
      (finiteExtensionPlaceEquivChart K L).apply_symm_apply q
    rcases Q with r | P
    · have hrUnder : r.under K[X] = p₀ := by
        rw [← hQq] at hq
        change ratFuncExhaustivePlaceEquivChart K
            (.inl (r.under K[X])) = .inl pChart at hq
        change Sum.inl (e (r.under K[X])) = Sum.inl (e p₀) at hq
        exact e.injective (Sum.inl.inj hq)
      have hrCount := hzCount r hrUnder
      have hrVal : r.valuation L z ≤
          WithZero.exp
            (Btop (finiteExtensionPlaceEquivChart K L (.inl r))) := by
        rw [valuation_eq_exp_neg_finitePlaceOrder r z hz0,
          WithZero.exp_le_exp]
        change -FractionalIdeal.count L r
            (FractionalIdeal.spanSingleton
              (RatFuncFiniteIntegralClosure K L)⁰ z) ≤ _
        dsimp only [n] at hrCount
        omega
      rw [← hQq]
      simpa [FunctionField.Chart.placeValuation,
        finiteExtensionPlaceEquivChart] using hrVal
    · rw [← hQq] at hq
      change ratFuncExhaustivePlaceEquivChart K
          (.inr (ratFuncInfinityPlace K)) = .inl pChart at hq
      change Sum.inr _ = Sum.inl pChart at hq
      cases hq
  refine ⟨β, hβFilt, ?_⟩
  simpa only [β, b] using hnorm.2.2

/-- Step (b1), infinity-place branch: after compensating the `-2e` term by
the square of the base infinity uniformizer, any coefficient strictly above
the infinity different is detected by cotrace. -/
theorem finiteExtensionFiberCotrace_detects_infinity_excess
    (ω : FunctionField.Chart.WeilDifferential K (RatFunc K))
    (hω : FunctionField.Chart.WeilDifferential.IsNonzero ω)
    (hdiv : FunctionField.Chart.WeilDifferential.divOmega ω hω =
      ratFuncCanonicalInfinityDivisor K)
    (Btop : FunctionField.Chart.DivisorA K L)
    (P₀ : FiniteExtensionInfinityPlace K L)
    (hbad :
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)))
          (finiteExtensionPlaceEquivChart K L (.inr P₀)) <
        Btop (finiteExtensionPlaceEquivChart K L (.inr P₀))) :
    ∃ β : finiteExtensionFiberConstantAdeleSubmodule K L,
      β.1 ∈ FunctionField.Chart.adeleFilt K L Btop ∧
      ω.toFun (finiteExtensionFiberTrace K L β) ≠ 0 := by
  classical
  let pInf := ratFuncInfinityPlace K
  let e := HeightOneSpectrum.equivOfRingEquiv
    (ratFuncInfinityBaseRingEquivChart K)
  let pChart : HeightOneSpectrum
      (FunctionField.Chart.infiniteIntegers K (RatFunc K)) := e pInf
  let p : FunctionField.Chart.PlaceA K (RatFunc K) := .inr pChart
  have hpBase : p = ratFuncInfinityPlaceChart K := by rfl
  have hpCanonical : p = ratFuncInfinityChartPlace K :=
    hpBase.trans (ratFuncInfinityChartPlace_eq_baseChart K).symm
  obtain ⟨a, haFilt, hωa, haAway, haVal⟩ :=
    ratFuncCanonicalWeil_exists_singlePlace_witness K ω hω hdiv p
  have hpCoeff : ratFuncCanonicalInfinityDivisor K p = -2 := by
    rw [hpCanonical, ratFuncCanonicalInfinityDivisor,
      Finsupp.single_eq_same]
  let x : RatFunc K := a.1 p
  have hx0 : x ≠ 0 := by
    apply (Valuation.ne_zero_iff
      (FunctionField.Chart.placeValuation K (RatFunc K) p)).mp
    rw [show FunctionField.Chart.placeValuation K (RatFunc K) p x =
      WithZero.exp (-1 : ℤ) by
        simpa [x, hpCoeff] using haVal]
    exact WithZero.exp_ne_zero
  have hxValChart : pChart.valuation (RatFunc K) x =
      WithZero.exp (-1 : ℤ) := by
    simpa [x, p, FunctionField.Chart.placeValuation,
      hpCoeff] using haVal
  have hbaseEq : pInf.valuation (RatFunc K) =
      pChart.valuation (RatFunc K) :=
    heightOneValuation_eq_of_ringEquiv
      (ratFuncInfinityBaseRingEquivChart K)
      (ratFuncInfinityBaseRingEquivChart_algebraMap K)
      pInf pChart rfl
  have hxValInf : pInf.valuation (RatFunc K) x =
      WithZero.exp (-1 : ℤ) := by
    rw [hbaseEq]
    exact hxValChart
  let s := ratFuncInfinityUniformizer K
  have hs : s ≠ 0 := by
    intro h
    have hcoe := congrArg Subtype.val h
    exact (one_div_ne_zero RatFunc.X_ne_zero) hcoe
  let t : RatFunc K := algebraMap (RatFuncInfinityIntegers K) (RatFunc K) s
  have ht0 : t ≠ 0 := by
    simpa only [t, map_zero] using
      (FaithfulSMul.algebraMap_injective
        (RatFuncInfinityIntegers K) (RatFunc K)).ne hs
  have htVal : pInf.valuation (RatFunc K) t =
      WithZero.exp (-1 : ℤ) := by
    change pInf.valuation (RatFunc K)
      (algebraMap (RatFuncInfinityIntegers K) (RatFunc K) s) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact pInf.intValuation_singleton hs
      (ratFuncInfinityPlace_span_uniformizer K)
  let w : RatFunc K := (t ^ 2)⁻¹ * x
  have hw0 : w ≠ 0 :=
    mul_ne_zero (inv_ne_zero (pow_ne_zero 2 ht0)) hx0
  have hwVal : pInf.valuation (RatFunc K) w =
      WithZero.exp (1 : ℤ) := by
    change pInf.valuation (RatFunc K) ((t ^ 2)⁻¹ * x) = _
    rw [map_mul, map_inv₀, map_pow, htVal, hxValInf]
    norm_num [← WithZero.exp_neg, ← WithZero.exp_add]
  let q₀ : HeightOneSpectrum (RatFuncInfinityIntegralClosure K L) :=
    primeOverHeightOne pInf P₀
  have hq₀Under : q₀.under (RatFuncInfinityIntegers K) = pInf := by
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def P₀.1 pInf.asIdeal).symm
  let n : HeightOneSpectrum (RatFuncInfinityIntegralClosure K L) → ℤ :=
    fun q =>
      -2 * ((((finiteExtensionInfinityPrimesOverEquivHeightOne K L).symm q).1.ramificationIdx
          (RatFuncInfinityIntegers K)) : ℤ) -
        Btop (finiteExtensionPlaceEquivChart K L
          (.inr ((finiteExtensionInfinityPrimesOverEquivHeightOne K L).symm q)))
  have hbad' : n q₀ <
      -(multiplicity q₀.asIdeal
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) : ℤ) := by
    have hcoeff :
        (finiteExtensionDivisorEquivChart K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L)))
            (finiteExtensionPlaceEquivChart K L (.inr P₀)) =
          (multiplicity P₀.1
            (differentIdeal (RatFuncInfinityIntegers K)
              (RatFuncInfinityIntegralClosure K L)) : ℤ) -
            2 * (P₀.1.ramificationIdx
              (RatFuncInfinityIntegers K) : ℤ) := by
      simp [finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply,
        finiteExtensionCanonicalDifferentDivisor_inr]
    rw [hcoeff] at hbad
    have hsymm :
        (finiteExtensionInfinityPrimesOverEquivHeightOne K L).symm q₀ = P₀ := by
      exact (finiteExtensionInfinityPrimesOverEquivHeightOne K L).symm_apply_apply P₀
    have hqIdeal : q₀.asIdeal = P₀.1 := rfl
    dsimp only [n]
    rw [hsymm, hqIdeal]
    omega
  obtain ⟨z₀, hz₀0, hz₀Trace, hz₀Count⟩ :=
    exists_trace_eq_of_count_threshold_lt_neg_different
      (A := RatFuncInfinityIntegers K) (K₀ := RatFunc K)
      (B := RatFuncInfinityIntegralClosure K L) (L := L)
      pInf n q₀ hq₀Under hbad' w hw0 hwVal
  let tL : L := algebraMap (RatFuncInfinityIntegers K) L s
  have htL0 : tL ≠ 0 := by
    simpa only [tL, map_zero] using
      (FaithfulSMul.algebraMap_injective
        (RatFuncInfinityIntegers K) L).ne hs
  have htTower : tL = algebraMap (RatFunc K) L t := by
    exact (IsScalarTower.algebraMap_apply
      (RatFuncInfinityIntegers K) (RatFunc K) L s).symm
  let z : L := tL ^ 2 * z₀
  have hz0 : z ≠ 0 := mul_ne_zero (pow_ne_zero 2 htL0) hz₀0
  have hzTrace : Algebra.trace (RatFunc K) L z = x := by
    have hscalar : tL ^ 2 * z₀ = (t ^ 2) • z₀ := by
      rw [Algebra.smul_def, htTower, map_pow]
    change Algebra.trace (RatFunc K) L (tL ^ 2 * z₀) = x
    rw [hscalar, map_smul, hz₀Trace]
    change t ^ 2 * ((t ^ 2)⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ht0), one_mul]
  let b : FunctionField.Chart.AdeleSpace K (RatFunc K) := x⁻¹ • a
  have hnorm := finiteExtensionFiberLift_normalized_trace
    K L ω p a hωa haAway x rfl hx0 z hzTrace
  have hbp : b.1 p = 1 := by simpa only [b] using hnorm.1
  have hbAway : ∀ v ≠ p, b.1 v = 0 := by
    simpa only [b] using hnorm.2.1
  let β := finiteExtensionFiberLift K L z b
  have hβFilt : β.1 ∈ FunctionField.Chart.adeleFilt K L Btop := by
    apply finiteExtensionFiberLift_mem_adeleFilt_of_supported
      K L Btop p b z hbp hbAway
    intro q hq
    let Q := (finiteExtensionPlaceEquivChart K L).symm q
    have hQq : finiteExtensionPlaceEquivChart K L Q = q :=
      (finiteExtensionPlaceEquivChart K L).apply_symm_apply q
    rcases Q with r | P
    · rw [← hQq] at hq
      change ratFuncExhaustivePlaceEquivChart K
          (.inl (r.under K[X])) = p at hq
      rw [hpBase] at hq
      change Sum.inl _ = Sum.inr _ at hq
      cases hq
    · let qH : HeightOneSpectrum
          (RatFuncInfinityIntegralClosure K L) :=
        primeOverHeightOne pInf P
      have hqHUnder : qH.under (RatFuncInfinityIntegers K) = pInf := by
        apply HeightOneSpectrum.ext
        exact (Ideal.over_def P.1 pInf.asIdeal).symm
      letI : qH.asIdeal.LiesOver pInf.asIdeal := ⟨by
        have hideal := congrArg HeightOneSpectrum.asIdeal hqHUnder
        exact hideal.symm⟩
      have hqCount := hz₀Count qH hqHUnder
      have hsymm :
          (finiteExtensionInfinityPrimesOverEquivHeightOne K L).symm qH = P := by
        exact (finiteExtensionInfinityPrimesOverEquivHeightOne K L).symm_apply_apply P
      have hqCount' :
          -2 * (P.1.ramificationIdx
              (RatFuncInfinityIntegers K) : ℤ) -
              Btop (finiteExtensionPlaceEquivChart K L (.inr P)) ≤
            finitePlaceOrder qH z₀ := by
        simpa only [n, hsymm, finitePlaceOrder] using hqCount
      have htOrder : finitePlaceOrder qH tL =
          (qH.asIdeal.ramificationIdx
            (RatFuncInfinityIntegers K) : ℤ) := by
        simpa only [tL, IsScalarTower.algebraMap_apply
          (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L) L] using
          finitePlaceOrder_algebraMap_uniformizer_eq_ramificationIdx
            (R := RatFuncInfinityIntegers K)
            (A := RatFuncInfinityIntegralClosure K L) (F := L)
            pInf qH s hs (ratFuncInfinityPlace_span_uniformizer K)
      have htSquareOrder :=
        finitePlaceOrder_mul_eq_add qH tL tL htL0 htL0
      rw [← pow_two] at htSquareOrder
      have hzOrder := finitePlaceOrder_mul_eq_add qH (tL ^ 2) z₀
        (pow_ne_zero 2 htL0) hz₀0
      have hideal : qH.asIdeal = P.1 := rfl
      have horderBound : -finitePlaceOrder qH z ≤
          Btop (finiteExtensionPlaceEquivChart K L (.inr P)) := by
        dsimp only [z]
        rw [hzOrder, htSquareOrder, htOrder, hideal]
        omega
      have hval : qH.valuation L z ≤
          WithZero.exp
            (Btop (finiteExtensionPlaceEquivChart K L (.inr P))) := by
        rw [valuation_eq_exp_neg_finitePlaceOrder qH z hz0,
          WithZero.exp_le_exp]
        exact horderBound
      rw [← hQq]
      have hvaluationEq :
          qH.valuation L z =
            FunctionField.Chart.placeValuation K L
              (finiteExtensionPlaceEquivChart K L (.inr P)) z := by
        simpa only [finiteExtensionPlaceValuation] using
          congrArg (fun v : Valuation L ℤᵐ⁰ => v z)
            (finiteExtensionPlaceValuation_eq_chart K L (.inr P))
      rw [← hvaluationEq]
      exact hval
  refine ⟨β, hβFilt, ?_⟩
  simpa only [β, b] using hnorm.2.2

/-- Stichtenoth, Theorem 3.4.6, Step (b1), in the project chart model: every
divisor not bounded by the explicit canonical different is detected by the
base canonical functional after cotrace. -/
theorem finiteExtensionFiberCotrace_detects_not_le
    (ω : FunctionField.Chart.WeilDifferential K (RatFunc K))
    (hω : FunctionField.Chart.WeilDifferential.IsNonzero ω)
    (hdiv : FunctionField.Chart.WeilDifferential.divOmega ω hω =
      ratFuncCanonicalInfinityDivisor K)
    (Btop : FunctionField.Chart.DivisorA K L)
    (hB : ¬ Btop ≤
      finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) :
    ∃ β : finiteExtensionFiberConstantAdeleSubmodule K L,
      β.1 ∈ FunctionField.Chart.adeleFilt K L Btop ∧
      ω.toFun (finiteExtensionFiberTrace K L β) ≠ 0 := by
  classical
  have hB' : ∃ q : FunctionField.Chart.PlaceA K L,
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) q < Btop q := by
    by_contra hnone
    apply hB
    intro q
    have hnot : ¬
        (finiteExtensionDivisorEquivChart K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) q < Btop q := by
      intro hlt
      exact hnone ⟨q, hlt⟩
    exact le_of_not_gt hnot
  obtain ⟨q, hq⟩ := hB'
  let Q := (finiteExtensionPlaceEquivChart K L).symm q
  have hQq : finiteExtensionPlaceEquivChart K L Q = q :=
    (finiteExtensionPlaceEquivChart K L).apply_symm_apply q
  rcases Q with r | P
  · apply finiteExtensionFiberCotrace_detects_finite_excess
      K L ω hω hdiv Btop r
    simpa only [hQq] using hq
  · apply finiteExtensionFiberCotrace_detects_infinity_excess
      K L ω hω hdiv Btop P
    simpa only [hQq] using hq

/-- The trace-different divisor is exactly the maximal vanishing divisor of
the Weil functional obtained by gluing cotrace to zero.  This is the direct
local-maximality conclusion of Stichtenoth, Theorem 3.4.6, Step (b1), and does
not assume a Riemann--Hurwitz degree identity. -/
theorem finiteExtensionCanonicalDifferent_isCanonical_of_cotrace
    [FunctionField.IsFullConstantField K L] :
    FunctionField.Chart.IsCanonical K L
      (finiteExtensionDivisorEquivChart K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) := by
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
  have hωTop : FunctionField.Chart.WeilDifferential.IsNonzero ωTop := hgNe
  have hDvan : D ∈
      FunctionField.Chart.WeilDifferential.vanishingDivisors ωTop := by
    intro a ha
    exact LinearMap.mem_ker.mp (hgV ha)
  have hDmax : ∀ B ∈
      FunctionField.Chart.WeilDifferential.vanishingDivisors ωTop,
      B ≤ D := by
    intro B hBvan
    by_contra hBle
    obtain ⟨β, hβFilt, hdetect⟩ :=
      finiteExtensionFiberCotrace_detects_not_le
        K L ωBase hωBase hdivBase B hBle
    have hβsum : β.1 ∈ FunctionField.Chart.adeleFilt K L B +
        FunctionField.Chart.diagonalSubmodule K L := by
      rw [Submodule.add_eq_sup]
      exact Submodule.mem_sup_left hβFilt
    have hgβ0 : g β.1 = 0 := hBvan β.1 hβsum
    have hgfβ : g β.1 = f β := by
      change (g.comp U.subtype) β = f β
      exact LinearMap.congr_fun hgU β
    have hfβ : f β ≠ 0 := by
      simpa only [f, LinearMap.coe_comp, Function.comp_apply] using hdetect
    exact hfβ (hgfβ.symm.trans hgβ0)
  have hmaxTop :
      FunctionField.Chart.WeilDifferential.divOmega ωTop hωTop ∈
          FunctionField.Chart.WeilDifferential.vanishingDivisors ωTop ∧
        ∀ B ∈ FunctionField.Chart.WeilDifferential.vanishingDivisors ωTop,
          B ≤ FunctionField.Chart.WeilDifferential.divOmega ωTop hωTop := by
    simpa only [FunctionField.Chart.WeilDifferential.divOmega] using
      (Classical.choose_spec
        (FunctionField.Chart.WeilDifferential.exists_max_vanishingDivisor
          (k := K) (K := L) hωTop)).1
  have heq : FunctionField.Chart.WeilDifferential.divOmega ωTop hωTop = D :=
    le_antisymm (hDmax _ hmaxTop.1) (hmaxTop.2 D hDvan)
  exact ⟨ωTop, hωTop, heq⟩

/-- The remaining trace-residue lower bound follows from the direct cotrace
canonicality theorem, with no degree premise. -/
theorem finiteExtension_genus_le_canonicalDifferent_finrank_of_cotrace
    [FunctionField.IsFullConstantField K L] :
    FunctionField.Chart.genus K L ≤
      Module.finrank K
        (finiteExtensionRiemannSpace K L
          (finiteExtensionCanonicalDifferentDivisor K L
            (finiteExtensionFiniteDifferentIdeal_ne_bot K L))) := by
  have hcanonical := finiteExtensionCanonicalDifferent_isCanonical_of_cotrace K L
  have hcharacterization :=
    (finiteExtensionCanonicalDifferent_isCanonical_iff_degree_finrank K L).mp
      hcanonical
  exact hcharacterization.2.ge

/-- Any upper bound for the explicit different degree gives the corresponding
genus bound directly from cotrace canonicality. -/
theorem finiteExtension_genus_le_budget_of_cotrace
    [FunctionField.IsFullConstantField K L]
    (budget : ℕ)
    (hdegree : finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) ≤
      2 * (budget : ℤ) - 2) :
    FunctionField.genus K L ≤ budget := by
  exact finiteExtension_genus_le_budget_of_canonicalDifferent_isCanonical
    K L budget
      (finiteExtensionCanonicalDifferent_isCanonical_of_cotrace K L)
      hdegree

end

end BGS.HasseWeil
