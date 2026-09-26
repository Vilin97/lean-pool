/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DegreeTermCount
public import Mathlib.Algebra.Group.Irreducible.Defs

/-!
# Factorisation after removing finite-support divisors

This module proves the conditional core of LM24, Proposition 5.6.1. A Hahn series with no
nonunit finite-support divisor factors into a nonzero scalar and a finite list of irreducible
series with infinite support. Well-founded induction on degree gives the factorisation, while
additivity of the uncompressed Cantor term count gives the sharp numerical upper bound.

For an arbitrary nonzero series `b`, division by its normalized maximal finite-support divisor
`p(b)` produces a residual with the required divisor property. The resulting theorem retains
the nonzeroness of the scalar, although the printed proposition does not state that consequence.

Pairwise greatest-common-divisor existence and the classification of units in the
finite-support ring remain explicit hypotheses. They are not hidden in instances. The coefficient
field has characteristic zero.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- A Hahn series has only unit finite-support divisors. This is the intrinsic property of the
residual after removing its maximal finite-support divisor. -/
def HasOnlyUnitFiniteSupportDivisors (b : Series K) : Prop :=
  ∀ p : FiniteSupportRing (K := K), (p : Series K) ∣ b → IsUnit p

omit [CharZero K] in
/-- Characterization of having only unit finite-support divisors. -/
theorem hasOnlyUnitFiniteSupportDivisors_iff (b : Series K) :
    HasOnlyUnitFiniteSupportDivisors b ↔
      ∀ p : FiniteSupportRing (K := K), (p : Series K) ∣ b → IsUnit p :=
  Iff.rfl

omit [CharZero K] in
/-- Every divisor of a series with only unit finite-support divisors has the same property. -/
theorem HasOnlyUnitFiniteSupportDivisors.of_dvd
    {b c : Series K} (hb : HasOnlyUnitFiniteSupportDivisors b) (hcb : c ∣ b) :
    HasOnlyUnitFiniteSupportDivisors c := by
  intro p hpc
  exact hb p (dvd_trans hpc hcb)

omit [CharZero K] in
private theorem series_coe_ne_zero {b : Series K} (hb : b ≠ 0) :
    (b : K⟦ℝ⟧) ≠ 0 := by
  intro hzero
  apply hb
  exact Subtype.ext hzero

omit [CharZero K] in
/-- A nonunit series with only unit finite-support divisors has infinite support. -/
theorem HasOnlyUnitFiniteSupportDivisors.support_infinite_of_not_isUnit
    {b : Series K} (hb : HasOnlyUnitFiniteSupportDivisors b)
    (hbUnit : ¬IsUnit b) :
    (b : K⟦ℝ⟧).support.Infinite := by
  by_contra hInfinite
  have hFinite : (b : K⟦ℝ⟧).support.Finite := Set.not_infinite.mp hInfinite
  let p : FiniteSupportRing (K := K) := ⟨b, by
    rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff]
    exact hFinite⟩
  have hpDvd : (p : Series K) ∣ b := ⟨1, by simp [p]⟩
  have hpUnit : IsUnit p := hb p hpDvd
  apply hbUnit
  change IsUnit (p : Series K)
  exact hpUnit.map
    (HahnSeries.Nonpositive.finiteSupportSubring
      (G := ℝ) (K := K)).subtype

/-- A nonzero series with only unit finite-support divisors factors into a nonzero scalar and
irreducible infinite-support series, with the number of factors bounded by the Cantor term count
of its degree. -/
theorem HasOnlyUnitFiniteSupportDivisors.exists_factorization
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ k : K, k ≠ 0 ∧
        p = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    {b : Series K} (hb : b ≠ 0)
    (hbPrimitive : HasOnlyUnitFiniteSupportDivisors b) :
    ∃ (k : K) (factors : List (Series K)),
      k ≠ 0 ∧ b = HahnSeries.Nonpositive.C k * factors.prod ∧
        (∀ c ∈ factors,
          Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
        factors.length ≤ HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) := by
  classical
  let wf : WellFounded (Function.onFun (fun α β : WithBot NatOrdinal ↦ α < β)
      (fun c : Series K ↦ (c : K⟦ℝ⟧).degree)) :=
    wellFounded_lt.onFun
  refine wf.induction
    (C := fun b ↦ b ≠ 0 → HasOnlyUnitFiniteSupportDivisors b →
      ∃ (k : K) (factors : List (Series K)),
        k ≠ 0 ∧ b = HahnSeries.Nonpositive.C k * factors.prod ∧
          (∀ c ∈ factors,
            Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
          factors.length ≤
            HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧)) b ?_ hb hbPrimitive
  intro b ih hb hbPrimitive
  by_cases hbDegree : (b : K⟦ℝ⟧).degree ≤ 0
  · have hbFinite : (b : K⟦ℝ⟧).support.Finite :=
      HahnSeries.degree_le_zero_iff.mp hbDegree
    let p : FiniteSupportRing (K := K) := ⟨b, by
      rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff]
      exact hbFinite⟩
    have hpDvd : (p : Series K) ∣ b := ⟨1, by simp [p]⟩
    obtain ⟨k, hk, hpk⟩ := (hunits p).mp (hbPrimitive p hpDvd)
    refine ⟨k, [], hk, ?_, ?_, ?_⟩
    · rw [List.prod_nil, mul_one]
      apply Subtype.ext
      simpa only [p, HahnSeries.Nonpositive.coe_C,
        HahnSeries.Nonpositive.coe_finiteSupportScalarHom] using congrArg
          (fun q : FiniteSupportRing (K := K) ↦
            ((q : Series K) : K⟦ℝ⟧)) hpk
    · simp
    · simp
  · have hbDegreePos : 0 < (b : K⟦ℝ⟧).degree := lt_of_not_ge hbDegree
    have hbNotUnit : ¬IsUnit b := by
      intro hbUnit
      exact (not_le_of_gt hbDegreePos)
        (HahnSeries.Nonpositive.degree_eq_zero_of_isUnit
          HahnSeries.Nonpositive.degree_mul hbUnit).le
    rcases irreducible_or_factor hbNotUnit with hbIrreducible | ⟨c, d, hcUnit, hdUnit, hfactor⟩
    · refine ⟨1, [b], one_ne_zero, ?_, ?_, ?_⟩
      · simp
      · simp only [List.mem_singleton, forall_eq]
        exact ⟨hbIrreducible,
          HahnSeries.degree_pos_iff_support_infinite.mp hbDegreePos⟩
      · exact HahnSeries.degreeCantorTermCount_pos_of_degree_pos hbDegreePos
    · have hc : c ≠ 0 := by
        intro hc
        apply hb
        rw [hfactor, hc, zero_mul]
      have hd : d ≠ 0 := by
        intro hd
        apply hb
        rw [hfactor, hd, mul_zero]
      have hcPrimitive := hbPrimitive.of_dvd ⟨d, hfactor⟩
      have hdPrimitive := hbPrimitive.of_dvd ⟨c, by
        rw [mul_comm]
        exact hfactor⟩
      have hcInfinite := hcPrimitive.support_infinite_of_not_isUnit hcUnit
      have hdInfinite := hdPrimitive.support_infinite_of_not_isUnit hdUnit
      have hcDegreePos : 0 < (c : K⟦ℝ⟧).degree :=
        HahnSeries.degree_pos_iff_support_infinite.mpr hcInfinite
      have hdDegreePos : 0 < (d : K⟦ℝ⟧).degree :=
        HahnSeries.degree_pos_iff_support_infinite.mpr hdInfinite
      have hcDegreeLt : (c : K⟦ℝ⟧).degree < (b : K⟦ℝ⟧).degree := by
        calc
          (c : K⟦ℝ⟧).degree <
              (c : K⟦ℝ⟧).degree + (d : K⟦ℝ⟧).degree :=
            calc
              (c : K⟦ℝ⟧).degree =
                  (c : K⟦ℝ⟧).degree + 0 := (add_zero _).symm
              _ < (c : K⟦ℝ⟧).degree + (d : K⟦ℝ⟧).degree :=
                WithBot.add_lt_add_left
                  (HahnSeries.degree_eq_bot.not.mpr (series_coe_ne_zero hc))
                  hdDegreePos
          _ = ((c * d : Series K) : K⟦ℝ⟧).degree :=
            (HahnSeries.Nonpositive.degree_mul c d).symm
          _ = (b : K⟦ℝ⟧).degree := congrArg
            (fun q : Series K ↦ (q : K⟦ℝ⟧).degree) hfactor.symm
      have hdDegreeLt : (d : K⟦ℝ⟧).degree < (b : K⟦ℝ⟧).degree := by
        calc
          (d : K⟦ℝ⟧).degree <
              (c : K⟦ℝ⟧).degree + (d : K⟦ℝ⟧).degree :=
            calc
              (d : K⟦ℝ⟧).degree =
                  0 + (d : K⟦ℝ⟧).degree := (zero_add _).symm
              _ < (c : K⟦ℝ⟧).degree + (d : K⟦ℝ⟧).degree :=
                WithBot.add_lt_add_right
                  (HahnSeries.degree_eq_bot.not.mpr (series_coe_ne_zero hd))
                  hcDegreePos
          _ = ((c * d : Series K) : K⟦ℝ⟧).degree :=
            (HahnSeries.Nonpositive.degree_mul c d).symm
          _ = (b : K⟦ℝ⟧).degree := congrArg
            (fun q : Series K ↦ (q : K⟦ℝ⟧).degree) hfactor.symm
      obtain ⟨kc, cs, hkc, hcFactor, hcs, hcsBound⟩ :=
        ih c hcDegreeLt hc hcPrimitive
      obtain ⟨kd, ds, hkd, hdFactor, hds, hdsBound⟩ :=
        ih d hdDegreeLt hd hdPrimitive
      refine ⟨kc * kd, cs ++ ds, mul_ne_zero hkc hkd, ?_, ?_, ?_⟩
      · rw [hfactor, hcFactor, hdFactor, List.prod_append,
          map_mul, mul_assoc]
        ring
      · intro q hq
        rw [List.mem_append] at hq
        exact hq.elim (hcs q) (hds q)
      · rw [List.length_append]
        calc
          cs.length + ds.length ≤
              HahnSeries.degreeCantorTermCount (c : K⟦ℝ⟧) +
                HahnSeries.degreeCantorTermCount (d : K⟦ℝ⟧) :=
            Nat.add_le_add hcsBound hdsBound
          _ = HahnSeries.degreeCantorTermCount ((c * d : Series K) : K⟦ℝ⟧) := by
            symm
            apply HahnSeries.degreeCantorTermCount_mul
            · simpa using HahnSeries.Nonpositive.degree_mul c d
            · exact series_coe_ne_zero hc
            · exact series_coe_ne_zero hd
          _ = HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) := by
            rw [← hfactor]

/-- Dividing a nonzero series by its normalized maximal finite-support divisor leaves only unit
finite-support divisors. -/
theorem hasOnlyUnitFiniteSupportDivisors_residual (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {b q : Series K} (hb : b ≠ 0)
    (hq : b =
      (seriesNormalizedMaximalFiniteSupportDivisor b : Series K) * q) :
    HasOnlyUnitFiniteSupportDivisors q := by
  let p := seriesNormalizedMaximalFiniteSupportDivisor b
  have hpSpec := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff b p).mp
    (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b)
  have hpNe : p ≠ 0 :=
    (seriesNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hb).ne_zero
  intro r hrq
  obtain ⟨s, hs⟩ := hrq
  let pr : FiniteSupportRing (K := K) := p * r
  have hprDvdB : (pr : Series K) ∣ b := by
    refine ⟨s, ?_⟩
    rw [hq, hs]
    simp only [pr, p, Subring.coe_mul, mul_assoc]
  have hprDvdP : pr ∣ p := (hpSpec.1 pr).mp hprDvdB
  obtain ⟨t, ht⟩ := hprDvdP
  apply isUnit_iff_exists.mpr
  have hrt : r * t = 1 := by
    apply mul_left_cancel₀ hpNe
    calc
      p * (r * t) = (p * r) * t := (mul_assoc _ _ _).symm
      _ = p := ht.symm
      _ = p * 1 := (mul_one p).symm
  exact ⟨t, hrt, by simpa only [mul_comm] using hrt⟩

/-- Conditional strengthened form of LM24, Proposition 5.6.1, retaining that the scalar is
nonzero. -/
theorem exists_series_infinite_support_factorization_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ p : FiniteSupportRing (K := K),
      IsUnit p ↔ ∃ k : K, k ≠ 0 ∧
        p = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    {b : Series K} (hb : b ≠ 0) :
    ∃ (k : K) (factors : List (Series K)),
      k ≠ 0 ∧
        b = HahnSeries.Nonpositive.C k *
          (seriesNormalizedMaximalFiniteSupportDivisor b : Series K) *
            factors.prod ∧
        (∀ c ∈ factors,
          Irreducible c ∧ (c : K⟦ℝ⟧).support.Infinite) ∧
        factors.length ≤ HahnSeries.degreeCantorTermCount (b : K⟦ℝ⟧) := by
  let p := seriesNormalizedMaximalFiniteSupportDivisor b
  have hpDvd : (p : Series K) ∣ b :=
    seriesNormalizedMaximalFiniteSupportDivisor_dvd_of_exists_gcd hgcd b
  obtain ⟨q, hq⟩ := hpDvd
  have hqNe : q ≠ 0 := by
    intro hzero
    apply hb
    rw [hq, hzero, mul_zero]
  have hqPrimitive : HasOnlyUnitFiniteSupportDivisors q :=
    hasOnlyUnitFiniteSupportDivisors_residual hgcd hb hq
  obtain ⟨k, factors, hk, hqFactor, hfactors, hbound⟩ :=
    hqPrimitive.exists_factorization hunits hqNe
  refine ⟨k, factors, hk, ?_, hfactors, ?_⟩
  · change b = HahnSeries.Nonpositive.C k * (p : Series K) * factors.prod
    rw [hq, hqFactor]
    ring
  · apply hbound.trans_eq
    apply HahnSeries.degreeCantorTermCount_congr
    rw [hq, HahnSeries.Nonpositive.degree_mul]
    have hpNe : p ≠ 0 :=
      (seriesNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hb).ne_zero
    have hpSeriesNe : (p : Series K) ≠ 0 := by
      intro hzero
      exact hpNe (Subtype.ext hzero)
    have hpHahnNe : (p : K⟦ℝ⟧) ≠ 0 :=
      series_coe_ne_zero hpSeriesNe
    rw [HahnSeries.degree_eq_zero.mpr ⟨hpHahnNe,
      (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff (p : Series K)).mp p.2⟩,
      zero_add]

end

end Berarducci
