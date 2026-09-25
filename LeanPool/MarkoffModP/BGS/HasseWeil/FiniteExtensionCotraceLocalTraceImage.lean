/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentCotrace
public import LeanPool.MarkoffModP.BGS.HasseWeil.FinitePlaceApproximation

/-!
# Local trace image for cotrace maximality

This file formalizes the exact local trace-image argument in Stichtenoth,
Theorem 3.4.6, Step (b1).  Weak approximation creates an element just outside
the complementary module at an offending extension place; trace duality then
shows that any prescribed base element of order `-1` is a trace without losing
the required lower bounds at the places over the chosen base place.
-/

@[expose] public section

namespace BGS.HasseWeil

open Set Function UniqueFactorizationMonoid IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

noncomputable section

universe u

variable (A K₀ : Type*) {L : Type u} {B : Type*}
variable [CommRing A] [Field K₀] [CommRing B] [Field L]
variable [Algebra A K₀] [Algebra B L] [Algebra A B] [Algebra K₀ L] [Algebra A L]
variable [IsScalarTower A K₀ L] [IsScalarTower A B L]
variable [IsDedekindDomain A] [IsFractionRing A K₀]
variable [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
variable [IsIntegralClosure B A L] [IsFractionRing B L]
variable [IsDedekindDomain B]
variable [Module.IsTorsionFree A B]
variable [Algebra.IsIntegral A B]

/-- Rebuild a height-one prime from an ideal in the finite primes-over set. -/
def heightOneOfPrimesOverFinset (p : HeightOneSpectrum A)
    (Q : Ideal B) (hQ : Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal B) :
    HeightOneSpectrum B := by
  have hQover : Q ∈ p.asIdeal.primesOver B :=
    (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot B).mp hQ
  exact ⟨Q, hQover.1,
    Ideal.ne_bot_of_mem_primesOver p.ne_bot hQover⟩

omit [Algebra.IsIntegral A B] in
@[simp]
theorem heightOneOfPrimesOverFinset_asIdeal (p : HeightOneSpectrum A)
    (Q : Ideal B) (hQ : Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal B) :
    (heightOneOfPrimesOverFinset (B := B) A p Q hQ).asIdeal = Q := rfl

/-- Membership in the finite primes-over set is equivalent to contraction to
the selected height-one prime. -/
theorem mem_primesOverFinset_iff_under_eq (p : HeightOneSpectrum A)
    (q : HeightOneSpectrum B) :
    q.asIdeal ∈ IsDedekindDomain.primesOverFinset p.asIdeal B ↔
      q.under A = p := by
  rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot B]
  constructor
  · rintro ⟨_, h⟩
    apply HeightOneSpectrum.ext
    rw [Ideal.liesOver_iff] at h
    exact h.symm
  · intro h
    refine ⟨q.isPrime, ?_⟩
    rw [Ideal.liesOver_iff]
    exact (congrArg HeightOneSpectrum.asIdeal h).symm

omit [Algebra.IsIntegral A B] in
/-- Every ideal selected by `primesOverFinset` is prime in the factorization
monoid sense required by the weak-approximation theorem. -/
theorem prime_of_mem_primesOverFinset (p : HeightOneSpectrum A)
    (Q : Ideal B)
    (hQ : Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal B) :
    Prime Q := by
  exact Ideal.prime_of_mem_primesOver p.ne_bot
    ((IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot B).mp hQ)

/-- A valuation bound on a nonzero element gives the corresponding lower
bound for its principal fractional-ideal coefficient. -/
theorem le_count_spanSingleton_of_valuation_le_exp_neg
    (q : HeightOneSpectrum B) {x : L} (hx : x ≠ 0) (n : ℤ)
    (hval : q.valuation L x ≤ WithZero.exp (-n)) :
    n ≤ FractionalIdeal.count L q
      (FractionalIdeal.spanSingleton B⁰ x) := by
  have hvaluation : q.valuation L x =
      WithZero.exp (-FractionalIdeal.count L q
        (FractionalIdeal.spanSingleton B⁰ x)) := by
    simpa using (FractionalIdeal.valuation_eq_exp_neg_count
      (R := B) (K := L) q (Units.mk0 x hx))
  rw [hvaluation] at hval
  have := WithZero.exp_le_exp.mp hval
  omega

omit [Algebra A L] [IsScalarTower A B L] [IsIntegralClosure B A L] in
/-- Weak approximation realizes simultaneous lower order bounds over one
base prime and realizes a prescribed negative order exactly at one chosen
prime. -/
theorem exists_element_with_counts_over_and_exact_at
    (p : HeightOneSpectrum A) (n : HeightOneSpectrum B → ℤ)
    (q₀ : HeightOneSpectrum B) (hq₀ : q₀.under A = p)
    (hn₀ : n q₀ < 0) :
    ∃ u : L, u ≠ 0 ∧
      (∀ q : HeightOneSpectrum B, q.under A = p →
        n q ≤ FractionalIdeal.count L q
          (FractionalIdeal.spanSingleton B⁰ u)) ∧
      FractionalIdeal.count L q₀
          (FractionalIdeal.spanSingleton B⁰ u) = n q₀ ∧
      ∀ q : HeightOneSpectrum B, q.under A ≠ p →
        0 ≤ FractionalIdeal.count L q
          (FractionalIdeal.spanSingleton B⁰ u) := by
  classical
  let selected := IsDedekindDomain.primesOverFinset p.asIdeal B
  let qOf : ∀ Q : Ideal B, Q ∈ selected → HeightOneSpectrum B :=
    fun Q hQ ↦ heightOneOfPrimesOverFinset (B := B) A p Q hQ
  let target : Ideal B → L := fun Q ↦
    if Q = q₀.asIdeal then
      (Classical.choose (q₀.valuation_exists_uniformizer L)) ^ (n q₀)
    else 0
  let precision : Ideal B → ℕ := fun Q ↦
    if hQ : Q ∈ selected then Int.toNat (n (qOf Q hQ)) else 0
  obtain ⟨u, huSelected, huElse⟩ :=
    exists_fraction_approximating_at_finitePlaces_regular_elsewhere
      (R := B) (L := L) selected
      (fun Q hQ ↦ prime_of_mem_primesOverFinset (B := B) A p Q hQ)
      target precision
  have hq₀Selected : q₀.asIdeal ∈ selected :=
    (mem_primesOverFinset_iff_under_eq (B := B) A p q₀).mpr hq₀
  have hq₀Of : qOf q₀.asIdeal hq₀Selected = q₀ := by
    apply HeightOneSpectrum.ext
    rfl
  have hprecisionq₀ : precision q₀.asIdeal = 0 := by
    simp only [precision, hq₀Selected, dite_true, qOf, hq₀Of]
    exact Int.toNat_of_nonpos hn₀.le
  let π : L := Classical.choose (q₀.valuation_exists_uniformizer L)
  have hπ : q₀.valuation L π = WithZero.exp (-1) :=
    Classical.choose_spec (q₀.valuation_exists_uniformizer L)
  have hπne : π ≠ 0 := by
    intro hzero
    rw [hzero, Valuation.map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have htargetq₀ : target q₀.asIdeal = π ^ (n q₀) := by
    simp [target, π]
  have huApprox : q₀.valuation L (u - π ^ (n q₀)) ≤ 1 := by
    simpa [hprecisionq₀, htargetq₀, WithZero.exp_zero] using
      huSelected q₀ hq₀Selected
  have htargetVal : q₀.valuation L (π ^ (n q₀)) =
      WithZero.exp (-(n q₀)) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    congr 1
    simp
  have herrorLt : q₀.valuation L (u - π ^ (n q₀)) <
      q₀.valuation L (π ^ (n q₀)) := by
    rw [htargetVal]
    apply lt_of_le_of_lt huApprox
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have huVal : q₀.valuation L u = WithZero.exp (-(n q₀)) := by
    rw [← htargetVal]
    exact Valuation.map_eq_of_sub_lt (q₀.valuation L) herrorLt
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, Valuation.map_zero] at huVal
    exact WithZero.exp_ne_zero huVal.symm
  have huCountExact : FractionalIdeal.count L q₀
      (FractionalIdeal.spanSingleton B⁰ u) = n q₀ := by
    have hvaluation : q₀.valuation L u =
        WithZero.exp (-FractionalIdeal.count L q₀
          (FractionalIdeal.spanSingleton B⁰ u)) := by
      simpa using (FractionalIdeal.valuation_eq_exp_neg_count
        (R := B) (K := L) q₀ (Units.mk0 u hu0))
    rw [huVal] at hvaluation
    exact neg_injective (WithZero.exp_injective hvaluation.symm)
  refine ⟨u, hu0, ?_, huCountExact, ?_⟩
  · intro q hq
    have hqSelected : q.asIdeal ∈ selected :=
      (mem_primesOverFinset_iff_under_eq (B := B) A p q).mpr hq
    have hqOf : qOf q.asIdeal hqSelected = q := by
      apply HeightOneSpectrum.ext
      rfl
    have hprecision : precision q.asIdeal = Int.toNat (n q) := by
      simp only [precision, hqSelected, dite_true, qOf, hqOf]
    have htarget : target q.asIdeal =
        if q.asIdeal = q₀.asIdeal then π ^ (n q₀) else 0 := by
      rfl
    by_cases hqq₀ : q = q₀
    · subst q
      exact huCountExact.ge
    · have hideal : q.asIdeal ≠ q₀.asIdeal := by
        intro h
        exact hqq₀ (HeightOneSpectrum.ext h)
      have hval : q.valuation L u ≤
          WithZero.exp (-(Int.toNat (n q) : ℤ)) := by
        have h := huSelected q hqSelected
        simpa [hprecision, target, hideal] using h
      have hnle : n q ≤ (Int.toNat (n q) : ℤ) := by
        by_cases hn : 0 ≤ n q
        · simpa [Int.toNat_of_nonneg hn]
        · rw [Int.toNat_of_nonpos (le_of_not_ge hn)]
          exact le_of_not_ge hn
      exact hnle.trans
        (le_count_spanSingleton_of_valuation_le_exp_neg
          (B := B) q hu0 (Int.toNat (n q)) hval)
  · intro q hq
    have hqNotSelected : q.asIdeal ∉ selected := by
      intro hmem
      exact hq ((mem_primesOverFinset_iff_under_eq (B := B) A p q).mp hmem)
    exact zero_le_count_spanSingleton_of_valuation_le_one q hu0
      (huElse q hqNotSelected)

/-- If one local order bound is strictly below the complementary-module
threshold, then every element of base order `-1` occurs as a trace while all
the prescribed order bounds over the chosen base prime are retained.

This is the algebraic core of Stichtenoth, Theorem 3.4.6, Step 1(b). -/
theorem exists_trace_eq_of_count_threshold_lt_neg_different
    (p : HeightOneSpectrum A) (n : HeightOneSpectrum B → ℤ)
    (q₀ : HeightOneSpectrum B) (hq₀ : q₀.under A = p)
    (hbad : n q₀ <
      -(multiplicity q₀.asIdeal (differentIdeal A B) : ℤ))
    (w : K₀) (hw : w ≠ 0)
    (hwVal : p.valuation K₀ w = WithZero.exp (1 : ℤ)) :
    ∃ z : L, z ≠ 0 ∧ Algebra.trace K₀ L z = w ∧
      ∀ q : HeightOneSpectrum B, q.under A = p →
        n q ≤ FractionalIdeal.count L q
          (FractionalIdeal.spanSingleton B⁰ z) := by
  classical
  have hn₀ : n q₀ < 0 := by
    have hmult : 0 ≤
        (multiplicity q₀.asIdeal (differentIdeal A B) : ℤ) := by
      exact_mod_cast (Nat.zero_le
        (multiplicity q₀.asIdeal (differentIdeal A B)))
    omega
  obtain ⟨u, hu0, huOver, huExact, huAway⟩ :=
    exists_element_with_counts_over_and_exact_at
      (A := A) (B := B) (L := L) p n q₀ hq₀ hn₀
  have huNotDual : u ∉
      FractionalIdeal.dual A K₀ (1 : FractionalIdeal B⁰ L) := by
    intro hu
    have hcounts :=
      (mem_dual_one_iff_different_multiplicity_le_count
        (A := A) (K₀ := K₀) hu0).mp hu
    have hq₀Count := hcounts q₀
    rw [huExact] at hq₀Count
    exact (not_lt_of_ge hq₀Count) hbad
  rw [FractionalIdeal.mem_dual (A := A) (K := K₀)
    (I := (1 : FractionalIdeal B⁰ L)) one_ne_zero] at huNotDual
  push Not at huNotDual
  obtain ⟨s, hs, husNot⟩ := huNotDual
  have hs0 : s ≠ 0 := by
    intro hsZero
    subst s
    simp [Algebra.traceForm_apply] at husNot
  let z₀ : L := u * s
  have hz₀0 : z₀ ≠ 0 := mul_ne_zero hu0 hs0
  have htraceNot : Algebra.trace K₀ L z₀ ∉ (algebraMap A K₀).range := by
    simpa only [Algebra.traceForm_apply, z₀] using husNot
  have hsCount : ∀ q : HeightOneSpectrum B,
      0 ≤ FractionalIdeal.count L q
        (FractionalIdeal.spanSingleton B⁰ s) := by
    have hsCounts := (FractionalIdeal.mem_iff_count_ge
      (I := (1 : FractionalIdeal B⁰ L)) one_ne_zero hs0).mp hs
    intro q
    simpa only [FractionalIdeal.count_one] using hsCounts q
  have hz₀Count : ∀ q : HeightOneSpectrum B,
      FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ z₀) =
        FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ u) +
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ s) := by
    intro q
    change FractionalIdeal.count L q
        (FractionalIdeal.spanSingleton B⁰ (u * s)) = _
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul]
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hu0
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hs0
  have hz₀Away : ∀ q : HeightOneSpectrum B, q.under A ≠ p →
      0 ≤ FractionalIdeal.count L q
        (FractionalIdeal.spanSingleton B⁰ z₀) := by
    intro q hq
    rw [hz₀Count q]
    exact add_nonneg (huAway q hq) (hsCount q)
  let t : K₀ := Algebra.trace K₀ L z₀
  have ht0 : t ≠ 0 := by
    intro ht
    apply htraceNot
    rw [show Algebra.trace K₀ L z₀ = t from rfl, ht]
    exact ⟨0, map_zero (algebraMap A K₀)⟩
  have hpNotIntegral : ¬ p.valuation K₀ t ≤ 1 := by
    intro hp
    apply htraceNot
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    by_cases hv : v = p
    · simpa [t, hv] using hp
    · have hlocal : ∀ q : HeightOneSpectrum B,
          q.under A = v →
            -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
              FractionalIdeal.count L q
                (FractionalIdeal.spanSingleton B⁰ z₀) := by
        intro q hq
        have hqAway : q.under A ≠ p := by
          rw [hq]
          exact hv
        have hnonneg := hz₀Away q hqAway
        have hmult : 0 ≤
            (multiplicity q.asIdeal (differentIdeal A B) : ℤ) := by
          exact_mod_cast (Nat.zero_le
            (multiplicity q.asIdeal (differentIdeal A B)))
        omega
      simpa [t] using
        valuation_trace_le_one_of_different_count_bounds_over
          (A := A) (K₀ := K₀) (B := B) (L := L) v hz₀0 hlocal
  have hpGt : 1 < p.valuation K₀ t := lt_of_not_ge hpNotIntegral
  have htVal : p.valuation K₀ t =
      WithZero.exp (-FractionalIdeal.count K₀ p
        (FractionalIdeal.spanSingleton A⁰ t)) := by
    simpa using (FractionalIdeal.valuation_eq_exp_neg_count
      (R := A) (K := K₀) p (Units.mk0 t ht0))
  have hwLeTrace : p.valuation K₀ w ≤ p.valuation K₀ t := by
    rw [hwVal, htVal, WithZero.exp_le_exp]
    rw [htVal, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hpGt
    omega
  let r : K₀ := w / t
  have hr0 : r ≠ 0 := div_ne_zero hw ht0
  have hrIntegral : p.valuation K₀ r ≤ 1 := by
    change p.valuation K₀ (w / t) ≤ 1
    rw [(p.valuation K₀).map_div]
    exact (div_le_one₀ (show 0 < p.valuation K₀ t by
      rw [htVal]
      exact WithZero.exp_pos)).mpr hwLeTrace
  let z : L := r • z₀
  have hz0 : z ≠ 0 := smul_ne_zero hr0 hz₀0
  have htraceZ : Algebra.trace K₀ L z = w := by
    change Algebra.trace K₀ L (r • z₀) = w
    rw [map_smul]
    change (w / t) * t = w
    exact div_mul_cancel₀ w ht0
  refine ⟨z, hz0, htraceZ, ?_⟩
  intro q hq
  have hrTopVal : q.valuation L (algebraMap K₀ L r) ≤ 1 :=
    heightOneValuation_algebraMap_le_one_of_under
      q p hq hrIntegral
  have hrTop0 : algebraMap K₀ L r ≠ 0 :=
    by simpa using (algebraMap K₀ L).injective.ne hr0
  have hrCount : 0 ≤ FractionalIdeal.count L q
      (FractionalIdeal.spanSingleton B⁰ (algebraMap K₀ L r)) :=
    zero_le_count_spanSingleton_of_valuation_le_one q hrTop0 hrTopVal
  have hzCount : FractionalIdeal.count L q
      (FractionalIdeal.spanSingleton B⁰ z) =
        FractionalIdeal.count L q
            (FractionalIdeal.spanSingleton B⁰ (algebraMap K₀ L r)) +
          FractionalIdeal.count L q
            (FractionalIdeal.spanSingleton B⁰ z₀) := by
    rw [show z = r • z₀ from rfl, Algebra.smul_def,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul]
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hrTop0
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz₀0
  rw [hzCount, hz₀Count q]
  have huq := huOver q hq
  have hsq := hsCount q
  omega

end

end BGS.HasseWeil
