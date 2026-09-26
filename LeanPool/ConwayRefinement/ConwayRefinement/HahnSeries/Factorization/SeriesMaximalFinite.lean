/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVMaximalFinite

/-!
# Maximal finite-support divisors of Hahn series

This module proves the intrinsic associate-class form of LM24, Proposition 5.5.1. It lifts the
maximal finite-support divisor from degree RV to the original ring `K((ℝ^{≤ 0}))` by
well-founded induction on Hahn-series degree.

At degree at most zero, exact degree multiplicativity reflects ambient divisibility back into the
finite-support subring. At positive degree, an RV-maximal finite-support divisor is lifted to a
series factor; subtracting that factor lowers degree. A pairwise greatest-common-divisor
hypothesis combines its divisor class with the recursively constructed residual class.

The definition and uniqueness of the intrinsic class do not depend on the existence proof.
Pairwise gcd existence remains an explicit hypothesis and is not installed as an instance; the
coefficient field has characteristic zero.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- A finite-support series divides another finite-support series in the finite-support subring
exactly when it divides it in the ambient Hahn-series ring. -/
theorem finiteSupport_dvd_iff_coe_dvd (p q : FiniteSupportRing (K := K)) :
    q ∣ p ↔ (q : Series K) ∣ (p : Series K) := by
  constructor
  · exact map_dvd
      (HahnSeries.Nonpositive.finiteSupportSubring (G := ℝ) (K := K)).subtype
  · rintro ⟨c, hc⟩
    by_cases hp : p = 0
    · subst p
      exact dvd_zero q
    have hpCoe : (p : Series K) ≠ 0 := by
      intro h
      apply hp
      exact Subtype.ext h
    have hq : q ≠ 0 := by
      intro hq
      subst q
      apply hpCoe
      simpa using hc
    have hpHahn : (p : K⟦ℝ⟧) ≠ 0 := by
      intro h
      apply hpCoe
      exact Subtype.ext h
    have hqHahn : (q : K⟦ℝ⟧) ≠ 0 := by
      intro h
      apply hq
      apply Subtype.ext
      exact Subtype.ext h
    have hpDegree : (p : K⟦ℝ⟧).degree = 0 := by
      rw [HahnSeries.degree_eq_zero]
      exact ⟨hpHahn,
        (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
          (p : Series K)).mp p.2⟩
    have hqDegree : (q : K⟦ℝ⟧).degree = 0 := by
      rw [HahnSeries.degree_eq_zero]
      exact ⟨hqHahn,
        (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
          (q : Series K)).mp q.2⟩
    have hcDegree : (c : K⟦ℝ⟧).degree = 0 := by
      have h := HahnSeries.Nonpositive.degree_mul (q : Series K) c
      rw [← hc, hpDegree, hqDegree, zero_add] at h
      exact h.symm
    let c' : FiniteSupportRing (K := K) := ⟨c, by
      rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff,
        ← HahnSeries.degree_le_zero_iff]
      exact hcDegree.le⟩
    refine ⟨c', ?_⟩
    apply Subtype.ext
    exact hc

/-- An associate class records exactly the finite-support divisors of a Hahn series. -/
def IsSeriesMaximalFiniteSupportDivisor
    (b : Series K) (a : Associates (FiniteSupportRing (K := K))) : Prop :=
  IsMaximalDivisorAlong
    (HahnSeries.Nonpositive.finiteSupportSubring (G := ℝ) (K := K)).subtype.toMonoidHom
    b a

omit [CharZero K] in
/-- The defining characterization of a maximal finite-support divisor class of a Hahn series. -/
theorem isSeriesMaximalFiniteSupportDivisor_iff
    (b : Series K) (a : Associates (FiniteSupportRing (K := K))) :
    IsSeriesMaximalFiniteSupportDivisor b a ↔
      ∀ q : FiniteSupportRing (K := K),
        Associates.mk q ≤ a ↔ (q : Series K) ∣ b := by
  rw [IsSeriesMaximalFiniteSupportDivisor, isMaximalDivisorAlong_iff]
  constructor <;> intro h q
  · have hq := h q
    change Associates.mk q ≤ a ↔ (q : Series K) ∣ b at hq
    exact hq
  · have hq := h q
    change Associates.mk q ≤ a ↔
      (HahnSeries.Nonpositive.finiteSupportSubring
        (G := ℝ) (K := K)).subtype q ∣ b
    exact hq

omit [CharZero K] in
/-- Representative form of the maximal finite-support divisor characterization. -/
theorem isSeriesMaximalFiniteSupportDivisor_mk_iff (b : Series K) (p : FiniteSupportRing (K := K)) :
    IsSeriesMaximalFiniteSupportDivisor b (Associates.mk p) ↔
      ∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p := by
  rw [isSeriesMaximalFiniteSupportDivisor_iff]
  constructor
  · intro h q
    constructor
    · intro hqb
      exact Associates.mk_le_mk_iff_dvd.mp ((h q).mpr hqb)
    · intro hqp
      exact (h q).mp (Associates.mk_le_mk_iff_dvd.mpr hqp)
  · intro h q
    constructor
    · intro hqp
      exact (h q).mpr (Associates.mk_le_mk_iff_dvd.mp hqp)
    · intro hqb
      exact Associates.mk_le_mk_iff_dvd.mpr ((h q).mp hqb)

omit [CharZero K] in
/-- A Hahn series has at most one maximal finite-support divisor class. -/
theorem IsSeriesMaximalFiniteSupportDivisor.eq
    {b : Series K} {a c : Associates (FiniteSupportRing (K := K))}
    (ha : IsSeriesMaximalFiniteSupportDivisor b a)
    (hc : IsSeriesMaximalFiniteSupportDivisor b c) : a = c := by
  exact IsMaximalDivisorAlong.eq ha hc

omit [CharZero K] in
/-- Zero has the zero maximal finite-support divisor class. -/
theorem IsSeriesMaximalFiniteSupportDivisor.zero :
    IsSeriesMaximalFiniteSupportDivisor (0 : Series K) 0 := by
  apply (isSeriesMaximalFiniteSupportDivisor_iff 0 0).mpr
  intro q
  constructor
  · intro _
    exact dvd_zero _
  · intro _
    exact Associates.mk_le_mk_of_dvd (dvd_zero q)

/-- Divisibility by a finite-support series splits across an RV-maximal divisor and the
corresponding subtraction residual. -/
theorem coe_dvd_iff_dvd_rvMaximal_and_residual (b b' : Series K) (p q : FiniteSupportRing (K := K))
    (hp : IsRVMaximalFiniteSupportDivisor
      ((HahnSeries.Nonpositive.degreeValuation K).rv b)
      (Associates.mk p)) :
    (q : Series K) ∣ b ↔
      q ∣ p ∧ (q : Series K) ∣ b - (p : Series K) * b' := by
  have hpSpec := (isRVMaximalFiniteSupportDivisor_mk_iff _ p).mp hp
  constructor
  · intro hqb
    have hqRV : finiteSupportRVEmbedding K q ∣
        (HahnSeries.Nonpositive.degreeValuation K).rv b := by
      simpa only [finiteSupportRVEmbedding_apply] using
        map_dvd
          (HahnSeries.Nonpositive.degreeValuation K).rv hqb
    have hqp : q ∣ p := (hpSpec q).mp hqRV
    have hqpCoe : (q : Series K) ∣ (p : Series K) :=
      (finiteSupport_dvd_iff_coe_dvd p q).mp hqp
    exact ⟨hqp, dvd_sub hqb (hqpCoe.mul_right b')⟩
  · rintro ⟨hqp, hqResidual⟩
    have hqpCoe : (q : Series K) ∣ (p : Series K) :=
      (finiteSupport_dvd_iff_coe_dvd p q).mp hqp
    simpa only [sub_add_cancel] using
      dvd_add hqResidual (hqpCoe.mul_right b')

/-- A positive-degree Hahn series admits an RV-maximal finite-support factor whose subtraction
residual has strictly smaller degree. -/
theorem exists_rvMaximalFiniteSupportApproximation_of_degree_pos
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {b : Series K} (hb : 0 < (b : K⟦ℝ⟧).degree) :
    ∃ (p : FiniteSupportRing (K := K)) (b' : Series K),
      IsRVMaximalFiniteSupportDivisor
          ((HahnSeries.Nonpositive.degreeValuation K).rv b)
          (Associates.mk p) ∧
        ((b - (p : Series K) * b' : Series K) : K⟦ℝ⟧).degree <
          (b : K⟦ℝ⟧).degree := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isRVMaximalFiniteSupportDivisor_of_exists_gcd hgcd (w.rv b)
  induction a using Quotient.inductionOn with
  | _ p =>
      have hpDvd : finiteSupportRVEmbedding K p ∣ w.rv b :=
        ((isRVMaximalFiniteSupportDivisor_mk_iff (w.rv b) p).mp ha p).mpr
          dvd_rfl
      obtain ⟨B', hB'⟩ := hpDvd
      obtain ⟨b', hb'⟩ := w.rv_surjective B'
      refine ⟨p, b', ha, ?_⟩
      have hbValue : w b ≠ ⊥ := by
        rw [HahnSeries.Nonpositive.degreeValuation_apply]
        intro hbot
        rw [hbot] at hb
        exact (not_lt_of_ge bot_le hb)
      have hrv : w.rv b = w.rv ((p : Series K) * b') := by
        calc
          w.rv b = finiteSupportRVEmbedding K p * B' := hB'
          _ = w.rv (p : Series K) * w.rv b' := by
            rw [finiteSupportRVEmbedding_apply, hb']
          _ = w.rv ((p : Series K) * b') := (map_mul w.rv _ _).symm
      have hdrop := (w.rv_eq_iff_of_value_ne_bot hbValue).mp hrv
      simpa only [w,
        HahnSeries.Nonpositive.degreeValuation_apply] using hdrop

/-- Pairwise greatest-common-divisor existence gives a maximal finite-support divisor class for
every Hahn series. -/
theorem exists_isSeriesMaximalFiniteSupportDivisor_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b : Series K) :
    ∃ a : Associates (FiniteSupportRing (K := K)),
      IsSeriesMaximalFiniteSupportDivisor b a := by
  classical
  let wf : WellFounded (Function.onFun (fun α β : WithBot NatOrdinal ↦ α < β)
      (fun c : Series K ↦ (c : K⟦ℝ⟧).degree)) :=
    wellFounded_lt.onFun
  refine wf.induction
    (C := fun b ↦ ∃ a : Associates (FiniteSupportRing (K := K)),
      IsSeriesMaximalFiniteSupportDivisor b a) b ?_
  intro b ih
  by_cases hbFinite : (b : K⟦ℝ⟧).degree ≤ 0
  · let p : FiniteSupportRing (K := K) := ⟨b, by
      rw [HahnSeries.Nonpositive.mem_finiteSupportSubring_iff,
        ← HahnSeries.degree_le_zero_iff]
      exact hbFinite⟩
    refine ⟨Associates.mk p,
      (isSeriesMaximalFiniteSupportDivisor_mk_iff b p).mpr ?_⟩
    intro q
    simpa only [p] using (finiteSupport_dvd_iff_coe_dvd p q).symm
  · have hbPos : 0 < (b : K⟦ℝ⟧).degree := lt_of_not_ge hbFinite
    obtain ⟨p, b', hp, hdrop⟩ :=
      exists_rvMaximalFiniteSupportApproximation_of_degree_pos hgcd hbPos
    let c : Series K := b - (p : Series K) * b'
    obtain ⟨a, ha⟩ := ih c (by simpa only [c] using hdrop)
    induction a using Quotient.inductionOn with
    | _ p' =>
        obtain ⟨d, hd⟩ := hgcd p p'
        refine ⟨Associates.mk d,
          (isSeriesMaximalFiniteSupportDivisor_mk_iff b d).mpr ?_⟩
        intro q
        calc
          (q : Series K) ∣ b ↔ q ∣ p ∧ (q : Series K) ∣ c := by
            simpa only [c] using
              coe_dvd_iff_dvd_rvMaximal_and_residual b b' p q hp
          _ ↔ q ∣ p ∧ q ∣ p' :=
            and_congr Iff.rfl
              ((isSeriesMaximalFiniteSupportDivisor_mk_iff c p').mp ha q)
          _ ↔ q ∣ d := hd q

/-- Pairwise greatest-common-divisor existence gives a unique maximal finite-support divisor
class for every Hahn series. -/
theorem existsUnique_isSeriesMaximalFiniteSupportDivisor_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b : Series K) :
    ∃! a : Associates (FiniteSupportRing (K := K)),
      IsSeriesMaximalFiniteSupportDivisor b a := by
  obtain ⟨a, ha⟩ :=
    exists_isSeriesMaximalFiniteSupportDivisor_of_exists_gcd hgcd b
  exact ⟨a, ha, fun c hc ↦ hc.eq ha⟩

/-- The canonical maximal finite-support divisor class of a Hahn series.

The fallback branch is unreachable whenever maximal-divisor existence has been established. -/
noncomputable def seriesMaximalFiniteSupportDivisor
    (b : Series K) : Associates (FiniteSupportRing (K := K)) := by
  classical
  exact if h : ∃ a : Associates (FiniteSupportRing (K := K)),
        IsSeriesMaximalFiniteSupportDivisor b a then
      Classical.choose h
    else
      0

omit [CharZero K] in
/-- Any class satisfying the series characterization is the canonical class. -/
theorem seriesMaximalFiniteSupportDivisor_eq_of_is
    {b : Series K} {a : Associates (FiniteSupportRing (K := K))}
    (ha : IsSeriesMaximalFiniteSupportDivisor b a) :
    seriesMaximalFiniteSupportDivisor b = a := by
  classical
  let hex : ∃ c : Associates (FiniteSupportRing (K := K)),
      IsSeriesMaximalFiniteSupportDivisor b c := ⟨a, ha⟩
  rw [seriesMaximalFiniteSupportDivisor, dite_eq_left hex]
  exact (Classical.choose_spec hex).eq ha

/-- Under pairwise greatest-common-divisor existence, the canonical class satisfies its defining
characterization. -/
theorem seriesMaximalFiniteSupportDivisor_is_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b : Series K) :
    IsSeriesMaximalFiniteSupportDivisor b
      (seriesMaximalFiniteSupportDivisor b) := by
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isSeriesMaximalFiniteSupportDivisor_of_exists_gcd hgcd b
  rw [seriesMaximalFiniteSupportDivisor_eq_of_is ha]
  exact ha

/-- Maximal finite-support divisor classes of Hahn series are supermultiplicative. -/
theorem seriesMaximalFiniteSupportDivisor_mul_le_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b c : Series K) :
    seriesMaximalFiniteSupportDivisor b *
        seriesMaximalFiniteSupportDivisor c ≤
      seriesMaximalFiniteSupportDivisor (b * c) := by
  exact IsMaximalDivisorAlong.mul_le
    (seriesMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b)
    (seriesMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd c)
    (seriesMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (b * c))

/-- The maximal divisor class of a finite-support series is its own associate class. -/
theorem seriesMaximalFiniteSupportDivisor_coe (p : FiniteSupportRing (K := K)) :
    seriesMaximalFiniteSupportDivisor (p : Series K) = Associates.mk p := by
  apply seriesMaximalFiniteSupportDivisor_eq_of_is
  apply (isSeriesMaximalFiniteSupportDivisor_mk_iff (p : Series K) p).mpr
  intro q
  exact (finiteSupport_dvd_iff_coe_dvd p q).symm

/-- A principal Hahn series has the unit associate class as its maximal finite-support divisor.
-/
theorem seriesMaximalFiniteSupportDivisor_eq_one_of_isPrincipal
    {b : Series K} (hb : HahnSeries.Nonpositive.IsPrincipal b) :
    seriesMaximalFiniteSupportDivisor b = 1 := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  have hPrincipalRV : IsPrincipalRV (w.rv b) :=
    (isPrincipalRV_iff (w.rv b)).mpr ⟨b, hb, rfl⟩
  obtain ⟨k, hk⟩ :=
    exists_scalar_isRVMaximalFiniteSupportDivisor_of_isPrincipal (w.rv b) hPrincipalRV
  let scalar := HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k
  have hkSpec := (isRVMaximalFiniteSupportDivisor_mk_iff (w.rv b) scalar).mp hk
  have hBNe : w.rv b ≠ 0 := by
    intro hzero
    have hbot := (w.rv_eq_zero_iff).mp hzero
    rw [HahnSeries.Nonpositive.degreeValuation_apply,
      HahnSeries.degree_eq_bot] at hbot
    exact hb.ne_zero (Subtype.ext hbot)
  have hkNe : k ≠ 0 := by
    intro hkZero
    subst k
    have hzeroDvd : finiteSupportRVEmbedding K 0 ∣ w.rv b :=
      (hkSpec 0).mpr (by simp [scalar])
    apply hBNe
    apply zero_dvd_iff.mp
    simpa using hzeroDvd
  have hscalarUnit : IsUnit scalar := by
    exact (isUnit_iff_ne_zero.mpr hkNe).map
      (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) (K := K))
  apply seriesMaximalFiniteSupportDivisor_eq_of_is
  apply (isSeriesMaximalFiniteSupportDivisor_mk_iff b 1).mpr
  intro q
  constructor
  · intro hqb
    have hqRV : finiteSupportRVEmbedding K q ∣ w.rv b := by
      simpa only [finiteSupportRVEmbedding_apply] using map_dvd w.rv hqb
    exact isUnit_iff_dvd_one.mp
      (isUnit_of_dvd_unit ((hkSpec q).mp hqRV) hscalarUnit)
  · intro hqOne
    exact (isUnit_of_dvd_one hqOne).map
      (HahnSeries.Nonpositive.finiteSupportSubring
        (G := ℝ) (K := K)).subtype |>.dvd

end

end Berarducci
