/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.SeriesMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportNormalization

/-!
# Normalized maximal finite-support divisors of Hahn series

This module passes from the intrinsic associate class of LM24, Proposition 5.5.1 to the
representative `p(b)` fixed by Notation 5.5.2. The representative is zero when `b = 0`; otherwise
its coefficient at the greatest support exponent is `1`.

The source-level divisibility characterization, the three clauses of Remark 5.5.3, and the
one-sided product divisibility of Proposition 5.5.5 are proved with their exact orientations. Unit
classification and pairwise greatest-common-divisor existence remain explicit hypotheses.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

/-- A finite-support series is the normalized maximal divisor of a Hahn series when it has
exactly its finite-support divisors and is zero at zero or monic otherwise. -/
def IsNormalizedSeriesMaximalFiniteSupportDivisor
    (b : Series K) (p : FiniteSupportRing (K := K)) : Prop :=
  (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p) ∧
    ((b = 0 ∧ p = 0) ∨
      (b ≠ 0 ∧ HahnSeries.Nonpositive.IsMonicFiniteSupport p))

omit [CharZero K] in
/-- Characterization of a normalized maximal finite-support divisor of a Hahn series. -/
theorem isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    (b : Series K) (p : FiniteSupportRing (K := K)) :
    IsNormalizedSeriesMaximalFiniteSupportDivisor b p ↔
      (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p) ∧
        ((b = 0 ∧ p = 0) ∨
          (b ≠ 0 ∧ HahnSeries.Nonpositive.IsMonicFiniteSupport p)) :=
  Iff.rfl

/-- The normalized representative of the maximal finite-support divisor class of a Hahn series.
-/
noncomputable def seriesNormalizedMaximalFiniteSupportDivisor
    (b : Series K) : FiniteSupportRing (K := K) :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative (G := ℝ)
    (seriesMaximalFiniteSupportDivisor b)

omit [CharZero K] in
/-- The chosen series-level representative is normalized in its associate class. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_isNormalized (b : Series K) :
    HahnSeries.Nonpositive.IsNormalizedAssociateRepresentative
      (seriesMaximalFiniteSupportDivisor b)
      (seriesNormalizedMaximalFiniteSupportDivisor b) :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative_is _

omit [CharZero K] in
/-- The associate class of the normalized representative is the intrinsic maximal-divisor
class. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_mk (b : Series K) :
    Associates.mk (seriesNormalizedMaximalFiniteSupportDivisor b) =
      seriesMaximalFiniteSupportDivisor b :=
  HahnSeries.Nonpositive.normalizedAssociateRepresentative_mk _

/-- On a finite-support input, the series-level normalization coincides with the earlier
graded normalization from LM24, Notation 5.4.5. This includes the zero input. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_coe_eq_graded (p : FiniteSupportRing (K := K)) :
    seriesNormalizedMaximalFiniteSupportDivisor (p : Series K) =
      gradedNormalizedMaximalFiniteSupportDivisor
        (finiteSupportGradedEmbedding K p) := by
  rw [seriesNormalizedMaximalFiniteSupportDivisor,
    seriesMaximalFiniteSupportDivisor_coe,
    gradedNormalizedMaximalFiniteSupportDivisor_finiteSupport]

/-- Under pairwise greatest-common-divisor existence, the normalized representative has exactly
the finite-support divisors of the Hahn series. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_isMaximal_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b : Series K) :
    IsSeriesMaximalFiniteSupportDivisor b
      (Associates.mk (seriesNormalizedMaximalFiniteSupportDivisor b)) := by
  rw [seriesNormalizedMaximalFiniteSupportDivisor_mk]
  exact seriesMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b

/-- A nonzero Hahn series has a nonzero maximal finite-support divisor class. -/
theorem seriesMaximalFiniteSupportDivisor_ne_zero_of_ne_zero
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {b : Series K} (hb : b ≠ 0) :
    seriesMaximalFiniteSupportDivisor b ≠ 0 := by
  intro hclass
  have hmax := seriesMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b
  have hzeroLe : Associates.mk (0 : FiniteSupportRing (K := K)) ≤
      seriesMaximalFiniteSupportDivisor b := by
    rw [hclass]
    exact le_rfl
  have hzeroDvd :=
    (isSeriesMaximalFiniteSupportDivisor_iff b _).mp hmax 0 |>.mp hzeroLe
  exact hb (zero_dvd_iff.mp hzeroDvd)

/-- The normalized maximal finite-support divisor of a nonzero Hahn series is monic. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {b : Series K} (hb : b ≠ 0) :
    HahnSeries.Nonpositive.IsMonicFiniteSupport
      (seriesNormalizedMaximalFiniteSupportDivisor b) := by
  apply HahnSeries.Nonpositive.normalizedAssociateRepresentative_isMonic_of_ne_zero
  exact seriesMaximalFiniteSupportDivisor_ne_zero_of_ne_zero hgcd hb

/-- Under pairwise greatest-common-divisor existence, the chosen representative satisfies the
normalized series-level maximal-divisor predicate. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b : Series K) :
    IsNormalizedSeriesMaximalFiniteSupportDivisor b
      (seriesNormalizedMaximalFiniteSupportDivisor b) := by
  constructor
  · exact (isSeriesMaximalFiniteSupportDivisor_mk_iff b _).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_isMaximal_of_exists_gcd hgcd b)
  · by_cases hb : b = 0
    · subst b
      apply Or.inl
      refine ⟨rfl, ?_⟩
      have hzero : IsSeriesMaximalFiniteSupportDivisor (0 : Series K) 0 :=
        IsSeriesMaximalFiniteSupportDivisor.zero
      rw [seriesNormalizedMaximalFiniteSupportDivisor,
        seriesMaximalFiniteSupportDivisor_eq_of_is hzero,
        HahnSeries.Nonpositive.normalizedAssociateRepresentative_zero]
    · exact Or.inr ⟨hb,
        seriesNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hb⟩

omit [CharZero K] in
/-- The normalized series-level predicate determines at most one finite-support series when all
units are nonzero constant series. -/
theorem IsNormalizedSeriesMaximalFiniteSupportDivisor.eq (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    {b : Series K} {p q : FiniteSupportRing (K := K)}
    (hp : IsNormalizedSeriesMaximalFiniteSupportDivisor b p)
    (hq : IsNormalizedSeriesMaximalFiniteSupportDivisor b q) : p = q := by
  have hpMax := (isSeriesMaximalFiniteSupportDivisor_mk_iff b p).mpr hp.1
  have hqMax := (isSeriesMaximalFiniteSupportDivisor_mk_iff b q).mpr hq.1
  have hclasses : Associates.mk p = Associates.mk q := hpMax.eq hqMax
  rcases hp.2 with hpZero | hpNonzero
  · rcases hq.2 with hqZero | hqNonzero
    · exact hpZero.2.trans hqZero.2.symm
    · exact (hqNonzero.1 hpZero.1).elim
  · rcases hq.2 with hqZero | hqNonzero
    · exact (hpNonzero.1 hqZero.1).elim
    · have hpNormalized :
          HahnSeries.Nonpositive.IsNormalizedAssociateRepresentative
            (Associates.mk p) p :=
        (HahnSeries.Nonpositive.isNormalizedAssociateRepresentative_iff
          (Associates.mk p) p).mpr
            (Or.inr ⟨Associates.mk_ne_zero.mpr hpNonzero.2.ne_zero,
              rfl, hpNonzero.2⟩)
      have hqNormalized :
          HahnSeries.Nonpositive.IsNormalizedAssociateRepresentative
            (Associates.mk p) q :=
        (HahnSeries.Nonpositive.isNormalizedAssociateRepresentative_iff
          (Associates.mk p) q).mpr
            (Or.inr ⟨Associates.mk_ne_zero.mpr hpNonzero.2.ne_zero,
              hclasses.symm, hqNonzero.2⟩)
      exact hpNormalized.eq hunits hqNormalized

/-- Any finite-support series satisfying the normalized predicate is the chosen normalized
representative. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_eq_of_is
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    {b : Series K} {p : FiniteSupportRing (K := K)}
    (hp : IsNormalizedSeriesMaximalFiniteSupportDivisor b p) :
    seriesNormalizedMaximalFiniteSupportDivisor b = p := by
  exact (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b).eq hunits hp

/-- The product of the normalized maximal finite-support divisors divides the normalized maximal
finite-support divisor of the product. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_mul_dvd_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b c : Series K) :
    seriesNormalizedMaximalFiniteSupportDivisor b *
        seriesNormalizedMaximalFiniteSupportDivisor c ∣
      seriesNormalizedMaximalFiniteSupportDivisor (b * c) := by
  apply Associates.mk_le_mk_iff_dvd.mp
  rw [← Associates.mk_mul_mk,
    seriesNormalizedMaximalFiniteSupportDivisor_mk,
    seriesNormalizedMaximalFiniteSupportDivisor_mk,
    seriesNormalizedMaximalFiniteSupportDivisor_mk]
  exact seriesMaximalFiniteSupportDivisor_mul_le_of_exists_gcd hgcd b c

/-- The normalized maximal finite-support divisor embeds as a divisor of the Hahn series. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_dvd_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (b : Series K) :
    (seriesNormalizedMaximalFiniteSupportDivisor b : Series K) ∣ b := by
  have h := seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b
  exact (h.1 (seriesNormalizedMaximalFiniteSupportDivisor b)).mpr dvd_rfl

/-- The normalized maximal finite-support divisor of zero is zero. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_zero_of_exists_gcd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d) :
    seriesNormalizedMaximalFiniteSupportDivisor (0 : Series K) = 0 := by
  have h := seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (0 : Series K)
  rcases h.2 with hzero | hnonzero
  · exact hzero.2
  · exact (hnonzero.1 rfl).elim

/-- The normalized maximal divisor of a finite-support series is a nonzero scalar multiple of
that series. -/
theorem exists_scalar_seriesNormalizedMaximalFiniteSupportDivisor_coe
    (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    (p : FiniteSupportRing (K := K)) :
    ∃ k : K, k ≠ 0 ∧
      seriesNormalizedMaximalFiniteSupportDivisor (p : Series K) =
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  have hclasses : Associates.mk p =
      Associates.mk (seriesNormalizedMaximalFiniteSupportDivisor (p : Series K)) := by
    rw [seriesNormalizedMaximalFiniteSupportDivisor_mk,
      seriesMaximalFiniteSupportDivisor_coe]
  exact HahnSeries.Nonpositive.exists_nonzero_scalar_mul_of_mk_eq_mk
    hunits hclasses

/-- The normalized maximal finite-support divisor of a principal Hahn series is one. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_eq_one_of_isPrincipal
    (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)
    {b : Series K} (hb : HahnSeries.Nonpositive.IsPrincipal b) :
    seriesNormalizedMaximalFiniteSupportDivisor b = 1 := by
  have hclass := seriesMaximalFiniteSupportDivisor_eq_one_of_isPrincipal hb
  apply HahnSeries.Nonpositive.normalizedAssociateRepresentative_eq_of_is hunits
  rw [HahnSeries.Nonpositive.isNormalizedAssociateRepresentative_iff, hclass]
  exact Or.inr ⟨one_ne_zero, Associates.mk_one,
    HahnSeries.Nonpositive.isMonicFiniteSupport_one⟩

end

end Berarducci
