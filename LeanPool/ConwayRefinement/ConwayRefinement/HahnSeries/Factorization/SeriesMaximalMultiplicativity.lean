/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.RVGradedMaximalFinite
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Order.RelClasses

/-!
# Multiplicativity of maximal finite-support divisors of Hahn series

This module proves the field-generic reduction underlying LM24, Proposition 6.3.8. The proof is
by lexicographic well-founded induction on the degrees of the two factors. Its explicit leading-RV
hypothesis is precisely the conclusion of LM24, Corollary 6.3.7.

Pairwise greatest-common-divisor existence and the classification of finite-support units remain
explicit hypotheses.
-/

open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

private def IsFiniteSupportPrimitive (b : Series K) : Prop :=
  ∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b → IsUnit q

private theorem degree_rightFactor_eq_of_monicFiniteSupport {p : FiniteSupportRing (K := K)}
    (hp : IsMonicFiniteSupport p)
    {b b₀ : Series K} (hbFactor : b = (p : Series K) * b₀) :
    (b₀ : K⟦ℝ⟧).degree = (b : K⟦ℝ⟧).degree := by
  have hpHahn : (p : K⟦ℝ⟧) ≠ 0 := by
    intro hpZero
    apply hp.ne_zero
    exact Subtype.ext (Subtype.ext hpZero)
  have hpDegree : (p : K⟦ℝ⟧).degree = 0 := by
    rw [HahnSeries.degree_eq_zero]
    exact ⟨hpHahn,
      (mem_finiteSupportSubring_iff (p : Series K)).mp p.2⟩
  have hproduct := HahnSeries.Nonpositive.degree_mul (p : Series K) b₀
  rw [← hbFactor, hpDegree, zero_add] at hproduct
  exact hproduct.symm

private theorem isFiniteSupportPrimitive_factor_of_normalizedMaximal
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {b b₀ : Series K} (hb : b ≠ 0)
    (hbFactor : b =
      (seriesNormalizedMaximalFiniteSupportDivisor b : Series K) * b₀) :
    IsFiniteSupportPrimitive b₀ := by
  let pB := seriesNormalizedMaximalFiniteSupportDivisor b
  have hmax := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff b pB).mp
    (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd b)
  have hpBMonic := seriesNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hb
  have hpB : pB ≠ 0 := hpBMonic.ne_zero
  intro q hq
  have hpBq : ((pB * q : FiniteSupportRing (K := K)) : Series K) ∣ b := by
    rw [hbFactor]
    change ((pB * q : FiniteSupportRing (K := K)) : Series K) ∣
      (pB : Series K) * b₀
    have hq' := mul_dvd_mul_left (pB : Series K) hq
    simpa only [Subring.coe_mul] using hq'
  have hpBqDvd : pB * q ∣ pB := (hmax.1 (pB * q)).mp hpBq
  have hqOne : q ∣ 1 := by
    apply (mul_dvd_mul_iff_left hpB).mp
    simpa only [mul_one] using hpBqDvd
  exact isUnit_of_dvd_one hqOne

/-- A positive-degree series can be approximated by its normalized maximal finite-support
divisor of the leading RV class, with a remainder of strictly smaller degree. -/
theorem exists_normalizedRVMaximalFiniteSupportApproximation_of_degree_pos
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {b : Series K} (hb : 0 < (b : K⟦ℝ⟧).degree) :
    ∃ b' : Series K,
      ((b -
          (gradedNormalizedMaximalFiniteSupportDivisor
              ((degreeValuation K).rvInitialFormHom
                ((degreeValuation K).rv b)) : Series K) *
            b' : Series K) : K⟦ℝ⟧).degree <
        (b : K⟦ℝ⟧).degree := by
  let w := degreeValuation K
  let pB := gradedNormalizedMaximalFiniteSupportDivisor
    (w.rvInitialFormHom (w.rv b))
  obtain ⟨p, b', hp, hdrop⟩ :=
    exists_rvMaximalFiniteSupportApproximation_of_degree_pos hgcd hb
  have hpGraded :
      IsGradedMaximalFiniteSupportDivisor
        (w.rvInitialFormHom (w.rv b)) (Associates.mk p) :=
    (isRVMaximalFiniteSupportDivisor_iff_isGradedMaximalFiniteSupportDivisor (w.rv b)
      (Associates.mk p)).mp hp
  have hpBGraded :
      IsGradedMaximalFiniteSupportDivisor
        (w.rvInitialFormHom (w.rv b)) (Associates.mk pB) := by
    exact (isGradedMaximalFiniteSupportDivisor_mk_iff _ pB).mpr
      ((isNormalizedGradedMaximalFiniteSupportDivisor_iff _ pB).mp
        (gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd _)).1
  have hclasses : Associates.mk pB = Associates.mk p :=
    hpBGraded.eq hpGraded
  obtain ⟨u, hu⟩ := Associates.mk_eq_mk_iff_associated.mp hclasses
  let b'' : Series K := (((u : FiniteSupportRing (K := K)) : Series K) * b')
  refine ⟨b'', ?_⟩
  have hproduct : (pB : Series K) * b'' = (p : Series K) * b' := by
    have hpEq : p = pB * (u : FiniteSupportRing (K := K)) := hu.symm
    calc
      (pB : Series K) * b'' =
          (pB : Series K) *
            ((u : FiniteSupportRing (K := K)) : Series K) * b' := by
        dsimp only [b'']
        rw [mul_assoc]
      _ = ((pB * (u : FiniteSupportRing (K := K)) :
            FiniteSupportRing (K := K)) : Series K) * b' := by
        exact congrArg (· * b')
          (map_mul
            (finiteSupportSubring (G := ℝ) (K := K)).subtype pB
              (u : FiniteSupportRing (K := K))).symm
      _ = (p : Series K) * b' := by rw [hpEq]
  simpa only [pB, w, hproduct] using hdrop

omit [CharZero K] in
/-- A finite-support-primitive series of degree at most `0` is a unit: it has finite support, so
it is its own finite-support divisor, and primitivity makes that divisor a unit. -/
private theorem isUnit_of_isFiniteSupportPrimitive_of_degree_le_zero {b : Series K}
    (hbPrimitive : IsFiniteSupportPrimitive b) (hbFinite : (b : K⟦ℝ⟧).degree ≤ 0) :
    IsUnit b := by
  let p : FiniteSupportRing (K := K) := ⟨b, by
    rw [mem_finiteSupportSubring_iff, ← HahnSeries.degree_le_zero_iff]
    exact hbFinite⟩
  have hpUnit : IsUnit p := hbPrimitive p (by simp [p])
  change IsUnit ((p : FiniteSupportRing (K := K)) : Series K)
  exact hpUnit.map (finiteSupportSubring (G := ℝ) (K := K)).subtype

/-- The coprimality step of the induction. Let `q` be a finite-support divisor of `b * c`, with
`b` finite-support primitive and the normalized maximal divisor of `c` a unit, and write
`b = p * b' + d` where multiplicativity of the normalized maximal divisor is known for `d * c`.
Every common finite-support divisor `r` of `q` and `p` divides `d * c`, hence the normalized
maximal divisor of `d`, hence `d`, hence `b`; primitivity of `b` makes `r` a unit. -/
private theorem isRelPrime_of_dvd_mul_of_eq_mul_add
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {b c b' d : Series K} {q p : FiniteSupportRing (K := K)}
    (hqbc : (q : Series K) ∣ b * c)
    (hbPrimitive : IsFiniteSupportPrimitive b)
    (hpCUnit : IsUnit (seriesNormalizedMaximalFiniteSupportDivisor c))
    (hsum : (p : Series K) * b' + d = b)
    (hmul : seriesNormalizedMaximalFiniteSupportDivisor (d * c) =
      seriesNormalizedMaximalFiniteSupportDivisor d *
        seriesNormalizedMaximalFiniteSupportDivisor c) :
    IsRelPrime q p := by
  intro r hrq hrp
  have hrbc : (r : Series K) ∣ b * c :=
    (map_dvd (finiteSupportSubring (G := ℝ) (K := K)).subtype hrq).trans hqbc
  have hrpCoe : (r : Series K) ∣ (p : Series K) :=
    map_dvd (finiteSupportSubring (G := ℝ) (K := K)).subtype hrp
  have hrdc : (r : Series K) ∣ d * c := by
    have hdc : d * c = b * c - (p : Series K) * b' * c := by
      rw [← hsum]
      ring
    rw [hdc]
    exact dvd_sub hrbc ((hrpCoe.mul_right b').mul_right c)
  have hmaxdc := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    (d * c) (seriesNormalizedMaximalFiniteSupportDivisor (d * c))).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (d * c))
  have hrpdc := (hmaxdc.1 r).mp hrdc
  rw [hmul] at hrpdc
  have hrpd : r ∣ seriesNormalizedMaximalFiniteSupportDivisor d :=
    hpCUnit.dvd_mul_right.mp hrpdc
  have hmaxd := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    d (seriesNormalizedMaximalFiniteSupportDivisor d)).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd d)
  have hrd : (r : Series K) ∣ d := (hmaxd.1 r).mpr hrpd
  apply hbPrimitive r
  rw [← hsum]
  exact dvd_add (hrpCoe.mul_right b') hrd

/-- A finite-support divisor of a series divides the normalized maximal finite-support divisor of
the initial form of its leading RV class: the RV map and the initial-form map are multiplicative,
and on finite-support elements their composite is the graded embedding. -/
private theorem dvd_gradedNormalizedMaximalFiniteSupportDivisor_rvInitialForm_of_dvd
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    {d : Series K} {q : FiniteSupportRing (K := K)} (hqd : (q : Series K) ∣ d) :
    q ∣ gradedNormalizedMaximalFiniteSupportDivisor
      ((degreeValuation K).rvInitialFormHom ((degreeValuation K).rv d)) := by
  let w := degreeValuation K
  have hqRV : finiteSupportRVEmbedding K q ∣ w.rv d := by
    simpa only [finiteSupportRVEmbedding_apply] using map_dvd w.rv hqd
  have hqInitialRaw := map_dvd w.rvInitialFormHom hqRV
  have hfinite :
      w.rvInitialFormHom (finiteSupportRVEmbedding K q) =
        finiteSupportGradedEmbedding K q := by
    calc
      w.rvInitialFormHom (finiteSupportRVEmbedding K q) =
          ((w.rvEquivHomogeneous (finiteSupportRVEmbedding K q) :
            w.HomogeneousClasses) : w.AssociatedGraded) := by
        rw [w.rvEquivHomogeneous_apply, w.coe_rvHomogeneous]
      _ = finiteSupportGradedEmbedding K q := by
        simpa only [w] using
          coe_rvEquivHomogeneous_finiteSupportRVEmbedding q
  rw [hfinite] at hqInitialRaw
  have hmax := (isNormalizedGradedMaximalFiniteSupportDivisor_iff
    (w.rvInitialFormHom (w.rv d))
    (gradedNormalizedMaximalFiniteSupportDivisor (w.rvInitialFormHom (w.rv d)))).mp
      (gradedNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd
        (w.rvInitialFormHom (w.rv d)))
  exact (hmax.1 q).mp hqInitialRaw

/-- Under leading-RV multiplicativity, the normalized maximal finite-support divisor of the
initial form of `rv (b * c)` is the product of those of the initial forms of `rv b` and
`rv c`, because `rv` and the initial-form map are monoid homomorphisms. -/
private theorem gradedNormalizedMaximalFiniteSupportDivisor_rvInitialForm_mul
    (hgradedMul : ∀ B C : DegreeGraded K,
      gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
        gradedNormalizedMaximalFiniteSupportDivisor B *
          gradedNormalizedMaximalFiniteSupportDivisor C)
    (b c : Series K) :
    gradedNormalizedMaximalFiniteSupportDivisor
        ((degreeValuation K).rvInitialFormHom ((degreeValuation K).rv (b * c))) =
      gradedNormalizedMaximalFiniteSupportDivisor
          ((degreeValuation K).rvInitialFormHom ((degreeValuation K).rv b)) *
        gradedNormalizedMaximalFiniteSupportDivisor
          ((degreeValuation K).rvInitialFormHom ((degreeValuation K).rv c)) := by
  rw [map_mul, map_mul]
  exact hgradedMul _ _

/-- The inductive step: the product of two finite-support-primitive series is finite-support
primitive, given multiplicativity of the normalized maximal divisor for pairs of strictly
smaller degree on either side. A factor of degree at most `0` is a unit and drops out. Otherwise
each factor is approximated by its leading-RV normalized maximal divisor with a remainder of
smaller degree; a finite-support divisor `q` of the product is coprime to both approximating
divisors and divides their product, so it is a unit. -/
private theorem isFiniteSupportPrimitive_mul_of_induction
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hgradedMul : ∀ B C : DegreeGraded K,
      gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
        gradedNormalizedMaximalFiniteSupportDivisor B *
          gradedNormalizedMaximalFiniteSupportDivisor C)
    {b c : Series K}
    (hbPrimitive : IsFiniteSupportPrimitive b)
    (hcPrimitive : IsFiniteSupportPrimitive c)
    (ihLeft : ∀ d : Series K,
      (d : K⟦ℝ⟧).degree < (b : K⟦ℝ⟧).degree →
        seriesNormalizedMaximalFiniteSupportDivisor (d * c) =
          seriesNormalizedMaximalFiniteSupportDivisor d *
            seriesNormalizedMaximalFiniteSupportDivisor c)
    (ihRight : ∀ d : Series K,
      (d : K⟦ℝ⟧).degree < (c : K⟦ℝ⟧).degree →
        seriesNormalizedMaximalFiniteSupportDivisor (b * d) =
          seriesNormalizedMaximalFiniteSupportDivisor b *
            seriesNormalizedMaximalFiniteSupportDivisor d) :
    IsFiniteSupportPrimitive (b * c) := by
  classical
  intro q hqbc
  by_cases hbFinite : (b : K⟦ℝ⟧).degree ≤ 0
  · exact hcPrimitive q
      ((isUnit_of_isFiniteSupportPrimitive_of_degree_le_zero hbPrimitive hbFinite).dvd_mul_left.mp
        hqbc)
  by_cases hcFinite : (c : K⟦ℝ⟧).degree ≤ 0
  · exact hbPrimitive q
      ((isUnit_of_isFiniteSupportPrimitive_of_degree_le_zero hcPrimitive hcFinite).dvd_mul_right.mp
        hqbc)
  obtain ⟨b', hdropB⟩ :=
    exists_normalizedRVMaximalFiniteSupportApproximation_of_degree_pos hgcd
      (lt_of_not_ge hbFinite)
  obtain ⟨c', hdropC⟩ :=
    exists_normalizedRVMaximalFiniteSupportApproximation_of_degree_pos hgcd
      (lt_of_not_ge hcFinite)
  have hpBUnit : IsUnit (seriesNormalizedMaximalFiniteSupportDivisor b) :=
    hbPrimitive _ (seriesNormalizedMaximalFiniteSupportDivisor_dvd_of_exists_gcd hgcd b)
  have hpCUnit : IsUnit (seriesNormalizedMaximalFiniteSupportDivisor c) :=
    hcPrimitive _ (seriesNormalizedMaximalFiniteSupportDivisor_dvd_of_exists_gcd hgcd c)
  have hrelB := isRelPrime_of_dvd_mul_of_eq_mul_add hgcd hqbc hbPrimitive hpCUnit
    (add_sub_cancel _ _) (ihLeft _ hdropB)
  have hrelC := isRelPrime_of_dvd_mul_of_eq_mul_add hgcd (by rw [mul_comm]; exact hqbc)
    hcPrimitive hpBUnit (add_sub_cancel _ _) (by rw [mul_comm, ihRight _ hdropC, mul_comm])
  have hq := dvd_gradedNormalizedMaximalFiniteSupportDivisor_rvInitialForm_of_dvd hgcd hqbc
  rw [gradedNormalizedMaximalFiniteSupportDivisor_rvInitialForm_mul hgradedMul] at hq
  let : GCDMonoid (FiniteSupportRing (K := K)) := gcdMonoidOfExistsGCD hgcd
  exact (hrelB.mul_right hrelC).isUnit_of_dvd hq

/-- Multiplicativity of normalized maximal finite-support divisors of Hahn series follows from
the corresponding leading-RV multiplicativity theorem. -/
theorem seriesNormalizedMaximalFiniteSupportDivisor_mul_of_graded
    (hgcd : ∀ p q : FiniteSupportRing (K := K),
      ∃ d : FiniteSupportRing (K := K),
        ∀ e : FiniteSupportRing (K := K), e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (hunits : ∀ u : FiniteSupportRing (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧
        u = finiteSupportScalarHom (G := ℝ) k)
    (hgradedMul : ∀ B C : DegreeGraded K,
      gradedNormalizedMaximalFiniteSupportDivisor (B * C) =
        gradedNormalizedMaximalFiniteSupportDivisor B *
          gradedNormalizedMaximalFiniteSupportDivisor C)
    (b c : Series K) :
    seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
      seriesNormalizedMaximalFiniteSupportDivisor b *
        seriesNormalizedMaximalFiniteSupportDivisor c := by
  classical
  let degreePair : Series K × Series K →
      WithBot NatOrdinal × WithBot NatOrdinal :=
    fun bc ↦ ((bc.1 : K⟦ℝ⟧).degree, (bc.2 : K⟦ℝ⟧).degree)
  let wf : WellFounded
      (Function.onFun (Prod.Lex (· < ·) (· < ·)) degreePair) :=
    (wellFounded_lt.prod_lex wellFounded_lt).onFun
  refine wf.induction (C := fun bc ↦
    seriesNormalizedMaximalFiniteSupportDivisor (bc.1 * bc.2) =
      seriesNormalizedMaximalFiniteSupportDivisor bc.1 *
        seriesNormalizedMaximalFiniteSupportDivisor bc.2) (b, c) ?_
  rintro ⟨b, c⟩ ih
  change seriesNormalizedMaximalFiniteSupportDivisor (b * c) =
    seriesNormalizedMaximalFiniteSupportDivisor b *
      seriesNormalizedMaximalFiniteSupportDivisor c
  by_cases hb : b = 0
  · subst b
    rw [zero_mul,
      seriesNormalizedMaximalFiniteSupportDivisor_zero_of_exists_gcd hgcd,
      zero_mul]
  by_cases hc : c = 0
  · subst c
    rw [mul_zero,
      seriesNormalizedMaximalFiniteSupportDivisor_zero_of_exists_gcd hgcd,
      mul_zero]
  let pB := seriesNormalizedMaximalFiniteSupportDivisor b
  let pC := seriesNormalizedMaximalFiniteSupportDivisor c
  have hpBMonic := seriesNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hb
  have hpCMonic := seriesNormalizedMaximalFiniteSupportDivisor_isMonic_of_ne_zero hgcd hc
  obtain ⟨b₀, hbFactor⟩ :=
    seriesNormalizedMaximalFiniteSupportDivisor_dvd_of_exists_gcd hgcd b
  obtain ⟨c₀, hcFactor⟩ :=
    seriesNormalizedMaximalFiniteSupportDivisor_dvd_of_exists_gcd hgcd c
  have hb₀Degree : (b₀ : K⟦ℝ⟧).degree = (b : K⟦ℝ⟧).degree :=
    degree_rightFactor_eq_of_monicFiniteSupport hpBMonic hbFactor
  have hc₀Degree : (c₀ : K⟦ℝ⟧).degree = (c : K⟦ℝ⟧).degree :=
    degree_rightFactor_eq_of_monicFiniteSupport hpCMonic hcFactor
  have hb₀Primitive : IsFiniteSupportPrimitive b₀ :=
    isFiniteSupportPrimitive_factor_of_normalizedMaximal hgcd hb hbFactor
  have hc₀Primitive : IsFiniteSupportPrimitive c₀ :=
    isFiniteSupportPrimitive_factor_of_normalizedMaximal hgcd hc hcFactor
  have hb₀c₀Primitive : IsFiniteSupportPrimitive (b₀ * c₀) :=
    isFiniteSupportPrimitive_mul_of_induction hgcd hgradedMul
      hb₀Primitive hc₀Primitive
      (fun d hd ↦ ih (d, c₀) (by
        change Prod.Lex (· < ·) (· < ·)
          ((d : K⟦ℝ⟧).degree, (c₀ : K⟦ℝ⟧).degree)
          ((b : K⟦ℝ⟧).degree, (c : K⟦ℝ⟧).degree)
        exact Prod.Lex.left _ _ (hd.trans_eq hb₀Degree)))
      (fun d hd ↦ ih (b₀, d) (by
        change Prod.Lex (· < ·) (· < ·)
          ((b₀ : K⟦ℝ⟧).degree, (d : K⟦ℝ⟧).degree)
          ((b : K⟦ℝ⟧).degree, (c : K⟦ℝ⟧).degree)
        rw [hb₀Degree]
        exact Prod.Lex.right _ (hd.trans_eq hc₀Degree)))
  let pBC := seriesNormalizedMaximalFiniteSupportDivisor (b * c)
  have hpProdDvd : pB * pC ∣ pBC := by
    exact seriesNormalizedMaximalFiniteSupportDivisor_mul_dvd_of_exists_gcd hgcd b c
  obtain ⟨r, hr⟩ := hpProdDvd
  have hpBCDvd : (pBC : Series K) ∣ b * c :=
    seriesNormalizedMaximalFiniteSupportDivisor_dvd_of_exists_gcd hgcd (b * c)
  have hleft :
      ((pB * pC * r : FiniteSupportRing (K := K)) : Series K) =
        (((pB * pC : FiniteSupportRing (K := K)) : Series K) *
          (r : Series K)) := by
    simp only [Subring.coe_mul]
  have hright :
      b * c =
        ((pB * pC : FiniteSupportRing (K := K)) : Series K) * (b₀ * c₀) := by
    rw [hbFactor, hcFactor]
    simp only [Subring.coe_mul]
    ring
  have hrDiv : (r : Series K) ∣ b₀ * c₀ := by
    have hdiv :
        ((pB * pC * r : FiniteSupportRing (K := K)) : Series K) ∣ b * c := by
      rw [← hr]
      exact hpBCDvd
    rw [hleft, hright] at hdiv
    apply (mul_dvd_mul_iff_left ?_).mp hdiv
    exact (map_ne_zero_iff
      (finiteSupportSubring (G := ℝ) (K := K)).subtype
        (finiteSupportSubring (G := ℝ) (K := K)).subtype_injective).mpr
          (mul_ne_zero hpBMonic.ne_zero hpCMonic.ne_zero)
  have hrUnit : IsUnit r := hb₀c₀Primitive r hrDiv
  have hmaxBC := (isNormalizedSeriesMaximalFiniteSupportDivisor_iff
    (b * c) pBC).mp
      (seriesNormalizedMaximalFiniteSupportDivisor_is_of_exists_gcd hgcd (b * c))
  apply seriesNormalizedMaximalFiniteSupportDivisor_eq_of_is hgcd hunits
  rw [isNormalizedSeriesMaximalFiniteSupportDivisor_iff]
  constructor
  · intro q
    rw [hmaxBC.1 q, hr, hrUnit.dvd_mul_right]
  · exact Or.inr ⟨mul_ne_zero hb hc, hpBMonic.mul hpCMonic⟩

end

end Berarducci
