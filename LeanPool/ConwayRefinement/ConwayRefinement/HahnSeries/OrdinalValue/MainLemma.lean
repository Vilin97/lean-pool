/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PurePowerRemainder

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueConstantMul
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage

/-!
# Ingredients of Berarducci's main lemma

The proof of Berarducci, Lemma 8.2 rewrites the expected value `⊙^k v_J(b) ⊙ v_J(c)` as the
ordinary product `[⊙^{k-1} v_J(b) ⊙ v_J^r(b) ⊙ v_J(c)] * v_J^p(b)`, so that ordinal
multiplication is continuous in its second argument there; the Hessenberg product is not. The
conversion is justified by the criterion on Cantor terms, and the hypothesis
`v_J^p(b) ≤ v_J^p(c)` is exactly what supplies it: every canonical multiplicative factor of an
ordinal value or of a residual value is at least the corresponding principal value.

The remaining ingredients are the invariance of the ordinal value under negation and under a
nonzero natural-number scalar. The second is the only place where the characteristic-zero
hypothesis of the source is used: in characteristic `p` the coefficient `k` of the surviving term
could annihilate it.
-/

universe v

public noncomputable section

open HahnSeries Ordinal

namespace Berarducci

variable {K : Type v} [Field K]

/-- `Y` is additive principal and each of its canonical multiplicative factors is at least
`ω ^ w`. -/
private def GoodAt (w : Ordinal) (Y : NatOrdinal) : Prop :=
  IsAdditivelyPrincipal Y.val ∧
    ∀ t ∈ (log omega0 Y.val).additivePrincipalTerms, w ≤ t

private theorem GoodAt.one (w : Ordinal) : GoodAt w 1 := by
  refine ⟨isAdditivelyPrincipal_iff.mpr ⟨0, by simp⟩, fun t ht ↦ ?_⟩
  rw [show ((1 : NatOrdinal).val) = 1 from rfl, log_one_right,
    additivePrincipalTerms_zero] at ht
  exact absurd ht (List.not_mem_nil)

private theorem GoodAt.mul {w : Ordinal} {Y Z : NatOrdinal}
    (hY : GoodAt w Y) (hZ : GoodAt w Z) : GoodAt w (Y * Z) := by
  have hYval : NatOrdinal.of Y.val = Y := NatOrdinal.of_val Y
  have hZval : NatOrdinal.of Z.val = Z := NatOrdinal.of_val Z
  have hprod : (NatOrdinal.of Y.val * NatOrdinal.of Z.val).val = (Y * Z).val := by
    rw [hYval, hZval]
  constructor
  · obtain ⟨e, he⟩ := isAdditivelyPrincipal_iff.mp hY.1
    obtain ⟨f, hf⟩ := isAdditivelyPrincipal_iff.mp hZ.1
    refine isAdditivelyPrincipal_iff.mpr
      ⟨(NatOrdinal.of e + NatOrdinal.of f).val, ?_⟩
    rw [← hprod, he, hf, NatOrdinal.of_omega0_opow, NatOrdinal.of_omega0_opow,
      ← NatOrdinal.wpow_add, NatOrdinal.val_wpow]
  · intro t ht
    rw [← hprod] at ht
    rcases mem_additivePrincipalTerms_log_natMul hY.1 hZ.1 ht with h | h
    · exact hY.2 t h
    · exact hZ.2 t h

private theorem GoodAt.pow {w : Ordinal} {Y : NatOrdinal} (hY : GoodAt w Y) (n : ℕ) :
    GoodAt w (Y ^ n) := by
  induction n with
  | zero => simpa using GoodAt.one w
  | succ n ih => rw [pow_succ]; exact ih.mul hY

private theorem goodAt_principalValue (b : SeriesWithOrdinalValueAboveOne K) :
    GoodAt (log omega0 b.principalValue.val) b.principalValue := by
  refine ⟨b.principalValue_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal,
    fun t ht ↦ ?_⟩
  rw [additivePrincipalTerms_of_isAdditivelyPrincipal
    b.isAdditivelyPrincipal_log_principalValue, List.mem_singleton] at ht
  exact ht.ge

private theorem goodAt_residualValue (b : SeriesWithOrdinalValueAboveOne K) :
    GoodAt (log omega0 b.principalValue.val) b.residualValue :=
  ⟨b.residualValue_isAdditivelyPrincipal,
    fun _ ht ↦ b.log_principalValue_le_of_mem_terms_residualValue ht⟩

private theorem goodAt_ordinalValue (b : SeriesWithOrdinalValueAboveOne K) :
    GoodAt (log omega0 b.principalValue.val) (ordinalValue b.1) :=
  ⟨ordinalValue_isAdditivelyPrincipal_of_one_lt b.2,
    fun _ ht ↦ b.log_principalValue_le_of_mem_terms_ordinalValue ht⟩

private theorem GoodAt.mono {w w' : Ordinal} {Y : NatOrdinal} (hY : GoodAt w Y)
    (hw : w' ≤ w) : GoodAt w' Y :=
  ⟨hY.1, fun t ht ↦ hw.trans (hY.2 t ht)⟩

private theorem log_principalValue_mono {b c : SeriesWithOrdinalValueAboveOne K}
    (hp : b.principalValue ≤ c.principalValue) :
    log omega0 b.principalValue.val ≤ log omega0 c.principalValue.val := by
  have hle : b.principalValue.val ≤ c.principalValue.val := NatOrdinal.val.monotone hp
  rw [← b.principalValue_val_eq_opow_log, ← c.principalValue_val_eq_opow_log] at hle
  exact (opow_le_opow_iff_right one_lt_omega0).mp hle

private theorem goodAt_powerRemainderBound (b c : SeriesWithOrdinalValueAboveOne K)
    (hp : b.principalValue ≤ c.principalValue) (m : ℕ) :
    GoodAt (log omega0 b.principalValue.val) (powerRemainderBound b c m) := by
  rw [powerRemainderBound_eq]
  exact (((goodAt_ordinalValue b).pow m).mul (goodAt_residualValue b)).mul
    ((goodAt_ordinalValue c).mono (log_principalValue_mono hp))

/-- The remainder bound is additive principal. -/
theorem isAdditivelyPrincipal_powerRemainderBound (b c : SeriesWithOrdinalValueAboveOne K)
    (hp : b.principalValue ≤ c.principalValue) (m : ℕ) :
    IsAdditivelyPrincipal (powerRemainderBound b c m).val :=
  (goodAt_powerRemainderBound b c hp m).1

/-- The Hessenberg-to-ordinary conversion described above, at the expected value. -/
theorem powerRemainderBound_mul_principalValue_val
    (b c : SeriesWithOrdinalValueAboveOne K) (hp : b.principalValue ≤ c.principalValue) (m : ℕ) :
    (powerRemainderBound b c m * b.principalValue).val
      = (powerRemainderBound b c m).val * b.principalValue.val := by
  have hX := goodAt_powerRemainderBound b c hp m
  have h := natOrdinal_of_mul_wpow_eq_mul_of_log_terms
    b.isAdditivelyPrincipal_log_principalValue hX.1 hX.2
  rw [b.principalValue_val_eq_opow_log, NatOrdinal.of_val, NatOrdinal.of_val] at h
  exact (congrArg NatOrdinal.val h).symm

private theorem goodAt_powerRemainderBoundOne (b : SeriesWithOrdinalValueAboveOne K) (m : ℕ) :
    GoodAt (log omega0 b.principalValue.val) (powerRemainderBoundOne b m) := by
  rw [powerRemainderBoundOne_eq]
  exact ((goodAt_ordinalValue b).pow m).mul (goodAt_residualValue b)

/-- The pure-power remainder bound is additive principal. -/
theorem isAdditivelyPrincipal_powerRemainderBoundOne (b : SeriesWithOrdinalValueAboveOne K)
    (m : ℕ) : IsAdditivelyPrincipal (powerRemainderBoundOne b m).val :=
  (goodAt_powerRemainderBoundOne b m).1

/-- The Hessenberg-to-ordinary conversion for a pure power. No comparison of principal values is
needed: both factors of the bound come from `b` itself. -/
theorem powerRemainderBoundOne_mul_principalValue_val (b : SeriesWithOrdinalValueAboveOne K)
    (m : ℕ) : (powerRemainderBoundOne b m * b.principalValue).val
      = (powerRemainderBoundOne b m).val * b.principalValue.val := by
  have hX := goodAt_powerRemainderBoundOne b m
  have h := natOrdinal_of_mul_wpow_eq_mul_of_log_terms
    b.isAdditivelyPrincipal_log_principalValue hX.1 hX.2
  rw [b.principalValue_val_eq_opow_log, NatOrdinal.of_val, NatOrdinal.of_val] at h
  exact (congrArg NatOrdinal.val h).symm

/-- Berarducci, Lemma 8.2: a value strictly below the expected one is bounded by a proper
ordinary multiple of the remainder bound. -/
theorem exists_le_mul_of_lt_powerRemainderBound_mul
    (b c : SeriesWithOrdinalValueAboveOne K) (hp : b.principalValue ≤ c.principalValue) (m : ℕ)
    {u : NatOrdinal} (hu : u < powerRemainderBound b c m * b.principalValue) :
    ∃ α < b.principalValue.val, u.val ≤ (powerRemainderBound b c m).val * α := by
  have hlt : u.val < (powerRemainderBound b c m).val * b.principalValue.val := by
    rw [← powerRemainderBound_mul_principalValue_val b c hp m]
    exact NatOrdinal.val.lt_iff_lt.mpr hu
  obtain ⟨α, hα, hlt'⟩ :=
    (Ordinal.lt_mul_iff_of_isSuccLimit
      b.principalValue_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp hlt
  exact ⟨α, hα, hlt'.le⟩

private theorem goodAt_prod {w : Ordinal} (l : Multiset (SeriesWithOrdinalValueAboveOne K))
    (hl : ∀ y ∈ l, GoodAt w (ordinalValue y.1)) :
    GoodAt w (l.map fun y ↦ ordinalValue y.1).prod := by
  induction l using Multiset.induction with
  | empty => simpa using GoodAt.one w
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact (hl a (Multiset.mem_cons_self a s)).mul
      (ih fun y hy ↦ hl y (Multiset.mem_cons_of_mem hy))

/-- If every factor of a product has principal value at least that of `b`, then so does the
product. This supplies the hypothesis of Lemma 8.2 when the second factor is itself a product. -/
theorem principalValue_le_of_forall_mem (b c : SeriesWithOrdinalValueAboveOne K)
    (l : Multiset (SeriesWithOrdinalValueAboveOne K))
    (hl : ∀ y ∈ l, b.principalValue ≤ y.principalValue)
    (hc : ordinalValue c.1 = (l.map fun y ↦ ordinalValue y.1).prod) :
    b.principalValue ≤ c.principalValue := by
  have hgood := goodAt_prod (w := log omega0 b.principalValue.val) l
    fun y hy ↦ (goodAt_ordinalValue y).mono (log_principalValue_mono (hl y hy))
  rw [← hc] at hgood
  exact b.le_principalValue_of_forall_mem_terms c fun t ht ↦ hgood.2 t ht

theorem ordinalValue_neg (x : Series K) : ordinalValue (-x) = ordinalValue x := by
  have hx : -x = HahnSeries.Nonpositive.C (-1 : K) * x := by
    rw [map_neg, map_one, neg_one_mul]
  rw [hx, ordinalValue_C_mul (neg_ne_zero.mpr one_ne_zero)]

theorem germOrdinalValue_neg (q : Germ K) : germOrdinalValue (-q) = germOrdinalValue q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_neg, germOrdinalValue_mk, germOrdinalValue_mk, ordinalValue_neg]

/-- A nonzero natural-number scalar does not change the ordinal value. This is the only place
where the characteristic-zero hypothesis is used. -/
theorem ordinalValue_nsmul {n : ℕ} (hn : (n : K) ≠ 0) (x : Series K) :
    ordinalValue (n • x) = ordinalValue x := by
  have hns : (n • x : Series K) = HahnSeries.Nonpositive.C ((n : K)) * x := by
    rw [map_natCast HahnSeries.Nonpositive.C n]
    exact nsmul_eq_mul _ _
  rw [hns, ordinalValue_C_mul hn]

theorem germOrdinalValue_nsmul {n : ℕ} (hn : (n : K) ≠ 0) (q : Germ K) :
    germOrdinalValue (n • q) = germOrdinalValue q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_nsmul, germOrdinalValue_mk, germOrdinalValue_mk, ordinalValue_nsmul hn]

end Berarducci
