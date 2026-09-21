/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.FactorizationClassification
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.TranslatedTruncationSpan
public import Mathlib.LinearAlgebra.Dimension.Finrank

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed

/-!
# Translated-truncation spans of degree-two factorisations

This module proves the part of Pommersheim--Shahriari, Proposition 3.2 used by their first
irreducibility criterion. If two nonpositive Hahn series have ordinal value `ω`, with critical
point zero, each negative translated-truncation class of their product is a coefficient-weighted
sum of the two factor classes modulo `J + K`. Consequently `V(bc)` has dimension at most two.

Combining that bound with PS06, Lemma 3.1 gives Corollary 3.3: a series outside `J + K`, with
support order type `ω²` or `ω² + 1`, is irreducible whenever `dim V(a) > 2`.

## References

* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
-/

universe v

open scoped Cardinal HahnSeries NatOrdinal

public noncomputable section

namespace PommersheimShahriari

open Berarducci HahnSeries Ordinal

variable {K : Type v} [Field K]

private theorem toSeriesQuotientByJAddConstants_mul_eq_smul_of_sub_C_mem_negativeMonomialIdeal
    {p q : Series K} {k : K}
    (hp : p - HahnSeries.Nonpositive.C k ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal K) :
    toSeriesQuotientByJAddConstants (p * q) = k • toSeriesQuotientByJAddConstants q := by
  rw [← map_smul toSeriesQuotientByJAddConstants]
  change toSeriesQuotientByJAddConstants (p * q) =
    toSeriesQuotientByJAddConstants (HahnSeries.Nonpositive.C k * q)
  rw [toSeriesQuotientByJAddConstants_eq_iff]
  have hJ : p * q - HahnSeries.Nonpositive.C k * q ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    rw [← sub_mul]
    exact Ideal.mul_mem_right q (HahnSeries.Nonpositive.negativeMonomialIdeal K) hp
  exact Berarducci.negativeMonomialIdeal_le_nearConstantSubgroup hJ

private theorem translatedTruncation_sub_C_coeff_mem_negativeMonomialIdeal
    {b : Series K} {x : ℝ}
    (hnear : translatedTruncation (b : K⟦ℝ⟧) x ∈ nearConstantSubgroup K) :
    translatedTruncation (b : K⟦ℝ⟧) x -
        HahnSeries.Nonpositive.C ((b : K⟦ℝ⟧).coeff x) ∈
      HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  have hJ := mem_nearConstantSubgroup_iff_sub_C_constantCoeff_mem.mp hnear
  convert hJ using 1
  congr 2
  rw [HahnSeries.Nonpositive.constantCoeff_apply, coeff_translatedTruncation]
  simp

private theorem toSeriesQuotientByJAddConstants_translatedTruncation_mul_eq_coeff_smul
    {b q : Series K} {x : ℝ}
    (hnear : translatedTruncation (b : K⟦ℝ⟧) x ∈ nearConstantSubgroup K) :
    toSeriesQuotientByJAddConstants (translatedTruncation (b : K⟦ℝ⟧) x * q) =
      (b : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants q :=
  toSeriesQuotientByJAddConstants_mul_eq_smul_of_sub_C_mem_negativeMonomialIdeal
    (translatedTruncation_sub_C_coeff_mem_negativeMonomialIdeal hnear)

private theorem toSeriesQuotientByJAddConstants_mul_translatedTruncation_eq_coeff_smul
    {p b : Series K} {x : ℝ}
    (hnear : translatedTruncation (b : K⟦ℝ⟧) x ∈ nearConstantSubgroup K) :
    toSeriesQuotientByJAddConstants (p * translatedTruncation (b : K⟦ℝ⟧) x) =
      (b : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants p := by
  rw [mul_comm]
  exact toSeriesQuotientByJAddConstants_translatedTruncation_mul_eq_coeff_smul hnear

private theorem translatedTruncationClass_mul_eq_sum (b c : Series K) (x : ℝ) :
    translatedTruncationClass (((b * c : Series K) : K⟦ℝ⟧)) x =
      ∑ β ∈ convolutionIndex (b : K⟦ℝ⟧) (c : K⟦ℝ⟧) x,
        toSeriesQuotientByJAddConstants
          (translatedTruncation (b : K⟦ℝ⟧) β * translatedTruncation (c : K⟦ℝ⟧) (x - β)) := by
  let s : Series K := ∑ β ∈ convolutionIndex (b : K⟦ℝ⟧) (c : K⟦ℝ⟧) x,
    translatedTruncation (b : K⟦ℝ⟧) β * translatedTruncation (c : K⟦ℝ⟧) (x - β)
  have hgerm : toGerm (translatedTruncation (((b * c : Series K) : K⟦ℝ⟧)) x) =
      toGerm s := by
    have hconv := germAt_mul (b : K⟦ℝ⟧) (c : K⟦ℝ⟧) x
    simpa only [germAt_apply, s, map_sum, map_mul, Subring.coe_mul] using hconv
  have hnear : translatedTruncation (((b * c : Series K) : K⟦ℝ⟧)) x - s ∈
      nearConstantSubgroup K :=
    negativeMonomialIdeal_le_nearConstantSubgroup (toGerm_eq_toGerm_iff.mp hgerm)
  rw [translatedTruncationClass_apply]
  calc
    toSeriesQuotientByJAddConstants (translatedTruncation (((b * c : Series K) : K⟦ℝ⟧)) x) =
        toSeriesQuotientByJAddConstants s := toSeriesQuotientByJAddConstants_eq_iff.mpr hnear
    _ = _ := by simp only [s, map_sum]

/-- PS06, Proposition 3.2(2): at a negative cutoff, the translated-truncation class of a product
of two value-`ω` factors with critical point zero is the coefficient-weighted sum of the two
factor classes modulo `J + K`. -/
theorem translatedTruncationClass_mul_eq
    {b c : Series K} (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
    (hcValue : ordinalValue c = ω^ (1 : NatOrdinal))
    (hbCritical : IsCriticalPoint b 0) (hcCritical : IsCriticalPoint c 0)
    {x : ℝ} (hx : x < 0) :
    translatedTruncationClass (((b * c : Series K) : K⟦ℝ⟧)) x =
      (c : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants b +
        (b : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants c := by
  classical
  rw [translatedTruncationClass_mul_eq_sum]
  let T := convolutionIndex (b : K⟦ℝ⟧) (c : K⟦ℝ⟧) x
  have hbNear : ∀ {y : ℝ}, y < 0 →
      translatedTruncation (b : K⟦ℝ⟧) y ∈ nearConstantSubgroup K :=
    translatedTruncation_mem_nearConstantSubgroup_of_criticalPoint_zero_of_value_omega
      hbCritical hbValue
  have hcNear : ∀ {y : ℝ}, y < 0 →
      translatedTruncation (c : K⟦ℝ⟧) y ∈ nearConstantSubgroup K :=
    translatedTruncation_mem_nearConstantSubgroup_of_criticalPoint_zero_of_value_omega
      hcCritical hcValue
  have hbClosure : closure (b : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
    closure_minimal (HahnSeries.Nonpositive.support_subset b) isClosed_Iic
  have hcClosure : closure (c : K⟦ℝ⟧).support ⊆ Set.Iic 0 :=
    closure_minimal (HahnSeries.Nonpositive.support_subset c) isClosed_Iic
  have hterm : ∀ β ∈ T,
      toSeriesQuotientByJAddConstants
          (translatedTruncation (b : K⟦ℝ⟧) β * translatedTruncation (c : K⟦ℝ⟧) (x - β)) =
        if β = 0 then
          (c : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants b
        else if β = x then
          (b : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants c
        else 0 := by
    intro β hβ
    have hβClosure := mem_convolutionIndex.mp hβ
    have hβle : β ≤ 0 := hbClosure hβClosure.1
    have hxβle : x - β ≤ 0 := hcClosure hβClosure.2
    by_cases hβ0 : β = 0
    · subst β
      rw [if_pos rfl, _root_.sub_zero, translatedTruncation_zero]
      exact toSeriesQuotientByJAddConstants_mul_translatedTruncation_eq_coeff_smul (hcNear hx)
    · rw [if_neg hβ0]
      by_cases hβx : β = x
      · subst β
        rw [if_pos rfl, _root_.sub_self, translatedTruncation_zero]
        exact toSeriesQuotientByJAddConstants_translatedTruncation_mul_eq_coeff_smul (hbNear hx)
      · rw [if_neg hβx]
        have hβneg : β < 0 := lt_of_le_of_ne hβle hβ0
        have hxβneg : x - β < 0 := by
          apply lt_of_le_of_ne hxβle
          intro heq
          exact hβx (by linarith)
        rw [toSeriesQuotientByJAddConstants_translatedTruncation_mul_eq_coeff_smul (hbNear hβneg)]
        rw [toSeriesQuotientByJAddConstants_eq_zero_iff.mpr (hcNear hxβneg), smul_zero]
  rw [Finset.sum_congr rfl hterm]
  let B := (c : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants b
  let C := (b : K⟦ℝ⟧).coeff x • toSeriesQuotientByJAddConstants c
  have hsplit : ∀ β : ℝ,
      (if β = 0 then B else if β = x then C else 0) =
        (if β = 0 then B else 0) + (if β = x then C else 0) := by
    intro β
    by_cases hβ0 : β = 0
    · subst β
      simp [hx.ne']
    · simp [hβ0]
  have hzero : (if 0 ∈ T then B else 0) = B := by
    by_cases hxClosure : x ∈ closure (c : K⟦ℝ⟧).support
    · rw [if_pos]
      exact mem_convolutionIndex.mpr
        ⟨hbCritical.mem_closure_support, by simpa using hxClosure⟩
    · have hxSupport : x ∉ (c : K⟦ℝ⟧).support :=
        fun hmem ↦ hxClosure (subset_closure hmem)
      rw [HahnSeries.mem_support, not_ne_iff] at hxSupport
      have hnot : 0 ∉ T := by
        rw [mem_convolutionIndex]
        simp [hxClosure]
      simp [hnot, B, hxSupport]
  have hxIndex : (if x ∈ T then C else 0) = C := by
    by_cases hxClosure : x ∈ closure (b : K⟦ℝ⟧).support
    · rw [if_pos]
      exact mem_convolutionIndex.mpr
        ⟨hxClosure, by simpa using hcCritical.mem_closure_support⟩
    · have hxSupport : x ∉ (b : K⟦ℝ⟧).support :=
        fun hmem ↦ hxClosure (subset_closure hmem)
      rw [HahnSeries.mem_support, not_ne_iff] at hxSupport
      have hnot : x ∉ T := by
        rw [mem_convolutionIndex]
        simp [hxClosure]
      simp [hnot, C, hxSupport]
  calc
    (∑ β ∈ T, if β = 0 then B else if β = x then C else 0) =
        (∑ β ∈ T, if β = 0 then B else 0) +
          ∑ β ∈ T, if β = x then C else 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun β _ ↦ hsplit β
    _ = (if 0 ∈ T then B else 0) + (if x ∈ T then C else 0) := by simp
    _ = B + C := by rw [hzero, hxIndex]

/-- PS06, Proposition 3.2(5), upper-bound direction: `V(bc)` is contained in the span of the two
factor classes modulo `J + K`. -/
theorem translatedTruncationSpan_mul_le_span_pair
    {b c : Series K} (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
    (hcValue : ordinalValue c = ω^ (1 : NatOrdinal))
    (hbCritical : IsCriticalPoint b 0) (hcCritical : IsCriticalPoint c 0) :
    translatedTruncationSpan (b * c) ≤
      Submodule.span K {toSeriesQuotientByJAddConstants b, toSeriesQuotientByJAddConstants c} := by
  rw [translatedTruncationSpan_le_iff]
  intro x hx
  rw [translatedTruncationClass_mul_eq hbValue hcValue hbCritical hcCritical hx]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)

/-- PS06, Proposition 3.2(5): a balanced product has translated-truncation-span dimension at most
two. -/
theorem rank_translatedTruncationSpan_mul_le_two
    {b c : Series K} (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
    (hcValue : ordinalValue c = ω^ (1 : NatOrdinal))
    (hbCritical : IsCriticalPoint b 0) (hcCritical : IsCriticalPoint c 0) :
    Module.rank K (translatedTruncationSpan (b * c)) ≤ 2 := by
  classical
  let s : Set (SeriesQuotientByJAddConstants K) :=
    {toSeriesQuotientByJAddConstants b, toSeriesQuotientByJAddConstants c}
  have hs : s.Finite := (Set.finite_singleton _).insert _
  letI : Fintype s := hs.fintype
  have hcard : s.toFinset.card ≤ 2 := by
    change ({toSeriesQuotientByJAddConstants b, toSeriesQuotientByJAddConstants c} :
      Set (SeriesQuotientByJAddConstants K)).toFinset.card ≤ 2
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  calc
    Module.rank K (translatedTruncationSpan (b * c)) ≤
        Module.rank K (Submodule.span K s) :=
      Submodule.rank_mono
        (by simpa [s] using
          translatedTruncationSpan_mul_le_span_pair hbValue hcValue hbCritical hcCritical)
    _ ≤ #s := rank_span_le s
    _ ≤ 2 := by
      rw [Cardinal.mk_fintype, ← Set.toFinset_card]
      exact_mod_cast hcard

/-- The finite-rank form of PS06, Proposition 3.2(5). -/
theorem finrank_translatedTruncationSpan_mul_le_two
    {b c : Series K} (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
    (hcValue : ordinalValue c = ω^ (1 : NatOrdinal))
    (hbCritical : IsCriticalPoint b 0) (hcCritical : IsCriticalPoint c 0) :
    Module.finrank K (translatedTruncationSpan (b * c)) ≤ 2 := by
  classical
  let s : Set (SeriesQuotientByJAddConstants K) :=
    {toSeriesQuotientByJAddConstants b, toSeriesQuotientByJAddConstants c}
  have hs : s.Finite := (Set.finite_singleton _).insert _
  letI : Fintype s := hs.fintype
  letI : Module.Finite K
      (Submodule.span K s) := Module.Finite.span_of_finite K hs
  have hcard : s.toFinset.card ≤ 2 := by
    change ({toSeriesQuotientByJAddConstants b, toSeriesQuotientByJAddConstants c} :
      Set (SeriesQuotientByJAddConstants K)).toFinset.card ≤ 2
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  calc
    Module.finrank K (translatedTruncationSpan (b * c)) ≤
        Module.finrank K (Submodule.span K s) :=
      Submodule.finrank_mono
        (by simpa [s] using
          translatedTruncationSpan_mul_le_span_pair hbValue hcValue hbCritical hcCritical)
    _ ≤ s.toFinset.card := finrank_span_le_card s
    _ ≤ 2 := hcard

private theorem mem_nearConstantSubgroup_of_isUnit {a : Series K} (ha : IsUnit a) :
    a ∈ nearConstantSubgroup K := by
  have hsupport := HahnSeries.Nonpositive.support_eq_singleton_zero_of_isUnit ha
  have hconstant : HahnSeries.Nonpositive.C
      (HahnSeries.Nonpositive.constantCoeff a) = a := by
    apply Subtype.ext
    apply HahnSeries.coeff_injective
    funext x
    by_cases hx : x = 0
    · subst x
      simp [HahnSeries.Nonpositive.constantCoeff_apply]
    · have hxmem : x ∉ (a : K⟦ℝ⟧).support := by
        rw [hsupport]
        simpa using hx
      rw [HahnSeries.mem_support, not_ne_iff] at hxmem
      simp [hx, hxmem]
  exact Berarducci.mem_nearConstantSubgroup_iff.mpr
    ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem,
      HahnSeries.Nonpositive.constantCoeff a, by simpa using hconstant⟩

/-- PS06, Corollary 3.3: a degree-two series outside `J + K` whose translated-truncation span has
dimension greater than two is irreducible. -/
@[blueprint "fact:ps06-irreducibility"
  (phase := "Primality and factorisation for real exponents")
  (title := "Irreducibility from translated truncation dimension")
  (statement := /--
    Let $K$ be a field of characteristic $0$ and
    $a\in K((\mathbb R^{\le 0}))$.  Assume that
    \[
      \operatorname{ot}(a)=\omega^2\quad\text{or}\quad
      \operatorname{ot}(a)=\omega^2+1,
    \]
    and that $0$ is an accumulation point of $\operatorname{supp}(a)$,
    equivalently $a\notin J+K$.  In
    $K((\mathbb R^{\le 0}))/(J+K)$, take the $K$-linear span of the classes of
    the translated truncations $a^{\vert x}$ for $x<0$.  If this span has
    dimension greater than $2$, then $a$ is irreducible in
    $K((\mathbb R^{\le 0}))$.  This is [PS06, Cor. 3.3] (Theorem A).
  -/)
  (proof := /--
    Suppose that $a=bc$.  After exchanging the factors if necessary, the
    factorisation classification for these two support order types leaves two
    cases: either $b$ is a nonzero constant, or
    $v_J(b)=v_J(c)=\omega$.  In the second case, multiplicativity of $v_J$ from
    \ref{fact:ordinal-value-multiplicativity}, together with the support-tail bound for
    negative translated truncations, forces the critical points of $b$ and $c$ to be $0$.
    The convolution formula modulo
    $J+K$ then writes, for every $x<0$, the class of $a^{\vert x}$ as
    \[
      c_x[b]+b_x[c].
    \]
    Thus the classes of translated truncations of $a$ lie in the span of $[b]$ and
    $[c]$, which has dimension at most $2$, a contradiction.  Hence one factor
    is a unit, and $a$ is irreducible.
  -/)]
theorem irreducible_of_two_lt_rank_translatedTruncationSpan [CharZero K] {a : Series K}
    (haNear : a ∉ nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) ∨
      (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1)
    (haDimension : (2 : Cardinal) < Module.rank K (translatedTruncationSpan a)) :
    Irreducible a := by
  rw [irreducible_iff]
  refine ⟨fun haUnit ↦ haNear (mem_nearConstantSubgroup_of_isUnit haUnit), ?_⟩
  intro b c habc
  have haNe : a ≠ 0 := by
    intro ha
    apply haNear
    rw [ha]
    exact (nearConstantSubgroup K).zero_mem
  have hbNe : b ≠ 0 := by
    intro hb
    apply haNe
    rw [habc, hb, zero_mul]
  have hcNe : c ≠ 0 := by
    intro hc
    apply haNe
    rw [habc, hc, mul_zero]
  have haValue : ordinalValue a = ω^ (2 : NatOrdinal) :=
    ordinalValue_eq_wpow_two haNear haType
  have haNegative : ∀ u : ℝ, u < 0 →
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ω^ (2 : NatOrdinal) :=
    fun _ hu ↦ ordinalValue_translatedTruncation_lt_wpow_two haNear haType hu
  have balancedContradiction
      (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
      (hcValue : ordinalValue c = ω^ (1 : NatOrdinal)) : False := by
    obtain ⟨x, hx⟩ := exists_isCriticalPoint hbNe
    obtain ⟨y, hy⟩ := exists_isCriticalPoint hcNe
    obtain ⟨rfl, rfl⟩ := criticalPoints_eq_zero_of_product_wpow_two
      habc haValue haNegative hx hy
    have hdim : Module.rank K (translatedTruncationSpan a) ≤ 2 := by
      rw [habc]
      exact rank_translatedTruncationSpan_mul_le_two hbValue hcValue hx hy
    exact (not_lt_of_ge hdim) haDimension
  rcases le_total (ordinalValue b) (ordinalValue c) with hbc | hcb
  · rcases factorization_cases_of_supportOrderType_wpow_two
      haNear haType habc hbc with hconstant | hbalanced
    · obtain ⟨k, hk, rfl, -⟩ := hconstant
      exact Or.inl ((isUnit_iff_ne_zero.mpr hk).map HahnSeries.Nonpositive.C)
    · exact (balancedContradiction hbalanced.2.2.1 hbalanced.2.2.2).elim
  · have hacb : a = c * b := by simpa [mul_comm] using habc
    rcases factorization_cases_of_supportOrderType_wpow_two
      haNear haType hacb hcb with hconstant | hbalanced
    · obtain ⟨k, hk, rfl, -⟩ := hconstant
      exact Or.inr ((isUnit_iff_ne_zero.mpr hk).map HahnSeries.Nonpositive.C)
    · exact (balancedContradiction hbalanced.2.2.2 hbalanced.2.2.1).elim

/-- The finite-rank specialization of PS06, Corollary 3.3. -/
theorem irreducible_of_two_lt_finrank_translatedTruncationSpan [CharZero K] {a : Series K}
    (haNear : a ∉ nearConstantSubgroup K)
    (haType : (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) ∨
      (a : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 ^ (2 : Ordinal) + 1)
    (haDimension : 2 < Module.finrank K (translatedTruncationSpan a)) :
    Irreducible a := by
  rw [irreducible_iff]
  refine ⟨fun haUnit ↦ haNear (mem_nearConstantSubgroup_of_isUnit haUnit), ?_⟩
  intro b c habc
  have haNe : a ≠ 0 := by
    intro ha
    apply haNear
    rw [ha]
    exact (nearConstantSubgroup K).zero_mem
  have hbNe : b ≠ 0 := by
    intro hb
    apply haNe
    rw [habc, hb, zero_mul]
  have hcNe : c ≠ 0 := by
    intro hc
    apply haNe
    rw [habc, hc, mul_zero]
  have haValue : ordinalValue a = ω^ (2 : NatOrdinal) :=
    ordinalValue_eq_wpow_two haNear haType
  have haNegative : ∀ u : ℝ, u < 0 →
      ordinalValue (translatedTruncation (a : K⟦ℝ⟧) u) < ω^ (2 : NatOrdinal) :=
    fun _ hu ↦ ordinalValue_translatedTruncation_lt_wpow_two haNear haType hu
  have balancedContradiction
      (hbValue : ordinalValue b = ω^ (1 : NatOrdinal))
      (hcValue : ordinalValue c = ω^ (1 : NatOrdinal)) : False := by
    obtain ⟨x, hx⟩ := exists_isCriticalPoint hbNe
    obtain ⟨y, hy⟩ := exists_isCriticalPoint hcNe
    obtain ⟨rfl, rfl⟩ := criticalPoints_eq_zero_of_product_wpow_two
      habc haValue haNegative hx hy
    have hdim : Module.finrank K (translatedTruncationSpan a) ≤ 2 := by
      rw [habc]
      exact finrank_translatedTruncationSpan_mul_le_two hbValue hcValue hx hy
    exact (not_lt_of_ge hdim) haDimension
  rcases le_total (ordinalValue b) (ordinalValue c) with hbc | hcb
  · rcases factorization_cases_of_supportOrderType_wpow_two
      haNear haType habc hbc with hconstant | hbalanced
    · obtain ⟨k, hk, rfl, -⟩ := hconstant
      exact Or.inl ((isUnit_iff_ne_zero.mpr hk).map HahnSeries.Nonpositive.C)
    · exact (balancedContradiction hbalanced.2.2.1 hbalanced.2.2.2).elim
  · have hacb : a = c * b := by simpa [mul_comm] using habc
    rcases factorization_cases_of_supportOrderType_wpow_two
      haNear haType hacb hcb with hconstant | hbalanced
    · obtain ⟨k, hk, rfl, -⟩ := hconstant
      exact Or.inr ((isUnit_iff_ne_zero.mpr hk).map HahnSeries.Nonpositive.C)
    · exact (balancedContradiction hbalanced.2.2.2 hbalanced.2.2.1).elim

end PommersheimShahriari
