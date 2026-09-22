/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponent
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.TruncationDrop
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.IncreasingSequenceUnion
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation
public import Mathlib.RingTheory.HahnSeries.Summable
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationPolynomial

/-!
# Sums along a sequence of cutoffs: prescribed classes at prescribed cutoffs

Given series `w_k`, negative reals `c_k` and cutoffs `γ_k`, their *sum along the sequence of
cutoffs* `γ_k` is

  `s = ∑_k (w_k)_{>c_k} t^{γ_k}`,  `γ_0 < γ_1 < ⋯ < 0`, `sup_k γ_k = 0`, `c_k < 0`,
  `γ_k ≤ γ_{k+1} + c_{k+1}`,

whose `k`-th term `(w_k)_{>c_k} t^{γ_k}` (`placedTerm w c γ k`) places the upper truncation
`(w_k)_{>c_k}` [LM24, Def. 3.2.2] at `γ_k`. The intervals `(γ_k + c_k, γ_k]` are pairwise disjoint
and increasing, so the supports of the terms form an increasing sequence of well-ordered sets and
their union is well ordered ([Ber00, Lem. 4.1] is the two-set case); on `(γ_k + c_k, γ_k]` the
coefficients of `s` are those of the `k`-th term, and off these intervals they vanish
(`sumAlongCutoffs`). This is the construction behind Berarducci's "hyper-series" [Ber00, §6].

Let `δ` be an ordinal, `γ_0 < γ_1 < ⋯ < 0` cutoffs with supremum `0`, and `a_k ∈ P_δ` classes.
There is a series `s ∈ J_{ω^(δ+2)}` whose translated truncation at `γ_k` represents `a_k` in `P_δ`
for every `k`, and whose translated truncation at every other cutoff `ξ ∈ (γ_0, 0)` has ordinal
value below `ω^δ` (`exists_sumAlongCutoffs`): choose principal representatives `w_k` of the `a_k`,
choose `c_k < 0` so close to `0` that the translated truncations of `w_k` at the cutoffs in
`(c_k, 0)` have ordinal value below `ω^δ` and that `γ_k ≤ γ_{k+1} + c_{k+1}`, and take this sum.
Its support is the union of an increasing sequence of sets of order type at most `ω^δ`, hence has
order type at most `ω^δ · ω = ω^(δ+1)`.

Read through the derivation `∂` on `P_{δ+1}`, this says that every function at `0⁻` with values in
`P_δ` vanishing outside a sequence `γ_k ↑ 0` is a derivative.
-/

universe v

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-! ### The terms of a sum along cutoffs -/

/-- The `k`-th term `(w_k)_{>c_k} t^{γ_k}` of the sum along cutoffs: the part of
`w k` with exponents in `(c k, 0]`, placed at `γ k`. -/
def placedTerm (w : ℕ → Series K) (c γ : ℕ → ℝ) (k : ℕ) : K⟦ℝ⟧ :=
  HahnSeries.translate (γ k) (truncGT (c k) (w k : K⟦ℝ⟧))

theorem coeff_placedTerm (w : ℕ → Series K) (c γ : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    (placedTerm w c γ k).coeff x = if c k < x - γ k then (w k : K⟦ℝ⟧).coeff (x - γ k) else 0 := by
  rw [placedTerm, coeff_translate]
  split_ifs with h
  · exact coeff_truncGT_of_lt h _
  · exact coeff_truncGT_of_le (not_lt.mp h) _

/-- The support of the `k`-th term lies in `(γ k + c k, γ k]`. -/
theorem support_placedTerm_subset (w : ℕ → Series K) (c γ : ℕ → ℝ) (k : ℕ) :
    (placedTerm w c γ k).support ⊆ Set.Ioc (γ k + c k) (γ k) := by
  intro x hx
  rw [HahnSeries.mem_support, coeff_placedTerm] at hx
  split_ifs at hx with h
  · have hle : x - γ k ≤ 0 :=
      HahnSeries.Nonpositive.support_subset (w k) ((HahnSeries.mem_support _ _).mpr hx)
    exact ⟨by linarith, by linarith⟩
  · exact absurd rfl hx

/-- The support of a term in the sum along cutoffs is partially well ordered. -/
theorem support_placedTerm_isPWO (w : ℕ → Series K) (c γ : ℕ → ℝ) (k : ℕ) :
    (placedTerm w c γ k).support.IsPWO :=
  (placedTerm w c γ k).isPWO_support

/-- The order type of the support of the `k`-th term is at most that of `w k`. -/
theorem supportOrderType_placedTerm_le (w : ℕ → Series K) (c γ : ℕ → ℝ) (k : ℕ) :
    (placedTerm w c γ k).supportOrderType ≤ (w k : K⟦ℝ⟧).supportOrderType := by
  rw [placedTerm, supportOrderType_translate, supportOrderType_eq_setOrderType,
    supportOrderType_eq_setOrderType]
  exact Set.IsPWO.orderType_mono _ _ (support_truncGT_subset (c k) (w k : K⟦ℝ⟧))

section Family

variable (w : ℕ → Series K) (c γ : ℕ → ℝ) (hγ : StrictMono γ)
  (hdisj : ∀ k, γ k ≤ γ (k + 1) + c (k + 1))
include hγ hdisj

/-- The intervals `(γ k + c k, γ k]` are pairwise disjoint and increasing. -/
theorem placedTerm_interval_lt {j k : ℕ} (hjk : j < k) {x y : ℝ}
    (hx : x ∈ Set.Ioc (γ j + c j) (γ j))
    (hy : y ∈ Set.Ioc (γ k + c k) (γ k)) : x < y := by
  have h1 : γ j ≤ γ (k - 1) := hγ.monotone (by omega)
  have h2 : γ (k - 1) ≤ γ k + c k := by
    have := hdisj (k - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)] at this
  linarith [hx.2, hy.1]

/-- The supports of the terms form an increasing sequence of sets: for `j < k`, every point of
the support of the `j`-th term lies below every point of the support of the `k`-th. -/
theorem placedTerm_support_lt {j k : ℕ} (hjk : j < k) {x y : ℝ}
    (hx : x ∈ (placedTerm w c γ j).support)
    (hy : y ∈ (placedTerm w c γ k).support) : x < y :=
  placedTerm_interval_lt c γ hγ hdisj hjk (support_placedTerm_subset w c γ j hx)
    (support_placedTerm_subset w c γ k hy)

/-- The terms in the sum along cutoffs form a summable family. -/
def placedTerms : SummableFamily ℝ K ℕ where
  toFun := placedTerm w c γ
  isPWO_iUnion_support' :=
    Set.IsPWO.iUnion_of_ordered (fun k ↦ support_placedTerm_isPWO w c γ k)
      fun j k hjk x hx y hy ↦ placedTerm_support_lt w c γ hγ hdisj hjk hx hy
  finite_co_support' x := by
    refine Set.Subsingleton.finite fun j hj k hk ↦ ?_
    by_contra hne
    rcases Ne.lt_or_gt hne with h | h
    · exact (placedTerm_support_lt w c γ hγ hdisj h hj hk).false
    · exact (placedTerm_support_lt w c γ hγ hdisj h hk hj).false

theorem placedTerms_apply (k : ℕ) : placedTerms w c γ hγ hdisj k = placedTerm w c γ k := (rfl)

/-- The sum along the sequence of cutoffs `γ_k`, `s = ∑_k (w_k)_{>c_k} t^{γ_k}`. -/
def sumAlongCutoffs : K⟦ℝ⟧ := (placedTerms w c γ hγ hdisj).hsum

/-- The support of the sum along cutoffs lies in the union of the intervals
`(γ k + c k, γ k]`. -/
theorem support_sumAlongCutoffs_subset :
    (sumAlongCutoffs w c γ hγ hdisj).support ⊆ ⋃ k, Set.Ioc (γ k + c k) (γ k) :=
  SummableFamily.support_hsum_subset.trans
    (Set.iUnion_mono fun k ↦ support_placedTerm_subset w c γ k)

/-- On the `k`-th interval, the coefficient of the sum is that of its `k`-th term. -/
theorem coeff_sumAlongCutoffs_of_mem {k : ℕ} {x : ℝ} (hx : x ∈ Set.Ioc (γ k + c k) (γ k)) :
    (sumAlongCutoffs w c γ hγ hdisj).coeff x = (placedTerm w c γ k).coeff x := by
  rw [sumAlongCutoffs, SummableFamily.coeff_hsum]
  rw [finsum_eq_single _ k]
  · rfl
  · intro j hjk
    by_contra hne
    have hmem : x ∈ (placedTerm w c γ j).support := (HahnSeries.mem_support _ _).mpr hne
    have hj := support_placedTerm_subset w c γ j hmem
    rcases Ne.lt_or_gt hjk with h | h
    · exact (placedTerm_interval_lt c γ hγ hdisj h hj hx).false
    · exact (placedTerm_interval_lt c γ hγ hdisj h hx hj).false

/-- Off every interval `(γ k + c k, γ k]` the coefficient of the sum along cutoffs vanishes. -/
theorem coeff_sumAlongCutoffs_eq_zero {x : ℝ} (hx : ∀ k, x ∉ Set.Ioc (γ k + c k) (γ k)) :
    (sumAlongCutoffs w c γ hγ hdisj).coeff x = 0 := by
  by_contra h
  have := support_sumAlongCutoffs_subset w c γ hγ hdisj ((HahnSeries.mem_support _ _).mpr h)
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp this
  exact hx k hk

/-- The sum along cutoffs is a nonpositive series. -/
theorem sumAlongCutoffs_mem (hneg : ∀ k, γ k < 0) :
    sumAlongCutoffs w c γ hγ hdisj ∈ HahnSeries.nonpositiveSubring ℝ K := by
  rw [HahnSeries.mem_nonpositiveSubring]
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (support_sumAlongCutoffs_subset w c γ hγ hdisj hx)
  exact hk.2.trans (hneg k).le

end Family

/-! ### Representatives -/

/-- Every class in `P_δ` has a representative `w ∈ J_{ω^(δ+1)}` of support order type at most
`ω^δ`: a principal series of degree `δ`, or `0`. -/
theorem exists_representative_supportOrderType_le (δ : NatOrdinal) (a : PrincipalComponent K δ) :
    ∃ w : Series K, ∃ hw : ordinalValue w < ω^ (δ + 1),
      principalComponentMk δ w hw = a ∧ (w : K⟦ℝ⟧).supportOrderType ≤ (ω^ δ).val := by
  rcases eq_or_ne a 0 with rfl | ha
  · have h0 : ordinalValue (0 : Series K) < ω^ (δ + 1) := by
      rw [ordinalValue_zero]; exact NatOrdinal.wpow_pos _
    refine ⟨0, h0, (principalComponentMk_eq_zero_iff δ 0 h0).mpr (by
      rw [ordinalValue_zero]; exact NatOrdinal.wpow_pos _), ?_⟩
    rw [Subring.coe_zero, supportOrderType_eq_setOrderType]
    have : ((0 : K⟦ℝ⟧).isPWO_support).orderType = 0 :=
      (Set.IsPWO.orderType_eq_zero _).mpr HahnSeries.support_zero
    rw [this]
    exact bot_le
  · obtain ⟨p, hp, hprin, hdeg, hpa⟩ := exists_principal_representative_of_ne_zero δ a ha
    exact ⟨p, hp, hpa, (hprin.supportOrderType_eq_wpow_of_degree_eq hdeg).le⟩

/-! ### Prescribed classes at prescribed cutoffs -/

/-- **A sum along a sequence of cutoffs with prescribed classes at the cutoffs.** Let
`γ_0 < γ_1 < ⋯ < 0` have supremum `0` and let `a_k ∈ P_δ`. There is `s ∈ J_{ω^(δ+2)}` whose
translated truncation at `γ_k` represents `a_k` in `P_δ` for every `k`, and whose translated
truncation at every `ξ ∈ (γ_0, 0)` other than the `γ_k` has ordinal value below `ω^δ`. -/
@[blueprint "prop:realise-derivative"
  (phase := "Translated truncations")
  (title := "Prescribed $\\mathrm P_\\delta$ classes at translated truncations")
  (statement := /--
    Let $K$ be a field and let $\delta$ be a countable ordinal. Let
    $(\gamma_k)_{k\in\mathbb N}$ be a strictly increasing sequence of negative
    reals cofinal below $0$, and let $a_k\in\mathrm P_\delta$ for every $k$.
    Then there is a series $s\in K((\mathbb R^{\le0}))$ such that
    \[
      v_J(s)<\omega^{\delta\oplus1\oplus1}.
    \]
    For every $k$,
    \[
      v_J(s^{\vert\gamma_k})<\omega^{\delta\oplus1},\qquad
      s^{\vert\gamma_k}+J_{\omega^\delta}=a_k
      \quad\text{in }\mathrm P_\delta.
    \]
    Moreover, if $\gamma_0<\xi<0$ and $\xi\ne\gamma_k$ for every $k$, then
    \[
      v_J(s^{\vert\xi})<\omega^\delta.
    \]
  -/)
  (proof := /--
  By \ref{fact:principal-series-representatives}, choose a principal series
  $w_k$ representing each nonzero $a_k$, and choose $w_k=0$ when $a_k=0$.
  Each support has order type at most $\omega^\delta$. By
  \ref{lem:truncation-drop}, choose $c_k<0$ such that every proper translated
  truncation of $w_k$ at a point of $(c_k,0)$ has ordinal value below
  $\omega^\delta$; enlarge $c_k$ if necessary so that
  $\gamma_{k-1}\le\gamma_k+c_k$ for $k\ge1$.

  Place $(w_k)_{>c_k}$ in the interval
  $(\gamma_k+c_k,\gamma_k]$. These intervals are disjoint and strictly
  increasing. By \ref{lem:increasing-union-order-type}, their union is well
  ordered and has order type at most $\omega^{\delta\oplus1}$. Hence the Hahn
  sum $s$ exists and
  $v_J(s)<\omega^{\delta\oplus1\oplus1}$.

  At $\gamma_k$, every earlier interval contributes only an element of $J$,
  the $k$-th interval has the same germ as $w_k$, and every later interval is
  excluded. Thus $s^{\vert\gamma_k}$ represents $a_k$. Between two prescribed
  cutoffs, its germ is either zero or the germ of a proper translated
  truncation of one $w_k$, whose ordinal value is below $\omega^\delta$ by the
  choice of $c_k$.
  -/)]
theorem exists_sumAlongCutoffs (δ : NatOrdinal) (γ : ℕ → ℝ) (hγ : StrictMono γ)
    (hneg : ∀ k, γ k < 0)
    (hcof : ∀ η < (0 : ℝ), ∃ k, η < γ k) (a : ℕ → PrincipalComponent K δ) :
    ∃ s : Series K, ordinalValue s < ω^ (δ + 1 + 1) ∧
      (∀ k, ∃ hk : ordinalValue (translatedTruncation (s : K⟦ℝ⟧) (γ k)) < ω^ (δ + 1),
        principalComponentMk δ (translatedTruncation (s : K⟦ℝ⟧) (γ k)) hk = a k) ∧
      (∀ ξ : ℝ, γ 0 < ξ → ξ < 0 → (∀ k, ξ ≠ γ k) →
        ordinalValue (translatedTruncation (s : K⟦ℝ⟧) ξ) < ω^ δ) := by
  classical
  -- representatives `w_k`, and an `ε_k` such that their translated truncations at the cutoffs in
  -- `(-ε_k, 0)` have ordinal value below `ω^δ`
  choose w hw hwa hwot using fun k ↦ exists_representative_supportOrderType_le δ (a k)
  have hwin : ∀ k, ∃ ε > 0, ∀ ξ : ℝ, -ε < ξ → ξ < 0 →
      ordinalValue (translatedTruncation ((w k : Series K) : K⟦ℝ⟧) ξ) < ω^ δ := fun k ↦
    exists_forall_ordinalValue_translatedTruncation_lt (hw k)
  choose ε hε hwin using hwin
  -- the reals `c_k`
  set c : ℕ → ℝ := fun k ↦ if k = 0 then -ε 0 else max (γ (k - 1) - γ k) (-ε k) with hcdef
  have hc : ∀ k, c k < 0 := by
    intro k
    simp only [hcdef]
    split_ifs with hk
    · subst hk; linarith [hε 0]
    · exact max_lt (sub_neg.mpr (hγ (by omega))) (by linarith [hε k])
  have hcε : ∀ k, -ε k ≤ c k := by
    intro k
    simp only [hcdef]
    split_ifs with hk
    · subst hk; exact le_rfl
    · exact le_max_right _ _
  have hdisj : ∀ k, γ k ≤ γ (k + 1) + c (k + 1) := by
    intro k
    simp only [hcdef, ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    linarith [le_max_left (γ k - γ (k + 1)) (-ε (k + 1))]
  -- the sum along cutoffs
  set s' := sumAlongCutoffs w c γ hγ hdisj with hs'def
  set s : Series K := ⟨s', sumAlongCutoffs_mem w c γ hγ hdisj hneg⟩ with hsdef
  have hscoe : (s : K⟦ℝ⟧) = s' := rfl
  refine ⟨s, ?_, ?_, ?_⟩
  · -- the ordinal value of `s`
    have hU : (⋃ k, (placedTerm w c γ k).support).IsPWO :=
      (placedTerms w c γ hγ hdisj).isPWO_iUnion_support
    have hUle : hU.orderType ≤ (ω^ (δ + 1)).val := by
      refine Set.IsPWO.orderType_iUnion_le_of_ordered (fun k ↦ support_placedTerm_isPWO w c γ k)
        (fun j k hjk x hx y hy ↦ placedTerm_support_lt w c γ hγ hdisj hjk hx hy) (ρ := (ω^ δ).val)
        (fun k ↦ ?_) fun n ↦ ?_
      · rw [← supportOrderType_eq_setOrderType]
        exact (supportOrderType_placedTerm_le w c γ k).trans (hwot k)
      · rw [NatOrdinal.of_val]
        refine NatOrdinal.val.lt_iff_lt.mpr ?_
        rw [nsmul_eq_mul, mul_comm]
        exact NatOrdinal.wpow_mul_natCast_lt (lt_add_one δ) n
    have hsupp : (s : K⟦ℝ⟧).support ⊆ ⋃ k, (placedTerm w c γ k).support :=
      SummableFamily.support_hsum_subset
    calc ordinalValue s ≤ NatOrdinal.of (s : K⟦ℝ⟧).supportOrderType :=
          ordinalValue_le_supportOrderType s
      _ ≤ NatOrdinal.of (ω^ (δ + 1)).val := by
          rw [supportOrderType_eq_setOrderType]
          exact NatOrdinal.of.le_iff_le.mpr
            ((Set.IsPWO.orderType_mono _ hU hsupp).trans hUle)
      _ = ω^ (δ + 1) := NatOrdinal.of_val _
      _ < ω^ (δ + 1 + 1) := NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)
  · -- the classes at the cutoffs
    intro k
    have hgerm : toGerm (translatedTruncation (s : K⟦ℝ⟧) (γ k)) = toGerm (w k) := by
      rw [toGerm_eq_toGerm_iff_exists_coeff_eq]
      refine ⟨c k, hc k, fun η hη1 hη2 ↦ ?_⟩
      rw [coeff_translatedTruncation, ite_eq_left hη2, hscoe,
        coeff_sumAlongCutoffs_of_mem w c γ hγ hdisj (k := k) ⟨by linarith, by linarith⟩,
        coeff_placedTerm,
        add_sub_cancel_left, ite_eq_left hη1]
    have hval : ordinalValue (translatedTruncation (s : K⟦ℝ⟧) (γ k)) = ordinalValue (w k) :=
      ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm)
    refine ⟨hval ▸ hw k, ?_⟩
    rw [← hwa k, principalComponentMk_eq_iff,
      ordinalValue_eq_zero_iff.mpr (toGerm_eq_toGerm_iff.mp hgerm)]
    exact NatOrdinal.wpow_pos _
  · -- the translated truncations between the cutoffs
    intro ξ hξ0 hξneg hξne
    -- the first cutoff above `ξ`
    have hex : ∃ k, ξ < γ k := hcof ξ hξneg
    set k := Nat.find hex with hkdef
    have hk : ξ < γ k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h
      rw [h] at hk
      exact hξ0.not_gt hk
    have hkpred : γ (k - 1) < ξ := by
      have hnot : ¬ ξ < γ (k - 1) := Nat.find_min hex (by omega)
      exact lt_of_le_of_ne (not_lt.mp hnot) (fun h ↦ hξne (k - 1) h.symm)
    rcases le_or_gt ξ (γ k + c k) with hle | hgt
    · -- `ξ ≤ γ k + c k`: the translated truncation lies in `J`
      have hgerm : toGerm (translatedTruncation (s : K⟦ℝ⟧) ξ) = toGerm 0 := by
        rw [toGerm_eq_toGerm_iff_exists_coeff_eq]
        refine ⟨γ (k - 1) - ξ, by linarith, fun η hη1 hη2 ↦ ?_⟩
        rw [coeff_translatedTruncation, ite_eq_left hη2, hscoe, Subring.coe_zero,
          HahnSeries.coeff_zero]
        refine coeff_sumAlongCutoffs_eq_zero w c γ hγ hdisj fun j hj ↦ ?_
        rcases lt_trichotomy j k with hjk | rfl | hjk
        · -- `j < k`: the interval lies below `γ (k - 1) < ξ + η`
          have : γ j ≤ γ (k - 1) := hγ.monotone (by omega)
          linarith [hj.2]
        · -- `j = k`: `ξ + η ≤ γ k + c k`
          linarith [hj.1]
        · -- `j > k`: the interval lies above `γ k > ξ + η`
          have h1 : γ k ≤ γ (j - 1) := hγ.monotone (by omega)
          have h2 : γ (j - 1) ≤ γ j + c j := by
            have := hdisj (j - 1)
            rwa [Nat.sub_add_cancel (by omega : 1 ≤ j)] at this
          linarith [hj.1]
      rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm),
        ordinalValue_zero]
      exact NatOrdinal.wpow_pos _
    · -- `γ k + c k < ξ < γ k`: the translated truncation is, modulo `J`, one of `w k`
      have hgerm : toGerm (translatedTruncation (s : K⟦ℝ⟧) ξ) =
          toGerm (translatedTruncation ((w k : Series K) : K⟦ℝ⟧) (ξ - γ k)) := by
        rw [toGerm_eq_toGerm_iff_exists_coeff_eq]
        refine ⟨γ k + c k - ξ, by linarith, fun η hη1 hη2 ↦ ?_⟩
        rw [coeff_translatedTruncation, coeff_translatedTruncation, ite_eq_left hη2, ite_eq_left
          hη2, hscoe,
          coeff_sumAlongCutoffs_of_mem w c γ hγ hdisj (k := k) ⟨by linarith, by linarith⟩,
          coeff_placedTerm,
          ite_eq_left (by linarith)]
        congr 1
        ring
      rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm)]
      exact hwin k (ξ - γ k) (by linarith [hcε k]) (by linarith)

end Berarducci
