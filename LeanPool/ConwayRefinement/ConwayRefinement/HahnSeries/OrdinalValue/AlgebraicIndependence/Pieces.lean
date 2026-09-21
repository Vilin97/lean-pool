/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SumAlongCutoffs
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SeriesTruncations
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.IncreasingSequenceUnion

/-!
# Pieces of a series and sums along a sequence of cutoffs: their translated truncations

For reals `a < b ≤ 0` the *piece* of a series `u` on `(a, b]`, translated to `0`, is
`(u_{>a})^{|b}` — the upper truncation [LM24, Def. 3.2.2] followed by the translated truncation at
`b` [Ber00, Def. 6.1] (`piece a b u`). In the induction over degrees a series is cut into the
pieces on `(γ_k, γ_{k+1}]` along a sequence `γ_k ↑ 0`, and the cofactors found for the pieces are
combined into a sum along the cutoffs, `s = ∑_k (w_k)_{>c_k} t^{γ_k}` (the sum (m) of
`SumAlongCutoffs.lean`, here as a nonpositive series, `sumAlongCutoffsSeries`). This file records
how translated truncations pass through the two operations, modulo `J`:

* `(piece a b u)^{|ξ} ≡ u^{|b + ξ}` for `a - b < ξ ≤ 0`;
* `s^{|γ_k + ξ} ≡ w_k^{|ξ}` for `c_k < ξ ≤ 0`, and the translated truncations of `s` at cutoffs
  `ζ ≤ γ_0 + c_0` vanish;
* the support of `s` has order type at most `ω^e` when every `w_k` has support of order type
  below `ω^e`.
-/

universe v

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- A translated truncation at a cutoff below the whole support vanishes. -/
theorem translatedTruncation_eq_zero_of_forall_lt {b : K⟦ℝ⟧} {ζ : ℝ}
    (h : ∀ y ∈ b.support, ζ < y) : translatedTruncation b ζ = 0 := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
  split_ifs with hδ
  · by_contra hne
    exact absurd (h (ζ + δ) ((HahnSeries.mem_support _ _).mpr hne)) (by linarith)
  · rfl

/-! ### Pieces -/

/-- The piece of the series `E` on `(a, b]`, translated so that `b` sits at `0`: `(E_{>a})^{|b}`,
the upper truncation `E_{>a}` followed by the translated truncation at `b`. -/
def piece (a b : ℝ) (E : K⟦ℝ⟧) : Series K :=
  ⟨translate (-b) (truncGT a (truncLE b E)), by
    rw [HahnSeries.mem_nonpositiveSubring, support_translate]
    rintro δ ⟨y, hy, rfl⟩
    rw [support_truncGT] at hy
    obtain ⟨hy1, -⟩ := hy
    rw [support_truncLE] at hy1
    change -b + y ≤ 0
    linarith [hy1.2]⟩

theorem coe_piece (a b : ℝ) (E : K⟦ℝ⟧) :
    ((piece a b E : Series K) : K⟦ℝ⟧) = translate (-b) (truncGT a (truncLE b E)) :=
  (rfl)

theorem coeff_piece (a b : ℝ) (E : K⟦ℝ⟧) (δ : ℝ) :
    ((piece a b E : Series K) : K⟦ℝ⟧).coeff δ =
      if a < δ + b ∧ δ + b ≤ b then E.coeff (δ + b) else 0 := by
  change (translate (-b) (truncGT a (truncLE b E))).coeff δ = _
  rw [coeff_translate, sub_neg_eq_add, HahnSeries.coeff_truncGT, HahnSeries.coeff_truncLE]
  by_cases h1 : a < δ + b <;> by_cases h2 : δ + b ≤ b <;> simp [h1, h2]

/-- **Translated truncations of interval pieces.** If `a - b < ξ ≤ 0`, then the translated
truncation at `ξ` of the restriction to `(a, b]`, translated so that `b` becomes `0`, is
congruent modulo `J` to the original series translated-truncated at `b + ξ`. -/
@[blueprint "lem:window-truncation"
  (phase := "Limit ordinals in the degree induction")
  (title := "Translated truncations of interval pieces")
  (statement := /--
    Let $K$ be a field, let $u\in K((\mathbb R))$, and let
    $a,b,\xi\in\mathbb R$ satisfy $a-b<\xi\le0$. Put
    \[
      p=t^{-b}\sum_{a<x\le b}u_xt^x.
    \]
    Then
    \[
      \trunc p\xi\equiv\trunc u{b+\xi}\pmod J.
    \]
  -/)
  (proof := /--
  The number $a-b-\xi$ is negative. For every exponent
  $\delta>a-b-\xi$, compare coefficients. If $\delta\le0$, then
  $a<b+\xi+\delta\le b$, and both coefficients are
  $u_{b+\xi+\delta}$. If $\delta>0$, both coefficients are zero. The support
  of the difference is therefore bounded above by $a-b-\xi<0$, so the
  difference lies in $J$.
  -/)]
theorem translatedTruncation_window_sub_mem (a b : ℝ) (E : K⟦ℝ⟧) {ξ : ℝ} (hξ : a - b < ξ)
    (hξ0 : ξ ≤ 0) :
    translatedTruncation ((piece a b E : Series K) : K⟦ℝ⟧) ξ - translatedTruncation E (b + ξ) ∈
      Nonpositive.negativeMonomialIdeal K := by
  refine mem_negativeMonomialIdeal_of_forall_support_le (s := a - b - ξ) (by linarith) fun δ hδ ↦ ?_
  rw [HahnSeries.mem_support, AddSubgroupClass.coe_sub, HahnSeries.coeff_sub,
    coeff_translatedTruncation, coeff_translatedTruncation, coeff_piece] at hδ
  by_contra hlt
  rw [not_le] at hlt
  apply hδ
  by_cases h0 : δ ≤ 0
  · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_left ⟨by linarith, by linarith⟩, show ξ + δ + b = b + ξ + δ by ring,
      sub_self]
  · rw [ite_eq_right h0, ite_eq_right h0, sub_zero]

/-! ### Sums along a sequence of cutoffs -/

section SumAlongCutoffsSeries

variable (w : ℕ → Series K) (c γ : ℕ → ℝ) (hγ : StrictMono γ)
  (hdisj : ∀ k, γ k ≤ γ (k + 1) + c (k + 1)) (hneg : ∀ k, γ k < 0)
include hγ hdisj hneg

/-- The sum (m), `∑_k (w_k)_{>c_k} t^{γ_k}`, as a nonpositive series. -/
def sumAlongCutoffsSeries : Series K :=
  ⟨sumAlongCutoffs w c γ hγ hdisj, sumAlongCutoffs_mem w c γ hγ hdisj hneg⟩

theorem coe_sumAlongCutoffsSeries :
    ((sumAlongCutoffsSeries w c γ hγ hdisj hneg : Series K) : K⟦ℝ⟧) =
    sumAlongCutoffs w c γ hγ hdisj :=
  (rfl)

/-- **Translated truncations of shifted truncation sums.** On the `k`-th support interval, the
translated truncation of the sum along cutoffs agrees modulo `J` with that of `w k`. -/
@[blueprint "lem:cutoff-sum-truncation"
  (phase := "Limit ordinals in the degree induction")
  (title := "Translated truncations of shifted truncation sums")
  (statement := /--
    Let $K$ be a field, let $w_k\in\Kser$, and let
    $c_k,\gamma_k\in\mathbb R$. Suppose that $(\gamma_k)$ is strictly
    increasing, $\gamma_k<0$, and
    $\gamma_k\le\gamma_{k+1}+c_{k+1}$ for every $k$. Put
    \[
      s=\sum_k\utrunc{w_k}{c_k}t^{\gamma_k}.
    \]
    For every $k$ and every $c_k<\xi\le0$,
    \[
      \trunc s{\gamma_k+\xi}\equiv\trunc{w_k}\xi\pmod J.
    \]
  -/)
  (proof := /--
  The shifted support intervals are strictly ordered, so
  \ref{lem:increasing-union} ensures that their union is well ordered and the
  series $s$ is defined. Fix $k$ and $c_k<\xi\le0$. Since $c_k-\xi<0$, it
  suffices to compare coefficients at exponents $\delta>c_k-\xi$. If
  $\delta\le0$, then $\gamma_k+\xi+\delta$ lies in the $k$-th interval, so
  the coefficient of $s$ comes from its $k$-th summand and equals the
  coefficient of $w_k$ at $\xi+\delta$. If $\delta>0$, both translated
  truncations have zero coefficient. Their difference is supported at or
  below $c_k-\xi<0$, and therefore lies in $J$.
  -/)]
theorem translatedTruncation_sumAlongCutoffsSeries_sub_mem (k : ℕ) {ξ : ℝ} (hξ : c k < ξ)
    (hξ0 : ξ ≤ 0) :
    translatedTruncation ((sumAlongCutoffsSeries w c γ hγ hdisj hneg : Series K) : K⟦ℝ⟧) (γ k + ξ) -
        translatedTruncation (w k : K⟦ℝ⟧) ξ ∈ Nonpositive.negativeMonomialIdeal K := by
  refine mem_negativeMonomialIdeal_of_forall_support_le (s := c k - ξ) (by linarith) fun δ hδ ↦ ?_
  rw [HahnSeries.mem_support, AddSubgroupClass.coe_sub, HahnSeries.coeff_sub,
    coeff_translatedTruncation, coeff_translatedTruncation, coe_sumAlongCutoffsSeries] at hδ
  by_contra hlt
  rw [not_le] at hlt
  apply hδ
  by_cases h0 : δ ≤ 0
  · rw [ite_eq_left h0, ite_eq_left h0,
      coeff_sumAlongCutoffs_of_mem w c γ hγ hdisj (k := k) ⟨by linarith, by linarith⟩,
      coeff_placedTerm,
      ite_eq_left (by linarith), show γ k + ξ + δ - γ k = ξ + δ by ring, sub_self]
  · rw [ite_eq_right h0, ite_eq_right h0, sub_zero]

/-- At cutoffs `ζ ≤ γ_0 + c_0`, below the first interval, the translated truncations of the sum
(m) vanish. -/
theorem translatedTruncation_sumAlongCutoffsSeries_eq_zero (hc0 : c 0 ≤ 0) {ζ : ℝ}
    (hζ : ζ ≤ γ 0 + c 0) :
    translatedTruncation ((sumAlongCutoffsSeries w c γ hγ hdisj hneg : Series K) : K⟦ℝ⟧) ζ = 0 := by
  refine translatedTruncation_eq_zero_of_forall_lt fun y hy ↦ ?_
  rw [coe_sumAlongCutoffsSeries] at hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (support_sumAlongCutoffs_subset w c γ hγ hdisj hy)
  have : γ 0 + c 0 ≤ γ k + c k := by
    rcases k with _ | k
    · exact le_rfl
    · have h1 : γ 0 ≤ γ k := hγ.monotone (Nat.zero_le k)
      have h2 := hdisj k
      linarith
  linarith [hk.1]

/-- **Order type of a sum along cutoffs.** If every `w k` has support order type below `ω^e`,
then the sum along cutoffs has support order type at most `ω^e`. -/
@[blueprint "lem:cutoff-sum-support"
  (phase := "Limit ordinals in the degree induction")
  (title := "Order type of a sum along cutoffs")
  (statement := /--
    Let $K$ be a field, let $w_k\in K((\mathbb R^{\le0}))$, let
    $(\gamma_k)$ be a strictly increasing sequence of negative real numbers,
    and let $c_k\in\mathbb R$ satisfy
    $\gamma_k\le\gamma_{k+1}+c_{k+1}$ for every $k$. Put
    \[
      s=\sum_k (w_k)_{>c_k}t^{\gamma_k}.
    \]
    If $\operatorname{ot}(\operatorname{supp}(w_k))<\omega^\rho$ for every
    $k$, then $\operatorname{ot}(\operatorname{supp}(s))\le\omega^\rho$.
  -/)
  (proof := /--
  The $k$-th summand is supported in $(\gamma_k+c_k,\gamma_k]$, and its
  support order type is at most $\operatorname{ot}(\operatorname{supp}(w_k))$.
  The cutoff inequality strictly orders these supports by $k$. By
  \ref{lem:increasing-union-below-principal-ordinal}, their union has order
  type at most $\omega^\rho$. The support of $s$ is contained in this union.
  -/)]
theorem supportOrderType_sumAlongCutoffsSeries_le {e : NatOrdinal}
    (hw : ∀ k, ((w k : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ e).val) :
    ((sumAlongCutoffsSeries w c γ hγ hdisj hneg : Series K) : K⟦ℝ⟧).supportOrderType ≤
      (ω^ e).val := by
  rw [coe_sumAlongCutoffsSeries]
  have hB : ∀ k, (placedTerm w c γ k).support.IsPWO := fun k ↦ support_placedTerm_isPWO w c γ k
  have hord : ∀ j k, j < k → ∀ x ∈ (placedTerm w c γ j).support,
      ∀ y ∈ (placedTerm w c γ k).support, x < y :=
    fun j k hjk x hx y hy ↦ placedTerm_support_lt w c γ hγ hdisj hjk hx hy
  have hU : (⋃ k, (placedTerm w c γ k).support).IsPWO := Set.IsPWO.iUnion_of_ordered hB hord
  have hsub : (sumAlongCutoffs w c γ hγ hdisj).support ⊆ ⋃ k, (placedTerm w c γ k).support :=
    fun y hy ↦ by
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (support_sumAlongCutoffs_subset w c γ hγ hdisj hy)
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [HahnSeries.mem_support] at hy ⊢
    rwa [coeff_sumAlongCutoffs_of_mem w c γ hγ hdisj hk] at hy
  rw [supportOrderType_eq_setOrderType]
  refine (Set.IsPWO.orderType_mono _ hU hsub).trans ?_
  refine Set.IsPWO.orderType_iUnion_le_wpow_of_ordered hB hord (fun k ↦ ?_)
  rw [← supportOrderType_eq_setOrderType]
  exact (supportOrderType_placedTerm_le w c γ k).trans_lt (hw k)

end SumAlongCutoffsSeries

end Berarducci
