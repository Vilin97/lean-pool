/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
public import Mathlib.Topology.Instances.Real.Lemmas

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Truncation drop

If `v_J(a) ≤ ω^β`, then the translated truncations `a^{|γ}` at all cutoffs `γ < 0`
sufficiently close to zero have ordinal value strictly below `ω^β`.

The proof reads the ordinal value from a sufficiently short support tail. If `a ∈ J + K`, the
translated truncations near zero lie in `J`. Otherwise `1 < v_J(a)`, so `β ≥ 1`, and for a cutoff
`γ` in a tail `(η, 0)` that computes the ordinal value, the support of `a` strictly between `η`
and `γ` is a proper initial segment of the full tail, whose order type is therefore below `ω^β`;
it is also a final segment of the support below `γ`, and bounds the ordinal value of `a^{|γ}`.
-/

open Filter Topology
open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- A translated truncation whose support has a gap immediately below the cutoff lies in
`J + K`, hence has ordinal value at most one. -/
theorem ordinalValue_translatedTruncation_le_one_of_eq_empty
    (b : Series K) {η γ : ℝ} (hηγ : η < γ)
    (hempty : (b : K⟦ℝ⟧).support ∩ Set.Ioo η γ = ∅) :
    ordinalValue (translatedTruncation (b : K⟦ℝ⟧) γ) ≤ 1 := by
  by_contra hlt
  have hLUB := isLUB_negativeSupport_zero_of_one_lt_ordinalValue (lt_of_not_ge hlt)
  obtain ⟨x, ⟨hxSupport, hx0⟩, hηx, _⟩ := hLUB.exists_between (sub_neg.mpr hηγ)
  rw [support_translatedTruncation] at hxSupport
  obtain ⟨y, ⟨hySupport, hyγ⟩, rfl⟩ := hxSupport
  have hy : y ∈ (b : K⟦ℝ⟧).support ∩ Set.Ioo η γ :=
    ⟨hySupport, by linarith, lt_of_le_of_ne hyγ (by intro h; subst h; simp at hx0)⟩
  rw [hempty] at hy
  exact hy

/-- **Truncation drop.** If `v_J(a) ≤ ω^β`, then `v_J(a^{|γ}) < ω^β` for every cutoff
`γ < 0` sufficiently close to zero. -/
@[blueprint "lem:truncation-drop"
  (phase := "Ordinal value and degree")
  (title := "Decrease of the ordinal value under translated truncation")
  (statement := /--
    Let $\beta<\omega_1$ and $b\in K((\mathbb R^{\le0}))$. If
    $v_J(b)\le\omega^\beta$, then
    \[
      v_J(b^{|\gamma})<\omega^\beta
    \]
    for all $\gamma<0$ sufficiently close to $0$.
  -/)
  (proof := /--
  If $b\in J+K$, all sufficiently late translated truncations lie in $J$.
  Otherwise $1<v_J(b)$, and
  \ref{fact:ordinal-value-support-tail}, followed by shortening the interval,
  gives a tail $(\eta,0)$ of order type $v_J(b)$. For a later cutoff $\gamma$,
  either the support has a gap immediately below $\gamma$, giving value at most
  $1<\omega^\beta$, or
  $\operatorname{supp}(b)\cap(\eta,\gamma)$ is both a final segment of the
  support below $\gamma$ and a proper initial segment of the tail $(\eta,0)$.
  Hence
  \[
    v_J(b^{|\gamma})
      \le\operatorname{ot}(\operatorname{supp}(b)\cap(\eta,\gamma))
      <v_J(b)\le\omega^\beta.
  \]
  -/)]
theorem eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_le
    (beta : NatOrdinal) (b : Series K) (hb : ordinalValue b ≤ ω^ beta) :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) γ) < ω^ beta := by
  rw [eventually_nhdsLT_iff_exists]
  by_cases hnear : b ∈ nearConstantSubgroup K
  · -- Near zero, the translated truncations agree with those of `0`, which lie in `J`.
    obtain ⟨η, hη, heq⟩ :=
        exists_ordinalValue_translatedTruncation_eq_of_sub_mem_nearConstantSubgroup
      (b := b) (c := 0) (by simpa using hnear)
    refine ⟨η, hη, fun γ hηγ hγ ↦ ?_⟩
    rw [heq γ hηγ hγ]
    rw [ZeroMemClass.coe_zero, translatedTruncation_zero_input, ordinalValue_zero]
    exact NatOrdinal.wpow_pos beta
  · -- `1 < v_J(a)`: use a support tail that computes the ordinal value.
    have hone : 1 < ordinalValue b := one_lt_ordinalValue_iff.mpr hnear
    have hbeta : 1 < ω^ beta := hone.trans_le hb
    obtain ⟨η₀, hη₀, htailType⟩ :=
      exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue b hone
    -- Every tail `(η, 0)` with `η₀ < η < 0` computes the ordinal value.
    set η : ℝ := η₀ / 2 with hηdef
    have hη₀η : η₀ < η := by rw [hηdef]; linarith
    have hη : η < 0 := by rw [hηdef]; linarith
    have hηType := htailType η hη₀η hη
    refine ⟨η, hη, fun γ hηγ hγ ↦ ?_⟩
    let C : Set ℝ := (b : K⟦ℝ⟧).support ∩ Set.Ioo η γ
    have hCsub : C ⊆ negativeSupportTail b η := fun x hx ↦
      mem_negativeSupportTail_iff.mpr ⟨hx.1, hx.2.1, hx.2.2.trans hγ⟩
    rcases C.eq_empty_or_nonempty with hCempty | hCne
    · exact (ordinalValue_translatedTruncation_le_one_of_eq_empty b hηγ hCempty).trans_lt hbeta
    -- `C` is a final segment of the support strictly below `γ`.
    have hCupper : IsRelUpperSet C (· ∈ (b : K⟦ℝ⟧).support ∩ Set.Iio γ) := by
      intro x hx
      refine ⟨⟨hx.1, hx.2.2⟩, fun y hxy hy ↦ ⟨hy.1, hx.2.1.trans_le hxy, hy.2⟩⟩
    have hbound := ordinalValue_translatedTruncation_le_orderType_of_isRelUpperSet_supportBelow
      (b : K⟦ℝ⟧) γ hCupper hCne
    -- `C` is a proper initial segment of the tail `(η, 0)`: the tail `(γ, 0)` is nonempty.
    have hγTail : (negativeSupportTail b γ).Nonempty := by
      obtain ⟨x, hxTail, hγx, _⟩ :=
        (isLUB_negativeSupportTail_zero_of_one_lt_ordinalValue b hone hη).exists_between hγ
      exact ⟨x, mem_negativeSupportTail_iff.mpr ⟨(mem_negativeSupportTail_iff.mp hxTail).1,
        hγx, (mem_negativeSupportTail_iff.mp hxTail).2.2⟩⟩
    obtain ⟨x, hxTail⟩ := hγTail
    have hxη : x ∈ negativeSupportTail b η :=
      mem_negativeSupportTail_iff.mpr ⟨(mem_negativeSupportTail_iff.mp hxTail).1,
        hηγ.trans (mem_negativeSupportTail_iff.mp hxTail).2.1,
        (mem_negativeSupportTail_iff.mp hxTail).2.2⟩
    let hηPWO : (negativeSupportTail b η).IsPWO :=
      (b : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support b η)
    have hCbelow : C ⊆ negativeSupportTail b η ∩ Set.Iio x := fun y hy ↦
      ⟨hCsub hy, hy.2.2.trans (mem_negativeSupportTail_iff.mp hxTail).2.1⟩
    have hCtype : ((b : K⟦ℝ⟧).isPWO_support.mono fun _ hy ↦ (hCupper hy).1.1).orderType <
        (ω^ beta).val := by
      calc
        ((b : K⟦ℝ⟧).isPWO_support.mono fun _ hy ↦ (hCupper hy).1.1).orderType ≤
            (hηPWO.mono (s := negativeSupportTail b η ∩ Set.Iio x)
              Set.inter_subset_left).orderType :=
          Set.IsPWO.orderType_mono _ _ hCbelow
        _ < hηPWO.orderType := hηPWO.orderType_inter_Iio_lt hxη
        _ = (ordinalValue b).val := hηType
        _ ≤ (ω^ beta).val := hb
    exact lt_of_le_of_lt hbound hCtype

/-- The truncation drop for the ideals `J_{ω^β}`: a series in `J_{ω^(β+1)}` has translated
truncations in `J_{ω^β}` for all `γ < 0` sufficiently close to `0`. -/
theorem eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
    (beta : NatOrdinal) (b : Series K) (hb : ordinalValue b < ω^ (beta + 1)) :
    ∀ᶠ γ in 𝓝[<] (0 : ℝ),
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) γ) < ω^ beta := by
  apply eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_le
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal b with hzero | hprincipal
  · rw [hzero]
    exact bot_le
  · have hxi := Ordinal.natOrdinal_of_eq_wpow_log hprincipal
    rw [NatOrdinal.of_val] at hxi
    rw [hxi] at hb ⊢
    exact NatOrdinal.wpow_le_wpow.mpr (Order.lt_add_one_iff.mp (NatOrdinal.wpow_lt_wpow.mp hb))

end Berarducci
