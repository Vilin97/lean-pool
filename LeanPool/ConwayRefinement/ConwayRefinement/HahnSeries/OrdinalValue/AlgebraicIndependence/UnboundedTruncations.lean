/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.TruncationDrop
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Translated truncations of a series of ordinal value `ω^β` reach every `ω^ρ`, `ρ < β`

If `v_J(u) = ω^β` and `ρ < β`, then for every real `θ < 0` there is a cutoff `θ < γ < 0` with
`v_J(u^{|γ}) = ω^ρ` exactly: take an interval `(η, 0)` with `η > θ` on which
`ot(supp u ∩ (γ', 0)) = v_J(u)` for all `γ' ∈ [η, 0)`, the initial segment `S` of
`supp u ∩ (η, 0)` of order type `ω^ρ`, and `γ := sup S`. Every point of `supp u ∩ (η, 0)` below
`γ` lies in `S`, so the support of `u^{|γ}` on some interval `(η', 0]` is a translate of a final
segment of `S`, of order type `ω^ρ` by additive indecomposability (for `ρ = 0`, `S` is a single
support point and `u^{|γ}` has a nonzero constant term and a gap below `0`). This is the
same support-tail phenomenon as Berarducci [Ber00, Lem. 6.8], at every degree below the ordinal
value. The case `β = α + 1`, `ρ = α` gives the injectivity of the lowering derivation on
`P_{α+1}`.
-/

universe v

open Ordinal Set
open scoped NatOrdinal

public noncomputable section

namespace Berarducci

open Berarducci HahnSeries

variable {K : Type v} [Field K]

/-- A translated truncation at a support point is not in `J`. -/
private theorem translatedTruncation_not_mem_negativeMonomialIdeal_of_mem_support
    (u : Series K) {γ : ℝ} (hγ : γ ∈ (u : K⟦ℝ⟧).support) :
    translatedTruncation (u : K⟦ℝ⟧) γ ∉ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  intro hJ
  rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero] at hJ
  have hzero : (0 : ℝ) ∈ ((translatedTruncation (u : K⟦ℝ⟧) γ : Series K) : K⟦ℝ⟧).support := by
    rw [HahnSeries.mem_support, coeff_translatedTruncation]
    simpa using hγ
  have hne : translatedTruncation (u : K⟦ℝ⟧) γ ≠ 0 := by
    intro h
    rw [h] at hzero
    simp at hzero
  rw [HahnSeries.Nonpositive.supportSup_of_ne hne] at hJ
  exact absurd (le_csSup (HahnSeries.Nonpositive.bddAbove_support _) hzero)
    (not_le.mpr (WithBot.coe_lt_coe.mp hJ))

/-- If `v_J(u) = ω^β`, `ρ < β` and `θ < 0`, there is a cutoff `θ < γ < 0` with `v_J(u^{|γ}) = ω^ρ`
(cf. [Ber00, Lem. 6.8]). -/
@[blueprint "lem:truncation-values"
  (phase := "Limit ordinals in the degree induction")
  (title := "Realisation of lower ordinal values by translated truncations")
  (statement := /--
    Let $K$ be a field and let
    $u\in K((\mathbb R^{\le0}))$. If
    \[
      v_J(u)=\omega^\beta
      \qquad\text{and}\qquad
      \rho<\beta,
    \]
    then, for every $\theta<0$, there is a $\gamma$ such that
    \[
      \theta<\gamma<0
      \qquad\text{and}\qquad
      v_J(u^{|\gamma})=\omega^\rho.
    \]
  -/)
  (proof := /--
  Since $\rho<\beta$, the ordinal value of $u$ is greater than $1$. By
  \ref{fact:ordinal-value-support-tail}, choose $\eta>\theta$ such that the
  negative support tail
  \[
    B=\operatorname{supp}(u)\cap(\eta,0)
  \]
  has order type $\omega^\beta$. Let $S$ be the initial segment of $B$ of
  order type $\omega^\rho$, and put $\gamma=\sup S$. Then
  $\theta<\gamma<0$.

  If $\rho=0$, the set $S$ is a singleton. Thus $\gamma$ is a support point
  with a gap immediately below it. The translated truncation $u^{|\gamma}$
  has a nonzero constant term and ordinal value at most $1$, hence ordinal
  value exactly $1=\omega^0$.

  Suppose $\rho>0$. Then $\omega^\rho$ is an additively principal limit
  ordinal, so $S$ has no largest element. The set $S$ is a final segment of
  the support strictly below $\gamma$, which gives
  $v_J(u^{|\gamma})\le\omega^\rho$. Conversely, every interval immediately
  below $\gamma$ contains a nonempty final segment of $S$, and every such
  final segment still has order type $\omega^\rho$. The support-tail
  characterisation of $v_J$ therefore gives the reverse inequality.
  -/)]
theorem exists_ordinalValue_translatedTruncation_eq_wpow_of_lt
    {beta rho : NatOrdinal} (hrho : rho < beta) (u : Series K) (hu : ordinalValue u = ω^ beta)
    {θ : ℝ} (hθ : θ < 0) :
    ∃ γ : ℝ, θ < γ ∧ γ < 0 ∧ ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) = ω^ rho := by
  have hbeta0 : beta ≠ 0 := (pos_of_gt hrho).ne'
  have hone : 1 < ordinalValue u := by
    rw [hu, ← NatOrdinal.wpow_zero]
    exact NatOrdinal.wpow_lt_wpow.mpr (pos_iff_ne_zero.mpr hbeta0)
  -- `B = supp(u) ∩ (η, 0)` with `η > θ`, on which the order type of the support is `v_J(u)`.
  obtain ⟨η₀, hη₀, hstable⟩ :=
    exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue u hone
  set η : ℝ := max (η₀ / 2) (θ / 2) with hηdef
  have hη₀η : η₀ < η := lt_max_of_lt_left (by linarith)
  have hθη : θ < η := lt_max_of_lt_right (by linarith)
  have hη : η < 0 := max_lt (by linarith) (by linarith)
  set B : Set ℝ := negativeSupportTail u η with hBdef
  have hBsupp : B ⊆ (u : K⟦ℝ⟧).support := negativeSupportTail_subset_support u η
  have hBpwo : B.IsPWO := (u : K⟦ℝ⟧).isPWO_support.mono hBsupp
  set ρ : Ordinal := omega0 ^ rho.val with hρdef
  have hρpos : 0 < ρ := opow_pos _ omega0_pos
  have hBtype : hBpwo.orderType = omega0 ^ beta.val := by
    rw [Set.IsPWO.orderType_proof_irrel hBpwo
      ((u : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support u η)),
      hstable η hη₀η hη, hu, NatOrdinal.val_wpow]
  -- The point `y` of index `ρ`; the initial segment `S = B ∩ (-∞, y)`.
  have hρlt : ρ < hBpwo.orderType := by
    rw [hBtype, hρdef]
    exact (opow_lt_opow_iff_right one_lt_omega0).mpr hrho
  obtain ⟨y, hyB, hyIdx⟩ := hBpwo.exists_orderType_inter_Iio_eq hρlt
  set S : Set ℝ := B ∩ Set.Iio y with hSdef
  have hSpwo : S.IsPWO := hBpwo.mono Set.inter_subset_left
  have hStype : hSpwo.orderType = ρ := hyIdx
  have hSne : S.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have := (hSpwo.orderType_eq_zero).mpr hempty
    rw [hStype] at this
    exact hρpos.ne' this
  have hSbdd : BddAbove S := ⟨y, fun x hx ↦ hx.2.le⟩
  set γ : ℝ := sSup S with hγdef
  have hSγ : ∀ x ∈ S, x ≤ γ := fun x hx ↦ le_csSup hSbdd hx
  have hγy : γ ≤ y := csSup_le hSne fun x hx ↦ hx.2.le
  have hy0 : y < 0 := (mem_negativeSupportTail_iff.mp hyB).2.2
  have hγ0 : γ < 0 := hγy.trans_lt hy0
  have hθγ : θ < γ := by
    obtain ⟨s, hs⟩ := hSne
    exact (hθη.trans (mem_negativeSupportTail_iff.mp hs.1).2.1).trans_le (hSγ s hs)
  -- Every point of `B` below `γ` lies in `S`.
  have hbelow : ∀ x ∈ B, x < γ → x ∈ S := by
    intro x hxB hxγ
    obtain ⟨s, hs, hxs⟩ := exists_lt_of_lt_csSup hSne hxγ
    exact ⟨hxB, hxs.trans hs.2⟩
  have hsuppBelow : ∀ x ∈ (u : K⟦ℝ⟧).support, η < x → x < γ → x ∈ S := fun x hx hηx hxγ ↦
    hbelow x (mem_negativeSupportTail_iff.mpr ⟨hx, hηx, hxγ.trans hγ0⟩) hxγ
  refine ⟨γ, hθγ, hγ0, ?_⟩
  rcases eq_or_ne rho 0 with rfl | hrho0
  · -- `ρ = 0`: `S` is a single support point `γ`.
    have hρone : ρ = 1 := by simp [hρdef]
    have hSmin : ∀ x ∈ S, ∀ x' ∈ S, x' ≤ x → x' = x := by
      intro x hx x' hx' hle
      by_contra hne
      have hlt : x' < x := lt_of_le_of_ne hle hne
      have hbelow := hSpwo.orderType_inter_Iio_lt hx
      rw [hStype, hρone, Order.lt_one_iff, Set.IsPWO.orderType_eq_zero] at hbelow
      have : x' ∈ S ∩ Set.Iio x := ⟨hx', hlt⟩
      rw [hbelow] at this
      exact this
    obtain ⟨m, hm⟩ := hSne
    have hSeq : S = {m} := by
      ext x
      constructor
      · intro hx
        rcases le_total x m with hxm | hmx
        · exact hSmin m hm x hx hxm
        · exact (hSmin x hx m hm hmx).symm
      · rintro rfl
        exact hm
    have hγm : γ = m := by rw [hγdef, hSeq, csSup_singleton]
    have hγS : γ ∈ S := hγm ▸ hm
    have hγsupp : γ ∈ (u : K⟦ℝ⟧).support := hBsupp hγS.1
    have hgap : (u : K⟦ℝ⟧).support ∩ Set.Ioo η γ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hηx, hxγ⟩
      have hxS := hsuppBelow x hx hηx hxγ
      rw [hSeq] at hxS
      exact hxγ.ne (hxS.trans hγm.symm)
    have hηγ : η < γ := (mem_negativeSupportTail_iff.mp hγS.1).2.1
    have hle := ordinalValue_translatedTruncation_le_one_of_eq_empty u hηγ hgap
    have hne : ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) ≠ 0 := by
      rw [Ne, ordinalValue_eq_zero_iff]
      exact translatedTruncation_not_mem_negativeMonomialIdeal_of_mem_support u hγsupp
    rw [NatOrdinal.wpow_zero]
    rcases Order.le_one_iff.mp hle with hzero | hone'
    · exact absurd hzero hne
    · exact hone'
  · -- `ρ ≥ 1`: `ω^ρ` is an additively indecomposable limit.
    have hρprin : IsAdditivelyPrincipal ρ := isAdditivelyPrincipal_omega0_opow _
    have hρone : 1 < ρ := by
      have : ω^ (0 : NatOrdinal) < ω^ rho :=
        NatOrdinal.wpow_lt_wpow.mpr (pos_iff_ne_zero.mpr hrho0)
      rw [NatOrdinal.wpow_zero] at this
      have hval : (1 : NatOrdinal).val < (ω^ rho).val := this
      simpa [hρdef] using hval
    have hlimit : Order.IsSuccLimit hSpwo.orderType := by
      rw [hStype]
      exact hρprin.isSuccLimit_of_one_lt hρone
    have hprincipal : IsPrincipal (fun a b : Ordinal ↦ a + b) hSpwo.orderType := by
      rw [hStype]
      exact (isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp hρprin).2
    -- `S` has no largest element, so every point of `S` lies strictly below `γ`.
    have hSlt : ∀ x ∈ S, x < γ := by
      intro x hx
      obtain ⟨x', hx', hxx'⟩ := hSpwo.exists_gt_of_isSuccLimit_orderType hlimit hx
      exact hxx'.trans_le (hSγ x' hx')
    -- Upper bound: `S` is a nonempty final segment of the support strictly below `γ`.
    have hSupper : IsRelUpperSet S (· ∈ (u : K⟦ℝ⟧).support ∩ Set.Iio γ) := by
      intro x hx
      refine ⟨⟨hBsupp hx.1, hSlt x hx⟩, fun y' hxy' hy' ↦ ?_⟩
      exact hsuppBelow y' hy'.1 ((mem_negativeSupportTail_iff.mp hx.1).2.1.trans_le hxy') hy'.2
    have hupper := ordinalValue_translatedTruncation_le_orderType_of_isRelUpperSet_supportBelow
      (u : K⟦ℝ⟧) γ hSupper hSne
    rw [Set.IsPWO.orderType_proof_irrel _ hSpwo, hStype] at hupper
    -- Lower bound: every interval `(θ', γ)` contains a nonempty final segment of `S`.
    have hlower : NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) := by
      apply le_ordinalValue_translatedTruncation_of_forall_le_orderType
      intro θ' hθ'γ
      obtain ⟨s, hs, hθ's⟩ := exists_lt_of_lt_csSup hSne hθ'γ
      have hfinal := hSpwo.orderType_inter_Ioi_eq_of_isPrincipal hprincipal ⟨s, hs, hθ's⟩
      rw [hStype] at hfinal
      rw [← hfinal]
      apply Set.IsPWO.orderType_mono
      intro x hx
      exact ⟨hBsupp hx.1.1, hx.2, hSlt x hx.1⟩
    rw [NatOrdinal.val_eq_iff.mp (le_antisymm hupper (NatOrdinal.of_le_iff.mp hlower)), hρdef,
      ← NatOrdinal.val_wpow, NatOrdinal.of_val]

/-- If `v_J(u) = ω^β` and `ρ < β`, then `v_J(u^{|γ}) = ω^ρ` for cutoffs `γ < 0` arbitrarily close
to `0`. -/
theorem frequently_ordinalValue_translatedTruncation_eq_wpow_of_lt
    {beta rho : NatOrdinal} (hrho : rho < beta) (u : Series K) (hu : ordinalValue u = ω^ beta) :
    ∃ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0),
      ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) = ω^ rho := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.mp hU
  obtain ⟨γ, hθγ, hγ0, hγ⟩ := exists_ordinalValue_translatedTruncation_eq_wpow_of_lt hrho u hu
    (neg_neg_of_pos hε : -ε < 0)
  refine ⟨γ, hεU ⟨?_, hγ0⟩, hγ⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

end Berarducci
