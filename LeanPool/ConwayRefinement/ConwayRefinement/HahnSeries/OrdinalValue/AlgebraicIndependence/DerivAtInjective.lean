/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAt

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AdditivelyPrincipal
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Injectivity of translated truncation on `P_α` for successor `α`

For every `α`, `∂` is injective on `P_{α+1}` (Berarducci's Lem. 6.8 in the present language).
Let `α = β + 1` be a successor ordinal and `u` a series with `v_J(u) = ω^α = ω^β · ω`. A
sufficiently short support tail `B` of `u` is order isomorphic to `ω` copies of `ω^β`. Let `S`
be its first block, the set of points of `B` of index below `ω^β`, and let `γ = sup S`. Then
`v_J(u^{|γ}) = ω^β`:

* if `β = 0`, then `S` is a single support point `γ`, so `u^{|γ}` has nonzero constant term and
  support otherwise bounded away from zero;
* if `β ≥ 1`, then `ω^β` is a limit, `S` has no largest element, the exponents of `u^{|γ}`
  immediately below zero are the translates of final segments of `S`, and every nonempty final
  segment of `S` has order type `ω^β` because `ω^β` is additively indecomposable.

Applying this to the tail above any `θ < 0` produces cutoffs `γ ∈ (θ, 0)` at which
`∂(u)(γ) = u^{|γ} + J_{ω^β}` is nonzero, so `∂(B) ≠ 0` for every nonzero `B ∈ P_α`.
-/

open Filter Topology Ordinal
open scoped HahnSeries NatOrdinal

universe v

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

/-- If `v_J(u) = ω^(β+1)` and `θ < 0`, there is a cutoff `θ < γ < 0` with
`v_J(u^{|γ}) = ω^β`. -/
@[blueprint "lem:successor-truncation-value"
  (phase := "Translated truncations")
  (title := "Translated truncations of successor ordinal value")
  (statement := /--
    Let $\beta<\omega_1$ and $b\in K((\mathbb R^{\le0}))$. If
    $v_J(b)=\omega^{\beta+1}$, then for every $\theta<0$ there is
    $\gamma\in(\theta,0)$ such that $v_J(b^{|\gamma})=\omega^\beta$.
  -/)
  (proof := /--
  By \ref{fact:ordinal-value-support-tail}, choose above $\theta$ a support
  tail $B$ of order type
  $\omega^{\beta+1}=\omega^\beta\cdot\omega$. Let $S$ be its initial block
  of order type $\omega^\beta$, and put $\gamma=\sup S$.

  If $\beta=0$, then $S=\{\gamma\}$. The translated truncation has a non-zero
  constant coefficient and a gap immediately below zero, so its ordinal value
  is $1$.

  If $\beta>0$, then $\omega^\beta$ is an additively principal limit ordinal.
  The set $S$ is a final segment of the support below $\gamma$, giving
  $v_J(b^{|\gamma})\le\omega^\beta$. Every interval immediately below
  $\gamma$ contains a final segment of $S$, still of order type
  $\omega^\beta$, giving the reverse inequality. Thus
  $v_J(b^{|\gamma})=\omega^\beta$, and the choice of $B$ gives
  $\theta<\gamma<0$.
  -/)]
theorem exists_ordinalValue_translatedTruncation_eq_wpow_of_ordinalValue_eq_wpow_add_one
    (beta : NatOrdinal) (u : Series K) (hu : ordinalValue u = ω^ (beta + 1))
    {θ : ℝ} (hθ : θ < 0) :
    ∃ γ : ℝ, θ < γ ∧ γ < 0 ∧ ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) = ω^ beta := by
  have hone : 1 < ordinalValue u := by
    rw [hu, ← NatOrdinal.wpow_zero]
    exact NatOrdinal.wpow_lt_wpow.mpr (by simp)
  -- A tail `B = supp(u) ∩ (η, 0)` that computes the ordinal value, above `θ`.
  obtain ⟨η₀, hη₀, htailType⟩ :=
    exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue u hone
  set η : ℝ := max (η₀ / 2) (θ / 2) with hηdef
  have hη₀η : η₀ < η := lt_max_of_lt_left (by linarith)
  have hθη : θ < η := lt_max_of_lt_right (by linarith)
  have hη : η < 0 := max_lt (by linarith) (by linarith)
  set B : Set ℝ := negativeSupportTail u η with hBdef
  have hBsupp : B ⊆ (u : K⟦ℝ⟧).support := negativeSupportTail_subset_support u η
  have hBpwo : B.IsPWO := (u : K⟦ℝ⟧).isPWO_support.mono hBsupp
  set ρ : Ordinal := omega0 ^ beta.val with hρdef
  have hρpos : 0 < ρ := opow_pos _ omega0_pos
  have hBtype : hBpwo.orderType = ρ * omega0 := by
    rw [Set.IsPWO.orderType_proof_irrel hBpwo
      ((u : K⟦ℝ⟧).isPWO_support.mono (negativeSupportTail_subset_support u η)),
      htailType η hη₀η hη, hu, NatOrdinal.val_wpow, NatOrdinal.val_add_one, hρdef,
      Ordinal.opow_add_one]
  -- The point `y` of index `ρ`; the first block is `S = B ∩ (-∞, y)`.
  have hρlt : ρ < hBpwo.orderType := by
    rw [hBtype]
    calc ρ = ρ * 1 := (mul_one ρ).symm
      _ < ρ * omega0 := mul_lt_mul_of_pos_left one_lt_omega0 hρpos
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
  -- Every point of `B` below `γ` lies in the first block.
  have hbelow : ∀ x ∈ B, x < γ → x ∈ S := by
    intro x hxB hxγ
    obtain ⟨s, hs, hxs⟩ := exists_lt_of_lt_csSup hSne hxγ
    exact ⟨hxB, hxs.trans hs.2⟩
  have hsuppBelow : ∀ x ∈ (u : K⟦ℝ⟧).support, η < x → x < γ → x ∈ S := fun x hx hηx hxγ ↦
    hbelow x (mem_negativeSupportTail_iff.mpr ⟨hx, hηx, hxγ.trans hγ0⟩) hxγ
  refine ⟨γ, hθγ, hγ0, ?_⟩
  rcases eq_or_ne beta 0 with rfl | hbeta
  · -- `β = 0`: the first block is a single support point `γ`.
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
  · -- `β ≥ 1`: `ω^β` is an additively indecomposable limit.
    have hρprin : IsAdditivelyPrincipal ρ := isAdditivelyPrincipal_omega0_opow _
    have hρone : 1 < ρ := by
      have : ω^ (0 : NatOrdinal) < ω^ beta :=
        NatOrdinal.wpow_lt_wpow.mpr (pos_iff_ne_zero.mpr hbeta)
      rw [NatOrdinal.wpow_zero] at this
      have hval : (1 : NatOrdinal).val < (ω^ beta).val := this
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
    -- Lower bound: every window `(θ', γ)` contains a nonempty final segment of `S`.
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

/-- A nonzero class in `P_α`, for successor `α`, has a representative of ordinal value exactly
`ω^α`. -/
theorem ordinalValue_eq_wpow_of_principalComponentMk_ne_zero (alpha : NatOrdinal)
    (u : Series K) (hu : ordinalValue u < ω^ (alpha + 1))
    (hne : principalComponentMk alpha u hu ≠ 0) :
    ordinalValue u = ω^ alpha := by
  have hnot : ¬ ordinalValue u < ω^ alpha := fun h ↦
    hne ((principalComponentMk_eq_zero_iff alpha u hu).mpr h)
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal u with hzero | hprincipal
  · exact absurd (hzero ▸ NatOrdinal.wpow_pos alpha) hnot
  · have hxi := Ordinal.natOrdinal_of_eq_wpow_log hprincipal
    rw [NatOrdinal.of_val] at hxi
    rw [hxi] at hu hnot ⊢
    rw [NatOrdinal.wpow_inj]
    exact le_antisymm (Order.lt_add_one_iff.mp (NatOrdinal.wpow_lt_wpow.mp hu))
      (not_lt.mp fun h ↦ hnot (NatOrdinal.wpow_lt_wpow.mpr h))

/-- If `α` is a successor, translated truncation sends every nonzero class in `P_α` to a nonzero
function at `0⁻`. -/
theorem principalComponentDerivAt_ne_zero
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    {x : PrincipalComponent K alpha} (hx : x ≠ 0) :
    principalComponentDerivAt K alpha halpha x ≠ 0 := by
  obtain ⟨u, hu, rfl⟩ := exists_principalComponentMk alpha x
  have hvalue := ordinalValue_eq_wpow_of_principalComponentMk_ne_zero alpha u hu hx
  have halpha' : alpha.removeNat 1 + 1 = alpha := by
    simpa using NatOrdinal.removeNat_add_natCast halpha
  rw [principalComponentDerivAt_principalComponentMk]
  intro hzero
  obtain ⟨θ, hθ, hθzero⟩ := (FunAtZeroMinus.coe_eq_zero_iff_exists _).mp hzero
  obtain ⟨γ, hθγ, hγ0, hγvalue⟩ :=
    exists_ordinalValue_translatedTruncation_eq_wpow_of_ordinalValue_eq_wpow_add_one
        (alpha.removeNat 1) u
      (by rw [hvalue, halpha']) hθ
  have hbound : ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) < ω^ (alpha.removeNat 1 + 1) := by
    rw [hγvalue]
    exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)
  have hcut := hθzero γ hθγ hγ0
  rw [derivAt_eq alpha u γ hbound, principalComponentMk_eq_zero_iff, hγvalue] at hcut
  exact lt_irrefl _ hcut

variable (K) in
/-- Translated truncation is injective on `P_α` for every successor ordinal `α`. -/
@[blueprint "prop:successor-principal-rv-injective"
  (phase := "Translated truncations")
  (title := "Injectivity of the translated-truncation map on $\\mathrm P_\\alpha$")
  (statement := /--
    Let $K$ be a field, let $\alpha<\omega_1$ be a successor ordinal, and write
    $\alpha=\beta+1$. Put
    \[
      \mathrm P_\delta:=J_{\omega^{\delta+1}}/J_{\omega^\delta}.
    \]
    Let $\operatorname{Fun}_{0^-}(V)$ be the space of $V$-valued functions on
    intervals $(\eta,0)$, identified when they agree sufficiently close to $0$.
    Then the $K$-linear map
    \[
      \partial_\alpha:\mathrm P_\alpha\longrightarrow
        \operatorname{Fun}_{0^-}(\mathrm P_\beta),\qquad
      \partial_\alpha([b])=[\gamma\mapsto[b^{|\gamma}]],
    \]
    is injective. The inner class is taken modulo $J_{\omega^\beta}$.
  -/)
  (proof := /--
  By \ref{lem:truncation-drop}, every series of ordinal value below
  $\omega^\alpha$ has translated truncations of ordinal value below $\omega^\beta$
  sufficiently close to $0$. Thus translated truncation induces the displayed map on the
  quotient.

  A nonzero class $[b]\in\mathrm P_\alpha$ has a representative with
  $v_J(b)=\omega^\alpha$. By
  \ref{lem:successor-truncation-value}, every interval $(\theta,0)$ contains
  a cutoff $\gamma$ with $v_J(b^{|\gamma})=\omega^\beta$. Hence
  $[b^{|\gamma}]\ne0$ in $\mathrm P_\beta$, so
  $\partial_\alpha([b])\ne0$. The kernel of the linear map
  $\partial_\alpha$ is therefore zero, and the map is injective.
  -/)]
theorem principalComponentDerivAt_injective
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    Function.Injective (principalComponentDerivAt K alpha halpha) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  exact principalComponentDerivAt_ne_zero alpha halpha hne hx

end Berarducci
