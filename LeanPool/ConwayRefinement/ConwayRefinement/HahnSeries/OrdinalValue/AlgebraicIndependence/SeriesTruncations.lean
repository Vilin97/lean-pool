/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.UnboundedTruncations
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Lifts
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation

/-!
# Translated truncations of shifted, restricted and bounded series

Elementary facts about the translated truncations `u^{|ζ} = t^{-ζ}(u|_{≤ζ})` [Ber00, Def. 6.1]
used in the induction over degrees:

* the translated truncation of a shift `t^ξ u` at `ζ` is that of `u` at `ζ - ξ`;
* a translated truncation at a cutoff strictly above the whole support lies in `J`;
* the support order type of a translated truncation is at most that of the series, and the
  translated truncation of a series whose support has order type at most `ω^e`, at a cutoff below
  some support point, has ordinal value below `ω^e`;
* if every translated truncation at a cutoff in some `(η, 0)` has ordinal value below `ω^ρ`, the
  series has ordinal value below `ω^(ρ+1)` (the converse direction of
  `exists_ordinalValue_translatedTruncation_eq_wpow_of_lt`).
-/

universe v

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-! ### Shifts -/

/-- The translated truncation of a shift: `(t^ξ b)^{|ζ} = b^{|ζ - ξ}`. -/
theorem translatedTruncation_translate (b : K⟦ℝ⟧) (ξ ζ : ℝ) :
    translatedTruncation (translate ξ b) ζ = translatedTruncation b (ζ - ξ) := by
  apply Subtype.ext
  rw [coe_translatedTruncation, coe_translatedTruncation, truncLE_translate, translate_add_apply]
  congr 1
  ring_nf

/-- A nonpositive series whose support lies below some `s < 0` belongs to `J`. -/
theorem mem_negativeMonomialIdeal_of_forall_support_le {b : Series K} {s : ℝ} (hs : s < 0)
    (h : ∀ x ∈ (b : K⟦ℝ⟧).support, x ≤ s) : b ∈ Nonpositive.negativeMonomialIdeal K := by
  rw [Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [Nonpositive.supportSup_zero]; exact WithBot.bot_lt_coe 0
  · rw [Nonpositive.supportSup_of_ne hb, ← WithBot.coe_zero, WithBot.coe_lt_coe]
    exact (csSup_le (support_nonempty_iff.mpr (by simpa using hb)) h).trans_lt hs

/-- A translated truncation at a cutoff strictly above the whole support lies in `J`. -/
theorem translatedTruncation_mem_negativeMonomialIdeal_of_forall_support_le {b : K⟦ℝ⟧} {s ζ : ℝ}
    (h : ∀ x ∈ b.support, x ≤ s) (hζ : s < ζ) :
    translatedTruncation b ζ ∈ Nonpositive.negativeMonomialIdeal K := by
  refine mem_negativeMonomialIdeal_of_forall_support_le (s := s - ζ) (by linarith) fun x hx ↦ ?_
  rw [support_translatedTruncation] at hx
  obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hx
  linarith [h y hy]

/-- A translated truncation at a cutoff strictly above the whole support has ordinal value `0`. -/
theorem ordinalValue_translatedTruncation_eq_zero_of_forall_support_le {b : K⟦ℝ⟧} {s ζ : ℝ}
    (h : ∀ x ∈ b.support, x ≤ s) (hζ : s < ζ) : ordinalValue (translatedTruncation b ζ) = 0 :=
  ordinalValue_of_mem_negativeMonomialIdeal
    (translatedTruncation_mem_negativeMonomialIdeal_of_forall_support_le h hζ)

/-! ### Order types of translated truncations -/

/-- The support order type of a translated truncation is at most that of the series. -/
theorem supportOrderType_translatedTruncation_le (b : K⟦ℝ⟧) (ζ : ℝ) :
    ((translatedTruncation b ζ : Series K) : K⟦ℝ⟧).supportOrderType ≤ b.supportOrderType := by
  rw [coe_translatedTruncation, supportOrderType_translate]
  exact supportOrderType_mono (by rw [support_truncLE]; exact Set.sep_subset _ _)

/-- The ordinal value of a translated truncation is at most the support order type of the
series. -/
theorem ordinalValue_translatedTruncation_le_of_supportOrderType (b : K⟦ℝ⟧) (ζ : ℝ) :
    ordinalValue (translatedTruncation b ζ) ≤ NatOrdinal.of b.supportOrderType :=
  (ordinalValue_le_supportOrderType _).trans
    (NatOrdinal.of.le_iff_le.mpr (supportOrderType_translatedTruncation_le b ζ))

/-- A translated truncation of a series of support order type below `ω^e` has ordinal value below
`ω^e`. -/
theorem ordinalValue_translatedTruncation_lt_of_supportOrderType_lt {b : K⟦ℝ⟧} {e : NatOrdinal}
    (hb : b.supportOrderType < (ω^ e).val) (ζ : ℝ) :
    ordinalValue (translatedTruncation b ζ) < ω^ e := by
  refine (ordinalValue_translatedTruncation_le_of_supportOrderType b ζ).trans_lt ?_
  rw [← NatOrdinal.of_val (ω^ e), NatOrdinal.of.lt_iff_lt]
  exact hb

/-- If the support of `b` has order type at most `ω^e` and some support point lies above the cutoff
`ζ`, the translated truncation at `ζ` has ordinal value below `ω^e`. (Without a support point
above `ζ` this fails: a series in `J` may have a translated truncation of large ordinal value.) -/
theorem ordinalValue_translatedTruncation_lt_of_supportOrderType_le {b : K⟦ℝ⟧} {e : NatOrdinal}
    (hb : b.supportOrderType ≤ (ω^ e).val) {ζ : ℝ} (hx : ∃ x ∈ b.support, ζ < x) :
    ordinalValue (translatedTruncation b ζ) < ω^ e := by
  classical
  have h : truncLE ζ b ≠ b := by
    intro h
    obtain ⟨x, hx, hζx⟩ := hx
    rw [← h, support_truncLE] at hx
    exact hζx.not_ge hx.2
  refine (ordinalValue_le_supportOrderType _).trans_lt ?_
  rw [coe_translatedTruncation, supportOrderType_translate, ← NatOrdinal.of_val (ω^ e),
    NatOrdinal.of.lt_iff_lt]
  exact (supportOrderType_truncLE_lt ζ h).trans_le hb

/-! ### From the translated truncations on `(η, 0)` to the series -/

/-- If every translated truncation at a cutoff in `(η, 0)` has ordinal value below `ω^ρ`, the
series has ordinal value below `ω^(ρ+1)` (cf. [Ber00, Lem. 6.8]). -/
theorem ordinalValue_lt_wpow_add_one_of_forall_translatedTruncation_lt {u : Series K}
    {ρ : NatOrdinal} {η : ℝ} (hη : η < 0)
    (h : ∀ γ, η < γ → γ < 0 → ordinalValue (translatedTruncation (u : K⟦ℝ⟧) γ) < ω^ ρ) :
    ordinalValue u < ω^ (ρ + 1) := by
  by_contra hcon
  rw [not_lt] at hcon
  rcases ordinalValue_eq_zero_or_isAdditivelyPrincipal u with h0 | hprin
  · rw [h0] at hcon
    exact absurd hcon (not_le.mpr (NatOrdinal.wpow_pos _))
  obtain ⟨β, hβ⟩ := Ordinal.isAdditivelyPrincipal_iff.mp hprin
  have hu : ordinalValue u = ω^ (NatOrdinal.of β) := by
    rw [← NatOrdinal.of_val (ordinalValue u), hβ]; rfl
  have hρβ : ρ < NatOrdinal.of β := by
    rw [hu] at hcon
    exact Order.add_one_le_iff.mp (NatOrdinal.wpow_le_wpow.mp hcon)
  obtain ⟨γ, hηγ, hγ0, hγ⟩ := exists_ordinalValue_translatedTruncation_eq_wpow_of_lt hρβ u hu hη
  exact absurd (h γ hηγ hγ0) (by rw [hγ]; exact lt_irrefl _)

end Berarducci
