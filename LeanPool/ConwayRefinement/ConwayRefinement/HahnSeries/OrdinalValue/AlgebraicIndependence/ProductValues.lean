/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalRepresentatives

/-!
# Ordinal values of the translated truncations of a term `u · q(b_𝓑)`

Let `q ∈ K[X]` be homogeneous of degree `c`, evaluated at principal-series representatives, and let
`u` be a series
of ordinal value below `ω^(b+1)` whose translated truncations at cutoffs `ζ < 0` have ordinal
value below `ω^b`. Under the separation condition (n) for `(b, c, τ)` — `b ⊕ θ < τ` for every
`θ < c` — and `τ ≤ ρ := b ⊕ c`, every translated truncation of the term `u · q(b_𝓑)` at a cutoff
`ζ < 0` has ordinal value below `ω^ρ`: in the convolution formula [Ber00, Lem. 7.5]
`(u q(b_𝓑))^{|ζ} ≡ u^{|ζ} q(b_𝓑) + ∑ u^{|β} q(b_𝓑)^{|ζ - β}` the first term has ordinal value
below `ω^ρ` since `v_J(u^{|ζ}) < ω^b`, and the others have ordinal value below `ω^τ ≤ ω^ρ`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- A product with a factor of ordinal value below `1` (a factor in `J`) has ordinal value `0`. -/
theorem ordinalValue_mul_eq_zero_of_lt_one {u v : Series K} (hv : ordinalValue v < 1) :
    ordinalValue (u * v) = 0 := by
  have hv0 : ordinalValue v = 0 := by
    by_contra h
    exact absurd (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr h)) (not_le.mpr hv)
  rw [ordinalValue_eq_zero_iff] at hv0 ⊢
  exact Ideal.mul_mem_left _ _ hv0

/-- The product of a series of ordinal value below `ω^(a+1)` and one of ordinal value below `ω^g`
has ordinal value below `ω^(a ⊕ g)`; for `g = 0` the second factor lies in `J`, and so does the
product. -/
theorem ordinalValue_mul_lt_wpow_add' {u v : Series K} {a g : NatOrdinal}
    (hu : ordinalValue u < ω^ (a + 1)) (hv : ordinalValue v < ω^ g) :
    ordinalValue (u * v) < ω^ (a + g) := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [NatOrdinal.wpow_zero] at hv
    rw [ordinalValue_mul_eq_zero_of_lt_one hv]
    exact NatOrdinal.wpow_pos _
  · exact Lifts.ordinalValue_mul_lt_wpow_add hg hu hv

/-- **The separation condition (n) bounds a product.** If `v_J(u) < ω^(a+1)`, `v_J(v) < ω^g`, and
(n) holds for `(a, g, τ)` (`a ⊕ θ < τ` for every `θ < g`), the product has ordinal value below
`ω^τ`. -/
theorem ordinalValue_mul_lt_wpow_of_forall_add_lt {u v : Series K} {a g τ : NatOrdinal}
    (hu : ordinalValue u < ω^ (a + 1)) (hv : ordinalValue v < ω^ g)
    (hsep : ∀ θ, θ < g → a + θ < τ) : ordinalValue (u * v) < ω^ τ := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [NatOrdinal.wpow_zero] at hv
    rw [ordinalValue_mul_eq_zero_of_lt_one hv]
    exact NatOrdinal.wpow_pos _
  · obtain ⟨θ, hθ, hvθ⟩ := exists_lt_wpow_add_one_of_lt_wpow hg hv
    exact (ordinalValue_mul_lt_wpow_add_one hu hvθ).trans_le
      (NatOrdinal.wpow_le_wpow.mpr (Order.add_one_le_of_lt (hsep θ (Order.add_one_le_iff.mp hθ))))

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts

variable {σ : Lifts wt x} (hσ : σ.IsPrincipal)
include hσ

/-- **Translated truncations of a term `u · q(b_𝓑)`.** With principal-series representatives, for
`q` homogeneous of
degree `c`, `u` with `v_J(u) < ω^(b+1)` whose translated truncations at cutoffs `< 0` have ordinal
value below `ω^b`, `ρ = b ⊕ c`, `τ ≤ ρ` and (n) for `(b, c, τ)` (`b ⊕ θ < τ` for every `θ < c`):
every translated truncation of `u · q(b_𝓑)` at a cutoff `ζ < 0` has ordinal value below `ω^ρ`. -/
theorem IsPrincipal.ordinalValue_translatedTruncation_mul_aeval_lt (hwt : ∀ i, wt i ≠ 0)
    {q : MvPolynomial ι K} {c : NatOrdinal} (hq : IsWeightedHomogeneous wt q c) {u : Series K}
    {b : NatOrdinal} (hu : ordinalValue u < ω^ (b + 1))
    (hucut : ∀ ζ : ℝ, ζ < 0 → ordinalValue (translatedTruncation (u : K⟦ℝ⟧) ζ) < ω^ b)
    {τ ρ : NatOrdinal} (hbc : b + c = ρ) (hτρ : τ ≤ ρ) (hsep : ∀ θ, θ < c → b + θ < τ) {ζ : ℝ}
    (hζ : ζ < 0) :
    ordinalValue (translatedTruncation ((u * aeval σ.lift q : Series K) : K⟦ℝ⟧) ζ) < ω^ ρ := by
  classical
  set v : Series K := aeval σ.lift q with hvdef
  have hv : ordinalValue v < ω^ (c + 1) := (σ.aeval_represents hq).ordinalValue_lt
  have hvcut : ∀ ξ : ℝ, ξ < 0 → ordinalValue (translatedTruncation (v : K⟦ℝ⟧) ξ) < ω^ c :=
    fun ξ hξ ↦ hσ.ordinalValue_translatedTruncation_aeval_lt hwt hq hξ
  set S : Finset ℝ := insert 0 (insert ζ (convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) ζ)) with hSdef
  have hS1 : convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) ζ ⊆ S :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have hS2 : ∀ β ∈ S, ζ ≤ β ∧ β ≤ 0 := by
    intro β hβ
    rw [hSdef, Finset.mem_insert, Finset.mem_insert] at hβ
    rcases hβ with rfl | rfl | hβ
    · exact ⟨hζ.le, le_rfl⟩
    · exact ⟨le_rfl, hζ.le⟩
    · exact mem_Icc_of_mem_convolutionIndex hβ
  have hucut' : ∀ β, β ≤ 0 → ordinalValue (translatedTruncation (u : K⟦ℝ⟧) β) < ω^ (b + 1) := by
    intro β hβ
    rcases lt_or_eq_of_le hβ with h | rfl
    · exact (hucut β h).trans (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one b))
    · rw [translatedTruncation_zero]; exact hu
  have hgerm : toGerm (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) ζ) =
      toGerm (∑ β ∈ S, translatedTruncation (u : K⟦ℝ⟧) β *
        translatedTruncation (v : K⟦ℝ⟧) (ζ - β)) := by
    rw [← germAt_apply, Subring.coe_mul, germAt_mul_of_subset u v ζ hS1, map_sum]
    simp only [germAt_apply, map_mul]
  rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm)]
  refine ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos ρ) fun β hβ ↦ ?_
  obtain ⟨hζβ, hβ0⟩ := hS2 β hβ
  rcases eq_or_lt_of_le hζβ with rfl | hlt
  · -- the term `u^{|ζ} · q(b_𝓑)`: the translated truncation of `u` at `ζ < 0` against the whole
    -- of `q(b_𝓑)`
    rw [sub_self, translatedTruncation_zero, mul_comm, ← hbc, add_comm]
    exact ordinalValue_mul_lt_wpow_add' hv (hucut _ hζ)
  · -- a translated truncation of `q(b_𝓑)` at a cutoff `< 0`: ordinal value below `ω^τ ≤ ω^ρ`
    exact (ordinalValue_mul_lt_wpow_of_forall_add_lt (hucut' β hβ0) (hvcut (ζ - β) (by linarith))
      hsep).trans_le (NatOrdinal.wpow_le_wpow.mpr hτρ)

end Lifts

end Berarducci
