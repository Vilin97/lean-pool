/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.ProductValues

/-!
# The translated truncation of a product against that of its first factor

For nonpositive series `u`, `v` and a cutoff `ζ < 0`, the convolution formula [Ber00, Lem. 7.5]
reads `(u v)^{|ζ} ≡ u^{|ζ} v + ∑_{ζ < β ≤ 0} u^{|β} v^{|ζ - β} (mod J)`. When every translated
truncation of `u` has ordinal value below `ω^(a+1)`, every translated truncation of `v` at a cutoff
`< 0` has ordinal value below `ω^g`, and the separation condition (n) holds for `(a, g, τ)` —
`a ⊕ θ < τ` for every `θ < g` — the sum has ordinal value below `ω^τ`:
`v_J((u v)^{|ζ} - u^{|ζ} v) < ω^τ`. This is the computation behind the terms `u′·Q(b_𝓑)` of a
sum along a sequence of cutoffs and behind the combined cofactors alike.
-/

universe v

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- **The convolution formula modulo `J`** (cf. [Ber00, Lem. 7.5]). For `S` containing the
convolution index set, `(u v)^{|ζ} - ∑_{β ∈ S} u^{|β} v^{|ζ - β} ∈ J`. -/
theorem translatedTruncation_mul_sub_sum_mem_negativeMonomialIdeal (u v : Series K) (ζ : ℝ)
    {S : Finset ℝ} (hS : convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) ζ ⊆ S) :
    translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) ζ -
        ∑ β ∈ S, translatedTruncation (u : K⟦ℝ⟧) β * translatedTruncation (v : K⟦ℝ⟧) (ζ - β) ∈
      Nonpositive.negativeMonomialIdeal K := by
  rw [← toGerm_eq_toGerm_iff, ← germAt_apply, Subring.coe_mul, germAt_mul_of_subset u v ζ hS,
    map_sum]
  simp only [germAt_apply, map_mul]

/-- **The translated truncation of a product against that of its first factor.** If every
translated truncation of `u` has ordinal value below `ω^(a+1)`, every translated truncation of `v`
at a cutoff `< 0` has ordinal value below `ω^g`, and (n) holds for `(a, g, τ)` (`a ⊕ θ < τ` for
every `θ < g`), then for every cutoff `ζ < 0` the difference `(u v)^{|ζ} - u^{|ζ} v` has ordinal
value below `ω^τ`. -/
theorem ordinalValue_translatedTruncation_mul_sub_mul_lt {u v : Series K} {a g τ : NatOrdinal}
    (hu : ∀ β : ℝ, β ≤ 0 → ordinalValue (translatedTruncation (u : K⟦ℝ⟧) β) < ω^ (a + 1))
    (hv : ∀ β : ℝ, β < 0 → ordinalValue (translatedTruncation (v : K⟦ℝ⟧) β) < ω^ g)
    (hsep : ∀ θ, θ < g → a + θ < τ) {ζ : ℝ} (hζ : ζ < 0) :
    ordinalValue (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) ζ -
      translatedTruncation (u : K⟦ℝ⟧) ζ * v) < ω^ τ := by
  classical
  set S : Finset ℝ := insert 0 (insert ζ (convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) ζ)) with hSdef
  have hS1 : convolutionIndex (u : K⟦ℝ⟧) (v : K⟦ℝ⟧) ζ ⊆ S :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have hζS : ζ ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hS2 : ∀ β ∈ S, ζ ≤ β ∧ β ≤ 0 := by
    intro β hβ
    rw [hSdef, Finset.mem_insert, Finset.mem_insert] at hβ
    rcases hβ with rfl | rfl | hβ
    · exact ⟨hζ.le, le_rfl⟩
    · exact ⟨le_rfl, hζ.le⟩
    · exact mem_Icc_of_mem_convolutionIndex hβ
  have hmem := translatedTruncation_mul_sub_sum_mem_negativeMonomialIdeal u v ζ hS1
  -- split off the term `β = ζ`
  rw [← Finset.add_sum_erase _ _ hζS, sub_self, translatedTruncation_zero] at hmem
  have heq : translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) ζ -
      translatedTruncation (u : K⟦ℝ⟧) ζ * v =
        (translatedTruncation ((u * v : Series K) : K⟦ℝ⟧) ζ -
          (translatedTruncation (u : K⟦ℝ⟧) ζ * v + ∑ β ∈ S.erase ζ,
            translatedTruncation (u : K⟦ℝ⟧) β * translatedTruncation (v : K⟦ℝ⟧) (ζ - β))) +
        ∑ β ∈ S.erase ζ,
          translatedTruncation (u : K⟦ℝ⟧) β * translatedTruncation (v : K⟦ℝ⟧) (ζ - β) := by
    ring
  rw [heq]
  refine (ordinalValue_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [ordinalValue_of_mem_negativeMonomialIdeal hmem]
    exact NatOrdinal.wpow_pos τ
  · refine ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos τ) fun β hβ ↦ ?_
    obtain ⟨hne, hβS⟩ := Finset.mem_erase.mp hβ
    obtain ⟨hζβ, hβ0⟩ := hS2 β hβS
    have hlt : ζ < β := lt_of_le_of_ne hζβ fun h ↦ hne h.symm
    exact ordinalValue_mul_lt_wpow_of_forall_add_lt (hu β hβ0) (hv (ζ - β) (by linarith)) hsep

end Berarducci
