/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Pieces
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.ProductTruncation

/-!
# The combined cofactors

Let `γ_k ↑ 0` and let `E` be a series. Suppose that for every piece `piece (γ k) (γ (k+1)) E` of
`E` — the piece on `(γ_k, γ_{k+1}]`, translated to `0` — we are given cofactors `w k j` with
supports of order type below `ω^{e j}`, such that `piece (γ k) (γ (k+1)) E - ∑_j w k j * v j` has
translated truncations of ordinal value below `ω^(τ+1)` at every cutoff in `(γ_k - γ_{k+1}, 0]`.
The *combined cofactors* are the sums (m) with the cofactors of the pieces as terms,
`∑_k (w_{kj})_{>γ_k - γ_{k+1}} t^{γ_{k+1}}` (`combinedCofactor`). Then the support of the `j`-th
combined cofactor has order type at most `ω^{e j}`, its translated truncations at cutoffs `ζ < 0`
have ordinal value below `ω^{e j}` and vanish at cutoffs `ζ ≤ γ_0`, and — under the separation
condition (n) for `(e j, c j, τ)`, `e j ⊕ θ < τ` for every `θ < c j`, where the translated
truncations of `v j` at cutoffs `ζ < 0` have ordinal value below `ω^{c j}` — the series
`E - ∑_j (combined cofactor)_j * v j` has translated truncations of ordinal value below `ω^(τ+1)`
at every cutoff in `(γ_0, 0)`.

For `ζ ∈ (γ_k, γ_{k+1}]` and `ξ := ζ - γ_{k+1}`: `E^{|ζ} ≡ (piece (γ k) (γ (k+1)) E)^{|ξ}` and
the translated truncation of the `j`-th combined cofactor at `ζ` is `(w k j)^{|ξ}`, both modulo
`J`; and the translated truncation of each product differs from the translated truncation of its
first factor times the second factor by a series of ordinal value below `ω^τ`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- A point of `(γ 0, 0)` lies in an interval `(γ k, γ (k+1)]` of a strictly increasing sequence
with supremum `0`. -/
theorem exists_lt_le_succ_of_strictMono {γ : ℕ → ℝ} (hcof : ∀ η < (0 : ℝ), ∃ k, η < γ k) {ζ : ℝ}
    (h0 : γ 0 < ζ) (hζ : ζ < 0) :
    ∃ k, γ k < ζ ∧ ζ ≤ γ (k + 1) := by
  classical
  have hex : ∃ n, ζ ≤ γ n := by
    obtain ⟨n, hn⟩ := hcof ζ hζ
    exact ⟨n, hn.le⟩
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact absurd this (not_le.mpr h0)
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    exact not_le.mp this
  · have := Nat.find_spec hex
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)]

section CombinedCofactors

variable {ι' : Type w} [Fintype ι'] (E : Series K) (γ : ℕ → ℝ) (hγ : StrictMono γ)
  (hneg : ∀ k, γ k < 0) (hcof : ∀ η < (0 : ℝ), ∃ k, η < γ k) (w : ℕ → ι' → Series K)

/-- The intervals `(γ k, γ (k+1)]` as the intervals `(γ_k + c_k, γ_k]` of the sum (m) of
`SumAlongCutoffs.lean`, with cutoffs `γ (k+1)` and `c_k := γ k - γ (k+1)`: the condition
`γ_k ≤ γ_{k+1} + c_{k+1}` of (m) holds. -/
theorem pieces_le_add_sub (k : ℕ) : γ (k + 1) ≤ γ (k + 1 + 1) + (γ (k + 1) - γ (k + 1 + 1)) := by
  linarith

include hγ hneg in
/-- The `j`-th combined cofactor `∑_k (w_{kj})_{>γ_k - γ_{k+1}} t^{γ_{k+1}}`: the sum (m) along the
cutoffs `γ_{k+1}` with the cofactors `w k j` of the pieces as terms. -/
def combinedCofactor (j : ι') : Series K :=
  sumAlongCutoffsSeries (fun k ↦ w k j) (fun k ↦ γ k - γ (k + 1)) (fun k ↦ γ (k + 1))
    (fun _ _ h ↦ hγ (by omega)) (pieces_le_add_sub γ) (fun k ↦ hneg (k + 1))

include hγ hneg

omit [Fintype ι'] in
/-- At cutoffs `ζ ≤ γ 0`, the translated truncations of the combined cofactor vanish. -/
theorem translatedTruncation_combinedCofactor_eq_zero (j : ι') {ζ : ℝ} (hζ : ζ ≤ γ 0) :
    translatedTruncation ((combinedCofactor γ hγ hneg w j : Series K) : K⟦ℝ⟧) ζ = 0 :=
  translatedTruncation_sumAlongCutoffsSeries_eq_zero _ _ _ _ _ _
    (by linarith [hγ (Nat.lt_succ_self 0)])
    (by linarith)

omit [Fintype ι'] in
/-- On the `k`-th interval, the translated truncations of the combined cofactor are those of
`w k j`, modulo `J`: at `γ (k+1) + ξ` for `γ k - γ (k+1) < ξ ≤ 0`, it is `(w k j)^{|ξ}`. -/
theorem translatedTruncation_combinedCofactor_sub_mem (j : ι') (k : ℕ) {ξ : ℝ}
    (hξ : γ k - γ (k + 1) < ξ) (hξ0 : ξ ≤ 0) :
    translatedTruncation ((combinedCofactor γ hγ hneg w j : Series K) : K⟦ℝ⟧) (γ (k + 1) + ξ) -
      translatedTruncation (w k j : K⟦ℝ⟧) ξ ∈ Nonpositive.negativeMonomialIdeal K :=
  translatedTruncation_sumAlongCutoffsSeries_sub_mem _ _ _ _ _ _ k hξ hξ0

variable {e : ι' → NatOrdinal}
  (hw : ∀ k j, ((w k j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (e j)).val)
include hw

omit [Fintype ι'] in
/-- The support of the combined cofactor has order type at most `ω^{e j}`. -/
theorem supportOrderType_combinedCofactor_le (j : ι') :
    ((combinedCofactor γ hγ hneg w j : Series K) : K⟦ℝ⟧).supportOrderType ≤ (ω^ (e j)).val :=
  supportOrderType_sumAlongCutoffsSeries_le _ _ _ _ _ _ fun k ↦ hw k j

omit [Fintype ι'] in
/-- Every translated truncation of the combined cofactor has ordinal value below `ω^(e j + 1)`. -/
theorem ordinalValue_translatedTruncation_combinedCofactor_lt_add_one (j : ι') (ζ : ℝ) :
    ordinalValue (translatedTruncation ((combinedCofactor γ hγ hneg w j : Series K) : K⟦ℝ⟧) ζ) <
      ω^ (e j + 1) := by
  refine (ordinalValue_translatedTruncation_le_of_supportOrderType _ ζ).trans_lt ?_
  rw [← NatOrdinal.of_val (ω^ (e j + 1)), NatOrdinal.of.lt_iff_lt]
  exact (supportOrderType_combinedCofactor_le γ hγ hneg w hw j).trans_lt
    (NatOrdinal.val.lt_iff_lt.mpr (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)))

include hcof

omit [Fintype ι'] in
/-- **The translated truncations of the combined cofactor at cutoffs `ζ < 0` have ordinal value
below `ω^{e j}`.** -/
theorem ordinalValue_translatedTruncation_combinedCofactor_lt (j : ι') {ζ : ℝ} (hζ : ζ < 0) :
    ordinalValue (translatedTruncation ((combinedCofactor γ hγ hneg w j : Series K) : K⟦ℝ⟧) ζ) <
      ω^ (e j) := by
  rcases le_or_gt ζ (γ 0) with h0 | h0
  · rw [translatedTruncation_combinedCofactor_eq_zero γ hγ hneg w j h0, ordinalValue_zero]
    exact NatOrdinal.wpow_pos _
  obtain ⟨k, hk1, hk2⟩ := exists_lt_le_succ_of_strictMono hcof h0 hζ
  have hmem := translatedTruncation_combinedCofactor_sub_mem γ hγ hneg w j k
    (ξ := ζ - γ (k + 1)) (by linarith) (by linarith)
  rw [show γ (k + 1) + (ζ - γ (k + 1)) = ζ by ring] at hmem
  rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal hmem]
  exact ordinalValue_translatedTruncation_lt_of_supportOrderType_lt (hw k j) _

variable {v : ι' → Series K} {c : ι' → NatOrdinal} {τ : NatOrdinal}
  (hv : ∀ j, ∀ β : ℝ, β < 0 → ordinalValue (translatedTruncation (v j : K⟦ℝ⟧) β) < ω^ (c j))
  (hsep : ∀ j, ∀ θ, θ < c j → e j + θ < τ)
  (hres : ∀ k, ∀ ξ : ℝ, γ k - γ (k + 1) < ξ → ξ ≤ 0 →
    ordinalValue (translatedTruncation
      ((piece (γ k) (γ (k + 1)) (E : K⟦ℝ⟧) - ∑ j, w k j * v j : Series K) : K⟦ℝ⟧) ξ) <
        ω^ (τ + 1))
include hv hsep hres

/-- **Combining the cofactors of the pieces.** At every cutoff `ζ ∈ (γ 0, 0)`, the translated
truncation of `E - ∑_j (combined cofactor)_j * v j` has ordinal value below `ω^(τ+1)`. -/
theorem ordinalValue_translatedTruncation_sub_sum_combinedCofactor_mul_lt {ζ : ℝ} (h0 : γ 0 < ζ)
    (hζ : ζ < 0) :
    ordinalValue (translatedTruncation
      ((E - ∑ j, combinedCofactor γ hγ hneg w j * v j : Series K) : K⟦ℝ⟧) ζ) < ω^ (τ + 1) := by
  classical
  obtain ⟨k, hk1, hk2⟩ := exists_lt_le_succ_of_strictMono hcof h0 hζ
  set ξ : ℝ := ζ - γ (k + 1) with hξdef
  have hξ : γ k - γ (k + 1) < ξ := by rw [hξdef]; linarith
  have hξ0 : ξ ≤ 0 := by rw [hξdef]; linarith
  have hζξ : γ (k + 1) + ξ = ζ := by rw [hξdef]; ring
  set C : ι' → Series K := combinedCofactor γ hγ hneg w with hCdef
  set Dk : Series K := piece (γ k) (γ (k + 1)) (E : K⟦ℝ⟧) with hDkdef
  -- the two translated truncations, expanded
  have hX : translatedTruncation ((E - ∑ j, C j * v j : Series K) : K⟦ℝ⟧) ζ =
      translatedTruncation (E : K⟦ℝ⟧) ζ -
        ∑ j, translatedTruncation ((C j * v j : Series K) : K⟦ℝ⟧) ζ := by
    rw [← translatedTruncationAddMonoidHom_apply, AddSubgroupClass.coe_sub, map_sub,
      AddSubmonoidClass.coe_finsetSum, map_sum]
    simp only [translatedTruncationAddMonoidHom_apply]
  have hY : translatedTruncation ((Dk - ∑ j, w k j * v j : Series K) : K⟦ℝ⟧) ξ =
      translatedTruncation (Dk : K⟦ℝ⟧) ξ -
        ∑ j, translatedTruncation ((w k j * v j : Series K) : K⟦ℝ⟧) ξ := by
    rw [← translatedTruncationAddMonoidHom_apply, AddSubgroupClass.coe_sub, map_sub,
      AddSubmonoidClass.coe_finsetSum, map_sum]
    simp only [translatedTruncationAddMonoidHom_apply]
  have hYlt := hres k ξ hξ hξ0
  rw [hY] at hYlt
  rw [hX]
  -- the difference of the two expansions
  set A := translatedTruncation (E : K⟦ℝ⟧) ζ
  set A' := translatedTruncation (Dk : K⟦ℝ⟧) ξ
  set P : ι' → Series K := fun j ↦ translatedTruncation ((C j * v j : Series K) : K⟦ℝ⟧) ζ
  set Q : ι' → Series K := fun j ↦ translatedTruncation ((C j : Series K) : K⟦ℝ⟧) ζ * v j
  set R : ι' → Series K := fun j ↦ translatedTruncation (w k j : K⟦ℝ⟧) ξ * v j
  set P' : ι' → Series K := fun j ↦ translatedTruncation ((w k j * v j : Series K) : K⟦ℝ⟧) ξ
  have hsplit : A - ∑ j, P j = (A' - ∑ j, P' j) +
      ((A - A') - ∑ j, (P j - Q j) - ∑ j, (Q j - R j) + ∑ j, (P' j - R j)) := by
    simp only [Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  refine (ordinalValue_add_le_max _ _).trans_lt (max_lt hYlt ?_)
  refine lt_of_lt_of_le ?_ (NatOrdinal.wpow_le_wpow.mpr (lt_add_one τ).le)
  -- each of the four differences has ordinal value below `ω^τ`
  have hτpos : (0 : NatOrdinal) < ω^ τ := NatOrdinal.wpow_pos τ
  have hAA' : ordinalValue (A - A') < ω^ τ := by
    have := translatedTruncation_window_sub_mem (γ k) (γ (k + 1)) (E : K⟦ℝ⟧) hξ hξ0
    rw [hζξ] at this
    rw [← ordinalValue_neg, neg_sub, ordinalValue_of_mem_negativeMonomialIdeal this]
    exact hτpos
  have hPQ : ∀ j, ordinalValue (P j - Q j) < ω^ τ := fun j ↦
    ordinalValue_translatedTruncation_mul_sub_mul_lt
      (fun β _ ↦ ordinalValue_translatedTruncation_combinedCofactor_lt_add_one γ hγ hneg w hw j β)
      (hv j) (hsep j) hζ
  have hQR : ∀ j, ordinalValue (Q j - R j) < ω^ τ := fun j ↦ by
    have hmem := translatedTruncation_combinedCofactor_sub_mem γ hγ hneg w j k hξ hξ0
    rw [hζξ] at hmem
    have : Q j - R j ∈ Nonpositive.negativeMonomialIdeal K := by
      rw [show Q j - R j = (translatedTruncation ((C j : Series K) : K⟦ℝ⟧) ζ -
        translatedTruncation (w k j : K⟦ℝ⟧) ξ) * v j by simp only [Q, R]; ring]
      exact Ideal.mul_mem_right _ _ hmem
    rw [ordinalValue_of_mem_negativeMonomialIdeal this]
    exact hτpos
  have hP'R : ∀ j, ordinalValue (P' j - R j) < ω^ τ := fun j ↦ by
    rcases lt_or_eq_of_le hξ0 with hξlt | hξ0'
    · exact ordinalValue_translatedTruncation_mul_sub_mul_lt
        (fun β _ ↦ (ordinalValue_translatedTruncation_lt_of_supportOrderType_lt (hw k j) β).trans
          (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)))
        (hv j) (hsep j) hξlt
    · simp only [P', R, hξ0', translatedTruncation_zero, sub_self, ordinalValue_zero]
      exact hτpos
  have hsum : ∀ (f : ι' → Series K), (∀ j, ordinalValue (f j) < ω^ τ) →
      ordinalValue (∑ j, f j) < ω^ τ := fun f hf ↦
    ordinalValue_sum_lt _ _ hτpos fun j _ ↦ hf j
  refine (ordinalValue_add_le_max _ _).trans_lt (max_lt ?_ (hsum _ hP'R))
  rw [sub_eq_add_neg]
  refine (ordinalValue_add_le_max _ _).trans_lt
    (max_lt ?_ (by rw [ordinalValue_neg]; exact hsum _ hQR))
  rw [sub_eq_add_neg]
  exact (ordinalValue_add_le_max _ _).trans_lt
    (max_lt hAA' (by rw [ordinalValue_neg]; exact hsum _ hPQ))

end CombinedCofactors

end Berarducci
