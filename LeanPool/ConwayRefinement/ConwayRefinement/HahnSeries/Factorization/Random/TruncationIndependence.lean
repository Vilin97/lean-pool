/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.HereditaryIndependence

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max

/-!
# Hereditary `rv_J`-independence from the independence of truncations

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Corollary 3.5 and Proposition 3.6, derive `Q(b_1, …, b_n)` from a randomness hypothesis by
verifying Axiom 1 for the family and for all families of translated truncations that Axiom 2
produces, the hypothesis being inherited by the truncations. This module isolates the
induction: if every finite family of translated truncations `(b_{j(k)})^{|γ(k)}` at distinct
pairs `(j(k), γ(k))` of a common positive degree `d` has linearly independent classes, then every
such family is hereditarily `rv_J`-independent.

The point needing care is the threshold `δ` of Axiom 2. Translated truncations compose,
`(b^{|γ})^{|γ'} = b^{|γ + γ'}`, so a family of truncations of the truncations is again a family of
truncations of the `b_i`, but two distinct pairs `(j, γ)`, `(j, γ'')` can produce the same pair
`(j, γ + δ₁) = (j, γ'' + δ₂)` when `|γ - γ''| = |δ₁ - δ₂|`. Choosing `δ` below half the least
gap between exponents attached to the same index keeps the composed pairs distinct, and the
source's requirement "`γ_{i,j} ≠ γ_{i,j'}` for `j ≠ j'`" is preserved.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

variable (K) in
/-- Every finite family of translated truncations of the `b i` at distinct pairs, all of ordinal
value `ω^d` with `d ≥ 1`, has `K`-linearly independent classes `rv_J`. -/
def TruncationsIndependent {ι : Type} (b : ι → Series K) : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (κ : Type) [Finite κ] (j : κ → ι) (γ : κ → ℝ),
    Function.Injective (fun k ↦ (j k, γ k)) → (∀ k, γ k ≤ 0) →
    (∀ k, ordinalValue (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) = ω^ (d : NatOrdinal)) →
    LinearIndependent K (fun k ↦ rvJ (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)))

/-- Introduction rule for `TruncationsIndependent`. -/
theorem TruncationsIndependent.of {ι : Type} {b : ι → Series K}
    (h : ∀ (d : ℕ), 1 ≤ d → ∀ (κ : Type) [Finite κ] (j : κ → ι) (γ : κ → ℝ),
      Function.Injective (fun k ↦ (j k, γ k)) → (∀ k, γ k ≤ 0) →
      (∀ k, ordinalValue (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) = ω^ (d : NatOrdinal)) →
      LinearIndependent K (fun k ↦ rvJ (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)))) :
    TruncationsIndependent K b :=
  h

theorem TruncationsIndependent.linearIndependent {ι : Type} {b : ι → Series K}
    (hb : TruncationsIndependent K b) {d : ℕ} (hd : 1 ≤ d) (κ : Type) [Finite κ] (j : κ → ι)
    (γ : κ → ℝ) (hinj : Function.Injective (fun k ↦ (j k, γ k))) (hγ : ∀ k, γ k ≤ 0)
    (hval : ∀ k, ordinalValue (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) =
      ω^ (d : NatOrdinal)) :
    LinearIndependent K (fun k ↦ rvJ (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k))) :=
  hb d hd κ j γ hinj hγ hval

/-- The least gap between two exponents attached to the same index of a finite family of pairs:
the minimum of the finite set `{|γ k - γ k'| : k ≠ k', j k = j k'}`, or `1` if the set is
empty. -/
private theorem exists_gap {ι κ : Type} [Finite κ] (j : κ → ι) (γ : κ → ℝ)
    (hinj : Function.Injective (fun k ↦ (j k, γ k))) :
    ∃ g : ℝ, 0 < g ∧ ∀ k k', k ≠ k' → j k = j k' → g ≤ |γ k - γ k'| := by
  classical
  cases nonempty_fintype κ
  let P : Finset (κ × κ) := Finset.univ.filter fun p ↦ p.1 ≠ p.2 ∧ j p.1 = j p.2
  let G : Finset ℝ := P.image fun p ↦ |γ p.1 - γ p.2|
  have hpos : ∀ g ∈ G, 0 < g := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hne, hj⟩ := (Finset.mem_filter.mp hp).2
    rw [abs_pos, sub_ne_zero]
    intro hγ
    exact hne (hinj (Prod.ext hj hγ))
  rcases G.eq_empty_or_nonempty with hG | hG
  · refine ⟨1, one_pos, fun k k' hne hj ↦ ?_⟩
    exfalso
    have : |γ k - γ k'| ∈ G :=
      Finset.mem_image.mpr ⟨(k, k'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hj⟩, rfl⟩
    rw [hG] at this
    exact Finset.notMem_empty _ this
  · refine ⟨G.min' hG, hpos _ (G.min'_mem hG), fun k k' hne hj ↦ ?_⟩
    exact G.min'_le _
      (Finset.mem_image.mpr ⟨(k, k'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hj⟩, rfl⟩)

/-- FLLM24, the common inductive core of Corollary 3.5 and Proposition 3.6: if all finite
families of translated truncations of the `b i` at distinct pairs and of a common positive degree
have independent classes, then every such family is hereditarily `rv_J`-independent. -/
theorem TruncationsIndependent.hereditarilyRVIndependent {ι : Type} {b : ι → Series K}
    (hb : TruncationsIndependent K b) {d : ℕ} (hd : 1 ≤ d) (κ : Type) [Finite κ] (j : κ → ι)
    (γ : κ → ℝ) (hinj : Function.Injective (fun k ↦ (j k, γ k))) (hγ : ∀ k, γ k ≤ 0)
    (hval : ∀ k, ordinalValue (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) =
      ω^ (d : NatOrdinal)) :
    HereditarilyRVIndependent d (fun k ↦ translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) := by
  induction d generalizing κ with
  | zero => exact absurd hd (by decide)
  | succ d ih =>
      refine HereditarilyRVIndependent.of_succ hval
        (hb.linearIndependent hd κ j γ hinj hγ hval) fun hd' ↦ ?_
      obtain ⟨g, hg, hgap⟩ := exists_gap j γ hinj
      refine ⟨-(g / 2), by linarith, fun κ' _ j' γ' hinj' hδγ' hγ' hval' ↦ ?_⟩
      -- The composed family of truncations of the `b i`.
      have hcomp : ∀ k', translatedTruncation
          ((translatedTruncation (b (j (j' k')) : K⟦ℝ⟧) (γ (j' k')) : Series K) : K⟦ℝ⟧) (γ' k') =
          translatedTruncation (b (j (j' k')) : K⟦ℝ⟧) (γ (j' k') + γ' k') := fun k' ↦
        translatedTruncation_translatedTruncation _ _ (hγ' k')
      have hinj'' : Function.Injective (fun k' ↦ (j (j' k'), γ (j' k') + γ' k')) := by
        intro k₁ k₂ h
        have h1 : j (j' k₁) = j (j' k₂) := congrArg Prod.fst h
        have h2 : γ (j' k₁) + γ' k₁ = γ (j' k₂) + γ' k₂ := congrArg Prod.snd h
        by_cases hk : j' k₁ = j' k₂
        · apply hinj'
          refine Prod.ext hk ?_
          rw [hk] at h2
          exact add_left_cancel h2
        · exfalso
          have hge := hgap _ _ hk h1
          have hsub : γ (j' k₁) - γ (j' k₂) = γ' k₂ - γ' k₁ := by linarith
          rw [hsub] at hge
          have h3 := hδγ' k₁
          have h4 := hδγ' k₂
          have h5 := hγ' k₁
          have h6 := hγ' k₂
          have hsmall : |γ' k₂ - γ' k₁| ≤ g / 2 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
          linarith
      have hval'' : ∀ k', ordinalValue (translatedTruncation (b (j (j' k')) : K⟦ℝ⟧)
          (γ (j' k') + γ' k')) = ω^ (d : NatOrdinal) := fun k' ↦ by
        rw [← hcomp k']; exact hval' k'
      have hQ := ih hd' κ' (fun k' ↦ j (j' k')) (fun k' ↦ γ (j' k') + γ' k') hinj''
        (fun k' ↦ add_nonpos (hγ (j' k')) (hγ' k')) hval''
      have hfun : (fun k' ↦ translatedTruncation
          ((translatedTruncation (b (j (j' k')) : K⟦ℝ⟧) (γ (j' k')) : Series K) : K⟦ℝ⟧)
            (γ' k')) =
          fun k' ↦ translatedTruncation (b (j (j' k')) : K⟦ℝ⟧) (γ (j' k') + γ' k') :=
        funext hcomp
      rw [hfun]
      exact hQ

/-- A finite family with independent truncations is hereditarily `rv_J`-independent at its
common positive degree. -/
theorem TruncationsIndependent.hereditarilyRVIndependent_self {ι : Type} [Finite ι]
    {b : ι → Series K} (hb : TruncationsIndependent K b) {d : ℕ} (hd : 1 ≤ d)
    (hval : ∀ i, ordinalValue (b i) = ω^ (d : NatOrdinal)) :
    HereditarilyRVIndependent d b := by
  have h := hb.hereditarilyRVIndependent hd ι id (fun _ ↦ 0)
    (fun i i' h ↦ congrArg Prod.fst h) (fun _ ↦ le_rfl)
    (fun i ↦ by rw [translatedTruncation_zero]; exact hval i)
  have hfun : (fun i ↦ translatedTruncation (b (id i) : K⟦ℝ⟧) 0) = b := by
    funext i
    exact translatedTruncation_zero (b i)
  rwa [hfun] at h

end FLLM24

end
