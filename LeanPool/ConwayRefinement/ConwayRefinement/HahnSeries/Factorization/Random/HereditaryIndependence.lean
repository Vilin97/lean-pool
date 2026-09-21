/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubring
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeSum

/-!
# Hereditary `rv_J`-independence at finite ordinal-value degrees

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
§ 3, define by recursion on `deg_J(b_1)` when series `b_1, …, b_n` of a common ordinal-value degree
are *hereditarily `rv_J`-independent*, written `Q(b_1, …, b_n)`:

1. the classes `rv_J(b_1), …, rv_J(b_n)` are `K`-linearly independent;
2. when `deg_J(b_1) ≠ deg_J^p(b_1)`, there is `δ < 0` such that for every degree `α` with
   `deg_J^r(b_1) ≤ α < deg_J(b_1)` and all exponents `γ_{i,j} ≥ δ`, distinct for fixed `i`, with
   `deg_J(b_i^{|γ_{i,j}}) = α`, the family of translated truncations `b_i^{|γ_{i,j}}` is again
   hereditarily `rv_J`-independent.

This module records the definition for finite ordinal-value degrees `n < ω`, the case of the
finite-degree irreducibility theorem. For `deg_J(b) = n ≥ 1` one has `v_J(b) = ω^n = ω^(n-1) · ω`,
so `deg_J^p(b) = 1` and `deg_J^r(b) = n - 1`: the second clause applies exactly when `n ≥ 2`, and
the degrees `α` it ranges over reduce to the single value `n - 1`. The class `rv_J(b)` is the
initial form of `b` in `P̂ = ⊕ P_α` for the ordinal-value degree.

Families are indexed by an arbitrary type in `Type`; the families of translated truncations in
the second clause are indexed by a finite type `κ` together with maps `j : κ → ι` and
`γ : κ → ℝ`, the requirement "`γ_{i,j} ≠ γ_{i,j'}` whenever `j ≠ j'`" being injectivity of
`k ↦ (j k, γ k)`. Translated truncations are taken at exponents `γ ≤ 0`, the domain of
Definition 2.4; at `γ = 0` the truncation is the series itself, whose degree excludes it from the
second clause.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

/-- The class `rv_J(b)` of FLLM24, Definition 2.15: the initial form of `b` in Berarducci's
ring `P̂` for the ordinal-value degree `deg_J`, which is zero exactly on `J`. -/
def rvJ (b : Series K) : PrincipalSubring K :=
  (ordinalValueDegreeValuation K).initialForm b

theorem rvJ_eq_initialForm (b : Series K) :
    rvJ b = (ordinalValueDegreeValuation K).initialForm b :=
  (rfl)

/-- At ordinal value `ω^α`, the class `rv_J(b)` is the homogeneous class of `b` in grade `α`. -/
theorem rvJ_eq_homogeneousMk {b : Series K} {α : NatOrdinal} (hb : ordinalValue b = ω^ α) :
    rvJ b = (ordinalValueDegreeValuation K).homogeneousMk α
      ⟨b, (mem_ordinalValueDegreeValuation_filtrationLE_iff b α).mpr
        (hb ▸ NatOrdinal.wpow_lt_wpow.mpr (Order.lt_add_one_iff.mpr le_rfl))⟩ := by
  rw [rvJ_eq_initialForm]
  symm
  apply MaxAddDegree.homogeneousMk_eq_initialForm_of_degree_eq
  rw [ordinalValueDegreeValuation_apply, ordinalValueDegree_eq_coe_iff]
  exact hb

/-- `rv_J(b)` vanishes exactly on `J`. -/
theorem rvJ_eq_zero_iff (b : Series K) :
    rvJ b = 0 ↔ b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  rw [rvJ_eq_initialForm, MaxAddDegree.initialForm_eq_zero_iff,
    ordinalValueDegreeValuation_eq_bot_iff]

/-- FLLM24, § 3, at a finite ordinal-value degree `n`: the series `b i` have `v_J(b i) = ω^n`,
their classes `rv_J(b i)` are `K`-linearly independent, and, when `n ≥ 2`, there is `δ < 0`
such that every finite family of translated truncations `(b (j k))^{|γ k}` at distinct pairs
`(j k, γ k)` with `δ ≤ γ k ≤ 0` and `v_J((b (j k))^{|γ k}) = ω^(n-1)` is hereditarily
`rv_J`-independent at degree `n - 1`. -/
def HereditarilyRVIndependent : ℕ → {ι : Type} → (ι → Series K) → Prop
  | 0, _, b =>
      (∀ i, ordinalValue (b i) = ω^ ((0 : ℕ) : NatOrdinal)) ∧
        LinearIndependent K (fun i ↦ rvJ (b i))
  | n + 1, ι, b =>
      (∀ i, ordinalValue (b i) = ω^ ((n + 1 : ℕ) : NatOrdinal)) ∧
        LinearIndependent K (fun i ↦ rvJ (b i)) ∧
        (1 ≤ n → ∃ δ : ℝ, δ < 0 ∧
          ∀ (κ : Type) [Finite κ] (j : κ → ι) (γ : κ → ℝ),
            Function.Injective (fun k ↦ (j k, γ k)) →
            (∀ k, δ ≤ γ k) → (∀ k, γ k ≤ 0) →
            (∀ k, ordinalValue (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) =
              ω^ (n : NatOrdinal)) →
            HereditarilyRVIndependent n
              (fun k ↦ translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)))

namespace HereditarilyRVIndependent

variable {ι : Type} {b : ι → Series K}

/-- Every member of a hereditarily `rv_J`-independent family at degree `n` has ordinal value
`ω^n`. -/
theorem ordinalValue_eq {n : ℕ} (h : HereditarilyRVIndependent n b) (i : ι) :
    ordinalValue (b i) = ω^ (n : NatOrdinal) := by
  cases n with
  | zero => exact h.1 i
  | succ n => exact h.1 i

/-- Axiom 1 of FLLM24, § 3: the classes `rv_J(b i)` are `K`-linearly independent. -/
theorem linearIndependent {n : ℕ} (h : HereditarilyRVIndependent n b) :
    LinearIndependent K (fun i ↦ rvJ (b i)) := by
  cases n with
  | zero => exact h.2
  | succ n => exact h.2.1

/-- Axiom 2 of FLLM24, § 3, at degree `n + 1 ≥ 2`: some threshold `δ < 0` makes every finite
family of translated truncations at distinct pairs above `δ` and of ordinal value `ω^n`
hereditarily `rv_J`-independent at degree `n`. -/
theorem truncations {n : ℕ} (hn : 1 ≤ n) (h : HereditarilyRVIndependent (n + 1) b) :
    ∃ δ : ℝ, δ < 0 ∧
      ∀ (κ : Type) [Finite κ] (j : κ → ι) (γ : κ → ℝ),
        Function.Injective (fun k ↦ (j k, γ k)) →
        (∀ k, δ ≤ γ k) → (∀ k, γ k ≤ 0) →
        (∀ k, ordinalValue (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) =
          ω^ (n : NatOrdinal)) →
        HereditarilyRVIndependent n (fun k ↦ translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) :=
  h.2.2 hn

/-- The constructor for degree `n + 1`: the two axioms, the second required when `n ≥ 1`. -/
theorem of_succ {n : ℕ}
    (hvalue : ∀ i, ordinalValue (b i) = ω^ ((n + 1 : ℕ) : NatOrdinal))
    (hindep : LinearIndependent K (fun i ↦ rvJ (b i)))
    (htrunc : 1 ≤ n → ∃ δ : ℝ, δ < 0 ∧
      ∀ (κ : Type) [Finite κ] (j : κ → ι) (γ : κ → ℝ),
        Function.Injective (fun k ↦ (j k, γ k)) →
        (∀ k, δ ≤ γ k) → (∀ k, γ k ≤ 0) →
        (∀ k, ordinalValue (translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k)) =
          ω^ (n : NatOrdinal)) →
        HereditarilyRVIndependent n (fun k ↦ translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k))) :
    HereditarilyRVIndependent (n + 1) b :=
  ⟨hvalue, hindep, htrunc⟩

/-- At degree one only Axiom 1 is required: `deg_J^p(b) = 1 = deg_J(b)`. -/
theorem of_one (hvalue : ∀ i, ordinalValue (b i) = ω^ ((1 : ℕ) : NatOrdinal))
    (hindep : LinearIndependent K (fun i ↦ rvJ (b i))) :
    HereditarilyRVIndependent 1 b :=
  ⟨hvalue, hindep, fun h ↦ absurd h (by decide)⟩

/-- Hereditary `rv_J`-independence passes to subfamilies. -/
theorem comp_injective {n : ℕ} (h : HereditarilyRVIndependent n b) {ι' : Type} (f : ι' → ι)
    (hf : Function.Injective f) :
    HereditarilyRVIndependent n (b ∘ f) := by
  induction n generalizing ι with
  | zero =>
      exact ⟨fun i ↦ h.1 (f i), h.2.comp f hf⟩
  | succ n ih =>
      refine ⟨fun i ↦ h.1 (f i), h.2.1.comp f hf, fun hn ↦ ?_⟩
      obtain ⟨δ, hδ, hδfam⟩ := h.2.2 hn
      refine ⟨δ, hδ, fun κ _ j γ hinj hδγ hγ hvalue ↦ ?_⟩
      have hinj' : Function.Injective (fun k ↦ (f (j k), γ k)) := by
        intro k k' hkk'
        have h1 : f (j k) = f (j k') := congrArg Prod.fst hkk'
        have h2 : γ k = γ k' := congrArg Prod.snd hkk'
        exact hinj (Prod.ext (hf h1) h2)
      exact hδfam κ (fun k ↦ f (j k)) γ hinj' hδγ hγ hvalue

end HereditarilyRVIndependent

end FLLM24

end
