/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.Random
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.TruncationIndependence
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.IndependenceWindow
public import LeanPool.ConwayRefinement.ConwayRefinement.LinearAlgebra.IndicatorFinsupp

/-!
# Independent support closures give hereditary `rv_J`-independence

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Proposition 3.6: if `deg_J(b_i) = α > 0`, the closures of the supports of the `b_i` meet pairwise
only in `{0}`, and the union of these closures with `0` removed is `ℚ`-linearly independent, then
`Q(b_1, …, b_n)` holds.

As in the source, a vanishing relation `∑ k_p c_p ∈ J_α` among translated truncations
`c_p = b_{i(p)}^{|γ_p}` at distinct pairs is tested at a support point `x < 0` of one `c_p` near
zero outside the support of the relation; the coefficient at `x` must cancel against another
`c_{p'}`, giving `β - γ_p = x = β' - γ_{p'}` with `β ∈ supp b_{i(p)}`, `β' ∈ supp b_{i(p')}`. The
`ℚ`-relation `β + γ_{p'} = β' + γ_p` among elements of the independent set (each `γ` lies in the
closure of the corresponding support, or is `0`) forces `β = β'` and `γ_p = γ_{p'}`, since
`β = γ_p` would give `x = 0`; then `β ≠ 0` lies in two support closures, so `i(p) = i(p')`, and
the pairs coincide. The source states Axiom 2 for the family itself and assumes principality
"for simplicity"; the argument here covers the truncation families directly, which is what
Axiom 2 needs at every depth.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-- A translated truncation outside `J` is taken at a point of the closure of the support. -/
private theorem mem_closure_support_of_ordinalValue_ne_zero {b : Series K} {γ : ℝ}
    (h : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) γ) ≠ 0) :
    γ ∈ closure (b : K⟦ℝ⟧).support := by
  by_contra hγ
  exact h (ordinalValue_of_mem_negativeMonomialIdeal
    (translatedTruncation_mem_negativeMonomialIdeal_of_not_mem_closure_support hγ))

/-- FLLM24, Proposition 3.6 in the form needed for Axiom 2: under the support clause of mutual
randomness, the translated truncations at distinct pairs of a common positive degree have
linearly independent classes. -/
theorem IsMutuallySupportRandom.truncationsIndependent {ι : Type} {b : ι → Series K}
    (hb : IsMutuallySupportRandom b) : TruncationsIndependent K b := by
  refine TruncationsIndependent.of fun d hd κ _ j γ hinj hγ hval ↦ ?_
  classical
  cases nonempty_fintype κ
  set c : κ → Series K := fun k ↦ translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k) with hc
  rw [linearIndependent_iff']
  intro s g hsum k₀ hk₀
  by_contra hg₀
  set P := s.filter (fun k ↦ g k ≠ 0) with hP
  have hk₀P : k₀ ∈ P := Finset.mem_filter.mpr ⟨hk₀, hg₀⟩
  have hgP : ∀ k ∈ P, g k ≠ 0 := fun k hk ↦ (Finset.mem_filter.mp hk).2
  have hrelP : ∑ k ∈ P, g k • rvJ (c k) = 0 := by
    rw [hP, Finset.sum_filter_of_ne]
    · exact hsum
    · intro k _ hk hgk
      exact hk (by rw [hgk, zero_smul])
  have hrel' : ∑ k : P, g k • rvJ (c k) = 0 := by
    rw [Finset.sum_coe_sort P (fun k ↦ g k • rvJ (c k))]
    exact hrelP
  set R : Series K := ∑ k : P, (HahnSeries.Nonpositive.C : K →+* Series K) (g k) * c k with hR
  have hRlt : ordinalValue R < ω^ (d : NatOrdinal) :=
    ordinalValue_sum_C_mul_lt_of_sum_smul_rvJ_eq_zero (fun k : P ↦ hval k) (fun k : P ↦ g k)
      hrel'
  have hd' : (0 : NatOrdinal) < d := Nat.cast_pos.mpr hd
  -- A support point of `c k₀` near zero outside the support of `R`.
  obtain ⟨η₀, hη₀, hwin⟩ := exists_forall_infinite_support_diff hd' (hval k₀) hRlt
  obtain ⟨x, ⟨hxc, -, hx0⟩, hxR⟩ := (hwin (η₀ / 2) (by linarith) (by linarith)).nonempty
  rw [HahnSeries.mem_support, not_ne_iff] at hxR
  -- The coefficient of `R` at `x` vanishes, so another `c k₁` contributes at `x`.
  have hcoeff : ∀ k : κ, ((c k : Series K) : K⟦ℝ⟧).coeff x =
      ((b (j k) : Series K) : K⟦ℝ⟧).coeff (γ k + x) := fun k ↦ by
    rw [hc, coeff_translatedTruncation, if_pos hx0.le]
  obtain ⟨k₁, hk₁P, hk₁ne, hk₁c⟩ : ∃ k₁ ∈ P, k₁ ≠ k₀ ∧ ((c k₁ : Series K) : K⟦ℝ⟧).coeff x ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hsum' : ((R : Series K) : K⟦ℝ⟧).coeff x = g k₀ * ((c k₀ : Series K) : K⟦ℝ⟧).coeff x := by
      rw [hR, coeff_sum_C_mul]
      rw [Finset.sum_eq_single ⟨k₀, hk₀P⟩]
      · intro k _ hk
        have hkne : (k : κ) ≠ k₀ := fun h ↦ hk (Subtype.ext h)
        rw [hnone k k.2 hkne, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hxR] at hsum'
    exact mul_ne_zero (hgP k₀ hk₀P) hxc hsum'.symm
  -- The two support points and the linear relation between them.
  set β := γ k₀ + x with hβ
  set β' := γ k₁ + x with hβ'
  have hβsupp : β ∈ ((b (j k₀) : Series K) : K⟦ℝ⟧).support := by
    rw [HahnSeries.mem_support, ← hcoeff k₀]; exact hxc
  have hβ'supp : β' ∈ ((b (j k₁) : Series K) : K⟦ℝ⟧).support := by
    rw [HahnSeries.mem_support, ← hcoeff k₁]; exact hk₁c
  have hβneg : β < 0 := by linarith [hγ k₀]
  have hβ'neg : β' < 0 := by linarith [hγ k₁]
  set L := supportClosureUnion b with hL
  have hβL : β ∈ L := (mem_supportClosureUnion_iff b β).mpr
    ⟨⟨j k₀, subset_closure hβsupp⟩, hβneg.ne⟩
  have hβ'L : β' ∈ L := (mem_supportClosureUnion_iff b β').mpr
    ⟨⟨j k₁, subset_closure hβ'supp⟩, hβ'neg.ne⟩
  have hγcl : ∀ k, γ k ∈ closure ((b (j k) : Series K) : K⟦ℝ⟧).support := fun k ↦
    mem_closure_support_of_ordinalValue_ne_zero (by rw [hval k]; exact (NatOrdinal.wpow_pos _).ne')
  have hγL : ∀ k, γ k ∈ L ∨ γ k = 0 := fun k ↦ by
    rcases eq_or_ne (γ k) 0 with h | h
    · exact Or.inr h
    · exact Or.inl ((mem_supportClosureUnion_iff b (γ k)).mpr ⟨⟨j k, hγcl k⟩, h⟩)
  -- Injectivity of the linear combination over the independent set `L`.
  have hinjL : Function.Injective (Finsupp.linearCombination ℚ (fun z : L ↦ (z : ℝ))) :=
    linearIndependent_iff_injective_finsuppLinearCombination.mp hb.linearIndependent
  have hcomb : ∀ k, Finsupp.linearCombination ℚ (fun z : L ↦ (z : ℝ))
      (L.indicatorFinsupp ℚ (γ k)) = γ k := fun k ↦ by
    rcases hγL k with h | h
    · exact L.linearCombination_indicatorFinsupp_of_mem ℚ h
    · rw [h]; exact L.linearCombination_indicatorFinsupp_zero ℚ
  have hrelation : L.indicatorFinsupp ℚ β + L.indicatorFinsupp ℚ (γ k₁) =
      L.indicatorFinsupp ℚ β' + L.indicatorFinsupp ℚ (γ k₀) := by
    apply hinjL
    rw [map_add, map_add, L.linearCombination_indicatorFinsupp_of_mem ℚ hβL,
      L.linearCombination_indicatorFinsupp_of_mem ℚ hβ'L, hcomb k₁, hcomb k₀, hβ, hβ']
    ring
  -- Evaluate at `β`: the right side must be nonzero there.
  have hpos : 0 < (L.indicatorFinsupp ℚ β + L.indicatorFinsupp ℚ (γ k₁)) ⟨β, hβL⟩ := by
    rw [Finsupp.add_apply, L.indicatorFinsupp_apply_self hβL]
    linarith [L.indicatorFinsupp_apply_nonneg (R := ℚ) (γ k₁) ⟨β, hβL⟩]
  rw [hrelation, Finsupp.add_apply] at hpos
  have hγ₀ : L.indicatorFinsupp ℚ (γ k₀) ⟨β, hβL⟩ = 0 := by
    apply L.indicatorFinsupp_apply_of_ne
    intro heq
    have : x = 0 := by simp only at heq; linarith
    exact hx0.ne this
  rw [hγ₀, add_zero] at hpos
  have hββ' : β = β' := by
    by_contra hne
    rw [L.indicatorFinsupp_apply_of_ne β' ⟨β, hβL⟩ hne] at hpos
    exact lt_irrefl _ hpos
  -- Hence the exponents agree and the support closures meet at `β ≠ 0`.
  have hγeq : γ k₁ = γ k₀ := by
    have h := hrelation
    rw [hββ', add_comm (L.indicatorFinsupp ℚ β'), add_comm (L.indicatorFinsupp ℚ β')] at h
    have h' := add_right_cancel h
    have := congrArg (Finsupp.linearCombination ℚ (fun z : L ↦ (z : ℝ))) h'
    rwa [hcomb k₁, hcomb k₀] at this
  have hj : j k₀ = j k₁ := by
    by_contra hne
    have hmem : β ∈ closure ((b (j k₀) : Series K) : K⟦ℝ⟧).support ∩
        closure ((b (j k₁) : Series K) : K⟦ℝ⟧).support :=
      ⟨subset_closure hβsupp, hββ' ▸ subset_closure hβ'supp⟩
    exact hβneg.ne (hb.closure_inter_subset _ _ hne hmem)
  exact hk₁ne (hinj (Prod.ext hj.symm hγeq))

/-- FLLM24, Proposition 3.6 for finite degrees: a finite family satisfying the support clause of
mutual randomness, of ordinal value `ω^n` with `n ≥ 1`, is hereditarily `rv_J`-independent. -/
theorem IsMutuallySupportRandom.hereditarilyRVIndependent {ι : Type} [Finite ι]
    {b : ι → Series K} (hb : IsMutuallySupportRandom b) {n : ℕ} (hn : 1 ≤ n)
    (hval : ∀ i, ordinalValue (b i) = ω^ (n : NatOrdinal)) :
    HereditarilyRVIndependent n b :=
  hb.truncationsIndependent.hereditarilyRVIndependent_self hn hval

end FLLM24

end
