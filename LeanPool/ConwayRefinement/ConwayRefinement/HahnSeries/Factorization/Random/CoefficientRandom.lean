/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.Random
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.TruncationIndependence
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.IndependenceWindow
public import LeanPool.ConwayRefinement.ConwayRefinement.LinearAlgebra.AlgebraicIndependentDet
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.DifferenceAvoidance

import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Algebraically independent coefficients give hereditary `rv_J`-independence

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Proposition 3.4 and Corollary 3.5: if the coefficients of `b_1, …, b_n` are algebraically
independent over `ℚ` and `deg_J(b_i) = α ≥ 1`, then `rv_J(b_1), …, rv_J(b_n)` are linearly
independent, and `Q(b_1, …, b_n)` holds.

The source's proof of Proposition 3.4 picks exponents `γ_1, …, γ_n` in `supp(u_1)` and forms
the matrix `A[i, j] = u_{j, γ_i}`, whose determinant vanishes because `A v = 0` for the
coefficient vector `v ≠ 0` of the relation; it concludes that "the elements of `A` are not
algebraically independent". Two points are completed here. The entries `u_{j, γ_i}` must be
distinct members of the coefficient family, so the `γ_i` have to be chosen in the supports of
all the `u_j` at once; and Corollary 3.5 applies Proposition 3.4 to families of translated
truncations `b_i^{|γ_{i,j}}`, whose joint coefficient family is not algebraically independent,
since one coefficient of `b_i` reappears in several truncations. Both are met by a single
argument for families of translated truncations `c_k = b_{j(k)}^{|γ(k)}` at distinct pairs: the
exponents `x_q`, one in the support of each `c_q` near zero and outside the support of the
relation, are chosen so that no difference `x_q - x_{q'}` equals a difference `γ(k) - γ(k')`.
Then the entries `c_k(x_q) = b_{j(k)}(γ(k) + x_q)` are zero or pairwise distinct coefficients, the
diagonal entries are nonzero, and the determinant is a nonzero polynomial in the coefficients,
being `1` when the diagonal variables are set to `1` and the others to `0`.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- FLLM24, Proposition 3.4 in the form needed for Corollary 3.5: the translated truncations at
distinct pairs of a family with algebraically independent coefficients, when of a common positive
degree, have linearly independent classes. -/
theorem IsMutuallyCoefficientRandom.truncationsIndependent {ι : Type} {b : ι → Series K}
    (hb : IsMutuallyCoefficientRandom b) : TruncationsIndependent K b := by
  refine TruncationsIndependent.of fun d hd κ _ j γ hinj hγ hval ↦ ?_
  classical
  cases nonempty_fintype κ
  set c : κ → Series K := fun k ↦ translatedTruncation (b (j k) : K⟦ℝ⟧) (γ k) with hc
  rw [linearIndependent_iff']
  intro s g hsum k₀ hk₀
  by_contra hg₀
  -- Restrict to the support `P` of the coefficients.
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
  -- The relation has ordinal value below `ω^d`.
  set R : Series K := ∑ k : P, (HahnSeries.Nonpositive.C : K →+* Series K) (g k) * c k with hR
  have hRlt : ordinalValue R < ω^ (d : NatOrdinal) :=
    ordinalValue_sum_C_mul_lt_of_sum_smul_rvJ_eq_zero (fun k : P ↦ hval k) (fun k : P ↦ g k)
      hrel'
  have hd' : (0 : NatOrdinal) < d := Nat.cast_pos.mpr hd
  -- A common window `(η, 0)` in which every `c k` has infinitely many support points outside
  -- the support of `R`.
  have hwin : ∀ k : P, ∃ η₀ < (0 : ℝ), ∀ η, η₀ < η → η < 0 →
      ((((c k : Series K) : K⟦ℝ⟧).support ∩ Set.Ioo η 0) \ (R : K⟦ℝ⟧).support).Infinite :=
    fun k ↦ exists_forall_infinite_support_diff hd' (hval k) hRlt
  choose η₀ hη₀ hwin using hwin
  have hPne : (Finset.univ : Finset P).Nonempty := ⟨⟨k₀, hk₀P⟩, Finset.mem_univ _⟩
  set η := (Finset.univ.sup' hPne η₀) / 2 with hη
  have hηneg : η < 0 := by
    have : Finset.univ.sup' hPne η₀ < 0 := by
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' hPne η₀
      rw [hk]; exact hη₀ k
    rw [hη]; linarith
  have hηgt : ∀ k : P, η₀ k < η := fun k ↦ by
    have h1 : η₀ k ≤ Finset.univ.sup' hPne η₀ := Finset.le_sup' η₀ (Finset.mem_univ k)
    have h2 : Finset.univ.sup' hPne η₀ < 0 := by linarith [hηneg]
    rw [hη]; linarith
  set E : P → Set ℝ := fun k ↦ (((c k : Series K) : K⟦ℝ⟧).support ∩ Set.Ioo η 0) \
    (R : K⟦ℝ⟧).support with hE
  have hEinf : ∀ k : P, (E k).Infinite := fun k ↦ hwin k η (hηgt k) hηneg
  -- Exponents with differences avoiding the differences of the `γ k`.
  set D : Finset ℝ := (Finset.univ : Finset (P × P)).image fun p ↦ γ p.1 - γ p.2 with hD
  obtain ⟨x, hxE, hxD⟩ := exists_forall_mem_forall_sub_notMem (Finset.univ : Finset P) E hEinf D
  have hxE' : ∀ q : P, x q ∈ E q := fun q ↦ hxE q (Finset.mem_univ q)
  have hxneg : ∀ q : P, x q < 0 := fun q ↦ (hxE' q).1.2.2
  have hxR : ∀ q : P, ((R : Series K) : K⟦ℝ⟧).coeff (x q) = 0 := fun q ↦ by
    have := (hxE' q).2
    rwa [HahnSeries.mem_support, not_ne_iff] at this
  have hxc : ∀ q : P, ((c q : Series K) : K⟦ℝ⟧).coeff (x q) ≠ 0 := fun q ↦ (hxE' q).1.1
  -- The matrix of coefficients.
  have hcoeff : ∀ (q k : P), ((c k : Series K) : K⟦ℝ⟧).coeff (x q) =
      ((b (j k) : Series K) : K⟦ℝ⟧).coeff (γ k + x q) := fun q k ↦ by
    rw [hc, coeff_translatedTruncation, ite_eq_left (hxneg q).le]
  let M : Matrix P P K := Matrix.of fun q k ↦ ((c k : Series K) : K⟦ℝ⟧).coeff (x q)
  have hMg : M.mulVec (fun k : P ↦ g k) = 0 := by
    funext q
    rw [Matrix.mulVec, Pi.zero_apply, ← hxR q, hR, coeff_sum_C_mul]
    simp only [dotProduct, Matrix.of_apply, M]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hgne : (fun k : P ↦ g k) ≠ 0 := by
    intro h
    exact hgP k₀ hk₀P (congrFun h ⟨k₀, hk₀P⟩)
  have hdet : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hgne, hMg⟩
  -- The pattern of variables.
  let v : P → P → Option (coefficientIndex b) := fun q k ↦
    if h : (j k, γ k + x q) ∈ coefficientIndex b then some ⟨(j k, γ k + x q), h⟩ else none
  have hM : ∀ q k, M q k = (v q k).elim 0 (fun p : coefficientIndex b ↦
      ((b p.1.1 : Series K) : K⟦ℝ⟧).coeff p.1.2) := by
    intro q k
    simp only [M, Matrix.of_apply, v]
    rw [hcoeff q k]
    by_cases h : (j k, γ k + x q) ∈ coefficientIndex b
    · rw [dite_eq_left h]
      rfl
    · rw [dite_eq_right h, Option.elim]
      rw [mem_coefficientIndex_iff, not_ne_iff] at h
      exact h
  have hdiag : ∀ q, (v q q).isSome := by
    intro q
    have h : (j q, γ q + x q) ∈ coefficientIndex b := by
      rw [mem_coefficientIndex_iff]
      rw [← hcoeff q q]
      exact hxc q
    simp only [v, dite_eq_left h, Option.isSome_some]
  have hdistinct : ∀ q k q' k' w, v q k = some w → v q' k' = some w → q = q' ∧ k = k' := by
    intro q k q' k' w h1 h2
    have hpair : (j k, γ k + x q) = (j k', γ k' + x q') := by
      by_cases hk : (j k, γ k + x q) ∈ coefficientIndex b
      · by_cases hk' : (j k', γ k' + x q') ∈ coefficientIndex b
        · simp only [v, dite_eq_left hk, dite_eq_left hk', Option.some.injEq] at h1 h2
          exact congrArg Subtype.val (h1.trans h2.symm)
        · simp [v, dite_eq_right hk'] at h2
      · simp [v, dite_eq_right hk] at h1
    have hj : j k = j k' := congrArg Prod.fst hpair
    have hγ' : γ k + x q = γ k' + x q' := congrArg Prod.snd hpair
    by_cases hqq : q = q'
    · subst hqq
      have hγk : γ k = γ k' := add_right_cancel hγ'
      exact ⟨rfl, Subtype.ext (hinj (Prod.ext hj hγk))⟩
    · exfalso
      apply hxD q (Finset.mem_univ q) q' (Finset.mem_univ q') hqq
      refine Finset.mem_image.mpr ⟨(k', k), Finset.mem_univ _, ?_⟩
      linarith
  exact Matrix.det_ne_zero_of_algebraicIndependent hb.algebraicIndependent v M hM hdiag
    hdistinct hdet

/-- FLLM24, Corollary 3.5 for finite degrees: a finite family of series with algebraically
independent coefficients and ordinal value `ω^n`, `n ≥ 1`, is hereditarily
`rv_J`-independent. -/
theorem IsMutuallyCoefficientRandom.hereditarilyRVIndependent {ι : Type} [Finite ι]
    {b : ι → Series K} (hb : IsMutuallyCoefficientRandom b) {n : ℕ} (hn : 1 ≤ n)
    (hval : ∀ i, ordinalValue (b i) = ω^ (n : NatOrdinal)) :
    HereditarilyRVIndependent n b :=
  hb.truncationsIndependent.hereditarilyRVIndependent_self hn hval

end FLLM24

end
