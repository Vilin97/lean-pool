/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.LeastTerm
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.CantorTermCount

/-!
# Approaching a natural sum from below in one summand

Let `λ ≠ 0` and let `σ` be an ordinal every term of whose Cantor normal form is at least the last
term `ω^e` of that of `λ`. Then every `τ < λ ⊕ σ` is bounded by some `ρ ⊕ σ` with `ρ < λ`:
`sup_{ρ < λ} (ρ ⊕ σ) = λ ⊕ σ`. Writing `λ = λ' + ω^e`, the natural sum `λ ⊕ σ` is the ordinal sum
`(λ' ⊕ σ) + ω^e`, because all terms of `λ' ⊕ σ` are at least `ω^e`; so `τ < λ' ⊕ σ`, in which
case `ρ = λ'` serves, or `τ = (λ' ⊕ σ) + ξ` with `ξ < ω^e`, in which case `ρ = λ' ⊕ ξ < λ` and
`ρ ⊕ σ ≥ τ`. Without the hypothesis on `σ` the supremum can be smaller: `sup_{ρ < ω} (ρ ⊕ 1) = ω`,
not `ω ⊕ 1`.
-/

open Ordinal

universe u

public noncomputable section

namespace NatOrdinal

/-- Every term of the Cantor normal form of `a ≠ 0`, with repeated terms, is at least its last
term. -/
theorem leastTerm_le_of_mem {a : NatOrdinal.{u}} (ha : a ≠ 0) {y : Ordinal.{u}}
    (hy : y ∈ a.val.additivePrincipalTerms) : leastTerm a ≤ NatOrdinal.of y :=
  NatOrdinal.val.le_iff_le.mp (by simpa using val_leastTerm_le_of_mem ha hy)

/-- The terms of a natural sum are the terms of the summands. -/
theorem mem_additivePrincipalTerms_add_iff (a b : NatOrdinal.{u}) (y : Ordinal.{u}) :
    y ∈ (a + b).val.additivePrincipalTerms ↔
      y ∈ a.val.additivePrincipalTerms ∨ y ∈ b.val.additivePrincipalTerms := by
  rw [(additivePrincipalTerms_add_perm a b).mem_iff, List.mem_append]

/-- If every term of `σ` is at least the last term of `λ ≠ 0`, then every term of `λ ⊕ σ` is. -/
theorem leastTerm_le_of_mem_add {lam sigma : NatOrdinal.{u}} (hlam : lam ≠ 0)
    (hsigma : sigma = 0 ∨ leastTerm lam ≤ leastTerm sigma) {y : Ordinal.{u}}
    (hy : y ∈ (lam + sigma).val.additivePrincipalTerms) : leastTerm lam ≤ NatOrdinal.of y := by
  rcases (mem_additivePrincipalTerms_add_iff lam sigma y).mp hy with h | h
  · exact leastTerm_le_of_mem hlam h
  · rcases hsigma with rfl | hle
    · rw [NatOrdinal.val_zero, additivePrincipalTerms_zero] at h
      exact absurd h List.not_mem_nil
    · exact hle.trans (leastTerm_le_of_mem (by rintro rfl; simp at h) h)

/-- Let `λ ≠ 0` and let every term of the Cantor normal form of `σ` be at least the last term of
that of `λ`. Then every `τ < λ ⊕ σ` is at most `ρ ⊕ σ` for some `ρ < λ`. -/
@[blueprint "lem:natural-sum-approach"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Cofinality below a Hessenberg sum")
  (statement := /--
    Let $\lambda\neq0$ and $\sigma$ be ordinals such that $\sigma=0$ or every
    term of the Cantor normal form of $\sigma$ is at least the last term of the
    Cantor normal form of $\lambda$.  Then for every $\tau<\lambda\nsum\sigma$
    there is $\rho<\lambda$ with $\tau\le\rho\nsum\sigma$.
  -/)
  (proof := /--
  Write $\lambda=\lambda'\mathbin\oplus\omega^e$, where $\omega^e$ is its last
  Cantor-normal-form term.  The hypothesis on $\sigma$ gives
  $\lambda\mathbin\oplus\sigma=(\lambda'\mathbin\oplus\sigma)+\omega^e$.
  If $\tau$ lies below $\lambda'\mathbin\oplus\sigma$, take $\rho=\lambda'$.
  Otherwise write $\tau=(\lambda'\mathbin\oplus\sigma)+\nu$ with
  $\nu<\omega^e$ and take $\rho=\lambda'\mathbin\oplus\nu$; strict
  monotonicity gives $\rho<\lambda$, and ordinary addition is bounded by the
  natural sum.
  -/)]
theorem exists_lt_le_add_of_lastCantorTerm_le {lam sigma tau : NatOrdinal.{u}} (hlam : lam ≠ 0)
    (hsigma : sigma = 0 ∨ leastTerm lam ≤ leastTerm sigma) (htau : tau < lam + sigma) :
    ∃ rho < lam, tau ≤ rho + sigma := by
  obtain ⟨L, hL⟩ : ∃ L, leastTerm lam = L := ⟨_, rfl⟩
  obtain ⟨lam', hlam'⟩ : ∃ lam', removeLeastTerm lam = lam' := ⟨_, rfl⟩
  have hsplit : lam' + L = lam := by rw [← hL, ← hlam']; exact removeLeastTerm_add_leastTerm lam
  have hLne : L ≠ 0 := hL ▸ leastTerm_ne_zero hlam
  have hLprin : IsAdditivelyPrincipal L.val := hL ▸ isAdditivelyPrincipal_leastTerm hlam
  have hlam'lt : lam' < lam := by
    rw [← hsplit]
    exact lt_add_of_pos_right lam' (pos_iff_ne_zero.mpr hLne)
  obtain ⟨A, hA⟩ : ∃ A, lam' + sigma = A := ⟨_, rfl⟩
  -- `λ ⊕ σ = A ⊕ L` is the ordinal sum `A.val + L.val`, as every term of `A` is at least `L`.
  have hterms : ∀ y ∈ A.val.additivePrincipalTerms, L.val ≤ y := by
    intro y hy
    have hy' : y ∈ (lam + sigma).val.additivePrincipalTerms := by
      rw [← hsplit, add_right_comm, hA, mem_additivePrincipalTerms_add_iff]
      exact Or.inl hy
    have := leastTerm_le_of_mem_add hlam hsigma hy'
    rw [hL] at this
    simpa using NatOrdinal.val.le_iff_le.mpr this
  have hsum : lam + sigma = NatOrdinal.of (A.val + L.val) := by
    rw [natOrdinal_of_add_eq_add_of_forall_le hLprin hterms, NatOrdinal.of_val, NatOrdinal.of_val,
      ← hA, ← hsplit, add_right_comm]
  have htau' : tau.val < A.val + L.val := by
    have := NatOrdinal.val.lt_iff_lt.mpr htau
    rwa [hsum, NatOrdinal.val_of] at this
  rcases lt_or_ge tau.val A.val with hlt | hge
  · -- `τ < A`: take `ρ = λ'`.
    exact ⟨lam', hlam'lt, hA ▸ (NatOrdinal.val.lt_iff_lt.mp hlt).le⟩
  · -- `τ = A + ξ` with `ξ < L`: take `ρ = λ' ⊕ ξ`.
    obtain ⟨ξ, hξ⟩ : ∃ ξ, tau.val - A.val = ξ := ⟨_, rfl⟩
    have hτξ : A.val + ξ = tau.val := by rw [← hξ]; exact Ordinal.add_sub_cancel_of_le hge
    have hξL : ξ < L.val := by
      rw [← hξ, Ordinal.sub_lt_of_le hge]
      exact htau'
    refine ⟨lam' + NatOrdinal.of ξ, ?_, ?_⟩
    · have hξL' : NatOrdinal.of ξ < L := by
        rw [← NatOrdinal.val.lt_iff_lt, NatOrdinal.val_of]
        exact hξL
      calc lam' + NatOrdinal.of ξ < lam' + L := by gcongr
        _ = lam := hsplit
    · calc tau = NatOrdinal.of (A.val + ξ) := by rw [hτξ, NatOrdinal.of_val]
        _ ≤ A + NatOrdinal.of ξ := by
            have := oadd_le_add A (NatOrdinal.of ξ)
            rwa [NatOrdinal.val_of] at this
        _ = lam' + NatOrdinal.of ξ + sigma := by rw [← hA, add_right_comm]

/-- For a successor `λ`, every `τ < λ ⊕ σ` is at most `ρ ⊕ σ` with `ρ := λ ⊖ 1 < λ`, whatever
`σ`. -/
theorem exists_lt_le_add_of_constantCoeff_pos {lam sigma tau : NatOrdinal.{u}}
    (hlam : 0 < lam.constantCoeff) (htau : tau < lam + sigma) :
    ∃ rho < lam, tau ≤ rho + sigma := by
  have hrho : lam = removeLeastTerm lam + 1 := by
    have := removeLeastTerm_add_leastTerm lam
    rwa [leastTerm_eq_one_of_constantCoeff_pos hlam, eq_comm] at this
  refine ⟨removeLeastTerm lam, ?_, ?_⟩
  · calc removeLeastTerm lam < removeLeastTerm lam + 1 := lt_add_one _
      _ = lam := hrho.symm
  · have htau' : tau < removeLeastTerm lam + sigma + 1 := by
      calc tau < lam + sigma := htau
        _ = removeLeastTerm lam + 1 + sigma := by rw [← hrho]
        _ = removeLeastTerm lam + sigma + 1 := add_right_comm _ _ _
    exact Order.lt_add_one_iff.mp htau'

end NatOrdinal
